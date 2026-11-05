#!/usr/bin/env python3
"""Solver-checked safety argument for an asynchronous directory MSI line.

No third-party Python package is required on Linux when libz3 is installed.
This creates a standalone SMT-LIB2 proof obligation and passes it to Z3.
Scope: n fixed caches, values/versions in 0..max_version, unlimited steps.
The protocol has arbitrary asynchronous delivery, one active directory transaction,
multiple queued requests, cached Modified writes, recalls, writebacks and grant acks.
"""
import argparse, ctypes, json, os, time


def a(*xs):
    xs=[x for x in xs if x not in ('true', None)]
    if any(x=='false' for x in xs):return 'false'
    if not xs:return 'true'
    return xs[0] if len(xs)==1 else '(and ' + ' '.join(xs) + ')'
def o(*xs):
    xs=[x for x in xs if x not in ('false', None)]
    if any(x=='true' for x in xs):return 'true'
    if not xs:return 'false'
    return xs[0] if len(xs)==1 else '(or ' + ' '.join(xs) + ')'
def neg(x):return f'(not {x})'
def eq(x,y):return f'(= {x} {y})'
def imp(x,y):return f'(=> {x} {y})'
def ite(x,y,z):return f'(ite {x} {y} {z})'
def ge(x,y):return f'(>= {x} {y})'
def le(x,y):return f'(<= {x} {y})'


class Protocol:
    # States: cache 0=Invalid,1=Shared,2=Modified.
    # Requests: rqR/rqW. Network messages: inv, recall, ack, wb, grS, grM, gack.
    def __init__(self,n=2,max_version=2,early_grant=False):
        self.n=n;self.max_version=max_version;self.early_grant=early_grant
        self.globals={'mem':'Int','latest':'Int','owner':'Int','tx':'Int','kind':'Int','phase':'Int'}
        self.local={'mode':'Int','val':'Int','pending':'Bool','share':'Bool','wait':'Bool',
                    'rqR':'Bool','rqW':'Bool','inv':'Bool','recall':'Bool','ack':'Bool',
                    'wb':'Bool','wbv':'Int','grS':'Bool','grM':'Bool','grv':'Int','gack':'Bool'}
        self.types=self.globals|{f'{k}_{c}':v for c in range(n) for k,v in self.local.items()}
        self.keys=list(self.types)
    def v(self,k,nxt=False):return k+('_next' if nxt else '')
    def L(self,k,c,nxt=False):return self.v(f'{k}_{c}',nxt)
    def declarations(self):
        return '\n'.join(f'(declare-const {self.v(k,nxt)} {typ})'
                         for nxt in (False,True) for k,typ in self.types.items())
    def init(self):
        fields={'mem':'0','latest':'0','owner':'(- 1)','tx':'(- 1)','kind':'0','phase':'0'}
        for c in range(self.n):
            for k in self.local:
                fields[f'{k}_{c}']='false' if self.local[k]=='Bool' else '0'
        return a(*(eq(self.v(k),v) for k,v in fields.items()))
    def domain(self,nxt=False):
        V=lambda k:self.v(k,nxt);L=lambda k,c:self.L(k,c,nxt)
        terms=[ge(V('mem'),'0'),
              ge(V('latest'),'0'),
              ge(V('owner'),'(- 1)'),le(V('owner'),str(self.n-1)),
              ge(V('tx'),'(- 1)'),le(V('tx'),str(self.n-1)),
              o(eq(V('kind'),'0'),eq(V('kind'),'1'),eq(V('kind'),'2')),
              o(eq(V('phase'),'0'),eq(V('phase'),'1'))]
        for c in range(self.n):
            terms.extend([ge(L('mode',c),'0'),le(L('mode',c),'2')])
            for k in ('val','wbv','grv'):
                terms.append(ge(L(k,c),'0'))
        if self.max_version is not None:
            terms.extend([le(V('mem'),str(self.max_version)),le(V('latest'),str(self.max_version))])
            for c in range(self.n):
                for k in ('val','wbv','grv'):
                    terms.append(le(L(k,c),str(self.max_version)))
        return a(*terms)
    def invariant_terms(self,nxt=False):
        V=lambda k:self.v(k,nxt);L=lambda k,c:self.L(k,c,nxt)
        tx=V('tx');owner=V('owner'); latest=V('latest'); mem=V('mem')
        terms=[self.domain(nxt),le(mem,latest),imp(eq(owner,'(- 1)'),eq(mem,latest)),
               imp(neg(eq(owner,'(- 1)')),a(*(neg(L('share',j)) for j in range(self.n)))),
               imp(neg(eq(tx,'(- 1)')),o(eq(V('kind'),'1'),eq(V('kind'),'2'))),
               imp(a(neg(eq(owner,'(- 1)')),eq(V('phase'),'0')),
                   o(*(a(eq(owner,str(c)),o(eq(L('mode',c),'2'),L('wb',c))) for c in range(self.n)))),
               imp(eq(tx,'(- 1)'),a(eq(V('phase'),'0'),eq(V('kind'),'0'),
                                       *(neg(L('wait',c)) for c in range(self.n)),
                                       *(neg(L(k,c)) for c in range(self.n) for k in ('inv','recall','ack','wb','grS','grM','gack')),
                                       o(eq(owner,'(- 1)'),*(a(eq(owner,str(c)),eq(L('mode',c),'2')) for c in range(self.n))))),
               imp(eq(V('phase'),'1'),a(neg(eq(tx,'(- 1)')),
                                              *(neg(L('wait',c)) for c in range(self.n))))]
        for c in range(self.n):
            M=eq(L('mode',c),'2');S=eq(L('mode',c),'1');I=eq(L('mode',c),'0')
            ownerc=eq(owner,str(c));txc=eq(tx,str(c))
            upgrade=a(ownerc,txc,eq(V('kind'),'2'),eq(V('phase'),'1'))
            terms.append(imp(M,a(ownerc,eq(L('val',c),latest),
                                      *(neg(L('share',j)) for j in range(self.n)))))
            terms.append(imp(L('share',c),o(S,L('ack',c),L('grS',c))))
            terms.append(imp(S,a(eq(L('val',c),latest),
                                  o(L('share',c),upgrade),
                                  o(eq(owner,'(- 1)'),ownerc))))
            terms.append(neg(a(L('rqR',c),L('rqW',c))))
            terms.append(imp(L('rqR',c),a(L('pending',c),I)))
            terms.append(imp(L('rqW',c),a(L('pending',c),o(I,S))))
            terms.append(imp(L('pending',c),o(L('rqR',c),L('rqW',c),txc)))
            terms.append(imp(a(txc,eq(V('phase'),'0')),a(L('pending',c),o(I,S))))
            terms.append(imp(a(txc,eq(V('phase'),'0')),a(neg(L('rqR',c)),neg(L('rqW',c)))))
            terms.append(imp(o(L('grS',c),L('grM',c)),a(neg(L('rqR',c)),neg(L('rqW',c)))))
            terms.append(imp(a(txc,eq(V('phase'),'0'),eq(V('kind'),'1')),I))
            terms.append(imp(L('inv',c),a(S,L('share',c),L('wait',c),
                                            neg(eq(tx,'(- 1)')),eq(V('phase'),'0'))))
            terms.append(imp(L('recall',c),a(M,ownerc,L('wait',c),
                                               neg(eq(tx,'(- 1)')),eq(V('phase'),'0'))))
            terms.append(imp(L('ack',c),a(I,L('share',c),L('wait',c),
                                           neg(eq(tx,'(- 1)')),eq(V('phase'),'0'))))
            terms.append(imp(L('wb',c),a(I,ownerc,L('wait',c),eq(L('wbv',c),latest),
                                          neg(eq(tx,'(- 1)')),eq(V('phase'),'0'))))
            terms.append(imp(L('grS',c),a(I,txc,eq(V('phase'),'1'),eq(V('kind'),'1'),
                                             L('pending',c),L('share',c),eq(L('grv',c),latest))))
            terms.append(imp(L('grM',c),a(o(I,S),txc,eq(V('phase'),'1'),eq(V('kind'),'2'),
                                               L('pending',c),ownerc,eq(L('grv',c),latest))))
            terms.append(imp(L('gack',c),a(txc,eq(V('phase'),'1'),
                                              o(S,M),eq(L('val',c),latest))))
            terms.append(imp(a(txc,eq(V('phase'),'1')),o(L('grS',c),L('grM',c),L('gack',c))))
            terms.append(imp(a(L('gack',c),eq(V('kind'),'2')),a(M,ownerc)))
            terms.append(imp(a(L('gack',c),L('pending',c)),o(L('rqR',c),L('rqW',c))))
            terms.append(imp(a(L('gack',c),eq(V('kind'),'1')),a(S,L('share',c))))
            terms.extend([
                neg(a(L('inv',c),L('recall',c))),neg(a(L('inv',c),L('ack',c))),
                neg(a(L('inv',c),L('wb',c))),neg(a(L('recall',c),L('ack',c))),
                neg(a(L('recall',c),L('wb',c))),neg(a(L('ack',c),L('wb',c)))
            ])
            terms.append(imp(a(eq(V('phase'),'0'),neg(eq(tx,'(- 1)')),eq(owner,str(c))),L('wait',c)))
            terms.append(imp(a(eq(V('phase'),'0'),neg(eq(tx,'(- 1)')),eq(V('kind'),'2'),
                               L('share',c),neg(txc)),L('wait',c)))
            terms.append(imp(L('wait',c),a(neg(eq(tx,'(- 1)')),eq(V('phase'),'0'),
                                               o(L('inv',c),L('recall',c),L('ack',c),L('wb',c)))))
            terms.append(imp(o(L('inv',c),L('recall',c),L('ack',c),L('wb',c)),L('wait',c)))
            # If directory memory is stale, newest data still exists in an M cache or writeback.
            terms.append(imp(a(ownerc,neg(eq(mem,latest))),
                             o(a(M,eq(L('val',c),latest)),
                               a(L('wb',c),eq(L('wbv',c),latest)))))
        return terms
    def inv(self,nxt=False):return a(*self.invariant_terms(nxt))
    def bad(self,nxt=False):
        # Actual contract: permission exclusion, data integrity, safe latest-memory fallback.
        V=lambda k:self.v(k,nxt);L=lambda k,c:self.L(k,c,nxt)
        constraints=[imp(eq(V('owner'),'(- 1)'),eq(V('mem'),V('latest')))]
        for c in range(self.n):
            constraints.append(imp(eq(L('mode',c),'2'),a(eq(V('owner'),str(c)),
                          eq(L('val',c),V('latest')),
                          *(neg(eq(L('mode',j),'1')) for j in range(self.n) if j!=c),
                          *(neg(eq(L('mode',j),'2')) for j in range(self.n) if j!=c))))
            constraints.append(imp(eq(L('mode',c),'1'),eq(L('val',c),V('latest'))))
        return neg(a(*constraints))
    def double_writer(self,nxt=False):
        L=lambda k,c:self.L(k,c,nxt)
        return o(*(a(eq(L('mode',c),'2'),eq(L('mode',d),'2'))
                   for c in range(self.n) for d in range(c+1,self.n)))
    def step(self,guard,patch,label):
        frames=[eq(self.v(k,True),patch.get(k,self.v(k))) for k in self.keys]
        return label,a(guard,*frames)
    def transitions(self):
        V=self.v;L=self.L;n=self.n
        steps=[]
        def add(label,guard,patch):steps.append(self.step(guard,patch,label))
        for c in range(n):
            nc=str(c);m=L('mode',c);p=L('pending',c)
            add(f'c{c}:issue_read',a(eq(m,'0'),neg(p)),{f'pending_{c}':'true',f'rqR_{c}':'true'})
            add(f'c{c}:issue_write',a(o(eq(m,'0'),eq(m,'1')),neg(p)),
                {f'pending_{c}':'true',f'rqW_{c}':'true'})
            add(f'c{c}:write',a(eq(m,'2'), 'true' if self.max_version is None else f'(< {V("latest")} {self.max_version})'),
                {'latest':f'(+ {V("latest")} 1)',f'val_{c}':f'(+ {V("latest")} 1)'})
            for typ in ('rqR','rqW'):
                isw=typ=='rqW'; reqkind='2' if isw else '1'
                patch={'tx':nc,'kind':reqkind,'phase':'0',f'{typ}_{c}':'false'}
                for j in range(n):
                    recall=eq(V('owner'),str(j))
                    invalid=a(L('share',j),'true' if isw and j!=c else 'false')
                    patch[f'wait_{j}']=o(recall,invalid)
                    patch[f'recall_{j}']=o(L('recall',j),recall)
                    patch[f'inv_{j}']=o(L('inv',j),invalid)
                add(f'dir:start_{typ}_c{c}',a(eq(V('tx'),'(- 1)'),L(typ,c)),patch)
            # Grant after all victim acknowledgments. Early-grant mutant intentionally removes wait.
            for isw in (False,True):
                guard=a(eq(V('tx'),nc),eq(V('phase'),'0'),
                        eq(V('kind'),'2' if isw else '1'),
                        'true' if self.early_grant else a(*(neg(L('wait',j)) for j in range(n))))
                patch={'phase':'1',f'{"grM" if isw else "grS"}_{c}':'true',f'grv_{c}':V('mem')}
                if isw:
                    patch['owner']=nc
                    for j in range(n):patch[f'share_{j}']='false'
                else:patch[f'share_{c}']='true'
                add(f'dir:grant_{"M" if isw else "S"}_c{c}',guard,patch)
            add(f'net:deliver_inv_c{c}',a(L('inv',c),eq(m,'1')),
                {f'inv_{c}':'false',f'mode_{c}':'0',f'ack_{c}':'true'})
            add(f'net:deliver_recall_c{c}',a(L('recall',c),eq(m,'2')),
                {f'recall_{c}':'false',f'mode_{c}':'0',f'wb_{c}':'true',f'wbv_{c}':L('val',c)})
            add(f'dir:accept_ack_c{c}',a(L('ack',c),L('wait',c)),
                {f'ack_{c}':'false',f'wait_{c}':'false',f'share_{c}':'false'})
            add(f'dir:accept_wb_c{c}',a(L('wb',c),L('wait',c)),
                {f'wb_{c}':'false',f'wait_{c}':'false','owner':'(- 1)','mem':L('wbv',c)})
            for kind in ('grS','grM'):
                add(f'net:deliver_{kind}_c{c}',L(kind,c),
                    {f'{kind}_{c}':'false',f'mode_{c}':'2' if kind=='grM' else '1',
                     f'val_{c}':L('grv',c),f'pending_{c}':'false',f'gack_{c}':'true'})
            add(f'dir:accept_gack_c{c}',a(L('gack',c),eq(V('tx'),nc),eq(V('phase'),'1')),
                {f'gack_{c}':'false','tx':'(- 1)','kind':'0','phase':'0'})
        return steps
    def T(self):return o(*(f for label,f in self.transitions()))
    def query_smt(self,goal='induction',model=False):
        prefix=self.declarations()+'\n'
        if goal=='initial': assertions=[self.init(),neg(self.inv())]
        elif goal=='induction': assertions=[self.inv(),self.T(),neg(self.inv(True))]
        elif goal=='safety': assertions=[self.inv(),self.bad()]
        elif goal=='safety_next':assertions=[self.inv(),self.T(),self.bad(True)]
        elif goal=='bmc0':assertions=[self.init(),self.bad()]
        else:raise ValueError(goal)
        return prefix+'\n'.join('(assert '+p+')' for p in assertions)+'\n(check-sat)\n'+('(get-model)\n' if model else '')


def z3_smt(s):
    lib=ctypes.CDLL('libz3.so.4')
    lib.Z3_mk_config.restype=ctypes.c_void_p
    lib.Z3_mk_context.argtypes=[ctypes.c_void_p];lib.Z3_mk_context.restype=ctypes.c_void_p
    lib.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p];lib.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
    lib.Z3_del_context.argtypes=[ctypes.c_void_p];lib.Z3_del_config.argtypes=[ctypes.c_void_p]
    cfg=lib.Z3_mk_config();ctx=lib.Z3_mk_context(cfg)
    try:
        output=lib.Z3_eval_smtlib2_string(ctx,s.encode()).decode()
    finally:
        lib.Z3_del_context(ctx);lib.Z3_del_config(cfg)
    return output


def check(n=2,max_version=2,early_grant=False,output_dir=None):
    p=Protocol(n,max_version,early_grant)
    outcomes={}
    for goal in ['initial','induction','safety']:
        t=time.monotonic();query=p.query_smt(goal,model=False)
        if output_dir:
            with open(os.path.join(output_dir,f'{goal}_{n}core'+('_bug' if early_grant else '')+'.smt2'),'w') as f:f.write(query)
        result=z3_smt(query)
        outcomes[goal]={'result':result.splitlines()[0], 'seconds':round(time.monotonic()-t,3)}
        if result.splitlines()[0]!='unsat':
            outcomes[goal]['z3_output']=z3_smt(p.query_smt(goal,model=True))[:12000] if result.splitlines()[0]=='sat' else result[:12000]
            break
    return {'n_cores':n,'max_version':max_version,'mutant':early_grant,
            'unbounded_depth_proof':all(v['result']=='unsat' for v in outcomes.values()),
            'checks':outcomes,'transitions':len(p.transitions()),
            'invariant_clauses':len(p.invariant_terms())}

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--cores',type=int,default=2)
    ap.add_argument('--max-version',type=int,default=2)
    ap.add_argument('--unbounded-versions',action='store_true')
    ap.add_argument('--early-grant',action='store_true')
    ap.add_argument('--output-dir',default='/mnt/data')
    args=ap.parse_args()
    os.makedirs(args.output_dir,exist_ok=True)
    print(json.dumps(check(args.cores,None if args.unbounded_versions else args.max_version,args.early_grant,args.output_dir),indent=2))
