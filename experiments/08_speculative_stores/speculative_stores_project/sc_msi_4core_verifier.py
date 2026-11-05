#!/usr/bin/env python3
"""Machine-checkable modular sequential-consistency safety proof for 4-core, 2-line MSI.

This builds on cache_smt_verifier.Protocol, retaining its explicit asynchronous
request, invalidation, recall, writeback, grant and ack steps. A CPU frontend
issues arbitrary R, W and CAS commands with one outstanding command per core.

Cache protocol state stores unique write-version tokens. An immutable symbolic
SMT array maps each version to an arbitrary data value, allowing repeated data
values (including ABA) and arbitrary store/CAS operands. Each completed write
is constrained to create a version with its requested data value. This is an
execution-wise symbolic encoding of arbitrary values, not concrete RAM RTL.

The checker constructs quantified-by-SMT symbolic initial, induction and
safety obligations. UNSAT for all is an unbounded-step proof for fixed 4 cores
and 2 lines. No liveness/fairness claims are made.
"""
import argparse, json, re, time, os
from cache_smt_verifier import Protocol, a, o, neg, eq, imp, ge, le, z3_smt

class System:
    def __init__(self, cores=4, lines=2, broken_ordering=False):
        self.n=cores;self.k=lines;self.broken=broken_ordering
        self.p=Protocol(cores, max_version=None)
        self.orig_pkeys=self.p.keys
        self.line_keys=[f'l{l}__{key}' for l in range(lines) for key in self.orig_pkeys]
        self.local_keys=[f'{key}_{c}' for c in range(cores) for key in ('busy','op','target','expected','newval','observed','cas_success')]
        self.keys=self.line_keys+self.local_keys+[f'ref_{l}' for l in range(lines)]+['bad']
        self.types={f'l{l}__{key}':typ for l in range(lines) for key,typ in self.p.types.items()}
        for c in range(cores):
            self.types.update({f'busy_{c}':'Bool',f'op_{c}':'Int',f'target_{c}':'Int',
                               f'expected_{c}':'Int',f'newval_{c}':'Int',f'observed_{c}':'Int',f'cas_success_{c}':'Bool'})
        self.types.update({f'ref_{l}':'Int' for l in range(lines)});self.types['bad']='Bool'
        names=sorted(self.orig_pkeys, key=len, reverse=True)
        self.rename_re=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(re.escape(x) for x in names)+r')(_next)?(?![A-Za-z0-9_])')
    def map_line(self, expr, line):
        return self.rename_re.sub(lambda m: f'l{line}__{m.group(1)}'+(m.group(2) or ''), expr)
    def v(self,name,nxt=False):return name+('_next' if nxt else '')
    def pl(self,l,key,core=None,nxt=False):
        return self.v(f'l{l}__{key}'+(f'_{core}' if core is not None else ''),nxt)
    def cpu(self,c,key,nxt=False):return self.v(f'{key}_{c}',nxt)
    def declarations(self):
        return '\n'.join(f'(declare-const {self.v(key,nxt)} {typ})' for nxt in (False,True) for key,typ in self.types.items())+'\n'+'\n'.join(f'(declare-const payload_{l} (Array Int Int))' for l in range(self.k))
    def init(self):
        terms=[self.map_line(self.p.init(),l) for l in range(self.k)]
        for c in range(self.n):
            for key,v in [('busy','false'),('op','0'),('target','0'),('expected','0'),('newval','0'),('observed','0'),('cas_success','false')]:
                terms.append(eq(self.cpu(c,key),v))
        for l in range(self.k):terms.append(eq(self.v(f'ref_{l}'),'0'))
        terms.append(eq(self.v('bad'),'false'))
        return a(*terms)
    def inv(self,nxt=False):
        terms=[self.map_line(self.p.inv(nxt),l) for l in range(self.k)]
        terms.extend([eq(self.v(f'ref_{l}',nxt),self.pl(l,'latest',nxt=nxt)) for l in range(self.k)])
        terms.append(neg(self.v('bad',nxt)))
        for c in range(self.n):
            busy=self.cpu(c,'busy',nxt);op=self.cpu(c,'op',nxt);target=self.cpu(c,'target',nxt)
            terms.extend([imp(busy,o(*(eq(op,str(z)) for z in (1,2,3)))),
                          imp(neg(busy),eq(op,'0')),
                          ge(target,'0'),le(target,str(self.k-1)),
                          ])
            # A CPU has at most one outstanding command. Every cache miss must
            # belong to the currently outstanding command for that line.
            for l in range(self.k):
                pending=self.pl(l,'pending',c,nxt)
                terms.append(imp(pending,a(busy,eq(target,str(l)))))
                terms.append(imp(self.pl(l,'rqR',c,nxt),eq(op,'1')))
                terms.append(imp(self.pl(l,'rqW',c,nxt),o(eq(op,'2'),eq(op,'3'))))
        return a(*terms)
    def step(self, label, guard, patch):
        assert set(patch)<=set(self.keys), set(patch)-set(self.keys)
        formula=a(guard,*(eq(self.v(key,True), patch.get(key,self.v(key))) for key in self.keys))
        return label,formula
    def steps(self):
        out=[]
        for l in range(self.k):
            for label,raw in self.p.transitions():
                if ':issue_' in label or label.endswith(':write'):
                    continue
                # A coherence-network step affects only this cache line.
                others=[eq(self.v(key,True),self.v(key)) for key in self.keys if not key.startswith(f'l{l}__')]
                out.append((f'l{l}::{label}',a(self.map_line(raw,l),*others)))
        for c in range(self.n):
            busy=self.cpu(c,'busy');op=self.cpu(c,'op');target=self.cpu(c,'target')
            for l in range(self.k):
                for kind in (1,2,3):
                    p={f'busy_{c}':'true',f'op_{c}':str(kind),f'target_{c}':str(l)}
                    # External inputs are arbitrary integer data values.
                    if kind==3:p[f'expected_{c}']=self.cpu(c,'expected',nxt=True)
                    if kind in (2,3):p[f'newval_{c}']=self.cpu(c,'newval',nxt=True)
                    # The self-reference on _next leaves the input unconstrained.
                    out.append(self.step(f'core{c}:issue_{kind}_line{l}',neg(busy),p))
                mode=self.pl(l,'mode',c)
                pending=self.pl(l,'pending',c)
                miss_read=a(busy,eq(target,str(l)),eq(op,'1'),eq(mode,'0'),neg(pending))
                miss_write=a(busy,eq(target,str(l)),o(eq(op,'2'),eq(op,'3')),
                             o(eq(mode,'0'),eq(mode,'1')),neg(pending))
                out.append(self.step(f'core{c}:ask_read_line{l}',miss_read,
                    {f'l{l}__pending_{c}':'true', f'l{l}__rqR_{c}':'true'}))
                out.append(self.step(f'core{c}:ask_write_line{l}',miss_write,
                    {f'l{l}__pending_{c}':'true', f'l{l}__rqW_{c}':'true'}))
                val=self.pl(l,'val',c);latest=self.pl(l,'latest');ref=self.v(f'ref_{l}')
                base=a(busy,eq(target,str(l)),neg(pending))
                reset={f'busy_{c}':'false',f'op_{c}':'0'}
                # Model architectural completion as a single linearization event.
                out.append(self.step(f'core{c}:complete_read_line{l}',
                    a(base,eq(op,'1'),o(eq(mode,'1'),eq(mode,'2'))),
                    dict(reset,**{f'observed_{c}':f'(select payload_{l} {val})',
                                 'bad':o(self.v('bad'),neg(eq(val,ref)))})))
                # Pure program-order store. A write-version token increments.
                out.append(self.step(f'core{c}:complete_store_line{l}',
                    a(base,eq(op,'2'),eq(mode,'2'),
                      eq(f'(select payload_{l} (+ {latest} 1))',self.cpu(c,'newval'))),
                    dict(reset,**{f'l{l}__latest':f'(+ {latest} 1)',
                                 f'l{l}__val_{c}':f'(+ {latest} 1)',
                                 f'ref_{l}':f'(+ {ref} 1)'})))
                cmp=eq(f'(select payload_{l} {val})',self.cpu(c,'expected'))
                out.append(self.step(f'core{c}:complete_cas_line{l}',
                    a(base,eq(op,'3'),eq(mode,'2'),
                      imp(cmp,eq(f'(select payload_{l} (+ {latest} 1))',self.cpu(c,'newval')))),
                    dict(reset,**{f'cas_success_{c}':cmp,
                                 f'observed_{c}':f'(select payload_{l} {val})',
                                 'bad':o(self.v('bad'),neg(eq(val,ref))),
                                 f'l{l}__latest':f'(ite {cmp} (+ {latest} 1) {latest})',
                                 f'l{l}__val_{c}':f'(ite {cmp} (+ {latest} 1) {val})',
                                 f'ref_{l}':f'(ite {cmp} (+ {ref} 1) {ref})'})))
        # An optional intentionally bad mutant permits a store to be observed
        # before the preceding core operation completes (e.g., mimics a bypass).
        # See separate small litmus BMC rather than inserting a nonsensical
        # non-coherent write into the MSI protocol.
        return out
    def T(self):return o(*(frm for _,frm in self.steps()))
    def query(self,which):
        init=self.init();inv=self.inv();invnext=self.inv(True);T=self.T()
        if which=='initial':goals=[init,neg(inv)]
        elif which=='induction':goals=[inv,T,neg(invnext)]
        elif which=='safety':goals=[inv,self.v('bad')]
        else:raise ValueError(which)
        return self.declarations()+'\n'+'\n'.join('(assert '+g+')' for g in goals)+'\n(check-sat)\n'
    def check(self,output_dir):
        os.makedirs(output_dir,exist_ok=True)
        stats=[]
        for which in ('initial','induction','safety'):
            query=self.query(which)
            file=os.path.join(output_dir,which+'.smt2');open(file,'w').write(query)
            start=time.monotonic();s=z3_smt(query).strip().splitlines()[0]
            stats.append({'obligation':which,'result':s,'seconds':round(time.monotonic()-start,3),
                          'smt_bytes':len(query),'file':os.path.basename(file)})
            if s!='unsat':break
        return {'cores':self.n,'lines':self.k,'programs':'nondeterministic command streams; one in-flight op per core',
                'values':'unbounded integers: symbolic payload(version) permits arbitrary and repeated data values; a successful write constrains its new version to requested data',
                'internal_protocol_actions':sum(1 for label,_ in self.p.transitions() if ':issue_' not in label and not label.endswith(':write'))*self.k,
                'frontend_actions':len(self.steps())-sum(1 for label,_ in self.p.transitions() if ':issue_' not in label and not label.endswith(':write'))*self.k,
                'proof':'UNBOUNDED_INDUCTION_PASS' if len(stats)==3 and all(x['result']=='unsat' for x in stats) else 'FAILED',
                'checks':stats}

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--cores',type=int,default=4);parser.add_argument('--lines',type=int,default=2)
    parser.add_argument('--output-dir',default='/mnt/data/sc_msi_smt')
    x=parser.parse_args()
    s=System(x.cores,x.lines)
    result=s.check(x.output_dir)
    open(os.path.join(x.output_dir,'results.json'),'w').write(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))
