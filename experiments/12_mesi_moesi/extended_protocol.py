"""Abstract MESI/MOESI coherence extension of the v1.9 MSI transition system.

States: I=0, S=1, M=2, E=3, O=4 (MOESI only).
The data tokens and ghost arrays retain v1.6's unbounded integer values.
No RTL, capacity/replacement policy, or real cache-to-cache data routing.

The original MSI module is deliberately left untouched. The same state-variable
names and messages are used; grS with kind=3 carries an E grant, and wb carries
an owner response (which need not update memory in MOESI). The latter is an
abstract owner-to-directory response, not necessarily a DRAM writeback.
"""
from __future__ import annotations
from cache_smt_verifier import Protocol, a, o, neg, eq, imp, ge, le

I,S,M,E,O=0,1,2,3,4

def ismode(m,*modes): return o(*(eq(m,str(v)) for v in modes))

class ExtendedProtocol(Protocol):
    def __init__(self,n=4,variant='MESI'):
        if variant not in ('MESI','MOESI'): raise ValueError(variant)
        super().__init__(n=n,max_version=None)
        self.variant=variant
        self.owned=(variant=='MOESI')
    def domain(self,nxt=False):
        V=lambda k:self.v(k,nxt); L=lambda k,c:self.L(k,c,nxt)
        mx=O if self.owned else E
        terms=[ge(V('mem'),'0'),ge(V('latest'),'0'),
               ge(V('owner'),'(- 1)'),le(V('owner'),str(self.n-1)),
               ge(V('tx'),'(- 1)'),le(V('tx'),str(self.n-1)),
               ismode(V('kind'),0,1,2,3),ismode(V('phase'),0,1)]
        for c in range(self.n):
            terms.extend([ge(L('mode',c),'0'),le(L('mode',c),str(mx))])
            for k in ('val','wbv','grv'):terms.append(ge(L(k,c),'0'))
        return a(*terms)
    def invariant_terms(self,nxt=False):
        V=lambda k:self.v(k,nxt);L=lambda k,c:self.L(k,c,nxt)
        tx,owner,latest,mem=(V(k) for k in ('tx','owner','latest','mem'))
        phase,kind=V('phase'),V('kind')
        none=eq(owner,'(- 1)'); idle=eq(tx,'(- 1)')
        terms=[self.domain(nxt),le(mem,latest),imp(none,eq(mem,latest)),
            imp(neg(none),a(*(imp(neg(eq(L('mode',j),str(O))),neg(L('share',j))) for j in range(self.n) if not self.owned))),
            imp(neg(idle),ismode(kind,1,2,3)),
            imp(a(neg(idle),eq(phase,'0')),ismode(kind,1,2)),
            imp(a(neg(none),eq(phase,'0')),o(*(a(eq(owner,str(c)),o(ismode(L('mode',c),M,E,*([O] if self.owned else [])),L('wb',c))) for c in range(self.n)))),
            imp(idle,a(eq(phase,'0'),eq(kind,'0'),*(neg(L('wait',j)) for j in range(self.n)),
                *(neg(L(z,j)) for j in range(self.n) for z in ('inv','recall','ack','wb','grS','grM','gack')),
                o(none,*(a(eq(owner,str(c)),ismode(L('mode',c),M,E,*([O] if self.owned else []))) for c in range(self.n))))),
            imp(eq(phase,'1'),a(neg(idle),*(neg(L('wait',j)) for j in range(self.n))))]
        if self.owned:
            # When a dirty owner has answered a queued read, the requester's
            # abstract response slot contains the latest version token.
            owner_owned=o(*(a(eq(owner,str(j)),eq(L('mode',j),str(O))) for j in range(self.n)))
            all_answered=a(*(neg(L('wait',j)) for j in range(self.n)))
            for c in range(self.n):
                terms.append(imp(a(eq(tx,str(c)),eq(phase,'0'),eq(kind,'1'),
                                  owner_owned,all_answered),eq(L('grv',c),latest)))
        # Note: unlike MSI, the O owner may coexist with directory sharers.
        for c in range(self.n):
            mode=L('mode',c); M_c=eq(mode,str(M)); E_c=eq(mode,str(E)); O_c=eq(mode,str(O))
            S_c=eq(mode,str(S)); I_c=eq(mode,str(I))
            oc=eq(owner,str(c)); tc=eq(tx,str(c))
            upgrade=a(oc,tc,eq(kind,'2'),eq(phase,'1'))
            clean_read_downgrade=a(L('wb',c),eq(kind,'1'),oc,S_c)
            terms.append(imp(oc,o(ismode(mode,M,E,*([O] if self.owned else [])),L('wb',c),
                 a(tc,eq(phase,'1'),eq(kind,'2'),L('grM',c)),
                 a(tc,eq(phase,'1'),eq(kind,'3'),L('grS',c)))))
            terms.append(imp(M_c,a(oc,eq(L('val',c),latest),*(neg(L('share',j)) for j in range(self.n)))))
            terms.append(imp(E_c,a(oc,eq(L('val',c),latest),eq(mem,latest),
                                  *(neg(L('share',j)) for j in range(self.n)))))
            if self.owned:
                terms.append(imp(O_c,a(oc,eq(L('val',c),latest),
                           *(neg(ismode(L('mode',j),M,E,O)) for j in range(self.n) if j!=c))))
            terms.append(imp(L('share',c),o(S_c,L('ack',c),a(L('grS',c),eq(kind,'1')))))
            terms.append(imp(S_c,a(eq(L('val',c),latest),o(L('share',c),upgrade,clean_read_downgrade),
                o(none,oc,*([o(*(a(eq(owner,str(j)),o(eq(L('mode',j),str(O)),L('wb',j))) for j in range(self.n)))] if self.owned else [])))))
            terms.append(neg(a(L('rqR',c),L('rqW',c))))
            terms.append(imp(L('rqR',c),a(L('pending',c),I_c)))
            terms.append(imp(L('rqW',c),a(L('pending',c),ismode(mode,I,S,*([O] if self.owned else [])))))
            terms.append(imp(L('pending',c),o(L('rqR',c),L('rqW',c),tc)))
            terms.append(imp(a(tc,eq(phase,'0')),a(L('pending',c),ismode(mode,I,S,*([O] if self.owned else [])))))
            terms.append(imp(a(tc,eq(phase,'0')),a(neg(L('rqR',c)),neg(L('rqW',c)))))
            terms.append(imp(o(L('grS',c),L('grM',c)),a(neg(L('rqR',c)),neg(L('rqW',c)))))
            terms.append(imp(a(tc,eq(phase,'0'),eq(kind,'1')),I_c))
            terms.append(imp(L('inv',c),a(S_c,L('share',c),L('wait',c),neg(idle),eq(phase,'0'),eq(kind,'2'))))
            terms.append(imp(L('recall',c),a(ismode(mode,M,E,*([O] if self.owned else [])),oc,L('wait',c),neg(idle),eq(phase,'0'))))
            terms.append(imp(L('ack',c),a(I_c,L('share',c),L('wait',c),neg(idle),eq(phase,'0'),eq(kind,'2'))))
            terms.append(imp(L('wb',c),a(ismode(mode,I,S,*([O] if self.owned else [])),oc,L('wait',c),eq(L('wbv',c),latest),neg(idle),eq(phase,'0'),
                imp(S_c,eq(kind,'1')),imp(S_c,neg(L('share',c))),
                *([imp(O_c,eq(kind,'1')),imp(I_c,eq(kind,'2'))] if self.owned else []))))
            terms.append(imp(a(L('wb',c),S_c),eq(mem,latest)))
            terms.append(imp(L('grS',c),a(I_c,tc,eq(phase,'1'),ismode(kind,1,3),L('pending',c),
                  eq(L('grv',c),latest),
                  o(a(eq(kind,'1'),L('share',c)),a(eq(kind,'3'),oc,neg(L('share',c)))))))
            terms.append(imp(L('grM',c),a(ismode(mode,I,S,*([O] if self.owned else [])),tc,eq(phase,'1'),eq(kind,'2'),
                                      L('pending',c),oc,eq(L('grv',c),latest),
                                      *(neg(L('share',j)) for j in range(self.n)))))
            terms.append(imp(L('gack',c),a(tc,eq(phase,'1'),ismode(mode,S,M,E),eq(L('val',c),latest))))
            terms.append(imp(a(tc,eq(phase,'1')),o(L('grS',c),L('grM',c),L('gack',c))))
            terms.append(imp(a(L('gack',c),eq(kind,'2')),a(M_c,oc)))
            terms.append(imp(a(L('gack',c),L('pending',c)),o(L('rqR',c),L('rqW',c))))
            terms.append(imp(a(L('gack',c),eq(kind,'1')),a(S_c,L('share',c))))
            terms.append(imp(a(L('gack',c),eq(kind,'3')),a(o(E_c,M_c),oc)))
            for x,y in [('inv','recall'),('inv','ack'),('inv','wb'),('recall','ack'),('recall','wb'),('ack','wb')]:
                terms.append(neg(a(L(x,c),L(y,c))))
            # Owner is only recalled if the transaction needs it (own O upgrade does not).
            terms.append(imp(a(eq(phase,'0'),neg(idle),oc,neg(o(a(eq(kind,'1'),O_c),a(tc,O_c)))),L('wait',c)))
            terms.append(imp(a(eq(phase,'0'),neg(idle),eq(kind,'2'),L('share',c),neg(tc)),L('wait',c)))
            terms.append(imp(L('wait',c),a(neg(idle),eq(phase,'0'),o(*(L(z,c) for z in ('inv','recall','ack','wb'))))))
            terms.append(imp(o(*(L(z,c) for z in ('inv','recall','ack','wb'))),L('wait',c)))
            terms.append(imp(a(oc,neg(eq(mem,latest))),o(
                a(ismode(mode,M,*([O] if self.owned else [])),eq(L('val',c),latest)),
                a(L('wb',c),eq(L('wbv',c),latest)))))
        return terms
    def bad(self,nxt=False):
        V=lambda k:self.v(k,nxt);L=lambda k,c:self.L(k,c,nxt)
        terms=[imp(eq(V('owner'),'(- 1)'),eq(V('mem'),V('latest')))]
        for c in range(self.n):
            mc=L('mode',c)
            for m in (M,E,*([O] if self.owned else [])):
                requirements=[eq(V('owner'),str(c)),eq(L('val',c),V('latest'))]
                if m in (M,E):requirements.extend(neg(L('share',j)) for j in range(self.n))
                requirements.extend(neg(ismode(L('mode',j),M,E,*([O] if self.owned else []))) for j in range(self.n) if j!=c)
                terms.append(imp(eq(mc,str(m)),a(*requirements)))
            terms.append(imp(eq(mc,str(S)),eq(L('val',c),V('latest'))))
        return neg(a(*terms))
    def transitions(self):
        V=self.v; L=self.L;n=self.n
        steps=[]
        def add(label,guard,patch):steps.append(self.step(guard,patch,label))
        for c in range(n):
            cs=str(c);mode=L('mode',c);pending=L('pending',c)
            add(f'c{c}:issue_read',a(eq(mode,'0'),neg(pending)),{f'pending_{c}':'true',f'rqR_{c}':'true'})
            add(f'c{c}:issue_write',a(ismode(mode,I,S,*([O] if self.owned else [])),neg(pending)),
                {f'pending_{c}':'true',f'rqW_{c}':'true'})
            # This raw local write is filtered out by the CPU-system frontend.
            add(f'c{c}:write',a(ismode(mode,M,E)),{'latest':f'(+ {V("latest")} 1)','val_'+cs:f'(+ {V("latest")} 1)',
                'mode_'+cs:'2'})
            for typ in ('rqR','rqW'):
                write=(typ=='rqW')
                patch={'tx':cs,'kind':'2' if write else '1','phase':'0',f'{typ}_{c}':'false'}
                for j in range(n):
                    owner_j=eq(V('owner'),str(j))
                    # Already-owned O requester upgrades after invalidating sharers.
                    recall=a(owner_j,neg(a('true' if write else 'false',eq(str(j),cs),eq(L('mode',j),str(O))))) if self.owned else owner_j
                    invalid=a(L('share',j),'true' if write and j!=c else 'false')
                    patch[f'wait_{j}']=o(recall,invalid)
                    patch[f'recall_{j}']=o(L('recall',j),recall)
                    patch[f'inv_{j}']=o(L('inv',j),invalid)
                add(f'dir:start_{typ}_c{c}',a(eq(V('tx'),'(- 1)'),L(typ,c)),patch)
            for write in (False,True):
                base=a(eq(V('tx'),cs),eq(V('phase'),'0'),eq(V('kind'),'2' if write else '1'),
                    *(neg(L('wait',j)) for j in range(n)))
                if write:
                    patch={'phase':'1',f'grM_{c}':'true',f'grv_{c}':V('latest'),'owner':cs}
                    for j in range(n):patch[f'share_{j}']='false'
                    add(f'dir:grant_M_c{c}',base,patch)
                else:
                    # E only when no other copy exists and memory is current.
                    exclusive=a(eq(V('owner'),'(- 1)'),*(neg(L('share',j)) for j in range(n)))
                    add(f'dir:grant_E_c{c}',a(base,exclusive),{'phase':'1','kind':'3',f'grS_{c}':'true',
                        f'grv_{c}':V('latest'),'owner':cs})
                    extra = imp(neg(eq(V('owner'),'(- 1)')),eq(L('grv',c),V('latest'))) if self.owned else 'true'
                    data = f'(ite (= {V("owner")} (- 1)) {V("mem")} {L("grv",c)})' if self.owned else V('latest')
                    add(f'dir:grant_S_c{c}',a(base,neg(exclusive),extra),{'phase':'1',f'grS_{c}':'true',
                        f'grv_{c}':data,f'share_{c}':'true'})
            add(f'net:deliver_inv_c{c}',a(L('inv',c),eq(mode,'1')),
                {f'inv_{c}':'false',f'mode_{c}':'0',f'ack_{c}':'true'})
            # MESI: M/E owner gives up line on remote read or write.
            # MOESI: M/O owner retains dirty Owned copy on remote read.
            if self.owned:
                for old in (M,O):
                    add(f'net:deliver_recall_to_O_from_{old}_c{c}',
                        a(L('recall',c),eq(mode,str(old)),eq(V('kind'),'1')),
                        {f'recall_{c}':'false',f'mode_{c}':str(O),f'wb_{c}':'true',f'wbv_{c}':L('val',c)})
            add(f'net:deliver_recall_E_read_c{c}',a(L('recall',c),eq(mode,str(E)),eq(V('kind'),'1')),
                {f'recall_{c}':'false',f'mode_{c}':str(S),f'wb_{c}':'true',f'wbv_{c}':L('val',c)})
            if not self.owned:
                add(f'net:deliver_recall_to_I_from_{M}_read_c{c}',
                    a(L('recall',c),eq(mode,str(M)),eq(V('kind'),'1')),
                    {f'recall_{c}':'false',f'mode_{c}':'0',f'wb_{c}':'true',f'wbv_{c}':L('val',c)})
            for old in (M,E,*([O] if self.owned else [])):
                add(f'net:deliver_recall_to_I_from_{old}_write_c{c}',
                    a(L('recall',c),eq(mode,str(old)),eq(V('kind'),'2')),
                    {f'recall_{c}':'false',f'mode_{c}':'0',f'wb_{c}':'true',f'wbv_{c}':L('val',c)})
            add(f'dir:accept_ack_c{c}',a(L('ack',c),L('wait',c)),
                {f'ack_{c}':'false',f'wait_{c}':'false',f'share_{c}':'false'})
            add(f'dir:accept_wb_E_read_c{c}',a(L('wb',c),L('wait',c),eq(mode,str(S)),eq(V('kind'),'1')),
                {f'wb_{c}':'false',f'wait_{c}':'false',f'share_{c}':'true','owner':'(- 1)'})
            if self.owned:
                patch={f'wb_{c}':'false',f'wait_{c}':'false'}
                # Abstract forwarded value is carried by wbv, then deposited
                # into the *requester's* response slot (grv). Memory stays stale.
                for j in range(n):
                    patch[f'grv_{j}']=f'(ite (= {V("tx")} {j}) {L("wbv",c)} {L("grv",j)})'
                add(f'dir:accept_wb_O_read_c{c}',a(L('wb',c),L('wait',c),eq(mode,str(O)),eq(V('kind'),'1')),
                    patch)
            add(f'dir:accept_wb_drop_c{c}',a(L('wb',c),L('wait',c),eq(mode,str(I))),
                {f'wb_{c}':'false',f'wait_{c}':'false','owner':'(- 1)','mem':L('wbv',c)})
            add(f'net:deliver_grS_c{c}',L('grS',c),
                {f'grS_{c}':'false',f'mode_{c}':f'(ite (= {V("kind")} 3) 3 1)',
                 f'val_{c}':L('grv',c),f'pending_{c}':'false',f'gack_{c}':'true'})
            add(f'net:deliver_grM_c{c}',L('grM',c),
                {f'grM_{c}':'false',f'mode_{c}':'2',f'val_{c}':L('grv',c),
                 f'pending_{c}':'false',f'gack_{c}':'true'})
            add(f'dir:accept_gack_c{c}',a(L('gack',c),eq(V('tx'),cs),eq(V('phase'),'1')),
                {f'gack_{c}':'false','tx':'(- 1)','kind':'0','phase':'0'})
        return steps
