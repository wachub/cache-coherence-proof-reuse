#!/usr/bin/env python3
"""Small explicit FIFO store-buffer + 3-line directory-MSI proof.

2 cores (W=0,R=1), independent lines A,B,F, writer performs
  store A=1; store B=1; release-CAS F:0->1
Reader acquires F==1, then can read A and B in either order.

For each line this REUSES the exact asynchronous directory protocol
from cache_smt_verifier.Protocol. The bounded program has one write per
line, but transition count, delays, and polling are unbounded.

libz3.so.4 is accessed via ctypes by the original model.
"""
import json, os, re, time, argparse, sys
from cache_smt_verifier import Protocol, a, o, neg, eq, imp, z3_smt


class FIFOProof:
    def __init__(self, broken=False):
        self.broken = broken
        self.base = Protocol(n=2, max_version=1)
        self.lines = ('A','B','F')
        self.extra = {
            'pc':'Int',       # 0 before A, 1 before B, 2 before release request, 3 release pending
            'count':'Int',    # 0/1/2 occupied FIFO entries
            'slot0':'Int',    # 0=empty,1=A,2=B
            'slot1':'Int',
            'released':'Bool',
            'acquired':'Bool',
            'read_A':'Bool',
            'read_B':'Bool',
            'rv_A':'Int',
            'rv_B':'Int',
        }
        self.types={f'{line}_{name}':typ for line in self.lines for name,typ in self.base.types.items()}
        self.types.update(self.extra)
        self.keys=list(self.types)
        self.symbol_re=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(sorted(map(re.escape,self.base.keys),key=len,reverse=True))+r')(_next)?(?![A-Za-z0-9_])')

    def v(self,name,nxt=False):return name+('_next' if nxt else '')
    def line(self,L,name,nxt=False):return self.v(f'{L}_{name}',nxt)
    def tr(self,term,L):
        return self.symbol_re.sub(lambda m:L+'_'+m.group(1)+(m.group(2) or ''),term)
    def decl(self,indexed=False,number=2):
        if indexed:
            return '\n'.join(f'(declare-const {name}_{i} {typ})' for i in range(number) for name,typ in self.types.items())
        return '\n'.join(f'(declare-const {self.v(name,nxt)} {typ})' for nxt in (False,True) for name,typ in self.types.items())
    def init(self):
        return a(*(self.tr(self.base.init(),L) for L in self.lines),
                 *(eq(name,'false' if typ=='Bool' else '0') for name,typ in self.extra.items()))
    def local_inv(self,nxt=False):
        return a(*(self.tr(self.base.inv(nxt),L) for L in self.lines))
    def buf_inv(self,nxt=False):
        v=lambda name:self.v(name,nxt)
        pc=v('pc');n=v('count');s0=v('slot0');s1=v('slot1')
        D=self.line('A','latest',nxt);E=self.line('B','latest',nxt);F=self.line('F','latest',nxt)
        # Exact FIFO accounting: only two enqueues, and their drains must happen in order.
        return a(
            f'(<= 0 {pc} 3)',f'(<= 0 {n} 2)',
            o(eq(n,'0'),eq(n,'1'),eq(n,'2')),
            imp(eq(n,'0'),a(eq(s0,'0'),eq(s1,'0'))),
            imp(eq(n,'1'),eq(s1,'0')),
            imp(eq(n,'2'),a(eq(s0,'1'),eq(s1,'2'))),
            imp(eq(pc,'0'),a(eq(n,'0'),eq(D,'0'),eq(E,'0'))),
            imp(eq(pc,'1'),o(a(eq(n,'1'),eq(s0,'1'),eq(D,'0'),eq(E,'0')),
                              a(eq(n,'0'),eq(D,'1'),eq(E,'0')))),
            imp(o(eq(pc,'2'),eq(pc,'3')),
                o(a(eq(n,'2'),eq(D,'0'),eq(E,'0')),
                  a(eq(n,'1'),eq(s0,'2'),eq(D,'1'),eq(E,'0')),
                  a(eq(n,'0'),eq(D,'1'),eq(E,'1')))),
            imp(v('released'),a(eq(pc,'3'),eq(n,'0'),eq(F,'1'))),
            imp(eq(F,'1'),v('released')),
            imp(v('acquired'),v('released')),
            imp(v('read_A'),v('acquired')),
            imp(v('read_B'),v('acquired')),
            imp(v('read_A'),eq(v('rv_A'),'1')),
            imp(v('read_B'),eq(v('rv_B'),'1')),
            o(eq(v('rv_A'),'0'),eq(v('rv_A'),'1')),
            o(eq(v('rv_B'),'0'),eq(v('rv_B'),'1')),
        )
    def inv(self,nxt=False):return a(self.local_inv(nxt),self.buf_inv(nxt))
    def bad(self):
        return o(a('read_A',neg(eq('rv_A','1'))),a('read_B',neg(eq('rv_B','1'))))
    def frame(self,names,patch):
        return a(*(eq(self.v(k,True),patch.get(k,k)) for k in names))
    def transitions(self):
        steps=[]
        for L in self.lines:
            for label,base_form in self.base.transitions():
                if label in ('c0:write','c1:write'):
                    continue
                frozen=[f'{other}_{name}' for other in self.lines if other!=L for name in self.base.keys]+list(self.extra)
                steps.append((f'{L}:{label}',a(self.tr(base_form,L),self.frame(frozen,{}))))
        # Enqueue ordinary stores in program order. A fully occupied FIFO cannot accept another store.
        steps.append(('cpu:enqueue_A', a(eq('pc','0'),eq('count','0'),
                    self.frame(self.keys,{'pc':'1','count':'1','slot0':'1'}))))
        steps.append(('cpu:enqueue_B', a(eq('pc','1'),f'(< count 2)',
                    self.frame(self.keys,{'pc':'2','count':'(+ count 1)',
                      'slot0':'(ite (= count 0) 2 slot0)',
                      'slot1':'(ite (= count 0) 0 2)'}))))
        steps.append(('cpu:issue_release',a(eq('pc','2'),
                    self.frame(self.keys,{'pc':'3'}))))
        # Explicit FIFO drains. Each drain invokes a real coherence write transition of MSI line.
        # This is a store-buffer implementation rule, not a guard requiring specific latest values.
        write_c0=dict(self.base.transitions())['c0:write']
        for L,tag in [('A','1'),('B','2')]:
            unchanged_other=[f'{other}_{name}' for other in self.lines if other!=L for name in self.base.keys]
            unchanged_base=[self.v(f'{L}_{name}',True) for name in ()]
            patch={'count':'(- count 1)','slot0':'slot1','slot1':'0'}
            steps.append((f'cpu:drain_{L}',a(f'(> count 0)',eq('slot0',tag),
                self.tr(write_c0,L),
                self.frame(unchanged_other+list(self.extra),patch))))
        # CAS F=0->1: writer must already have Modified F; then it uses the original MSI write.
        # The correct release waits for FIFO empty; broken mutant skips that ordering rule.
        flush='true' if self.broken else eq('count','0')
        steps.append(('cpu:release_CAS',a(eq('pc','3'),neg('released'),flush,
            eq('F_val_0','0'),self.tr(write_c0,'F'),
            self.frame([f'{other}_{name}' for other in ('A','B') for name in self.base.keys]
                       +list(self.extra),{'released':'true'}))))
        # Read flag through a valid coherent S/M cache line; acquire sees only F=1.
        # Base invariant guarantees any valid S/M copy equals latest per-line version.
        valid_F=a(o(eq('F_mode_1','1'),eq('F_mode_1','2')),eq('F_val_1','1'))
        steps.append(('cpu:acquire_flag',a(neg('acquired'),valid_F,
                      self.frame(self.keys,{'acquired':'true'}))))
        for L in ('A','B'):
            valid=o(eq(f'{L}_mode_1','1'),eq(f'{L}_mode_1','2'))
            steps.append((f'cpu:read_{L}',a('acquired',neg(f'read_{L}'),valid,
                self.frame(self.keys,{f'read_{L}':'true',f'rv_{L}':f'{L}_val_1'}))))
        return steps
    def T(self):return o(*(form for _,form in self.transitions()))
    def query(self,kind):
        if kind=='init': f=a(self.init(),neg(self.inv()))
        elif kind=='step_buffer':f=a(self.inv(),self.T(),neg(self.buf_inv(True)))
        elif kind=='step_full':f=a(self.inv(),self.T(),neg(self.inv(True)))
        elif kind=='safety':f=a(self.inv(),self.bad())
        else:raise ValueError(kind)
        return self.decl()+'\n(assert '+f+')\n(check-sat)\n'
    def _at(self,formula,idx,idx1=None):
        symbols={self.v(k):f'{k}_{idx}' for k in self.keys}
        if idx1 is not None:symbols.update({self.v(k,True):f'{k}_{idx1}' for k in self.keys})
        rx=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(sorted(map(re.escape,symbols),key=len,reverse=True))+r')(?![A-Za-z0-9_])')
        return rx.sub(lambda m:symbols[m.group(0)],formula)
    def trace_query(self,trace,post):
        actions=dict(self.transitions())
        assert all(x in actions for x in trace)
        strings=[self.decl(True,len(trace)+1),'(assert '+self._at(self.init(),0)+')']
        for k,label in enumerate(trace):
            strings.append('(assert '+self._at(actions[label],k,k+1)+')')
        strings.append('(assert '+self._at(post,len(trace))+')')
        return '\n'.join(strings)+'\n(check-sat)\n'

# The mutant publishes the flag even though its two preceding stores are still queued.
BAD_TRACE = [
  'cpu:enqueue_A','cpu:enqueue_B','cpu:issue_release',
  'F:c0:issue_write','F:dir:start_rqW_c0','F:dir:grant_M_c0',
  'F:net:deliver_grM_c0','F:dir:accept_gack_c0','cpu:release_CAS',
  'F:c1:issue_read','F:dir:start_rqR_c1','F:net:deliver_recall_c0',
  'F:dir:accept_wb_c0','F:dir:grant_S_c1','F:net:deliver_grS_c1',
  'F:dir:accept_gack_c1','cpu:acquire_flag',
  'B:c1:issue_read','B:dir:start_rqR_c1','B:dir:grant_S_c1',
  'B:net:deliver_grS_c1','B:dir:accept_gack_c1','cpu:read_B',
]

def load_read(L):
    return [f'{L}:c1:issue_read', f'{L}:dir:start_rqR_c1',
        f'{L}:net:deliver_recall_c0',f'{L}:dir:accept_wb_c0',
        f'{L}:dir:grant_S_c1',f'{L}:net:deliver_grS_c1',
        f'{L}:dir:accept_gack_c1',f'cpu:read_{L}']

def get_M(L):
    return [f'{L}:c0:issue_write',f'{L}:dir:start_rqW_c0',
        f'{L}:dir:grant_M_c0',f'{L}:net:deliver_grM_c0',f'{L}:dir:accept_gack_c0']

GOOD_TRACE = (['cpu:enqueue_A','cpu:enqueue_B','cpu:issue_release']
  +get_M('A')+['cpu:drain_A']
  +get_M('B')+['cpu:drain_B']
  +get_M('F')+['cpu:release_CAS']
  +['F:c1:issue_read','F:dir:start_rqR_c1','F:net:deliver_recall_c0',
     'F:dir:accept_wb_c0','F:dir:grant_S_c1','F:net:deliver_grS_c1',
     'F:dir:accept_gack_c1','cpu:acquire_flag']
  +load_read('A')+load_read('B'))

# A second positive execution: the reader already holds a stale Shared copy
# of B before the writer's update. Coherence invalidates it at the writer's
# exclusive-ownership request; a post-acquire read obtains the new value.
STALLED_COPY_GOOD_TRACE = (
  ['B:c1:issue_read','B:dir:start_rqR_c1','B:dir:grant_S_c1',
   'B:net:deliver_grS_c1','B:dir:accept_gack_c1',
   'cpu:enqueue_A','cpu:enqueue_B','cpu:issue_release']
  +get_M('A')+['cpu:drain_A']
  +['B:c0:issue_write','B:dir:start_rqW_c0',
    'B:net:deliver_inv_c1','B:dir:accept_ack_c1',
    'B:dir:grant_M_c0','B:net:deliver_grM_c0',
    'B:dir:accept_gack_c0','cpu:drain_B']
  +get_M('F')+['cpu:release_CAS']
  +['F:c1:issue_read','F:dir:start_rqR_c1','F:net:deliver_recall_c0',
     'F:dir:accept_wb_c0','F:dir:grant_S_c1','F:net:deliver_grS_c1',
     'F:dir:accept_gack_c1','cpu:acquire_flag']
  +load_read('A')+load_read('B'))

def run(folder):
    os.makedirs(folder,exist_ok=True)
    record={'tool':'Z3 4.x via libz3.so.4','scope':'2 cores, 3 lines (A,B,F), 2-entry FIFO, 2 stores + 1 release CAS; arbitrary transition count'}
    for broken in (False,True):
        name='mutant' if broken else 'correct'
        obj=FIFOProof(broken)
        results={}
        qs=['init','step_buffer','safety'] if not broken else ['step_buffer']
        # Full conjunctive check is separately useful and can be expensive.
        if not broken:qs.append('step_full')
        for q in qs:
            form=obj.query(q)
            fp=os.path.join(folder,f'{name}_{q}.smt2')
            with open(fp,'w') as f:f.write(form)
            t=time.monotonic(); raw=z3_smt(form);elapsed=time.monotonic()-t
            results[q]={'result':raw.splitlines()[0].strip(),'seconds':round(elapsed,3),'bytes':len(form)}
            if results[q]['result'] not in ('unsat','sat'):
                results[q]['output']=raw[:2000]
            print(name,q,results[q],flush=True)
        q=obj.trace_query(BAD_TRACE,obj.bad())
        fp=os.path.join(folder,name+'_bad_trace.smt2')
        with open(fp,'w') as f:f.write(q)
        t=time.monotonic(); raw=z3_smt(q)
        results['bad_trace']={'result':raw.splitlines()[0].strip(),'length':len(BAD_TRACE),'seconds':round(time.monotonic()-t,3)}
        print(name,'bad_trace',results['bad_trace'],flush=True)
        if not broken:
            q=obj.trace_query(GOOD_TRACE,a('read_A','read_B',eq('rv_A','1'),eq('rv_B','1')))
            fp=os.path.join(folder,name+'_good_trace.smt2')
            with open(fp,'w') as f:f.write(q)
            t=time.monotonic();raw=z3_smt(q)
            results['good_trace']={'result':raw.splitlines()[0].strip(),'length':len(GOOD_TRACE),'seconds':round(time.monotonic()-t,3)}
            print(name,'good_trace',results['good_trace'],flush=True)
            q=obj.trace_query(STALLED_COPY_GOOD_TRACE,a('read_A','read_B',eq('rv_A','1'),eq('rv_B','1')))
            with open(os.path.join(folder,name+'_stale_copy_good_trace.smt2'),'w') as f:f.write(q)
            t=time.monotonic();raw=z3_smt(q)
            results['stale_copy_good_trace']={'result':raw.splitlines()[0].strip(),'length':len(STALLED_COPY_GOOD_TRACE),'seconds':round(time.monotonic()-t,3)}
            print(name,'stale_copy_good_trace',results['stale_copy_good_trace'],flush=True)
        record[name]=results
    with open(os.path.join(folder,'results.json'),'w') as f:json.dump(record,f,indent=2)
    return record

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output-dir',default='/mnt/data/fifo_order_proof')
    args=p.parse_args();r=run(args.output_dir)
    assert r['correct']['init']['result']=='unsat'
    assert r['correct']['step_buffer']['result']=='unsat'
    assert r['correct']['step_full']['result']=='unsat'
    assert r['correct']['safety']['result']=='unsat'
    assert r['correct']['bad_trace']['result']=='unsat'
    assert r['correct']['good_trace']['result']=='sat'
    assert r['correct']['stale_copy_good_trace']['result']=='sat'
    assert r['mutant']['bad_trace']['result']=='sat'
    assert r['mutant']['step_buffer']['result']=='sat'
    print('ALL EXPECTED OUTCOMES CONFIRMED',flush=True)
