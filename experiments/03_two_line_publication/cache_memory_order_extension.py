#!/usr/bin/env python3
"""Two-line memory-ordering extension of the original MSI-style SMT protocol.

Uses the ORIGINAL Protocol transition system from cache_smt_verifier.py unchanged,
instantiated independently for two lines D and F. Adds processor-level program
order, a 2-entry FIFO store buffer (abstracted by enqueue and drain flags),
release CAS (F:0->1 after D=1 drains), and acquire (reader observes F=1 and reads D).

The checks use libz3.so.4 via ctypes and SMT-LIB2. The proof is unbounded in
transition count for exactly two caches and two lines, bounded to one write
per line. No claim of general ISA/RTL correctness or liveness is made.
"""
import argparse
import json
import os
import re
import sys
import time
from cache_smt_verifier import Protocol, a, o, neg, eq, imp, z3_smt


def fmtbool(flag):
    return 'true' if flag else 'false'


class MemoryOrderExtension:
    def __init__(self, broken_release=False):
        self.base = Protocol(n=2, max_version=1, early_grant=False)
        self.lines = ('D', 'F')
        self.broken_release = broken_release
        self.wflags = {
            'enq_D': 'Bool', 'enq_F': 'Bool',
            'done_D': 'Bool', 'done_F': 'Bool',
            'saw_F': 'Bool', 'read_D': 'Bool', 'read_value': 'Int',
        }
        self.vars = {f'{line}_{k}':v for line in self.lines for k,v in self.base.types.items()}
        self.vars.update(self.wflags)
        self.keys = list(self.vars)
        self.symbol_re = re.compile(r'\b('+'|'.join(sorted(map(re.escape,self.base.keys),key=len,reverse=True))+r')(_next)?\b')
    def tr(self, term, line):
        return self.symbol_re.sub(lambda m:line+'_'+m.group(1)+(m.group(2) or ''), term)
    def V(self, k, nxt=False):
        return k+('_next' if nxt else '')
    def linevar(self, line, k, nxt=False):
        return self.V(f'{line}_{k}',nxt)
    def declarations(self, indexed=False, count=2):
        if indexed:
            return '\n'.join(f'(declare-const {k}_{i} {v})' for i in range(count) for k,v in self.vars.items())
        return '\n'.join(f'(declare-const {self.V(k,nxt)} {v})' for nxt in (False,True) for k,v in self.vars.items())
    def init(self):
        return a(*(self.tr(self.base.init(),line) for line in self.lines),
                 *(eq(k,'0' if v=='Int' else 'false') for k,v in self.wflags.items()))
    def local_invariant(self,nxt=False):
        return a(*(self.tr(self.base.inv(nxt),line) for line in self.lines))
    def ordering_invariant(self,nxt=False):
        v=lambda k:self.V(k,nxt)
        dl=self.linevar('D','latest',nxt); fl=self.linevar('F','latest',nxt)
        return a(
            imp(v('enq_F'),v('enq_D')),
            imp(v('done_D'),eq(dl,'1')),
            imp(eq(dl,'1'),v('done_D')),
            imp(v('done_F'),eq(fl,'1')),
            imp(eq(fl,'1'),v('done_F')),
            imp(v('done_F'),v('done_D')),
            imp(v('saw_F'),v('done_F')),
            imp(v('read_D'),v('saw_F')),
            imp(v('read_D'),eq(v('read_value'),'1')),
            o(eq(v('read_value'),'0'),eq(v('read_value'),'1')),
        )
    def bad(self,nxt=False):
        v=lambda k:self.V(k,nxt)
        return a(v('read_D'),neg(eq(v('read_value'),'1')))
    def _frame(self, names, patch):
        return a(*(eq(self.V(k,True),patch.get(k,k)) for k in names))
    def step(self,label,guard,patch,base_formula=None,affected_line=None):
        if affected_line is None:
            return (label,a(guard,self._frame(self.keys,patch)))
        other='F' if affected_line=='D' else 'D'
        frozen=[f'{other}_{k}' for k in self.base.keys]+list(self.wflags)
        return label,a(guard,base_formula,self._frame(frozen,patch))
    def transitions(self):
        steps=[]
        for line in self.lines:
            for label,formula in self.base.transitions():
                # Local writes are issued ONLY by Core 0, after buffer enqueues.
                # All other original cache/directory transitions remain unchanged.
                if label=='c1:write':
                    continue
                guard='true';patch={}
                if label=='c0:write':
                    guard=a(self.V('enq_'+line),neg(self.V('done_'+line)))
                    if line=='F':
                        # Successful CAS(flag, expected=0, new=1): the line
                        # must be exclusively owned and contain the expected value.
                        guard=a(guard,eq('F_val_0','0'))
                        if not self.broken_release:
                            # FIFO store-buffer drain + release ordering.
                            guard=a(guard,self.V('done_D'))
                    patch['done_'+line]='true'
                steps.append(self.step(line+':'+label,guard,patch,self.tr(formula,line),line))
        steps.append(self.step('cpu:enqueue_data',neg('enq_D'),{'enq_D':'true'}))
        steps.append(self.step('cpu:enqueue_flag',a('enq_D',neg('enq_F')),{'enq_F':'true'}))
        # The original per-line coherence proof ensures visible S/M copies
        # match the latest logical value, even with arbitrary in-flight messages.
        flag_visible=a(o(eq('F_mode_1','1'),eq('F_mode_1','2')),eq('F_val_1','1'))
        data_visible=o(eq('D_mode_1','1'),eq('D_mode_1','2'))
        steps.append(self.step('cpu:acquire_flag',a(neg('saw_F'),flag_visible),{'saw_F':'true'}))
        steps.append(self.step('cpu:read_data',a('saw_F',neg('read_D'),data_visible),
                               {'read_D':'true','read_value':'D_val_1'}))
        return steps
    def transition(self):
        return o(*(f for _,f in self.transitions()))
    def obligation(self,goal):
        if goal=='initial':terms=[self.init(),neg(self.ordering_invariant())]
        elif goal=='step':terms=[self.local_invariant(),self.ordering_invariant(),
                                 self.transition(),neg(self.ordering_invariant(True))]
        elif goal=='safety':terms=[self.local_invariant(),self.ordering_invariant(),self.bad()]
        elif goal=='full_step':terms=[self.local_invariant(),self.ordering_invariant(),
                                      self.transition(),neg(a(self.local_invariant(True),self.ordering_invariant(True)))]
        else:raise ValueError(goal)
        return self.declarations()+'\n'+'\n'.join('(assert '+t+')' for t in terms)+'\n(check-sat)\n'
    def _at(self, formula, idx, nxtidx=None):
        mapping={self.V(k):f'{k}_{idx}' for k in self.keys}
        if nxtidx is not None:
            mapping.update({self.V(k,True):f'{k}_{nxtidx}' for k in self.keys})
        keys=sorted(mapping,key=len,reverse=True)
        reg=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(map(re.escape,keys))+r')(?![A-Za-z0-9_])')
        return reg.sub(lambda m:mapping[m.group(1)],formula)
    def trace_formula(self, labels, require_bad=True):
        by_name=dict(self.transitions())
        missing=[name for name in labels if name not in by_name]
        if missing:raise ValueError('Unknown labels: '+str(missing))
        strings=[self.declarations(True,len(labels)+1),
                 '(assert '+self._at(self.init(),0)+')']
        for i,label in enumerate(labels):
            strings.append('(assert '+self._at(by_name[label],i,i+1)+')')
        goal=self.bad() if require_bad else a('read_D',eq('read_value','1'))
        strings.append('(assert '+self._at(goal,len(labels))+')')
        strings.append('(check-sat)')
        return '\n'.join(strings)+'\n'

# A physically motivated schedule for the broken controller: the flag
# becomes visible before the writer's queued data store has drained.
MUTANT_TRACE=[
    'cpu:enqueue_data',
    'cpu:enqueue_flag',
    'D:c1:issue_read', 'D:dir:start_rqR_c1', 'D:dir:grant_S_c1',
    'D:net:deliver_grS_c1', 'D:dir:accept_gack_c1',
    'F:c0:issue_write', 'F:dir:start_rqW_c0', 'F:dir:grant_M_c0',
    'F:net:deliver_grM_c0', 'F:dir:accept_gack_c0',
    'F:c0:write',
    'F:c1:issue_read', 'F:dir:start_rqR_c1',
    'F:net:deliver_recall_c0', 'F:dir:accept_wb_c0',
    'F:dir:grant_S_c1', 'F:net:deliver_grS_c1',
    'F:dir:accept_gack_c1',
    'cpu:acquire_flag',
    'cpu:read_data'
]


POSITIVE_TRACE=[
    'cpu:enqueue_data', 'cpu:enqueue_flag',
    'D:c1:issue_read', 'D:dir:start_rqR_c1', 'D:dir:grant_S_c1',
    'D:net:deliver_grS_c1', 'D:dir:accept_gack_c1',
    'D:c0:issue_write', 'D:dir:start_rqW_c0',
    'D:net:deliver_inv_c1', 'D:dir:accept_ack_c1',
    'D:dir:grant_M_c0', 'D:net:deliver_grM_c0',
    'D:dir:accept_gack_c0', 'D:c0:write',
    'F:c0:issue_write', 'F:dir:start_rqW_c0', 'F:dir:grant_M_c0',
    'F:net:deliver_grM_c0', 'F:dir:accept_gack_c0', 'F:c0:write',
    'F:c1:issue_read', 'F:dir:start_rqR_c1',
    'F:net:deliver_recall_c0', 'F:dir:accept_wb_c0',
    'F:dir:grant_S_c1', 'F:net:deliver_grS_c1',
    'F:dir:accept_gack_c1', 'cpu:acquire_flag',
    'D:c1:issue_read', 'D:dir:start_rqR_c1',
    'D:net:deliver_recall_c0', 'D:dir:accept_wb_c0',
    'D:dir:grant_S_c1', 'D:net:deliver_grS_c1',
    'D:dir:accept_gack_c1', 'cpu:read_data',
]

def run(outdir='/mnt/data'):
    os.makedirs(outdir,exist_ok=True)
    results={}
    for broken in (False,True):
        m=MemoryOrderExtension(broken_release=broken)
        prefix='mutant' if broken else 'correct'
        checks={}
        for goal in (['initial','step','safety','full_step'] if not broken else ['step']):
            smt=m.obligation(goal)
            path=os.path.join(outdir,f'{prefix}_{goal}.smt2')
            with open(path,'w') as f:f.write(smt)
            t=time.monotonic()
            output=z3_smt(smt)
            checks[goal]={'result':output.splitlines()[0].strip(),
                          'seconds':round(time.monotonic()-t,3),
                          'bytes':len(smt)}
        witness=m.trace_formula(MUTANT_TRACE)
        with open(os.path.join(outdir,f'{prefix}_witness.smt2'),'w') as f:f.write(witness)
        t=time.monotonic();output=z3_smt(witness)
        checks['counterexample_trace']={'result':output.splitlines()[0].strip(),
                                        'seconds':round(time.monotonic()-t,3),
                                        'steps':len(MUTANT_TRACE)}
        if not broken:
            positive=m.trace_formula(POSITIVE_TRACE,require_bad=False)
            with open(os.path.join(outdir,'correct_positive_trace.smt2'),'w') as f:f.write(positive)
            t=time.monotonic();result=z3_smt(positive)
            checks['positive_trace']={'result':result.splitlines()[0].strip(),
                                      'seconds':round(time.monotonic()-t,3),
                                      'steps':len(POSITIVE_TRACE)}
        results[prefix]=checks
    with open(os.path.join(outdir,'memory_order_results.json'),'w') as f:json.dump(results,f,indent=2)
    return results

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--output-dir',default='/mnt/data/cache_order_model')
    args=p.parse_args()
    results=run(args.output_dir)
    print(json.dumps(results,indent=2))
    ok=(all(results['correct'][k]['result']=='unsat' for k in ('initial','step','safety','full_step'))
        and results['mutant']['step']['result']=='sat'
        and results['mutant']['counterexample_trace']['result']=='sat'
        and results['correct']['counterexample_trace']['result']=='unsat'
        and results['correct']['positive_trace']['result']=='sat')
    if not ok:
        print('Unexpected result; inspect SMT obligations.',file=sys.stderr)
        sys.exit(1)
