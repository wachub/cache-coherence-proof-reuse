"""MESI/MOESI versions of the original verified abstract multicore frontend.

Only the per-line coherence state machine and the guards affected by E/O are
changed. The two-entry speculative store queue, forwarding/replay discipline,
mutable ghost arrays, and RR arbiter are inherited from v1.7.
"""
from __future__ import annotations
import re
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
for p in (ROOT/'experiments/09_combined_speculative_reads_writes', ROOT/'tools',Path(__file__).parent):
    sys.path.insert(0,str(p))
from temporal_v17_verify import TemporalFairSpec
from cache_smt_verifier import a,o,neg,eq,imp
from extended_protocol import ExtendedProtocol

class ExtendedFairSpec(TemporalFairSpec):
    def __init__(self,cores=4,lines=2,variant='MESI',unfair_arbiter=False):
        super().__init__(cores,lines,unfair_arbiter=unfair_arbiter)
        self.variant=variant
        replacement=ExtendedProtocol(cores,variant=variant)
        assert replacement.keys==self.p.keys, 'interface state must remain unchanged'
        self.p=replacement

    def _valid(self,m):
        return o(*(eq(m,str(z)) for z in (1,2,3,*([4] if self.variant=='MOESI' else []))))

    def step(self,label,guard,patch):
        # The old CPU frontend has a single architectural instruction in flight.
        # E->M local write/atomic success is a silent directory transition.
        match=re.fullmatch(r'core(\d+):(ask_write|complete_read|complete_store|complete_cas)_line(\d+)',label)
        if match:
            c,op,l=int(match[1]),match[2],int(match[3])
            mode=self.pl(l,'mode',c)
            if op=='ask_write':
                prev=o(eq(mode,'0'),eq(mode,'1'))
                guard=guard.replace(prev,o(prev,eq(mode,'4'))) if self.variant=='MOESI' else guard
            elif op=='complete_read':
                prev=o(eq(mode,'1'),eq(mode,'2'))
                assert prev in guard, (label,guard)
                guard=guard.replace(prev,self._valid(mode))
            elif op in ('complete_store','complete_cas'):
                old=eq(mode,'2')
                assert old in guard,(label,guard)
                guard=guard.replace(old,o(old,eq(mode,'3')))
                if op=='complete_store':
                    patch=dict(patch,**{f'l{l}__mode_{c}':'2'})
                else:
                    value=self.pl(l,'val',c)
                    success=eq(f'(select payload_{l} {value})',self.cpu(c,'expected'))
                    patch=dict(patch,**{f'l{l}__mode_{c}':f'(ite {success} 2 {mode})'})
        if getattr(self,'_guard_log',None) is not None:
            fixed=guard
            mo=re.fullmatch(r'core(\d+):complete_(store|cas)_line(\d+)',label)
            if mo:
                c,l=int(mo[1]),int(mo[3]);fresh=f'(+ {self.pl(l,"latest")} 1)'
                old_required=eq(f'(select payload_{l} {fresh})',self.cpu(c,'newval'))
                assert old_required in fixed,label
                fixed=fixed.replace(old_required,'true')
            self._guard_log[label]=fixed
        return super().step(label,guard,patch)

    def delta_steps(self,mutant=None):
        # The old speculative frontend is unchanged except that a valid cache
        # line may now carry E/O permission in addition to S/M.
        result=[]
        for label,form in super().delta_steps(mutant=mutant):
            for c in range(self.n):
                for l in range(self.k):
                    m=self.pl(l,'mode',c)
                    old=o(eq(m,'1'),eq(m,'2'))
                    if old in form:form=form.replace(old,self._valid(m))
                    if getattr(self,'_guard_log',None) is not None and label in self._guard_log:
                        self._guard_log[label]=self._guard_log[label].replace(old,self._valid(m))
            result.append((label,form))
        return result

    def effective_frontend_guards(self):
        self._guard_log={}
        try:
            self.inherited_steps()
            self.delta_steps()
            return dict(self._guard_log)
        finally:
            self._guard_log=None
