#!/usr/bin/env python3
"""v1.6 experimental repair: round-robin directory + mutable ghost payloads.

This deliberately creates a NEW transition system. v1.5 remains available as a
negative-control baseline. The arrays are specification ghost state, not RTL.
"""
from __future__ import annotations
import re
import sys
from pathlib import Path
BASE = Path(__file__).resolve().parents[1] / '09_combined_speculative_reads_writes'
sys.path.insert(0, str(BASE))
from combined_speculative_model import CombinedSpec
from sc_msi_4core_verifier import System
from cache_smt_verifier import a, o, neg, eq, ge, le

class FairProgressSpec(CombinedSpec):
    def __init__(self, cores=4, lines=2, unfair_arbiter=False):
        if cores < 1 or lines < 1:
            raise ValueError('cores, lines must be positive')
        super().__init__(cores, lines)
        self.unfair_arbiter = unfair_arbiter
        for l in range(lines):
            self.types[f'payload_{l}'] = '(Array Int Int)'
            self.keys.append(f'payload_{l}')
            self.types[f'l{l}__rr_turn'] = 'Int'
            self.keys.append(f'l{l}__rr_turn')

    def declarations(self):
        # Unlike the inherited model, the payload ghost arrays are stateful.
        return '\n'.join(f'(declare-const {self.v(key,nxt)} {typ})'
            for nxt in (False,True) for key,typ in self.types.items())

    def init(self):
        return a(super().init(),*(eq(self.v(f'l{l}__rr_turn'),'0') for l in range(self.k)))

    def inv(self,nxt=False):
        return a(System.inv(self,nxt), self.new_inv(nxt),
            *(a(ge(self.v(f'l{l}__rr_turn',nxt),'0'),
                 le(self.v(f'l{l}__rr_turn',nxt),str(self.n-1))) for l in range(self.k)))

    def new_inv(self, nxt=False):
        expr=super().new_inv(nxt)
        # Captured speculative values refer to the *current* ghost array in
        # the state being described. Needed for induction across writes.
        if nxt:
            expr = re.sub(r'\bpayload_(\d+)\b', r'payload_\1_next', expr)
        bounds=[]
        for c in range(self.n):
            for l in range(self.k):
                bounds.append(f'(=> (and {self.x(c,"load_active",nxt)} '
                    f'(= {self.x(c,"load_kind",nxt)} 0) '
                    f'(= {self.x(c,"load_addr",nxt)} {l})) '
                    f'(<= {self.x(c,"load_version",nxt)} {self.pl(l,"latest",nxt=nxt)}))')
        return a(expr,*bounds)

    def step(self,label,guard,patch):
        # Eliminate the old immutable-array representability guard; the store
        # itself sets the fresh version's data in the next ghost array.
        match = re.fullmatch(r'core(\d+):complete_(store|cas)_line(\d+)',label)
        if match:
            c,kind,l = int(match[1]), match[2],int(match[3])
            fresh=f'(+ {self.pl(l,"latest")} 1)'
            old_required=eq(f'(select payload_{l} {fresh})',self.cpu(c,'newval'))
            if old_required not in guard:
                raise AssertionError(f'expected old payload guard missing from {label}')
            guard=guard.replace(old_required,'true')
            written=f'(store payload_{l} {fresh} {self.cpu(c,"newval")})'
            if kind=='cas':
                oldval=self.pl(l,'val',c)
                succeeds=eq(f'(select payload_{l} {oldval})',self.cpu(c,'expected'))
                written=f'(ite {succeeds} {written} payload_{l})'
            patch=dict(patch,**{f'payload_{l}':written})
        return super().step(label,guard,patch)

    def _rr_selected(self,line,c):
        if self.unfair_arbiter: return "true"  # deliberate negative control
        turn=self.v(f'l{line}__rr_turn')
        branches=[]
        for t in range(self.n):
            before=[]
            for offset in range(self.n):
                j=(t+offset)%self.n
                if j==c: break
                before.extend([neg(self.pl(line,'rqR',j)),neg(self.pl(line,'rqW',j))])
            branches.append(a(eq(turn,str(t)),*before))
        return o(*branches)

    def steps(self):
        # Network transitions from the original model do not touch the new
        # per-line RR pointer, so explicitly frame or advance it here.
        result=[]
        for label,formula in super().steps():
            is_start=re.fullmatch(r'l(\d+)::dir:start_rq[RW]_c(\d+)',label)
            line_action=re.match(r'l(\d+)::',label)
            changes=[]
            if is_start:
                l,c=int(is_start[1]),int(is_start[2])
                formula=a(formula,self._rr_selected(l,c))
                changes.append(eq(self.v(f'l{l}__rr_turn',True),str((c+1)%self.n)))
            if line_action:
                l=int(line_action[1])
                if not is_start:
                    changes.append(eq(self.v(f'l{l}__rr_turn',True),self.v(f'l{l}__rr_turn')))
            # Non-line transitions use self.step(), which already frames pointer.
            result.append((label,a(formula,*changes) if changes else formula))
        return result

    def T(self):
        return o(*(t for _,t in self.steps()))
