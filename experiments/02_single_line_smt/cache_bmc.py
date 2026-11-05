#!/usr/bin/env python3
"""Bounded model checking of the same SMT transition relation; example mutant witness."""
import argparse,json,re,time
from cache_smt_verifier import Protocol,z3_smt,o

def smt_at(p,expr,t,next_t=None):
    replacements={p.v(k):f'{k}_t{t}' for k in p.keys}
    if next_t is not None:
        replacements.update({p.v(k,True):f'{k}_t{next_t}' for k in p.keys})
    regex=re.compile(r'(?<![A-Za-z0-9_])(?:'+ '|'.join(re.escape(k) for k in sorted(replacements,key=len,reverse=True))+r')(?![A-Za-z0-9_])')
    return regex.sub(lambda m:replacements[m.group()],expr)

def smt_depth(p,depth,double_writer=False):
    declarations='\n'.join(f'(declare-const {k}_t{i} {typ})'
        for i in range(depth+1) for k,typ in p.types.items())
    clauses=[smt_at(p,p.init(),0)]+[smt_at(p,p.T(),i,i+1) for i in range(depth)]
    clauses.append(o(*(smt_at(p,p.double_writer() if double_writer else p.bad(),i) for i in range(depth+1))))
    return declarations+'\n'+ '\n'.join(f'(assert {clause})' for clause in clauses)+'\n(check-sat)\n'

def get_witness(p, smt, depth):
    raw=z3_smt(smt+'(get-model)\n')
    pat=re.compile(r'\(define-fun ([a-zA-Z_0-9]+) \(\) (Bool|Int)\s+(true|false|\d+|\(- 1\))\)')
    vals={m.group(1):m.group(3) for m in pat.finditer(raw)}
    def val(k,t):return vals.get(f'{k}_t{t}','?')
    states=[]
    for t in range(depth+1):
        cores=[]
        for c in range(p.n):
            cores.append({'cache':c,'mode':{'0':'I','1':'S','2':'M'}.get(val(f'mode_{c}',t),'?'),
                          'value':val(f'val_{c}',t),'pending':val(f'pending_{c}',t),
                          'sharer':val(f'share_{c}',t)})
        state={'step':t,'transaction':val('tx',t),'kind':val('kind',t),
               'phase':val('phase',t),'directory_owner':val('owner',t),
               'directory_memory':val('mem',t),'latest':val('latest',t),'cores':cores}
        states.append(state)
    for t in range(1,depth+1):
        changes=[k for k in p.keys if val(k,t-1)!=val(k,t)]
        def changed(k):return k in changes
        if changed('latest'):action='Core performs local write'
        elif changed('tx') and val('tx',t-1)=='(- 1)':action='Directory begins a request transaction'
        elif changed('tx') and val('tx',t)=='(- 1)':action='Directory receives grant acknowledgment'
        elif changed('phase') and val('phase',t)=='1':action='Directory issues grant'
        elif any(changed(f'pending_{c}') and val(f'pending_{c}',t)=='true' for c in range(p.n)):
            action='Core issues read/write request'
        elif any(changed(f'mode_{c}') and val(f'mode_{c}',t)=='2' for c in range(p.n)):
            action='Core receives Modified grant'
        elif any(changed(f'mode_{c}') and val(f'mode_{c}',t)=='1' for c in range(p.n)):
            action='Core receives Shared grant'
        elif any(changed(f'wb_{c}') for c in range(p.n)):action='Dirty writeback transfer'
        else:action='Network or acknowledgment step'
        states[t]['event']=action
    states[0]['event']='Initial state'
    return states

def run_bmc(n=2,limit=12,early_grant=True,outfile=None,double_writer=False):
    p=Protocol(n,2,early_grant)
    findings=[]
    for d in range(limit+1):
        smt=smt_depth(p,d,double_writer)
        if outfile and d==limit:
            open(outfile,'w').write(smt)
        t=time.monotonic();out=z3_smt(smt).splitlines()[0]
        findings.append({'depth':d,'result':out,'seconds':round(time.monotonic()-t,3)})
        if out=='sat':
            if outfile:open(outfile,'w').write(smt)
            return {'result':'COUNTEREXAMPLE','first_depth':d,'checks':findings,
                    'witness_states':get_witness(p,smt,d)}
        if out!='unsat':break
    return {'result':'NO_COUNTEREXAMPLE_TO_DEPTH','checks':findings}

if __name__=='__main__':
    a=argparse.ArgumentParser()
    a.add_argument('--cores',type=int,default=2)
    a.add_argument('--limit',type=int,default=12)
    a.add_argument('--correct',action='store_true')
    a.add_argument('--double-writer',action='store_true')
    a.add_argument('--outfile',default='/mnt/data/cache_bmc_witness.smt2')
    x=a.parse_args()
    print(json.dumps(run_bmc(x.cores,x.limit,not x.correct,x.outfile,x.double_writer),indent=2))
