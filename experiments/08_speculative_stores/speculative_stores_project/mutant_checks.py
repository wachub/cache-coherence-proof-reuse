#!/usr/bin/env python3
"""Single-step SMT checks detect violating protocol modifications."""
import json, os, time
from speculative_store_delta import SpecStore, a, o, neg, z3_smt

def main():
    directory=os.path.join(os.path.dirname(__file__),'mutants')
    os.makedirs(directory,exist_ok=True)
    x=SpecStore(4,2)
    lawful=x.legal_queue_retirement_projection()
    inv=a(x.q_inv(),super(SpecStore,x).inv())
    results={}
    for kind,step in [('unresolved',x.delta_steps(unsafe_unresolved=True)),
                      ('tail_first',x.delta_steps(unsafe_second_first=True))]:
        steps=[expr for label,expr in step if ':BUG_' in label]
        formula=a(inv,o(*steps),neg(lawful))
        query=x.declarations()+'\n(assert '+formula+')\n(check-sat)\n'
        filename=f'{kind}_violates_program_order.smt2'
        open(os.path.join(directory,filename),'w').write(query)
        t=time.monotonic();response=z3_smt(query).strip().splitlines()[0]
        results[kind]={'query_result':response,'elapsed_seconds':round(time.monotonic()-t,4),
                       'file':filename,
                       'interpretation':'SAT here means a candidate transition breaks the verified queue-retirement contract'}
    open(os.path.join(directory,'results.json'),'w').write(json.dumps(results,indent=2))
    print(json.dumps(results,indent=2))
if __name__=='__main__':main()
