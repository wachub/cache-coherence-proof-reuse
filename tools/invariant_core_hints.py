#!/usr/bin/env python3
"""Mine Z3 UNSAT-core hints for speculative-state invariant clauses.

Diagnostic / optional performance experiment, NOT a replacement theorem or a
sound general-purpose cone-of-influence reduction for changed transition sets.
A pruned query is still re-solved below; each *new* feature must be rechecked.
"""
from pathlib import Path
import argparse
import json
import re
import sys
import time

sys.path.insert(0,str(Path(__file__).parent))
from fast_verify import load_combined, eval_z3, _read_statuses


def top_and(expr: str) -> list[str]:
    """Split only one outer (and ...) from generated SMT expressions."""
    expr=expr.strip()
    if not expr.startswith('(and ') or not expr.endswith(')'):
        return [expr]
    body=expr[5:-1].strip()
    terms=[];i=0
    while i<len(body):
        while i<len(body) and body[i].isspace():i+=1
        if i>=len(body):break
        start=i
        if body[i]=='(':
            depth=0
            while i<len(body):
                if body[i]=='(':depth+=1
                elif body[i]==')':
                    depth-=1
                    if depth==0:
                        i+=1
                        break
                i+=1
            if depth:raise ValueError('Unbalanced SMT formula')
        else:
            while i<len(body) and not body[i].isspace():i+=1
        terms.append(body[start:i])
    return terms


def mine(model):
    from sc_msi_4core_verifier import System, a, o, neg
    before=time.monotonic()
    parts={'old_msi_invariant':System.inv(model),
           'delta_transitions':o(*(e for _,e in model.delta_steps())),
           'violation':neg(model.new_inv(True))}
    spec_parts=top_and(model.new_inv())
    for i,part in enumerate(spec_parts):parts[f'spec_inv_{i:03}']=part
    script='(set-option :produce-unsat-cores true)\n(set-option :smt.core.minimize true)\n'+model.declarations()+'\n'
    for key,expr in parts.items():script+=f'(assert (! {expr} :named {key}))\n'
    script+='(check-sat)\n(get-unsat-core)\n'
    out=eval_z3(script)
    lines=[line.strip() for line in out.splitlines() if line.strip()]
    if not lines or lines[0]!='unsat':
        raise RuntimeError('Core mining requires an UNSAT obligation; got '+out[:300])
    core=set(re.findall(r'[a-zA-Z_][a-zA-Z0-9_]*', '\n'.join(lines[1:])))
    unknown=core-set(parts)
    if unknown:raise RuntimeError('Unknown UNSAT-core names: '+repr(unknown))
    reduced='\n'.join('(assert '+parts[k]+')' for k in parts if k in core)
    # Critical: actually recheck the weaker formula, never trust only core metadata.
    verify=eval_z3(model.declarations()+'\n'+reduced+'\n(check-sat)\n')
    if _read_statuses(verify,1)!=['unsat']:
        raise RuntimeError('Core verification failed: '+repr(verify))
    retained=sorted(core)
    return {'cores':model.n,'lines':model.k,'initial_spec_clauses':len(spec_parts),
            'retained_spec_clauses':sum(k.startswith('spec_inv_') for k in core),
            'total_assumptions':len(parts),'core_size':len(core),
            'retained_assertions':retained,'reduced_query_rechecked':'unsat',
            'seconds':round(time.monotonic()-before,4),
            'warning':'Core valid only for this exact UNSAT query. Not an arbitrary-feature proof or generally inductive subset.'}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cores',type=int,default=4)
    p.add_argument('--lines',type=int,default=2)
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    result=mine(load_combined(args.cores,args.lines))
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
