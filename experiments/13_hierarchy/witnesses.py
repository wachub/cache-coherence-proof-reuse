#!/usr/bin/env python3
"""Reachable SAT traces and deliberate hierarchy fault witnesses."""
import json,re,sys,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(Path(__file__).resolve().parent))
sys.path.insert(0,str(ROOT/'experiments/09_combined_speculative_reads_writes'))
from hierarchy import Hierarchy,AND,NOT,EQ
from cache_smt_verifier import z3_smt


def trace(m,labels,target,od,name,write_value=7,expect_sat=True):
    od.mkdir(parents=True,exist_ok=True)
    symbols=sorted([k+('_next' if nxt else '') for k in m.keys for nxt in (True,False)],key=len,reverse=True)
    patt=re.compile(r'(?<![A-Za-z0-9_])('+ '|'.join(map(re.escape,symbols))+
        r'|input_value|input_expected)(?![A-Za-z0-9_])')
    def rename(f,t):
        def replacement(mt):
            k=mt.group(0)
            if k=='input_value':return f'input_value_{t}'
            if k=='input_expected':return f'input_expected_{t}'
            if k.endswith('_next'):return k[:-5]+'_'+str(t+1)
            return k+'_'+str(t)
        return patt.sub(replacement,f)
    count=len(labels)
    decl='\n'.join(f'(declare-const {k}_{t} {typ})' for t in range(count+1) for k,typ in m.types.items())
    decl+='\n'+'\n'.join(f'(declare-const input_{nm}_{t} Int)' for t in range(count)
            for nm in ('value','expected'))
    all_steps=dict(m.steps())
    goals=[rename(m.init(),0)]
    for t,label in enumerate(labels):
        goals.append(rename(all_steps[label],t))
        goals.append(f'(= input_value_{t} {write_value})')
    # State-only final assertion; add '+1' to index via two-state renamer.
    goals.append(rename(target,count))
    query='(set-option :timeout 30000)\n'+decl+'\n'+'\n'.join('(assert '+g+')' for g in goals)+'\n(check-sat)\n'
    (od/(name+'.smt2')).write_text(query)
    out=z3_smt(query).strip();status=out.splitlines()[0] if out else 'error'
    result={'name':name,'status':status,'expected':'sat' if expect_sat else 'unsat',
            'passed':status==('sat' if expect_sat else 'unsat'),
            'trace':labels,'variant':m.variant,'topology':m.top.summary(),
            'sha256':hashlib.sha256(query.encode()).hexdigest()}
    if not result['passed']:raise AssertionError(result)
    return result


def run(od):
    m=Hierarchy((2,2),'MESI');w=[]
    w.append(trace(m,['core0:issue_read','core0:serve_read','core0:issue_write','core0:serve_write'],
        AND(EQ(m.c(0,'mode'),'2'),EQ(m.v('latest'),'1'),EQ(m.v('mem'),'0')),
        od,'mesi_exclusive_local_write'))
    w.append(trace(m,['core0:issue_write','core0:serve_write','core2:issue_read','core2:serve_read'],
        AND(EQ(m.c(0,'mode'),'1'),EQ(m.c(2,'mode'),'1'),
            EQ(m.v('mem'),'1'),EQ(m.v('latest'),'1'),
            m.nd(m.top.root,'leaf_present_0'),m.nd(m.top.root,'leaf_present_1')),
        od,'mesi_remote_read_writeback'))
    w.append(trace(m,['core0:issue_read','core0:serve_read','core0:issue_evict','core0:serve_evict',
        'core1:issue_read','core1:serve_read'],
        AND(EQ(m.c(1,'reply_source'),'3'),EQ(m.c(1,'mode'),'3')),
        od,'mesi_L2_cache_hit'))
    mo=Hierarchy((2,2),'MOESI')
    w.append(trace(mo,['core0:issue_write','core0:serve_write','core2:issue_read','core2:serve_read'],
        AND(EQ(mo.c(0,'mode'),'4'),EQ(mo.c(2,'mode'),'1'),
            EQ(mo.v('latest'),'1'),EQ(mo.v('mem'),'0'),
            EQ(mo.nd(mo.top.root,'dirty_child'),'0'),
            mo.nd(mo.top.root,'leaf_present_0'),mo.nd(mo.top.root,'leaf_present_1')),
        od,'moesi_owned_remote_sharing'))
    bad=Hierarchy((2,2),'MOESI',mutant='drop_dirty_writeback')
    w.append(trace(bad,['core0:issue_write','core0:serve_write','core0:issue_evict','core0:serve_evict'],
         NOT(bad.invariant()),od,'mutant_dirty_evict_breaks_invariant'))
    drop=Hierarchy((2,2),'MESI',mutant='drop_presence')
    w.append(trace(drop,['core0:issue_read','core0:serve_read'],
         NOT(drop.invariant()),od,'mutant_directory_misroutes_metadata'))
    # Anti-vacuity: the ordinary hierarchy cannot reach these mutant-invalid
    # states along the same fixed traces, which should be solver UNSAT.
    w.append(trace(m,['core0:issue_read','core0:serve_read'],NOT(m.invariant()),
                   od,'sound_directory_invariant_control',expect_sat=False))
    out={'passed':all(x['passed'] for x in w),'checks':w}
    (od/'summary.json').write_text(json.dumps(out,indent=2))
    return out
if __name__=='__main__':
    output=ROOT/'artifacts/hierarchy_v21_witnesses'
    r=run(output)
    print(json.dumps({'passed':r['passed'],'witnesses':[(x['name'],x['status']) for x in r['checks']]},indent=2))
