#!/usr/bin/env python3
"""Key 3-line progress obligations; full 2-line progress suite is separate."""
from __future__ import annotations
import argparse,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'experiments/12_mesi_moesi'))
from extended_system import ExtendedFairSpec
from verify_mesi_moesi_v20 import emit
from verify_extended_progress_v20 import goals

def run(out,cores,lines,timeout):
    out=Path(out);all_ok=True
    for variant in ('MESI','MOESI'):
        m=ExtendedFairSpec(cores,lines,variant);d=out/f'{variant.lower()}_{cores}cores_{lines}lines';d.mkdir(parents=True,exist_ok=True)
        selected={name:goal for name,goal in goals(m).items() if name=='global_no_terminal_stall_enabledness'
             or name.endswith(('_active_has_service_enabled','_some_service_guard_stable_without_service',
                                 '_service_decreases_rank','_busy_without_pending_has_ask_or_complete'))}
        result=[]
        for name,goal in selected.items():
            rec=emit(m,d,name,goal,timeout);result.append(rec)
            print(variant,name,rec['result'],flush=True)
            if not rec['passed']:break
        ok=all(r['passed'] for r in result)
        (d/'summary.json').write_text(json.dumps({'variant':variant,'config':f'{cores}x{lines}',
                'passed':ok,'checks':result,'scope':'selected progress premises, not complete temporal theorem'},indent=2))
        all_ok&=ok
    return all_ok
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--cores',type=int,default=4);ap.add_argument('--lines',type=int,default=3)
    ap.add_argument('--timeout-ms',type=int,default=30000)
    ap.add_argument('--out',type=Path,default=ROOT/'artifacts/mesi_moesi_v20/progress_focused')
    x=ap.parse_args();sys.exit(0 if run(x.out,x.cores,x.lines,x.timeout_ms) else 1)
