# Machine-checked progress artifacts (v1.5)

`summary.json` lists every SMT outcome and the exact assumptions. All `.smt2`
files are self-contained and can be rerun in an SMT-LIB-compliant Z3 build.
The checker calls `libz3.so.4` through the repo's existing ctypes bridge.

Key positive files:
- `protocol/active_transaction_has_service_step.smt2`
- `protocol/service_strictly_decreases_rank.smt2`
- `protocol/active_transaction_rank_never_increases.smt2`
- `combined_deadlock_2lines/combined_busy_system_has_some_progress_action_if_payload_available.smt2`
- `rank_frames_2lines/line0_all_foreign_and_frontend_steps_frame_transaction_rank.smt2`

Key negative witnesses (expected SAT):
- `reachable_symbolic_payload_stall.smt2`
- `reachable_combined_4core_2line_starvation_lasso.smt2`
- `reachable_combined_4core_3line_starvation_lasso.smt2`

The starvation lassos contain complete initial-state-to-cycle traces and
explicit return-to-the-same-state constraints. These are exact **reachability
witnesses**, not fabricated hypothetical schedules.

See `docs/LIVENESS_PROGRESS_ANALYSIS.md` for semantics and limitations.
