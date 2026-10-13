import WebMu.Revised.FaithfulEndpoint
import Lean

-- Added for the independent review; delivered source modules are unchanged.
#check WebMu.Revised.paper_main_faithful
#check WebMu.Revised.paper_canonicality_faithful
#check WebMu.Revised.paper_unbounded_faithful
#print axioms WebMu.Revised.paper_main_faithful
#print axioms WebMu.Revised.paper_canonicality_faithful
#print axioms WebMu.Revised.paper_unbounded_faithful

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := #[`WebMu.Revised.paper_main_faithful,
    `WebMu.Revised.paper_canonicality_faithful,
    `WebMu.Revised.paper_unbounded_faithful]
  let allowed := #[`propext, `Classical.choice, `Quot.sound, `Lean.ofReduceBool]
  for root in roots do
    unless (env.checked.get.find? root).isSome do throwError "Missing endpoint {root}"
    let (_, deps) := ((CollectAxioms.collect root).run env).run {}
    for n in deps.axioms do
      unless allowed.contains n do throwError "Unexpected axiom {n} in {root}"
    for n in #[`WebMu.Revised.Bar.AtomicCoordinates.circuit_matrix,
      `WebMu.Revised.tensor_coordinate_change,
      `WebMu.Revised.Bar.tensorOriginal_fixed,
      `WebMu.Revised.WrittenProof.localProperties,
      `WebMu.Revised.LocalDegreeProof.block_nonpositive_from_local,
      `WebMu.Revised.tensor_unique_leading_state] do
      unless deps.visited.contains n do throwError "Missing main proof component {n} in {root}"
    for n in #[`sorryAx, `WebMu.proposition_4_2,
      `WebMu.norm_integral_constant_one,
      `WebMu.Revised.tensorOriginal_integral,
      `WebMu.Revised.tensorOriginal_source_even,
      `WebMu.Revised.block_integral_check,
      `WebMu.Revised.selected_ABC_row,
      `WebMu.Revised.selected_scalar_row] do
      if deps.visited.contains n then throwError "Unexpected earlier certificate {n} in {root}"
    logInfo m!"Independent main audit passed for {root}: only allowed axioms; actual circuit, gauge cancellation and local proof present; former certificates absent."
