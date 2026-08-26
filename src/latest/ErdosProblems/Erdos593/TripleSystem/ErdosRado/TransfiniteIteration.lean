import ErdosProblems.Erdos593.TripleSystem.ErdosRado.CanonicalTrace
import Mathlib.Order.TransfiniteIteration

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Transfinite set iteration for the Erdos--Rado trace route

This file records the Mathlib transfinite-recursion interface used by the
canonical-trace route. It is deliberately generic: a later construction must
supply the inflationary extension step and prove that its added trace nodes
satisfy the required coloring invariants.
-/

namespace Erdos593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado
namespace TraceIteration

/-- A potential trace entry records the ordinal stage and the selected carrier point. -/
abbrev TraceStage : Type 1 := Ordinal × TraceCarrier

/-- The complete lattice on which the trace-extension step is iterated. -/
abbrev TraceStageSet : Type 1 := Set TraceStage

variable (step : TraceStageSet → TraceStageSet)

/-- The transfinite run of a trace-extension step, initialized at the empty set. -/
noncomputable def run (eta : Ordinal) : TraceStageSet :=
  transfiniteIterate step eta ∅

/-- The zero stage of the trace run is empty. -/
@[simp]
theorem run_zero : run step 0 = ∅ := by
  change transfiniteIterate step (0 : Ordinal) (∅ : TraceStageSet) = ∅
  rw [← Ordinal.bot_eq_zero]
  exact transfiniteIterate_bot step (∅ : TraceStageSet)

/-- A successor stage applies the extension step once. -/
theorem run_succ (eta : Ordinal) (h_eta : ¬ IsMax eta) :
    run step (Order.succ eta) = step (run step eta) := by
  simpa [run] using!
    (transfiniteIterate_succ step (∅ : TraceStageSet) eta h_eta)

/-- Ordinals have no maximal element, so the successor rewrite has no side condition. -/
theorem run_succ_ordinal (eta : Ordinal) :
    run step (Order.succ eta) = step (run step eta) := by
  exact run_succ step eta (not_isMax eta)

/-- A limit stage is the supremum of all earlier stages. -/
theorem run_limit (eta : Ordinal) (h_eta : Order.IsSuccLimit eta) :
    run step eta = ⨆ xi : Set.Iio eta, run step xi.1 := by
  simpa [run] using!
    (transfiniteIterate_limit step (∅ : TraceStageSet) eta h_eta)

/-- Inflationarity of the extension step makes the transfinite run monotone. -/
theorem monotone_run (hinfl : ∀ s : TraceStageSet, s ⊆ step s) :
    Monotone (run step) := by
  exact monotone_transfiniteIterate step ∅ hinfl

end TraceIteration
end ErdosRado
end TriangleHost
end TripleSystem
end Erdos593
