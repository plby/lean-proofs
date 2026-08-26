import ErdosProblems.Erdos593.TripleSystem.ErdosRadoCarrier
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftMissingBridgeObstruction

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Unconditional missing-bridge obstruction

The complete graph on a universe lift of the Erdős--Rado carrier has no
proper colouring by natural numbers.  It therefore supplies a concrete host
for the sequence-lift obstruction: a finite linear triple system whose
isolated reduction misses an incident Levi bridge is not obligatory.
-/

namespace Erdos593

open scoped Cardinal

universe u

namespace SequenceLift

/-- A universe-polymorphic copy of the fixed Erdős--Rado carrier. -/
abbrev MissingBridgeHostVertex : Type u :=
  ULift.{u} TripleSystem.TriangleHost.ErdosRadoCarrier

/-- The complete graph used as the concrete sequence-lift host. -/
abbrev missingBridgeHost : _root_.SimpleGraph MissingBridgeHostVertex.{u} :=
  _root_.SimpleGraph.completeGraph MissingBridgeHostVertex.{u}

/-- The complete graph on the lifted Erdős--Rado carrier has no proper
colouring by natural numbers. -/
theorem not_nonempty_coloring_missingBridgeHost :
    ¬ Nonempty (missingBridgeHost.{u}.Coloring ℕ) := by
  rintro ⟨C⟩
  have hC : Function.Injective C := by
    simpa only [Function.comp_id] using!
      C.injective_comp_of_pairwise_adj (f := id) (by
        intro x y hxy
        simpa using! hxy)
  let colorLift : MissingBridgeHostVertex.{u} → ULift.{u} ℕ :=
    fun x ↦ ULift.up (C x)
  have hcolorLift : Function.Injective colorLift := by
    intro x y hxy
    exact hC (congrArg ULift.down hxy)
  have hcard : Cardinal.mk MissingBridgeHostVertex.{u} ≤
      Cardinal.mk (ULift.{u} ℕ) :=
    Cardinal.mk_le_of_injective hcolorLift
  have hcard' : Order.succ (Cardinal.continuum : Cardinal.{u}) ≤ ℵ₀ := by
    simpa [MissingBridgeHostVertex,
      TripleSystem.TriangleHost.mk_erdosRadoCarrier, Cardinal.mk_nat] using! hcard
  have hsucc_le_continuum :
      Order.succ (Cardinal.continuum : Cardinal.{u}) ≤ Cardinal.continuum :=
    hcard'.trans Cardinal.aleph0_le_continuum
  exact (Order.lt_succ (Cardinal.continuum : Cardinal.{u})).2
    hsucc_le_continuum

end SequenceLift

namespace TripleSystem

variable {X I : Type u}

/-- A finite linear triple system whose isolated reduction misses an incident
Levi bridge is not obligatory. -/
theorem not_isObligatory_of_linear_of_not_isolatedReduction_bridgeAtEveryEdge
    (F : TripleSystem X I) [Fintype I]
    (hlinear : F.Linear)
    (hno : ¬ F.isolatedReduction.BridgeAtEveryEdge) :
    ¬ F.IsObligatory := by
  exact SequenceLift.not_isObligatory_of_linear_of_not_isolatedReduction_bridgeAtEveryEdge
    (G := SequenceLift.missingBridgeHost.{u})
    SequenceLift.not_nonempty_coloring_missingBridgeHost.{u} hlinear hno

end TripleSystem

end Erdos593
