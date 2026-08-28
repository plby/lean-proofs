import Wikipedia.HopfProblem.DegreeCollapseMorseCells

/-!
# Finite homotopy cell constructions

This inductive predicate records a finite sequence of genuine disk attachments
and actual homotopy equivalences. It does not assert a CW structure on the
original space, or replace any original topology. Every disk has real dimension
at most the stated bound. The interspersed homotopy equivalences permit direct
use of native Morse sublevels without changing attaching maps.
-/

noncomputable section

open Set Metric
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.FiniteCells

open Wikipedia.SmoothSixDPoincare

/-- A finite construction by bounded-dimensional cells, up to actual homotopy equivalence. -/
inductive Built (d : ℕ) : (X : Type) → [TopologicalSpace X] → Prop
  | empty (X : Type) [TopologicalSpace X] [IsEmpty X] : Built d X
  | equiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
      (e : X ≃ₕ Y) (h : Built d X) : Built d Y
  | attach {V M : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      [FiniteDimensional ℝ V] [TopologicalSpace M]
      (A : Set M) (h : C(MorseHandle.UnitDisk V, M))
      (hboundary : ∀ u : MorseHandle.UnitDisk V, ‖(u : V)‖ = 1 → h u ∈ A)
      (hdim : Module.finrank ℝ V ≤ d) (hA : Built d A) :
      Built d (ClosedAttachment.Space A
        {u : MorseHandle.UnitDisk V | ‖(u : V)‖ = 1} h)

end Wikipedia.HopfProblem.DegreeCollapse.FiniteCells
