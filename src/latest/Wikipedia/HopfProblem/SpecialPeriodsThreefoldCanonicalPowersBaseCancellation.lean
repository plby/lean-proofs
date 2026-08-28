import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersBase
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersComparisonsCancellation

/-!
# Cancellation with the actual pulled-back positive point line

The positive point line has the literal dual cocycle of the original
pulled-back ideal line. The genuine native cancellation therefore gives
`B^2 tensor f^*O(1) ≃ B`, including the base-preserving holomorphic map
and its exact complex-linear fibre map.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersBase

open CanonicalGlobalLineBundle

attribute [local instance] Threefold.chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "B" => GlobalBasePullback.cartier.transitions

/-- The actual comparison uses the already identified dual pullback cocycle. -/
def squarePointCancellation : CrossGauge IF (tensor ((B).power 2) pullbackData) B := by
  rw [pullbackData_eq_dual_base]
  exact Powers.squareDualCrossGauge IF B

/-- The original native source bundle of the cancellation. -/
abbrev squarePointBundle := (tensor ((B).power 2) pullbackData).core

/-- The cancellation is a biholomorphism of the actual original total spaces. -/
def squarePointCancellationDiffeomorph :
    Diffeomorph ((IF).prod 𝓘(ℂ)) ((IF).prod 𝓘(ℂ))
      squarePointBundle.TotalSpace GlobalBasePullback.bundle.TotalSpace ω :=
  squarePointCancellation.diffeomorph

/-- Its genuine continuous complex-linear map on each original fibre. -/
def squarePointCancellationFiberEquiv (x : Threefold.Space) :
    squarePointBundle.Fiber x ≃L[ℂ] GlobalBasePullback.bundle.Fiber x :=
  squarePointCancellation.fiberEquiv x

theorem squarePointCancellation_fiber_apply (x : Threefold.Space)
    (v : squarePointBundle.Fiber x) :
    squarePointCancellation.fiberEquiv x v = id (α := ℂ) v := by
  have h := Powers.squareDualCrossGauge_diffeomorph_apply IF B
    (⟨x, v⟩ : squarePointBundle.TotalSpace)
  have h' := h.trans (Powers.squareDualDiffeomorph_mk IF B x v)
  exact (congrArg (fun p : GlobalBasePullback.bundle.TotalSpace => id (α := ℂ) p.2) h').trans
    (Powers.squareDualFiberEquiv_apply IF B x v)

@[simp] theorem squarePointCancellationFiberEquiv_apply (x : Threefold.Space)
    (v : squarePointBundle.Fiber x) :
    squarePointCancellationFiberEquiv x v = id (α := ℂ) v :=
  squarePointCancellation_fiber_apply x v

@[simp] theorem squarePointCancellationDiffeomorph_proj (p : squarePointBundle.TotalSpace) :
    (squarePointCancellationDiffeomorph p).proj = p.proj :=
  squarePointCancellation.diffeomorph_proj p

theorem squarePointCancellationDiffeomorph_mk (x : Threefold.Space)
    (v : squarePointBundle.Fiber x) :
    squarePointCancellationDiffeomorph ⟨x, v⟩ =
      ⟨x, squarePointCancellationFiberEquiv x v⟩ :=
  squarePointCancellation.diffeomorph_mk x v

/-- No scalar rescaling is introduced in the actual preferred fibre coordinates. -/
theorem squarePointCancellationDiffeomorph_fibre_identity (x : Threefold.Space)
    (v : squarePointBundle.Fiber x) :
    squarePointCancellationDiffeomorph ⟨x, v⟩ = ⟨x, id (α := ℂ) v⟩ := by
  rw [squarePointCancellationDiffeomorph_mk, squarePointCancellationFiberEquiv_apply]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersBase
