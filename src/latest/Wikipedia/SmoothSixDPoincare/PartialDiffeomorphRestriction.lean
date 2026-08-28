import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Open restrictions and native derivatives of partial diffeomorphisms

Restriction keeps the actual maps and their inverse, and changes only the
open source and target. The native differential is a genuine continuous
linear equivalence at every source point.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.PartialChart

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  (Φ : PartialDiffeomorph I J M N ∞)

def restrictSource {U : Set M} (hU : IsOpen U) : PartialDiffeomorph I J M N ∞ where
  toPartialEquiv := (Φ.toOpenPartialHomeomorph.restrOpen U hU).toPartialEquiv
  open_source := (Φ.toOpenPartialHomeomorph.restrOpen U hU).open_source
  open_target := (Φ.toOpenPartialHomeomorph.restrOpen U hU).open_target
  contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono inter_subset_left
  contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono inter_subset_left

def restrictTarget {V : Set N} (hV : IsOpen V) : PartialDiffeomorph I J M N ∞ :=
  (restrictSource Φ.symm hV).symm

theorem restrictTarget_source {V : Set N} (hV : IsOpen V) :
    (restrictTarget Φ hV).source = Φ.source ∩ Φ ⁻¹' V := rfl

theorem restrictTarget_target {V : Set N} (hV : IsOpen V) :
    (restrictTarget Φ hV).target = Φ.target ∩ V := rfl

theorem restrictTarget_apply {V : Set N} (hV : IsOpen V) (x : M) :
    restrictTarget Φ hV x = Φ x := rfl

theorem bijective_mfderiv {x : M} (hx : x ∈ Φ.source) :
    Function.Bijective (mfderiv I J Φ x) := by
  have hdiff : Φ.toOpenPartialHomeomorph.MDifferentiable I J :=
    ⟨Φ.mdifferentiableOn (by simp), Φ.symm.mdifferentiableOn (by simp)⟩
  exact hdiff.mfderiv_bijective hx

end Wikipedia.SmoothSixDPoincare.PartialChart
