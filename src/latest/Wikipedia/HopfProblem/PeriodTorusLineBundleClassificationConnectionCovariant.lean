import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationConnectionCoefficients
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Coordinate covariance of the constructed differential operator

The local expression `ds + Aᵢ s` formed from the constructed connection
coefficients transforms by exactly the original scalar transition. This
checks the sign of the connection law against actual section coordinates.
-/

noncomputable section

open Filter Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationConnection

open HolomorphicCharacterBundle

local notation "Iℂ" => modelWithCornersSelf ℂ ComplexPlane₂

variable {ι : Type*} (A : TransitionData ComplexPlane₂ ι)

/-- The actual local first-order operator `ds + Aᵢ s`, with the constructed
smooth one-form coefficient. -/
def localCovariantDerivative (i : ι) (s : ComplexPlane₂ → ℂ) (x : ComplexPlane₂) :
    ComplexPlane₂ →L[ℝ] ℂ :=
  fderiv ℝ s x + s x • connectionForm A i x

variable [A.IsHolomorphic Iℂ]

/-- Genuine compatible scalar section coordinates give compatible covariant
derivatives, with precisely the original nonzero scalar transition. -/
theorem localCovariantDerivative_change (s : ι → ComplexPlane₂ → ℂ)
    (hs : ∀ i, DifferentiableOn ℝ (s i) (A.baseSet i))
    (htrans : ∀ i j x, x ∈ A.baseSet i ∩ A.baseSet j →
      s j x = (A.transition i j x : ℂ) * s i x)
    (i j : ι) {x : ComplexPlane₂} (hi : x ∈ A.baseSet i) (hj : x ∈ A.baseSet j) :
    localCovariantDerivative A j (s j) x =
      (A.transition i j x : ℂ) • localCovariantDerivative A i (s i) x := by
  let g : ComplexPlane₂ → ℂ := fun y => (A.transition i j y : ℂ)
  have hgc : ContDiffOn ℂ ω g (A.baseSet i ∩ A.baseSet j) :=
    (A.transition_holomorphic Iℂ i j).contDiffOn
  have hgr : ContDiffOn ℝ ∞ g (A.baseSet i ∩ A.baseSet j) :=
    (hgc.of_le le_top).restrict_scalars ℝ
  have hg : DifferentiableAt ℝ g x :=
    (hgr.contDiffAt (((A.isOpen_baseSet i).inter (A.isOpen_baseSet j)).mem_nhds
      ⟨hi, hj⟩)).differentiableAt (by simp)
  have hsi : DifferentiableAt ℝ (s i) x :=
    (hs i x hi).differentiableAt ((A.isOpen_baseSet i).mem_nhds hi)
  have hrel : s j =ᶠ[𝓝 x] (fun y => g y * s i y) := by
    filter_upwards [((A.isOpen_baseSet i).inter (A.isOpen_baseSet j)).mem_nhds ⟨hi, hj⟩]
      with y hy
    exact htrans i j y hy
  have hder := hrel.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_mul hg hsi] at hder
  have hg0 : g x ≠ 0 := A.transition_ne_zero i j x
  ext v
  change fderiv ℝ (s j) x v + s j x * connectionForm A j x v =
    g x * (fderiv ℝ (s i) x v + s i x * connectionForm A i x v)
  rw [hder]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [htrans i j x ⟨hi, hj⟩, connectionForm_change_apply A i j hi hj]
  change g x * fderiv ℝ (s i) x v + s i x * fderiv ℝ g x v +
    (g x * s i x) * (connectionForm A i x v - (g x)⁻¹ * fderiv ℝ g x v) =
      g x * (fderiv ℝ (s i) x v + s i x * connectionForm A i x v)
  field_simp
  ring

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationConnection
