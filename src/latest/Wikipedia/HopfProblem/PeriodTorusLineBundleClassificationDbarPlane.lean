import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLocalDbar
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationDbarAnalytic
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalyticCoordinates

/-!
# Antiholomorphic primitives in the actual period-cover coordinates

The derivatives below use literal coordinate replacement in
`ComplexPlane₂ = Fin 2 → ℂ`.  The product-coordinate integral solver is
transported through the canonical complex continuous linear equivalence.
-/

noncomputable section

open Complex Set Metric
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open HolomorphicCousin
open PeriodTorusLineBundleClassificationPolydiscAnalytic (complexPairEquiv)

/-- The actual antiholomorphic derivative in coordinate `i` of the covering
vector space, defined by varying that coordinate alone. -/
def dbarCoordinate (f : ComplexPlane₂ → ℂ) (i : Fin 2) (z : ComplexPlane₂) : ℂ :=
  dbar (fun w => f (Function.update z i w)) (z i)

theorem dbarCoordinate_zero_eq_pair (f : ComplexPlane₂ → ℂ) (z : ComplexPlane₂) :
    dbarCoordinate f 0 z =
      dbarFirst (f ∘ complexPairEquiv.symm) (complexPairEquiv z) := by
  change dbar (fun w => f (Function.update z 0 w)) (z 0) =
    dbar (fun w => f ![w, z 1]) (z 0)
  congr 1
  funext w
  congr 1
  ext i
  fin_cases i <;> simp

theorem dbarCoordinate_one_eq_pair (f : ComplexPlane₂ → ℂ) (z : ComplexPlane₂) :
    dbarCoordinate f 1 z =
      dbarSecond (f ∘ complexPairEquiv.symm) (complexPairEquiv z) := by
  change dbar (fun w => f (Function.update z 1 w)) (z 1) =
    dbar (fun w => f ![z 0, w]) (z 1)
  congr 1
  funext w
  congr 1
  ext i
  fin_cases i <;> simp

theorem dbarCoordinate_pair_zero (u : ℂ × ℂ → ℂ) (z : ComplexPlane₂) :
    dbarCoordinate (u ∘ complexPairEquiv) 0 z = dbarFirst u (complexPairEquiv z) := by
  rw [dbarCoordinate_zero_eq_pair]
  have he : (u ∘ complexPairEquiv) ∘ complexPairEquiv.symm = u := by
    funext q
    simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [he]

theorem dbarCoordinate_pair_one (u : ℂ × ℂ → ℂ) (z : ComplexPlane₂) :
    dbarCoordinate (u ∘ complexPairEquiv) 1 z = dbarSecond u (complexPairEquiv z) := by
  rw [dbarCoordinate_one_eq_pair]
  have he : (u ∘ complexPairEquiv) ∘ complexPairEquiv.symm = u := by
    funext q
    simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [he]

theorem pair_isDbarClosed {f g : ComplexPlane₂ → ℂ}
    (hclosed : ∀ z, dbarCoordinate g 0 z = dbarCoordinate f 1 z) :
    IsDbarClosed (f ∘ complexPairEquiv.symm) (g ∘ complexPairEquiv.symm) := by
  intro q
  have he := hclosed (complexPairEquiv.symm q)
  rw [dbarCoordinate_zero_eq_pair, dbarCoordinate_one_eq_pair,
    ContinuousLinearEquiv.apply_symm_apply] at he
  exact he

/-- The smooth closed form has a genuine primitive on every prescribed
closed ball of the actual period-cover vector space. -/
theorem exists_smooth_primitive_on_cover_closedBall {f g : ComplexPlane₂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hclosed : ∀ z, dbarCoordinate g 0 z = dbarCoordinate f 1 z)
    (R : ℝ) (hR : 0 < R) :
    ∃ u : ComplexPlane₂ → ℂ, ContDiff ℝ ∞ u ∧ ∀ z ∈ closedBall (0 : ComplexPlane₂) R,
      dbarCoordinate u 0 z = f z ∧ dbarCoordinate u 1 z = g z := by
  have he : ContDiff ℝ ∞ complexPairEquiv.symm :=
    complexPairEquiv.symm.contDiff.restrict_scalars ℝ
  obtain ⟨u, hu, hdu⟩ := exists_smooth_primitive_on_closedBidisc (hf.comp he) (hg.comp he)
    (pair_isDbarClosed hclosed) R hR
  refine ⟨u ∘ complexPairEquiv, hu.comp (complexPairEquiv.contDiff.restrict_scalars ℝ), ?_⟩
  intro z hz
  have hzn : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hq : complexPairEquiv z ∈ closedBall (0 : ℂ) R ×ˢ closedBall 0 R := by
    constructor
    · exact mem_closedBall_zero_iff.mpr ((norm_le_pi_norm z 0).trans hzn)
    · exact mem_closedBall_zero_iff.mpr ((norm_le_pi_norm z 1).trans hzn)
  simpa only [dbarCoordinate_pair_zero, dbarCoordinate_pair_one, Function.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply] using hdu (complexPairEquiv z) hq

/-- The compact-support solver likewise acts on the actual cover coordinates. -/
theorem exists_smooth_primitive_on_cover_of_compact_support {f g : ComplexPlane₂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g)
    (hclosed : ∀ z, dbarCoordinate g 0 z = dbarCoordinate f 1 z) :
    ∃ u : ComplexPlane₂ → ℂ, ContDiff ℝ ∞ u ∧
      (∀ z, dbarCoordinate u 0 z = f z) ∧ ∀ z, dbarCoordinate u 1 z = g z := by
  have he : ContDiff ℝ ∞ complexPairEquiv.symm :=
    complexPairEquiv.symm.contDiff.restrict_scalars ℝ
  obtain ⟨u, hu, hdu, hdv⟩ := exists_smooth_primitive_of_compact_support (hf.comp he) (hg.comp he)
    (hcf.comp_homeomorph complexPairEquiv.symm.toHomeomorph)
    (hcg.comp_homeomorph complexPairEquiv.symm.toHomeomorph) (pair_isDbarClosed hclosed)
  refine ⟨u ∘ complexPairEquiv, hu.comp (complexPairEquiv.contDiff.restrict_scalars ℝ), ?_, ?_⟩
  · intro z
    simpa only [dbarCoordinate_pair_zero, Function.comp_apply,
      ContinuousLinearEquiv.symm_apply_apply] using hdu (complexPairEquiv z)
  · intro z
    simpa only [dbarCoordinate_pair_one, Function.comp_apply,
      ContinuousLinearEquiv.symm_apply_apply] using hdv (complexPairEquiv z)

/-- Vanishing coordinate antiholomorphic derivatives gives actual joint
analyticity in the native covering vector space. -/
theorem analyticOnNhd_of_dbarCoordinate_zero {f : ComplexPlane₂ → ℂ}
    {U : Set ComplexPlane₂} (hU : IsOpen U) (hf : DifferentiableOn ℝ f U)
    (h₀ : ∀ z ∈ U, dbarCoordinate f 0 z = 0)
    (h₁ : ∀ z ∈ U, dbarCoordinate f 1 z = 0) : AnalyticOnNhd ℂ f U := by
  apply PeriodTorusLineBundleClassificationPolydiscAnalytic.analyticOnNhd_complexPlane₂_of_pair
  apply analyticOnNhd_of_coordinate_dbar_zero
    (hU.preimage complexPairEquiv.symm.continuous)
    (hf.comp (complexPairEquiv.symm.differentiable.restrictScalars ℝ).differentiableOn
      (fun _ h => h))
  · intro q hq
    have he := h₀ (complexPairEquiv.symm q) hq
    rw [dbarCoordinate_zero_eq_pair, ContinuousLinearEquiv.apply_symm_apply] at he
    exact he
  · intro q hq
    have he := h₁ (complexPairEquiv.symm q) hq
    rw [dbarCoordinate_one_eq_pair, ContinuousLinearEquiv.apply_symm_apply] at he
    exact he

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
