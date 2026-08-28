import Wikipedia.SmoothSixDPoincare.LocalInverseIntoManifold
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue

/-!
# Smooth radial diffeomorphisms with positive nondecreasing scale

A positive smooth scale depending monotonically on squared radius gives an
injective map with invertible derivative. If the scale is one outside a
fixed radius, the intermediate value theorem proves global surjectivity.
This supplies a genuine smooth shrinking map, including at the center.
-/

noncomputable section

open Set Metric Function
open scoped ContDiff Manifold RealInnerProductSpace

namespace Wikipedia.SmoothSixDPoincare.SmoothRadial

variable {N : Type*} [NormedAddCommGroup N]

section Normed

variable [NormedSpace ℝ N]

def radialMap (φ : ℝ → ℝ) (x : N) : N := φ (‖x‖ ^ 2) • x

theorem norm_radialMap {φ : ℝ → ℝ} (hpos : ∀ s, 0 < φ s) (x : N) :
    ‖radialMap φ x‖ = φ (‖x‖ ^ 2) * ‖x‖ := by
  rw [radialMap, norm_smul, Real.norm_eq_abs, abs_of_pos (hpos _)]

omit [NormedAddCommGroup N] [NormedSpace ℝ N] in
theorem radius_strictMono {φ : ℝ → ℝ} (hpos : ∀ s, 0 < φ s) (hmono : Monotone φ) :
    StrictMonoOn (fun r => φ (r ^ 2) * r) (Ici 0) := by
  intro r hr s hs hrs
  have hsq : r ^ 2 ≤ s ^ 2 := (sq_le_sq₀ hr hs).mpr hrs.le
  exact (mul_lt_mul_of_pos_left hrs (hpos _)).trans_le
    (mul_le_mul_of_nonneg_right (hmono hsq) hs)

theorem radialMap_injective {φ : ℝ → ℝ} (hpos : ∀ s, 0 < φ s) (hmono : Monotone φ) :
    Injective (radialMap (N := N) φ) := by
  intro x y hxy
  have hn : ‖x‖ = ‖y‖ := by
    apply (radius_strictMono hpos hmono).injOn (norm_nonneg x) (norm_nonneg y)
    simpa only [norm_radialMap hpos] using congrArg norm hxy
  change φ (‖x‖ ^ 2) • x = φ (‖y‖ ^ 2) • y at hxy
  rw [hn] at hxy
  exact smul_right_injective N (hpos _).ne' hxy

theorem radialMap_surjective {φ : ℝ → ℝ} (hc : Continuous φ)
    {R : ℝ} (hR : 0 < R) (hout : ∀ s, R ^ 2 ≤ s → φ s = 1) :
    Surjective (radialMap (N := N) φ) := by
  intro y
  by_cases hy : R ≤ ‖y‖
  · refine ⟨y, ?_⟩
    rw [radialMap, hout _ ((sq_le_sq₀ hR.le (norm_nonneg y)).mpr hy), one_smul]
  by_cases hyzero : y = 0
  · subst y
    exact ⟨0, by simp only [radialMap, smul_zero]⟩
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hyzero
  have htarget : ‖y‖ ∈ Icc (φ (0 ^ 2) * 0) (φ (R ^ 2) * R) := by
    simpa only [mul_zero, hout _ le_rfl, one_mul, mem_Icc] using
      And.intro hypos.le (le_of_not_ge hy)
  have hcont : Continuous (fun r : ℝ => φ (r ^ 2) * r) :=
    (hc.comp (continuous_id.pow 2)).mul continuous_id
  obtain ⟨r, hr, hradius⟩ := intermediate_value_Icc hR.le hcont.continuousOn htarget
  change φ (r ^ 2) * r = ‖y‖ at hradius
  let x : N := (r / ‖y‖) • y
  have hnorm : ‖x‖ = r := by
    change ‖(r / ‖y‖) • y‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr.1 hypos.le),
      div_mul_cancel₀ _ hypos.ne']
  refine ⟨x, ?_⟩
  change φ (‖x‖ ^ 2) • ((r / ‖y‖) • y) = y
  rw [hnorm, smul_smul, ← mul_div_assoc, hradius, div_self hypos.ne', one_smul]

end Normed

variable [InnerProductSpace ℝ N]

theorem contDiff_radialMap {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (radialMap (N := N) φ) :=
  (hφ.comp (contDiff_id.norm_sq ℝ)).smul contDiff_id

theorem fderiv_radialMap_apply {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (x v : N) :
    fderiv ℝ (radialMap φ) x v =
      φ (‖x‖ ^ 2) • v + (2 * deriv φ (‖x‖ ^ 2) * inner ℝ x v) • x := by
  have hscale := ((hφ.differentiable (by simp) (‖x‖ ^ 2)).hasDerivAt).comp_hasFDerivAt x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hd := hscale.smul (hasFDerivAt_id x)
  rw [show fderiv ℝ (radialMap φ) x = _ from hd.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, smul_eq_mul, Function.comp_apply, id_eq]
  congr 1
  ring

theorem fderiv_radialMap_injective {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hpos : ∀ s, 0 < φ s) (hmono : Monotone φ) (x : N) :
    Injective (fderiv ℝ (radialMap φ) x) := by
  have hzero : ∀ v : N, fderiv ℝ (radialMap φ) x v = 0 → v = 0 := by
    intro v hv
    have heq := congrArg (fun w : N => inner ℝ v w) hv
    rw [fderiv_radialMap_apply hφ, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_comm v x, inner_zero_right] at heq
    have hd : 0 ≤ deriv φ (‖x‖ ^ 2) := hmono.deriv_nonneg
    have hnonneg : 0 ≤ 2 * deriv φ (‖x‖ ^ 2) * (inner ℝ v x) ^ 2 := by positivity
    have hterm : φ (‖x‖ ^ 2) * ‖v‖ ^ 2 ≤ 0 := by nlinarith
    have hsq : ‖v‖ ^ 2 ≤ 0 := by
      by_contra hn
      exact (not_lt_of_ge hterm) (mul_pos (hpos _) (lt_of_not_ge hn))
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
  intro v w hvw
  have hsub : fderiv ℝ (radialMap φ) x (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  exact sub_eq_zero.mp (hzero (v - w) hsub)

variable [FiniteDimensional ℝ N]

theorem isInvertible_fderiv_radialMap {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hpos : ∀ s, 0 < φ s) (hmono : Monotone φ) (x : N) :
    (fderiv ℝ (radialMap (N := N) φ) x).IsInvertible := by
  let L := (LinearEquiv.ofInjectiveEndo (fderiv ℝ (radialMap φ) x).toLinearMap
    (fderiv_radialMap_injective hφ hpos hmono x)).toContinuousLinearEquiv
  exact ⟨L, by ext v; rfl⟩

/-- The actual smooth global inverse is obtained from the local inverse
theorem and the proved bijectivity. -/
def diffeomorph {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hpos : ∀ s, 0 < φ s) (hmono : Monotone φ)
    {R : ℝ} (hR : 0 < R) (hout : ∀ s, R ^ 2 ≤ s → φ s = 1) :
    Diffeomorph 𝓘(ℝ, N) 𝓘(ℝ, N) N N ∞ := by
  have hlocal : IsLocalDiffeomorph 𝓘(ℝ, N) 𝓘(ℝ, N) ∞ (radialMap (N := N) φ) := by
    intro x
    apply isLocalDiffeomorphAt_of_contMDiffOn isOpen_univ (mem_univ x)
      (contDiff_radialMap hφ).contMDiff.contMDiffOn
    rw [mfderiv_eq_fderiv]
    exact isInvertible_fderiv_radialMap hφ hpos hmono x
  exact hlocal.diffeomorphOfBijective
    ⟨radialMap_injective hpos hmono, radialMap_surjective hφ.continuous hR hout⟩

theorem diffeomorph_apply {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hpos : ∀ s, 0 < φ s) (hmono : Monotone φ)
    {R : ℝ} (hR : 0 < R) (hout : ∀ s, R ^ 2 ≤ s → φ s = 1) (x : N) :
    diffeomorph hφ hpos hmono hR hout x = radialMap φ x := rfl

end Wikipedia.SmoothSixDPoincare.SmoothRadial
