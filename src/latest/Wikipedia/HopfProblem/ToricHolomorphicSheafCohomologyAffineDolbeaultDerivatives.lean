import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyAffineDolbeaultBasic
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousinDifferential
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationDbarOperations

/-!
# Literal antiholomorphic derivatives of affine smooth sections

The two operators are the already proved actual slice derivatives. Their
locality, smoothness and complex linearity give endomorphisms on every
actual section space. Real symmetry of second derivatives proves that the
two section operators commute.
-/

noncomputable section

open Set TopologicalSpace Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineDolbeault

open PeriodTorusLineBundleClassification PeriodTorusLineBundleClassificationCousin

/-- The literal first and second antiholomorphic coordinate derivatives. -/
def coordinateDbar : Bool → (ℂ × ℂ → ℂ) → ℂ × ℂ → ℂ
  | false => dbarFirst
  | true => dbarSecond

theorem coordinateDbar_contDiffAt (b : Bool) {f : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (hf : ContDiffAt ℝ ∞ f q) : ContDiffAt ℝ ∞ (coordinateDbar b f) q := by
  cases b
  · exact contDiffAt_dbarFirst hf
  · exact contDiffAt_dbarSecond hf

theorem coordinateDbar_congr (b : Bool) {f g : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (he : f =ᶠ[𝓝 q] g) : coordinateDbar b f q = coordinateDbar b g q := by
  cases b
  · exact dbarFirst_congr he
  · exact dbarSecond_congr he

theorem coordinateDbar_add (b : Bool) {f g : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q) :
    coordinateDbar b (fun p => f p + g p) q =
      coordinateDbar b f q + coordinateDbar b g q := by
  cases b
  · exact dbarFirst_add hf hg
  · exact dbarSecond_add hf hg

theorem coordinateDbar_const_mul (b : Bool) {f : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (hf : DifferentiableAt ℝ f q) (c : ℂ) :
    coordinateDbar b (fun p => c * f p) q = c * coordinateDbar b f q := by
  cases b
  · change dbarFirst (fun p => c * f p) q = c * dbarFirst f q
    rw [dbarFirst_eq_linear (hf.const_mul c), fderiv_const_mul hf c,
      dbarFirstLinear_complex_smul, ← dbarFirst_eq_linear hf]
  · change dbarSecond (fun p => c * f p) q = c * dbarSecond f q
    rw [dbarSecond_eq_linear (hf.const_mul c), fderiv_const_mul hf c,
      dbarSecondLinear_complex_smul, ← dbarSecond_eq_linear hf]

/-- Actual complex-linear differentiation on an actual open section space. -/
def derivativeSection (b : Bool) (U : Opens (ℂ × ℂ)) :
    SmoothSection U →ₗ[ℂ] SmoothSection U where
  toFun s :=
    ⟨fun q => coordinateDbar b (smoothExtend U s) q,
      fun q => contMDiffAt_subtype_iff.mpr
        (coordinateDbar_contDiffAt b (smoothExtend_contDiffAt U s q q.property)).contMDiffAt⟩
  map_add' s t := by
    apply ContMDiffMap.ext
    intro q
    change coordinateDbar b (smoothExtend U (s + t)) q =
      coordinateDbar b (smoothExtend U s) q + coordinateDbar b (smoothExtend U t) q
    rw [smoothExtend_add]
    exact coordinateDbar_add b
      ((smoothExtend_contDiffAt U s q q.property).differentiableAt (by simp))
      ((smoothExtend_contDiffAt U t q q.property).differentiableAt (by simp))
  map_smul' c s := by
    apply ContMDiffMap.ext
    intro q
    change coordinateDbar b (smoothExtend U (c • s)) q =
      c * coordinateDbar b (smoothExtend U s) q
    rw [smoothExtend_smul]
    exact coordinateDbar_const_mul b
      ((smoothExtend_contDiffAt U s q q.property).differentiableAt (by simp)) c

@[simp] theorem derivativeSection_apply (b : Bool) (U : Opens (ℂ × ℂ))
    (s : SmoothSection U) (q : U) :
    derivativeSection b U s q = coordinateDbar b (smoothExtend U s) q := rfl

/-- Genuine differentiation commutes with literal section restriction. -/
theorem derivativeSection_restrict (b : Bool) {U V : Opens (ℂ × ℂ)} (h : U ≤ V)
    (s : SmoothSection V) :
    derivativeSection b U (restriction h s) = restriction h (derivativeSection b V s) := by
  apply ContMDiffMap.ext
  intro q
  exact coordinateDbar_congr b (smoothExtend_restrict_germ h s q q.property)

theorem smoothExtend_derivativeSection_germ (b : Bool) (U : Opens (ℂ × ℂ))
    (s : SmoothSection U) (q : ℂ × ℂ) (hq : q ∈ U) :
    smoothExtend U (derivativeSection b U s) =ᶠ[𝓝 q]
      coordinateDbar b (smoothExtend U s) := by
  filter_upwards [U.isOpen.mem_nhds hq] with p hp
  exact smoothExtend_apply U (derivativeSection b U s) p hp

/-- The actual mixed antiholomorphic section derivatives commute. -/
theorem derivativeSection_commute (U : Opens (ℂ × ℂ)) (s : SmoothSection U) :
    derivativeSection false U (derivativeSection true U s) =
      derivativeSection true U (derivativeSection false U s) := by
  apply ContMDiffMap.ext
  intro q
  change dbarFirst (smoothExtend U (derivativeSection true U s)) q =
    dbarSecond (smoothExtend U (derivativeSection false U s)) q
  rw [dbarFirst_congr (smoothExtend_derivativeSection_germ true U s q q.property),
    dbarSecond_congr (smoothExtend_derivativeSection_germ false U s q q.property)]
  exact dbarFirst_dbarSecond_of_contDiffAt (smoothExtend_contDiffAt U s q q.property)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineDolbeault
