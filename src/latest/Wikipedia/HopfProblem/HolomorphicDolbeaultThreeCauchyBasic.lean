import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCauchy

/-!
# Antiholomorphic directions for a parameter-dependent Cauchy–Green integral

These operators use the actual joint real derivative on `P × ℂ`.  The final
coordinate derivative is also identified with the ordinary one-variable
antiholomorphic derivative of a slice.  No complex atlas is changed here.
-/

noncomputable section

open Complex Set Filter
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Cauchy

open HolomorphicCousin PeriodTorusLineBundleClassification

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Evaluation of the antiholomorphic part of a joint real derivative in the
last complex coordinate. -/
def lastLinear : ((P × ℂ) →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1 / (2 : ℂ)) • (ContinuousLinearMap.apply ℝ ℂ (0, 1) +
    I • ContinuousLinearMap.apply ℝ ℂ (0, I))

@[simp] theorem lastLinear_apply (L : (P × ℂ) →L[ℝ] ℂ) :
    lastLinear L = (L (0, 1) + I * L (0, I)) / 2 := by
  simp only [lastLinear, smul_apply, add_apply,
    ContinuousLinearMap.apply_apply, smul_eq_mul]
  ring

theorem lastLinear_complex_smul (c : ℂ) (L : (P × ℂ) →L[ℝ] ℂ) :
    lastLinear (c • L) = c * lastLinear L := by
  simp only [lastLinear_apply, smul_apply, smul_eq_mul]
  ring

/-- The actual antiholomorphic derivative of the last-coordinate slice. -/
def lastDbar (f : P × ℂ → ℂ) (q : P × ℂ) : ℂ :=
  dbar (fun w => f (q.1, w)) q.2

theorem lastDbar_eq_linear {f : P × ℂ → ℂ} {q : P × ℂ}
    (hf : DifferentiableAt ℝ f q) :
    lastDbar f q = lastLinear (fderiv ℝ f q) := by
  have he := (hf.hasFDerivAt.comp q.2
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)).fderiv
  change fderiv ℝ (fun w => f (q.1, w)) q.2 = _ at he
  simp only [lastDbar, dbar, he, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, lastLinear_apply]

theorem lastDbar_eq_formula {f : P × ℂ → ℂ} {q : P × ℂ}
    (hf : DifferentiableAt ℝ f q) :
    lastDbar f q =
      (fderiv ℝ f q (0, 1) + I * fderiv ℝ f q (0, I)) / 2 := by
  rw [lastDbar_eq_linear hf, lastLinear_apply]

theorem continuous_lastDbar {f : P × ℂ → ℂ} (hf : ContDiff ℝ 1 f) :
    Continuous (lastDbar f) := by
  have he : lastDbar f = lastLinear ∘ fderiv ℝ f :=
    funext (fun q => lastDbar_eq_linear ((hf.differentiable one_ne_zero) q))
  rw [he]
  exact lastLinear.continuous.comp (hf.continuous_fderiv one_ne_zero)

theorem contDiff_lastDbar {f : P × ℂ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (lastDbar f) := by
  have he : lastDbar f = lastLinear ∘ fderiv ℝ f :=
    funext (fun q => lastDbar_eq_linear ((hf.differentiable (by simp)) q))
  rw [he]
  exact lastLinear.contDiff.comp (contDiff_infty_iff_fderiv.mp hf).2

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The last derivative vanishes outside the same closed uniform support,
without any global differentiability assumption. -/
theorem lastDbar_eq_zero_off_second_support {f : P × ℂ → ℂ} {k : Set ℂ}
    (hk : IsClosed k) (hfk : ∀ p w, w ∉ k → f (p, w) = 0)
    (p : P) {w : ℂ} (hw : w ∉ k) : lastDbar f (p, w) = 0 := by
  have he : (fun z : ℂ => f (p, z)) =ᶠ[𝓝 w] fun _ => (0 : ℂ) := by
    filter_upwards [hk.isOpen_compl.mem_nhds hw] with z hz
    exact hfk p z hz
  have hd : fderiv ℝ (fun z : ℂ => f (p, z)) w = 0 :=
    (hasFDerivAt_zero_of_eventually_const (0 : ℂ) he).fderiv
  simp only [lastDbar, dbar, hd, zero_apply, mul_zero,
    zero_add, zero_div]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem hasCompactSupport_lastDbar_slice {f : P × ℂ → ℂ} {k : Set ℂ}
    (hk : IsCompact k) (hfk : ∀ p w, w ∉ k → f (p, w) = 0) (p : P) :
    HasCompactSupport (fun w => lastDbar f (p, w)) :=
  HasCompactSupport.intro hk (fun _ hw =>
    lastDbar_eq_zero_off_second_support hk.isClosed hfk p hw)

section ComplexParameter

variable [NormedSpace ℂ P]

/-- Evaluation of the antiholomorphic part in the constant parameter direction
`v`, leaving the integrated coordinate fixed. -/
def parameterLinear (v : P) : ((P × ℂ) →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1 / (2 : ℂ)) • (ContinuousLinearMap.apply ℝ ℂ (v, 0) +
    I • ContinuousLinearMap.apply ℝ ℂ (I • v, 0))

@[simp] theorem parameterLinear_apply (v : P) (L : (P × ℂ) →L[ℝ] ℂ) :
    parameterLinear v L = (L (v, 0) + I * L (I • v, 0)) / 2 := by
  simp only [parameterLinear, smul_apply, add_apply,
    ContinuousLinearMap.apply_apply, smul_eq_mul]
  ring

theorem parameterLinear_complex_smul (v : P) (c : ℂ)
    (L : (P × ℂ) →L[ℝ] ℂ) :
    parameterLinear v (c • L) = c * parameterLinear v L := by
  simp only [parameterLinear_apply, smul_apply, smul_eq_mul]
  ring

/-- The actual joint derivative evaluated in an antiholomorphic parameter
direction. -/
def parameterDbar (v : P) (f : P × ℂ → ℂ) (q : P × ℂ) : ℂ :=
  parameterLinear v (fderiv ℝ f q)

theorem parameterDbar_eq_formula (v : P) (f : P × ℂ → ℂ) (q : P × ℂ) :
    parameterDbar v f q =
      (fderiv ℝ f q (v, 0) + I * fderiv ℝ f q (I • v, 0)) / 2 :=
  parameterLinear_apply v _

theorem continuous_parameterDbar (v : P) {f : P × ℂ → ℂ}
    (hf : ContDiff ℝ 1 f) : Continuous (parameterDbar v f) :=
  (parameterLinear v).continuous.comp (hf.continuous_fderiv one_ne_zero)

theorem contDiff_parameterDbar (v : P) {f : P × ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (parameterDbar v f) :=
  (parameterLinear v).contDiff.comp (contDiff_infty_iff_fderiv.mp hf).2

/-- Parameter derivatives keep the original uniform support in the last
coordinate. -/
theorem parameterDbar_eq_zero_off_second_support (v : P)
    {f : P × ℂ → ℂ} {k : Set ℂ} (hk : IsClosed k)
    (hfk : ∀ p w, w ∉ k → f (p, w) = 0) (p : P) {w : ℂ} (hw : w ∉ k) :
    parameterDbar v f (p, w) = 0 := by
  rw [parameterDbar, fderiv_eq_zero_off_second_support hk hfk p hw, map_zero]

theorem hasCompactSupport_parameterDbar_slice (v : P)
    {f : P × ℂ → ℂ} {k : Set ℂ} (hk : IsCompact k)
    (hfk : ∀ p w, w ∉ k → f (p, w) = 0) (p : P) :
    HasCompactSupport (fun w => parameterDbar v f (p, w)) :=
  HasCompactSupport.intro hk (fun _ hw =>
    parameterDbar_eq_zero_off_second_support v hk.isClosed hfk p hw)

end ComplexParameter

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Cauchy
