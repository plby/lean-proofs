import Wikipedia.HopfProblem.RiemannBoundaryGluing

/-!
# Reflection from a unit-modulus boundary limit

Only the modulus is assumed to converge at the straight boundary.  The
complex-valued boundary limit and analytic continuation are conclusions.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology ComplexConjugate

namespace Wikipedia.HopfProblem.RiemannBoundary

/-- The size of the jump between a complex number and its reflection in
the unit circle depends only on its modulus. The identity includes zero,
with the usual field convention for division by zero. -/
theorem norm_sub_inv_conj (w : ℂ) :
    ‖w - (conj w)⁻¹‖ = |‖w‖ ^ 2 - 1| / ‖w‖ := by
  have heq : w - (conj w)⁻¹ = ((‖w‖ ^ 2 - 1 : ℝ) : ℂ) / conj w := by
    by_cases hw : w = 0
    · simp [hw]
    have hc : conj w ≠ 0 := by simpa using hw
    apply (eq_div_iff hc).mpr
    rw [sub_mul, inv_mul_cancel₀ hc, mul_conj, normSq_eq_norm_sq, ofReal_sub, ofReal_one]
  rw [heq, norm_div, norm_real, Real.norm_eq_abs, norm_conj]

/-- Unit-modulus convergence implies a vanishing reflection jump,
without a phase or argument limit. -/
theorem tendsto_sub_inv_conj_of_norm {α : Type*} {l : Filter α} {f : α → ℂ}
    (hf : Tendsto (fun x => ‖f x‖) l (𝓝 1)) :
    Tendsto (fun x => f x - (conj (f x))⁻¹) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_sub_inv_conj]
  have hn : Tendsto (fun x => |‖f x‖ ^ 2 - 1|) l (𝓝 (0 : ℝ)) := by
    simpa using ((hf.pow 2).sub (tendsto_const_nhds (x := (1 : ℝ)))).abs
  have hdiv := hn.div hf one_ne_zero
  have hfun : ((fun x => |‖f x‖ ^ 2 - 1|) / (fun x => ‖f x‖)) =
      (fun x => |‖f x‖ ^ 2 - 1| / ‖f x‖) := by rfl
  rw [hfun] at hdiv
  simpa only [zero_div] using hdiv

/-- A continuous analytic extension whose upper values agree with the
original map takes unit-circle values on the diameter. -/
theorem norm_axis_eq_one_of_extension {H f : ℂ → ℂ} {a b h x : ℝ}
    (hh : 0 < h) (hx : x ∈ Ioo a b)
    (hH : ContinuousOn H (openRectangle a b (-h) h))
    (heq : EqOn H f (openRectangle a b 0 h))
    (hmod : Tendsto (fun z => ‖f z‖)
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 1)) :
    ‖H (x : ℂ)‖ = 1 := by
  have hxU : (x : ℂ) ∈ openRectangle a b (-h) h := by
    simpa [openRectangle] using And.intro hx (show (0 : ℝ) ∈ Ioo (-h) h by
      constructor <;> linarith)
  have hHt : Tendsto (fun y : ℝ => ‖H (x + y * I)‖) (𝓝[>] 0) (𝓝 ‖H (x : ℂ)‖) := by
    have hcont := (hH.continuousAt ((isOpen_openRectangle _ _ _ _).mem_nhds hxU)).norm
    have ht : Tendsto (fun y : ℝ => (x : ℂ) + y * I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
      have hc : Continuous (fun y : ℝ => (x : ℂ) + y * I) := by fun_prop
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    exact hcont.tendsto.comp ht
  have hft : Tendsto (fun y : ℝ => ‖f (x + y * I)‖) (𝓝[>] 0) (𝓝 1) := by
    apply hmod.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun y : ℝ => (x : ℂ) + y * I) := by fun_prop
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simpa using hy
  have hevent : (fun y : ℝ => ‖H (x + y * I)‖) =ᶠ[𝓝[>] 0]
      (fun y : ℝ => ‖f (x + y * I)‖) := by
    filter_upwards [Ioo_mem_nhdsGT hh] with y hy
    rw [heq (by simpa [openRectangle] using And.intro hx hy)]
  exact tendsto_nhds_unique hHt (hft.congr' hevent.symm)

/-- Unit-modulus limits imply analytic reflection on a rectangle when
the upper function is bounded and bounded away from zero. These are local
size bounds, not assumed boundary values or an assumed extension. -/
theorem exists_analytic_extension_of_modulus_one_bounded
    {f : ℂ → ℂ} {a b h M m : ℝ} (hab : a < b) (hh : 0 < h) (hm : 0 < m)
    (hf : DifferentiableOn ℂ f (openRectangle a b 0 h))
    (hfb : ∀ z ∈ openRectangle a b 0 h, ‖f z‖ ≤ M)
    (hfl : ∀ z ∈ openRectangle a b 0 h, m ≤ ‖f z‖)
    (hmod : ∀ x ∈ Ioo a b,
      Tendsto (fun z => ‖f z‖) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 1)) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (openRectangle a b (-h) h) ∧
      EqOn H f (openRectangle a b 0 h) ∧
      EqOn H (fun z => (conj (f (conj z)))⁻¹) (openRectangle a b (-h) 0) ∧
      ∀ x ∈ Ioo a b, ‖H (x : ℂ)‖ = 1 := by
  let g : ℂ → ℂ := fun z => (conj (f (conj z)))⁻¹
  have hconj : ∀ z ∈ openRectangle a b (-h) 0, conj z ∈ openRectangle a b 0 h := by
    intro z hz
    refine ⟨by simpa using hz.1, ?_⟩
    simp only [conj_im, mem_Ioo]
    constructor <;> linarith [hz.2.1, hz.2.2]
  have hnz : ∀ z ∈ openRectangle a b 0 h, f z ≠ 0 := by
    intro z hz heq
    have hb := hfl z hz
    rw [heq, norm_zero] at hb
    exact (not_le.mpr hm) hb
  have hg : DifferentiableOn ℂ g (openRectangle a b (-h) 0) := by
    intro z hz
    have hd := (hf.differentiableAt
      ((isOpen_openRectangle _ _ _ _).mem_nhds (hconj z hz))).conj_conj
    have hd' : DifferentiableAt ℂ (fun w => conj (f (conj w))) z := by
      simpa only [Function.comp_def, starRingEnd_self_apply] using hd
    exact (hd'.inv (by simpa using hnz (conj z) (hconj z hz))).differentiableWithinAt
  have hgb : ∀ z ∈ openRectangle a b (-h) 0, ‖g z‖ ≤ m⁻¹ := by
    intro z hz
    simp only [g, norm_inv, norm_conj]
    exact (inv_le_inv₀ (hm.trans_le (hfl _ (hconj z hz))) hm).mpr (hfl _ (hconj z hz))
  have hjump : ∀ x ∈ Ioo a b,
      Tendsto (fun z => f z - g (conj z))
        (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 0) := by
    intro x hx
    simpa only [g, starRingEnd_self_apply] using tendsto_sub_inv_conj_of_norm (hmod x hx)
  obtain ⟨H, hH, he, hl⟩ := exists_analytic_extension_of_vanishing_jump hab hh hf hg hfb hgb hjump
  exact ⟨H, hH, he, hl, fun x hx => norm_axis_eq_one_of_extension hh hx
    hH.continuousOn he (hmod x hx)⟩

end Wikipedia.HopfProblem.RiemannBoundary
