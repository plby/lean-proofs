/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RiemannMapping
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.UniformSpace.Ascoli
import ErdosProblems.Erdos515.External.Ray.Koebe.Koebe

/-!
# Riemann maps used for Erdős Problem 515

Mathlib v4.33.0 contains the first two construction steps of the Riemann mapping theorem in
`Mathlib.Analysis.Complex.RiemannMapping`, but not yet the surjectivity argument.  This file ports
the missing normal-family argument from mathlib4 PR #33505.  Names specific to the port carry the
suffix `515`, so that the file can coexist with the eventual upstream API.
-/

open Filter Function Metric Set
open scoped ComplexConjugate Pointwise Topology UniformConvergence Uniformity

noncomputable section

namespace Complex.UnitDisc

lemma shiftDenNeZero515 (z w : 𝔻) : 1 + conj (z : ℂ) * w ≠ 0 :=
  (star z * w).one_add_coe_ne_zero

private lemma norm_shiftFun515_le (z w : 𝔻) :
    ‖(z + w : ℂ) / (1 + conj ↑z * w)‖ ≤
      (‖(z : ℂ)‖ + ‖(w : ℂ)‖) / (1 + ‖(z : ℂ)‖ * ‖(w : ℂ)‖) := by
  have hz := z.sq_norm_lt_one
  have hw := w.sq_norm_lt_one
  have hzw : z.re * w.re + z.im * w.im ≤ ‖(z : ℂ)‖ * ‖(w : ℂ)‖ := by
    rw [norm_def, norm_def, ← Real.sqrt_mul, normSq_apply, normSq_apply]
    · apply Real.le_sqrt_of_sq_le
      linear_combination (norm := {apply le_of_eq; simp; ring})
        sq_nonneg (z.re * w.im - z.im * w.re)
    · apply normSq_nonneg
  rw [norm_div, div_le_div_iff₀, ← sq_le_sq₀]
  · rw [← sub_nonneg] at hzw
    simp [mul_pow, RCLike.norm_sq_eq_def, add_sq] at hz hw ⊢
    linear_combination 2 * mul_nonneg hzw
      (mul_nonneg (sub_nonneg.2 hz.le) (sub_nonneg.2 hw.le))
  any_goals positivity
  simpa using shiftDenNeZero515 z w

private def shiftFun515 (z w : 𝔻) : 𝔻 :=
  .mk ((z + w : ℂ) / (1 + conj ↑z * w)) <| by
    refine (norm_shiftFun515_le _ _).trans_lt ?_
    rw [div_lt_one (by positivity)]
    nlinarith only [z.norm_lt_one, w.norm_lt_one]

@[simp] private lemma coe_shiftFun515 (z w : 𝔻) :
    (shiftFun515 z w : ℂ) = (z + w) / (1 + conj ↑z * w) := rfl

private lemma shiftFun515_eq_iff {z w u : 𝔻} :
    shiftFun515 z w = u ↔ (z + w : ℂ) = u + u * conj ↑z * w := by
  rw [← coe_inj, coe_shiftFun515, div_eq_iff (shiftDenNeZero515 _ _)]
  ring_nf

private lemma shiftFun515_neg_apply_shiftFun515 (z w : 𝔻) :
    shiftFun515 (-z) (shiftFun515 z w) = w := by
  rw [shiftFun515_eq_iff, coe_shiftFun515, add_div_eq_mul_add_div, ← mul_div_assoc,
    add_div_eq_mul_add_div]
  · simp
    ring
  all_goals exact shiftDenNeZero515 z w

/-- The automorphism of the unit disk which takes `0` to `z`.

This is a locally-named copy of the construction in mathlib4 PR #33505. -/
def shift515 (z : 𝔻) : 𝔻 ≃ 𝔻 where
  toFun := shiftFun515 z
  invFun := shiftFun515 (-z)
  left_inv := shiftFun515_neg_apply_shiftFun515 _
  right_inv := fun w ↦ by simpa using shiftFun515_neg_apply_shiftFun515 (-z) w

lemma coe_shift515 (z w : 𝔻) :
    (shift515 z w : ℂ) = (z + w) / (1 + conj ↑z * w) := rfl

@[simp] lemma shift515_apply_zero (z : 𝔻) : shift515 z 0 = z := by
  rw [← coe_inj, coe_shift515]
  simp

@[simp] lemma shift515_neg_apply_self (z : 𝔻) : shift515 (-z) z = 0 := by
  rw [← coe_inj, coe_shift515]
  simp [← sub_eq_add_neg]

@[simp] lemma shift515_eq_zero_iff {z w : 𝔻} : shift515 z w = 0 ↔ w = -z := by
  have hz0 : shift515 z (-z) = 0 := by
    simpa only [neg_neg] using shift515_neg_apply_self (-z)
  constructor
  · intro h
    exact (shift515 z).injective (h.trans hz0.symm)
  · rintro rfl
    exact hz0

@[simp] lemma shift515_neg_apply_shift515 (z w : 𝔻) :
    shift515 (-z) (shift515 z w) = w :=
  shiftFun515_neg_apply_shiftFun515 z w

@[fun_prop] lemma continuous_shift515 (z : 𝔻) : Continuous (shift515 z) := by
  simp only [isEmbedding_coe.continuous_iff, Function.comp_def, coe_shift515]
  exact .div (by fun_prop) (by fun_prop) fun _ ↦ shiftDenNeZero515 _ _

lemma hasDerivWithinAt_shift515_comp {f : ℂ → 𝔻} {z f' : ℂ} {s : Set ℂ}
    (w : 𝔻) (hf : HasDerivWithinAt (fun x ↦ ↑(f x)) f' s z) :
    HasDerivWithinAt (fun x ↦ w.shift515 (f x) : ℂ → ℂ)
      ((1 - conj (w : ℂ) * w) / (1 + conj ↑w * f z) ^ 2 * f') s z := by
  simp only [coe_shift515]
  have hq := (hf.const_add (w : ℂ)).fun_div
      ((hf.const_mul (conj (w : ℂ))).const_add 1) (shiftDenNeZero515 w (f z))
  convert hq using 1 <;> try rfl
  ring

lemma hasDerivAt_shift515_comp {f : ℂ → 𝔻} {z f' : ℂ} (w : 𝔻)
    (hf : HasDerivAt (fun x ↦ ↑(f x)) f' z) :
    HasDerivAt (fun x ↦ w.shift515 (f x) : ℂ → ℂ)
      ((1 - conj (w : ℂ) * w) / (1 + conj ↑w * f z) ^ 2 * f') z :=
  (hasDerivWithinAt_shift515_comp w hf.hasDerivWithinAt).hasDerivAt univ_mem

@[simp] lemma differentiableOn_shift515_comp_iff {f : ℂ → 𝔻} {s : Set ℂ} (w : 𝔻) :
    DifferentiableOn ℂ (fun x ↦ w.shift515 (f x) : ℂ → ℂ) s ↔
      DifferentiableOn ℂ (fun x ↦ (f x : ℂ)) s := by
  constructor
  · intro h z hz
    have heq : (fun x ↦ (f x : ℂ)) = fun x ↦ ((-w).shift515 (w.shift515 (f x)) : ℂ) := by
      funext x
      exact congrArg ((↑·) : 𝔻 → ℂ) (shift515_neg_apply_shift515 w (f x)).symm
    rw [heq]
    exact (hasDerivWithinAt_shift515_comp (-w) (h z hz).hasDerivWithinAt).differentiableWithinAt
  · intro h z hz
    exact (hasDerivWithinAt_shift515_comp w (h z hz).hasDerivWithinAt).differentiableWithinAt

lemma deriv_shift515_comp (f : ℂ → 𝔻) (z : ℂ) (w : 𝔻) :
    deriv (fun x ↦ w.shift515 (f x) : ℂ → ℂ) z =
      (1 - conj (w : ℂ) * w) / (1 + conj ↑w * f z) ^ 2 *
        deriv (fun x ↦ (f x : ℂ)) z := by
  by_cases hfd : DifferentiableAt ℂ (fun x ↦ (f x : ℂ)) z
  · exact (hasDerivAt_shift515_comp w hfd.hasDerivAt).deriv
  · rw [deriv_zero_of_not_differentiableAt hfd, deriv_zero_of_not_differentiableAt, mul_zero]
    intro h
    apply hfd
    have heq : (fun x ↦ (f x : ℂ)) = fun x ↦ ((-w).shift515 (w.shift515 (f x)) : ℂ) := by
      funext x
      exact congrArg ((↑·) : 𝔻 → ℂ) (shift515_neg_apply_shift515 w (f x)).symm
    rw [heq]
    exact (hasDerivAt_shift515_comp (-w) h.hasDerivAt).differentiableAt

lemma deriv_shift515_comp_eq_zero (f : ℂ → 𝔻) (z : ℂ) (w : 𝔻) :
    deriv (fun x ↦ w.shift515 (f x) : ℂ → ℂ) z = 0 ↔
      deriv (fun x ↦ (f x : ℂ)) z = 0 := by
  rw [deriv_shift515_comp, mul_eq_zero]
  simp only [div_eq_zero_iff, pow_eq_zero_iff two_ne_zero, shiftDenNeZero515, or_false]
  apply or_iff_right
  apply sub_ne_zero.mpr
  intro h
  have hn := congrArg norm h
  simp only [norm_one, norm_mul, norm_conj] at hn
  rw [← sq] at hn
  exact w.sq_norm_lt_one.ne hn.symm

lemma norm_one_sub_conj_mul_self515 (z : 𝔻) :
    ‖1 - conj (z : ℂ) * z‖ = 1 - ‖(z : ℂ)‖ ^ 2 := by
  rw [conj_mul']
  norm_cast
  rw [Real.norm_eq_abs, abs_of_pos]
  exact sub_pos.mpr z.sq_norm_lt_one

end Complex.UnitDisc

namespace Erdos515

open Complex

private theorem AnalyticOnNhd.exists_finset_eq_prod_smul_nonzero515
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {s : Set 𝕜}
    (hfs : AnalyticOnNhd 𝕜 f s) (hs_comp : IsCompact s) (hs_conn : IsPreconnected s)
    (hf₀ : ¬EqOn f 0 s) :
    ∃ (t : Finset 𝕜), (∀ x, x ∈ t ↔ x ∈ s ∧ f x = 0) ∧
      ∃ (g : 𝕜 → E), AnalyticOnNhd 𝕜 g s ∧
        (f = fun z ↦ (∏ x ∈ t, (z - x) ^ analyticOrderNatAt f x) • g z) ∧
        (∀ z ∈ s, g z ≠ 0) := by
  have hf_top : ∀ {f : 𝕜 → E}, AnalyticOnNhd 𝕜 f s → ¬EqOn f 0 s → ∀ x ∈ s,
      analyticOrderAt f x ≠ ⊤ := by
    intro f hfs hf₀ x hx hfx
    rw [analyticOrderAt_eq_top] at hfx
    exact hf₀ <| hfs.eqOn_zero_of_preconnected_of_eventuallyEq_zero hs_conn hx hfx
  obtain ⟨t, hts⟩ : ∃ t : Finset 𝕜, ∀ x, x ∈ t ↔ x ∈ s ∧ f x = 0 := by
    use hs_comp.finite_diff_of_mem_codiscreteWithin
      hfs.codiscreteWithin_setOf_analyticOrderAt_eq_zero_or_top |>.toFinset
    simp only [Finite.mem_toFinset, mem_diff, mem_setOf_eq, not_or, analyticOrderAt_eq_zero,
      and_congr_right_iff]
    push_neg
    intro x hx
    simp [hfs _ hx, hf_top hfs hf₀ x hx]
  use t, hts
  induction t using Finset.cons_induction generalizing f with
  | empty =>
    use f, hfs
    simpa using hts
  | cons a t hat iht =>
    simp only [Finset.mem_cons] at hts
    have has : a ∈ s := (hts a).mp (.inl rfl) |>.1
    obtain ⟨g, hga, hg₀, hfg⟩ : ∃ g, AnalyticOnNhd 𝕜 g s ∧ g a ≠ 0 ∧
        f = fun z ↦ (z - a) ^ analyticOrderNatAt f a • g z := by
      classical
      rcases hfs a has |>.analyticOrderAt_ne_top |>.mp
        (hf_top hfs hf₀ a has) with ⟨g, hga, hg₀, hfg⟩
      set g' := Function.update
        (fun z ↦ (z - a) ^ (-analyticOrderNatAt f a : ℤ) • f z) a (g a)
      have hgg' : g =ᶠ[nhds a] g' := by
        refine hfg.mono fun z hz ↦ ?_
        rcases eq_or_ne z a with rfl | hza
        · simp [g']
        · simp [g', hza, hz, sub_eq_zero]
      refine ⟨g', ?_, ?_, ?_⟩
      · intro z hz
        rcases eq_or_ne z a with rfl | hza
        · exact hga.congr hgg'
        · have : g' =ᶠ[nhds z] fun z ↦ (z - a) ^ (-analyticOrderNatAt f a : ℤ) • f z :=
            eventually_ne_nhds hza |>.mono fun w hw ↦ by simp [g', hw]
          rw [analyticAt_congr this]
          refine .smul (.zpow ?_ (by rwa [sub_ne_zero])) (hfs z hz)
          fun_prop
      · simp [g', hg₀]
      · ext z
        rcases eq_or_ne z a with rfl | hza
        · simpa [g'] using hfg.self_of_nhds
        · simp [g', hza, sub_eq_zero]
    have hgt : ∀ z, z ∈ t ↔ z ∈ s ∧ g z = 0 := by
      rw [hfg] at hts
      intro z
      rcases eq_or_ne z a with rfl | hza
      · simp [hg₀, hat]
      · simpa [hza, sub_eq_zero] using hts z
    have hgs₀ : ¬EqOn g 0 s := by
      intro hgs₀
      exact hg₀ <| hgs₀ has
    rcases iht hga hgs₀ hgt with ⟨g', hg's, hgg', hg'₀⟩
    use g', hg's, ?_, hg'₀
    ext z
    rw [congrFun hfg, congrFun hgg', Finset.prod_cons, mul_smul]
    congr 2
    refine Finset.prod_congr rfl fun x hx ↦ ?_
    congr 1
    conv_rhs => rw [hfg, analyticOrderNatAt]
    rw [← Pi.smul_def', analyticOrderAt_smul]
    · suffices analyticOrderAt (fun z ↦ (z - a) ^ analyticOrderNatAt f a) x = 0 by
        rw [this]
        simp [analyticOrderNatAt]
      rw [analyticOrderAt_eq_zero]
      right
      simp [sub_eq_zero, ne_of_mem_of_not_mem hx hat]
    · fun_prop
    · exact hga _ <| ((hts _).mp <| .inr hx).1

private theorem circleIntegral_logDeriv_eq_finsum_analyticOrderNatAdd515
    {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hf₀ : ∀ z ∈ sphere c R, f z ≠ 0)
    (hR : 0 ≤ R) :
    ∮ z in C(c, R), logDeriv f z =
      (2 * Real.pi * Complex.I) * ∑ᶠ z ∈ ball c R, analyticOrderNatAt f z := by
  rcases AnalyticOnNhd.exists_finset_eq_prod_smul_nonzero515 hf (isCompact_closedBall _ _)
    isPreconnected_closedBall
    (fun hf₀' ↦ ((NormedSpace.sphere_nonempty (x := c)).mpr hR).elim fun x hx ↦
      hf₀ x hx <| hf₀' <| sphere_subset_closedBall hx)
    with ⟨t, htR, g, hgR, hfg, hg₀⟩
  have hne : ∀ z ∈ sphere c R, ∀ w ∈ t, z - w ≠ 0 := by
    intro z hz w hw
    rw [sub_ne_zero]
    rintro rfl
    rw [htR] at hw
    exact hf₀ _ hz hw.2
  have ht_sub : ↑t ⊆ ball c R := by
    intro w hw
    rw [Finset.mem_coe, htR, ← sphere_union_ball, mem_union] at hw
    exact hw.1.resolve_left fun hw' ↦ hf₀ w hw' hw.2
  have hleft : EqOn (logDeriv f)
      (fun z ↦ (∑ w ∈ t, analyticOrderNatAt f w / (z - w)) + logDeriv g z)
      (sphere c R) := by
    intro z hz
    conv_lhs => rw [hfg]
    simp only [smul_eq_mul]
    rw [logDeriv_mul, logDeriv_prod]
    · congr 1
      refine Finset.sum_congr rfl fun w hw ↦ ?_
      rw [logDeriv_fun_pow (by fun_prop), logDeriv, Pi.div_apply, deriv_sub_const, deriv_id'']
      simp [div_eq_mul_inv]
    · intro w hw
      apply pow_ne_zero
      exact hne z hz w hw
    · intros
      fun_prop
    · rw [Finset.prod_ne_zero_iff]
      exact fun w hw ↦ pow_ne_zero _ (hne z hz w hw)
    · exact hg₀ z (sphere_subset_closedBall hz)
    · fun_prop
    · exact hgR _ (sphere_subset_closedBall hz) |>.differentiableAt
  rw [finsum_mem_eq_sum_of_subset (t := t), circleIntegral.integral_congr hR hleft]
  · have hdg : AnalyticOnNhd ℂ (logDeriv g) (closedBall c R) :=
      hgR.deriv.div hgR hg₀
    have hi : ∀ w ∈ t, CircleIntegrable (fun z ↦ analyticOrderNatAt f w / (z - w)) c R := by
      intro w hw
      simp only [div_eq_mul_inv]
      refine .const_mul (circleIntegrable_sub_inv_iff.mpr <| .inr fun hw' ↦ ?_) _
      rw [abs_of_nonneg hR] at hw'
      exact hne w hw' w hw (sub_self _)
    rw [circleIntegral.integral_add, circleIntegral.integral_fun_sum,
      DiffContOnCl.circleIntegral_eq_zero hR, add_zero, Nat.cast_sum, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun w hw ↦ ?_
      rw [circleIntegral_div_sub_of_differentiable_on_off_countable countable_empty]
      · exact ht_sub hw
      · fun_prop
      · intros
        fun_prop
    · exact hdg.differentiableOn.diffContOnCl_ball subset_rfl
    · exact hi
    · exact .fun_sum _ hi
    · exact hdg.continuousOn.mono sphere_subset_closedBall |>.circleIntegrable hR
  · rintro z ⟨hzc, hz⟩
    rw [mem_support, analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or,
      analyticOrderAt_eq_zero, not_or, not_not, ne_eq, not_not] at hz
    replace hz := hz.1.2
    rw [hfg, smul_eq_zero, Finset.prod_eq_zero_iff] at hz
    rcases hz.resolve_right (hg₀ z <| ball_subset_closedBall hzc) with ⟨w, hwt, hzw⟩
    have hzw' : z = w := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hzw)
    simpa [hzw'] using hwt
  · exact ht_sub

private theorem eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn515
    {ι : Type*} {U : Set ℂ} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hF : ∀ᶠ i in l, ∀ x ∈ U, F i x ≠ 0)
    (hFd : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U)
    (hf : TendstoLocallyUniformlyOn F f l U) :
    EqOn f 0 U ∨ ∀ x ∈ U, f x ≠ 0 := by
  have hfd : DifferentiableOn ℂ f U := hf.differentiableOn hFd hUo
  rw [or_iff_not_imp_left]
  intro hf₀ c hc hfc
  rcases hfd.analyticAt (hUo.mem_nhds hc) |>.eventually_eq_zero_or_eventually_ne_zero
    with hfc₀ | hfc₀
  · exact hf₀ <| hfd.analyticOnNhd hUo
      |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hc hfc₀
  · obtain ⟨R, hR₀, hRU, hfR⟩ :
        ∃ R > 0, closedBall c R ⊆ U ∧ ∀ w ∈ sphere c R, f w ≠ 0 := by
      rw [eventually_nhdsWithin_iff] at hfc₀
      rcases Metric.nhds_basis_closedBall.eventually_iff.mp (hfc₀.and <| hUo.eventually_mem hc)
        with ⟨R, hR₀, hR⟩
      refine ⟨R, hR₀, fun w hw ↦ (hR hw).2,
        fun w hw ↦ (hR <| sphere_subset_closedBall hw).1 ?_⟩
      exact ne_of_mem_sphere hw hR₀.ne'
    have hRU' : sphere c R ⊆ U := sphere_subset_closedBall.trans hRU
    have hlogDeriv : TendstoUniformlyOn (fun i ↦ logDeriv (F i)) (logDeriv f) l
        (sphere c R) := by
      simp only [logDeriv]
      have hderiv := (hf.deriv hFd hUo).mono hRU'
      rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
        (isCompact_sphere c R)]
      refine hderiv.fun_div₀ (hf.mono hRU') ?_ ?_ ?_
      · exact hfd.analyticOnNhd hUo |>.deriv |>.continuousOn |>.mono hRU'
      · exact hfd.continuousOn.mono hRU'
      · exact hfR
    have hcirc : Tendsto (fun i ↦ ∮ z in C(c, R), logDeriv (F i) z) l
        (nhds (∮ z in C(c, R), logDeriv f z)) := by
      apply hlogDeriv.tendsto_circleIntegral_of_continuousOn hR₀.le
      filter_upwards [hF, hFd] with i hi₀ hiD
      refine .div ?_ (hiD.continuousOn.mono hRU') ?_
      · exact hiD.analyticOnNhd hUo |>.deriv |>.continuousOn |>.mono hRU'
      · exact fun x hx ↦ hi₀ x (hRU' hx)
    have H₀ : ∀ᶠ i in l, ∮ (z : ℂ) in C(c, R), logDeriv (F i) z = 0 := by
      filter_upwards [hF, hFd] with i hi hid
      apply DiffContOnCl.circleIntegral_eq_zero hR₀.le
      exact (hid.deriv hUo).div hid hi |>.diffContOnCl_ball hRU
    have hlim := hcirc.congr' H₀
    rw [tendsto_const_nhds_iff, eq_comm,
      circleIntegral_logDeriv_eq_finsum_analyticOrderNatAdd515, mul_eq_zero] at hlim
    · replace hlim := hlim.resolve_left (by simp)
      norm_cast at hlim
      refine ne_of_gt ?_ hlim
      apply finsum_cond_pos
      · simp
      · use c
        suffices ∃ᶠ (x : ℂ) in nhds c, f x ≠ 0 by
          simpa [pos_iff_ne_zero, analyticOrderNatAt, analyticOrderAt_eq_zero, hfc,
            analyticOrderAt_eq_top, hfd.analyticAt (hUo.mem_nhds hc), hR₀]
        rw [eventually_nhdsWithin_iff] at hfc₀
        refine Frequently.mp ?_ hfc₀
        rw [frequently_iff_neBot, setOf_mem_eq, ← nhdsWithin]
        infer_instance
      · have hfinite := (isCompact_closedBall c R).finite_diff_of_mem_codiscreteWithin
          (((hfd.analyticOnNhd hUo).mono hRU)
            |>.codiscreteWithin_setOf_analyticOrderAt_eq_zero_or_top)
        refine hfinite.subset ?_
        simp +contextual [subset_def, analyticOrderNatAt, le_of_lt]
    · exact hfd.analyticOnNhd hUo |>.mono hRU
    · exact hfR
    · exact hR₀.le

private theorem eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn515
    {ι : Type*} {U : Set ℂ} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hF : ∀ᶠ i in l, InjOn (F i) U)
    (hFd : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U)
    (hf : TendstoLocallyUniformlyOn F f l U) :
    (∃ C, ∀ x ∈ U, f x = C) ∨ InjOn f U := by
  rw [or_iff_not_imp_left]
  intro hfU x hx y hy hxy
  by_contra! hne
  obtain ⟨r, hr₀, hrU, hry⟩ : ∃ r > 0, ball x r ⊆ U ∧ y ∉ ball x r := by
    simp_rw [← subset_compl_singleton_iff, ← subset_inter_iff, ← Metric.mem_nhds_iff]
    simp [hUo.mem_nhds hx, hne]
  have hf_sub : TendstoLocallyUniformlyOn
      (fun i z ↦ F i z - F i y) (fun z ↦ f z - f y) l (ball x r) := by
    refine (hf.mono hrU).fun_sub <|
      (Tendsto.tendstoUniformly_const ?_).tendstoUniformlyOn.tendstoLocallyUniformlyOn
    exact hf.tendsto_at hy
  refine eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn515
    isOpen_ball isPreconnected_ball
    (hF.mono fun i hi z hz ↦ ?_) ?_ hf_sub |>.resolve_left ?_ x (by simpa)
      (by rwa [sub_eq_zero])
  · rw [sub_ne_zero, hi.ne_iff (hrU hz) hy]
    exact ne_of_mem_of_not_mem hz hry
  · exact hFd.mono fun i hi ↦ hi.mono hrU |>.sub_const _
  · intro heq
    refine hfU ⟨f y, ?_⟩
    refine hf.differentiableOn hFd hUo |>.analyticOnNhd hUo
      |>.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hUc hx ?_
    exact heq.eventuallyEq_of_mem (ball_mem_nhds _ hr₀) |>.mono fun z hz ↦ sub_eq_zero.mp hz

private theorem exists_injective_not_dense_image_deriv_ne_zero515
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ univ) :
    ∃ f : ℂ → ℂ, Injective f ∧ ¬Dense (f '' U) ∧ ∀ z ∈ U, deriv f z ≠ 0 := by
  wlog hU₀ : 0 ∉ U
  · rw [ne_univ_iff_exists_notMem] at hU
    rcases hU with ⟨a, ha⟩
    specialize this (hUo.vadd (-a)) (by simpa) (by simp [hU])
      (by simpa [mem_vadd_set_iff_neg_vadd_mem])
    rcases this with ⟨f, hf_inj, hf_dense, hdf⟩
    refine ⟨f ∘ (-a + ·), hf_inj.comp (add_right_injective (-a)), ?_, fun z hz ↦ ?_⟩
    · simpa only [← image_vadd, Set.image_image] using! hf_dense
    · simpa [Function.comp_def, deriv_comp_const_add] using
        hdf (-a + z) (mapsTo_image _ _ hz)
  rcases Complex.exists_continuousOn_pow_eq hUc hUo continuousOn_id
    (by rwa [image_id]) two_ne_zero with ⟨f, hfc, hf_inv⟩
  replace hf_inv : LeftInverse (· ^ 2) f := hf_inv
  have hf₀ : ∀ z ∈ U, f z ≠ 0 := by
    intro z hz hfz
    simpa [hfz, (ne_of_mem_of_not_mem hz hU₀).symm] using hf_inv z
  have hdf : ∀ z ∈ U, HasStrictDerivAt f (2 * f z)⁻¹ z := by
    intro z hz
    apply HasStrictDerivAt.of_local_left_inverse
    · exact hfc.continuousAt <| hUo.mem_nhds hz
    · simpa using hasStrictDerivAt_pow 2 (f z)
    · simpa using hf₀ z hz
    · exact .of_forall hf_inv
  refine ⟨f, hf_inv.injective, ?_, fun z hz ↦ ?_⟩
  · simp only [Dense, not_forall, mem_closure_iff_frequently, not_frequently]
    rcases hUc.nonempty with ⟨x, hx⟩
    use -f x
    have hnhds : f '' U ∈ nhds (f x) := by
      rw [← (hdf x hx).map_nhds_eq (by simpa using hf₀ x hx)]
      exact Filter.image_mem_map <| hUo.mem_nhds hx
    rw [nhds_neg, eventually_neg]
    filter_upwards [hnhds]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    obtain rfl : a = b := by
      rw [← hf_inv b, hab]
      simp [hf_inv a]
    refine hf₀ a ha ?_
    linear_combination hab / 2
  · simpa [(hdf z hz).hasDerivAt.deriv] using hf₀ z hz

private theorem exists_mapsTo_unitBall_injOn_deriv_ne_zero515
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ univ) :
    ∃ f : ℂ → ℂ, MapsTo f U (ball 0 1) ∧ InjOn f U ∧
      ∀ z ∈ U, deriv f z ≠ 0 := by
  rcases exists_injective_not_dense_image_deriv_ne_zero515 hUo hUc hU
    with ⟨f, hf_inj, hfd, hdf⟩
  obtain ⟨x, ε, hε₀, hε⟩ : ∃ (x : ℂ) (ε : ℝ), 0 < ε ∧ ∀ a ∈ U, ε < dist (f a) x := by
    simpa [Dense, mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall] using hfd
  have hfx : ∀ z ∈ U, f z ≠ x := fun z hz ↦ by simpa using hε₀.trans (hε z hz)
  use fun z ↦ ε / (f z - x)
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rw [mem_ball_zero_iff, norm_div, norm_real, Real.norm_of_nonneg hε₀.le, div_lt_one₀]
    · simpa [dist_eq_norm] using hε z hz
    · simpa [sub_eq_zero] using hfx z hz
  · intro z hz w hw heq
    simpa [div_eq_mul_inv, hε₀.ne', hf_inj.eq_iff] using heq
  · intro z hz
    have hdz : DifferentiableAt ℂ f z := differentiableAt_of_deriv_ne_zero (hdf z hz)
    rw [(hasDerivAt_const _ _).fun_div (hdz.hasDerivAt.sub_const _) _ |>.deriv] <;>
      simp [*, ne_of_gt, sub_eq_zero]

private theorem exists_map_unitDisc_injOn_deriv_ne_zero₀515
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ univ)
    {x : ℂ} (hx : x ∈ U) :
    ∃ f : ℂ → Complex.UnitDisc, f x = 0 ∧ InjOn f U ∧
      (∀ z ∈ U, deriv (fun z ↦ (f z : ℂ)) z ≠ 0) := by
  classical
  obtain ⟨f, hf_inj, hf_deriv⟩ :
      ∃ f : ℂ → Complex.UnitDisc, InjOn f U ∧
        ∀ z ∈ U, deriv (fun z ↦ (f z : ℂ)) z ≠ 0 := by
    rcases exists_mapsTo_unitBall_injOn_deriv_ne_zero515 hUo hUc hU
      with ⟨f, hfU, hf_inj, hdf⟩
    let g : ℂ → Complex.UnitDisc := fun z ↦
      if hz : z ∈ U then Complex.UnitDisc.mk (f z) (by simpa using hfU hz) else 0
    refine ⟨g, ?_, ?_⟩
    · intro z hz w hw hzw
      apply hf_inj hz hw
      simpa [g, hz, hw] using congrArg ((↑·) : Complex.UnitDisc → ℂ) hzw
    · intro z hz
      convert hdf z hz using 1
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hUo.mem_nhds hz] with w hw
      simp [g, hw]
  let g : ℂ → Complex.UnitDisc := fun z ↦ Complex.UnitDisc.shift515 (-f x) (f z)
  refine ⟨g, ?_, Complex.UnitDisc.shift515 (-f x) |>.injective.comp_injOn hf_inj, ?_⟩
  · simp [g]
  · intro z hz
    simpa only [g, ne_eq, Complex.UnitDisc.deriv_shift515_comp_eq_zero] using hf_deriv z hz

private theorem exists_map_unitDisc_injOn_norm_deriv_gt515
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ univ)
    {x : ℂ} (hx : x ∈ U) {f : ℂ → Complex.UnitDisc}
    (hdf : DifferentiableOn ℂ (fun z ↦ (f z : ℂ)) U) (hf₀ : f x = 0)
    (hf_inj : InjOn f U) (hsurj : ¬SurjOn f U univ) :
    ∃ g : ℂ → Complex.UnitDisc, g x = 0 ∧ InjOn g U ∧
      DifferentiableOn ℂ (fun z ↦ (g z : ℂ)) U ∧
      ‖deriv (fun z ↦ (f z : ℂ)) x‖ < ‖deriv (fun z ↦ (g z : ℂ)) x‖ := by
  by_cases hdf₀ : deriv (fun z ↦ (f z : ℂ)) x = 0
  · rcases exists_map_unitDisc_injOn_deriv_ne_zero₀515 hUo hUc hU hx
      with ⟨g, hg₀, hg_inj, hdg⟩
    refine ⟨g, hg₀, hg_inj, fun z hz ↦
      (differentiableAt_of_deriv_ne_zero (hdg z hz)).differentiableWithinAt, ?_⟩
    simpa [hdf₀] using hdg x hx
  obtain ⟨c, hc⟩ : ∃ c, ∀ z ∈ U, f z ≠ c := by
    simpa [SurjOn, eq_univ_iff_forall] using hsurj
  have hcf : ContinuousOn f U := by
    rw [Complex.UnitDisc.isEmbedding_coe.continuousOn_iff]
    exact hdf.continuousOn
  rcases Complex.UnitDisc.exists_continuousOn_pow_eq hUc hUo
    ((-c).continuous_shift515.comp_continuousOn hcf) (by simpa) 2
    with ⟨g, hgc, hgf⟩
  have hg₀ : ∀ z ∈ U, g z ≠ 0 := by
    intro z hz
    suffices g z ^ (2 : ℕ+) ≠ 0 by simpa using this
    simp [hgf, Function.comp_def, hc z hz]
  have hdg : ∀ z ∈ U, HasDerivAt (fun z ↦ (g z : ℂ))
      (((1 - conj ((-c : Complex.UnitDisc) : ℂ) * (-c : Complex.UnitDisc)) /
          (1 + conj ((-c : Complex.UnitDisc) : ℂ) * f z) ^ 2 *
            deriv (fun z ↦ (f z : ℂ)) z) / (2 * g z)) z := by
    intro z hz
    have H := (hasDerivAt_pow 2 _).of_comp_left
      (Complex.UnitDisc.continuous_coe.continuousAt.comp <| hgc.continuousAt <| hUo.mem_nhds hz)
      (Complex.UnitDisc.hasDerivAt_shift515_comp (-c) <|
        (hdf.hasDerivAt <| hUo.mem_nhds hz))
      (by simp [Function.comp_def, hg₀ z hz])
      (.of_forall fun x ↦ congr(Complex.UnitDisc.coe $(hgf x)))
    simpa [Function.comp_def, hg₀ z hz] using H
  have hg_sq_norm (z : ℂ) :
      ‖(g z : ℂ)‖ ^ 2 = ‖((-c).shift515 (f z) : ℂ)‖ := by
    rw [← norm_pow, ← PNat.val_ofNat, ← Complex.UnitDisc.coe_pow, hgf]
    rfl
  let G : ℂ → Complex.UnitDisc := fun z ↦ (-g x).shift515 (g z)
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · simp [G]
  · refine Complex.UnitDisc.shift515 (-g x) |>.injective.comp_injOn
      fun z hz w hw hzw ↦ ?_
    simpa [hgf, hf_inj.eq_iff hz hw] using congr($hzw ^ (2 : ℕ+))
  · exact (-g x).differentiableOn_shift515_comp_iff.mpr fun z hz ↦
      (hdg z hz).differentiableAt.differentiableWithinAt
  · have hspos : 0 < ‖(g x : ℂ)‖ := norm_pos_iff.mpr <| by
      exact Complex.UnitDisc.coe_eq_zero.not.mpr (hg₀ x hx)
    have hslt : ‖(g x : ℂ)‖ < 1 := (g x).norm_lt_one
    have hsone : 0 < 1 - ‖(g x : ℂ)‖ ^ 2 := sub_pos.mpr (g x).sq_norm_lt_one
    have hsq : ‖(g x : ℂ)‖ ^ 2 = ‖(c : ℂ)‖ := by
      simpa [hf₀] using hg_sq_norm x
    have hkey : ‖deriv (fun z ↦ (G z : ℂ)) x‖ =
        ‖deriv (fun z ↦ (f z : ℂ)) x‖ *
          (‖(g x : ℂ)‖ + ‖(g x : ℂ)‖⁻¹) / 2 := by
      rw [Complex.UnitDisc.deriv_shift515_comp, (hdg x hx).deriv]
      simp only [G, norm_mul, norm_div, norm_pow, Complex.UnitDisc.coe_neg, map_neg,
        neg_mul, neg_neg, norm_ofNat]
      simp only [mul_neg, neg_neg]
      rw [← hsq]
      field_simp [hspos.ne']
      ring
    rw [hkey, mul_div_assoc]
    apply lt_mul_of_one_lt_right
    · simpa using hdf₀
    · rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      field_simp [hspos.ne']
      nlinarith [sq_pos_of_pos (sub_pos.mpr hslt)]

private theorem uniformEquicontinuousOn_of_thickening_subset_of_forall_norm_le515
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ι → E → F} {s U : Set E} {r : ℝ}
    (hr₀ : 0 < r) (hU : thickening r s ⊆ U) (hfd : ∀ i, DifferentiableOn ℂ (f i) U)
    (hf : ∃ C, ∀ i, ∀ z ∈ U, ‖f i z‖ ≤ C) : UniformEquicontinuousOn f s := by
  have hsU : s ⊆ U := (self_subset_thickening hr₀ _).trans hU
  rw [(uniformity_basis_dist.inf_principal _).uniformEquicontinuousOn_iff uniformity_basis_dist_le]
  intro ε hε
  rcases hf with ⟨C, hC⟩
  rcases exists_pos_mul_lt hε (2 * C / r) with ⟨δ, hδ₀, hδ⟩
  use min δ r, by positivity
  simp only [mem_setOf, mem_inter_iff, prodMk_mem_set_prod_eq]
  rintro x y ⟨hdist, hx, hy⟩ i
  rw [lt_min_iff] at hdist
  rw [thickening_eq_biUnion_ball, iUnion₂_subset_iff] at hU
  calc
    dist (f i x) (f i y) ≤ (2 * C / r) * dist x y := by
      apply Complex.dist_le_div_mul_dist_of_mapsTo_ball
      · exact (hfd i).mono (hU _ hy)
      · intro z hz
        rw [mem_closedBall, two_mul]
        exact dist_le_norm_add_norm _ _ |>.trans <|
          add_le_add (hC _ _ <| hU y hy hz) (hC _ _ <| hsU hy)
      · exact hdist.2
    _ ≤ _ := by
      grw [hdist.1]
      · exact hδ.le
      · have := (norm_nonneg _).trans (hC i x (hsU hx))
        positivity

private theorem equicontinuousAt_of_forall_norm_le515
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ι → E → F} {U : Set E} {x : E}
    (hU : U ∈ nhds x) (hfd : ∀ i, DifferentiableOn ℂ (f i) U)
    (hf : ∃ C, ∀ i, ∀ z ∈ U, ‖f i z‖ ≤ C) : EquicontinuousAt f x := by
  rcases nhds_basis_ball.mem_iff.mp hU with ⟨r, hr₀, hr⟩
  have hthick : thickening (r / 2) (ball x (r / 2)) ⊆ U := by
    grw [Metric.thickening_ball]
    rwa [add_halves]
  have heq := uniformEquicontinuousOn_of_thickening_subset_of_forall_norm_le515
    (by positivity) hthick hfd hf |>.equicontinuousOn x (by simpa)
  rwa [EquicontinuousWithinAt,
    nhdsWithin_eq_nhds.mpr (ball_mem_nhds _ (by positivity))] at heq

/-- The normalized domain-to-disk form of the Riemann mapping theorem.

The function is arbitrary off `U`; all analytic and bijectivity assertions are correctly scoped
to `U`. -/
theorem exists_riemannMap_to_unitDisk
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ univ)
    {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ BijOn f U (ball 0 1) ∧
      f x₀ = 0 ∧ ∀ z ∈ U, deriv f z ≠ 0 := by
  let 𝔖 : Set (Set ℂ) := {K | K ⊆ U ∧ IsCompact K}
  have h𝔖K : ∀ K ∈ 𝔖, IsCompact K := fun _ ↦ And.right
  have hcnt : (uniformity (ℂ →ᵤ[𝔖] ℂ)).IsCountablyGenerated := by
    let _ := hUo.locallyCompactSpace
    let _ : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
    let φ : CompactExhaustion U := default
    apply UniformOnFun.isCountablyGenerated_uniformity (t := fun n ↦ (↑·) '' φ n)
    · intro n
      exact ⟨image_val_subset, φ.isCompact n |>.image continuous_subtype_val⟩
    · exact monotone_image.comp φ.subset
    · rintro K ⟨hKU, hKc⟩
      lift K to Set U using hKU
      rw [← Subtype.isCompact_iff] at hKc
      exact (φ.exists_superset_of_isCompact hKc).imp fun n hn ↦ by gcongr
  let : (uniformity (ℂ →ᵤ[𝔖] ℂ)).IsCountablyGenerated := hcnt
  let F : (ℂ →ᵤ[𝔖] ℂ) → (ℂ → ℂ) := fun f ↦ UniformOnFun.toFun _ f
  have hF : ∀ {f : ℂ →ᵤ[𝔖] ℂ} {s},
      TendstoLocallyUniformlyOn F (F f) (nhdsWithin f s) U := by
    intro f s
    have hid : Tendsto id (nhdsWithin f s) (nhds f) :=
      tendsto_id'.mpr nhdsWithin_le_nhds
    simpa [tendstoLocallyUniformlyOn_iff_forall_isCompact hUo,
      UniformOnFun.tendsto_iff_tendstoUniformlyOn, 𝔖] using hid
  let s : Set (ℂ →ᵤ[𝔖] ℂ) :=
    {f : ℂ →ᵤ[𝔖] ℂ |
      MapsTo (F f) U (ball 0 1) ∧ InjOn (F f) U ∧
      DifferentiableOn ℂ (F f) U ∧
      deriv (F f) x₀ ≠ 0 ∧ F f x₀ = 0}
  have hsd : ∀ f ∈ s, DifferentiableOn ℂ (F f) U := fun f hf ↦ hf.2.2.1
  have hs_ne : s.Nonempty := by
    rcases exists_map_unitDisc_injOn_deriv_ne_zero₀515 hUo hUc hU hx₀
      with ⟨f, hf₀, hf_inj, hfd⟩
    exact ⟨UniformOnFun.ofFun 𝔖 (fun z ↦ (f z : ℂ)),
      fun x hx ↦ (f x).2,
      by simpa [F, InjOn] using hf_inj,
      fun z hz ↦ differentiableAt_of_deriv_ne_zero (hfd z hz) |>.differentiableWithinAt,
      hfd x₀ hx₀, by simp [F, hf₀]⟩
  have hcmpct := ArzelaAscoli.isCompact_closure_of_isClosedEmbedding h𝔖K
    (α := ℂ) (s := s) (F := F) .id ?eqcont ?bdd
  case eqcont =>
    rintro K ⟨hKU, -⟩ z hz
    refine equicontinuousAt_of_forall_norm_le515 (hUo.mem_nhds <| hKU hz)
      (fun i ↦ hsd _ i.2) ⟨1, fun i z hz ↦ le_of_lt ?_⟩ |>.equicontinuousWithinAt _
    simpa using i.2.1 hz
  case bdd =>
    intro K hK x hx
    exact ⟨closedBall 0 1, isCompact_closedBall _ _, fun i hi ↦
      ball_subset_closedBall <| hi.1 (hK.1 hx)⟩
  have hcl : closure s ⊆
      {f | MapsTo (F f) U (ball 0 1) ∧
           ((∃ C, EqOn (F f) (Function.const ℂ C) U) ∨ InjOn (F f) U) ∧
           DifferentiableOn ℂ (F f) U ∧
           F f x₀ = 0} := by
    intro f hf
    rw [mem_closure_iff_nhdsWithin_neBot] at hf
    have htendsto : TendstoLocallyUniformlyOn F (F f) (nhdsWithin f s) U := hF
    have hdf : DifferentiableOn ℂ (F f) U := htendsto.differentiableOn
      (eventually_mem_nhdsWithin.mono hsd) hUo
    have hf_le : ∀ z ∈ U, ‖F f z‖ ≤ 1 := by
      intro z hz
      refine le_of_tendsto (htendsto.tendsto_at hz).norm <|
        eventually_mem_nhdsWithin.mono ?_
      intro g hg
      apply le_of_lt
      simpa using hg.1 hz
    have hfx₀ : F f x₀ = 0 := by
      refine tendsto_nhds_unique (htendsto.tendsto_at hx₀) ?_
      refine tendsto_const_nhds.congr' <| eventually_mem_nhdsWithin.mono fun g hg ↦ ?_
      exact hg.2.2.2.2.symm
    refine ⟨?_, ?_, hdf, hfx₀⟩
    · by_contra hf_ball
      obtain ⟨z, hzU, hz⟩ : ∃ z ∈ U, 1 ≤ ‖F f z‖ := by simpa [MapsTo] using hf_ball
      have hmax : IsMaxOn (‖F f ·‖) U z := by
        intro y hy
        simpa using (hf_le y hy).trans hz
      have heq : F f x₀ = F f z := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
        hUc.isPathConnected.isConnected.isPreconnected hUo hdf hzU hmax hx₀
      norm_num [← heq, hfx₀] at hz
    · exact eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn515 hUo
        hUc.isPathConnected.isConnected.isPreconnected
        (eventually_mem_nhdsWithin.mono fun g hg ↦ hg.2.1)
        (eventually_mem_nhdsWithin.mono hsd) htendsto
  have hcont : ContinuousOn (fun f ↦ ‖deriv (F f) x₀‖) (closure s) := by
    refine .mono (.norm fun f hf ↦ ?_) hcl
    refine TendstoLocallyUniformlyOn.tendsto_at (.deriv hF ?_ hUo) hx₀
    refine eventually_mem_nhdsWithin.mono fun g hg ↦ ?_
    exact hg.2.2.1
  rcases hcmpct.exists_isMaxOn hs_ne.closure hcont with ⟨f₀, hf₀_mem, hf₀_max⟩
  have hdf₀_x₀ : 0 < ‖deriv (F f₀) x₀‖ := by
    rcases hs_ne with ⟨f', hf'⟩
    refine lt_of_lt_of_le ?_ (hf₀_max <| subset_closure hf')
    simpa using hf'.2.2.2.1
  rcases hcl hf₀_mem with ⟨hf₀_mapsTo, hf₀_inj, hf₀_diff, hf₀_x₀⟩
  replace hf₀_inj : InjOn (F f₀) U := by
    refine hf₀_inj.resolve_left ?_
    rintro ⟨C, hC⟩
    rw [hC.eventuallyEq_of_mem (hUo.mem_nhds hx₀) |>.deriv_eq] at hdf₀_x₀
    unfold Function.const at hdf₀_x₀
    simp at hdf₀_x₀
  have hf₀_surj : SurjOn (F f₀) U (ball 0 1) := by
    by_contra! hsurj
    clear hf₀_mem hdf₀_x₀
    rw [isMaxOn_iff] at hf₀_max
    wlog hf₀_lt : ∀ z, ‖F f₀ z‖ < 1 generalizing f₀
    · classical
      apply this (UniformOnFun.ofFun _ <| U.indicator (F f₀))
      · have hderiv : deriv (U.indicator (F f₀)) x₀ = deriv (F f₀) x₀ :=
          U.eqOn_indicator.eventuallyEq_of_mem (hUo.mem_nhds hx₀) |>.deriv_eq
        simpa [hderiv, F] using hf₀_max
      · simpa [F, U.eqOn_indicator.mapsTo_iff]
      · simpa [F, differentiableOn_congr U.eqOn_indicator]
      · simp [F, hf₀_x₀]
      · simpa [F, U.eqOn_indicator.injOn_iff]
      · simpa [F, U.eqOn_indicator.surjOn_iff]
      · intro z
        by_cases hz : z ∈ U <;> simp [F, hz, mem_ball_zero_iff.mp (hf₀_mapsTo _)]
    lift F f₀ to ℂ → Complex.UnitDisc using hf₀_lt with f hf
    replace hsurj : ¬SurjOn f U univ := by
      simpa [SurjOn, eq_univ_iff_forall, subset_def, Complex.UnitDisc.exists,
        ← Complex.UnitDisc.coe_inj] using hsurj
    rcases exists_map_unitDisc_injOn_norm_deriv_gt515 hUo hUc hU hx₀ hf₀_diff
      (by simpa using hf₀_x₀) (by simpa [InjOn] using hf₀_inj) hsurj
      with ⟨g, hg₀, hg_inj, hdg, hg_lt⟩
    refine hf₀_max (UniformOnFun.ofFun _ (fun z ↦ (g z : ℂ)))
      (subset_closure ?_) |>.not_gt hg_lt
    refine ⟨fun z _ ↦ (g z).2, by simpa [F, InjOn] using hg_inj, hdg,
      ?_, by simpa [F] using hg₀⟩
    rw [← norm_pos_iff]
    exact (norm_nonneg _).trans_lt hg_lt
  refine ⟨F f₀, hf₀_diff, ⟨hf₀_mapsTo, hf₀_inj, hf₀_surj⟩, hf₀_x₀, ?_⟩
  intro z hz
  exact hf₀_inj.deriv_ne_zero hUo hz (hf₀_diff.analyticAt <| hUo.mem_nhds hz)

/-- The normalized disk-to-domain form of the Riemann mapping theorem.

This is the form used by the short-path argument for Erdős Problem 515.  Besides bijectivity and
holomorphicity, the statement records the nonvanishing derivative at the center, which is needed
for the Koebe quarter estimate. -/
theorem exists_riemannMap
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ univ)
    {a : ℂ} (ha : a ∈ U) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ball 0 1) ∧
      BijOn F (ball 0 1) U ∧ F 0 = a ∧ deriv F 0 ≠ 0 := by
  rcases exists_riemannMap_to_unitDisk hUo hUc hU ha with
    ⟨f, hfd, hbij, hfa, hf_deriv⟩
  let F : ℂ → ℂ := Function.invFunOn f U
  have hinv : InvOn F f U (ball 0 1) := hbij.invOn_invFunOn
  have hF_maps : MapsTo F (ball 0 1) U := hbij.surjOn.mapsTo_invFunOn
  have hF_bij : BijOn F (ball 0 1) U :=
    hinv.symm.bijOn hF_maps hbij.mapsTo
  have hopen : ∀ s ⊆ U, IsOpen s → IsOpen (f '' s) := by
    refine (hfd.analyticOnNhd hUo).is_constant_or_isOpen
      hUc.isPathConnected.isConnected.isPreconnected |>.resolve_left ?_
    rintro ⟨w, hw⟩
    have heq := (show EqOn f (Function.const ℂ w) U from hw)
      |>.eventuallyEq_of_mem (hUo.mem_nhds ha) |>.deriv_eq
    apply hf_deriv a ha
    rw [heq]
    exact deriv_const a w
  have hF_cont : ∀ z ∈ ball (0 : ℂ) 1, ContinuousAt F z := by
    intro z hz
    rw [continuousAt_def]
    intro t ht
    rcases _root_.mem_nhds_iff.mp ht with ⟨s, hst, hsopen, hFs⟩
    have hFzU : F z ∈ U := hF_maps hz
    have himOpen : IsOpen (f '' (s ∩ U)) :=
      hopen _ inter_subset_right (hsopen.inter hUo)
    have hzimg : z ∈ f '' (s ∩ U) :=
      ⟨F z, ⟨hFs, hFzU⟩, hinv.2 hz⟩
    refine mem_of_superset (himOpen.mem_nhds hzimg) ?_
    rintro y ⟨x, ⟨hxs, hxU⟩, rfl⟩
    exact hst <| by simpa [hinv.1 hxU]
  have hF_hasDeriv : ∀ z ∈ ball (0 : ℂ) 1,
      HasDerivAt F (deriv f (F z))⁻¹ z := by
    intro z hz
    apply HasDerivAt.of_local_left_inverse (hF_cont z hz)
    · exact hfd.hasDerivAt <| hUo.mem_nhds (hF_maps hz)
    · exact hf_deriv (F z) (hF_maps hz)
    · exact eventually_of_mem (isOpen_ball.mem_nhds hz) hinv.2
  refine ⟨F, fun z hz ↦ (hF_hasDeriv z hz).differentiableAt.differentiableWithinAt,
    hF_bij, ?_, ?_⟩
  · apply hbij.injOn (hF_maps (by simp)) ha
    exact (hinv.2 (by simp)).trans hfa.symm
  · rw [(hF_hasDeriv 0 (by simp)).deriv]
    exact inv_ne_zero <| hf_deriv (F 0) (hF_maps (by simp))

/-- The unit-disk Koebe quarter theorem in the differentiability-on-open-set form used below. -/
theorem koebe_quarter_of_differentiableOn
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1)) :
    ball (f 0) (‖deriv f 0‖ / 4) ⊆ f '' (ball 0 1) :=
  koebe_quarter (hf.analyticOnNhd isOpen_ball) hinj

/-- A normalized Riemann map together with the exact Koebe-quarter inclusion used in the
short-path construction. -/
theorem exists_riemannMap_with_koebe
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ univ)
    {a : ℂ} (ha : a ∈ U) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ball 0 1) ∧
      BijOn F (ball 0 1) U ∧ F 0 = a ∧ deriv F 0 ≠ 0 ∧
      ball a (‖deriv F 0‖ / 4) ⊆ U := by
  rcases exists_riemannMap hUo hUc hU ha with ⟨F, hFd, hFbij, hFa, hFderiv⟩
  refine ⟨F, hFd, hFbij, hFa, hFderiv, ?_⟩
  rw [← hFa]
  intro y hy
  rcases koebe_quarter_of_differentiableOn hFd hFbij.injOn hy with ⟨z, hz, rfl⟩
  exact hFbij.mapsTo hz

end Erdos515
