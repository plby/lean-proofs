/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import Wikipedia.HopfProblem.RiemannMappingDiscReduction
import Wikipedia.HopfProblem.RiemannMappingDiscShift
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Tactic

/-!
# Normalized disc embeddings and strict derivative improvement

Adapted from Yury Kudryashov's Riemann mapping theorem development,
Mathlib PR 33505, commit `d43061d911b1aeae0788591da437a3b115098962`,
lines 467–606.  The branch-root API is updated to the bundled Mathlib
version.  In addition to the source statement, the improvement preserves
nonvanishing derivatives throughout the domain when the input has that
property.
-/

noncomputable section

open Set Metric Function Filter
open scoped Topology ComplexConjugate Real

namespace Complex

theorem UnitDisc.hasDerivWithinAt_shift_comp {f : ℂ → UnitDisc} {z f' : ℂ} {s : Set ℂ}
    (w : UnitDisc) (hf : HasDerivWithinAt (fun x ↦ ↑(f x)) f' s z) :
    HasDerivWithinAt (fun x ↦ w.shift (f x) : ℂ → ℂ)
      ((1 - ‖(w : ℂ)‖ ^ 2) / (1 + conj ↑w * f z) ^ 2 * f') s z := by
  simp only [UnitDisc.coe_shift]
  refine ((hf.const_add (w : ℂ)).fun_div
    ((hf.const_mul (conj (w : ℂ))).const_add 1)
    (UnitDisc.shift_den_ne_zero w (f z))).congr_deriv ?_
  rw [← mul_conj']
  ring

theorem UnitDisc.hasDerivAt_shift_comp {f : ℂ → UnitDisc} {z f' : ℂ} (w : UnitDisc)
    (hf : HasDerivAt (fun x ↦ ↑(f x)) f' z) :
    HasDerivAt (fun x ↦ w.shift (f x) : ℂ → ℂ)
      ((1 - ‖(w : ℂ)‖ ^ 2) / (1 + conj ↑w * f z) ^ 2 * f') z :=
  (UnitDisc.hasDerivWithinAt_shift_comp w hf.hasDerivWithinAt).hasDerivAt univ_mem

@[simp] theorem UnitDisc.differentiableWithinAt_shift_comp_iff
    {f : ℂ → UnitDisc} {z : ℂ} {s : Set ℂ} (w : UnitDisc) :
    DifferentiableWithinAt ℂ (fun x ↦ w.shift (f x) : ℂ → ℂ) s z ↔
      DifferentiableWithinAt ℂ (f · : ℂ → ℂ) s z := by
  refine ⟨fun h ↦ ?_, fun h ↦
    (UnitDisc.hasDerivWithinAt_shift_comp w h.hasDerivWithinAt).differentiableWithinAt⟩
  simpa using (UnitDisc.hasDerivWithinAt_shift_comp (-w) h.hasDerivWithinAt).differentiableWithinAt

@[simp] theorem UnitDisc.differentiableOn_shift_comp_iff
    {f : ℂ → UnitDisc} {s : Set ℂ} (w : UnitDisc) :
    DifferentiableOn ℂ (fun x ↦ w.shift (f x) : ℂ → ℂ) s ↔
      DifferentiableOn ℂ (f · : ℂ → ℂ) s := by
  simp [DifferentiableOn]

@[simp] theorem UnitDisc.differentiableAt_shift_comp_iff
    {f : ℂ → UnitDisc} {z : ℂ} (w : UnitDisc) :
    DifferentiableAt ℂ (fun x ↦ w.shift (f x) : ℂ → ℂ) z ↔
      DifferentiableAt ℂ (f · : ℂ → ℂ) z := by
  refine ⟨fun h ↦ ?_, fun h ↦ (UnitDisc.hasDerivAt_shift_comp w h.hasDerivAt).differentiableAt⟩
  simpa using (UnitDisc.hasDerivAt_shift_comp (-w) h.hasDerivAt).differentiableAt

@[simp] theorem UnitDisc.deriv_shift_comp (f : ℂ → UnitDisc) (z : ℂ) (w : UnitDisc) :
    deriv (fun x ↦ w.shift (f x) : ℂ → ℂ) z =
      (1 - ‖(w : ℂ)‖ ^ 2) / (1 + conj ↑w * f z) ^ 2 * deriv (f · : ℂ → ℂ) z := by
  by_cases hfd : DifferentiableAt ℂ (f · : ℂ → ℂ) z
  · exact (UnitDisc.hasDerivAt_shift_comp w hfd.hasDerivAt).deriv
  · rw [deriv_zero_of_not_differentiableAt hfd, deriv_zero_of_not_differentiableAt, mul_zero]
    simpa using hfd

theorem UnitDisc.deriv_shift_comp_eq_zero (f : ℂ → UnitDisc) (z : ℂ) (w : UnitDisc) :
    deriv (fun x ↦ w.shift (f x) : ℂ → ℂ) z = 0 ↔ deriv (f · : ℂ → ℂ) z = 0 := by
  simp only [UnitDisc.deriv_shift_comp, mul_eq_zero, div_eq_zero_iff,
    pow_eq_zero_iff two_ne_zero, UnitDisc.shift_den_ne_zero, or_false]
  apply or_iff_right
  exact mod_cast sub_ne_zero.mpr w.sq_norm_lt_one.ne'

/-- A proper simply connected plane domain admits an injective disc map
normalized at a chosen point, with derivative nonzero throughout the domain. -/
theorem exists_map_unitDisc_injOn_deriv_ne_zero₀ {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) {x : ℂ} (_hx : x ∈ U) :
    ∃ f : ℂ → UnitDisc, f x = 0 ∧ InjOn f U ∧
      (∀ z ∈ U, deriv (UnitDisc.coe ∘ f) z ≠ 0) := by
  classical
  obtain ⟨f, hf_inj, hf_deriv⟩ :
      ∃ f : ℂ → UnitDisc, InjOn f U ∧ ∀ z ∈ U, deriv (UnitDisc.coe ∘ f) z ≠ 0 := by
    rcases exists_mapsTo_unitBall_injOn_deriv_ne_zero hUo hUc hU with ⟨f, hfU, hf_inj, hdf⟩
    use fun z ↦ if hz : z ∈ U then .mk (f z) (by simpa using hfU hz) else 0
    constructor
    · simp +contextual [InjOn, UnitDisc.mk_inj, hf_inj.eq_iff]
    · intro z hz
      convert hdf z hz using 1
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hUo.mem_nhds hz] with w hw
      simp [hw]
  use fun z ↦ (-f x).shift (f z)
  refine ⟨?_, (-f x).shift.injective.comp_injOn hf_inj, ?_⟩
  · simp
  · simpa only [Function.comp_def, ne_eq, UnitDisc.deriv_shift_comp_eq_zero]

/-- The source's square-root improvement, together with preservation of
nonvanishing derivatives wherever the input derivative does not vanish. -/
theorem exist_map_unitDisc_injOn_norm_deriv_gt_preserves_nonzero
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ univ)
    {x : ℂ} (hx : x ∈ U) {f : ℂ → UnitDisc}
    (hdf : DifferentiableOn ℂ (UnitDisc.coe ∘ f) U) (hf₀ : f x = 0) (hf_inj : InjOn f U)
    (hsurj : ¬SurjOn f U univ) :
    ∃ g : ℂ → UnitDisc, g x = 0 ∧ InjOn g U ∧ DifferentiableOn ℂ (UnitDisc.coe ∘ g) U ∧
      ‖deriv (UnitDisc.coe ∘ f) x‖ < ‖deriv (UnitDisc.coe ∘ g) x‖ ∧
      ((∀ z ∈ U, deriv (UnitDisc.coe ∘ f) z ≠ 0) →
        ∀ z ∈ U, deriv (UnitDisc.coe ∘ g) z ≠ 0) := by
  by_cases hdf₀ : deriv (UnitDisc.coe ∘ f) x = 0
  · rcases exists_map_unitDisc_injOn_deriv_ne_zero₀ hUo hUc hU hx with ⟨g, hg₀, hg_inj, hdg⟩
    refine ⟨g, hg₀, hg_inj, fun z hz ↦ ?_, ?_, fun _ => hdg⟩
    · exact (differentiableAt_of_deriv_ne_zero (hdg z hz)).differentiableWithinAt
    · simpa [hdf₀] using hdg x hx
  obtain ⟨c, hc⟩ : ∃ c, ∀ z ∈ U, f z ≠ c := by simpa [SurjOn, eq_univ_iff_forall] using hsurj
  have hcf : ContinuousOn f U := by
    rw [UnitDisc.isEmbedding_coe.continuousOn_iff]
    exact hdf.continuousOn
  rcases UnitDisc.exists_continuousOn_pow_eq hUc hUo
    ((-c).continuous_shift.comp_continuousOn hcf) (by simpa) 2 with ⟨g, hgc, hgf⟩
  have hg₀ : ∀ z ∈ U, g z ≠ 0 := by
    intro z hz
    suffices g z ^ (2 : ℕ+) ≠ 0 by simpa using this
    simp [hgf, hc z hz]
  have hdg : ∀ z ∈ U, HasDerivAt (g · : ℂ → ℂ)
      ((1 - ‖(c : ℂ)‖ ^ 2) / (2 * g z * (1 - conj ↑c * f z) ^ 2) *
        deriv (f · : ℂ → ℂ) z) z := by
    intro z hz
    refine ((hasDerivAt_pow 2 _).of_comp_left
      (UnitDisc.continuous_coe.continuousAt.comp <| hgc.continuousAt <| hUo.mem_nhds hz)
      (UnitDisc.hasDerivAt_shift_comp _ <| (hdf.hasDerivAt <| hUo.mem_nhds hz))
      (by simp [hg₀ z hz])
      (.of_forall fun a ↦ congr(UnitDisc.coe $(hgf a)))).congr_deriv ?_
    simp [Function.comp_def, field]
    ring
  have hg_sq_norm (z : ℂ) : ‖(g z : ℂ)‖ ^ 2 = ‖((-c).shift (f z) : ℂ)‖ := by
    rw [← norm_pow, ← PNat.val_ofNat, ← UnitDisc.coe_pow, hgf, Function.comp_apply]
  have hg_norm (z : ℂ) : ‖(g z : ℂ)‖ = √‖((-c).shift (f z) : ℂ)‖ := by
    rw [← Real.sqrt_sq (norm_nonneg _), hg_sq_norm]
  refine ⟨(-g x).shift ∘ g, ?map_x, ?injOn, ?deriv, ?norm_deriv, ?preserve⟩
  case map_x => simp
  case injOn =>
    refine (-g x).shift.injective.comp_injOn fun z hz w hw hzw ↦ ?_
    simpa [hgf, hf_inj.eq_iff hz hw] using congr($hzw ^ (2 : ℕ+))
  case deriv =>
    exact (-g x).differentiableOn_shift_comp_iff.mpr fun z hz ↦
      (hdg z hz).differentiableAt.differentiableWithinAt
  case norm_deriv =>
    have hkey : ‖deriv (UnitDisc.coe ∘ ⇑(-g x).shift ∘ g) x‖ =
        ‖deriv (f · : ℂ → ℂ) x‖ * (√‖(c : ℂ)‖ + √‖(c⁻¹ : ℂ)‖) / 2 := by
      have hgx : ‖(g x : ℂ)‖ = √‖(c : ℂ)‖ := by simp [hg_norm, hf₀]
      simp only [Function.comp_def, UnitDisc.deriv_shift_comp, (hdg x hx).deriv,
        norm_mul, norm_div, ← mul_assoc, conj_mul', UnitDisc.coe_neg, map_neg, neg_mul]
      conv_rhs => rw [mul_comm, mul_div_right_comm]
      congr 1
      norm_cast
      have hpos₁ : 0 < 1 - ‖(c : ℂ)‖ := sub_pos.2 c.norm_lt_one
      have hpos₂ : 0 < 1 - ‖(c : ℂ)‖ ^ 2 := sub_pos.2 c.sq_norm_lt_one
      simp [field, hgx, hf₀, ← sub_eq_add_neg, abs_of_pos, hpos₁, hpos₂]
      ring
    rw [hkey, mul_div_assoc]
    apply lt_mul_of_one_lt_right
    · simpa using hdf₀
    · have hc₀ : 0 < ‖(c : ℂ)‖ := by simpa [hf₀] using (hc x hx).symm
      suffices √‖(c : ℂ)‖ * 2 < ‖(c : ℂ)‖ + 1 by simpa [field] using this
      have : √‖(c : ℂ)‖ ≠ 1 := by simp [c.norm_ne_one]
      rw [← sub_ne_zero, ← sq_pos_iff, sub_sq, Real.sq_sqrt] at this
      · linear_combination this
      · apply norm_nonneg
  case preserve =>
    intro hnonzero z hz
    change deriv (fun a => ((-g x).shift (g a) : ℂ)) z ≠ 0
    rw [ne_eq, UnitDisc.deriv_shift_comp_eq_zero, (hdg z hz).deriv]
    apply mul_ne_zero
    · apply div_ne_zero
      · exact mod_cast sub_ne_zero.mpr c.sq_norm_lt_one.ne'
      · refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) (pow_ne_zero _ ?_)
        · simpa using hg₀ z hz
        · simpa only [UnitDisc.coe_neg, map_neg, neg_mul, ← sub_eq_add_neg] using
            UnitDisc.shift_den_ne_zero (-c) (f z)
    · exact hnonzero z hz

/-- If a normalized injective holomorphic disc map omits a point, then
another normalized injective disc map has strictly greater derivative norm. -/
theorem exist_map_unitDisc_injOn_norm_deriv_gt {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) {x : ℂ} (hx : x ∈ U) {f : ℂ → UnitDisc}
    (hdf : DifferentiableOn ℂ (UnitDisc.coe ∘ f) U) (hf₀ : f x = 0) (hf_inj : InjOn f U)
    (hsurj : ¬SurjOn f U univ) :
    ∃ g : ℂ → UnitDisc, g x = 0 ∧ InjOn g U ∧ DifferentiableOn ℂ (UnitDisc.coe ∘ g) U ∧
      ‖deriv (UnitDisc.coe ∘ f) x‖ < ‖deriv (UnitDisc.coe ∘ g) x‖ := by
  obtain ⟨g, hg₀, hgi, hgd, hgt, _⟩ :=
    exist_map_unitDisc_injOn_norm_deriv_gt_preserves_nonzero hUo hUc hU hx hdf hf₀ hf_inj hsurj
  exact ⟨g, hg₀, hgi, hgd, hgt⟩

/-- The strict derivative improvement also preserves the all-point
nonvanishing derivative condition used in the extremal class. -/
theorem exist_map_unitDisc_injOn_deriv_ne_zero_norm_deriv_gt
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ univ)
    {x : ℂ} (hx : x ∈ U) {f : ℂ → UnitDisc}
    (hdf : DifferentiableOn ℂ (UnitDisc.coe ∘ f) U) (hf₀ : f x = 0) (hf_inj : InjOn f U)
    (hsurj : ¬SurjOn f U univ) (hnonzero : ∀ z ∈ U, deriv (UnitDisc.coe ∘ f) z ≠ 0) :
    ∃ g : ℂ → UnitDisc, g x = 0 ∧ InjOn g U ∧ DifferentiableOn ℂ (UnitDisc.coe ∘ g) U ∧
      (∀ z ∈ U, deriv (UnitDisc.coe ∘ g) z ≠ 0) ∧
      ‖deriv (UnitDisc.coe ∘ f) x‖ < ‖deriv (UnitDisc.coe ∘ g) x‖ := by
  obtain ⟨g, hg₀, hgi, hgd, hgt, hpres⟩ :=
    exist_map_unitDisc_injOn_norm_deriv_gt_preserves_nonzero hUo hUc hU hx hdf hf₀ hf_inj hsurj
  exact ⟨g, hg₀, hgi, hgd, hpres hnonzero, hgt⟩

end Complex
