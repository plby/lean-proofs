/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 861.
https://www.erdosproblems.com/forum/thread/861

Informal authors:
- David Saxton
- Andrew Thomason
- Yoshiharu Kohayakawa
- Sang June Lee
- Vojtěch Rödl
- Wojciech Samotij

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos861.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos862

/-!
# Erdős Problem 861

Let f N be the largest size of a Sidon subset of {1, ..., N}, and let
A N be the number of Sidon subsets of that interval. Saxton and Thomason's
five-choice construction gives a fixed logarithmic gap above 2 ^ f N.

This file proves both answers:

* (A N : ℝ) / 2 ^ f N tends to infinity;
* log (A N) / (f N * log 2) does not tend to 1.

The latter limit is the precise meaning of A(N) = 2^((1 + o(1)) f(N)).
The detailed mathematical proof and source reconstruction are in tex/861.tex.
-/

namespace Erdos861

open Filter
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The family of Sidon subsets of the exact interval {1, ..., N}. -/
noncomputable def sidonFamily (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset.filter
    (fun S : Finset ℕ => Erdos862.Sidon (S : Set ℕ))

/-- f(N): the largest cardinality of a Sidon subset of {1, ..., N}. -/
noncomputable def f (N : ℕ) : ℕ :=
  (sidonFamily N).sup Finset.card

/-- A(N): the number of Sidon subsets of {1, ..., N}. -/
noncomputable def A (N : ℕ) : ℕ :=
  (sidonFamily N).card

/-- The literal quotient in the first question of Problem 861. -/
noncomputable def normalizedRatio (N : ℕ) : ℝ :=
  (A N : ℝ) / (2 : ℝ) ^ f N

/-- The standard precise reading of A(N) = 2^((1 + o(1)) f(N)). -/
def UnitExponentAsymptotic : Prop :=
  Tendsto
    (fun N : ℕ =>
      Real.log (A N : ℝ) / ((f N : ℝ) * Real.log 2))
    atTop (nhds 1)

/-- Translation of a finite set by one. -/
def shift (S : Finset ℕ) : Finset ℕ :=
  S.image Nat.succ

/-- The successor image operation is injective on finite sets. -/
lemma shift_injective : Function.Injective shift := by
  intro S T hST
  ext x
  have hx := congrArg (fun U : Finset ℕ => x + 1 ∈ U) hST
  simpa [shift] using hx

/-- Translating every element by one preserves the Sidon property. -/
lemma sidon_shift_iff (S : Finset ℕ) :
    Erdos862.Sidon (shift S : Set ℕ) ↔ Erdos862.Sidon (S : Set ℕ) := by
  constructor
  · intro h a b c d ha hb hc hd habcd
    have hpair :=
      h (a + 1) (b + 1) (c + 1) (d + 1)
        (by
          change a + 1 ∈ S.image Nat.succ
          exact Finset.mem_image.mpr ⟨a, ha, by omega⟩)
        (by
          change b + 1 ∈ S.image Nat.succ
          exact Finset.mem_image.mpr ⟨b, hb, by omega⟩)
        (by
          change c + 1 ∈ S.image Nat.succ
          exact Finset.mem_image.mpr ⟨c, hc, by omega⟩)
        (by
          change d + 1 ∈ S.image Nat.succ
          exact Finset.mem_image.mpr ⟨d, hd, by omega⟩)
        (by omega)
    simpa [Set.pair_eq_pair_iff] using hpair
  · intro h a b c d ha hb hc hd habcd
    change a ∈ S.image Nat.succ at ha
    change b ∈ S.image Nat.succ at hb
    change c ∈ S.image Nat.succ at hc
    change d ∈ S.image Nat.succ at hd
    obtain ⟨a', haS, ha_eq⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hbS, hb_eq⟩ := Finset.mem_image.mp hb
    obtain ⟨c', hcS, hc_eq⟩ := Finset.mem_image.mp hc
    obtain ⟨d', hdS, hd_eq⟩ := Finset.mem_image.mp hd
    subst a
    subst b
    subst c
    subst d
    have hpair := h a' b' c' d' haS hbS hcS hdS (by omega)
    simpa [Set.pair_eq_pair_iff] using hpair

/-- Successor maps a subset of range N into {1, ..., N}. -/
lemma shift_subset_Icc {N : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range N) :
    shift S ⊆ Finset.Icc 1 N := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  have hyN := Finset.mem_range.mp (hS hy)
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

/-- Predecessor maps a subset of {1, ..., N} back into range N. -/
lemma pred_image_subset_range {N : ℕ} {T : Finset ℕ}
    (hT : T ⊆ Finset.Icc 1 N) :
    T.image Nat.pred ⊆ Finset.range N := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  have hyIcc := Finset.mem_Icc.mp (hT hy)
  have hypos : 0 < y := by omega
  exact Finset.mem_range.mpr
    ((Nat.pred_lt hypos.ne').trans_le hyIcc.2)

/-- On subsets of {1, ..., N}, predecessor followed by successor is exact. -/
lemma shift_pred_image {N : ℕ} {T : Finset ℕ}
    (hT : T ⊆ Finset.Icc 1 N) :
    shift (T.image Nat.pred) = T := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    have hzpos : 0 < z := by
      have := Finset.mem_Icc.mp (hT hz)
      omega
    change Nat.succ (Nat.pred z) ∈ T
    rw [Nat.succ_pred_eq_of_pos hzpos]
    exact hz
  · intro hx
    have hxpos : 0 < x := by
      have := Finset.mem_Icc.mp (hT hx)
      omega
    exact Finset.mem_image.mpr
      ⟨x.pred, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
        Nat.succ_pred_eq_of_pos hxpos⟩

/-- The zero-based Sidon family used internally by Problem 862. -/
noncomputable def zeroBasedFamily (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.range N).powerset.filter
    (fun S : Finset ℕ => Erdos862.Sidon (S : Set ℕ))

/-- Translation by one maps the zero-based family bijectively onto the
problem's family. -/
lemma image_zeroBasedFamily (N : ℕ) :
    (zeroBasedFamily N).image shift = sidonFamily N := by
  ext T
  constructor
  · intro hT
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
    have hS' := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr
          (shift_subset_Icc (Finset.mem_powerset.mp hS'.1)),
        (sidon_shift_iff S).2 hS'.2⟩
  · intro hT
    have hT' := Finset.mem_filter.mp hT
    have hTsub : T ⊆ Finset.Icc 1 N :=
      Finset.mem_powerset.mp hT'.1
    let S := T.image Nat.pred
    have hSsub : S ⊆ Finset.range N :=
      pred_image_subset_range hTsub
    have hshift : shift S = T :=
      shift_pred_image hTsub
    refine Finset.mem_image.mpr ⟨S, ?_, hshift⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hSsub,
        (sidon_shift_iff S).1 (hshift.symm ▸ hT'.2)⟩

/-- The exact count on {1, ..., N} agrees with the translated count already
used in the Problem 862 development. -/
theorem A_eq_erdos862_A (N : ℕ) : A N = Erdos862.A N := by
  rw [A, ← image_zeroBasedFamily]
  rw [Finset.card_image_of_injective _ shift_injective]
  rfl

/-- The exact extremal definition agrees with the existing one. -/
theorem f_eq_erdos862_f (N : ℕ) : f N = Erdos862.f N := by
  rfl

/-- The positive constant separating the Saxton--Thomason exponent from one
is exactly the constant already used in the Problem 862 development. -/
lemma eta_eq_log_gap :
    Erdos862.eta = Real.log 5 / 2 - Real.log 2 := by
  unfold Erdos862.eta
  rw [show (5 / 4 : ℝ) = 5 / 2 ^ 2 by norm_num,
    Real.log_div, Real.log_pow] <;> norm_num
  ring

lemma eta_pos : 0 < Erdos862.eta := by
  unfold Erdos862.eta
  exact mul_pos (by norm_num) (Real.log_pos (by norm_num))

/-- There is always at least the empty Sidon subset. -/
lemma A_pos (N : ℕ) : 0 < A N := by
  rw [A]
  refine Finset.card_pos.mpr ⟨∅, ?_⟩
  simp [sidonFamily, Erdos862.Sidon]

/-- Every nonempty interval contains the one-element Sidon set. -/
lemma f_pos_of_pos {N : ℕ} (hN : 0 < N) : 0 < f N := by
  have hmem : ({1} : Finset ℕ) ∈ sidonFamily N := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_singleton] at hx
      subst x
      exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    · intro a b c d ha hb hc hd _
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb hc hd
      subst a
      subst b
      subst c
      subst d
      rfl
  have hle : ({1} : Finset ℕ).card ≤ f N := by
    exact Finset.le_sup hmem
  simpa using lt_of_lt_of_le (by decide : 0 < ({1} : Finset ℕ).card) hle

/-- The two asymptotic inputs imply a fixed positive excess in the logarithm:
eventually log A(N) - f(N) log 2 is at least (eta / 2) sqrt N. -/
lemma eventually_log_excess :
    ∀ᶠ N : ℕ in atTop,
      (Erdos862.eta / 2) * Real.sqrt N ≤
        Real.log (A N : ℝ) - (f N : ℝ) * Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have heta : 0 < Erdos862.eta := eta_pos
  let ε : ℝ := Erdos862.eta / (4 * Real.log 2)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hA0 :=
    Erdos862.eventually_lower_bound
      (Real.log 5 / 2 - Erdos862.eta / 4) (by linarith)
  obtain ⟨N₀, hN₀⟩ := Erdos862.ErdosTuran ε hε
  have hf0 :
      ∀ᶠ N : ℕ in atTop,
        (Erdos862.f N : ℝ) ≤ (1 + ε) * Real.sqrt N :=
    eventually_atTop.mpr ⟨N₀, hN₀⟩
  filter_upwards [hA0, hf0, eventually_gt_atTop 0] with N hA_N hf_N hN
  rw [← A_eq_erdos862_A] at hA_N
  rw [← f_eq_erdos862_f] at hf_N
  have hsqrt : 0 < Real.sqrt N :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hlogA :
      (Real.log 5 / 2 - Erdos862.eta / 4) * Real.sqrt N ≤
        Real.log (A N : ℝ) := by
    calc
      (Real.log 5 / 2 - Erdos862.eta / 4) * Real.sqrt N
          ≤ (Real.log (A N : ℝ) / Real.sqrt N) * Real.sqrt N :=
        mul_le_mul_of_nonneg_right hA_N hsqrt.le
      _ = Real.log (A N : ℝ) := div_mul_cancel₀ _ hsqrt.ne'
  have hεlog :
      ε * Real.log 2 = Erdos862.eta / 4 := by
    dsimp [ε]
    field_simp [hlog2.ne']
  have hf_mul :=
    mul_le_mul_of_nonneg_right hf_N (Real.log_nonneg one_le_two)
  have hf_bound :
      (f N : ℝ) * Real.log 2 ≤
        (Real.log 2 + Erdos862.eta / 4) * Real.sqrt N := by
    calc
      (f N : ℝ) * Real.log 2
          ≤ (1 + ε) * Real.sqrt N * Real.log 2 := hf_mul
      _ = Real.sqrt N * Real.log 2 +
            (ε * Real.log 2) * Real.sqrt N := by ring
      _ = Real.sqrt N * Real.log 2 +
            (Erdos862.eta / 4) * Real.sqrt N := by rw [hεlog]
      _ = (Real.log 2 + Erdos862.eta / 4) * Real.sqrt N := by ring
  rw [eta_eq_log_gap] at hlogA hf_bound ⊢
  nlinarith

/-- The logarithmic excess itself tends to infinity. -/
lemma log_excess_tendsto_atTop :
    Tendsto
      (fun N : ℕ =>
        Real.log (A N : ℝ) - (f N : ℝ) * Real.log 2)
      atTop atTop := by
  have hsqrt :
      Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hscaled :
      Tendsto
        (fun N : ℕ => (Erdos862.eta / 2) * Real.sqrt N)
        atTop atTop :=
    hsqrt.const_mul_atTop (half_pos eta_pos)
  exact tendsto_atTop_mono' atTop eventually_log_excess hscaled

/-- Re-express the literal quotient as the exponential of its logarithmic
excess. -/
lemma normalizedRatio_eq_exp (N : ℕ) :
    normalizedRatio N =
      Real.exp
        (Real.log (A N : ℝ) - (f N : ℝ) * Real.log 2) := by
  rw [normalizedRatio, Real.exp_sub, Real.exp_log]
  · rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  · exact_mod_cast (A_pos N)

/-- Positive answer to the first question of Problem 861. -/
theorem ratio_tendsto_atTop :
    Tendsto normalizedRatio atTop atTop := by
  have hexp :
      Tendsto
        (fun N : ℕ =>
          Real.exp
            (Real.log (A N : ℝ) - (f N : ℝ) * Real.log 2))
        atTop atTop :=
    Real.tendsto_exp_atTop.comp log_excess_tendsto_atTop
  exact hexp.congr' (Eventually.of_forall fun N => (normalizedRatio_eq_exp N).symm)

/-- Eventually the base-two exponent of A(N) is separated from one by a
fixed positive constant. -/
lemma eventually_exponent_gap :
    ∀ᶠ N : ℕ in atTop,
      1 + Erdos862.eta / (4 * Real.log 2) ≤
        Real.log (A N : ℝ) / ((f N : ℝ) * Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have heta : 0 < Erdos862.eta := eta_pos
  obtain ⟨N₀, hN₀⟩ := Erdos862.ErdosTuran 1 (by norm_num)
  have hf2 :
      ∀ᶠ N : ℕ in atTop,
        (f N : ℝ) ≤ 2 * Real.sqrt N := by
    filter_upwards [eventually_atTop.mpr ⟨N₀, hN₀⟩] with N hN
    rw [f_eq_erdos862_f]
    norm_num at hN ⊢
    exact hN
  filter_upwards [eventually_log_excess, hf2, eventually_gt_atTop 0]
    with N hgap hf_N hN
  have hfpos : 0 < (f N : ℝ) :=
    Nat.cast_pos.mpr (f_pos_of_pos hN)
  rw [le_div_iff₀ (mul_pos hfpos hlog2)]
  have hf_eta :
      (Erdos862.eta / 4) * (f N : ℝ) ≤
        (Erdos862.eta / 2) * Real.sqrt N := by
    nlinarith [mul_le_mul_of_nonneg_left hf_N
      (by positivity : 0 ≤ Erdos862.eta / 4)]
  have hidentity :
      (1 + Erdos862.eta / (4 * Real.log 2)) *
          ((f N : ℝ) * Real.log 2) =
        (f N : ℝ) * Real.log 2 +
          (Erdos862.eta / 4) * (f N : ℝ) := by
    field_simp [hlog2.ne']
  rw [hidentity]
  linarith

/-- Negative answer to the second question of Problem 861. -/
theorem not_unitExponentAsymptotic :
    ¬ UnitExponentAsymptotic := by
  intro h
  unfold UnitExponentAsymptotic at h
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hδ : 0 < Erdos862.eta / (4 * Real.log 2) := by
    exact div_pos eta_pos (mul_pos (by norm_num) hlog2)
  have hupper :=
    h.eventually
      (gt_mem_nhds
        (show
          (1 : ℝ) <
            1 + (Erdos862.eta / (4 * Real.log 2)) / 2 by
          linarith))
  obtain ⟨N, hlower, hupper_N⟩ :=
    (eventually_exponent_gap.and hupper).exists
  linarith

/-- Complete resolution of Erdős Problem 861: the first answer is yes and the
second is no. -/
theorem erdos861 :
    Tendsto normalizedRatio atTop atTop ∧
      ¬ UnitExponentAsymptotic :=
  ⟨ratio_tendsto_atTop, not_unitExponentAsymptotic⟩

end

end Erdos861

#print axioms Erdos861.erdos861
