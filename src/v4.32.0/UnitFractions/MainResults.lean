import Mathlib
import UnitFractions.Definitions
import UnitFractions.AuxiliaryLemmas
import UnitFractions.Fourier
import UnitFractions.ForMathlib.BasicEstimates
import UnitFractions.ForMathlib.Misc

namespace UnitFractions

open scoped ArithmeticFunction.omega BigOperators
open Filter Finset Real
open _root_.Finset

/-!
This file ports the front compatibility surface of `src/main_results.lean`.

There is not much in Mathlib 4 corresponding directly to the project-specific statements in this
file. The main reusable Mathlib-backed ingredients come indirectly from the earlier local ports:

* `Definitions` for `rec_sum_local`, `interval_rare_ppowers`, `good_condition`, ...
* `AuxiliaryLemmas` for finset summation bounds and interval lemmas
* `ForMathlib.BasicEstimates` for the Chebyshev and prime-power infrastructure already upstream

The full declaration surface from the Lean 3 file is mirrored here. A couple of lemmas below have
already been ported with proofs. For the remaining declarations, the Lean 4 statements are present
so downstream files can target the right API shape while the proof transport continues.
-/

lemma good_d (N : ℕ) (M δ : ℝ) (A : Finset ℕ) (_hA₁ : A ⊆ Finset.range (N + 1)) (hM : 0 < M)
    (hAM : ∀ n ∈ A, M ≤ (n : ℝ))
    (hAq : ∀ q ∈ ppowers_in_set A, (2 : ℝ) * δ ≤ rec_sum_local A q)
    (I : Finset ℤ) (q : ℕ) (hq : q ∈ interval_rare_ppowers I A (M * δ)) :
    δ ≤ rec_sum_local (A.filter fun n => ∃ x ∈ I, ((n : ℤ) ∣ x)) q := by
  classical
  rw [interval_rare_ppowers, Finset.mem_filter] at hq
  let nA : Finset ℕ := A.filter fun n => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)
  have hnA : nA = A.filter fun n : ℕ => ¬ ∃ x ∈ I, ((n : ℤ) ∣ x) := by
    apply Finset.filter_congr
    intro n hn
    simp
  have hqpp : IsPrimePow q := (mem_ppowers_in_set.mp hq.1).1
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast hqpp.ne_zero
  have hqrare :
      (((local_part A q).filter fun n : ℕ => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)).card : ℝ) <
        (M * δ) / q := by
    simpa [Finset.fmap_def, Finset.filter_image,
      Finset.card_image_of_injective _ Nat.cast_injective] using hq.2
  have h1 : (rec_sum_local nA q : ℝ) ≤ δ := by
    rw [rec_sum_local, local_part, Finset.filter_comm, ← local_part, Rat.cast_sum]
    simp_rw [Rat.cast_div, Rat.cast_natCast]
    refine
      (sum_le_card_mul_real
        (A := (local_part A q).filter fun n => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x))
        (M := (q : ℝ) / M)
        (f := fun i => (q : ℝ) / i) ?_).trans ?_
    · intro i hi
      simp only [Finset.mem_filter, mem_local_part, and_assoc] at hi
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg q) hM (hAM _ hi.1)
    · refine (mul_le_mul_of_nonneg_right hqrare.le ?_).trans ?_
      · exact div_nonneg (Nat.cast_nonneg q) hM.le
      · have hEq : ((M * δ) / q) * ((q : ℝ) / M) = δ := by
          field_simp [hq0, hM.ne']
        exact hEq.le
  have h2 :
      rec_sum_local A q =
        rec_sum_local (A.filter fun n : ℕ => ∃ x ∈ I, ((n : ℤ) ∣ x)) q + rec_sum_local nA q := by
    rw [hnA, ← rec_sum_local_disjoint (Finset.disjoint_filter_filter_not _ _ _),
      Finset.filter_union_filter_not_eq]
  have h2' :
      (rec_sum_local A q : ℝ) =
        rec_sum_local (A.filter fun n : ℕ => ∃ x ∈ I, ((n : ℤ) ∣ x)) q + rec_sum_local nA q := by
    exact_mod_cast h2
  have h4 :
      2 * δ ≤
        (rec_sum_local
          (A.filter fun n : ℕ => ∃ x ∈ I, ((n : ℤ) ∣ x)) q : ℝ) + rec_sum_local nA q := by
    rw [← h2']
    exact hAq _ hq.1
  linarith

lemma explicit_mertens2 :
    ∀ᶠ N : ℕ in atTop,
      (((Finset.range (N + 1)).filter IsPrimePow).sum (fun q ↦ (1 / q : ℝ)) : ℝ) ≤
        (501 / 500 : ℝ) * log (log N) := by
  obtain ⟨b, hb⟩ := prime_power_reciprocal
  obtain ⟨c, hc₀, hc⟩ := hb.exists_pos
  filter_upwards
    [ (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (c : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (500 * (b + 1)))
    , tendsto_natCast_atTop_atTop.eventually hc.bound ] with N hN₁ hN₂ hN₃
  dsimp at hN₁ hN₂
  have hN₄ : 0 < log N := hc₀.trans_le hN₁
  simp_rw [norm_inv, ← div_eq_mul_inv, ← one_div, norm_eq_abs, abs_of_nonneg hN₄.le,
    Nat.floor_natCast]
    at hN₃
  have hdiv : c / log N ≤ 1 := by
    rw [div_le_iff₀ hN₄]
    linarith
  have hmain := sub_le_iff_le_add.1 (sub_le_of_abs_sub_le_right (hN₃.trans hdiv))
  have hsum :
      (((Finset.range (N + 1)).filter IsPrimePow).sum (fun q ↦ (1 / q : ℝ)) : ℝ) =
        ∑ q ∈ Finset.Icc 1 N with IsPrimePow q, (1 / q : ℝ) := by
    refine Finset.sum_congr ?_ fun _ _ => rfl
    rw [Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc]
    ext n
    simpa only
      [Finset.mem_filter, and_congr_left_iff, Finset.mem_Icc, zero_le, iff_and_self, true_and]
      using fun h _ => (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨h.ne_zero, h.ne_one⟩).le
  rw [hsum]
  exact
    hmain.trans
      (show log (log N) + b + 1 ≤ (501 / 500 : ℝ) * log (log N) by
        linarith)

lemma rec_sum_split (A B C E : Finset ℕ) (h : 0 ∉ B)
    (hC :
      C =
        A.filter fun n : ℕ => n ∈ B ∧ ∀ q ∈ ppowers_in_set A, n ∈ local_part B q → q ∈ E) :
    rec_sum ((A \ C) ∩ B) ≤ (((ppowers_in_set A) \ E).sum fun q => (rec_sum_local B q) / q) := by
  classical
  simp_rw [rec_sum, rec_sum_local, Finset.sum_div]
  calc
    (((A \ C) ∩ B).sum fun n => (1 : ℚ) / n) ≤
        ((((ppowers_in_set A) \ E).biUnion fun x => local_part B x).sum fun n => (1 : ℚ) / n) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro n hn
        rw [hC] at hn
        rw [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_filter, not_and, not_and] at hn
        have hn' := hn.1.2 hn.1.1 hn.2
        rw [not_forall] at hn'
        rcases hn' with ⟨q, hq⟩
        rw [Classical.not_imp, Classical.not_imp] at hq
        rw [Finset.mem_biUnion]
        refine ⟨q, ?_, hq.2.1⟩
        rw [Finset.mem_sdiff]
        exact ⟨hq.1, hq.2.2⟩
      · intro i hi₁ hi₂
        rw [one_div_nonneg]
        exact Nat.cast_nonneg i
    _ ≤ (((ppowers_in_set A) \ E).sum fun x => (local_part B x).sum fun x₁ => (1 : ℚ) / x₁) := by
      exact sum_bUnion_le_sum_of_nonneg fun i hi => by
        rw [one_div_nonneg]
        exact Nat.cast_nonneg i
    _ ≤ (((ppowers_in_set A) \ E).sum fun q => (local_part B q).sum fun i => (q : ℚ) / i / q) := by
      have hlast :
          (((ppowers_in_set A) \ E).sum fun x => (local_part B x).sum fun x₁ => (1 : ℚ) / x₁) =
            (((ppowers_in_set A) \ E).sum fun q =>
              (local_part B q).sum fun i => (q : ℚ) / i / q) := by
        rw [Finset.sum_congr rfl]
        intro x hx
        rw [Finset.sum_congr rfl]
        intro x₁ hx₁
        rw [local_part, Finset.mem_filter] at hx₁
        have hx0 : (x : ℚ) ≠ 0 := by
          exact_mod_cast (mem_ppowers_in_set.mp (Finset.mem_sdiff.mp hx).1).1.ne_zero
        have hx₁0 : (x₁ : ℚ) ≠ 0 := by
          intro hz
          apply h
          exact (by exact_mod_cast hz : x₁ = 0) ▸ hx₁.1
        field_simp [hx0, hx₁0]
      exact hlast.le

private lemma force_good_properties_hIcard0
    (N : ℕ) (M t : ℝ) (I : Finset ℤ)
    (hI :
      I =
        Finset.Icc
          ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉
          ⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋)
    (h0M : 0 < M) :
    (I.card : ℤ) =
      ⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ + 1 -
        ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉ := by
  rw [hI, Int.card_Icc]
  have hnonneg :
      0 ≤
        ⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ + 1 -
          ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉ := by
    refine sub_nonneg.mpr ?_
    rw [Int.ceil_le]
    have hwidth_nonneg : 0 ≤ M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) := by
      exact mul_nonneg h0M.le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    have hlt :
        t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2 <
          ↑(⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ + 1 : ℤ) := by
      calc
        t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2 ≤
            t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2 := by
          linarith
        _ < (⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ : ℝ) + 1 := by
          exact Int.lt_floor_add_one _
        _ = ↑(⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ + 1 : ℤ) := by
          norm_num
    exact le_of_lt hlt
  exact_mod_cast Int.toNat_of_nonneg hnonneg

private lemma force_good_properties_hIcardn0
    (N : ℕ) (M t : ℝ) (I : Finset ℤ)
    (hI :
      I =
        Finset.Icc
          ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉
          ⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋)
    (hlarge1 : 1 ≤ M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) :
    I.card ≠ 0 := by
  have hIne : I.Nonempty := by
    rw [hI, Finset.nonempty_Icc]
    rw [Int.ceil_le]
    have hfloor :
        t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2 - 1 <
          (⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ : ℤ) := by
      exact Int.sub_one_lt_floor _
    have hgap :
        t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2 ≤
          t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2 - 1 := by
      nlinarith
    exact le_trans hgap (le_of_lt hfloor)
  exact Finset.card_ne_zero.mpr hIne

private lemma force_good_properties_hIcard'
    (N : ℕ) (M t : ℝ) (I : Finset ℤ)
    (hIcard0 :
      (I.card : ℤ) =
        ⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ + 1 -
          ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉) :
    (I.card : ℝ) ≤ M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) + 1 := by
  rw [show (I.card : ℝ) = ((I.card : ℤ) : ℝ) by norm_num, hIcard0]
  push_cast
  calc
    (⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ : ℝ) + 1 -
        ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉ ≤
      t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2 + 1 -
        ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉ := by
      rw [sub_le_sub_iff_right, add_le_add_iff_right]
      exact Int.floor_le _
    _ ≤
      t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2 + 1 -
        (t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2) := by
      rw [sub_le_sub_iff_left]
      exact Int.le_ceil _
    _ = M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) + 1 := by
      ring

private lemma force_good_properties_hIcard''
    (N : ℕ) (M : ℝ) (I : Finset ℤ)
    (hIcard' : (I.card : ℝ) ≤ M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) + 1)
    (hlarge1 : 1 ≤ M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) :
    (I.card : ℝ) ≤ 2 * M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) := by
  nlinarith

private lemma force_good_properties_hlarge9
    (N : ℕ) (M : ℝ) (I : Finset ℤ)
    (hlarge : 1 < N)
    (h0M : 0 < M)
    (hlargeNs :
      (2 : ℝ) * (N : ℝ) ^ (-2 / log (log N) + 2 * log 2 / log (log N) * (1 + 1 / 3)) <
        log N ^ (-((1 : ℝ) / 101)) / 6)
    (hIcard'' : (I.card : ℝ) ≤ 2 * M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)))
    (hIcardn0 : I.card ≠ 0) :
    (N : ℝ) ^ (2 * log 2 / log (log N) * (1 + 1 / 3)) <
      M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ) := by
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (lt_trans zero_lt_one hlarge)
  have hcardpos : 0 < (I.card : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hIcardn0
  have hpowpos : 0 < (N : ℝ) ^ (2 * log 2 / log (log N) * (1 + 1 / 3)) := by
    exact Real.rpow_pos_of_pos hNpos _
  refine (_root_.lt_div_iff₀ hcardpos).2 ?_
  calc
    (N : ℝ) ^ (2 * log 2 / log (log N) * (1 + 1 / 3)) * (I.card : ℝ) ≤
        (N : ℝ) ^ (2 * log 2 / log (log N) * (1 + 1 / 3)) *
          (2 * M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) := by
      exact mul_le_mul_of_nonneg_left hIcard'' (le_of_lt hpowpos)
    _ = M * (2 * (N : ℝ) ^ (-2 / log (log N) + 2 * log 2 / log (log N) * (1 + 1 / 3))) := by
      calc
        (N : ℝ) ^ (2 * log 2 / log (log N) * (1 + 1 / 3)) *
            (2 * M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) =
            2 * M *
              ((N : ℝ) ^ (2 * log 2 / log (log N) * (1 + 1 / 3)) *
                (N : ℝ) ^ (-(2 : ℝ) / log (log N))) := by
              ring
        _ = 2 * M * (N : ℝ) ^ (-2 / log (log N) + 2 * log 2 / log (log N) * (1 + 1 / 3)) := by
          rw [show (N : ℝ) ^ (2 * log 2 / log (log N) * (1 + 1 / 3)) *
              (N : ℝ) ^ (-(2 : ℝ) / log (log N)) =
              (N : ℝ) ^ (-2 / log (log N) + 2 * log 2 / log (log N) * (1 + 1 / 3)) by
                rw [mul_comm, ← Real.rpow_add hNpos]
              ]
        _ = M * (2 * (N : ℝ) ^ (-2 / log (log N) + 2 * log 2 / log (log N) * (1 + 1 / 3))) := by
          ring
    _ < M * (log N ^ (-(1 / 101 : ℝ)) / 6) := by
      exact mul_lt_mul_of_pos_left hlargeNs h0M

private lemma force_good_properties_hIclose'
    (N : ℕ) (M t : ℝ) (I : Finset ℤ)
    (hI :
      I =
        Finset.Icc
          ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉
          ⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋)
    (hlarge2 : M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) ≤ N) :
    ∀ x ∈ I, ∀ y ∈ I, (|x - y| : ℝ) ≤ N := by
  intro x hx y hy
  refine le_trans (two_in_Icc' I hI hx hy) ?_
  calc
    (((⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ : ℤ) : ℝ) -
        ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉) ≤
      t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2 -
        ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉ := by
      rw [sub_le_sub_iff_right]
      exact Int.floor_le _
    _ ≤
      t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2 -
        (t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2) := by
      rw [sub_le_sub_iff_left]
      exact Int.le_ceil _
    _ = M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) := by
      ring
    _ ≤ N := hlarge2

private lemma force_good_properties_hIclose
    (N : ℕ) (I : Finset ℤ)
    (hIclose' : ∀ x ∈ I, ∀ y ∈ I, (|x - y| : ℝ) ≤ N) :
    ∀ x ∈ I, ∀ y ∈ I, Int.natAbs (x - y) ≤ N := by
  intro x hx y hy
  have hxy := hIclose' x hx y hy
  rw [nat_cast_diff_issue] at hxy
  exact_mod_cast hxy

private lemma force_good_properties_two_values_case
    (N : ℕ) (M c : ℝ) (A A_I E : Finset ℕ) (I : Finset ℤ) (x1 x2 : ℕ) (f : ℕ → ℤ)
    (hA : A ⊆ Finset.range (N + 1))
    (h0A : 0 ∉ A)
    (h0M : 0 < M)
    (hMA : ∀ n ∈ A, M ≤ (n : ℝ))
    (hrecA : (log N) ^ (-(1 / 101 : ℝ)) ≤ rec_sum A)
    (hlarge0 : 0 < log N)
    (hlarge5 :
      1 / log N + (1 / (2 * log N ^ ((1 : ℝ) / 100))) * ((501 / 500 : ℝ) * log (log N)) ≤
        log N ^ (-(1 / 101 : ℝ)) / 6)
    (hlarge3 : 0 < log (log N))
    (hnum : (502 / 500 : ℝ) - c ≤ 2 / 3)
    (hzI : ¬ (0 : ℤ) ∈ I)
    (hP :
      ↑(((@Finset.image ℕ ℤ (fun a b ↦ Classical.propDecidable (a = b)) Nat.cast A).filter
          fun n : ℤ => ∀ x ∈ I, ¬ n ∣ x).card) <
        M / log N)
    (hnoB :
      ¬ ∃ B ⊆ A, rec_sum A ≤ 3 * rec_sum B ∧ (ppower_rec_sum B : ℝ) ≤ (2 / 3) * log (log N))
    (hrecN :
      ∀ x y : ℤ,
        x ≠ y →
          |(x : ℝ) - y| ≤ N →
            ((Finset.range (N + 1)).filter
                (fun n : ℕ ↦ IsPrimePow n ∧ (n : ℤ) ∣ x ∧ (n : ℤ) ∣ y)).sum
              (fun q : ℕ ↦ (1 : ℝ) / q) <
              ((1 : ℝ) / 500) * log (log N))
    (hsum4 : (ppower_rec_sum A : ℝ) ≤ (501 / 500 : ℝ) * log (log N))
    (hlarge9 :
      (N : ℝ) ^ (2 * log 2 / log (log N) * (1 + 1 / 3)) <
        M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ))
    (hdiv :
      ∀ n : ℕ,
        n ≤ N ^ 2 →
          (ArithmeticFunction.sigma 0 n : ℝ) ≤
            N ^ (2 * log 2 / log (log (N : ℝ)) * (1 + 1 / 3)))
    (hIclose : ∀ x ∈ I, ∀ y ∈ I, Int.natAbs (x - y) ≤ N)
    (hA_I : A_I = A.filter fun n : ℕ => ∃ x ∈ I, (n : ℤ) ∣ x)
    (hE :
      E =
        (ppowers_in_set A).filter
          (fun q : ℕ => 1 / (2 * log N ^ ((1 : ℝ) / 100)) ≤ rec_sum_local A_I q))
    (hf :
      ∀ q ∈ E,
        f q ∈ I ∧
          ((q : ℤ) ∣ f q) ∧
            c * log (log N) ≤
              ((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f q).sum
                (fun r : ℕ => (1 / r : ℝ)))
    (hx1E : x1 ∈ E)
    (hx2E : x2 ∈ E)
    (hclose12 : |(f x2 : ℝ) - f x1| ≤ N)
    (htwoxs : f x2 ≠ f x1)
    (hthreexs : ∀ x ∈ E, f x = f x1 ∨ f x = f x2) :
    (x2 : ℤ) ∣ f x1 := by
  classical
  exfalso
  let A1 := A.filter fun n : ℕ => (n : ℤ) ∣ f x1
  let A2 := A.filter fun n : ℕ => (n : ℤ) ∣ f x2
  let A0 := A \ (A1 ∪ A2)
  have hf1 := hf x1 hx1E
  have hf2 := hf x2 hx2E
  have h3rec : rec_sum A ≤ rec_sum A1 + rec_sum A2 + rec_sum A0 := by
    refine le_trans ?_ rec_sum_le_three
    refine rec_sum_mono ?_
    intro n hn
    rw [Finset.mem_union]
    by_cases htemp : n ∈ A1 ∪ A2
    · exact Or.inl htemp
    · exact Or.inr <| Finset.mem_sdiff.mpr ⟨hn, htemp⟩
  by_cases hAlarge : rec_sum A ≤ 3 * rec_sum A1 ∨ rec_sum A ≤ 3 * rec_sum A2
  · apply hnoB
    let P1 := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x1
    let P2 := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x2
    let P12 := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x1 ∧ (n : ℤ) ∣ f x2
    have hrecAs :
        P1.sum (fun q : ℕ => (1 : ℝ) / q) + P2.sum (fun q : ℕ => (1 : ℝ) / q) ≤
          (502 / 500 : ℝ) * log (log N) := by
      have hunion :
          P1.sum (fun q : ℕ => (1 : ℝ) / q) + P2.sum (fun q : ℕ => (1 : ℝ) / q) =
            (P1 ∪ P2).sum (fun q : ℕ => (1 : ℝ) / q) + P12.sum (fun q : ℕ => (1 : ℝ) / q) := by
        dsimp [P1, P2, P12]
        have h :=
          (Finset.sum_union_inter
            (s₁ := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x1)
            (s₂ := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x2)
            (f := fun q : ℕ => (1 : ℝ) / q)).symm
        simpa [Finset.filter_inter, Finset.inter_filter, Finset.inter_self, Finset.filter_filter,
          and_left_comm, and_right_comm, and_assoc, add_comm, add_left_comm, add_assoc] using h
      have hunion_subset : P1 ∪ P2 ⊆ ppowers_in_set A := by
        intro q hq
        rcases Finset.mem_union.mp hq with hq | hq
        · exact Finset.mem_of_mem_filter _ hq
        · exact Finset.mem_of_mem_filter _ hq
      calc
        P1.sum (fun q : ℕ => (1 : ℝ) / q) + P2.sum (fun q : ℕ => (1 : ℝ) / q) =
            (P1 ∪ P2).sum (fun q : ℕ => (1 : ℝ) / q) + P12.sum (fun q : ℕ => (1 : ℝ) / q) := hunion
        _ ≤ (ppower_rec_sum A : ℝ) + P12.sum (fun q : ℕ => (1 : ℝ) / q) := by
              rw [add_le_add_iff_right, ppower_rec_sum]
              push_cast
              exact Finset.sum_le_sum_of_subset_of_nonneg hunion_subset fun i _ _ => by
                rw [one_div_nonneg]
                exact Nat.cast_nonneg i
        _ ≤ (ppower_rec_sum A : ℝ) + ((1 : ℝ) / 500) * log (log N) := by
              rw [add_le_add_iff_left]
              refine le_trans ?_ (le_of_lt (hrecN (f x2) (f x1) htwoxs hclose12))
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
              · intro r hr
                rw [Finset.mem_filter] at hr
                rw [Finset.mem_filter]
                rw [ppowers_in_set, Finset.mem_biUnion] at hr
                rcases hr.1 with ⟨m, hmA, hmq⟩
                rw [Finset.mem_filter, Nat.mem_divisors] at hmq
                refine ⟨?_, hmq.2.1, hr.2.2, hr.2.1⟩
                rw [Finset.mem_range]
                exact lt_of_le_of_lt
                  (Nat.le_of_dvd (Nat.pos_of_ne_zero hmq.1.2) hmq.1.1)
                  (by
                    rw [← Finset.mem_range]
                    exact hA hmA)
              · intro i _ _
                rw [one_div_nonneg]
                exact Nat.cast_nonneg i
        _ ≤ (501 / 500 : ℝ) * log (log N) + ((1 : ℝ) / 500) * log (log N) := by
              rw [add_le_add_iff_right]
              exact hsum4
        _ = (502 / 500 : ℝ) * log (log N) := by
              ring_nf
    rcases hAlarge with hA1large | hA2large
    · refine ⟨A1, Finset.filter_subset _ _, hA1large, ?_⟩
      rw [ppower_rec_sum]
      push_cast
      calc
        ((ppowers_in_set A1).sum fun q : ℕ => (1 : ℝ) / q) ≤ P1.sum (fun q : ℕ => (1 : ℝ) / q) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
              · intro q hq
                rw [ppowers_in_set, Finset.mem_biUnion] at hq
                rcases hq with ⟨a, ha, hq⟩
                rw [Finset.mem_filter] at ha
                exact Finset.mem_filter.mpr ⟨
                  (ppowers_in_set_subset (A := A1) (B := A) (Finset.filter_subset _ _))
                    (by
                      rw [ppowers_in_set, Finset.mem_biUnion]
                      refine ⟨a, ?_, hq⟩
                      dsimp [A1]
                      rw [Finset.mem_filter]
                      exact ha),
                  dvd_trans (by
                    norm_cast
                    exact Nat.dvd_of_mem_divisors (Finset.mem_of_mem_filter q hq)) ha.2⟩
              · intro i _ _
                rw [one_div_nonneg]
                exact Nat.cast_nonneg i
        _ ≤ (502 / 500 : ℝ) * log (log N) -
              (((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x2).sum
                fun q : ℕ => (1 : ℝ) / q) := by
              rw [le_sub_iff_add_le]
              exact hrecAs
        _ ≤ (502 / 500 : ℝ) * log (log N) - c * log (log N) := by
              rw [sub_le_sub_iff_left]
              exact hf2.2.2
        _ ≤ (2 / 3 : ℝ) * log (log N) := by
              nlinarith
    · refine ⟨A2, Finset.filter_subset _ _, hA2large, ?_⟩
      rw [ppower_rec_sum]
      push_cast
      calc
        ((ppowers_in_set A2).sum fun q : ℕ => (1 : ℝ) / q) ≤ P2.sum (fun q : ℕ => (1 : ℝ) / q) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
              · intro q hq
                rw [ppowers_in_set, Finset.mem_biUnion] at hq
                rcases hq with ⟨a, ha, hq⟩
                rw [Finset.mem_filter] at ha
                exact Finset.mem_filter.mpr ⟨
                  (ppowers_in_set_subset (A := A2) (B := A) (Finset.filter_subset _ _))
                    (by
                      rw [ppowers_in_set, Finset.mem_biUnion]
                      refine ⟨a, ?_, hq⟩
                      dsimp [A2]
                      rw [Finset.mem_filter]
                      exact ha),
                  dvd_trans (by
                    norm_cast
                    exact Nat.dvd_of_mem_divisors (Finset.mem_of_mem_filter q hq)) ha.2⟩
              · intro i _ _
                rw [one_div_nonneg]
                exact Nat.cast_nonneg i
        _ ≤ (502 / 500 : ℝ) * log (log N) -
              (((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x1).sum
                fun q : ℕ => (1 : ℝ) / q) := by
              rw [le_sub_iff_add_le, add_comm]
              exact hrecAs
        _ ≤ (502 / 500 : ℝ) * log (log N) - c * log (log N) := by
              rw [sub_le_sub_iff_left]
              exact hf1.2.2
        _ ≤ (2 / 3 : ℝ) * log (log N) := by
              nlinarith
  · let A' := A0.filter fun n : ℕ => n ∈ A_I ∧ ∀ q ∈ ppowers_in_set A0, n ∈ local_part A_I q → q ∈ E
    have hP' : ((A \ A_I).card : ℝ) < M / log N := by
      let F : Finset ℤ := (A.image fun n : ℕ => (n : ℤ)).filter fun n : ℤ => ∀ x ∈ I, ¬ n ∣ x
      have hsubset : (A \ A_I).image (fun n : ℕ => (n : ℤ)) ⊆ F := by
        intro z hz
        rw [Finset.mem_image] at hz
        rcases hz with ⟨n, hn, rfl⟩
        rw [Finset.mem_filter, Finset.mem_image]
        refine ⟨⟨n, (Finset.mem_sdiff.mp hn).1, rfl⟩, ?_⟩
        intro x hx hnx
        apply (Finset.mem_sdiff.mp hn).2
        rw [hA_I, Finset.mem_filter]
        exact ⟨(Finset.mem_sdiff.mp hn).1, ⟨x, hx, hnx⟩⟩
      have hcardle : (((A \ A_I).image (fun n : ℕ => (n : ℤ))).card : ℝ) ≤ (F.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      have hcardeq : ((A \ A_I).image (fun n : ℕ => (n : ℤ))).card = (A \ A_I).card := by
        exact Finset.card_image_of_injective _ Nat.cast_injective
      have hF :
          F =
            ((@Finset.image ℕ ℤ (fun a b ↦ Classical.propDecidable (a = b)) Nat.cast A).filter
              fun n : ℤ => ∀ x ∈ I, ¬ n ∣ x) := by
        ext z
        simp [F, Finset.mem_image]
      have hPstd : (F.card : ℝ) < M / log N := by
        rw [hF]
        exact hP
      exact lt_of_le_of_lt (by simpa [hcardeq] using hcardle) hPstd
    have hrecaux' : 1 / log N + rec_sum ((A0 \ A') ∩ A_I) ≤ (log N) ^ (-(1 / 101 : ℝ)) / 6 := by
      calc
        1 / log N + rec_sum ((A0 \ A') ∩ A_I) ≤
            1 / log N + (((ppowers_in_set A0) \ E).sum fun q => (rec_sum_local A_I q) / q) := by
              rw [add_le_add_iff_left]
              norm_cast
              refine rec_sum_split A0 A_I A' E ?_ ?_
              · intro hzA
                apply h0A
                rw [hA_I] at hzA
                exact Finset.mem_of_mem_filter 0 hzA
              · rfl
        _ ≤
            1 / log N +
              (1 / (2 * log N ^ ((1 : ℝ) / 100))) *
                (((ppowers_in_set A0) \ E).sum fun q => (1 : ℝ) / q) := by
              norm_cast
              rw [add_le_add_iff_left, Rat.cast_sum, Finset.mul_sum]
              simp_rw [Rat.cast_div, Rat.cast_natCast]
              refine Finset.sum_le_sum ?_
              intro q hq
              have hle : (rec_sum_local A_I q : ℝ) ≤ 1 / (2 * log N ^ ((1 : ℝ) / 100)) := by
                rw [← not_lt]
                intro nlt
                rw [Finset.mem_sdiff] at hq
                apply hq.2
                rw [hE, Finset.mem_filter]
                refine ⟨(ppowers_in_set_subset Finset.sdiff_subset) hq.1, le_of_lt nlt⟩
              exact
                (by
                  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
                    (mul_le_mul_of_nonneg_right hle
                      (inv_nonneg.mpr (Nat.cast_nonneg q))))
        _ ≤ 1 / log N + (1 / (2 * log N ^ ((1 : ℝ) / 100))) * ((501 / 500 : ℝ) * log (log N)) := by
              rw [add_le_add_iff_left]
              refine mul_le_mul_of_nonneg_left ?_ ?_
              · refine le_trans ?_ hsum4
                rw [ppower_rec_sum]
                push_cast
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
                · exact Finset.sdiff_subset.trans (ppowers_in_set_subset Finset.sdiff_subset)
                · intro i _ _
                  rw [one_div_nonneg]
                  exact Nat.cast_nonneg i
              · positivity
        _ ≤ (log N) ^ (-(1 / 101 : ℝ)) / 6 := hlarge5
    have hrecA0 : (log N) ^ (-(1 / 101 : ℝ)) / 3 ≤ rec_sum A0 := by
      have hAlarge1 : ¬ ((rec_sum A : ℝ) ≤ 3 * rec_sum A1) := by
        intro h
        apply hAlarge
        exact Or.inl (by exact_mod_cast h)
      have hAlarge2 : ¬ ((rec_sum A : ℝ) ≤ 3 * rec_sum A2) := by
        intro h
        apply hAlarge
        exact Or.inr (by exact_mod_cast h)
      have hA1small : (rec_sum A1 : ℝ) < rec_sum A / 3 := by
        apply lt_of_not_ge
        intro hA1small
        apply hAlarge1
        nlinarith
      have hA2small : (rec_sum A2 : ℝ) < rec_sum A / 3 := by
        apply lt_of_not_ge
        intro hA2small
        apply hAlarge2
        nlinarith
      have hA0big : (rec_sum A : ℝ) / 3 ≤ rec_sum A0 := by
        have h3rec' : (rec_sum A : ℝ) ≤ rec_sum A1 + rec_sum A2 + rec_sum A0 := by
          exact_mod_cast h3rec
        by_contra hA0big
        have hA0small : (rec_sum A0 : ℝ) < rec_sum A / 3 := lt_of_not_ge hA0big
        nlinarith [h3rec', hA1small, hA2small, hA0small]
      nlinarith [hrecA, hA0big]
    have hrecaux : (rec_sum (A0 \ A') : ℝ) ≤ (log N) ^ (-(1 / 101 : ℝ)) / 6 := by
      calc
        (rec_sum (A0 \ A') : ℝ) = rec_sum ((A0 \ A') \ A_I) + rec_sum ((A0 \ A') ∩ A_I) := by
          norm_cast
          rw [← rec_sum_disjoint, Finset.sdiff_union_inter]
          exact Finset.disjoint_sdiff_inter _ _
        _ ≤ rec_sum (A \ A_I) + rec_sum ((A0 \ A') ∩ A_I) := by
          rw [add_le_add_iff_right]
          norm_cast
          refine rec_sum_mono ?_
          intro n hn
          rw [Finset.mem_sdiff] at hn ⊢
          have hnA0 : n ∈ A0 := (Finset.mem_sdiff.mp hn.1).1
          have hnA : n ∈ A := by
            dsimp [A0] at hnA0
            exact (Finset.mem_sdiff.mp hnA0).1
          exact ⟨hnA, hn.2⟩
        _ ≤ ((A \ A_I).card : ℝ) / M + rec_sum ((A0 \ A') ∩ A_I) := by
          rw [add_le_add_iff_right]
          exact rec_sum_le_card_div h0M fun n hn => hMA n (Finset.mem_sdiff.mp hn).1
        _ ≤ 1 / log N + rec_sum ((A0 \ A') ∩ A_I) := by
          rw [add_le_add_iff_right]
          have htmp : ((A \ A_I).card : ℝ) / M < 1 / log N := by
            rw [_root_.div_lt_iff₀ h0M]
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hP'
          exact le_of_lt htmp
        _ ≤ (log N) ^ (-(1 / 101 : ℝ)) / 6 := hrecaux'
    have hrecA' : (log N) ^ (-(1 / 101 : ℝ)) / 6 ≤ rec_sum A' := by
      calc
        (log N) ^ (-(1 / 101 : ℝ)) / 6 ≤
            (log N) ^ (-(1 / 101 : ℝ)) / 3 - (log N) ^ (-(1 / 101 : ℝ)) / 6 := by
          nlinarith
        _ ≤ (rec_sum A0 : ℝ) - (log N) ^ (-(1 / 101 : ℝ)) / 6 := by
          rw [sub_le_sub_iff_right]
          exact hrecA0
        _ ≤ (rec_sum A0 : ℝ) - rec_sum (A0 \ A') := by
          rw [sub_le_sub_iff_left]
          exact hrecaux
        _ = rec_sum A' := by
          rw [sub_eq_iff_eq_add]
          norm_cast
          rw [← rec_sum_disjoint, Finset.union_sdiff_of_subset]
          · exact Finset.filter_subset _ _
          · exact Finset.disjoint_sdiff
    have hA'size : M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) ≤ A'.card := by
      have htmp : (rec_sum A' : ℝ) ≤ A'.card / M := by
        refine rec_sum_le_card_div h0M ?_
        intro n hn
        have hnA0 : n ∈ A0 := (Finset.mem_filter.mp hn).1
        have hnA : n ∈ A := by
          dsimp [A0] at hnA0
          exact (Finset.mem_sdiff.mp hnA0).1
        exact hMA n hnA
      have htmp' : ((log N) ^ (-(1 / 101 : ℝ)) / 6) * M ≤ (A'.card : ℝ) := by
        exact (_root_.le_div_iff₀ h0M).mp (hrecA'.trans htmp)
      simpa [mul_comm, mul_left_comm, mul_assoc] using htmp'
    have hIne : I.Nonempty := ⟨f x1, hf1.1⟩
    have hbadx :
        ∃ x ∈ I,
          M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ) ≤
            (A'.filter fun n : ℕ => (n : ℤ) ∣ x).card := by
      by_contra h
      rw [← not_lt] at hA'size
      apply hA'size
      have hA'union : A' = I.biUnion fun x : ℤ => A'.filter fun n : ℕ => (n : ℤ) ∣ x := by
        ext a
        constructor
        · intro hn
          have hn' := hn
          rw [Finset.mem_filter, hA_I, Finset.mem_filter] at hn
          rcases hn.2.1.2 with ⟨x, hx1, hx2⟩
          rw [Finset.mem_biUnion]
          exact ⟨x, hx1, by
            rw [Finset.mem_filter]
            exact ⟨hn', hx2⟩⟩
        · intro hn
          rw [Finset.mem_biUnion] at hn
          rcases hn with ⟨x, hx1, hx2⟩
          exact Finset.mem_of_mem_filter a hx2
      rw [hA'union]
      refine
        lt_of_lt_of_le
          (card_bUnion_lt_card_mul_real
            (M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ)) ?_ hIne)
          ?_
      · intro x hx
        rw [← not_le]
        intro hnle
        apply h
        exact ⟨x, hx, hnle⟩
      · rw [show ((I.card : ℝ) * (M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ))) =
            M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) by
            field_simp [show (I.card : ℝ) ≠ 0 by
              exact_mod_cast (Finset.card_ne_zero.mpr hIne)]]
    rcases hbadx with ⟨x, hx1, hx2⟩
    let m := Nat.gcd (Int.natAbs x) (Int.natAbs (f x1 * f x2))
    have hmsmall : m ≤ N ^ 2 := by
      have hbadx' : ∃ n ∈ A', (n : ℤ) ∣ x := by
        have hA'temp : (A'.filter fun n : ℕ => (n : ℤ) ∣ x).Nonempty := by
          rw [← Finset.card_pos, Nat.pos_iff_ne_zero]
          intro hz
          rw [hz] at hx2
          have hpos : 0 < M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ) := by
            refine div_pos ?_ ?_
            · refine mul_pos h0M ?_
              refine div_pos ?_ ?_
              · exact Real.rpow_pos_of_pos hlarge0 _
              · norm_num1
            · exact_mod_cast (Finset.card_pos.mpr hIne)
          linarith
        rcases hA'temp with ⟨n, hn⟩
        rw [Finset.mem_filter] at hn
        exact ⟨n, hn.1, hn.2⟩
      rcases hbadx' with ⟨ns, hns1, hns2⟩
      rw [Finset.mem_filter] at hns1
      have hns3 := hns1.1
      rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hns3
      rw [not_or] at hns3
      refine le_trans (nat_gcd_prod_le_diff ?_ ?_) ?_
      · intro hnetemp
        rw [hnetemp] at hns2
        exact hns3.2.1 ⟨hns3.1, hns2⟩
      · intro hnetemp
        rw [hnetemp] at hns2
        exact hns3.2.2 ⟨hns3.1, hns2⟩
      · rw [sq]
        refine Nat.mul_le_mul ?_ ?_
        · exact hIclose x hx1 (f x1) hf1.1
        · exact hIclose x hx1 (f x2) hf2.1
    have hdivm : (A'.filter fun n : ℕ => (n : ℤ) ∣ x).card ≤ ArithmeticFunction.sigma 0 m := by
      rw [divisor_function_eq_card_divisors]
      refine Finset.card_le_card ?_
      intro n hn
      rw [Nat.mem_divisors]
      refine ⟨?_, ?_⟩
      · rw [dvd_iff_ppowers_dvd' n m]
        · intro q hq1 hq2
          rw [Nat.dvd_gcd_iff]
          rcases Finset.mem_filter.mp hn with ⟨hnA', hnx⟩
          rcases Finset.mem_filter.mp hnA' with ⟨hnA0, hnAI, hprop⟩
          refine ⟨?_, ?_⟩
          · have hqx : (q : ℤ) ∣ x := dvd_trans (Int.natCast_dvd_natCast.mpr hq1) hnx
            exact Int.natCast_dvd.mp <| by
              simpa using Int.dvd_natAbs.mpr hqx
          · have hqE : q ∈ E := by
              have hnA : n ∈ A := by
                dsimp [A0] at hnA0
                exact (Finset.mem_sdiff.mp hnA0).1
              have hn0 : n ≠ 0 := by
                intro hnz
                apply h0A
                simpa [hnz] using hnA
              exact hprop q (by
                rw [ppowers_in_set, Finset.mem_biUnion]
                refine ⟨n, hnA0, ?_⟩
                rw [Finset.mem_filter, Nat.mem_divisors]
                exact ⟨⟨hq1, hn0⟩, hq2.1, hq2.2⟩) (by
                rw [local_part, Finset.mem_filter]
                exact ⟨hnAI, hq1, hq2.2⟩)
            have hfq := hf q hqE
            rcases hthreexs q hqE with hqfx1 | hqfx2
            · have hqx1 : (q : ℤ) ∣ f x1 := by simpa [hqfx1] using hfq.2.1
              have hqabs : q ∣ Int.natAbs (f x1) := by
                exact Int.natCast_dvd.mp <| by simpa using Int.dvd_natAbs.mpr hqx1
              simpa [Int.natAbs_mul] using dvd_mul_of_dvd_left hqabs (Int.natAbs (f x2))
            · have hqx2 : (q : ℤ) ∣ f x2 := by simpa [hqfx2] using hfq.2.1
              have hqabs : q ∣ Int.natAbs (f x2) := by
                exact Int.natCast_dvd.mp <| by simpa using Int.dvd_natAbs.mpr hqx2
              simpa [Int.natAbs_mul, Nat.mul_comm] using
                dvd_mul_of_dvd_right hqabs (Int.natAbs (f x1))
        · intro hnz
          apply h0A
          have hbah : A'.filter fun n : ℕ => (n : ℤ) ∣ x ⊆ A := by
            intro k hk
            have hkA' : k ∈ A' := (Finset.mem_filter.mp hk).1
            have hkA0 : k ∈ A0 := (Finset.mem_filter.mp hkA').1
            dsimp [A0] at hkA0
            exact (Finset.mem_sdiff.mp hkA0).1
          rw [hnz] at hn
          exact hbah hn
      · intro hmz
        rw [Nat.gcd_eq_zero_iff] at hmz
        have hmz' : x = 0 := by simpa using hmz.1
        rw [hmz'] at hx1
        exact hzI hx1
    specialize hdiv m hmsmall
    have hsigma_lt :
        (ArithmeticFunction.sigma 0 m : ℝ) <
          M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ) :=
      lt_of_le_of_lt hdiv hlarge9
    have hsigma_ge :
        M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ) ≤
          ArithmeticFunction.sigma 0 m := by
      exact le_trans hx2 (by exact_mod_cast hdivm)
    exact (not_lt_of_ge hsigma_ge) hsigma_lt

private lemma force_good_properties_three_values_case
    (N : ℕ) (c : ℝ) (A : Finset ℕ) (x1 x2 x3 : ℕ) (f : ℕ → ℤ)
    (hA : A ⊆ Finset.range (N + 1))
    (hlarge3 : 0 < log (log N))
    (hnum : (102 / 100 : ℝ) ≤ 3 * c - ((1 : ℝ) / 500 + (1 : ℝ) / 500 + (1 : ℝ) / 500))
    (hrecN :
      ∀ x y : ℤ,
        x ≠ y →
          |(x : ℝ) - y| ≤ N →
            ((Finset.range (N + 1)).filter
                (fun n : ℕ ↦ IsPrimePow n ∧ (n : ℤ) ∣ x ∧ (n : ℤ) ∣ y)).sum
              (fun q : ℕ ↦ (1 : ℝ) / q) <
              ((1 : ℝ) / 500) * log (log N))
    (hsum4 : (ppower_rec_sum A : ℝ) ≤ (501 / 500 : ℝ) * log (log N))
    (hS1 :
      c * log (log N) ≤
        ((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x1).sum
          (fun r : ℕ => (1 / r : ℝ)))
    (hS2 :
      c * log (log N) ≤
        ((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x2).sum
          (fun r : ℕ => (1 / r : ℝ)))
    (hS3 :
      c * log (log N) ≤
        ((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x3).sum
          (fun r : ℕ => (1 / r : ℝ)))
    (h21 : f x2 ≠ f x1)
    (h32 : f x3 ≠ f x2)
    (h31 : f x3 ≠ f x1)
    (hclose21 : |(f x2 : ℝ) - f x1| ≤ N)
    (hclose32 : |(f x3 : ℝ) - f x2| ≤ N)
    (hclose31 : |(f x3 : ℝ) - f x1| ≤ N) :
    False := by
  let F1 := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x1
  let F2 := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x2
  let F3 := (ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ f x3
  let S1 := F1.sum fun r : ℕ => (1 : ℝ) / r
  let S2 := F2.sum fun r : ℕ => (1 : ℝ) / r
  let S3 := F3.sum fun r : ℕ => (1 : ℝ) / r
  let S12 := (F1 ∩ F2).sum fun r : ℕ => (1 : ℝ) / r
  let S23 := (F2 ∩ F3).sum fun r : ℕ => (1 : ℝ) / r
  let S13 := (F1 ∩ F3).sum fun r : ℕ => (1 : ℝ) / r
  let S123 := (F1 ∩ F2 ∩ F3).sum fun r : ℕ => (1 : ℝ) / r
  have hsum1 : 3 * c * log (log N) ≤ S1 + S2 + S3 := by
    have hS1' : c * log (log N) ≤ S1 := by simpa [S1, F1] using hS1
    have hS2' : c * log (log N) ≤ S2 := by simpa [S2, F2] using hS2
    have hS3' : c * log (log N) ≤ S3 := by simpa [S3, F3] using hS3
    nlinarith
  have hunion :
      S1 + S2 + S3 =
        (F1 ∪ F2 ∪ F3).sum (fun r : ℕ => (1 : ℝ) / r) + S12 + S13 + S23 - S123 := by
    dsimp [S1, S2, S3, S12, S13, S23, S123]
    simpa [F1, F2, F3, Finset.union_assoc, Finset.inter_assoc, Finset.inter_left_comm,
      Finset.filter_inter, Finset.inter_filter, Finset.inter_self, Finset.filter_filter,
      and_assoc, and_left_comm, and_right_comm, add_comm, add_left_comm, add_assoc] using
      (sum_add_sum_add_sum (A := F1) (B := F2) (C := F3) (f := fun r : ℕ => (1 : ℝ) / r))
  have hsum2 : (S1 + S2 + S3) - (S12 + S13 + S23) ≤ ppower_rec_sum A := by
    have h123nonneg : 0 ≤ S123 := by
      dsimp [S123]
      refine Finset.sum_nonneg ?_
      intro i hi
      rw [one_div_nonneg]
      exact Nat.cast_nonneg i
    have hunion_le :
        (F1 ∪ F2 ∪ F3).sum (fun r : ℕ => (1 : ℝ) / r) ≤ ppower_rec_sum A := by
      rw [ppower_rec_sum]
      push_cast
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro q hq
        rw [Finset.mem_union, Finset.mem_union] at hq
        rcases hq with hq | hq
        · rcases hq with hq | hq
          · exact Finset.mem_of_mem_filter q hq
          · exact Finset.mem_of_mem_filter q hq
        · exact Finset.mem_of_mem_filter q hq
      · intro i hi1 hi2
        rw [one_div_nonneg]
        exact Nat.cast_nonneg i
    calc
      (S1 + S2 + S3) - (S12 + S13 + S23) =
          ((F1 ∪ F2 ∪ F3).sum (fun r : ℕ => (1 : ℝ) / r) + S12 + S13 + S23 - S123) -
            (S12 + S13 + S23) := by rw [hunion]
      _ ≤ (F1 ∪ F2 ∪ F3).sum (fun r : ℕ => (1 : ℝ) / r) := by
          nlinarith
      _ ≤ ppower_rec_sum A := hunion_le
  have hsum3 :
      S12 + S23 + S13 ≤
        (((1 : ℝ) / 500) + ((1 : ℝ) / 500) + ((1 : ℝ) / 500)) * log (log N) := by
    have h12 :
        S12 ≤ ((1 : ℝ) / 500) * log (log N) := by
      dsimp [S12, F1, F2]
      refine le_trans ?_ (le_of_lt (hrecN (f x2) (f x1) h21 hclose21))
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro r hr
        rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hr
        rw [Finset.mem_filter]
        rw [ppowers_in_set, Finset.mem_biUnion] at hr
        rcases hr.1.1 with ⟨m, hmA, hmq⟩
        rw [Finset.mem_filter, Nat.mem_divisors] at hmq
        exact ⟨by
            rw [Finset.mem_range]
            exact lt_of_le_of_lt
              (Nat.le_of_dvd (Nat.pos_of_ne_zero hmq.1.2) hmq.1.1)
              (by
                rw [← Finset.mem_range]
                exact hA hmA),
          hmq.2.1, hr.2.2, hr.1.2⟩
      · intro i hi1 hi2
        rw [one_div_nonneg]
        exact Nat.cast_nonneg i
    have h23 :
        S23 ≤ ((1 : ℝ) / 500) * log (log N) := by
      dsimp [S23, F2, F3]
      refine le_trans ?_ (le_of_lt (hrecN (f x3) (f x2) h32 hclose32))
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro r hr
        rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hr
        rw [Finset.mem_filter]
        rw [ppowers_in_set, Finset.mem_biUnion] at hr
        rcases hr.1.1 with ⟨m, hmA, hmq⟩
        rw [Finset.mem_filter, Nat.mem_divisors] at hmq
        exact ⟨by
            rw [Finset.mem_range]
            exact lt_of_le_of_lt
              (Nat.le_of_dvd (Nat.pos_of_ne_zero hmq.1.2) hmq.1.1)
              (by
                rw [← Finset.mem_range]
                exact hA hmA),
          hmq.2.1, hr.2.2, hr.1.2⟩
      · intro i hi1 hi2
        rw [one_div_nonneg]
        exact Nat.cast_nonneg i
    have h13 :
        S13 ≤ ((1 : ℝ) / 500) * log (log N) := by
      dsimp [S13, F1, F3]
      refine le_trans ?_ (le_of_lt (hrecN (f x3) (f x1) h31 hclose31))
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro r hr
        rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hr
        rw [Finset.mem_filter]
        rw [ppowers_in_set, Finset.mem_biUnion] at hr
        rcases hr.1.1 with ⟨m, hmA, hmq⟩
        rw [Finset.mem_filter, Nat.mem_divisors] at hmq
        exact ⟨by
            rw [Finset.mem_range]
            exact lt_of_le_of_lt
              (Nat.le_of_dvd (Nat.pos_of_ne_zero hmq.1.2) hmq.1.1)
              (by
                rw [← Finset.mem_range]
                exact hA hmA),
          hmq.2.1, hr.2.2, hr.1.2⟩
      · intro i hi1 hi2
        rw [one_div_nonneg]
        exact Nat.cast_nonneg i
    nlinarith
  have hsum5 : ¬ ((501 / 500 : ℝ) * log (log N) < ((102 : ℝ) / 100) * log (log N)) := by
    rw [not_lt]
    calc
      (((102 : ℝ) / 100) * log (log N)) ≤
          (3 * c - (((1 : ℝ) / 500) + ((1 : ℝ) / 500) + ((1 : ℝ) / 500))) *
            log (log N) := by
              exact mul_le_mul_of_nonneg_right hnum (le_of_lt hlarge3)
      _ = 3 * c * log (log N) -
            ((((1 : ℝ) / 500) + ((1 : ℝ) / 500) + ((1 : ℝ) / 500)) * log (log N)) := by
              ring
      _ ≤ (S1 + S2 + S3) - (S12 + S13 + S23) := by
              nlinarith [hsum1, hsum3]
      _ ≤ ppower_rec_sum A := hsum2
      _ ≤ (501 / 500 : ℝ) * log (log N) := hsum4
  apply hsum5
  exact mul_lt_mul_of_pos_right (by norm_num) hlarge3

theorem force_good_properties :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℝ, ∀ A ⊆ Finset.range (N + 1),
      0 < M → M ≤ N → (N : ℝ) ≤ M ^ 2 → 0 ∉ A →
      (∀ n ∈ A, M ≤ (n : ℝ)) → arith_regular N A →
      (log N) ^ (-(1 / 101 : ℝ)) ≤ rec_sum A →
      (∀ q ∈ ppowers_in_set A, (log N) ^ (-(1 / 100 : ℝ)) ≤ rec_sum_local A q) →
      ((∃ B ⊆ A, rec_sum A ≤ 3 * rec_sum B ∧ (ppower_rec_sum B : ℝ) ≤ (2 / 3) * log (log N)) ∨
        good_condition A (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) ((M : ℝ) / log N)
          (M / (2 * (log N) ^ (1 / 100 : ℝ)))) := by
  classical
  let c := (35 : ℝ) / 100
  have hthirdpos : (0 : ℝ) < 1 / 3 := by
    norm_num1
  filter_upwards
    [ eventually_gt_atTop (1 : ℕ)
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp
        tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop ((2 : ℝ) / (1 / 2)))
    , yet_another_large_N
    , yet_another_large_N'
    , rec_pp_sum_close
    , find_good_x
    , explicit_mertens2
    , div_bound_useful_version hthirdpos ] with
    N hlarge hlarge0 hlarge4 hlargeNs hlarge5 hrecN hgoodx hmertens hdiv
    M A hA h0M hMN hNM h0A hMA hreg hrecA hreclocal
  dsimp at hlarge0
  have hlarge3 : 0 < log (log N) := by
    refine lt_of_lt_of_le ?_ hlarge4
    norm_num1
  have hlarge1 : 1 ≤ M * N ^ ((-2 : ℝ) / log (log N)) := by
    have hNpos : 0 < (N : ℝ) := by
      exact_mod_cast (lt_trans zero_lt_one hlarge)
    have hexp : (2 : ℝ) / log (log N) ≤ (1 : ℝ) / 2 := by
      have hlarge4' := hlarge4
      norm_num at hlarge4'
      refine (div_le_iff₀ hlarge3).2 ?_
      nlinarith
    have hpow : (N : ℝ) ^ ((2 : ℝ) / log (log N)) ≤ M := by
      calc
        (N : ℝ) ^ ((2 : ℝ) / log (log N)) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast le_of_lt hlarge) hexp
        _ ≤ M := by
          rw [← Real.sqrt_eq_rpow]
          exact Real.sqrt_le_iff.mpr ⟨le_of_lt h0M, hNM⟩
    have hneg : (-2 : ℝ) / log (log N) = -((2 : ℝ) / log (log N)) := by
      ring
    rw [hneg, Real.rpow_neg, div_eq_mul_inv]
    · exact (one_le_div (Real.rpow_pos_of_pos hNpos _)).2 hpow
    · exact Nat.cast_nonneg N
  have hlarge2 : M * N ^ ((-2 : ℝ) / log (log N)) ≤ N := by
    have hrpow : N ^ ((-2 : ℝ) / log (log N)) ≤ (1 : ℝ) := by
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast le_of_lt hlarge
      · apply div_nonpos_of_nonpos_of_nonneg
        · rw [neg_nonpos]
          exact zero_le_two
        · exact le_of_lt hlarge3
    calc
      _ ≤ M := by
        simpa [mul_one] using mul_le_mul_of_nonneg_left hrpow h0M.le
      _ ≤ N := hMN
  refine or_iff_not_imp_left.2 ?_
  intro hnoB
  rw [good_condition]
  intro t I hI
  refine or_iff_not_imp_left.2 ?_
  intro hP
  by_cases hzI : (0 : ℤ) ∈ I
  · refine ⟨0, hzI, ?_⟩
    intro q hq
    exact dvd_zero (q : ℤ)
  have hIcard0 :
      (I.card : ℤ) =
        ⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ + 1 -
          ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉ := by
    exact force_good_properties_hIcard0 N M t I hI h0M
  have hIcardn0 : I.card ≠ 0 := by
    exact force_good_properties_hIcardn0 N M t I hI hlarge1
  have hIcard' : (I.card : ℝ) ≤ M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) + 1 := by
    exact force_good_properties_hIcard' N M t I hIcard0
  have hIcard'' : (I.card : ℝ) ≤ 2 * M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) := by
    exact force_good_properties_hIcard'' N M I hIcard' hlarge1
  have hlarge9 :
      (N : ℝ) ^ (2 * log 2 / log (log N) * (1 + 1 / 3)) <
        M * ((log N) ^ (-(1 / 101 : ℝ)) / 6) / (I.card : ℝ) := by
    exact force_good_properties_hlarge9 N M I hlarge h0M hlargeNs hIcard'' hIcardn0
  have hIclose' : ∀ x ∈ I, ∀ y ∈ I, (|x - y| : ℝ) ≤ N := by
    exact force_good_properties_hIclose' N M t I hI hlarge2
  have hIclose : ∀ x ∈ I, ∀ y ∈ I, Int.natAbs (x - y) ≤ N := by
    exact force_good_properties_hIclose N I hIclose'
  let A_I := A.filter fun n : ℕ => ∃ x ∈ I, (n : ℤ) ∣ x
  let D := interval_rare_ppowers I A (M / (2 * log N ^ ((1 : ℝ) / 100)))
  let E := (ppowers_in_set A).filter
    fun q : ℕ => 1 / (2 * log N ^ ((1 : ℝ) / 100)) ≤ rec_sum_local A_I q
  let K := M / (2 * log N ^ ((1 : ℝ) / 100))
  by_cases hDne : D.Nonempty
  · rcases hDne with ⟨x1, hx1⟩
    have hDE : D ⊆ E := by
      intro q hq
      rw [Finset.mem_filter]
      refine ⟨interval_rare_ppowers_subset I K hq, ?_⟩
      refine good_d N M (1 / (2 * log N ^ ((1 : ℝ) / 100))) A hA h0M hMA ?_ I q ?_
      · intro q hq'
        rw [two_mul, one_div, ← inv_div_left, add_halves, ← Real.rpow_neg]
        · exact hreclocal q hq'
        · exact le_of_lt hlarge0
      · rw [← div_eq_mul_one_div]
        exact hq
    have hlocal :
        ∀ q ∈ E, ∃ x ∈ I, ((q : ℤ) ∣ x) ∧
          c * log (log N) ≤
            ((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ x).sum
              (fun r : ℕ => (1 / r : ℝ)) := by
      intro q hq
      specialize hgoodx M A hA h0M hMN h0A hMA hreg t I q
        (Finset.mem_of_mem_filter q hq) hI
      apply hgoodx
      rw [Finset.mem_filter] at hq
      exact hq.2
    clear hgoodx
    choose! f hf using hlocal
    use f x1
    have hfcopy := hf
    have hfcopy2 := hf
    have hfcopy3 := hf
    specialize hf x1 (hDE hx1)
    refine ⟨hf.1, ?_⟩
    intro x2 hx2
    specialize hfcopy2 x2 (hDE hx2)
    have hclose : ∀ x ∈ E, ∀ y ∈ E, |(f x : ℝ) - f y| ≤ N := by
      intro q hq r hr
      have hfcopy' := hfcopy
      specialize hfcopy q hq
      specialize hfcopy' r hr
      apply @le_trans _ _ _
        (((⌊t + M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) / 2⌋ : ℤ) : ℝ) -
          ⌈t - M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) / 2⌉) N
      · apply two_in_Icc
        · rw [← hI]
          exact hfcopy.1
        · rw [← hI]
          exact hfcopy'.1
      · have hfloor :
            ((⌊t + M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) / 2⌋ : ℤ) : ℝ) ≤
              t + M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) / 2 := by
          exact Int.floor_le _
        have hceil :
            t - M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) / 2 ≤
              (⌈t - M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) / 2⌉ : ℤ) := by
          exact Int.le_ceil _
        nlinarith
    have hsum4 : (ppower_rec_sum A : ℝ) ≤ (501 / 500 : ℝ) * log (log N) := by
      refine le_trans ?_ hmertens
      rw [ppower_rec_sum]
      push_cast
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro r hr
        rw [ppowers_in_set, Finset.mem_biUnion] at hr
        rw [Finset.mem_filter, Finset.mem_range]
        rcases hr with ⟨a, ha, hr⟩
        rw [Finset.mem_filter] at hr
        refine ⟨?_, hr.2.1⟩
        exact lt_of_le_of_lt (Nat.divisor_le hr.1) (by
          rw [← Finset.mem_range]
          exact hA ha)
      · intro i _ _
        rw [one_div_nonneg]
        exact Nat.cast_nonneg i
    by_cases htwoxs : f x2 = f x1
    · obtain hf' := hfcopy2.2.1
      rw [htwoxs] at hf'
      exact hf'
    · by_cases hthreexs : ∀ x ∈ E, f x = f x1 ∨ f x = f x2
      · exact
          force_good_properties_two_values_case
            N M c A A_I E I x1 x2 f hA h0A h0M hMA hrecA hlarge0 hlarge5 hlarge3
            (by norm_num1) hzI (by simpa using hP) hnoB hrecN hsum4 hlarge9 hdiv hIclose rfl rfl
            hfcopy (hDE hx1) (hDE hx2) (hclose x2 (hDE hx2) x1 (hDE hx1)) htwoxs hthreexs
      · rw [not_forall] at hthreexs
        rcases hthreexs with ⟨x3, hx3⟩
        rw [Classical.not_imp, not_or] at hx3
        specialize hfcopy3 x3 hx3.1
        exfalso
        let S1 :=
          ((ppowers_in_set A).filter fun n => (n : ℤ) ∣ f x1).sum (fun r => (1 : ℝ) / r)
        let S2 :=
          ((ppowers_in_set A).filter fun n => (n : ℤ) ∣ f x2).sum (fun r => (1 : ℝ) / r)
        let S3 :=
          ((ppowers_in_set A).filter fun n => (n : ℤ) ∣ f x3).sum (fun r => (1 : ℝ) / r)
        exact
          force_good_properties_three_values_case
            N c A x1 x2 x3 f hA hlarge3
            (by
              dsimp [c]
              norm_num1)
            hrecN hsum4 hf.2.2
            hfcopy2.2.2 hfcopy3.2.2 htwoxs hx3.2.2 hx3.2.1
            (hclose x2 (hDE hx2) x1 (hDE hx1)) (hclose x3 hx3.1 x2 (hDE hx2))
            (hclose x3 hx3.1 x1 (hDE hx1))
  · have hIne : I.Nonempty := by
      rw [hI, Finset.nonempty_Icc]
      rw [Int.ceil_le]
      have hfloor : t + M * N ^ ((-2 : ℝ) / log (log N)) / 2 - 1 <
          (⌊t + M * N ^ ((-2 : ℝ) / log (log N)) / 2⌋ : ℤ) := by
        exact Int.sub_one_lt_floor _
      have hgap :
          t - M * N ^ ((-2 : ℝ) / log (log N)) / 2 ≤
            t + M * N ^ ((-2 : ℝ) / log (log N)) / 2 - 1 := by
        nlinarith
      exact le_trans hgap (le_of_lt hfloor)
    rcases hIne with ⟨x, hx⟩
    refine ⟨x, hx, ?_⟩
    intro q hq
    exfalso
    apply hDne
    exact ⟨q, hq⟩

theorem force_good_properties2 :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℝ, ∀ A ⊆ Finset.range (N + 1),
      0 < M → M ≤ N → (N : ℝ) ≤ M ^ 2 → 0 ∉ A →
      (∀ n ∈ A, M ≤ (n : ℝ)) → arith_regular N A →
      (∀ q ∈ ppowers_in_set A, (log N) ^ (-(1 / 100 : ℝ)) ≤ rec_sum_local A q) →
      (ppower_rec_sum A : ℝ) ≤ (2 / 3) * log (log N) →
      good_condition A (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) ((M : ℝ) / log N)
        (M / (2 * (log N) ^ (1 / 100 : ℝ))) := by
  classical
  let c := (35 : ℝ) / 100
  filter_upwards
    [ eventually_gt_atTop (1 : ℕ)
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp
        tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop ((2 : ℝ) / (1 / 2)))
    , rec_pp_sum_close
    , find_good_x ] with
    N hlarge hlarge0 hlarge4 hrecN hgoodx M A hA h0M hMN hNM h0A hMA hreg hreclocal hpprecA
  dsimp at hlarge0
  have hlarge3 : 0 < log (log N) := by
    refine lt_of_lt_of_le ?_ hlarge4
    norm_num1
  have hlarge1 : 1 ≤ M * N ^ ((-2 : ℝ) / log (log N)) := by
    have hNpos : 0 < (N : ℝ) := by
      exact_mod_cast (lt_trans zero_lt_one hlarge)
    have hexp : (2 : ℝ) / log (log N) ≤ (1 : ℝ) / 2 := by
      have hlarge4' := hlarge4
      norm_num at hlarge4'
      refine (div_le_iff₀ hlarge3).2 ?_
      nlinarith
    have hpow :
        (N : ℝ) ^ ((2 : ℝ) / log (log N)) ≤ M := by
      calc
        (N : ℝ) ^ ((2 : ℝ) / log (log N)) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast le_of_lt hlarge) hexp
        _ ≤ M := by
          rw [← Real.sqrt_eq_rpow]
          exact Real.sqrt_le_iff.mpr ⟨le_of_lt h0M, hNM⟩
    have hneg : (-2 : ℝ) / log (log N) = -((2 : ℝ) / log (log N)) := by
      ring
    rw [hneg, Real.rpow_neg, div_eq_mul_inv]
    · exact (one_le_div (Real.rpow_pos_of_pos hNpos _)).2 hpow
    · exact Nat.cast_nonneg N
  have hlarge2 : M * N ^ ((-2 : ℝ) / log (log N)) ≤ N := by
    have hrpow : N ^ ((-2 : ℝ) / log (log N)) ≤ (1 : ℝ) := by
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast le_of_lt hlarge
      · apply div_nonpos_of_nonpos_of_nonneg
        · rw [neg_nonpos]
          exact zero_le_two
        · exact le_of_lt hlarge3
    calc
      _ ≤ M := by
        simpa [mul_one] using mul_le_mul_of_nonneg_left hrpow h0M.le
      _ ≤ N := hMN
  rw [good_condition]
  intro t I hI
  refine or_iff_not_imp_left.2 ?_
  intro hP
  let D := interval_rare_ppowers I A (M / (2 * log N ^ ((1 : ℝ) / 100)))
  let K := M / (2 * log N ^ ((1 : ℝ) / 100))
  by_cases hDne : D.Nonempty
  · rcases hDne with ⟨x1, hx1⟩
    have hlocal :
        ∀ q ∈ D, ∃ x ∈ I, ((q : ℤ) ∣ x) ∧
            ((35 : ℝ) / 100) * log (log N) ≤
            (((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ x).sum
              fun r : ℕ => (1 / r : ℝ)) := by
      intro q hq
      specialize hgoodx M A hA h0M hMN h0A hMA hreg t I q
        (interval_rare_ppowers_subset I K hq) hI
      have hgoodq :
          (1 : ℝ) / (2 * log N ^ ((1 : ℝ) / 100)) ≤
            rec_sum_local (A.filter fun n => ∃ x ∈ I, (n : ℤ) ∣ x) q := by
        refine good_d N M (1 / (2 * log N ^ ((1 : ℝ) / 100))) A hA h0M hMA ?_ I q ?_
        · intro q hq'
          rw [two_mul, one_div, ← inv_div_left, add_halves, ← Real.rpow_neg]
          · exact hreclocal q hq'
          · exact le_of_lt hlarge0
        · rw [← div_eq_mul_one_div]
          exact hq
      exact hgoodx hgoodq
    clear hgoodx
    choose! f hf using hlocal
    use f x1
    have hfcopy := hf
    specialize hf x1 hx1
    refine ⟨hf.1, ?_⟩
    intro q hq
    specialize hfcopy q hq
    by_cases htwoxs : f q = f x1
    · obtain hf' := hfcopy.2.1
      rw [htwoxs] at hf'
      exact hf'
    · exfalso
      let S1 : Finset ℕ := (ppowers_in_set A).filter fun n => (n : ℤ) ∣ f x1
      let S2 : Finset ℕ := (ppowers_in_set A).filter fun n => (n : ℤ) ∣ f q
      let S12 : Finset ℕ := (ppowers_in_set A).filter fun n => (n : ℤ) ∣ f q ∧ (n : ℤ) ∣ f x1
      have hfS1 : c * log (log N) ≤ S1.sum (fun r => (1 / r : ℝ)) := by
        simpa [S1, c] using hf.2.2
      have hfcopyS2 : c * log (log N) ≤ S2.sum (fun r => (1 / r : ℝ)) := by
        simpa [S2, c] using hfcopy.2.2
      have hsum1 :
          2 * c * log (log N) ≤
            S1.sum (fun r => (1 / r : ℝ)) + S2.sum (fun r => (1 / r : ℝ)) := by
        rw [two_mul, add_mul]
        exact add_le_add hfS1 hfcopyS2
      have hsum2 :
          S1.sum (fun r => (1 : ℝ) / r) + S2.sum (fun r => (1 : ℝ) / r) -
              S12.sum (fun r => (1 : ℝ) / r) ≤
            ppower_rec_sum A := by
        have hS12 : S1 ∩ S2 = S12 := by
          ext r
          simp [S1, S2, S12, and_left_comm, and_assoc, and_comm]
        have hEq :
            S1.sum (fun r => (1 : ℝ) / r) + S2.sum (fun r => (1 : ℝ) / r) -
                S12.sum (fun r => (1 : ℝ) / r) =
              (S1 ∪ S2).sum (fun r => (1 : ℝ) / r) := by
          rw [← hS12]
          linarith [Finset.sum_union_inter (s₁ := S1) (s₂ := S2) (f := fun r => (1 : ℝ) / r)]
        rw [ppower_rec_sum]
        push_cast
        rw [hEq]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro r hr
          rw [Finset.mem_union] at hr
          cases hr with
          | inl hr1 =>
              exact (Finset.mem_filter.mp hr1).1
          | inr hr2 =>
              exact (Finset.mem_filter.mp hr2).1
        · intro i _ _
          rw [one_div_nonneg]
          exact Nat.cast_nonneg i
      have hsum3 :
          S1.sum (fun r => (1 : ℝ) / r) + S2.sum (fun r => (1 : ℝ) / r) - ppower_rec_sum A ≤
            S12.sum (fun r => (1 : ℝ) / r) := by
        linarith
      have hsum4 :
          ((1 : ℝ) / 500) * log (log N) ≤
            S12.sum (fun r => (1 : ℝ) / r) := by
        have hsilly : c = 35 / 100 := by
          rfl
        nlinarith
      have hqx1close : |(f q : ℝ) - f x1| ≤ N := by
        apply @le_trans _ _ _
          (((⌊t + M * N ^ ((-2 : ℝ) / log (log N)) / 2⌋ : ℤ) : ℝ) -
            ⌈t - M * N ^ ((-2 : ℝ) / log (log N)) / 2⌉) N
        · apply two_in_Icc
          · rw [← hI]
            exact hfcopy.1
          · rw [← hI]
            exact hf.1
        · have hfloor :
              ((⌊t + M * N ^ ((-2 : ℝ) / log (log N)) / 2⌋ : ℤ) : ℝ) ≤
                t + M * N ^ ((-2 : ℝ) / log (log N)) / 2 := by
            exact Int.floor_le _
          have hceil :
              t - M * N ^ ((-2 : ℝ) / log (log N)) / 2 ≤
                (⌈t - M * N ^ ((-2 : ℝ) / log (log N)) / 2⌉ : ℤ) := by
            exact Int.le_ceil _
          nlinarith
      specialize hrecN (f q) (f x1) htwoxs hqx1close
      rw [lt_iff_not_ge] at hrecN
      apply hrecN
      refine le_trans hsum4 ?_
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro r hr
        simp only [S12, Finset.mem_filter] at hr
        rw [ppowers_in_set, Finset.mem_biUnion] at hr
        rcases hr.1 with ⟨m, hm1, hm2⟩
        rw [Finset.mem_filter] at hm2
        rw [Finset.mem_filter]
        refine ⟨?_, hm2.2.1, hr.2⟩
        rw [Finset.mem_range]
        exact lt_of_le_of_lt (Nat.divisor_le hm2.1) (by
          rw [← Finset.mem_range]
          exact hA hm1)
      · intro i _ _
        exact div_nonneg zero_le_one (Nat.cast_nonneg i)
  · have hIne : I.Nonempty := by
      rw [hI, Finset.nonempty_Icc]
      rw [Int.ceil_le]
      have hfloor : t + M * N ^ ((-2 : ℝ) / log (log N)) / 2 - 1 <
          (⌊t + M * N ^ ((-2 : ℝ) / log (log N)) / 2⌋ : ℤ) := by
        exact Int.sub_one_lt_floor _
      have hgap :
          t - M * N ^ ((-2 : ℝ) / log (log N)) / 2 ≤
            t + M * N ^ ((-2 : ℝ) / log (log N)) / 2 - 1 := by
        nlinarith
      exact le_trans hgap (le_of_lt hfloor)
    rcases hIne with ⟨x, hx⟩
    refine ⟨x, hx, ?_⟩
    intro q hq
    exfalso
    apply hDne
    exact ⟨q, hq⟩

lemma pruning_lemma_one_prec (A : Finset ℕ) (ε : ℝ) (i : ℕ) :
    ∃ A_i ⊆ A, ∃ Q_i ⊆ ppowers_in_set A,
      Disjoint Q_i (ppowers_in_set A_i) ∧
      ((rec_sum A : ℝ) - ε * rec_sum Q_i ≤ rec_sum A_i) ∧
      (i ≤ (A \ A_i).card ∨ ∀ q ∈ ppowers_in_set A_i, ε < rec_sum_local A_i q) := by
  induction i with
  | zero =>
      exact ⟨A, Finset.Subset.rfl, ∅, by simp⟩
  | succ i ih =>
      obtain ⟨A', hA', Q', hQ', hQA', hr, hi⟩ := ih
      by_cases hq : ∀ q ∈ ppowers_in_set A', ε < rec_sum_local A' q
      · exact ⟨A', hA', Q', hQ', hQA', hr, Or.inr hq⟩
      · have hq_neg := hq
        push Not at hq
        obtain ⟨q', hq', h4⟩ := hq
        have hq'zero : q' ≠ 0 := ne_of_mem_of_not_mem hq' zero_not_mem_ppowers_in_set
        have hq'zero' : (q' : ℚ) ≠ 0 := by
          exact_mod_cast hq'zero
        let A'' := A'.filter fun n ↦ ¬ (q' ∣ n ∧ Nat.Coprime q' (n / q'))
        let Q'' := insert q' Q'
        have hq'' : q' ∉ Q' := by
          rw [Finset.disjoint_left] at hQA'
          exact fun hmem ↦ hQA' hmem hq'
        refine ⟨A'', (Finset.filter_subset _ _).trans hA', Q'', ?_, ?_, ?_, ?_⟩
        · exact Finset.insert_subset (ppowers_in_set_subset hA' hq') hQ'
        · refine Finset.disjoint_insert_left.2 ⟨?_, ?_⟩
          · intro hmem
            rcases (mem_ppowers_in_set.mp hmem).2 with ⟨x, hx⟩
            rcases (mem_local_part (A := A'') (q := q') x).mp hx with ⟨hxA'', hxdvd, hxcop⟩
            exact (Finset.mem_filter.mp hxA'').2 ⟨hxdvd, hxcop⟩
          · exact hQA'.mono_right (ppowers_in_set_subset (Finset.filter_subset _ _))
        · have hrs : (rec_sum Q'' : ℝ) = rec_sum Q' + 1 / (q' : ℝ) := by
            have hrsQ : rec_sum Q'' = rec_sum Q' + (1 : ℚ) / q' := by
              simp [Q'', rec_sum, hq'', add_comm]
            simpa [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using
              congrArg (fun x : ℚ ↦ (x : ℝ)) hrsQ
          have hsplit : Disjoint (local_part A' q') A'' := by
            rw [Finset.disjoint_left]
            intro n hnlocal hnA''
            rcases (mem_local_part (A := A') (q := q') n).mp hnlocal with ⟨_, hndvd, hncop⟩
            exact (Finset.mem_filter.mp hnA'').2 ⟨hndvd, hncop⟩
          have hunion : local_part A' q' ∪ A'' = A' := by
            ext n
            constructor
            · intro hn
              rcases Finset.mem_union.mp hn with hn | hn
              · exact (mem_local_part (A := A') (q := q') n).mp hn |>.1
              · exact (Finset.mem_filter.mp hn).1
            · intro hnA
              by_cases hp : q' ∣ n ∧ Nat.Coprime q' (n / q')
              · exact Finset.mem_union.mpr <| Or.inl <|
                  (mem_local_part (A := A') (q := q') n).2 ⟨hnA, hp.1, hp.2⟩
              · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_filter.mpr ⟨hnA, hp⟩
          have hlocaleq : rec_sum_local A' q' / q' = rec_sum (local_part A' q') := by
            rw [rec_sum_local, rec_sum, Finset.sum_div]
            refine Finset.sum_congr rfl ?_
            intro n hn
            by_cases hn0 : n = 0
            · simp [hn0]
            · field_simp [hn0, hq'zero']
          have hrs2a : rec_sum A'' + rec_sum_local A' q' / q' = rec_sum A' := by
            calc
              rec_sum A'' + rec_sum_local A' q' / q' =
                  rec_sum A'' + rec_sum (local_part A' q') := by
                rw [hlocaleq]
              _ = rec_sum (local_part A' q' ∪ A'') := by
                rw [add_comm, ← rec_sum_disjoint hsplit]
              _ = rec_sum A' := by
                rw [hunion]
          have hrs2a_real : (rec_sum A'' : ℝ) + rec_sum_local A' q' / (q' : ℝ) = rec_sum A' := by
            exact_mod_cast hrs2a
          have hrs3 : (rec_sum A' : ℝ) ≤ rec_sum A'' + ε * (1 / (q' : ℝ)) := by
            rw [← hrs2a_real, div_eq_mul_one_div]
            have hqnonneg : 0 ≤ (q' : ℝ) := by
              exact_mod_cast Nat.zero_le q'
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left
                (mul_le_mul_of_nonneg_right h4 <| one_div_nonneg.mpr hqnonneg) (rec_sum A'' : ℝ)
          have hmain : (rec_sum A : ℝ) - ε * rec_sum Q' - ε * (1 / (q' : ℝ)) ≤ rec_sum A'' := by
            linarith [hr, hrs3]
          have hrewrite :
              (rec_sum A : ℝ) - ε * rec_sum Q'' =
                (rec_sum A : ℝ) - ε * rec_sum Q' - ε * (1 / (q' : ℝ)) := by
            rw [hrs]
            ring
          rw [hrewrite]
          exact hmain
        · left
          rw [Nat.succ_le_iff]
          refine (hi.resolve_right hq_neg).trans_lt ?_
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset
            (Finset.sdiff_subset_sdiff Finset.Subset.rfl (Finset.filter_subset _ _))]
          simp only [ppowers_in_set, Finset.mem_biUnion, Finset.mem_filter, Nat.mem_divisors,
            and_assoc] at hq'
          obtain ⟨x, hx₁, hx₂, hx₃, -, hx₅⟩ := hq'
          refine ⟨x, ?_⟩
          simp [hx₁, hx₂, hx₅, hA' hx₁]

lemma pruning_lemma_one :
    ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Finset.range (N + 1), ∀ ε : ℝ, 0 < ε →
      ∃ B ⊆ A,
        ((rec_sum A : ℝ) - ε * 2 * log (log N) ≤ rec_sum B) ∧
        (∀ q ∈ ppowers_in_set B, ε < rec_sum_local B q) := by
  filter_upwards [explicit_mertens] with N hN A hA ε hε
  obtain ⟨B, hB, Q, hQ, haux, h_recsums, h_local⟩ := pruning_lemma_one_prec A ε (A.card + 1)
  refine ⟨B, hB, ?_, ?_⟩
  · have hQu : Q ⊆ (Finset.range (N + 1)).filter IsPrimePow := by
      intro q hq
      rw [Finset.mem_filter, Finset.mem_range]
      have hqA : q ∈ ppowers_in_set A := hQ hq
      simp only [ppowers_in_set, Finset.mem_biUnion, Finset.mem_filter] at hqA
      obtain ⟨a, ha, hqa, hq', hq''⟩ := hqA
      exact ⟨(Nat.divisor_le hqa).trans_lt (Finset.mem_range.mp (hA ha)), hq'⟩
    have hQt :
        (rec_sum Q : ℝ) ≤
          ((Finset.range (N + 1)).filter IsPrimePow).sum (fun q ↦ (1 / q : ℝ)) := by
      simp only [rec_sum, Rat.cast_sum, one_div, Rat.cast_inv, Rat.cast_natCast]
      exact Finset.sum_le_sum_of_subset_of_nonneg hQu (by simp)
    nlinarith
  · rcases h_local with hcard | hlocal
    · exfalso
      rw [Nat.succ_le_iff] at hcard
      exact not_lt_of_ge (Finset.card_le_card Finset.sdiff_subset) hcard
    · exact hlocal

lemma pruning_lemma_two_ind :
    ∀ᶠ N : ℕ in atTop, ∀ M α ε : ℝ, ∀ A ⊆ Finset.range (N + 1),
      0 < M → M < N → 0 < ε → 4 * ε * log (log N) < α → (∀ n ∈ A, M ≤ ↑n) →
      α ≤ rec_sum A →
      (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε * M ∧ ε < rec_sum_local A q) →
      ∀ i : ℕ,
        ∃ A_i ⊆ A,
          (α - 1 / M ≤ rec_sum A_i) ∧
          (∀ q ∈ ppowers_in_set A_i, ε < rec_sum_local A_i q) ∧
          (i ≤ (A \ A_i).card ∨ (rec_sum A_i : ℝ) < α) := by
  filter_upwards [pruning_lemma_one] with N hN M α ε A hA hM hMN hε hεα hMA hrec hsmooth i
  induction i with
  | zero =>
      refine ⟨A, Finset.Subset.rfl, ?_, ?_, Or.inl zero_le⟩
      · exact (sub_le_self _ (by simp only [hM.le, one_div, inv_nonneg])).trans hrec
      · intro q hq
        exact (hsmooth _ hq).2
  | succ i ih =>
      obtain ⟨A_i, hA_i, ih1, ih2, ih3⟩ := ih
      by_cases hr : (rec_sum A_i : ℝ) < α
      · exact ⟨A_i, hA_i, ih1, ih2, Or.inr hr⟩
      · have hA_ir : A_i ⊆ Finset.range (N + 1) := hA_i.trans hA
        let ε' := 2 * ε
        obtain ⟨B, hB, hN1, hN2⟩ := hN A_i hA_ir ε' (mul_pos zero_lt_two hε)
        have ht0 : α ≤ rec_sum A_i := not_lt.mp hr
        have hBexists : B.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          rintro rfl
          simp only [rec_sum_empty, Rat.cast_zero, sub_nonpos] at hN1
          have ht1 : 4 * ε * log (log N) < ε' * 2 * log (log N) := by
            exact hεα.trans_le (ht0.trans hN1)
          rw [mul_right_comm 2 ε] at ht1
          linarith only [ht1]
        rcases hBexists with ⟨x, hx⟩
        have hxA1 : x ∈ A_i := hB hx
        have hxA2 : x ∈ A := hA_i hxA1
        let A_i' := A_i.erase x
        have h3 : A_i' ⊆ A_i := Finset.erase_subset _ _
        refine ⟨A_i', h3.trans hA_i, ?_, ?_, ?_⟩
        · have hrs2 : (rec_sum A_i : ℝ) - 1 / x = rec_sum A_i' := by
            simp only [A_i', rec_sum, sub_eq_iff_eq_add, Rat.cast_sum, one_div, Rat.cast_inv,
              Rat.cast_natCast, Finset.sum_erase_add _ _ hxA1]
          linarith only [ht0, one_div_le_one_div_of_le hM (hMA x (hA_i (hB hx))), hrs2]
        · intro q hq
          by_cases hxq : q ∣ x ∧ Nat.Coprime q (x / q)
          · have hlocalpart : local_part A_i' q = (local_part A_i q).erase x := by
              exact Finset.filter_erase _ _ _
            have hlocal : rec_sum_local A_i q = rec_sum_local A_i' q + q / x := by
              rw [rec_sum_local, rec_sum_local, hlocalpart, Finset.sum_erase_add]
              rw [local_part, Finset.mem_filter]
              exact ⟨hB hx, hxq⟩
            have hlocal2 : rec_sum_local A_i q - q / x = rec_sum_local A_i' q := by
              rwa [sub_eq_iff_eq_add]
            rw [← hlocal2]
            push_cast
            have hppB : q ∈ ppowers_in_set B := by
              rw [ppowers_in_set, Finset.mem_biUnion]
              refine ⟨x, hx, Finset.mem_filter.2 ?_⟩
              refine ⟨Nat.mem_divisors.2 ⟨hxq.1, ?_⟩, (mem_ppowers_in_set.1 hq).1, hxq.2⟩
              rintro rfl
              exact not_le_of_gt hM (by simpa only [Nat.cast_zero] using hMA _ hxA2)
            have hlocal3 : (rec_sum_local B q : ℝ) ≤ rec_sum_local A_i q :=
              Rat.cast_le.2 (rec_sum_local_mono hB)
            have hll : ε + ε < rec_sum_local A_i q := by
              rw [← two_mul ε]
              exact (hN2 q hppB).trans_le hlocal3
            have hll2 : (q : ℝ) / x ≤ ε := by
              rw [div_le_iff₀ (hM.trans_le (hMA x hxA2))]
              have hppA : ppowers_in_set A_i' ⊆ ppowers_in_set A :=
                ppowers_in_set_subset (h3.trans hA_i)
              exact (hsmooth q (hppA hq)).1.trans (mul_le_mul_of_nonneg_left (hMA x hxA2) hε.le)
            rw [lt_sub_iff_add_lt]
            linarith
          · have hrecl : rec_sum_local A_i q = rec_sum_local A_i' q := by
              have hlocalaux : local_part A_i q = local_part A_i' q := by
                ext n
                by_cases hnx : n = x
                · subst hnx
                  simp [A_i', local_part, hxA1, hxq]
                · simp [A_i', local_part, hnx]
              rw [rec_sum_local, rec_sum_local, hlocalaux]
            rw [← hrecl]
            exact ih2 q (ppowers_in_set_subset h3 hq)
        · left
          have hcard : (A \ A_i).card < (A \ A_i').card := by
            rw [Finset.card_sdiff_of_subset hA_i, Finset.card_sdiff_of_subset (h3.trans hA_i),
              tsub_lt_tsub_iff_left_of_le (Finset.card_le_card hA_i)]
            exact Finset.card_erase_lt_of_mem hxA1
          have hcard' : (A \ A_i).card + 1 ≤ (A \ A_i').card := Nat.succ_le_iff.2 hcard
          cases ih3 with
          | inl hf1 =>
              linarith
          | inr hf2 =>
              exfalso
              linarith

lemma pruning_lemma_two :
    ∀ᶠ N : ℕ in atTop, ∀ M α ε : ℝ, ∀ A ⊆ Finset.range (N + 1),
      0 < M → M < N → ε > 0 → 4 * ε * log (log N) < α →
      (∀ n ∈ A, M ≤ (n : ℝ)) →
      α + 2 * ε * log (log N) ≤ rec_sum A →
      (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε * M) →
      ∃ B ⊆ A,
        ((rec_sum B : ℝ) < α) ∧
        (α - 1 / M ≤ rec_sum B) ∧
        (∀ q ∈ ppowers_in_set B, ε < rec_sum_local B q) := by
  filter_upwards [pruning_lemma_one, pruning_lemma_two_ind] with
    N h₁ h₂ M α ε A hA hM hMN hε hεα hMA hrec hsmooth
  obtain ⟨A', hA', hA'₁, hA'₃⟩ := h₁ A hA ε hε
  have hA'range : A' ⊆ Finset.range (N + 1) := hA'.trans hA
  have hMA' : ∀ n ∈ A', M ≤ (n : ℝ) := fun n hn => hMA n (hA' hn)
  have hrecA' : α ≤ rec_sum A' := by
    have hA'₁' : ((rec_sum A : ℝ) - 2 * ε * log (log N) ≤ rec_sum A') := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hA'₁
    nlinarith
  have hsmooth' : ∀ q ∈ ppowers_in_set A', (q : ℝ) ≤ ε * M ∧ ε < rec_sum_local A' q := by
    intro q hq
    exact ⟨hsmooth q ((ppowers_in_set_subset hA') hq), hA'₃ q hq⟩
  let i := A'.card + 1
  obtain ⟨B, hB, hB₁, hB₂, hB₃⟩ := h₂ M α ε A' hA'range hM hMN hε hεα hMA' hrecA' hsmooth' i
  refine ⟨B, hB.trans hA', ?_, hB₁, hB₂⟩
  refine hB₃.resolve_left ?_
  dsimp [i]
  intro hcard
  exact not_le_of_gt (Nat.lt_succ_self A'.card)
    (hcard.trans (Finset.card_le_card Finset.sdiff_subset))

lemma main_tech_lemma_ind :
    ∀ᶠ N : ℕ in atTop, ∀ M ε y w : ℝ, ∀ A ⊆ Finset.range (N + 1),
      0 < M → M < N → 0 < ε → w < 2 * M → 1 / M < ε * log (log N) →
      1 ≤ y → 2 ≤ w → ⌈y⌉₊ ≤ ⌊w⌋₊ →
      3 * ε * log (log N) ≤ 2 / w ^ 2 →
      (∀ n ∈ A, M ≤ (n : ℝ)) →
      2 / y + 2 * ε * log (log N) ≤ rec_sum A →
      (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε * M) →
      (∀ n ∈ A, ∃ d : ℕ, y ≤ d ∧ (d : ℝ) ≤ w ∧ d ∣ n) →
      ∀ i : ℕ,
        ∃ A_i ⊆ A, ∃ d_i : ℕ,
          y ≤ d_i ∧ d_i ≤ ⌈y⌉₊ + i ∧ d_i ≤ ⌊w⌋₊ ∧
          rec_sum A_i < 2 / d_i ∧ (2 : ℝ) / d_i - 1 / M ≤ rec_sum A_i ∧
          (∀ q ∈ ppowers_in_set A_i, ε < rec_sum_local A_i q) ∧
          (∀ n ∈ A_i, ∀ k, k ∣ n → k < d_i → (k : ℝ) < y) ∧
          ((∃ n ∈ A_i, d_i ∣ n) ∨
            (∀ n ∈ A_i, ∀ k, k ∣ n → k ≤ ⌈y⌉₊ + i → k ≤ ⌊w⌋₊ → (k : ℝ) < y)) := by
  have hloglog : Tendsto (fun N : ℕ ↦ log (log N)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [pruning_lemma_two, hloglog.eventually (eventually_gt_atTop (0 : ℝ))] with
    N hN hloglog_pos M ε y w A hA hM hMN hε hMw hMN2 hy h2w hyw2 hNw hMA hrec hsmooth hdiv i
  have hy01 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hy12 : 2 ≤ y + 1 := by linarith
  have hceil_lt : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy01.le
  have hwzero : 0 < w := lt_of_lt_of_le zero_lt_two h2w
  have hfloor_le : (⌊w⌋₊ : ℝ) ≤ w := Nat.floor_le hwzero.le
  have hεNaux : 4 * ε * log (log N) < 2 * (3 * ε * log (log N)) := by
    nlinarith [hε, hloglog_pos]
  have hεNaux2 : 2 * (3 * ε * log (log N)) ≤ 2 * (2 / w ^ 2) := by
    nlinarith [hNw]
  have hwaux : 2 * w ≤ w ^ 2 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right h2w hwzero.le
  induction i with
  | zero =>
      let α : ℚ := 2 / ⌈y⌉₊
      have hαaux : (α : ℝ) = 2 / ⌈y⌉₊ := by
        simp [α]
      have hceil_le_w : (⌈y⌉₊ : ℝ) ≤ w := (Nat.cast_le.mpr hyw2).trans hfloor_le
      have hceil_pos : 0 < (⌈y⌉₊ : ℝ) := by
        exact_mod_cast Nat.ceil_pos.mpr hy01
      have hα : 4 * ε * log (log N) < α := by
        have hα1 : 2 * ((2 : ℝ) / w ^ 2) ≤ 2 / ⌈y⌉₊ := by
          have hα1' : (4 : ℝ) / w ^ 2 ≤ 2 / ⌈y⌉₊ := by
            refine (div_le_div_iff₀ (by positivity) hceil_pos).2 ?_
            nlinarith [hceil_le_w, hwaux]
          simpa [show (4 : ℝ) / w ^ 2 = 2 * ((2 : ℝ) / w ^ 2) by ring] using hα1'
        rw [hαaux]
        exact hεNaux.trans_le (hεNaux2.trans hα1)
      have hrec2 : (α : ℝ) + 2 * ε * log (log N) ≤ rec_sum A := by
        rw [hαaux]
        have hdivaux : (2 : ℝ) / ⌈y⌉₊ ≤ 2 / y :=
          div_le_div_of_nonneg_left zero_le_two hy01 (Nat.le_ceil y)
        linarith
      obtain ⟨B, hB, hB', hB'', hN'⟩ := hN M α ε A hA hM hMN hε hα hMA hrec2 hsmooth
      refine ⟨B, hB, ⌈y⌉₊, ?_, Nat.le_refl _, hyw2, ?_, ?_, hN', ?_, ?_⟩
      · exact Nat.le_ceil y
      · exact_mod_cast hB'
      · simpa [hαaux] using hB''
      · intro n hn k hk1 hk2
        exact Nat.lt_ceil.mp hk2
      · refine or_iff_not_imp_left.2 ?_
        intro hp n hn k hk1 hk2 hk3
        have hklt : k < ⌈y⌉₊ := by
          refine lt_of_le_of_ne hk2 ?_
          intro hk
          apply hp
          exact ⟨n, hn, hk ▸ hk1⟩
        exact Nat.lt_ceil.mp hklt
  | succ i ih =>
      rcases ih with ⟨A_i, hA_i, d_i, hyi, hdiy, hdiw, hrec_lt, hrec_ge, hsmooth_i, hsmall, hfinal⟩
      by_cases hdiv2 : ∃ n ∈ A_i, d_i ∣ n
      · exact ⟨A_i, hA_i, d_i, hyi, hdiy.trans (Nat.le_succ _), hdiw, hrec_lt, hrec_ge,
          hsmooth_i, hsmall, Or.inl hdiv2⟩
      · let dNext := min (⌈y⌉₊ + i + 1) ⌊w⌋₊
        have hdNext : d_i + 1 ≤ dNext := by
          change d_i + 1 ≤ min (⌈y⌉₊ + i + 1) ⌊w⌋₊
          rw [le_min_iff]
          refine ⟨Nat.succ_le_succ hdiy, ?_⟩
          refine lt_of_le_of_ne hdiw ?_
          intro hdEq
          have hA_in : A_i.Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hAi
            have hrec_nonpos : (rec_sum A_i : ℝ) ≤ 0 := by
              simp [hAi]
            have hlower : (2 : ℝ) / d_i - 1 / M ≤ 0 := le_trans hrec_ge hrec_nonpos
            have hdipos : 0 < (d_i : ℝ) := hy01.trans_le hyi
            have hdi_le_w : (d_i : ℝ) ≤ w := (Nat.cast_le.mpr hdiw).trans hfloor_le
            have hMw' : 2 * M ≤ w := by
              have hMd : 2 * M ≤ (d_i : ℝ) := by
                have hlower' := hlower
                field_simp [hdipos.ne', hM.ne'] at hlower'
                nlinarith
              linarith
            exact (not_lt_of_ge hMw') hMw
          obtain ⟨x, hx⟩ := hA_in
          obtain ⟨d, hd1, hd2, hd3⟩ := hdiv x (hA_i hx)
          have hdle : d ≤ ⌊w⌋₊ := Nat.le_floor hd2
          have hdle' : d ≤ d_i := by simpa [hdEq] using hdle
          have hlt : d < d_i := by
            refine lt_of_le_of_ne hdle' ?_
            intro hdEq'
            apply hdiv2
            exact ⟨x, hx, hdEq' ▸ hd3⟩
          exact (not_le_of_gt (hsmall x hx d hd3 hlt)) hd1
        let αNext : ℚ := 2 / dNext
        have hαNextaux : (αNext : ℝ) = 2 / (dNext : ℝ) := by
          simp [αNext]
        have hdNext_le_floor : dNext ≤ ⌊w⌋₊ := by
          simp [dNext]
        have hdNext_le_w : (dNext : ℝ) ≤ w := (Nat.cast_le.mpr hdNext_le_floor).trans hfloor_le
        have hdipos_real : 0 < (d_i : ℝ) := hy01.trans_le hyi
        have hdipos_nat : 0 < d_i := Nat.cast_pos.mp hdipos_real
        have hOneLt_dNext : (1 : ℝ) < dNext := by
          exact_mod_cast lt_of_lt_of_le (Nat.succ_lt_succ hdipos_nat) hdNext
        have hαNext : 4 * ε * log (log N) < αNext := by
          have hαNext1' : (4 : ℝ) / w ^ 2 ≤ 2 / (dNext : ℝ) := by
            refine (div_le_div_iff₀ (by positivity) (zero_lt_one.trans hOneLt_dNext)).2 ?_
            nlinarith [hdNext_le_w, hwaux]
          have hαNext1 : 2 * ((2 : ℝ) / w ^ 2) ≤ 2 / (dNext : ℝ) := by
            simpa [show (4 : ℝ) / w ^ 2 = 2 * ((2 : ℝ) / w ^ 2) by ring] using hαNext1'
          rw [hαNextaux]
          exact hεNaux.trans_le (hεNaux2.trans hαNext1)
        have hrec2 : (αNext : ℝ) + 2 * ε * log (log N) ≤ rec_sum A_i := by
          rw [hαNextaux]
          have hrec3p : (d_i : ℝ) ≤ (dNext : ℝ) - 1 := by
            have hdNext' : (d_i : ℝ) + 1 ≤ dNext := by exact_mod_cast hdNext
            linarith
          have hrec3 : (2 : ℝ) / ((dNext : ℝ) - 1) - 1 / M ≤ rec_sum A_i := by
            have hrec3' : (2 : ℝ) / ((dNext : ℝ) - 1) ≤ 2 / d_i :=
              div_le_div_of_nonneg_left zero_le_two hdipos_real hrec3p
            exact le_trans (sub_le_sub_right hrec3' _) hrec_ge
          have hrec5 : (2 : ℝ) / (dNext : ℝ) ^ 2 ≤ 2 / ((dNext : ℝ) - 1) - 2 / (dNext : ℝ) := by
            have hdNext_pos : 0 < (dNext : ℝ) := zero_lt_one.trans hOneLt_dNext
            have hsubpos : 0 < (dNext : ℝ) - 1 := sub_pos.mpr hOneLt_dNext
            field_simp [hdNext_pos.ne', hsubpos.ne']
            nlinarith
          have hrec6 : (2 : ℝ) / w ^ 2 ≤ 2 / (dNext : ℝ) ^ 2 := by
            refine div_le_div_of_nonneg_left zero_le_two (by positivity) ?_
            nlinarith [hdNext_le_w, hwzero]
          linarith [hMN2, hNw, hrec3, hrec5, hrec6]
        have hA_i' : A_i ⊆ Finset.range (N + 1) := hA_i.trans hA
        have hMA' : ∀ n ∈ A_i, M ≤ (n : ℝ) := fun n hn => hMA n (hA_i hn)
        have hsmooth' : ∀ q ∈ ppowers_in_set A_i, (q : ℝ) ≤ ε * M := by
          intro q hq
          exact hsmooth q ((ppowers_in_set_subset hA_i) hq)
        obtain ⟨B, hB, hBlt, hBge, hBsm⟩ :=
          hN M αNext ε A_i hA_i' hM hMN hε hαNext hMA' hrec2 hsmooth'
        refine ⟨B, hB.trans hA_i, dNext, ?_, ?_, hdNext_le_floor, ?_, ?_, hBsm, ?_, ?_⟩
        · exact hyi.trans (Nat.cast_le.mpr <| (Nat.le_succ _).trans hdNext)
        · simp [dNext]
        · exact_mod_cast hBlt
        · simpa [hαNextaux] using hBge
        · intro n hn k hk1 hk2
          have hn2 : n ∈ A_i := hB hn
          cases hfinal with
          | inl h =>
              exfalso
              exact hdiv2 h
          | inr hnew2 =>
              have hk2' : k ≤ ⌈y⌉₊ + i := by
                change k < min (⌈y⌉₊ + i + 1) ⌊w⌋₊ at hk2
                rw [lt_min_iff] at hk2
                exact Nat.le_of_lt_succ hk2.1
              have hk2'' : k ≤ ⌊w⌋₊ := by
                change k < min (⌈y⌉₊ + i + 1) ⌊w⌋₊ at hk2
                rw [lt_min_iff] at hk2
                exact le_of_lt hk2.2
              exact hnew2 n hn2 k hk1 hk2' hk2''
        · by_cases hdNextDiv : ∃ n ∈ B, dNext ∣ n
          · exact Or.inl hdNextDiv
          · right
            intro n hn k hk1 hk2 hk3
            have hn2 : n ∈ A_i := hB hn
            cases hfinal with
            | inl h =>
                exfalso
                exact hdiv2 h
            | inr hnew2 =>
                have hk2' : k ≤ dNext := by
                  change k ≤ min (⌈y⌉₊ + i + 1) ⌊w⌋₊
                  rw [le_min_iff]
                  exact ⟨hk2, hk3⟩
                have hk2'' : k < dNext := by
                  refine lt_of_le_of_ne hk2' ?_
                  intro hkEq
                  apply hdNextDiv
                  exact ⟨n, hn, hkEq ▸ hk1⟩
                have hk2''' : k ≤ ⌈y⌉₊ + i := by
                  change k < min (⌈y⌉₊ + i + 1) ⌊w⌋₊ at hk2''
                  rw [lt_min_iff] at hk2''
                  exact Nat.le_of_lt_succ hk2''.1
                have hk2'''' : k ≤ ⌊w⌋₊ := by
                  change k < min (⌈y⌉₊ + i + 1) ⌊w⌋₊ at hk2''
                  rw [lt_min_iff] at hk2''
                  exact le_of_lt hk2''.2
                exact hnew2 n hn2 k hk1 hk2''' hk2''''

lemma main_tech_lemma :
    ∀ᶠ N : ℕ in atTop, ∀ M ε y w : ℝ, ∀ A ⊆ Finset.range (N + 1),
      0 < M → M < N → 0 < ε → 2 * M > w → 1 / M < ε * log (log N) →
      1 ≤ y → 2 ≤ w → ⌈y⌉₊ ≤ ⌊w⌋₊ →
      3 * ε * log (log N) ≤ 2 / (w ^ 2) →
      (∀ n ∈ A, M ≤ (n : ℝ)) →
      2 / y + 2 * ε * log (log N) ≤ rec_sum A →
      (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε * M) →
      (∀ n ∈ A, ∃ d : ℕ, y ≤ d ∧ ((d : ℝ) ≤ w) ∧ d ∣ n) →
      ∃ A' ⊆ A, ∃ d : ℕ,
        A' ≠ ∅ ∧ y ≤ d ∧ ((d : ℝ) ≤ w) ∧ rec_sum A' < 2 / d ∧
        (2 : ℝ) / d - 1 / M ≤ rec_sum A' ∧
        (∀ q ∈ ppowers_in_set A', ε < rec_sum_local A' q) ∧
        (∃ n ∈ A', d ∣ n) ∧
        (∀ n ∈ A', ∀ k : ℕ, k ∣ n → k < d → (k : ℝ) < y) := by
  have hloglog : Tendsto (fun N : ℕ ↦ log (log N)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [main_tech_lemma_ind, hloglog.eventually (eventually_gt_atTop (0 : ℝ))] with
    N hN hloglog_pos M ε y w A hA hM hMN hε hMw hMN2 hy h2w hyw hNw hAM hrec hsmooth hdiv
  have hy01 : 0 < y := by
    exact lt_of_lt_of_le zero_lt_one hy
  have hwzero : 0 < w := by
    exact lt_of_lt_of_le zero_lt_two h2w
  let i := ⌊w⌋₊ - ⌈y⌉₊
  specialize hN M ε y w A hA hM hMN hε hMw hMN2 hy h2w hyw hNw hAM hrec hsmooth hdiv i
  rcases hN with ⟨A', hA', d, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8⟩
  refine ⟨A', hA', d, ?_⟩
  have hdw : (d : ℝ) ≤ w := by
    have hfloorw : (⌊w⌋₊ : ℝ) ≤ w := Nat.floor_le hwzero.le
    have hdfloor : (d : ℝ) ≤ (⌊w⌋₊ : ℝ) := by
      exact_mod_cast hd3
    exact hdfloor.trans hfloorw
  have hA'ne : A' ≠ ∅ := by
    intro hA'em
    have hreczero : rec_sum A' = 0 := by
      rw [hA'em, rec_sum_empty]
    have hlow : (2 : ℝ) / d - 1 / M ≤ 0 := by
      rw [hreczero] at hd5
      simpa using hd5
    have haux1 : (2 : ℝ) / d ≤ 1 / M := by
      exact sub_nonpos.mp hlow
    have haux2 : (2 : ℝ) / w ≤ 2 / d := by
      refine div_le_div_of_nonneg_left zero_le_two ?_ ?_
      · exact hy01.trans_le hd1
      · exact hdw
    have haux3 : (2 : ℝ) / w ^ 2 ≤ 2 / w := by
      field_simp [hwzero.ne']
      nlinarith [h2w, hwzero]
    have haux4 : 3 * ε * log (log N) < ε * log (log N) := by
      exact lt_of_le_of_lt hNw <| lt_of_le_of_lt haux3 <| lt_of_le_of_lt haux2 <|
        lt_of_le_of_lt haux1 hMN2
    have hthree_lt_one : (3 : ℝ) < 1 := by
      nlinarith [haux4, hε, hloglog_pos]
    linarith
  refine ⟨hA'ne, hd1, hdw, hd4, hd5, hd6, ?_, hd7⟩
  · cases hd8 with
    | inl h =>
        exact h
    | inr h =>
        exfalso
        have hAexists : ∃ x : ℕ, x ∈ A' := by
          by_contra h
          apply hA'ne
          apply Finset.not_nonempty_iff_eq_empty.mp
          simpa [Finset.Nonempty] using h
        rcases hAexists with ⟨x, hx⟩
        have hxA : x ∈ A := hA' hx
        rcases hdiv x hxA with ⟨m, hm1, hm2, hm3⟩
        have htempw : m ≤ ⌊w⌋₊ := Nat.le_floor hm2
        have htemp : m ≤ ⌈y⌉₊ + i := by
          have hobvious : ⌈y⌉₊ + i = ⌊w⌋₊ := by
            dsimp [i]
            exact Nat.add_sub_of_le hyw
          rw [hobvious]
          exact htempw
        have := h x hx m hm3 htemp htempw
        linarith

private lemma large_enough_Naux1_hreduce
    (N : ℕ) (hN6 : 0 < (N : ℝ)) (hN7 : 0 < log (log N)) (hN8 : 0 < log N) :
    (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤
      ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ))) *
        (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 / (16 * N ^ 2 * log N ^ 2)) ↔
      (2 * 16 : ℝ) * log N ^ (2 + 1 / 100 : ℝ) ≤ (N : ℝ) ^ (1 / log (log N)) := by
  have hAiff :
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤
          ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ))) *
            (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 / (16 * N ^ 2 * log N ^ 2)) ↔
        log (2 * 16) + (2 + 1 / 100 : ℝ) * log (log N) ≤ log N / log (log N) := by
    rw [← Real.log_le_log_iff
      (show 0 < (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) by positivity)
      (show 0 <
        ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ))) *
          (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 / (16 * N ^ 2 * log N ^ 2)) by
            positivity)]
    have hsq :
        (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2) =
          (N : ℝ) ^ ((1 - (3 : ℝ) / log (log N)) * 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hN6)]
      ring_nf
    rw [Real.log_mul
        (show (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ)) ≠ 0 by
          positivity)
        (show (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 / (16 * N ^ 2 * log N ^ 2)) ≠ 0 by
          positivity)]
    rw [Real.log_div
        (Real.rpow_pos_of_pos hN6 _).ne'
        (show (2 * log N ^ (1 / 100 : ℝ)) ≠ 0 by positivity)]
    rw [Real.log_div
        (show (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2) ≠ 0 by positivity)
        (show (16 * N ^ 2 * log N ^ 2 : ℝ) ≠ 0 by positivity)]
    have hlogDen1 :
        Real.log (16 * N ^ 2 * log N ^ 2 : ℝ) =
          Real.log 16 + 2 * Real.log N + 2 * Real.log (Real.log N) := by
      rw [show (16 * N ^ 2 * log N ^ 2 : ℝ) = 16 * ((N : ℝ) ^ 2 * log N ^ 2) by
        ring_nf]
      rw [Real.log_mul (show (16 : ℝ) ≠ 0 by norm_num)
        (show (N : ℝ) ^ 2 * log N ^ 2 ≠ 0 by positivity)]
      rw [Real.log_mul
        (show (N : ℝ) ^ 2 ≠ 0 by positivity)
        (show log N ^ 2 ≠ 0 by positivity)]
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, Real.log_rpow hN6, Real.log_rpow hN8]
      ring_nf
    have hlogDen2 :
        Real.log (2 * log N ^ (1 / 100 : ℝ)) =
          Real.log 2 + (1 / 100 : ℝ) * Real.log (Real.log N) := by
      rw [Real.log_mul
        (show (2 : ℝ) ≠ 0 by norm_num)
        (show log N ^ (1 / 100 : ℝ) ≠ 0 by positivity)]
      rw [Real.log_rpow hN8]
    rw [Real.log_rpow hN6, hsq, hlogDen1, hlogDen2]
    simp_rw [Real.log_rpow hN6]
    have hlog32 : Real.log (2 * 16 : ℝ) = Real.log 2 + Real.log 16 := by
      rw [Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) (show (16 : ℝ) ≠ 0 by norm_num)]
    constructor
    · intro h
      rw [hlog32] at *
      field_simp [hN7.ne'] at h ⊢
      ring_nf at h ⊢
      linarith
    · intro h
      rw [hlog32] at *
      field_simp [hN7.ne'] at h ⊢
      ring_nf at h ⊢
      linarith
  have hBiff :
      (2 * 16 : ℝ) * log N ^ (2 + 1 / 100 : ℝ) ≤ (N : ℝ) ^ (1 / log (log N)) ↔
        log (2 * 16) + (2 + 1 / 100 : ℝ) * log (log N) ≤ log N / log (log N) := by
    rw [← Real.log_le_log_iff
      (show 0 < (2 * 16 : ℝ) * log N ^ (2 + 1 / 100 : ℝ) by positivity)
      (show 0 < (N : ℝ) ^ (1 / log (log N)) by positivity)]
    rw [Real.log_mul (show (2 * 16 : ℝ) ≠ 0 by norm_num)
      (Real.rpow_pos_of_pos hN8 _).ne']
    rw [Real.log_rpow hN8, Real.log_rpow hN6]
    constructor
    · intro h
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
    · intro h
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  exact hAiff.trans hBiff.symm

lemma large_enough_Naux1 :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤
        ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ))) *
          (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 / (16 * N ^ 2 * log N ^ 2)) := by
  let C : ℝ := (((2 : ℝ) * ((2 : ℝ) + (1 / 100 : ℝ))) ^ ((1 : ℝ) / 2))
  have haux4 :=
    (isLittleO_log_id_atTop.bound <| by
      rw [one_div_pos]
      exact mul_pos zero_lt_two (Real.log_pos (show (1 : ℝ) < 2 * 16 by norm_num)))
  have haux5 :
      ∀ᶠ x : ℝ in atTop,
        ‖log x‖ ≤ (1 / C) * ‖x ^ ((1 : ℝ) / 2)‖ :=
    (isLittleO_log_rpow_atTop (half_pos zero_lt_one)).bound <| by
      rw [one_div_pos]
      dsimp [C]
      exact Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) * ((2 : ℝ) + (1 / 100 : ℝ)) by norm_num)
        _
  filter_upwards
    [ tendsto_log_log_coe_at_top (eventually_ge_atTop (6 : ℝ))
    , tendsto_log_coe_at_top.eventually (eventually_ge_atTop ((128 : ℝ) ^ (500 : ℝ)))
    , eventually_ge_atTop (64 : ℕ)
    , tendsto_log_coe_at_top.eventually haux4
    , tendsto_log_coe_at_top.eventually haux5 ] with
    N hN1 hN2 hN3 hN3new4 hN3new5
  dsimp at hN1 hN2 hN3new4
  have hN4 : 1 < log (log N) := by
    linarith
  have hN5 : (1 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 64) hN3)
  have hN6 : (0 : ℝ) < N := by
    linarith
  have hN7 : 0 < log (log N) := by
    linarith
  have hN8 : 0 < log N := by
    have hpowpos : 0 < (128 : ℝ) ^ (500 : ℝ) := by
      exact Real.rpow_pos_of_pos (by norm_num) _
    exact lt_of_lt_of_le hpowpos hN2
  have hN12 : 2 * log (2 * 16) * log (log N) ≤ log N := by
    have habs : |log (log N)| ≤ (1 / (2 * log (2 * 16))) * |log N| := by
      simpa [Function.comp, id, Real.norm_eq_abs] using hN3new4
    rw [abs_of_nonneg hN7.le, abs_of_nonneg hN8.le] at habs
    have hconst : 0 < 2 * log (2 * 16) := by
      exact mul_pos zero_lt_two (Real.log_pos (by norm_num))
    have hdiv : log (log N) ≤ log N / (2 * log (2 * 16)) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using habs
    have hmul : log (log N) * (2 * log (2 * 16)) ≤ log N := by
      exact (_root_.le_div_iff₀ hconst).mp hdiv
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hN13 :
      C * log (log N) ≤ log N ^ ((1 : ℝ) / 2) := by
    have habs :
        |log (log N)| ≤ (1 / C) * |log N ^ ((1 : ℝ) / 2)| := by
      simpa [Function.comp, id, Real.norm_eq_abs] using hN3new5
    rw [abs_of_nonneg hN7.le, abs_of_nonneg (by positivity)] at habs
    have hconst : 0 < C := by
      dsimp [C]
      positivity
    have hdiv :
        log (log N) ≤ log N ^ ((1 : ℝ) / 2) / C := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using habs
    have hmul : log (log N) * C ≤ log N ^ ((1 : ℝ) / 2) := by
      exact (_root_.le_div_iff₀ hconst).mp hdiv
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hC_sq : C * C = 2 * (2 + (1 / 100 : ℝ)) := by
    dsimp [C]
    have hbase : 0 < (2 : ℝ) * ((2 : ℝ) + (1 / 100 : ℝ)) := by positivity
    rw [← Real.rpow_add hbase]
    norm_num
  have hreduce :
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤
        ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ))) *
          (((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 / (16 * N ^ 2 * log N ^ 2)) ↔
        (2 * 16 : ℝ) * log N ^ (2 + 1 / 100 : ℝ) ≤ (N : ℝ) ^ (1 / log (log N)) := by
    exact large_enough_Naux1_hreduce N hN6 hN7 hN8
  rw [hreduce]
  rw [← Real.log_le_log_iff
    (show 0 < (2 * 16 : ℝ) * log N ^ (2 + 1 / 100 : ℝ) by positivity)
    (show 0 < (N : ℝ) ^ (1 / log (log N)) by positivity)]
  rw [Real.log_mul (show (2 * 16 : ℝ) ≠ 0 by norm_num) (Real.rpow_pos_of_pos hN8 _).ne',
    Real.log_rpow hN8, Real.log_rpow hN6]
  have hfirst :
      log (2 * 16) ≤ (1 / 2 : ℝ) * (log N / log (log N)) := by
    have htmp : 2 * log (2 * 16) * log (log N) ≤ log N := hN12
    have hpos : 0 < log (log N) := hN7
    have htmp' : 2 * log (2 * 16) ≤ log N / log (log N) := by
      exact (_root_.le_div_iff₀ hpos).2 <| by simpa [mul_assoc] using htmp
    nlinarith
  have hsecond :
      (2 + 1 / 100 : ℝ) * log (log N) ≤ (1 / 2 : ℝ) * (log N / log (log N)) := by
    have hsq : 2 * (2 + 1 / 100 : ℝ) * (log (log N)) ^ 2 ≤ log N := by
      have hmul :=
        mul_le_mul hN13 hN13
          (show 0 ≤ C * log (log N) by positivity)
          (show 0 ≤ log N ^ ((1 : ℝ) / 2) by positivity)
      have hsimp :
          (C * log (log N)) * (C * log (log N)) =
            2 * (2 + 1 / 100 : ℝ) * (log (log N)) ^ 2 := by
        calc
          (C * log (log N)) * (C * log (log N)) =
              (C * C) * (log (log N) * log (log N)) := by ring
          _ = 2 * (2 + 1 / 100 : ℝ) * (log (log N)) ^ 2 := by
              rw [hC_sq]
              ring_nf
      have hsimp' : (log N ^ ((1 : ℝ) / 2)) * (log N ^ ((1 : ℝ) / 2)) = log N := by
        rw [← Real.rpow_add hN8]
        norm_num
      calc
        2 * (2 + 1 / 100 : ℝ) * (log (log N)) ^ 2 = (C * log (log N)) * (C * log (log N)) := by
          symm
          exact hsimp
        _ ≤ (log N ^ ((1 : ℝ) / 2)) * (log N ^ ((1 : ℝ) / 2)) := hmul
        _ = log N := hsimp'
    have htmp' : 2 * (2 + 1 / 100 : ℝ) * log (log N) ≤ log N / log (log N) := by
      exact (_root_.le_div_iff₀ hN7).2 <| by
        simpa [mul_assoc, pow_two] using hsq
    nlinarith
  calc
    log (2 * 16) + (2 + 1 / 100 : ℝ) * log (log N) ≤
        (1 / 2 : ℝ) * (log N / log (log N)) + (1 / 2 : ℝ) * (log N / log (log N)) := by
          exact add_le_add hfirst hsecond
    _ = log N / log (log N) := by ring
    _ = (1 / log (log N)) * log N := by ring

lemma large_enough_Naux2 :
    ∀ c : ℝ, c > 0 → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤
          c * (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (log N) ^ (1 / 500 : ℝ) ∧
        (log N) ^ (-(1 / 101 : ℝ)) ≤
          (2 : ℝ) / ((log N) ^ (1 / 500 : ℝ) / 4) -
            1 / (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
  intro c hc
  have haux :=
    (isLittleO_log_rpow_atTop (half_pos zero_lt_one)).bound (show 0 < (1 : ℝ) by norm_num)
  have haux2 := (isLittleO_log_rpow_atTop zero_lt_one).bound (show 0 < (1 : ℝ) by norm_num)
  filter_upwards
    [ (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (6 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (1 : ℝ))
    , eventually_ge_atTop (64 : ℕ)
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually haux
    , tendsto_natCast_atTop_atTop.eventually haux2
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (-log c / (7 - 1 / 500))) ] with
    N hN1 hN2 hN3 hNnew hNnew2 hNnew3
  dsimp at hN1 hN2 hNnew3
  have hN5 : (1 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 64) hN3)
  have hN6 : (0 : ℝ) < N := by
    linarith
  have hN7 : 0 < log (log N) := by
    linarith
  have hN8 : 0 < log N := by
    linarith
  have hN9 : log (log N) ≤ log N ^ ((1 : ℝ) / 2) := by
    have habs : |log (log N)| ≤ (1 : ℝ) * |log N ^ ((1 : ℝ) / 2)| := by
      simpa [Function.comp, id, Real.norm_eq_abs] using hNnew
    rw [abs_of_nonneg (le_of_lt hN7), abs_of_nonneg (by positivity), one_mul] at habs
    exact habs
  have hN10 : log N ≤ N := by
    have habs : |log N| ≤ (1 : ℝ) * |(N : ℝ) ^ (1 : ℝ)| := by
      simpa [Function.comp, id, Real.norm_eq_abs] using hNnew2
    rw [abs_of_nonneg (le_of_lt hN8), abs_of_nonneg (by positivity), one_mul, Real.rpow_one] at habs
    exact habs
  constructor
  · have hmain :
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) * (log N) ^ (1 / 500 : ℝ) ≤
          c * (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
      rw [← Real.log_le_log_iff (show 0 < (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) *
          (log N) ^ (1 / 500 : ℝ) by positivity)
        (show 0 < c * (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) by positivity)]
      rw [Real.log_mul (Real.rpow_pos_of_pos hN6 _).ne' (Real.rpow_pos_of_pos hN8 _).ne',
        Real.log_mul hc.ne' (Real.rpow_pos_of_pos hN6 _).ne', Real.log_rpow hN6,
        Real.log_rpow hN8, Real.log_rpow hN6]
      have hcN : -(7 - (1 : ℝ) / 500) * log (log N) ≤ log c := by
        have ha : 0 < (7 - (1 : ℝ) / 500) := by norm_num
        have htmp : -log c ≤ log (log N) * (7 - (1 : ℝ) / 500) := by
          exact (_root_.div_le_iff₀ ha).mp hNnew3
        nlinarith
      have hsqmul : log (log N) * log (log N) ≤ log N := by
        have hsq' :=
          mul_le_mul hN9 hN9
            (show 0 ≤ log (log N) by linarith)
            (show 0 ≤ log N ^ ((1 : ℝ) / 2) by positivity)
        have hlog : log N ^ ((1 : ℝ) / 2) * log N ^ ((1 : ℝ) / 2) = log N := by
          rw [← Real.rpow_add hN8]
          norm_num
        calc
          log (log N) * log (log N) ≤ log N ^ ((1 : ℝ) / 2) * log N ^ ((1 : ℝ) / 2) := by
            simpa [pow_two] using hsq'
          _ = log N := hlog
      have hdiv : log (log N) ≤ log N / log (log N) := by
        exact (_root_.le_div_iff₀ hN7).2 hsqmul
      have hfrac : -(7 : ℝ) * (log N / log (log N)) + (1 / 500 : ℝ) * log (log N) ≤ log c := by
        have hstep :
            -(7 : ℝ) * (log N / log (log N)) + (1 / 500 : ℝ) * log (log N) ≤
              -(7 : ℝ) * log (log N) + (1 / 500 : ℝ) * log (log N) := by
          nlinarith
        linarith
      have hadd := add_le_add_right hfrac ((1 - (1 : ℝ) / log (log N)) * log N)
      have hrew :
          (-(7 : ℝ) * (log N / log (log N)) + (1 / 500 : ℝ) * log (log N)) +
              ((1 - (1 : ℝ) / log (log N)) * log N) =
            (1 - (8 : ℝ) / log (log N)) * log N + (1 / 500 : ℝ) * log (log N) := by
        field_simp [hN7.ne']
        ring
      have hrew' :
          ((1 - (1 : ℝ) / log (log N)) * log N) +
              (-(7 : ℝ) * (log N / log (log N)) + (1 / 500 : ℝ) * log (log N)) =
            (1 - (8 : ℝ) / log (log N)) * log N + (1 / 500 : ℝ) * log (log N) := by
        simpa [add_assoc, add_left_comm, add_comm] using hrew
      rw [hrew'] at hadd
      simpa [add_assoc, add_left_comm, add_comm] using hadd
    exact (le_div_iff₀ (show 0 < log N ^ ((1 : ℝ) / 500) by positivity)).mpr hmain
  · refine le_trans (b := (7 : ℝ) / (log N ^ ((1 : ℝ) / 500))) ?_ ?_
    · refine (_root_.le_div_iff₀ (show 0 < log N ^ ((1 : ℝ) / 500) by positivity)).2 ?_
      rw [← Real.rpow_add hN8]
      have hpow : log N ^ (-(1 / 101 : ℝ) + (1 / 500 : ℝ)) ≤ (1 : ℝ) := by
        apply Real.rpow_le_one_of_one_le_of_nonpos hN2
        · norm_num
      linarith
    · rw [le_sub_iff_add_le]
      have hlogpow : log N ^ ((1 : ℝ) / 500) ≤ (N : ℝ) ^ ((1 : ℝ) / 500) := by
        exact Real.rpow_le_rpow (le_of_lt hN8) hN10 (by norm_num : 0 ≤ (1 : ℝ) / 500)
      have hNexp : (N : ℝ) ^ ((1 : ℝ) / 500) ≤ (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
        apply Real.rpow_le_rpow_of_exponent_le (le_of_lt hN5)
        have hrec : 1 / log (log N) ≤ (1 : ℝ) / 6 := by
          exact one_div_le_one_div_of_le (by norm_num : 0 < (6 : ℝ)) hN1
        nlinarith
      have hInv :
          1 / (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) ≤
            1 / (log N ^ ((1 : ℝ) / 500)) := by
        exact one_div_le_one_div_of_le (show 0 < log N ^ ((1 : ℝ) / 500) by positivity)
          (le_trans hlogpow hNexp)
      have hDne : log N ^ ((1 : ℝ) / 500) ≠ 0 := by positivity
      calc
        (7 : ℝ) / (log N ^ ((1 : ℝ) / 500)) + 1 / (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) ≤
            (7 : ℝ) / (log N ^ ((1 : ℝ) / 500)) + 1 / (log N ^ ((1 : ℝ) / 500)) := by
              exact add_le_add le_rfl hInv
        _ = (2 : ℝ) / (log N ^ ((1 : ℝ) / 500) / 4) := by
              field_simp [hDne]
              norm_num

lemma large_enough_Naux :
    ∀ c : ℝ, c > 0 → ∀ᶠ N : ℕ in atTop,
      let M := (N : ℝ) ^ (1 - (1 : ℝ) / log (log N))
      let L := M / (2 * log N ^ (1 / 100 : ℝ))
      let T := M / log N
      let ε := (N : ℝ) ^ (-(5 : ℝ) / log (log N))
      let ε' := (log N) ^ (-(1 / 100 : ℝ))
      let K := (N : ℝ) ^ (1 - (3 : ℝ) / log (log N))
      ε ≤ ε' →
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ ε' * M ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ L * K ^ 2 / (16 * N ^ 2 * log N ^ 2) ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ T * K ^ 2 / (N ^ 2 * log N) ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ c * M / (log N) ^ (1 / 500 : ℝ) ∧
        (log N) ^ (-(1 / 101 : ℝ)) ≤ (2 : ℝ) / ((log N) ^ (1 / 500 : ℝ) / 4) - 1 / M := by
  intro c hc
  have hlargeaux1 := large_enough_Naux1
  have hlargeaux2 := large_enough_Naux2 c hc
  filter_upwards
    [ tendsto_log_log_coe_at_top (eventually_ge_atTop (6 : ℝ))
    , tendsto_log_coe_at_top.eventually (eventually_ge_atTop ((128 : ℝ) ^ (500 : ℝ)))
    , eventually_ge_atTop (64 : ℕ)
    , hlargeaux2
    , hlargeaux1 ] with
    N hN1 hN2 hN3 hotheraux hnec
  dsimp at hN1 hN2
  have hN4 : 1 < log (log N) := by
    refine lt_of_lt_of_le ?_ hN1
    norm_num1
  have hN5 : (1 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num1 : 1 < 64) hN3)
  have hN6 : (0 : ℝ) < N := by
    linarith
  have hN7 : 0 < log (log N) := by
    linarith
  have hN8 : 0 < log N := by
    have hpowpos : 0 < (128 : ℝ) ^ (500 : ℝ) := by
      positivity
    exact lt_of_lt_of_le hpowpos hN2
  dsimp
  intro hT3
  constructor
  · rw [← div_le_iff₀ (show 0 < (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) by positivity)]
    rw [← Real.rpow_sub hN6]
    have hexp :
        (1 - (8 : ℝ) / log (log N)) - (1 - (1 : ℝ) / log (log N)) =
          (-7 : ℝ) / log (log N) := by
      field_simp [hN7.ne']
      ring
    rw [hexp]
    refine le_trans ?_ hT3
    refine Real.rpow_le_rpow_of_exponent_le (le_of_lt hN5) ?_
    exact (div_le_div_iff_of_pos_right hN7).2 (by norm_num)
  constructor
  · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hnec
  constructor
  · refine le_trans
        (b :=
          (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ)) *
            ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 /
              (16 * (N : ℝ) ^ 2 * log N ^ 2)) ?_ ?_
    · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hnec
    · have hstep :
          (((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (2 * log N ^ (1 / 100 : ℝ))) *
              ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2) /
            (16 * (N : ℝ) ^ 2 * log N ^ 2) ≤
            (((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / log N) *
              ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2) /
            ((N : ℝ) ^ 2 * log N) := by
        rw [div_le_div_iff₀
          (show 0 < 16 * (N : ℝ) ^ 2 * log N ^ 2 by positivity)
          (show 0 < (N : ℝ) ^ 2 * log N by positivity)]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have hEq1 :
            (N : ℝ) ^ (1 - (1 : ℝ) * (log (log N))⁻¹) *
                (2 * log N ^ (1 / 100 : ℝ))⁻¹ *
                ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 *
                ((N : ℝ) ^ 2 * log N) =
            (((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) *
                ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 *
                (N : ℝ) ^ 2) *
              ((2 * log N ^ (1 / 100 : ℝ))⁻¹ * log N) := by
          ring_nf
        have hEq2 :
            (N : ℝ) ^ (1 - (1 : ℝ) * (log (log N))⁻¹) / log N *
                ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 *
                (16 * (N : ℝ) ^ 2 * log N ^ 2) =
            (((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) *
                ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 *
                (N : ℝ) ^ 2) *
              ((log N)⁻¹ * 16 * log N ^ 2) := by
          rw [div_eq_mul_inv]
          ring_nf
        rw [hEq1, hEq2]
        have hcommon_nonneg :
            0 ≤
              ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) *
                ((N : ℝ) ^ (1 - (3 : ℝ) / log (log N))) ^ 2 *
                  (N : ℝ) ^ 2 := by
          positivity
        have hscalar :
            (2 * log N ^ (1 / 100 : ℝ))⁻¹ * log N ≤ (log N)⁻¹ * 16 * log N ^ 2 := by
          have h128 : (1 : ℝ) ≤ (128 : ℝ) ^ (500 : ℝ) := by
            apply one_le_rpow
            · norm_num
            · norm_num
          have hlogpow_ge_one : 1 ≤ log N ^ (1 / 100 : ℝ) := by
            apply one_le_rpow
            · exact le_trans h128 hN2
            · norm_num
          have hfac : 1 ≤ 2 * log N ^ (1 / 100 : ℝ) := by
            nlinarith
          have hleft :
              (2 * log N ^ (1 / 100 : ℝ))⁻¹ * log N = log N / (2 * log N ^ (1 / 100 : ℝ)) := by
            calc
              (2 * log N ^ (1 / 100 : ℝ))⁻¹ * log N =
                  log N * (2 * log N ^ (1 / 100 : ℝ))⁻¹ := by ac_rfl
              _ = log N / (2 * log N ^ (1 / 100 : ℝ)) := by
                  symm
                  rw [div_eq_mul_inv]
          have hright :
              (log N)⁻¹ * 16 * log N ^ 2 = (16 * log N ^ 2) / log N := by
            calc
              (log N)⁻¹ * 16 * log N ^ 2 = 16 * log N ^ 2 * (log N)⁻¹ := by ac_rfl
              _ = (16 * log N ^ 2) / log N := by rw [div_eq_mul_inv]
          rw [hleft, hright]
          refine (div_le_div_iff₀ (show 0 < 2 * log N ^ (1 / 100 : ℝ) by positivity) hN8).2 ?_
          calc
            log N * log N = log N ^ 2 := by ring
            _ ≤ 16 * log N ^ 2 := by
              simpa [one_mul] using
                mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 16 by norm_num)
                  (show 0 ≤ log N ^ 2 by positivity)
            _ ≤ (16 * log N ^ 2) * (2 * log N ^ (1 / 100 : ℝ)) := by
              simpa [mul_one] using
                mul_le_mul_of_nonneg_left hfac (show 0 ≤ 16 * log N ^ 2 by positivity)
        exact mul_le_mul_of_nonneg_left hscalar hcommon_nonneg
      simpa using hstep
  · exact hotheraux

private lemma large_enough_N_hTp
    (N : ℕ)
    (hN1 : 6 ≤ log (log N))
    (hN2 : (192 : ℝ) ^ (500 : ℝ) ≤ log N)
    (hN5 : (1 : ℝ) < N)
    (hN6 : 0 < (N : ℝ))
    (_hN7 : 0 < log (log N))
    (hN8 : 0 < log N) :
    192 * (log N) ^ (1 / 500 : ℝ) < (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
  have h500 : (0 : ℝ) < 500 := by norm_num
  have h5002 : (0 : ℝ) < 500 / 2 := by norm_num
  have hlog_nonneg : 0 ≤ log N := le_of_lt hN8
  have haux :
      192 * (log N) ^ (1 / 500 : ℝ) ≤
        (log N) ^ (1 / 500 : ℝ) * (log N) ^ (1 / 500 : ℝ) := by
    have h192 : (192 : ℝ) ≤ (log N) ^ (1 / 500 : ℝ) := by
      rw [← Real.rpow_le_rpow_iff (show 0 ≤ (192 : ℝ) by norm_num)
        (show 0 ≤ (log N) ^ (1 / 500 : ℝ) by positivity) h500]
      rw [← Real.rpow_mul hlog_nonneg, one_div_mul_cancel (show (500 : ℝ) ≠ 0 by norm_num),
        Real.rpow_one]
      exact hN2
    exact mul_le_mul_of_nonneg_right h192 (show 0 ≤ (log N) ^ (1 / 500 : ℝ) by positivity)
  refine lt_of_le_of_lt haux ?_
  rw [← Real.rpow_add hN8]
  refine (Real.rpow_lt_rpow_iff
    (show 0 ≤ (log N) ^ (1 / 500 + 1 / 500 : ℝ) by positivity)
    (show 0 ≤ (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) by positivity) h5002).1 ?_
  rw [← Real.rpow_mul hlog_nonneg]
  norm_num
  refine lt_of_le_of_lt (Real.log_le_sub_one_of_pos hN6) ?_
  refine lt_of_lt_of_le (sub_one_lt (N : ℝ)) ?_
  have hrightEq :
      ((N : ℝ) ^ (1 - (log (log N))⁻¹)) ^ (250 : ℕ) =
        (N : ℝ) ^ ((1 - (log (log N))⁻¹) * (250 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hN6)]
    norm_num
  have hdiv : (log (log N))⁻¹ ≤ 1 / 6 := by
    have h6 : (0 : ℝ) < 6 := by linarith
    simpa [one_div] using
      (one_div_le_one_div_of_le h6 hN1)
  have hpow :
      (N : ℝ) ≤ (N : ℝ) ^ ((1 - (log (log N))⁻¹) * (250 : ℝ)) := by
    have hpow' : (N : ℝ) ^ (1 : ℝ) ≤ (N : ℝ) ^ ((1 - (log (log N))⁻¹) * (250 : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le (le_of_lt hN5) ?_
      nlinarith
    simpa using hpow'
  exact le_trans hpow hrightEq.ge

private lemma large_enough_N_hT1
    (N : ℕ)
    (hN8 : 0 < log N)
    (hN10 : log (log N) ≤ (2 / 3 : ℝ) * (log N) ^ (3 / 500 : ℝ)) :
    3 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N) ≤ 2 / ((log N) ^ (1 / 500 : ℝ)) ^ 2 := by
  have hstep :
      3 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N) ≤
        3 * (log N) ^ (-(1 / 100 : ℝ)) * ((2 / 3 : ℝ) * (log N) ^ (3 / 500 : ℝ)) := by
    gcongr
  calc
    3 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N) ≤
        3 * (log N) ^ (-(1 / 100 : ℝ)) * ((2 / 3 : ℝ) * (log N) ^ (3 / 500 : ℝ)) := hstep
    _ = 2 * ((log N) ^ (-(1 / 100 : ℝ)) * (log N) ^ (3 / 500 : ℝ)) := by ring
    _ = 2 * (log N) ^ ((-(1 / 100 : ℝ)) + 3 / 500) := by
      rw [← Real.rpow_add hN8]
    _ = 2 * (log N) ^ (-(1 / 250 : ℝ)) := by
      congr 2
      norm_num
    _ = 2 / ((log N) ^ (1 / 500 : ℝ)) ^ 2 := by
      rw [div_eq_mul_inv]
      congr 1
      calc
        (log N) ^ (-(1 / 250 : ℝ)) = ((log N) ^ (1 / 250 : ℝ))⁻¹ := by
          exact Real.rpow_neg hN8.le (1 / 250 : ℝ)
        _ = (((log N) ^ (1 / 500 : ℝ)) ^ 2)⁻¹ := by
          congr 1
          calc
            (log N) ^ (1 / 250 : ℝ) = (log N) ^ ((1 / 500 : ℝ) + 1 / 500) := by
              congr 2
              norm_num
            _ = ((log N) ^ (1 / 500 : ℝ)) ^ 2 := by
              rw [pow_two, ← Real.rpow_add hN8]

private lemma large_enough_N_hT2
    (N : ℕ)
    (hN8 : 0 < log N)
    (hN11 : 2 * log (log N) ≤ (log N) ^ (1 / 200 : ℝ)) :
    2 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N) ≤ (log N) ^ (-(1 / 200 : ℝ)) := by
  have hpow_nonneg : 0 ≤ (log N) ^ (-(1 / 100 : ℝ)) := by positivity
  have hstep :
      2 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N) ≤
        (log N) ^ (1 / 200 : ℝ) * (log N) ^ (-(1 / 100 : ℝ)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right hN11 hpow_nonneg
  refine hstep.trans ?_
  rw [← Real.rpow_add hN8]
  norm_num

private lemma large_enough_N_hT3
    (N : ℕ)
    (hN2 : (192 : ℝ) ^ (500 : ℝ) ≤ log N)
    (hN6 : 0 < (N : ℝ))
    (hN7 : 0 < log (log N))
    (hN8 : 0 < log N)
    (hN10 : log (log N) ≤ (2 / 3 : ℝ) * (log N) ^ (3 / 500 : ℝ)) :
    (N : ℝ) ^ (-(5 : ℝ) / log (log N)) ≤ (log N) ^ (-(1 / 100 : ℝ)) := by
  have hlog_ge_one : (1 : ℝ) ≤ log N := by
    refine le_trans ?_ hN2
    apply one_le_rpow
    · norm_num
    · norm_num
  have hsq :
      log (log N) ^ (2 : ℕ) ≤ 500 * log N := by
    calc
      log (log N) ^ (2 : ℕ) ≤ (((2 / 3 : ℝ) * (log N) ^ (3 / 500 : ℝ)) ^ (2 : ℕ)) := by
        nlinarith [hN10]
      _ = (4 / 9 : ℝ) * ((log N) ^ (3 / 500 : ℝ) * (log N) ^ (3 / 500 : ℝ)) := by ring
      _ = (4 / 9 : ℝ) * (log N) ^ ((3 / 500 : ℝ) + 3 / 500) := by
        rw [← Real.rpow_add hN8]
      _ = (4 / 9 : ℝ) * (log N) ^ (3 / 250 : ℝ) := by
        congr 2
        norm_num
      _ ≤ (4 / 9 : ℝ) * log N := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hexp : (3 / 250 : ℝ) ≤ 1 := by norm_num
        simpa using Real.rpow_le_rpow_of_exponent_le hlog_ge_one hexp
      _ ≤ 500 * log N := by
        exact mul_le_mul_of_nonneg_right (by norm_num : (4 / 9 : ℝ) ≤ 500) (le_of_lt hN8)
  have hlogineq : (1 / 100 : ℝ) * log (log N) ≤ 5 * log N / log (log N) := by
    rw [le_div_iff₀ hN7]
    nlinarith [hsq]
  rw [← Real.log_le_log_iff (show 0 < (N : ℝ) ^ (-(5 : ℝ) / log (log N)) by positivity)
    (show 0 < (log N) ^ (-(1 / 100 : ℝ)) by positivity)]
  rw [Real.log_rpow hN6, Real.log_rpow hN8]
  have hlogineq' : (1 / 100 : ℝ) * log (log N) ≤ (5 / log (log N)) * log N := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hlogineq
  have hneg :
      -((5 / log (log N)) * log N) ≤ -((1 / 100 : ℝ) * log (log N)) := by
    linarith
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hneg

private lemma large_enough_N_hMε
    (N : ℕ)
    (hN1 : 6 ≤ log (log N))
    (hN5 : (1 : ℝ) < N)
    (hN6 : 0 < (N : ℝ))
    (hN7 : 0 < log (log N)) :
    1 / ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) <
      (N : ℝ) ^ (-(5 : ℝ) / log (log N)) * log (log N) := by
  have hN4 : 1 < log (log N) := by
    linarith
  have hexp_nonneg : 0 ≤ (1 : ℝ) - (6 : ℝ) / log (log N) := by
    rw [sub_nonneg, div_le_one hN7]
    simpa using hN1
  have hpow_ge_one : 1 ≤ (N : ℝ) ^ ((1 : ℝ) - (6 : ℝ) / log (log N)) := by
    refine one_le_rpow (le_of_lt hN5) hexp_nonneg
  have hpow_nonneg : 0 ≤ (N : ℝ) ^ ((1 : ℝ) - (6 : ℝ) / log (log N)) := by
    positivity
  have hmain : 1 < log (log N) * (N : ℝ) ^ ((1 : ℝ) - (6 : ℝ) / log (log N)) := by
    nlinarith
  have hexp :
      (-(5 : ℝ) / log (log N)) + (1 - (1 : ℝ) / log (log N)) =
        (1 : ℝ) - (6 : ℝ) / log (log N) := by
    ring
  rw [one_div, inv_lt_iff_one_lt_mul₀ (Real.rpow_pos_of_pos hN6 _)]
  rw [mul_assoc]
  rw [mul_left_comm ((N : ℝ) ^ (-(5 : ℝ) / log (log N))) (log (log N))
    ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)))]
  rw [← mul_assoc]
  calc
    1 < log (log N) * (N : ℝ) ^ ((1 : ℝ) - (6 : ℝ) / log (log N)) := hmain
    _ = log (log N) *
          ((N : ℝ) ^ (-(5 : ℝ) / log (log N)) *
            (N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) := by
          rw [← Real.rpow_add hN6, hexp]
    _ = log (log N) * (N : ℝ) ^ (-(5 : ℝ) / log (log N)) *
          (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
          rw [mul_assoc]

private lemma large_enough_N_hKlower
    (N : ℕ)
    (hN1 : 6 ≤ log (log N))
    (hN3 : 64 ≤ N)
    (hN5 : (1 : ℝ) < N)
    (hN6 : 0 < (N : ℝ))
    (hN7 : 0 < log (log N))
    (hN8 : 0 < log N) :
    8 ≤ (N : ℝ) ^ (1 - (3 : ℝ) / log (log N)) := by
  have _ : 0 < log N := hN8
  have hhalf : (8 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_le_rpow_iff (show 0 ≤ (8 : ℝ) by norm_num)
      (Real.rpow_nonneg (le_of_lt hN6) ((1 : ℝ) / 2)) (show (0 : ℝ) < 2 by norm_num)]
    rw [← Real.rpow_mul (le_of_lt hN6)]
    norm_num
    exact_mod_cast hN3
  have hexp : (1 : ℝ) / 2 ≤ 1 - (3 : ℝ) / log (log N) := by
    have hdiv : (3 : ℝ) / log (log N) ≤ (1 : ℝ) / 2 := by
      rw [div_le_iff₀ hN7]
      nlinarith
    nlinarith
  exact hhalf.trans <| Real.rpow_le_rpow_of_exponent_le (le_of_lt hN5) hexp

private lemma large_enough_N_hKM
    (N : ℕ)
    (hN5 : (1 : ℝ) < N)
    (hN7 : 0 < log (log N)) :
    (N : ℝ) ^ (1 - (3 : ℝ) / log (log N)) < (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
  apply Real.rpow_lt_rpow_of_exponent_lt hN5
  have hdiv : (1 : ℝ) / log (log N) < (3 : ℝ) / log (log N) := by
    rw [div_lt_div_iff₀ hN7 hN7]
    nlinarith
  nlinarith

private lemma large_enough_N_hsum
    (N : ℕ)
    (hN8 : 0 < log N)
    (hN9 : 24 * log (log N) ≤ (log N) ^ (1 / 125 : ℝ))
    (hT : 4 * (log N) ^ (1 / 500 : ℝ) < (N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) :
    3 * (2 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N)) +
        1 / ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) ≤
      1 / (2 * (log N) ^ (1 / 500 : ℝ)) := by
  have hquarter_pos : 0 < 4 * (log N) ^ (1 / 500 : ℝ) := by positivity
  have hfirst :
      3 * (2 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N)) ≤
        1 / (4 * (log N) ^ (1 / 500 : ℝ)) := by
    rw [_root_.le_div_iff₀ hquarter_pos]
    calc
      3 * (2 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N)) *
          (4 * (log N) ^ (1 / 500 : ℝ)) =
        24 * ((log N) ^ (-(1 / 100 : ℝ)) * (log N) ^ (1 / 500 : ℝ)) * log (log N) := by
          ring
      _ = 24 * (log N) ^ ((-(1 / 100 : ℝ)) + 1 / 500) * log (log N) := by
        rw [← Real.rpow_add hN8]
      _ = 24 * (log N) ^ (-(1 / 125 : ℝ)) * log (log N) := by
        congr 2
        norm_num
      _ = (24 * log (log N)) / (log N) ^ (1 / 125 : ℝ) := by
        rw [div_eq_mul_inv, Real.rpow_neg hN8.le]
        ring
      _ ≤ 1 := by
        rw [div_le_iff₀ (show 0 < (log N) ^ (1 / 125 : ℝ) by positivity)]
        simpa [one_mul] using hN9
  have hsecond :
      1 / ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) ≤
        1 / (4 * (log N) ^ (1 / 500 : ℝ)) := by
    exact one_div_le_one_div_of_le hquarter_pos hT.le
  calc
    3 * (2 * (log N) ^ (-(1 / 100 : ℝ)) * log (log N)) +
        1 / ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) ≤
      1 / (4 * (log N) ^ (1 / 500 : ℝ)) + 1 / (4 * (log N) ^ (1 / 500 : ℝ)) := by
        exact add_le_add hfirst hsecond
    _ = 1 / (2 * (log N) ^ (1 / 500 : ℝ)) := by
      have hPne : (log N) ^ (1 / 500 : ℝ) ≠ 0 := by positivity
      field_simp [hPne]
      norm_num

private lemma large_enough_N_honeOverM
    (N : ℕ)
    (hN1 : 6 ≤ log (log N))
    (hN5 : (1 : ℝ) < N)
    (hN8 : 0 < log N)
    (_hN9 : 24 * log (log N) ≤ (log N) ^ (1 / 125 : ℝ)) :
    1 / ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N))) <
      (log N) ^ (-(1 / 100 : ℝ)) * log (log N) := by
  have hN6 : 0 < (N : ℝ) := by
    linarith
  have hN7 : 0 < log (log N) := by
    linarith
  have hN4 : 1 < log (log N) := by
    linarith
  have hTq :
      (log N) ^ (1 / 100 : ℝ) <
        (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
    have h100 : (0 : ℝ) < 100 := by
      norm_num
    refine (Real.rpow_lt_rpow_iff
      (show 0 ≤ (log N) ^ (1 / 100 : ℝ) by positivity)
      (show 0 ≤ (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) by positivity) h100).1 ?_
    rw [← Real.rpow_mul hN8.le]
    norm_num
    refine lt_of_le_of_lt (Real.log_le_sub_one_of_pos hN6) ?_
    refine lt_of_lt_of_le (sub_one_lt (N : ℝ)) ?_
    have hdiv : (1 : ℝ) / log (log N) ≤ (1 : ℝ) / 6 := by
      have h6 : (0 : ℝ) < 6 := by
        norm_num
      exact one_div_le_one_div_of_le h6 hN1
    have hbound : (log (log N))⁻¹ ≤ (99 : ℝ) / 100 := by
      have haux : (1 : ℝ) / 6 ≤ (99 : ℝ) / 100 := by
        norm_num
      have hdiv' : (log (log N))⁻¹ ≤ (1 : ℝ) / 6 := by
        simpa [one_div] using hdiv
      exact hdiv'.trans haux
    have hexp : (1 : ℝ) ≤ (1 - (log (log N))⁻¹) * (100 : ℝ) := by
      nlinarith
    have hpow :
        (N : ℝ) ≤ (N : ℝ) ^ ((1 - (log (log N))⁻¹) * (100 : ℝ)) := by
      have hpow' :
          (N : ℝ) ^ (1 : ℝ) ≤ (N : ℝ) ^ ((1 - (log (log N))⁻¹) * (100 : ℝ)) := by
        exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hN5) hexp
      simpa using hpow'
    exact le_trans hpow <| by
      apply le_of_eq
      symm
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hN6)]
      congr 2
  have hratio :
      1 <
        (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (log N) ^ (1 / 100 : ℝ) := by
    exact (one_lt_div_iff).2 <| Or.inl ⟨show 0 < (log N) ^ (1 / 100 : ℝ) by positivity, hTq⟩
  rw [Real.rpow_neg hN8.le, one_div]
  rw [inv_lt_iff_one_lt_mul₀ (Real.rpow_pos_of_pos hN6 _)]
  calc
    1 <
        log (log N) *
          ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) / (log N) ^ (1 / 100 : ℝ)) :=
      one_lt_mul_of_lt_of_le hN4 hratio.le
    _ = log (log N) *
          ((N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) *
            ((log N) ^ (1 / 100 : ℝ))⁻¹) := by
          rw [div_eq_mul_inv]
    _ = ((log N) ^ (1 / 100 : ℝ))⁻¹ * log (log N) *
          (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by
          ac_rfl

lemma large_enough_N :
    ∀ c : ℝ, c > 0 → ∀ᶠ N : ℕ in atTop,
      let M := (N : ℝ) ^ (1 - (1 : ℝ) / log (log N))
      let L := M / (2 * log N ^ (1 / 100 : ℝ))
      let T := M / log N
      let ε := (N : ℝ) ^ (-(5 : ℝ) / log (log N))
      let ε' := (log N) ^ (-(1 / 100 : ℝ))
      let K := (N : ℝ) ^ (1 - (3 : ℝ) / log (log N))
      1 / M < ε * log (log N) ∧ 0 < ε ∧ (N : ℝ) ≤ M ^ (2 : ℝ) ∧ M < N ∧ 0 < M ∧
        (0 : ℝ) < log N ∧ 8 ≤ K ∧ K < M ∧ (log N) ^ (1 / 500 : ℝ) < 2 * M ∧
        2 * ε * log (log N) ≤ (log N) ^ (-(1 / 200 : ℝ)) ∧
        3 * ε * log (log N) ≤ 2 / ((log N) ^ (1 / 500 : ℝ)) ^ 2 ∧
        3 * (2 * ε' * log (log N)) + 1 / M ≤ 1 / (2 * (log N) ^ (1 / 500 : ℝ)) ∧
        (log N) ^ (1 / 500 : ℝ) ≤ M / 192 ∧ 1 / M < ε' * log (log N) ∧
        3 * ε' * log (log N) ≤ 2 / ((log N) ^ (1 / 500 : ℝ)) ^ 2 ∧
        2 * ε' * log (log N) ≤ (log N) ^ (-(1 / 200 : ℝ)) ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ ε' * M ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ L * K ^ 2 / (16 * N ^ 2 * log N ^ 2) ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ T * K ^ 2 / (N ^ 2 * log N) ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ c * M / (log N) ^ (1 / 500 : ℝ) ∧
        (log N) ^ (-(1 / 101 : ℝ)) ≤ (2 : ℝ) / ((log N) ^ (1 / 500 : ℝ) / 4) - 1 / M := by
  intro c hc
  have hlargeaux := large_enough_Naux c hc
  have haux4 :
      ∀ᶠ x : ℝ in atTop, ‖log x‖ ≤ (1 / 24 : ℝ) * ‖x ^ (1 / 125 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (show 0 < (1 / 125 : ℝ) by norm_num)).bound
      (show 0 < (1 / 24 : ℝ) by norm_num)
  have haux5 :
      ∀ᶠ x : ℝ in atTop, ‖log x‖ ≤ (2 / 3 : ℝ) * ‖x ^ (3 / 500 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (show 0 < (3 / 500 : ℝ) by norm_num)).bound
      (show 0 < (2 / 3 : ℝ) by norm_num)
  have haux6 :
      ∀ᶠ x : ℝ in atTop, ‖log x‖ ≤ (1 / 2 : ℝ) * ‖x ^ (1 / 200 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (show 0 < (1 / 200 : ℝ) by norm_num)).bound
      (show 0 < (1 / 2 : ℝ) by norm_num)
  filter_upwards
    [ tendsto_log_log_coe_at_top (eventually_ge_atTop (6 : ℝ))
    , tendsto_log_coe_at_top.eventually (eventually_ge_atTop ((192 : ℝ) ^ (500 : ℝ)))
    , eventually_ge_atTop (64 : ℕ)
    , tendsto_log_coe_at_top.eventually haux4
    , tendsto_log_coe_at_top.eventually haux5
    , tendsto_log_coe_at_top.eventually haux6
    , hlargeaux ] with
    N hN1 hN2 hN3 hN3new hN3new2 hN3new3 hotheraux
  dsimp at hN1 hN2
  have hN4 : 1 < log (log N) := by
    linarith
  have hN5 : (1 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 64) hN3)
  have hN6 : (0 : ℝ) < N := by
    linarith
  have hN7 : 0 < log (log N) := by
    linarith
  have hN8 : 0 < log N := by
    have hpowpos : 0 < (192 : ℝ) ^ (500 : ℝ) := by
      positivity
    exact lt_of_lt_of_le hpowpos hN2
  have hbound1 :
      log (log N) ≤ (1 / 24 : ℝ) * (log N) ^ (1 / 125 : ℝ) := by
    have habs :
        log (log N) ≤ (1 / 24 : ℝ) * |(log N) ^ (1 / 125 : ℝ)| := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hN7.le] using hN3new
    rw [abs_of_nonneg (show 0 ≤ (log N) ^ (1 / 125 : ℝ) by positivity)] at habs
    exact habs
  have hN9 : 24 * log (log N) ≤ (log N) ^ (1 / 125 : ℝ) := by
    nlinarith
  have hN10 :
      log (log N) ≤ (2 / 3 : ℝ) * (log N) ^ (3 / 500 : ℝ) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hN7.le,
      abs_of_nonneg (show 0 ≤ (log N) ^ (3 / 500 : ℝ) by positivity)] using hN3new2
  have hN11 : 2 * log (log N) ≤ (log N) ^ (1 / 200 : ℝ) := by
    have hbound3 :
        log (log N) ≤ (1 / 2 : ℝ) * (log N) ^ (1 / 200 : ℝ) := by
      have habs :
          log (log N) ≤ (1 / 2 : ℝ) * |(log N) ^ (1 / 200 : ℝ)| := by
        simpa [Real.norm_eq_abs, abs_of_nonneg hN7.le] using hN3new3
      rw [abs_of_nonneg (show 0 ≤ (log N) ^ (1 / 200 : ℝ) by positivity)] at habs
      exact habs
    nlinarith
  let M : ℝ := (N : ℝ) ^ (1 - (1 : ℝ) / log (log N))
  let L : ℝ := M / (2 * log N ^ (1 / 100 : ℝ))
  let T : ℝ := M / log N
  let ε : ℝ := (N : ℝ) ^ (-(5 : ℝ) / log (log N))
  let ε' : ℝ := (log N) ^ (-(1 / 100 : ℝ))
  let K : ℝ := (N : ℝ) ^ (1 - (3 : ℝ) / log (log N))
  let P : ℝ := (log N) ^ (1 / 500 : ℝ)
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  have hε'pos : 0 < ε' := by
    dsimp [ε']
    positivity
  have hPpos : 0 < P := by
    dsimp [P]
    positivity
  have hotheraux' :
      ε ≤ ε' →
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ ε' * M ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ L * K ^ 2 / (16 * N ^ 2 * log N ^ 2) ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ T * K ^ 2 / (N ^ 2 * log N) ∧
        (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ c * M / P ∧
        (log N) ^ (-(1 / 101 : ℝ)) ≤ (2 : ℝ) / (P / 4) - 1 / M := by
    simpa [M, L, T, ε, ε', K, P] using hotheraux
  have hTp : 192 * P < M := by
    simpa [M, P] using large_enough_N_hTp N hN1 hN2 hN5 hN6 hN7 hN8
  have hT : 4 * P < M := by
    have hstep : 4 * P ≤ 192 * P := by
      nlinarith [show 0 ≤ P by positivity]
    exact lt_of_le_of_lt hstep hTp
  have hT' : P < M := by
    have hstep : P ≤ 4 * P := by
      nlinarith [show 0 ≤ P by positivity]
    exact lt_of_le_of_lt hstep hT
  have hT1 : 3 * ε' * log (log N) ≤ 2 / P ^ 2 := by
    simpa [ε', P] using large_enough_N_hT1 N hN8 hN10
  have hT2 : 2 * ε' * log (log N) ≤ (log N) ^ (-(1 / 200 : ℝ)) := by
    simpa [ε'] using large_enough_N_hT2 N hN8 hN11
  have hT3 : ε ≤ ε' := by
    simpa [ε, ε'] using large_enough_N_hT3 N hN2 hN6 hN7 hN8 hN10
  have hKlower : 8 ≤ K := by
    simpa [K] using large_enough_N_hKlower N hN1 hN3 hN5 hN6 hN7 hN8
  have hsum :
      3 * (2 * ε' * log (log N)) + 1 / M ≤ 1 / (2 * P) := by
    simpa [M, ε', P] using large_enough_N_hsum N hN8 hN9 (by simpa [M, P] using hT)
  have honeOverM : 1 / M < ε' * log (log N) := by
    simpa [M, ε'] using large_enough_N_honeOverM N hN1 hN5 hN8 hN9
  change
    1 / M < ε * log (log N) ∧ 0 < ε ∧ (N : ℝ) ≤ M ^ (2 : ℝ) ∧ M < N ∧ 0 < M ∧
      (0 : ℝ) < log N ∧ 8 ≤ K ∧ K < M ∧ P < 2 * M ∧
      2 * ε * log (log N) ≤ (log N) ^ (-(1 / 200 : ℝ)) ∧
      3 * ε * log (log N) ≤ 2 / P ^ 2 ∧
      3 * (2 * ε' * log (log N)) + 1 / M ≤ 1 / (2 * P) ∧
      P ≤ M / 192 ∧ 1 / M < ε' * log (log N) ∧
      3 * ε' * log (log N) ≤ 2 / P ^ 2 ∧
      2 * ε' * log (log N) ≤ (log N) ^ (-(1 / 200 : ℝ)) ∧
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ ε' * M ∧
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ L * K ^ 2 / (16 * N ^ 2 * log N ^ 2) ∧
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ T * K ^ 2 / (N ^ 2 * log N) ∧
      (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ c * M / P ∧
      (log N) ^ (-(1 / 101 : ℝ)) ≤ (2 : ℝ) / (P / 4) - 1 / M
  constructor
  · simpa [M, ε] using large_enough_N_hMε N hN1 hN5 hN6 hN7
  constructor
  · exact hεpos
  constructor
  · have hrec : (1 : ℝ) / log (log N) ≤ (1 : ℝ) / 2 := by
      exact
        one_div_le_one_div_of_le
          (by norm_num : 0 < (2 : ℝ))
          (by linarith : (2 : ℝ) ≤ log (log N))
    have hexp : (1 : ℝ) ≤ (1 - (1 : ℝ) / log (log N)) * (2 : ℝ) := by
      nlinarith
    calc
      (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (N : ℝ) ^ ((1 - (1 : ℝ) / log (log N)) * (2 : ℝ)) := by
        exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hN5) hexp
      _ = M ^ (2 : ℝ) := by
        dsimp [M]
        rw [← Real.rpow_mul (le_of_lt hN6)]
  constructor
  · calc
      M = (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) := by rfl
      _ < (N : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt hN5
        have hdivpos : 0 < (1 : ℝ) / log (log N) := by positivity
        nlinarith
      _ = N := by rw [Real.rpow_one]
  constructor
  · exact hMpos
  constructor
  · exact hN8
  constructor
  · exact hKlower
  constructor
  · simpa [M, K] using large_enough_N_hKM N hN5 hN7
  constructor
  · have hstep : M ≤ 2 * M := by
      nlinarith [hMpos]
    exact lt_of_lt_of_le hT' hstep
  constructor
  · have hmul1 : 2 * ε ≤ 2 * ε' := by
      exact mul_le_mul_of_nonneg_left hT3 (show 0 ≤ (2 : ℝ) by norm_num)
    have hmul2 : (2 * ε) * log (log N) ≤ (2 * ε') * log (log N) := by
      exact mul_le_mul_of_nonneg_right hmul1 hN7.le
    refine le_trans ?_ hT2
    simpa [mul_assoc] using hmul2
  constructor
  · have hmul1 : 3 * ε ≤ 3 * ε' := by
      exact mul_le_mul_of_nonneg_left hT3 (show 0 ≤ (3 : ℝ) by norm_num)
    have hmul2 : (3 * ε) * log (log N) ≤ (3 * ε') * log (log N) := by
      exact mul_le_mul_of_nonneg_right hmul1 hN7.le
    refine le_trans ?_ hT1
    simpa [mul_assoc] using hmul2
  constructor
  · exact hsum
  constructor
  · exact le_of_lt <| (_root_.lt_div_iff₀ (show 0 < (192 : ℝ) by norm_num)).2 <| by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hTp
  constructor
  · exact honeOverM
  constructor
  · exact hT1
  constructor
  · exact hT2
  · exact hotheraux' hT3

private lemma technical_prop_hdiv_aux
    (y z : ℝ) (n d₁ d₂ : ℕ)
    (hd₁ : d₁ ∣ n)
    (hyd₁ : y ≤ d₁)
    (hd₁₂ : 4 * d₁ ≤ d₂)
    (hd₂z : (d₂ : ℝ) ≤ z) :
    ∃ d : ℕ, y ≤ d ∧ ((d : ℝ) ≤ z / 4) ∧ d ∣ n := by
  refine ⟨d₁, hyd₁, ?_, hd₁⟩
  have hd₁₂' : (4 : ℝ) * d₁ ≤ d₂ := by
    exact_mod_cast hd₁₂
  nlinarith

private lemma technical_prop_hrecB
    (N : ℕ) (M ε' y z : ℝ) (A' B : Finset ℕ) (d : ℕ)
    (h1y : 1 ≤ y)
    (hz_pos : 0 < z)
    (hzN : z ≤ (log N) ^ (1 / 500 : ℝ))
    (hε'M :
      3 * (2 * ε' * log (log N)) + 1 / M ≤ 1 / (2 * ((log N) ^ (1 / 500 : ℝ))))
    (hrecB : rec_sum A' ≤ 3 * rec_sum B)
    (hdy : y ≤ d)
    (hdz : (d : ℝ) ≤ z / 4)
    (htechrec : (2 : ℝ) / d - 1 / M ≤ rec_sum A') :
    2 / ((4 : ℝ) * d) + 2 * ε' * log (log N) ≤ rec_sum B := by
  have hd_pos : 0 < (d : ℝ) := by
    linarith
  have hdz' : (d : ℝ) ≤ z := by
    nlinarith [hdz, hz_pos]
  have hsmall : 3 * (2 * ε' * log (log N)) + 1 / M ≤ 1 / (2 * d) := by
    calc
      3 * (2 * ε' * log (log N)) + 1 / M ≤
          1 / (2 * ((log N) ^ (1 / 500 : ℝ))) := hε'M
      _ ≤ 1 / (2 * z) := by
        apply one_div_le_one_div_of_le
        · positivity
        · nlinarith [hzN]
      _ ≤ 1 / (2 * d) := by
        apply one_div_le_one_div_of_le
        · nlinarith [hd_pos]
        · nlinarith [hdz']
  have hhalfEq : (1 / (2 * d) : ℝ) = ((1 / 2 : ℝ) / d) := by
    field_simp [hd_pos.ne']
  have hadd :
      (3 / 2 : ℝ) / d + ((1 / 2 : ℝ) / d) = (2 : ℝ) / d := by
    field_simp [hd_pos.ne']
    ring
  have hsmall' :
      3 * (2 * ε' * log (log N)) + 1 / M ≤ ((1 / 2 : ℝ) / d) := by
    rw [← hhalfEq]
    exact hsmall
  have hbound :
      (3 / 2 : ℝ) / d + (3 * (2 * ε' * log (log N)) + 1 / M) ≤ (2 : ℝ) / d := by
    calc
      (3 / 2 : ℝ) / d + (3 * (2 * ε' * log (log N)) + 1 / M) ≤
          (3 / 2 : ℝ) / d + ((1 / 2 : ℝ) / d) := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_left hsmall' ((3 / 2 : ℝ) / d)
      _ = (2 : ℝ) / d := hadd
  have hpre :
      (3 / 2 : ℝ) / d + 3 * (2 * ε' * log (log N)) ≤ rec_sum A' := by
    linarith
  have haux : (3 : ℝ) * (2 / ((4 : ℝ) * d)) = ((3 / 2 : ℝ) / d) := by
    field_simp [hd_pos.ne']
    ring
  have hrecB' : (rec_sum A' : ℝ) ≤ 3 * (rec_sum B : ℝ) := by
    exact_mod_cast hrecB
  have hmulA : 3 * (2 / ((4 : ℝ) * d) + 2 * ε' * log (log N)) ≤ rec_sum A' := by
    rw [mul_add, haux]
    exact hpre
  have hmulB : 3 * (2 / ((4 : ℝ) * d) + 2 * ε' * log (log N)) ≤ 3 * rec_sum B := by
    exact le_trans hmulA hrecB'
  exact le_of_mul_le_mul_left hmulB (show 0 < (3 : ℝ) by norm_num)

set_option maxHeartbeats 1000000 in
-- The translated Lean 4 proof is long enough that it needs more heartbeats to elaborate.
theorem technical_prop :
    ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Finset.range (N + 1), ∀ y z : ℝ,
      1 ≤ y → 4 * y + 4 ≤ z → z ≤ (log N) ^ (1 / 500 : ℝ) → 0 ∉ A →
      (∀ n ∈ A, (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) ≤ n) →
      2 / y + (log N) ^ (-(1 / 200 : ℝ)) ≤ rec_sum A →
      (∀ n ∈ A, ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ y ≤ d₁ ∧ 4 * d₁ ≤ d₂ ∧ ((d₂ : ℝ) ≤ z)) →
      (∀ n ∈ A, is_smooth ((N : ℝ) ^ (1 - (8 : ℝ) / log (log N))) n) →
      arith_regular N A →
      ∃ S ⊆ A, ∃ d : ℕ, y ≤ d ∧ ((d : ℝ) ≤ z) ∧ rec_sum S = 1 / d := by
  obtain ⟨c, hc, circle_method⟩ := circle_method_prop2
  obtain hlargeN := large_enough_N
  specialize hlargeN c hc
  filter_upwards
    [ main_tech_lemma
    , force_good_properties
    , force_good_properties2
    , circle_method
    , hlargeN ] with
    N htechlemma hforce1 hforce2 hcircle hlargeN
  clear circle_method
  let M : ℝ := (N : ℝ) ^ (1 - (1 : ℝ) / log (log N))
  let K : ℝ := (N : ℝ) ^ (1 - (3 : ℝ) / log (log N))
  let L : ℝ := M / (2 * log N ^ ((1 : ℝ) / 100))
  let T : ℝ := M / log N
  rcases hlargeN with
    ⟨hMε, hε, hM3, hM2, hM1, hlogN3, heK, hKM, hlogN4, hlogN5, hlogN6, hlargeNnew,
      hlargenew2, hε'M, hlarge3, hlarge4, hεε'M, hUhelper, hUhelper2, hUhelper3, hlarge7⟩
  have hNMcast : (N : ℝ) ≤ M ^ 2 := by
    rw [← Real.rpow_natCast]
    exact hM3
  have hM2aux : M ≤ N := by
    exact le_of_lt hM2
  intro A hA y z h1y hyz hzN h0A hA2 hrec hdiv hsmooth hreg
  have htemp6 :
      (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) = K := by
    have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le hM1 hM2aux
    rw [← Real.rpow_add hNpos]
    have hEq :
        1 - (1 : ℝ) / log (log N) + (-(2 : ℝ) / log (log N)) =
          1 - (3 : ℝ) / log (log N) := by
      ring_nf
    rw [hEq]
  have hzT : 0 < T := by
    exact div_pos hM1 hlogN3
  have hzL : 0 < L := by
    apply div_pos hM1
    apply mul_pos
    · exact zero_lt_two
    · exact Real.rpow_pos_of_pos hlogN3 _
  have hyzaux : y ≤ z := by
    apply le_trans (b := 4 * y)
    · exact le_mul_of_one_le_left (le_trans zero_le_one h1y) (by norm_num : (1 : ℝ) ≤ 4)
    · apply le_trans (b := 4 * y + 4)
      · exact le_add_of_nonneg_right (show 0 ≤ (4 : ℝ) by norm_num)
      · exact hyz
  have hz_pos : 0 < z := by
    exact lt_of_lt_of_le zero_lt_one (le_trans h1y hyzaux)
  have hwM : z / 4 < 2 * M := by
    apply lt_of_lt_of_le (b := z)
    · rw [div_lt_iff₀ zero_lt_four]
      exact lt_mul_of_one_lt_right hz_pos one_lt_four
    · exact le_trans hzN (le_of_lt hlogN4)
  have h8z : 8 ≤ z := by
    apply le_trans (b := 4 * y + 4)
    · have h4y : 4 ≤ 4 * y := by
        exact le_mul_of_one_le_right (show 0 ≤ (4 : ℝ) by norm_num) h1y
      linarith
    · exact hyz
  have h2z : 2 ≤ z / 4 := by
    rw [le_div_iff₀ zero_lt_four]
    norm_num1
    exact h8z
  have hyz' : ⌈y⌉₊ ≤ ⌊z / 4⌋₊ := by
    rw [Nat.ceil_le]
    apply le_trans (b := z / 4 - 1)
    · apply le_sub_right_of_add_le
      rw [le_div_iff₀ zero_lt_four, add_mul, one_mul, mul_comm]
      exact hyz
    · rw [sub_le_iff_le_add]
      refine le_trans le_rfl ?_
      have hfloor : z / 4 < (⌊z / 4⌋₊ : ℝ) + 1 := by
        exact Nat.lt_floor_add_one (z / 4)
      exact le_of_lt hfloor
  let ε' : ℝ := (log N) ^ (-(1 / 100 : ℝ))
  have h0ε' : 0 < ε' := by
    exact Real.rpow_pos_of_pos hlogN3 _
  have hε'w2 : 3 * ε' * log (log N) ≤ 2 / (z ^ 2) := by
    have hsq : z ^ 2 ≤ ((log N) ^ ((1 / 500 : ℝ))) ^ 2 := by
      nlinarith [hzN, hz_pos, show 0 ≤ (log N) ^ ((1 / 500 : ℝ)) by positivity]
    have hInv : 1 / (((log N) ^ ((1 / 500 : ℝ))) ^ 2) ≤ 1 / (z ^ 2) := by
      exact one_div_le_one_div_of_le (sq_pos_of_pos hz_pos) hsq
    refine hlarge3.trans ?_
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      (mul_le_mul_of_nonneg_left hInv (show 0 ≤ (2 : ℝ) by norm_num))
  have hε'z : 3 * ε' * log (log N) ≤ 2 / ((z / 4) ^ 2) := by
    have hεzaux : (z / 4) ^ 2 ≤ z ^ 2 := by
      nlinarith [hz_pos]
    have hInv : 1 / (z ^ 2) ≤ 1 / ((z / 4) ^ 2) := by
      exact one_div_le_one_div_of_le (sq_pos_of_pos (div_pos hz_pos zero_lt_four)) hεzaux
    refine hε'w2.trans ?_
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      (mul_le_mul_of_nonneg_left hInv (show 0 ≤ (2 : ℝ) by norm_num))
  have hrec' : 2 / y + 2 * ε' * log (log N) ≤ rec_sum A := by
    apply le_trans ?_ hrec
    exact add_le_add le_rfl hlarge4
  have hsmooth' : ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ ε' * M := by
    intro q hq
    rw [ppowers_in_set, Finset.mem_biUnion] at hq
    rcases hq with ⟨a, ha, hq⟩
    rw [Finset.mem_filter] at hq
    simp_rw [is_smooth] at hsmooth
    specialize hsmooth a ha q hq.2.1
    apply le_trans _ hεε'M
    exact hsmooth (Nat.dvd_of_mem_divisors hq.1)
  have hdiv' : ∀ n ∈ A, ∃ d : ℕ, y ≤ d ∧ ((d : ℝ) ≤ z / 4) ∧ d ∣ n := by
    intro n hn
    specialize hdiv n hn
    rcases hdiv with ⟨d₁, d₂, hd₁, hd₂, hyd₁, hd₁₂, hd₂z⟩
    exact technical_prop_hdiv_aux y z n d₁ d₂ hd₁ hyd₁ hd₁₂ hd₂z
  have htech2 := htechlemma
  specialize htechlemma M ε' y (z / 4) A hA hM1 hM2 h0ε' hwM hε'M h1y h2z hyz' hε'z hA2 hrec'
    hsmooth' hdiv'
  rcases htechlemma with ⟨A', hA', d, htech⟩
  have hzd : d ≠ 0 := by
    have hd1 : 1 ≤ d := by
      exact_mod_cast le_trans h1y htech.2.1
    exact Nat.ne_of_gt (Nat.succ_le_iff.mp hd1)
  by_cases
    hgoodsubset :
      ∃ B ⊆ A',
        rec_sum A' ≤ 3 * rec_sum B ∧ (ppower_rec_sum B : ℝ) ≤ (2 / 3) * log (log N)
  · clear hforce1
    rcases hgoodsubset with ⟨B, hB, hrecB, hppB⟩
    have hB2 : B ⊆ Finset.range (N + 1) := by
      exact (hB.trans hA').trans hA
    have hzM : z < 2 * M := by
      exact lt_of_le_of_lt hzN hlogN4
    have h14d : 1 ≤ (4 : ℝ) * d := by
      have hd1 : (1 : ℝ) ≤ d := by
        exact le_trans h1y htech.2.1
      nlinarith
    have h2z' : 2 ≤ z := by
      exact le_trans (by norm_num1 : (2 : ℝ) ≤ 8) h8z
    have hdz : ⌈(4 : ℝ) * d⌉₊ ≤ ⌊z⌋₊ := by
      have h4dz : (4 : ℝ) * d ≤ z := by
        nlinarith [htech.2.2.1]
      have h4dz_nat : 4 * d ≤ ⌊z⌋₊ := by
        exact (Nat.le_floor_iff (le_of_lt hz_pos)).mpr <| by
          simpa [Nat.cast_mul] using h4dz
      rw [show ((4 : ℝ) * d) = ((4 * d : ℕ) : ℝ) by norm_num, Nat.ceil_natCast]
      exact h4dz_nat
    have hB3 : ∀ n : ℕ, n ∈ B → M ≤ n := by
      intro n hn
      exact hA2 n ((hB.trans hA') hn)
    have hrecB' : 2 / ((4 : ℝ) * d) + 2 * ε' * log (log N) ≤ rec_sum B := by
      exact technical_prop_hrecB N M ε' y z A' B d h1y hz_pos hzN hlargeNnew hrecB htech.2.1
        htech.2.2.1 htech.2.2.2.2.1
    have hsmoothB : ∀ q ∈ ppowers_in_set B, (q : ℝ) ≤ ε' * M := by
      intro q hq
      exact hsmooth' q ((ppowers_in_set_subset ((hB.trans hA')) hq))
    have hdivB :
        ∀ n : ℕ, n ∈ B → ∃ d₁ : ℕ, (4 : ℝ) * d ≤ d₁ ∧ (d₁ : ℝ) ≤ z ∧ d₁ ∣ n := by
      intro n hn
      specialize hdiv n ((hB.trans hA') hn)
      rcases hdiv with ⟨d₁, d₂, hd₁, hd₂, hyd₁, hd₁₂, hd₂z⟩
      have hdle : d ≤ d₁ := by
        obtain htech' := htech.2.2.2.2.2.2.2
        specialize htech' n (hB hn) d₁ hd₁
        apply le_of_not_gt
        intro hfoo
        specialize htech' hfoo
        exact (not_le.mpr htech') hyd₁
      refine ⟨d₂, ?_, hd₂z, hd₂⟩
      norm_cast
      apply le_trans (b := 4 * d₁)
      · have hdle' : (d : ℝ) ≤ d₁ := by
          exact_mod_cast hdle
        nlinarith
      · exact hd₁₂
    specialize htech2 M ε' ((4 : ℝ) * d) z B hB2 hM1 hM2 h0ε' hzM hε'M h14d h2z' hdz hε'w2 hB3
      hrecB' hsmoothB hdivB
    rcases htech2 with ⟨B', hB', d', htech2⟩
    have hB'2 : B' ⊆ Finset.range (N + 1) := by
      exact hB'.trans hB2
    have hB'reg : arith_regular N B' := by
      exact hreg.subset (hB'.trans (hB.trans hA'))
    have hB'3 : ∀ q ∈ ppowers_in_set B', (log N) ^ (-(1 / 100 : ℝ)) ≤ rec_sum_local B' q := by
      obtain htech2' := htech2.2.2.2.2.2.1
      intro q hq
      exact le_of_lt (htech2' q hq)
    have hB'4 : (ppower_rec_sum B' : ℝ) ≤ (2 / 3) * log (log N) := by
      apply le_trans _ hppB
      norm_cast
      exact ppower_rec_sum_mono hB'
    have hB'5 : ∀ n : ℕ, n ∈ B' → M ≤ n := by
      intro n hn
      exact hA2 n ((hA' <| hB <| hB' hn))
    have hB'n0 : 0 ∉ B' := by
      intro hz
      exact h0A (hA' (hB (hB' hz)))
    specialize hforce2 M B' hB'2 hM1 (le_of_lt hM2) hNMcast hB'n0 hB'5 hB'reg hB'3 hB'4
    have hzd' : d' ≠ 0 := by
      have hd1 : 1 ≤ d' := by
        exact_mod_cast le_trans h14d htech2.2.1
      exact Nat.ne_of_gt (Nat.succ_le_iff.mp hd1)
    have hd'M : (d' : ℝ) ≤ M / 192 := by
      exact le_trans htech2.2.2.1 (le_trans hzN hlargenew2)
    have hB'6 : ∀ n : ℕ, n ∈ B' → n ≤ N := by
      intro n hn
      rw [← Nat.lt_add_one_iff, ← Finset.mem_range]
      exact hB'2 hn
    have hdB' : d' ∣ B'.lcm id := by
      rcases htech2.2.2.2.2.2.2.1 with ⟨n, hn, hnew⟩
      exact dvd_trans hnew (Finset.dvd_lcm hn)
    let U' :=
      min (L * K ^ 2 / (16 * N ^ 2 * log N ^ 2)) (min (c * M / d') (T * K ^ 2 / (N ^ 2 * log N)))
    have hU'M : (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ U' := by
      rw [le_min_iff]
      constructor
      · exact hUhelper
      · rw [le_min_iff]
        constructor
        · apply le_trans (b := c * M / z)
          · apply le_trans (b := c * M / (log N) ^ ((1 / 500 : ℝ)))
            · exact hUhelper3
            · have hInv : 1 / ((log N) ^ ((1 / 500 : ℝ))) ≤ 1 / z := by
                exact one_div_le_one_div_of_le hz_pos hzN
              simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
                (mul_le_mul_of_nonneg_left hInv (show 0 ≤ c * M by positivity))
          · have hd'pos : 0 < (d' : ℝ) := by
              exact_mod_cast Nat.pos_of_ne_zero hzd'
            have hInv : 1 / z ≤ 1 / d' := by
              exact one_div_le_one_div_of_le hd'pos htech2.2.2.1
            simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
              (mul_le_mul_of_nonneg_left hInv (show 0 ≤ c * M by positivity))
        · exact hUhelper2
    have hppB' : ∀ q : ℕ, q ∈ ppowers_in_set B' → (q : ℝ) ≤ U' := by
      intro q hq
      rw [ppowers_in_set, Finset.mem_biUnion] at hq
      rcases hq with ⟨a, ha, hq⟩
      rw [Finset.mem_filter] at hq
      simp_rw [is_smooth] at hsmooth
      specialize hsmooth a (hA' (hB (hB' ha))) q hq.2.1
      apply le_trans _ hU'M
      exact hsmooth (Nat.dvd_of_mem_divisors hq.1)
    have hgoodB' : good_condition B' K T L := by
      rw [htemp6] at hforce2
      exact hforce2
    specialize
      @hcircle K L M T d' B' hzT hzL heK hKM hM2aux hzd' hd'M hB'5 hB'6 htech2.2.2.2.1
        htech2.2.2.2.2.1 hdB' hppB' hgoodB'
    rcases hcircle with ⟨S, hS, hcirc⟩
    refine ⟨S, hS.trans (hB'.trans (hB.trans hA')), d', ?_, htech2.2.2.1, hcirc⟩
    apply le_trans htech.2.1
    apply le_trans (b := (4 : ℝ) * d)
    · exact le_mul_of_one_le_left (Nat.cast_nonneg d) (by norm_num : (1 : ℝ) ≤ 4)
    · exact htech2.2.1
  · clear hforce2 htech2
    have hrangeA' : A' ⊆ Finset.range (N + 1) := by
      exact hA'.trans hA
    have hregA' : arith_regular N A' := by
      exact hreg.subset hA'
    have hNA' : (log N) ^ (-(1 / 101 : ℝ)) ≤ rec_sum A' := by
      have hdP : (d : ℝ) ≤ (log N) ^ (1 / 500 : ℝ) / 4 := by
        nlinarith [htech.2.2.1, hzN]
      have htwoDiv : (2 : ℝ) / ((log N) ^ (1 / 500 : ℝ) / 4) ≤ 2 / d := by
        have hdpos : 0 < (d : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hzd
        have hInv : 1 / ((log N) ^ (1 / 500 : ℝ) / 4) ≤ 1 / d := by
          exact one_div_le_one_div_of_le hdpos hdP
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
          (mul_le_mul_of_nonneg_left hInv (show 0 ≤ (2 : ℝ) by norm_num))
      exact hlarge7.trans <| (sub_le_sub_right htwoDiv _).trans htech.2.2.2.2.1
    have hppA' : ∀ q ∈ ppowers_in_set A', (log N) ^ (-(1 / 100 : ℝ)) ≤ rec_sum_local A' q := by
      obtain htech' := htech.2.2.2.2.2.1
      intro q hq
      exact le_of_lt (htech' q hq)
    have hA'5 : ∀ n : ℕ, n ∈ A' → M ≤ n := by
      intro n hn
      exact hA2 n (hA' hn)
    have hA'n0 : 0 ∉ A' := by
      intro hz
      exact h0A (hA' hz)
    specialize hforce1 M A' hrangeA' hM1 (le_of_lt hM2) hNMcast hA'n0 hA'5 hregA' hNA' hppA'
    rcases hforce1 with htemp1 | htemp2
    · exfalso
      exact hgoodsubset htemp1
    · have hgoodA' : good_condition A' K T L := by
        rw [htemp6] at htemp2
        exact htemp2
      have hdM : (d : ℝ) ≤ M / 192 := by
        apply le_trans htech.2.2.1
        apply le_trans (b := z / 4)
        · exact le_rfl
        · apply le_trans ?_ (le_trans hzN hlargenew2)
          exact div_le_self (le_of_lt hz_pos) (by norm_num : (1 : ℝ) ≤ 4)
      have hA'6 : ∀ n : ℕ, n ∈ A' → n ≤ N := by
        intro n hn
        rw [← Nat.lt_add_one_iff, ← Finset.mem_range]
        exact hrangeA' hn
      have hdA' : d ∣ A'.lcm id := by
        rcases htech.2.2.2.2.2.2.1 with ⟨n, hn, hnew⟩
        exact dvd_trans hnew (Finset.dvd_lcm hn)
      let U :=
        min (L * K ^ 2 / (16 * N ^ 2 * log N ^ 2)) (min (c * M / d) (T * K ^ 2 / (N ^ 2 * log N)))
      have hUM : (N : ℝ) ^ (1 - (8 : ℝ) / log (log N)) ≤ U := by
        rw [le_min_iff]
        constructor
        · exact hUhelper
        · rw [le_min_iff]
          constructor
          · apply le_trans (b := c * M / z)
            · apply le_trans (b := c * M / (log N) ^ ((1 / 500 : ℝ)))
              · exact hUhelper3
              · have hInv : 1 / ((log N) ^ ((1 / 500 : ℝ))) ≤ 1 / z := by
                  exact one_div_le_one_div_of_le hz_pos hzN
                simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
                  (mul_le_mul_of_nonneg_left hInv (show 0 ≤ c * M by positivity))
            · have hdpos : 0 < (d : ℝ) := by
                exact_mod_cast Nat.pos_of_ne_zero hzd
              have hdz' : (d : ℝ) ≤ z := by
                have : (d : ℝ) ≤ z / 4 := htech.2.2.1
                nlinarith
              have hInv : 1 / z ≤ 1 / d := by
                exact one_div_le_one_div_of_le hdpos hdz'
              simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
                (mul_le_mul_of_nonneg_left hInv (show 0 ≤ c * M by positivity))
          · exact hUhelper2
      have hppA' : ∀ q : ℕ, q ∈ ppowers_in_set A' → (q : ℝ) ≤ U := by
        intro q hq
        rw [ppowers_in_set, Finset.mem_biUnion] at hq
        rcases hq with ⟨a, ha, hq⟩
        rw [Finset.mem_filter] at hq
        simp_rw [is_smooth] at hsmooth
        specialize hsmooth a (hA' ha) q hq.2.1
        apply le_trans _ hUM
        exact hsmooth (Nat.dvd_of_mem_divisors hq.1)
      specialize
        @hcircle K L M T d A' hzT hzL heK hKM hM2aux hzd hdM hA'5 hA'6 htech.2.2.2.1
          htech.2.2.2.2.1 hdA' hppA' hgoodA'
      rcases hcircle with ⟨S, hS, hcirc⟩
      refine ⟨S, hS.trans hA', d, htech.2.1, ?_, hcirc⟩
      apply le_trans htech.2.2.1
      apply div_le_self
      · exact le_trans zero_le_one (le_trans h1y hyzaux)
      · norm_num

lemma prop_one_specialise :
    ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Finset.range (N + 1),
      (∀ n ∈ A, (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) ≤ n) → 0 ∉ A →
      (log N) ^ (1 / 500 : ℝ) ≤ (rec_sum A : ℝ) →
      (∀ n ∈ A, ∃ d₂ : ℕ, d₂ ∣ n ∧ 4 ≤ d₂ ∧ (d₂ : ℝ) ≤ (log N) ^ (1 / 500 : ℝ)) →
      (∀ n ∈ A, is_smooth ((N : ℝ) ^ (1 - (8 : ℝ) / log (log N))) n) →
      arith_regular N A →
      ∃ S ⊆ A, ∃ d : ℕ, 1 ≤ d ∧ (d : ℝ) ≤ (log N) ^ (1 / 500 : ℝ) ∧ rec_sum S = 1 / d := by
  have hf : Tendsto (fun x : ℕ => log x ^ (1 / 500 : ℝ)) atTop atTop :=
    tendsto_coe_log_pow_at_top _ (by norm_num1)
  have hf' : Tendsto (fun x : ℕ => log x ^ (1 / 200 : ℝ)) atTop atTop :=
    tendsto_coe_log_pow_at_top _ (by norm_num1)
  filter_upwards
    [ technical_prop
    , hf.eventually (eventually_ge_atTop (8 : ℝ))
    , hf'.eventually (eventually_ge_atTop (1 : ℝ))
    , (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (0 : ℝ)) ] with
    N hN hN' hN'' hN''' A A_upper_bound A_lower_bound h0A hA₁ hA₂ hA₃ hA₄
  dsimp at hN' hN'' hN'''
  obtain ⟨S, hS, d, hd1, hd2, hrec⟩ :=
    hN A A_upper_bound 1 ((log N) ^ (1 / 500 : ℝ)) le_rfl
      (show 4 * (1 : ℝ) + 4 ≤ (log N) ^ (1 / 500 : ℝ) by
        exact le_trans (by norm_num1) hN')
      le_rfl h0A A_lower_bound
      (show 2 / (1 : ℝ) + (log N) ^ (-(1 / 200 : ℝ)) ≤ rec_sum A by
        apply (le_trans _ hN').trans hA₁
        rw [← le_sub_iff_add_le', Real.rpow_neg]
        · norm_num1
          have hpow_inv :
              ((log N) ^ (1 / 200 : ℝ))⁻¹ ≤ 1 := by
            simpa [one_div] using
              (one_div_le_one_div_of_le (show 0 < (1 : ℝ) by norm_num) hN'')
          exact le_trans hpow_inv (by norm_num1)
        · exact hN''')
      (by
        intro n hn
        obtain ⟨d₂, hd₂, hd₂', hd₂''⟩ := hA₂ n hn
        exact ⟨1, d₂, one_dvd _, hd₂, by simp, by simpa, hd₂''⟩)
      hA₃ hA₄
  refine ⟨S, hS, d, ?_, hd2, hrec⟩
  exact_mod_cast hd1

theorem corollary_one :
    ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Finset.range (N + 1),
      (∀ n ∈ A, (N : ℝ) ^ (1 - (1 : ℝ) / log (log N)) ≤ n) →
      2 * (log N) ^ (1 / 500 : ℝ) ≤ rec_sum A →
      (∀ n ∈ A, ∃ p : ℕ, p ∣ n ∧ 4 ≤ p ∧ (p : ℝ) ≤ (log N) ^ (1 / 500 : ℝ)) →
      (∀ n ∈ A, is_smooth ((N : ℝ) ^ (1 - (8 : ℝ) / log (log N))) n) →
      arith_regular N A →
      ∃ S ⊆ A, rec_sum S = 1 := by
  classical
  filter_upwards [prop_one_specialise, eventually_ge_atTop (1 : ℕ)] with
    N p1 hN₁ A A_upper_bound A_lower_bound hA₁ hA₂ hA₃ hA₄
  let good_set : Finset (Finset ℕ) → Prop := fun S =>
    (∀ s ∈ S, s ⊆ A) ∧ (S : Set (Finset ℕ)).PairwiseDisjoint id ∧
      ∀ s, ∃ d : ℕ, s ∈ S → 1 ≤ d ∧ (d : ℝ) ≤ (log N) ^ (1 / 500 : ℝ) ∧ rec_sum s = 1 / d
  let P : ℕ → Prop := fun k => ∃ S : Finset (Finset ℕ), S.card = k ∧ good_set S
  let k : ℕ := Nat.findGreatest P (A.card + 1)
  have P0 : P 0 := by
    refine ⟨∅, ?_⟩
    simp [good_set]
  have Pk : P k := by
    dsimp [k]
    exact Nat.findGreatest_spec (P := P) (Nat.zero_le _) P0
  obtain ⟨S, hk, hS₁, hS₂, hS₃⟩ := Pk
  choose d' hd'₁ hd'₂ hd'₃ using hS₃
  let t : ℕ → ℕ := fun d => (S.filter fun s => d' s = d).card
  by_cases h : ∃ d : ℕ, 0 < d ∧ d ≤ t d
  · obtain ⟨d, d_pos, ht⟩ := h
    obtain ⟨T', hT', hd₂⟩ :=
      Finset.exists_subset_card_eq (s := S.filter fun s => d' s = d) ht
    have hT'S : T' ⊆ S := hT'.trans (Finset.filter_subset _ _)
    refine ⟨T'.biUnion id, ?_, ?_⟩
    · refine (Finset.biUnion_subset_biUnion_of_subset_left _ hT'S).trans ?_
      rwa [Finset.biUnion_subset]
    · rw [rec_sum_bUnion_disjoint (hS₂.subset hT'S)]
      have hsumT : T'.sum rec_sum = T'.sum (fun _ : Finset ℕ => (1 : ℚ) / d) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa [(Finset.mem_filter.mp (hT' hi)).2] using (hd'₃ i (hT'S hi))
      rw [hsumT, Finset.sum_const, hd₂, nsmul_eq_mul]
      field_simp [show (d : ℚ) ≠ 0 by exact_mod_cast d_pos.ne']
  · exfalso
    have hcount : ∀ d : ℕ, 0 < d → t d < d := by
      intro d hd
      by_contra hdt
      exact h ⟨d, hd, le_of_not_gt hdt⟩
    let A' := A \ S.biUnion id
    have hS : ((S.sum rec_sum : ℚ) : ℝ) ≤ (log N) ^ (1 / 500 : ℝ) := by
      have hmaps : ∀ s ∈ S, d' s ∈ Finset.Icc 1 ⌊(log N) ^ (1 / 500 : ℝ)⌋₊ := by
        intro s hs
        simp only [Finset.mem_Icc, hd'₁ s hs, Nat.le_floor (hd'₂ s hs), and_self]
      have hS1 :
          ((S.sum rec_sum : ℚ) : ℝ) ≤
            (Finset.Icc 1 ⌊(log N) ^ (1 / 500 : ℝ)⌋₊).sum (fun d => (t d : ℝ) / d) := by
        rw [Rat.cast_sum, ← Finset.sum_fiberwise_of_maps_to hmaps]
        refine Finset.sum_le_sum ?_
        intro d hd
        rw [div_eq_mul_one_div, ← nsmul_eq_mul]
        refine Finset.sum_le_card_nsmul _ _ _ ?_
        intro s hs
        rcases Finset.mem_filter.mp hs with ⟨hsS, hsEq⟩
        have hrec_cast : (rec_sum s : ℝ) = (1 : ℝ) / d := by
          have hcast := congrArg (fun x : ℚ => (x : ℝ)) (hd'₃ s hsS)
          simpa [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, hsEq] using hcast
        simpa [one_div] using hrec_cast.le
      have hS2 :
          (Finset.Icc 1 ⌊(log N) ^ (1 / 500 : ℝ)⌋₊).sum (fun d => (t d : ℝ) / d) ≤
            (log N) ^ (1 / 500 : ℝ) := by
        refine (Finset.sum_le_card_nsmul _ _ 1 ?_).trans ?_
        · simp only [one_div, Finset.mem_Icc, and_imp]
          intro d hd₁ _hd₂
          exact div_le_one_of_le₀ (Nat.cast_le.mpr (hcount d hd₁).le) (Nat.cast_nonneg _)
        · simpa [Nat.card_Icc, nsmul_eq_mul] using
            (Nat.floor_le (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hN₁)) _))
      exact le_trans hS1 hS2
    have hAS : Disjoint A' (S.biUnion id) := Finset.sdiff_disjoint
    have RA'_ineq : (log N) ^ (1 / 500 : ℝ) ≤ rec_sum A' := by
      have hsum : rec_sum A = rec_sum A' + rec_sum (S.biUnion id) := by
        rw [← rec_sum_disjoint hAS, Finset.sdiff_union_of_subset]
        rwa [Finset.biUnion_subset]
      rw [hsum] at hA₁
      simp only [Rat.cast_add] at hA₁
      rw [rec_sum_bUnion_disjoint hS₂, Rat.cast_sum] at hA₁
      rw [Rat.cast_sum] at hS
      linarith
    have hA' : A' ⊆ A := by
      intro n hn
      exact (Finset.mem_sdiff.mp hn).1
    have h0A' : 0 ∉ A' := by
      intro hz
      specialize A_lower_bound 0 (hA' hz)
      rw [← not_lt] at A_lower_bound
      apply A_lower_bound
      have hNpos : (0 : ℝ) < N := by
        exact_mod_cast lt_of_lt_of_le zero_lt_one hN₁
      simpa using (Real.rpow_pos_of_pos hNpos (1 - (1 : ℝ) / log (log N)))
    obtain ⟨S', hS', d, hd, hd', hS'₂⟩ :=
      p1 A' (hA'.trans A_upper_bound) (fun n hn => A_lower_bound n (hA' hn)) h0A' RA'_ineq
        (fun n hn => hA₂ n (hA' hn)) (fun n hn => hA₃ n (hA' hn)) (hA₄.subset hA')
    have hS'' : ∀ s ∈ S, Disjoint S' s := fun s hs =>
      Disjoint.mono hS' (Finset.subset_biUnion_of_mem id hs) hAS
    have hS''' : S' ∉ S := by
      intro hs
      exact (nonempty_of_rec_sum_recip hd hS'₂).ne_empty (disjoint_self.mp (hS'' _ hs))
    have hPk1 : P (k + 1) := by
      refine ⟨insert S' S, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hS''', hk]
      · refine ⟨?_, ?_, ?_⟩
        · simpa [hS'.trans hA'] using hS₁
        · simpa [Set.pairwiseDisjoint_insert_of_notMem hS''', hS₂] using fun s hs =>
            hS'' _ hs
        · intro s
          rcases eq_or_ne s S' with rfl | hs
          · exact ⟨d, fun _ => ⟨hd, hd', hS'₂⟩⟩
          · refine ⟨d' s, fun hs' => ?_⟩
            have hsS : s ∈ S := Finset.mem_of_mem_insert_of_ne hs' hs
            exact ⟨hd'₁ _ hsS, hd'₂ _ hsS, hd'₃ _ hsS⟩
    have hk_bound : k + 1 ≤ A.card + 1 := by
      rw [← hk, add_le_add_iff_right]
      refine le_trans ?_ (Finset.card_le_card (Finset.biUnion_subset.2 hS₁))
      refine Finset.card_le_card_biUnion hS₂ ?_
      intro s hs
      exact nonempty_of_rec_sum_recip (hd'₁ s hs) (hd'₃ s hs)
    have : k + 1 ≤ k := Nat.le_findGreatest hk_bound hPk1
    exact Nat.not_succ_le_self _ this
end UnitFractions
