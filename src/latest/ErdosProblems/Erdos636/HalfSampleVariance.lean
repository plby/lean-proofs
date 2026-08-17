/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos636.HalfSample
import ErdosProblems.Erdos636.External.Erdos88.Concentration

/-! # Second moments of uniform half-samples -/

open scoped BigOperators

namespace Erdos636
namespace HalfSampleVariance

open Classical
open Erdos88.Concentration

universe u

private lemma card_filter_slice_subset {I : Type u} [Fintype I]
    [DecidableEq I] {s : ℕ} (T : Finset I) (hTs : T.card ≤ s) :
    ((Finset.univ.filter fun S : HalfSample.Slice I s ↦ T ⊆ S.1).card) =
      (Fintype.card I - T.card).choose (s - T.card) := by
  let A := Finset.univ.filter fun S : HalfSample.Slice I s ↦ T ⊆ S.1
  let B := ((Finset.univ : Finset I).powersetCard s).filter (T ⊆ ·)
  have hAB : A.card = B.card := by
    apply Finset.card_bij (fun S _ ↦ S.1)
    · intro S hS
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hS
      simp only [B, Finset.mem_filter, Finset.mem_powersetCard,
        Finset.subset_univ, true_and]
      exact ⟨S.2, hS⟩
    · intro S₁ hS₁ S₂ hS₂ h
      exact Subtype.ext h
    · intro S hS
      simp only [B, Finset.mem_filter, Finset.mem_powersetCard,
        Finset.subset_univ, true_and] at hS
      refine ⟨⟨S, hS.1⟩, ?_, rfl⟩
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hS.2
  rw [hAB]
  simpa using Finset.card_filter_powersetCard_subset T
    (Finset.univ : Finset I) s (Finset.subset_univ T) hTs

private lemma sum_indicator_pair {I : Type u} [Fintype I] [DecidableEq I]
    {s : ℕ} (i j : I) (hpair : ({i, j} : Finset I).card ≤ s) :
    (∑ S : HalfSample.Slice I s,
        if i ∈ S.1 ∧ j ∈ S.1 then (1 : ℝ) else 0) =
      ((Fintype.card I - ({i, j} : Finset I).card).choose
        (s - ({i, j} : Finset I).card) : ℝ) := by
  calc
    (∑ S : HalfSample.Slice I s,
        if i ∈ S.1 ∧ j ∈ S.1 then (1 : ℝ) else 0) =
      ∑ S : HalfSample.Slice I s,
        if ({i, j} : Finset I) ⊆ S.1 then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro S _
          congr 1
          apply propext
          constructor
          · rintro ⟨hi, hj⟩ x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hi
            · exact hj
          · intro h
            exact ⟨h (by simp), h (by simp)⟩
    _ = _ := by
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero, Finset.sum_const,
        nsmul_eq_mul, mul_one]
      exact_mod_cast card_filter_slice_subset ({i, j} : Finset I) hpair

private lemma sum_sliceSum_sq_exact {I : Type u} [Fintype I] [DecidableEq I]
    {s : ℕ} (hs : 2 ≤ s) (a : I → ℝ) (hsum : ∑ i, a i = 0) :
    (∑ S : HalfSample.Slice I s, (HalfSample.sliceSum a S) ^ 2) =
      (((Fintype.card I - 1).choose (s - 1) : ℝ) -
        ((Fintype.card I - 2).choose (s - 2) : ℝ)) *
          ∑ i, (a i) ^ 2 := by
  have hpair (i j : I) : ({i, j} : Finset I).card ≤ s := by
    rcases Finset.card_pair_eq_one_or_two (a := i) (b := j) with h | h <;> omega
  have hcount (i j : I) :
      (∑ S : HalfSample.Slice I s,
          if i ∈ S.1 ∧ j ∈ S.1 then (1 : ℝ) else 0) =
        if i = j then ((Fintype.card I - 1).choose (s - 1) : ℝ)
        else ((Fintype.card I - 2).choose (s - 2) : ℝ) := by
    rw [sum_indicator_pair i j (hpair i j)]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  calc
    (∑ S : HalfSample.Slice I s, (HalfSample.sliceSum a S) ^ 2) =
        ∑ S : HalfSample.Slice I s, ∑ i, ∑ j,
          a i * a j * if i ∈ S.1 ∧ j ∈ S.1 then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      simp only [HalfSample.sliceSum, pow_two]
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
      calc
        (∑ i ∈ S.1, ∑ j ∈ S.1, a i * a j) =
            ∑ i ∈ S.1, ∑ j,
              a i * a j * if i ∈ S.1 ∧ j ∈ S.1 then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ S.1)
          · intro j hj
            have hjS : j ∉ S.1 := (Finset.mem_sdiff.mp hj).2
            simp [hjS]
          · intro j hj
            simp [hi, hj]
        _ = ∑ i, ∑ j,
              a i * a j * if i ∈ S.1 ∧ j ∈ S.1 then (1 : ℝ) else 0 := by
          apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ S.1)
          · intro i hi
            have hiS : i ∉ S.1 := (Finset.mem_sdiff.mp hi).2
            simp [hiS]
          · intro i hi
            rfl
    _ = ∑ i, ∑ j, ∑ S : HalfSample.Slice I s,
          a i * a j * if i ∈ S.1 ∧ j ∈ S.1 then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, a i * a j *
          (∑ S : HalfSample.Slice I s,
            if i ∈ S.1 ∧ j ∈ S.1 then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, a i * a j *
        (if i = j then ((Fintype.card I - 1).choose (s - 1) : ℝ)
         else ((Fintype.card I - 2).choose (s - 2) : ℝ)) := by
      simp_rw [hcount]
    _ = (((Fintype.card I - 1).choose (s - 1) : ℝ) -
        ((Fintype.card I - 2).choose (s - 2) : ℝ)) *
          ∑ i, (a i) ^ 2 := by
      let c₁ : ℝ := (Fintype.card I - 1).choose (s - 1)
      let c₂ : ℝ := (Fintype.card I - 2).choose (s - 2)
      have hoff : (∑ i, ∑ j, if i = j then (0 : ℝ) else a i * a j) =
          -(∑ i, (a i) ^ 2) := by
        have htotal : (∑ i, ∑ j, a i * a j) = 0 := by
          calc
            (∑ i, ∑ j, a i * a j) = (∑ i, a i) * (∑ j, a j) := by
              rw [Finset.sum_mul_sum]
            _ = 0 := by rw [hsum]; ring
        have hdiag : (∑ i, ∑ j, if i = j then a i * a j else 0) =
            ∑ i, (a i)^2 := by simp [pow_two]
        have hsplit : (∑ i, ∑ j, a i * a j) =
            (∑ i, (a i) ^ 2) +
              ∑ i, ∑ j, if i = j then (0 : ℝ) else a i * a j := by
          rw [← hdiag, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          by_cases hij : i = j <;> simp [hij]
        linarith
      change (∑ i, ∑ j, a i * a j * (if i = j then c₁ else c₂)) = _
      have hdecomp :
          (∑ i, ∑ j, a i * a j * (if i = j then c₁ else c₂)) =
            c₁ * (∑ i, (a i)^2) + c₂ *
              (∑ i, ∑ j, if i = j then 0 else a i * a j) := by
        calc
          _ = ∑ i, ∑ j,
              ((if i = j then a i * a j else 0) * c₁ +
               (if i = j then 0 else a i * a j) * c₂) := by
                apply Finset.sum_congr rfl
                intro i _
                apply Finset.sum_congr rfl
                intro j _
                by_cases hij : i = j <;> simp [hij]
          _ = c₁ * (∑ i, (a i)^2) + c₂ *
              (∑ i, ∑ j, if i = j then 0 else a i * a j) := by
                simp_rw [Finset.sum_add_distrib]
                have hdiag : (∑ i, ∑ j,
                    (if i = j then a i * a j else 0) * c₁) =
                    c₁ * ∑ i, (a i)^2 := by
                      simp [pow_two, mul_comm]
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro i hi
                      ring
                rw [hdiag]
                simp_rw [← Finset.sum_mul]
                ring
      rw [hdecomp, hoff]
      dsimp [c₁, c₂]
      ring

/-- `L²` form of the centred half-slice estimate. -/
private theorem uniformExpectation_sliceSum_sq_le_of_sum_sq
    {I : Type u} [Fintype I] [DecidableEq I] {s : ℕ}
    (hcard : Fintype.card I = 2 * s) (hs : 2 ≤ s)
    (a : I → ℝ) (K : ℝ) (hsum : ∑ i, a i = 0)
    (hsquares : (∑ i, (a i) ^ 2) ≤ (2 * s : ℝ) * K ^ 2) :
    uniformExpectation (fun S : HalfSample.Slice I s ↦
      (HalfSample.sliceSum a S) ^ 2) ≤ (s : ℝ) * K ^ 2 := by
  classical
  let _ := HalfSample.sliceNonempty hcard
  rw [uniformExpectation, sum_sliceSum_sq_exact hs a hsum]
  rw [Fintype.card_finset_len, hcard]
  have hchoosePos : 0 < (2 * s).choose s := Nat.choose_pos (by omega)
  have hc2nonneg : (0 : ℝ) ≤ ((2 * s - 2).choose (s - 2) : ℝ) := by
    positivity
  have hc1ratio :
      (((2 * s - 1).choose (s - 1) : ℝ) /
        ((2 * s).choose s : ℝ)) = (1 : ℝ) / 2 := by
    have hchoose := Nat.choose_mul (n := 2 * s) (k := s) (s := 1)
      (show 0 < s by omega)
    norm_num at hchoose
    have hreal : ((2 * s).choose s : ℝ) * s =
        (2 * s : ℝ) * ((2 * s - 1).choose (s - 1) : ℝ) := by
      exact_mod_cast hchoose
    field_simp [Nat.ne_of_gt hchoosePos]
    nlinarith [show (0 : ℝ) < s by exact_mod_cast (show 0 < s by omega)]
  calc
    ((((2 * s - 1).choose (s - 1) : ℝ) -
        ((2 * s - 2).choose (s - 2) : ℝ)) * ∑ i, (a i)^2) /
        ((2 * s).choose s : ℝ) ≤
      (((2 * s - 1).choose (s - 1) : ℝ) * ∑ i, (a i)^2) /
        ((2 * s).choose s : ℝ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right (sub_le_self _ hc2nonneg)
            (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    _ = ((1 : ℝ) / 2) * ∑ i, (a i)^2 := by
      rw [mul_div_assoc]
      calc
        ((2 * s - 1).choose (s - 1) : ℝ) *
            ((∑ i, a i ^ 2) / ((2 * s).choose s : ℝ)) =
            (((2 * s - 1).choose (s - 1) : ℝ) /
              ((2 * s).choose s : ℝ)) * (∑ i, a i^2) := by ring
        _ = _ := by rw [hc1ratio]
    _ ≤ (1 / 2 : ℝ) * ((2 * s : ℝ) * K^2) := by gcongr
    _ = (s : ℝ) * K^2 := by ring

private theorem uniformExpectation_add_sliceSum_sq_le_of_sum_sq
    {I : Type u} [Fintype I] [DecidableEq I] {s : ℕ}
    (hcard : Fintype.card I = 2 * s) (hs : 2 ≤ s)
    (a : I → ℝ) (K : ℝ) (hsum : ∑ i, a i = 0)
    (hsquares : (∑ i, (a i) ^ 2) ≤ (2 * s : ℝ) * K ^ 2)
    (offset R : ℝ) (hR : 0 ≤ R)
    (hoffset : |offset| ≤ R * Real.sqrt s) :
    uniformExpectation (fun S : HalfSample.Slice I s ↦
      (offset + HalfSample.sliceSum a S) ^ 2) ≤
        (K ^ 2 + R ^ 2) * s := by
  classical
  let _ := HalfSample.sliceNonempty hcard
  have hmean : uniformExpectation
      (fun S : HalfSample.Slice I s ↦ HalfSample.sliceSum a S) = 0 := by
    change HalfSample.sliceExpectation hcard a = 0
    rw [HalfSample.sliceExpectation_eq_half_total, hsum]
    norm_num
  have hsquare := uniformExpectation_sliceSum_sq_le_of_sum_sq
    hcard hs a K hsum hsquares
  have hmul : uniformExpectation
      (fun S : HalfSample.Slice I s ↦
        (2 * offset) * HalfSample.sliceSum a S) = 0 := by
    have hsumMul : (∑ S : HalfSample.Slice I s,
        (2 * offset) * HalfSample.sliceSum a S) =
        (2 * offset) * ∑ S : HalfSample.Slice I s,
          HalfSample.sliceSum a S := by rw [Finset.mul_sum]
    simp only [uniformExpectation]
    rw [hsumMul]
    have hmean' : (∑ S : HalfSample.Slice I s,
        HalfSample.sliceSum a S) /
          (Fintype.card (HalfSample.Slice I s) : ℝ) = 0 := hmean
    calc
      ((2 * offset) * ∑ S : HalfSample.Slice I s,
          HalfSample.sliceSum a S) /
          (Fintype.card (HalfSample.Slice I s) : ℝ) =
        (2 * offset) * ((∑ S : HalfSample.Slice I s,
          HalfSample.sliceSum a S) /
          (Fintype.card (HalfSample.Slice I s) : ℝ)) := by ring
      _ = 0 := by rw [hmean']; ring
  have hexpand : uniformExpectation (fun S : HalfSample.Slice I s ↦
      (offset + HalfSample.sliceSum a S) ^ 2) =
      offset ^ 2 + uniformExpectation (fun S : HalfSample.Slice I s ↦
        (HalfSample.sliceSum a S) ^ 2) := by
    calc
      _ = uniformExpectation (fun S : HalfSample.Slice I s ↦
          offset ^ 2 + (2 * offset) * HalfSample.sliceSum a S +
            (HalfSample.sliceSum a S) ^ 2) := by
              congr 1
              funext S
              ring
      _ = offset ^ 2 + 0 + uniformExpectation
          (fun S : HalfSample.Slice I s ↦
            (HalfSample.sliceSum a S) ^ 2) := by
              rw [uniformExpectation_add, uniformExpectation_add,
                uniformExpectation_const, hmul]
      _ = _ := by ring
  have hsnonneg : (0 : ℝ) ≤ s := by positivity
  have hsqrt : 0 ≤ R * Real.sqrt s :=
    mul_nonneg hR (Real.sqrt_nonneg _)
  have hoffsetSq : offset ^ 2 ≤ R ^ 2 * s := by
    have hsq := (sq_le_sq₀ (abs_nonneg offset) hsqrt).2 hoffset
    rw [sq_abs, mul_pow, Real.sq_sqrt hsnonneg] at hsq
    exact hsq
  rw [hexpand]
  calc
    offset ^ 2 + uniformExpectation (fun S : HalfSample.Slice I s ↦
        (HalfSample.sliceSum a S) ^ 2) ≤
        R ^ 2 * s + (s : ℝ) * K ^ 2 := add_le_add hoffsetSq hsquare
    _ = (K ^ 2 + R ^ 2) * s := by ring

/-- A centred coefficient sum on a uniform half-slice has second moment at
most `s K²` when every coefficient has absolute value at most `K`. -/
theorem uniformExpectation_sliceSum_sq_le {I : Type u} [Fintype I]
    [DecidableEq I] {s : ℕ} (hcard : Fintype.card I = 2 * s)
    (hs : 0 < s) (a : I → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (ha : ∀ i, |a i| ≤ K) (hsum : ∑ i, a i = 0) :
    uniformExpectation (fun S : HalfSample.Slice I s ↦
      (HalfSample.sliceSum a S) ^ 2) ≤ (s : ℝ) * K ^ 2 := by
  classical
  let _ := HalfSample.sliceNonempty hcard
  by_cases hs1 : s = 1
  · subst s
    have hcardI : Fintype.card I = 2 := by simpa using hcard
    rw [uniformExpectation]
    have hden : (Fintype.card (HalfSample.Slice I 1) : ℝ) = 2 := by
      simp [Fintype.card_finset_len, hcardI]
    rw [hden]
    have hpoint (S : HalfSample.Slice I 1) :
        (HalfSample.sliceSum a S) ^ 2 ≤ K ^ 2 := by
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp S.2
      simp [HalfSample.sliceSum, hi]
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (a i)) hK).2 (ha i)
    have hsumle := Finset.sum_le_sum (fun S (_ : S ∈ (Finset.univ :
        Finset (HalfSample.Slice I 1))) ↦ hpoint S)
    have hsumle' : (∑ S : HalfSample.Slice I 1,
        (HalfSample.sliceSum a S)^2) ≤
        (Fintype.card (HalfSample.Slice I 1) : ℝ) * K^2 := by
      simpa using hsumle
    rw [hden] at hsumle'
    norm_num at hs ⊢
    linarith
  · have hs2 : 2 ≤ s := by omega
    rw [uniformExpectation, sum_sliceSum_sq_exact hs2 a hsum]
    rw [Fintype.card_finset_len, hcard]
    have hchoosePos : 0 < (2 * s).choose s := Nat.choose_pos (by omega)
    have hc2nonneg : (0 : ℝ) ≤ ((2 * s - 2).choose (s - 2) : ℝ) := by positivity
    have hsquares : (∑ i, (a i)^2) ≤ (2 * s : ℝ) * K^2 := by
      calc
        (∑ i, (a i)^2) ≤ ∑ _i : I, K^2 := by
          apply Finset.sum_le_sum
          intro i _
          simpa only [sq_abs] using
            (sq_le_sq₀ (abs_nonneg (a i)) hK).2 (ha i)
        _ = (Fintype.card I : ℝ) * K^2 := by simp
        _ = (2 * s : ℝ) * K^2 := by rw [hcard]; norm_num
    have hc1ratio :
        (((2 * s - 1).choose (s - 1) : ℝ) /
          ((2 * s).choose s : ℝ)) = (1 : ℝ) / 2 := by
      have hchoose := Nat.choose_mul (n := 2 * s) (k := s) (s := 1) hs
      norm_num at hchoose
      have hreal : ((2 * s).choose s : ℝ) * s =
          (2 * s : ℝ) * ((2 * s - 1).choose (s - 1) : ℝ) := by
        exact_mod_cast hchoose
      field_simp [Nat.ne_of_gt hchoosePos]
      nlinarith [show (0 : ℝ) < s by exact_mod_cast hs]
    calc
      ((((2 * s - 1).choose (s - 1) : ℝ) -
          ((2 * s - 2).choose (s - 2) : ℝ)) * ∑ i, (a i)^2) /
          ((2 * s).choose s : ℝ) ≤
        (((2 * s - 1).choose (s - 1) : ℝ) * ∑ i, (a i)^2) /
          ((2 * s).choose s : ℝ) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right (sub_le_self _ hc2nonneg)
              (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
      _ = ((1 : ℝ) / 2) * ∑ i, (a i)^2 := by
        rw [mul_div_assoc]
        calc
          ((2 * s - 1).choose (s - 1) : ℝ) *
              ((∑ i, a i ^ 2) / ((2 * s).choose s : ℝ)) =
              (((2 * s - 1).choose (s - 1) : ℝ) /
                ((2 * s).choose s : ℝ)) * (∑ i, a i^2) := by ring
          _ = _ := by rw [hc1ratio]
      _ ≤ (1 / 2 : ℝ) * ((2 * s : ℝ) * K^2) := by gcongr
      _ = (s : ℝ) * K^2 := by ring

/-- Affine form of the half-slice second-moment bound.  If the deterministic
offset is at most `R √s`, the second moment of the affine statistic is at
most `(K² + R²)s`. -/
theorem uniformExpectation_add_sliceSum_sq_le
    {I : Type u} [Fintype I] [DecidableEq I]
    {s : ℕ} (hcard : Fintype.card I = 2 * s) (hs : 0 < s)
    (a : I → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (ha : ∀ i, |a i| ≤ K) (hsum : ∑ i, a i = 0)
    (offset R : ℝ) (hR : 0 ≤ R)
    (hoffset : |offset| ≤ R * Real.sqrt s) :
    uniformExpectation (fun S : HalfSample.Slice I s ↦
      (offset + HalfSample.sliceSum a S) ^ 2) ≤
        (K ^ 2 + R ^ 2) * s := by
  classical
  let _ := HalfSample.sliceNonempty hcard
  have hmean : uniformExpectation
      (fun S : HalfSample.Slice I s ↦ HalfSample.sliceSum a S) = 0 := by
    change HalfSample.sliceExpectation hcard a = 0
    rw [HalfSample.sliceExpectation_eq_half_total, hsum]
    norm_num
  have hsquare := uniformExpectation_sliceSum_sq_le
    hcard hs a K hK ha hsum
  have hmul : uniformExpectation
      (fun S : HalfSample.Slice I s ↦
        (2 * offset) * HalfSample.sliceSum a S) =
      (2 * offset) * uniformExpectation
        (fun S : HalfSample.Slice I s ↦ HalfSample.sliceSum a S) := by
    have hsum : (∑ S : HalfSample.Slice I s,
        (2 * offset) * HalfSample.sliceSum a S) =
        (2 * offset) * ∑ S : HalfSample.Slice I s,
          HalfSample.sliceSum a S := by
      symm
      rw [Finset.mul_sum]
    simp only [uniformExpectation]
    rw [hsum]
    ring
  have hexpand : uniformExpectation (fun S : HalfSample.Slice I s ↦
      (offset + HalfSample.sliceSum a S) ^ 2) =
      offset ^ 2 + uniformExpectation (fun S : HalfSample.Slice I s ↦
        (HalfSample.sliceSum a S) ^ 2) := by
    calc
      uniformExpectation (fun S : HalfSample.Slice I s ↦
          (offset + HalfSample.sliceSum a S) ^ 2) =
          uniformExpectation (fun S : HalfSample.Slice I s ↦
            offset ^ 2 + (2 * offset) * HalfSample.sliceSum a S +
              (HalfSample.sliceSum a S) ^ 2) := by
            congr 1
            funext S
            ring
      _ = offset ^ 2 + (2 * offset) *
            uniformExpectation
              (fun S : HalfSample.Slice I s ↦ HalfSample.sliceSum a S) +
            uniformExpectation (fun S : HalfSample.Slice I s ↦
              (HalfSample.sliceSum a S) ^ 2) := by
            rw [uniformExpectation_add, uniformExpectation_add,
              uniformExpectation_const, hmul]
      _ = _ := by rw [hmean]; ring
  have hsnonneg : (0 : ℝ) ≤ s := by positivity
  have hsqrt : 0 ≤ R * Real.sqrt s :=
    mul_nonneg hR (Real.sqrt_nonneg _)
  have hoffsetSq : offset ^ 2 ≤ R ^ 2 * s := by
    have hsq := (sq_le_sq₀ (abs_nonneg offset) hsqrt).2 hoffset
    rw [sq_abs, mul_pow, Real.sq_sqrt hsnonneg] at hsq
    exact hsq
  rw [hexpand]
  calc
    offset ^ 2 + uniformExpectation (fun S : HalfSample.Slice I s ↦
        (HalfSample.sliceSum a S) ^ 2) ≤
        R ^ 2 * s + (s : ℝ) * K ^ 2 := add_le_add hoffsetSq hsquare
    _ = (K ^ 2 + R ^ 2) * s := by ring

/-- Sharp affine second-moment bound without a zero-total assumption.  The
deterministic hypothesis is imposed on the actual mean: a half-slice has
mean one half of the full coefficient sum. -/
theorem uniformExpectation_add_sliceSum_sq_le_of_mean
    {I : Type u} [Fintype I] [DecidableEq I]
    {s : ℕ} (hcard : Fintype.card I = 2 * s) (hs : 2 ≤ s)
    (a : I → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (ha : ∀ i, |a i| ≤ K)
    (offset R : ℝ) (hR : 0 ≤ R)
    (hoffsetMean : |offset + (∑ i, a i) / 2| ≤
      R * Real.sqrt s) :
    uniformExpectation (fun S : HalfSample.Slice I s ↦
      (offset + HalfSample.sliceSum a S) ^ 2) ≤
        (K ^ 2 + R ^ 2) * s := by
  classical
  let _ := HalfSample.sliceNonempty hcard
  let mu : ℝ := (∑ i, a i) / (2 * s : ℝ)
  let b : I → ℝ := fun i ↦ a i - mu
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hcardR : (Fintype.card I : ℝ) = 2 * s := by
    exact_mod_cast hcard
  have hmu : (2 * s : ℝ) * mu = ∑ i, a i := by
    dsimp [mu]
    field_simp
  have hbsum : ∑ i, b i = 0 := by
    simp only [b, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [show (Finset.univ : Finset I).card = Fintype.card I by simp,
      hcardR, hmu]
    ring
  have haSquares : (∑ i, (a i) ^ 2) ≤ (2 * s : ℝ) * K ^ 2 := by
    calc
      (∑ i, (a i) ^ 2) ≤ ∑ _i : I, K ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg (a i)) hK).2 (ha i)
      _ = (Fintype.card I : ℝ) * K ^ 2 := by simp
      _ = (2 * s : ℝ) * K ^ 2 := by rw [hcardR]
  have hcross : (∑ i, 2 * mu * b i) = 0 := by
    rw [← Finset.mul_sum, hbsum]
    ring
  have hdecomp : (∑ i, (a i) ^ 2) =
      (∑ i, (b i) ^ 2) + (Fintype.card I : ℝ) * mu ^ 2 := by
    calc
      (∑ i, (a i) ^ 2) = ∑ i, (b i + mu) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [b]
        ring
      _ = ∑ i, ((b i) ^ 2 + 2 * mu * b i + mu ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, (b i) ^ 2) + (Fintype.card I : ℝ) * mu ^ 2 := by
        simp_rw [Finset.sum_add_distrib]
        rw [hcross]
        simp
  have hbSquares : (∑ i, (b i) ^ 2) ≤ (2 * s : ℝ) * K ^ 2 := by
    apply le_trans ?_ haSquares
    rw [hdecomp]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg mu))
  have hsmu : (s : ℝ) * mu = (∑ i, a i) / 2 := by
    dsimp [mu]
    field_simp
  have hslice (S : HalfSample.Slice I s) :
      HalfSample.sliceSum b S = HalfSample.sliceSum a S - (s : ℝ) * mu := by
    simp [HalfSample.sliceSum, b, Finset.sum_sub_distrib, S.2]
  have hcentered := uniformExpectation_add_sliceSum_sq_le_of_sum_sq
    hcard hs b K hbsum hbSquares
      (offset + (∑ i, a i) / 2) R hR hoffsetMean
  calc
    uniformExpectation (fun S : HalfSample.Slice I s ↦
        (offset + HalfSample.sliceSum a S) ^ 2) =
      uniformExpectation (fun S : HalfSample.Slice I s ↦
        (offset + (∑ i, a i) / 2 + HalfSample.sliceSum b S) ^ 2) := by
          congr 1
          funext S
          rw [hslice, hsmu]
          ring
    _ ≤ (K ^ 2 + R ^ 2) * s := hcentered

/-- Positive-size version of `uniformExpectation_add_sliceSum_sq_le_of_mean`.
The exceptional one-point half-slice is handled directly. -/
theorem uniformExpectation_add_sliceSum_sq_le_of_mean_pos
    {I : Type u} [Fintype I] [DecidableEq I]
    {s : ℕ} (hcard : Fintype.card I = 2 * s) (hs : 0 < s)
    (a : I → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (ha : ∀ i, |a i| ≤ K)
    (offset R : ℝ) (hR : 0 ≤ R)
    (hoffsetMean : |offset + (∑ i, a i) / 2| ≤
      R * Real.sqrt s) :
    uniformExpectation (fun S : HalfSample.Slice I s ↦
      (offset + HalfSample.sliceSum a S) ^ 2) ≤
        (K ^ 2 + R ^ 2) * s := by
  classical
  by_cases hs1 : s = 1
  · subst s
    let _ := HalfSample.sliceNonempty hcard
    have hcardI : Fintype.card I = 2 := by simpa using hcard
    have hden : (Fintype.card (HalfSample.Slice I 1) : ℝ) = 2 := by
      simp [Fintype.card_finset_len, hcardI]
    have hpoint (S : HalfSample.Slice I 1) :
        (HalfSample.sliceSum a S) ^ 2 ≤ K ^ 2 := by
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp S.2
      simp [HalfSample.sliceSum, hi]
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (a i)) hK).2 (ha i)
    have hsumle := Finset.sum_le_sum (fun S (_ : S ∈ (Finset.univ :
        Finset (HalfSample.Slice I 1))) ↦ hpoint S)
    have hraw : uniformExpectation (fun S : HalfSample.Slice I 1 ↦
        (HalfSample.sliceSum a S)^2) ≤ K^2 := by
      rw [uniformExpectation, hden]
      have hsumle' : (∑ S : HalfSample.Slice I 1,
          (HalfSample.sliceSum a S)^2) ≤ 2 * K^2 := by
        have hsumle'' : (∑ S : HalfSample.Slice I 1,
            (HalfSample.sliceSum a S)^2) ≤
            (Fintype.card (HalfSample.Slice I 1) : ℝ) * K^2 := by
          simpa using hsumle
        rw [hden] at hsumle''
        exact hsumle''
      linarith
    let m : ℝ := (∑ i, a i) / 2
    have hmean : uniformExpectation
        (fun S : HalfSample.Slice I 1 ↦ HalfSample.sliceSum a S) = m := by
      change HalfSample.sliceExpectation hcard a = m
      rw [HalfSample.sliceExpectation_eq_half_total]
    have hmul : uniformExpectation
        (fun S : HalfSample.Slice I 1 ↦
          (2 * offset) * HalfSample.sliceSum a S) =
        (2 * offset) * uniformExpectation
          (fun S : HalfSample.Slice I 1 ↦ HalfSample.sliceSum a S) := by
      have hsumMul : (∑ S : HalfSample.Slice I 1,
          (2 * offset) * HalfSample.sliceSum a S) =
          (2 * offset) * ∑ S : HalfSample.Slice I 1,
            HalfSample.sliceSum a S := by
        symm
        rw [Finset.mul_sum]
      simp only [uniformExpectation]
      rw [hsumMul]
      ring
    have hexpand : uniformExpectation (fun S : HalfSample.Slice I 1 ↦
        (offset + HalfSample.sliceSum a S) ^ 2) =
        offset ^ 2 + 2 * offset * m +
          uniformExpectation (fun S : HalfSample.Slice I 1 ↦
            (HalfSample.sliceSum a S) ^ 2) := by
      calc
        _ = uniformExpectation (fun S : HalfSample.Slice I 1 ↦
            offset ^ 2 + (2 * offset) * HalfSample.sliceSum a S +
              (HalfSample.sliceSum a S) ^ 2) := by
                congr 1
                funext S
                ring
        _ = offset ^ 2 + (2 * offset) *
              uniformExpectation
                (fun S : HalfSample.Slice I 1 ↦ HalfSample.sliceSum a S) +
              uniformExpectation (fun S : HalfSample.Slice I 1 ↦
                (HalfSample.sliceSum a S) ^ 2) := by
                rw [uniformExpectation_add, uniformExpectation_add,
                  uniformExpectation_const, hmul]
        _ = _ := by rw [hmean]
    have hmeanBound : |offset + m| ≤ R := by
      simpa [m] using hoffsetMean
    have hmeanSq : (offset + m) ^ 2 ≤ R ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (offset + m)) hR).2 hmeanBound
    rw [hexpand]
    calc
      offset ^ 2 + 2 * offset * m +
          uniformExpectation (fun S : HalfSample.Slice I 1 ↦
            (HalfSample.sliceSum a S) ^ 2) ≤
          offset ^ 2 + 2 * offset * m + K^2 := by linarith
      _ = (offset + m)^2 + K^2 - m^2 := by ring
      _ ≤ (offset + m)^2 + K^2 := sub_le_self _ (sq_nonneg m)
      _ ≤ R^2 + K^2 := by gcongr
      _ = (K^2 + R^2) * ((1 : ℕ) : ℝ) := by ring
  · exact uniformExpectation_add_sliceSum_sq_le_of_mean hcard (by omega)
      a K hK ha offset R hR hoffsetMean

end HalfSampleVariance
end Erdos636
