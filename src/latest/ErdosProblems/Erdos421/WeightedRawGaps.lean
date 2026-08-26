import ErdosProblems.Erdos421.ChildEncoding
import ErdosProblems.Erdos421.WitnessLengths

/-! # Raw witnesses counted with reciprocal gap-length weights -/

namespace Erdos421

theorem intervalSolutions_card_bound_cube (B r s T : ℕ) (hs : 0 < s) (hrs : s < r)
    (hT : 0 < T) (hB : B ≤ T ^ 3) :
    (intervalSolutions B r s).card ≤ 3 * T ^ 2 + 1 + 2 * r ^ 2 := by
  have h := intervalSolutions_card_bound B r s T hs hrs
  have hmul : T * (intervalSolutions B r s).card ≤ T * (3 * T ^ 2 + 1 + 2 * r ^ 2) := by
    nlinarith
  exact Nat.le_of_mul_le_mul_left hmul hT

theorem lengthPairs_reciprocal_sum_le (L C : ℕ) :
    (∑ p ∈ lengthPairs L, (C : ℝ) / p.1) ≤ (C : ℝ) * L := by
  have hinner : ∀ r ∈ Finset.Icc 1 L,
      (∑ s ∈ Finset.Icc 1 L, if s < r then (C : ℝ) / r else 0) ≤ C := by
    intro r hr
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (Finset.mem_Icc.mp hr).1
    let F := (Finset.Icc 1 L).filter (fun s ↦ s < r)
    have hsub : F ⊆ Finset.range r := fun s hs ↦ Finset.mem_range.mpr (Finset.mem_filter.mp hs).2
    have hcard : (F.card : ℝ) ≤ r := by
      exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range r)
    have heq : (∑ s ∈ Finset.Icc 1 L, if s < r then (C : ℝ) / r else 0) =
        F.card * ((C : ℝ) / r) := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, F]
    rw [heq]
    calc
      _ ≤ (r : ℝ) * ((C : ℝ) / r) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = C := by field_simp
  have hsum := Finset.sum_le_sum hinner
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel] at hsum
  unfold lengthPairs
  rw [Finset.sum_filter, Finset.sum_product]
  simpa only [mul_comm] using hsum

theorem allIntervalSolutions_weight_sum_le (B L T C : ℕ) (hT : 0 < T) (hB : B ≤ T ^ 3) :
    (∑ c ∈ allIntervalSolutions B L, (C : ℝ) / c.1.1) ≤
      (C : ℝ) * L * (3 * T ^ 2 + 1 + 2 * L ^ 2 : ℕ) := by
  let D := 3 * T ^ 2 + 1 + 2 * L ^ 2
  have hcard : ∀ p ∈ lengthPairs L, (intervalSolutions B p.1 p.2).card ≤ D := by
    intro p hp
    obtain ⟨hp, hrs⟩ := Finset.mem_filter.mp hp
    obtain ⟨hr, hs⟩ := Finset.mem_product.mp hp
    have h := intervalSolutions_card_bound_cube B p.1 p.2 T
      (Finset.mem_Icc.mp hs).1 hrs hT hB
    have hsq := Nat.pow_le_pow_left (Finset.mem_Icc.mp hr).2 2
    dsimp only [D]
    omega
  calc
    _ = ∑ p ∈ lengthPairs L, (intervalSolutions B p.1 p.2).card * ((C : ℝ) / p.1) := by
      simp only [allIntervalSolutions, Finset.sum_sigma, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ lengthPairs L, (D : ℝ) * ((C : ℝ) / p.1) := by
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard p hp
    _ = (D : ℝ) * (∑ p ∈ lengthPairs L, (C : ℝ) / p.1) := (Finset.mul_sum ..).symm
    _ ≤ (D : ℝ) * ((C : ℝ) * L) :=
      mul_le_mul_of_nonneg_left (lengthPairs_reciprocal_sum_le L C) (Nat.cast_nonneg D)
    _ = _ := by ring

/-- A weighted raw-root estimate. The only scale hypothesis is an endpoint
bound, and the gap threshold `H` is arbitrary. -/
theorem raw_reciprocal_sum_bound (I : Finset ℕ) (K H T : ℕ)
    (hI : ∀ k ∈ I, Raw k ∧ prime (k + 1) ≤ 2 ^ K ∧ gapLength k ≤ H)
    (hT : 0 < T) (hB : 2 ^ K ≤ T ^ 3) :
    (∑ k ∈ I, (1 : ℝ) / gapLength k) ≤
      (K : ℝ) * (K * H : ℕ) * (3 * T ^ 2 + 1 + 2 * (K * H) ^ 2 : ℕ) := by
  classical
  let S := allIntervalSolutions (2 ^ K) (K * H)
  let w : (k : I) → RawWitness k := fun k ↦ Classical.choice (hI k k.property).1.2
  have hL : ∀ k : I, (w k).earlierLength ≤ K * H := fun k ↦
    ((w k).length_le_log_mul_gap (hI k k.property).2.1).trans
      (Nat.mul_le_mul_left _ (hI k k.property).2.2)
  let code : I → S := fun k ↦ ⟨(w k).code, (w k).code_mem (hI k k.property).2.1 (hL k)⟩
  have hinj : Function.Injective code := by
    intro i j hij
    have hm : (w i).m = (w j).m := congrArg (fun c : S ↦ c.val.2.2) hij
    apply Subtype.ext
    apply prime_gap_index_unique (w i).gap_left ((w i).later_nonempty.trans_lt (w i).gap_right)
    · rw [hm]
      exact (w j).gap_left
    · rw [hm]
      exact (w j).later_nonempty.trans_lt (w j).gap_right
  have hpoint : ∀ k : I, (1 : ℝ) / gapLength k ≤ K / (code k).val.1.1 := by
    intro k
    change (1 : ℝ) / gapLength k ≤ K / (w k).earlierLength
    have hg : (0 : ℝ) < gapLength k := by exact_mod_cast gapLength_pos k
    have hr : (0 : ℝ) < (w k).earlierLength := by
      exact_mod_cast (w k).laterLength_pos.trans (w k).length_lt
    apply (div_le_div_iff₀ hg hr).mpr
    simpa only [one_mul] using
      (show ((w k).earlierLength : ℝ) ≤ K * gapLength k by
        exact_mod_cast (w k).length_le_log_mul_gap (hI k k.property).2.1)
  have hbound : (∑ k : I, (1 : ℝ) / gapLength k) ≤
      (K : ℝ) * (K * H : ℕ) * (3 * T ^ 2 + 1 + 2 * (K * H) ^ 2 : ℕ) := by
    calc
      _ ≤ ∑ k : I, (K : ℝ) / (code k).val.1.1 := Finset.sum_le_sum (fun k _ ↦ hpoint k)
      _ ≤ ∑ c : S, (K : ℝ) / c.val.1.1 :=
        sum_weight_le_of_injective code hinj (fun c : S ↦ (K : ℝ) / c.val.1.1)
          (fun _ ↦ by positivity)
      _ = ∑ c ∈ S, (K : ℝ) / c.1.1 :=
        Finset.sum_coe_sort S (fun c : IntervalWitnessCode ↦ (K : ℝ) / c.1.1)
      _ ≤ _ := allIntervalSolutions_weight_sum_le (2 ^ K) (K * H) T K hT hB
  rwa [Finset.sum_coe_sort I (fun k : ℕ ↦ (1 : ℝ) / gapLength k)] at hbound

end Erdos421
