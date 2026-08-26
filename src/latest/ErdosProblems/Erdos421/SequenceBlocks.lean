import ErdosProblems.Erdos421.ParentForest

/-! # Index intervals for blocks in the final increasing sequence -/

namespace Erdos421

theorem IsSetBlock.exists_image_Icc {d : ℕ → ℕ} (hd : StrictMono d)
    {E : Finset ℕ} (hE : IsSetBlock (Set.range d) E) :
    ∃ u v, u ≤ v ∧ E = (Finset.Icc u v).image d := by
  let a := E.min' hE.nonempty
  let b := E.max' hE.nonempty
  have ha : a ∈ E := E.min'_mem hE.nonempty
  have hb : b ∈ E := E.max'_mem hE.nonempty
  obtain ⟨u, hu⟩ := hE.subset a ha
  obtain ⟨v, hv⟩ := hE.subset b hb
  have huv : u ≤ v := hd.le_iff_le.mp (by rw [hu, hv]; exact E.min'_le b hb)
  refine ⟨u, v, huv, Finset.Subset.antisymm ?_ ?_⟩
  · intro e he
    obtain ⟨i, hi⟩ := hE.subset e he
    refine Finset.mem_image.mpr ⟨i, Finset.mem_Icc.mpr ⟨?_, ?_⟩, hi⟩
    · apply hd.le_iff_le.mp
      rw [hu, hi]
      exact E.min'_le e he
    · apply hd.le_iff_le.mp
      rw [hv, hi]
      exact E.le_max' e he
  · intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hui, hiv⟩ := Finset.mem_Icc.mp hi
    apply hE.convex ha hb ⟨i, rfl⟩
    · rw [← hu]
      exact hd.monotone hui
    · rw [← hv]
      exact hd.monotone hiv

theorem IsSetBlock.exists_start {d : ℕ → ℕ} (hd : StrictMono d)
    {E : Finset ℕ} (hE : IsSetBlock (Set.range d) E) :
    ∃ u, E = (Finset.Ico u (u + E.card)).image d := by
  obtain ⟨u, v, huv, hEq⟩ := hE.exists_image_Icc hd
  have hcard : E.card = v + 1 - u := by
    rw [hEq, Finset.card_image_of_injective _ hd.injective, Nat.card_Icc]
  refine ⟨u, ?_⟩
  have hv : u + E.card = v + 1 := by omega
  rw [hv, Finset.Ico_add_one_right_eq_Icc]
  exact hEq

theorem RejectedWitness.later_card {k : ℕ} (w : RejectedWitness k) :
    (Finset.Icc w.m w.n).card = w.n - w.m + 1 := by
  rw [Nat.card_Icc]
  have := w.later_nonempty
  omega

theorem RejectedWitness.later_length_le_scale {k u : ℕ} (w : RejectedWitness k)
    (hshort : ShortGap k) (hB : prime (k + 1) ≤ 2 ^ (60 * u)) :
    w.n - w.m + 1 ≤ 2 ^ (3 * u) := by
  apply le_trans _ (hshort.length_le_scale hB)
  unfold gapLength
  have := w.gap_left
  have := w.gap_right
  have := w.later_nonempty
  omega

theorem RejectedWitness.length_le_scale {k u : ℕ} (w : RejectedWitness k)
    (hshort : ShortGap k) (hB : prime (k + 1) ≤ 2 ^ (60 * u)) (hu : 10 ≤ u) :
    w.E.card ≤ 2 ^ (4 * u) := by
  have hs := w.later_length_le_scale hshort hB
  have htwo : ∀ e ∈ w.E, 2 ≤ e := by
    intro e he
    rcases Finset.mem_union.mp (w.earlier_block.subset he) with h | h
    · exact (stage_bounds k e h).1
    · exact (prime_prime k).two_le.trans (Finset.mem_Ioc.mp h).1.le
  have hpower := witness_power_bound htwo
    (by
      intro t ht
      exact ((Finset.mem_Icc.mp ht).2.trans w.gap_right.le).trans hB) w.product_eq
  rw [w.later_card, ← pow_mul] at hpower
  have hr : w.E.card ≤ (60 * u) * (w.n - w.m + 1) :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpower
  calc
    w.E.card ≤ (60 * u) * 2 ^ (3 * u) := hr.trans (Nat.mul_le_mul_left _ hs)
    _ ≤ 2 ^ u * 2 ^ (3 * u) := Nat.mul_le_mul_right _ (sixty_mul_le_two_pow hu)
    _ = 2 ^ (4 * u) := by rw [← pow_add]; congr 1; omega

end Erdos421
