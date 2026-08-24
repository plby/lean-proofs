import ErdosProblems.Erdos587.GAPDefinitions

/-!
Cover a dilated GAP by boundedly many translates of the original GAP.
The cover does not require properness; it is valid after a dilation has
developed collisions, as needed when propagating high-fold growth bounds.
-/

open scoped Pointwise

namespace Erdos587.GeneralizedAP

def dilationCoverShift (P : GeneralizedAP) (n : ℕ) (u : Fin P.rank → Fin n) : ℤ :=
  (n : ℤ) * P.base - P.base +
    ∑ i : Fin P.rank, (u i : ℤ) * ((P.length i : ℤ) + 1) * P.step i

def dilationCoverOffsets (P : GeneralizedAP) (n : ℕ) : Finset ℤ :=
  (Finset.univ : Finset (Fin P.rank → Fin n)).image (P.dilationCoverShift n)

theorem card_dilationCoverOffsets_le (P : GeneralizedAP) (n : ℕ) :
    (P.dilationCoverOffsets n).card ≤ n ^ P.rank := by
  calc
    (P.dilationCoverOffsets n).card ≤
        (Finset.univ : Finset (Fin P.rank → Fin n)).card := Finset.card_image_le
    _ = n ^ P.rank := by simp

/-- Quotients by the side cardinalities index the translated boxes. -/
def dilationCoverIndex (P : GeneralizedAP) {n : ℕ} (hn : 0 < n)
    (x : (P.dilate n).Param) : Fin P.rank → Fin n := fun i =>
  ⟨(x i : ℕ) / (P.length i + 1), by
    apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).mpr
    have hx : (x i : ℕ) ≤ n * P.length i := Nat.le_of_lt_succ (x i).isLt
    nlinarith⟩

def dilationCoverRemainder (P : GeneralizedAP) {n : ℕ}
    (x : (P.dilate n).Param) : P.Param := fun i =>
  ⟨(x i : ℕ) % (P.length i + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem eval_dilationCover (P : GeneralizedAP) {n : ℕ} (hn : 0 < n)
    (x : (P.dilate n).Param) :
    P.dilationCoverShift n (P.dilationCoverIndex hn x) +
      P.eval (P.dilationCoverRemainder x) = (P.dilate n).eval x := by
  have hcoord (i : Fin P.rank) :
      ((P.dilationCoverIndex hn x i : ℕ) * (P.length i + 1) +
        (P.dilationCoverRemainder x i : ℕ)) = (x i : ℕ) := by
    change (x i : ℕ) / (P.length i + 1) * (P.length i + 1) +
      (x i : ℕ) % (P.length i + 1) = (x i : ℕ)
    simpa only [Nat.mul_comm] using Nat.div_add_mod (x i : ℕ) (P.length i + 1)
  have hsum :
      (∑ i : Fin P.rank,
        (P.dilationCoverIndex hn x i : ℤ) * ((P.length i : ℤ) + 1) * P.step i) +
      (∑ i : Fin P.rank, (P.dilationCoverRemainder x i : ℤ) * P.step i) =
      ∑ i : Fin P.rank, (x i : ℤ) * P.step i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hc : (P.dilationCoverIndex hn x i : ℤ) * ((P.length i : ℤ) + 1) +
        (P.dilationCoverRemainder x i : ℤ) = (x i : ℤ) := by exact_mod_cast hcoord i
    calc
      _ = ((P.dilationCoverIndex hn x i : ℤ) * ((P.length i : ℤ) + 1) +
          (P.dilationCoverRemainder x i : ℤ)) * P.step i := by ring
      _ = (x i : ℤ) * P.step i := by rw [hc]
  change ((n : ℤ) * P.base - P.base +
      (∑ i : Fin P.rank,
        (P.dilationCoverIndex hn x i : ℤ) * ((P.length i : ℤ) + 1) * P.step i)) +
      (P.base + ∑ i : Fin P.rank, (P.dilationCoverRemainder x i : ℤ) * P.step i) =
    (n : ℤ) * P.base + ∑ i : Fin P.rank, (x i : ℤ) * P.step i
  linear_combination hsum

theorem carrier_dilate_subset_offsets_add (P : GeneralizedAP) {n : ℕ} (hn : 0 < n) :
    (P.dilate n).carrier ⊆ P.dilationCoverOffsets n + P.carrier := by
  intro z hz
  obtain ⟨x, rfl⟩ := (P.dilate n).mem_carrier_iff.mp hz
  apply Finset.mem_add.mpr
  refine ⟨P.dilationCoverShift n (P.dilationCoverIndex hn x), ?_,
    P.eval (P.dilationCoverRemainder x), ?_, P.eval_dilationCover hn x⟩
  · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · exact P.mem_carrier_iff.mpr ⟨_, rfl⟩

/-- Dilation has at most polynomial cardinality growth, including for
nonproper GAPs. -/
theorem card_dilate_le_pow_mul_card (P : GeneralizedAP) {n : ℕ} (hn : 0 < n) :
    (P.dilate n).carrier.card ≤ n ^ P.rank * P.carrier.card := by
  calc
    (P.dilate n).carrier.card ≤ (P.dilationCoverOffsets n + P.carrier).card :=
      Finset.card_le_card (P.carrier_dilate_subset_offsets_add hn)
    _ ≤ (P.dilationCoverOffsets n).card * P.carrier.card := Finset.card_add_le
    _ ≤ n ^ P.rank * P.carrier.card :=
      Nat.mul_le_mul_right _ (P.card_dilationCoverOffsets_le n)

theorem card_dilate_mul_le_pow_mul_card_dilate (P : GeneralizedAP)
    (h : ℕ) {n : ℕ} (hn : 0 < n) :
    (P.dilate (n * h)).carrier.card ≤ n ^ P.rank * (P.dilate h).carrier.card := by
  simpa only [dilate_dilate, rank_dilate] using (P.dilate h).card_dilate_le_pow_mul_card hn

end Erdos587.GeneralizedAP
