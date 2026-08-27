import Arxiv.Arxiv2411_18291.CliqueFamilyLowerDegrees
import Arxiv.Arxiv2411_18291.CliqueSupportBounds

/-! # Boundary degrees after refining a family of larger cliques

No disjointness is needed: repeated refined cliques only decrease the
boundary of the resulting set.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V] {q r k : ℕ}

theorem cliqueRefinement_face_card_le (Z : I → Block V k) (S : Finset V)
    (hS : S.card ≤ q) :
    ((cliqueRefinement q (univ.image Z)).filter fun Q => S ⊆ Q.val).card ≤
      (k - S.card).choose (q - S.card) * familyDegree Z S := by
  classical
  let A : I → Finset (Block V q) := fun i =>
    univ.filter fun Q => S ⊆ Q.val ∧ Q.val ⊆ (Z i).val
  have hsub : ((cliqueRefinement q (univ.image Z)).filter fun Q => S ⊆ Q.val) ⊆
      univ.biUnion A := by
    intro Q hQ
    obtain ⟨Y, hY, hQY⟩ := (mem_cliqueRefinement _ Q).mp (mem_filter.mp hQ).1
    obtain ⟨i, _, rfl⟩ := mem_image.mp hY
    exact mem_biUnion.mpr ⟨i, mem_univ _,
      mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hQ).2, hQY⟩⟩
  have hc (i : I) : (A i).card =
      if S ⊆ (Z i).val then (k - S.card).choose (q - S.card) else 0 := by
    dsimp only [A]
    by_cases hSZ : S ⊆ (Z i).val
    · rw [if_pos hSZ, card_blocks_between S (Z i).val hSZ hS, (Z i).property]
    · rw [if_neg hSZ, card_eq_zero]
      exact eq_empty_iff_forall_notMem.mpr fun Q hQ =>
        hSZ ((mem_filter.mp hQ).2.1.trans (mem_filter.mp hQ).2.2)
  calc
    _ ≤ (univ.biUnion A).card := card_le_card hsub
    _ ≤ ∑ i, (A i).card := card_biUnion_le
    _ = _ := by
      simp only [hc, familyDegree, ← sum_filter, sum_const, nsmul_eq_mul]
      exact Nat.mul_comm _ _

theorem cliqueRefinement_bounded_of_face_bound (Z : I → Block V k)
    (hrq : r < q) (hqk : q ≤ k) {L : ℝ}
    (hZ : ∀ S : Block V r, (familyDegree Z S.val : ℝ) < L * Fintype.card V) :
    IsCliqueFamilyBounded r (cliqueRefinement q (univ.image Z))
      ((q - r : ℕ) * (k - r).choose (q - r) * L) := by
  intro S
  rw [degree_boundary _ S.val (by rw [S.property]; omega), degree_indicator,
    S.property, Nat.add_sub_cancel_left, Nat.choose_one_right]
  push_cast
  have hq : (0 : ℝ) < (q - r : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hrq
  have hk : (0 : ℝ) < (k - r).choose (q - r) := by
    exact_mod_cast Nat.choose_pos (Nat.sub_le_sub_right hqk r)
  have hcard :
      (((cliqueRefinement q (univ.image Z)).filter fun Q => S.val ⊆ Q.val).card : ℝ) ≤
        ((k - r).choose (q - r) : ℝ) * familyDegree Z S.val := by
    exact_mod_cast (by simpa only [S.property] using
      cliqueRefinement_face_card_le (q := q) Z S.val (by rw [S.property]; omega))
  calc
    _ ≤ (q - r : ℕ) * (((k - r).choose (q - r) : ℝ) * familyDegree Z S.val) :=
      mul_le_mul_of_nonneg_left hcard hq.le
    _ < (q - r : ℕ) * (((k - r).choose (q - r) : ℝ) * (L * Fintype.card V)) :=
      mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left (hZ S) hk) hq
    _ = _ := by ring

theorem cliqueImage_bounded_of_face_bound (Z : I → Block V q)
    (hrq : r < q) {L : ℝ}
    (hZ : ∀ S : Block V r, (familyDegree Z S.val : ℝ) < L * Fintype.card V) :
    IsCliqueFamilyBounded r (univ.image Z) ((q - r : ℕ) * L) := by
  have h := cliqueRefinement_bounded_of_face_bound Z hrq le_rfl hZ
  simp only [Nat.choose_self, Nat.cast_one, mul_one] at h
  apply h.subfamily
  intro Q hQ
  exact (mem_cliqueRefinement _ Q).mpr ⟨Q, hQ, Subset.refl _⟩

end Arxiv2411_18291
