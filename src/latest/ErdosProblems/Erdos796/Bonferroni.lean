import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A finite pairwise-overlap bound

This is the coarse Bonferroni inequality used for the semiprime fibres.  If
every two distinct members of a finite family intersect in at most `K`
points, then the sum of their cardinalities exceeds the cardinality of their
union by at most the square of the number of fibres times `K`.
-/

namespace Erdos796

open scoped BigOperators

theorem card_inter_biUnion_le_card_mul
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (S : Finset ι) (F : ι → Finset α) (a : ι) (K : ℕ)
    (hpair : ∀ j ∈ S, (F a ∩ F j).card ≤ K) :
    (F a ∩ S.biUnion F).card ≤ S.card * K := by
  have hsub : F a ∩ S.biUnion F ⊆ S.biUnion fun j => F a ∩ F j := by
    intro x hx
    have hx' := Finset.mem_inter.mp hx
    rcases Finset.mem_biUnion.mp hx'.2 with ⟨j, hj, hxj⟩
    exact Finset.mem_biUnion.mpr
      ⟨j, hj, Finset.mem_inter.mpr ⟨hx'.1, hxj⟩⟩
  calc
    (F a ∩ S.biUnion F).card ≤
        (S.biUnion fun j => F a ∩ F j).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ S, (F a ∩ F j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ S, K := by
      apply Finset.sum_le_sum
      intro j hj
      exact hpair j hj
    _ = S.card * K := by simp

/-- Coarse finite Bonferroni inequality with a uniform pairwise-intersection
bound. -/
theorem sum_card_le_card_biUnion_add_sq_mul
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (S : Finset ι) (F : ι → Finset α) (K : ℕ)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (F i ∩ F j).card ≤ K) :
    ∑ i ∈ S, (F i).card ≤ (S.biUnion F).card + S.card ^ 2 * K := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      have hpairS :
          ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (F i ∩ F j).card ≤ K := by
        intro i hi j hj hij
        exact hpair i (Finset.mem_insert_of_mem hi)
          j (Finset.mem_insert_of_mem hj) hij
      have hih := ih hpairS
      have hinter : (F a ∩ S.biUnion F).card ≤ S.card * K := by
        apply card_inter_biUnion_le_card_mul
        intro j hj
        exact hpair a (Finset.mem_insert_self a S)
          j (Finset.mem_insert_of_mem hj) (by aesop)
      have hunion := Finset.card_union_add_card_inter (F a) (S.biUnion F)
      rw [Finset.sum_insert ha, Finset.biUnion_insert,
        Finset.card_insert_of_notMem ha]
      nlinarith [hih, hinter, hunion]

end Erdos796
