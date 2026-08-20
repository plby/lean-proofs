import ErdosProblems.Erdos733.ST.Preamble
import Mathlib.Algebra.BigOperators.Ring.Finset

open Classical
noncomputable section

-- [TABLET NODE: FinitePowersetBernoulliFamilyMoment]
lemma FinitePowersetBernoulliFamilyMoment {α ι : Type*}
    (S : Finset α) (I : Finset ι) (support : ι → Finset α)
    (hsupport : ∀ i ∈ I, support i ⊆ S) (p : ℝ) :
    ∑ X ∈ S.powerset,
        p ^ X.card * (1 - p) ^ (S \ X).card *
          ((I.filter fun i => support i ⊆ X).card : ℝ) =
      ∑ i ∈ I, p ^ (support i).card := by
-- BODY
  classical
  calc
    (∑ X ∈ S.powerset,
        p ^ X.card * (1 - p) ^ (S \ X).card *
          ((I.filter fun i => support i ⊆ X).card : ℝ)) =
        ∑ X ∈ S.powerset,
          ∑ i ∈ I,
            if support i ⊆ X then
              p ^ X.card * (1 - p) ^ (S \ X).card
            else 0 := by
      apply Finset.sum_congr rfl
      intro X _hX
      rw [Finset.natCast_card_filter]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      split_ifs <;> ring
    _ = ∑ i ∈ I,
          ∑ X ∈ S.powerset,
            if support i ⊆ X then
              p ^ X.card * (1 - p) ^ (S \ X).card
            else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ I, p ^ (support i).card := by
      apply Finset.sum_congr rfl
      intro i hi
      have hexpand := Finset.prod_add
        (fun _ : α => p)
        (fun a : α => if a ∈ support i then 0 else 1 - p) S
      calc
        (∑ X ∈ S.powerset,
            if support i ⊆ X then
              p ^ X.card * (1 - p) ^ (S \ X).card
            else 0) =
            ∑ X ∈ S.powerset,
              (∏ _a ∈ X, p) *
                ∏ a ∈ S \ X,
                  (if a ∈ support i then 0 else 1 - p) := by
          apply Finset.sum_congr rfl
          intro X hX
          have hXS : X ⊆ S := Finset.mem_powerset.mp hX
          split_ifs with hsupportX
          · congr 1
            · exact (Finset.prod_const p).symm
            symm
            apply Finset.prod_eq_pow_card
            intro a ha
            simp only [Finset.mem_sdiff] at ha
            have haNotSupport : a ∉ support i :=
              fun haSupport => ha.2 (hsupportX haSupport)
            rw [if_neg haNotSupport]
          · obtain ⟨a, haSupport, haX⟩ :
                ∃ a, a ∈ support i ∧ a ∉ X := by
              simpa [Finset.subset_iff] using hsupportX
            have haSX : a ∈ S \ X :=
              Finset.mem_sdiff.mpr ⟨hsupport i hi haSupport, haX⟩
            have haZero :
                (if a ∈ support i then (0 : ℝ) else 1 - p) = 0 :=
              if_pos haSupport
            rw [Finset.prod_eq_zero haSX haZero]
            simp
        _ = ∏ a ∈ S,
              (p + if a ∈ support i then 0 else 1 - p) :=
          hexpand.symm
        _ = ∏ a ∈ support i,
              (p + if a ∈ support i then 0 else 1 - p) := by
          symm
          apply Finset.prod_subset (hsupport i hi)
          intro a _haS haSupport
          rw [if_neg haSupport]
          ring
        _ = p ^ (support i).card := by
          apply Finset.prod_eq_pow_card
          intro a haSupport
          rw [if_pos haSupport]
          ring
