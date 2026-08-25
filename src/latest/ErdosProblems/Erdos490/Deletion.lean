import ErdosProblems.Erdos490.Basic

noncomputable section

namespace Erdos490

open Finset BigOperators

def WeightRegular (w : ℕ → ℝ) (S : Finset ℕ) : Prop :=
  ∀ k, ∀ p ∈ I_layer 2 k, 0 < w k → (sdiv S p).Nonempty →
    w k * S.card < (sdiv S p).card

def weightTotal (w : ℕ → ℝ) : ℝ := ∑' k, w k * (N_layer 2 k : ℝ)

def activeWeight (w : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  ∑' k, w k * ((I_layer 2 k).filter (fun p => (sdiv S p).Nonempty)).card

lemma activeWeight_summable (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hs : Summable (fun k => w k * (N_layer 2 k : ℝ))) (S : Finset ℕ) :
    Summable (fun k => w k * ((I_layer 2 k).filter (fun p => (sdiv S p).Nonempty)).card) := by
  apply hs.of_nonneg_of_le
  · intro k
    exact mul_nonneg (hw k) (Nat.cast_nonneg _)
  · intro k
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_filter_le _ _)) (hw k)

lemma activeWeight_nonneg (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k) (S : Finset ℕ) :
    0 ≤ activeWeight w S := by
  exact tsum_nonneg fun k => mul_nonneg (hw k) (Nat.cast_nonneg _)

lemma activeWeight_le_total (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hs : Summable (fun k => w k * (N_layer 2 k : ℝ))) (S : Finset ℕ) :
    activeWeight w S ≤ weightTotal w := by
  apply Summable.tsum_le_tsum _ (activeWeight_summable w hw hs S) hs
  intro k
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_filter_le _ _)) (hw k)

lemma activeWeight_delete (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hs : Summable (fun k => w k * (N_layer 2 k : ℝ)))
    (S : Finset ℕ) (k p : ℕ) (hp : p ∈ I_layer 2 k) (hne : (sdiv S p).Nonempty) :
    activeWeight w (S \ sdiv S p) + w k ≤ activeWeight w S := by
  have hsub (j : ℕ) :
      (I_layer 2 j).filter (fun q => (sdiv (S \ sdiv S p) q).Nonempty) ⊆
        (I_layer 2 j).filter (fun q => (sdiv S q).Nonempty) := by
    intro q hq
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hq).1, sdiv_sdiff_subset S p q (Finset.mem_filter.mp hq).2⟩
  have hstrict :
      ((I_layer 2 k).filter (fun q => (sdiv (S \ sdiv S p) q).Nonempty)).card + 1 ≤
        ((I_layer 2 k).filter (fun q => (sdiv S q).Nonempty)).card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hsub k, ?_⟩
    intro heq
    have hp' : p ∈ (I_layer 2 k).filter (fun q => (sdiv S q).Nonempty) :=
      Finset.mem_filter.mpr ⟨hp, hne⟩
    rw [← heq] at hp'
    have h := (Finset.mem_filter.mp hp').2
    simp only [sdiv_sdiff_self_empty, Finset.not_nonempty_empty] at h
  have hterm (j : ℕ) :
      w j * ((I_layer 2 j).filter (fun q => (sdiv (S \ sdiv S p) q).Nonempty)).card +
        (if j = k then w k else 0) ≤
          w j * ((I_layer 2 j).filter (fun q => (sdiv S q).Nonempty)).card := by
    by_cases hj : j = k
    · subst j
      rw [if_pos rfl]
      have hc :
          (((I_layer 2 k).filter (fun q => (sdiv (S \ sdiv S p) q).Nonempty)).card : ℝ) + 1 ≤
            ((I_layer 2 k).filter (fun q => (sdiv S q).Nonempty)).card := by
        exact_mod_cast hstrict
      nlinarith [hw k]
    · simp only [if_neg hj, add_zero]
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card (hsub j))) (hw j)
  have hsingle : Summable (fun j : ℕ => if j = k then w k else 0) :=
    ⟨_, hasSum_single k (by intro j hj; simp [hj])⟩
  have hsum := Summable.tsum_le_tsum hterm
    ((activeWeight_summable w hw hs (S \ sdiv S p)).add hsingle)
    (activeWeight_summable w hw hs S)
  rw [Summable.tsum_add (activeWeight_summable w hw hs (S \ sdiv S p)) hsingle] at hsum
  simpa [activeWeight] using hsum

theorem weighted_subset (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hs : Summable (fun k => w k * (N_layer 2 k : ℝ))) (S : Finset ℕ) :
    ∃ S' ⊆ S, WeightRegular w S' ∧
      (1 - weightTotal w) * S.card ≤ (S'.card : ℝ) := by
  suffices h : ∀ n : ℕ, ∀ T : Finset ℕ, T.card = n →
      ∃ S' ⊆ T, WeightRegular w S' ∧
        (T.card : ℝ) - S'.card ≤ activeWeight w T * T.card by
    obtain ⟨S', hS', hreg, hbound⟩ := h S.card S rfl
    exact ⟨S', hS', hreg, by nlinarith [activeWeight_le_total w hw hs S]⟩
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro T hT
    by_cases hreg : WeightRegular w T
    · refine ⟨T, Finset.Subset.refl T, hreg, ?_⟩
      simp only [sub_self]
      exact mul_nonneg (activeWeight_nonneg w hw T) (Nat.cast_nonneg _)
    · simp only [WeightRegular, not_forall] at hreg
      obtain ⟨k, p, hp, hwp, hne, hbad⟩ := hreg
      have hbound : ((sdiv T p).card : ℝ) ≤ w k * T.card := le_of_not_gt hbad
      let T₁ := T \ sdiv T p
      have hlt : T₁.card < T.card := card_sdiff_sdiv_lt T p hne
      obtain ⟨S', hS', hreg', hbound'⟩ := ih T₁.card (hT ▸ hlt) T₁ rfl
      refine ⟨S', hS'.trans Finset.sdiff_subset, hreg', ?_⟩
      have hcard : (T.card : ℝ) - T₁.card = (sdiv T p).card := by
        have h := Finset.card_sdiff_add_card_inter T (sdiv T p)
        rw [Finset.inter_eq_right.mpr (sdiv_subset T p)] at h
        have h' : (T₁.card : ℝ) + (sdiv T p).card = T.card := by exact_mod_cast h
        linarith
      have hmu := activeWeight_delete w hw hs T k p hp hne
      have hmono : activeWeight w T₁ * T₁.card ≤ activeWeight w T₁ * T.card :=
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hlt.le) (activeWeight_nonneg w hw T₁)
      dsimp [T₁] at hmu hmono hbound' hcard ⊢
      nlinarith

theorem weighted_pair_subset (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hs : Summable (fun k => w k * (N_layer 2 k : ℝ))) (hΩ : weightTotal w < 1)
    {n : ℕ} {A B : Finset ℕ} (hAB : ProductAdmissible n A B) :
    ∃ A' B' : Finset ℕ, ProductAdmissible n A' B' ∧ WeightRegular w A' ∧
      WeightRegular w B' ∧
        (1 - weightTotal w)^2 * ((A.card : ℝ) * B.card) ≤ (A'.card : ℝ) * B'.card := by
  obtain ⟨A', hA', hrA, hcA⟩ := weighted_subset w hw hs A
  obtain ⟨B', hB', hrB, hcB⟩ := weighted_subset w hw hs B
  refine ⟨A', B', admissible_subset hAB hA' hB', hrA, hrB, ?_⟩
  have hnonneg : 0 ≤ 1 - weightTotal w := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hcA hnonneg,
    mul_le_mul_of_nonneg_left hcB hnonneg]

end Erdos490
