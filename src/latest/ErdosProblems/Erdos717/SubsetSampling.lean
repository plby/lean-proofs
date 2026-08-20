/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Uniform-subset sampling for ordered missing pairs. -/

import ErdosProblems.Erdos717.ReservoirArithmetic

open Function Set
open SimpleGraph

namespace Erdos717

private theorem sum_missingOrdered_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (s : ℕ) (hs : 2 ≤ s) :
    ∑ S ∈ A.powersetCard s, (missingOrderedPairs G S).card =
      (missingOrderedPairs G A).card * Nat.choose (A.card - 2) (s - 2) := by
  classical
  let F := missingOrderedPairs G A
  let carrier : V × V → Finset V := fun p => {p.1, p.2}
  have hcarrierSub : ∀ p ∈ F, carrier p ⊆ A := by
    intro p hp x hx
    have hp' := Finset.mem_filter.mp hp
    have hpA := Finset.mem_product.mp hp'.1
    simp only [carrier, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hpA.1
    · exact hpA.2
  have hcarrierCard : ∀ p ∈ F, (carrier p).card = 2 := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    simp [carrier, hp'.2.1]
  have hdouble :
      ∑ S ∈ A.powersetCard s, (F.filter fun p => carrier p ⊆ S).card =
        ∑ p ∈ F, ((A.powersetCard s).filter fun S => carrier p ⊆ S).card := by
    simpa [Finset.bipartiteAbove, Finset.bipartiteBelow] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (r := fun S p => carrier p ⊆ S)
        (s := A.powersetCard s) (t := F))
  have hfilter (S : Finset V) (hSA : S ⊆ A) :
      F.filter (fun p => carrier p ⊆ S) = missingOrderedPairs G S := by
    ext p
    constructor
    · intro hp
      have hpF := Finset.mem_filter.mp hp
      have hpM := Finset.mem_filter.mp hpF.1
      have hpA := Finset.mem_product.mp hpM.1
      have hpne := hpM.2.1
      have hpn := hpM.2.2
      have hcar := hpF.2
      have hp1S : p.1 ∈ S := hcar (by simp [carrier])
      have hp2S : p.2 ∈ S := hcar (by simp [carrier])
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hp1S, hp2S⟩, hpne, hpn⟩
    · intro hp
      have hpM := Finset.mem_filter.mp hp
      have hpS := Finset.mem_product.mp hpM.1
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hSA hpS.1, hSA hpS.2⟩, hpM.2⟩, ?_⟩
      intro x hx
      simp only [carrier, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hpS.1
      · exact hpS.2
  calc
    ∑ S ∈ A.powersetCard s, (missingOrderedPairs G S).card =
        ∑ S ∈ A.powersetCard s, (F.filter fun p => carrier p ⊆ S).card := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [hfilter S (Finset.mem_powersetCard.mp hS).1]
    _ = ∑ p ∈ F, ((A.powersetCard s).filter fun S => carrier p ⊆ S).card := hdouble
    _ = ∑ _p ∈ F, Nat.choose (A.card - 2) (s - 2) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.card_filter_powersetCard_subset (carrier p) A s
        (hcarrierSub p hp)]
      · rw [hcarrierCard p hp]
      · simpa [hcarrierCard p hp] using hs
    _ = F.card * Nat.choose (A.card - 2) (s - 2) := by simp

private theorem choose_mul_two_descending
    (n s : ℕ) (hs : 2 ≤ s) (hsn : s ≤ n) :
    Nat.choose n s * (s * (s - 1)) =
      (n * (n - 1)) * Nat.choose (n - 2) (s - 2) := by
  have hn : 2 ≤ n := hs.trans hsn
  have h1 := Nat.add_one_mul_choose_eq (n - 1) (s - 1)
  have h2 := Nat.add_one_mul_choose_eq (n - 2) (s - 2)
  have hn1 : n - 1 + 1 = n := by omega
  have hs1 : s - 1 + 1 = s := by omega
  have hn2 : n - 2 + 1 = n - 1 := by omega
  have hs2 : s - 2 + 1 = s - 1 := by omega
  rw [hn1, hs1] at h1
  rw [hn2, hs2] at h2
  nlinarith

/-- A uniform subset preserves ordered-missing-pair density up to a factor
two.  The factor only absorbs the diagonal difference between `n²` and
`n(n-1)` and is convenient for integer routing estimates. -/
theorem exists_subset_missingOrdered_density
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (R s : ℕ) (hs : 2 ≤ s) (hsA : s ≤ A.card)
    (hmissing : R * (missingOrderedPairs G A).card ≤ A.card * A.card) :
    ∃ S : Finset V, S ⊆ A ∧ S.card = s ∧
      R * (missingOrderedPairs G S).card ≤ 2 * (s * s) := by
  classical
  let family := A.powersetCard s
  have hfamily : family.Nonempty := Finset.powersetCard_nonempty.mpr hsA
  obtain ⟨S, hSfamily, haverage⟩ :=
    Finset.exists_min_image family (fun S => (missingOrderedPairs G S).card) hfamily
  have hmin : family.card * (missingOrderedPairs G S).card ≤
      ∑ T ∈ family, (missingOrderedPairs G T).card := by
    simpa [nsmul_eq_mul] using
      family.card_nsmul_le_sum (fun T => (missingOrderedPairs G T).card)
        ((missingOrderedPairs G S).card) haverage
  have hSdata := Finset.mem_powersetCard.mp hSfamily
  have havg : Nat.choose A.card s * (missingOrderedPairs G S).card ≤
      (missingOrderedPairs G A).card * Nat.choose (A.card - 2) (s - 2) := by
    rw [Finset.card_powersetCard, sum_missingOrdered_subset G A s hs] at hmin
    exact hmin
  have hchoose := choose_mul_two_descending A.card s hs hsA
  have hscaled : Nat.choose A.card s *
      ((missingOrderedPairs G S).card * (A.card * (A.card - 1))) ≤
      Nat.choose A.card s *
        ((missingOrderedPairs G A).card * (s * (s - 1))) := by
    calc
      Nat.choose A.card s *
          ((missingOrderedPairs G S).card * (A.card * (A.card - 1))) =
          (Nat.choose A.card s * (missingOrderedPairs G S).card) *
            (A.card * (A.card - 1)) := by ring
      _ ≤ ((missingOrderedPairs G A).card *
          Nat.choose (A.card - 2) (s - 2)) *
            (A.card * (A.card - 1)) := Nat.mul_le_mul_right _ havg
      _ = Nat.choose A.card s *
          ((missingOrderedPairs G A).card * (s * (s - 1))) := by
            calc
              (missingOrderedPairs G A).card *
                    Nat.choose (A.card - 2) (s - 2) *
                    (A.card * (A.card - 1)) =
                  (missingOrderedPairs G A).card *
                    ((A.card * (A.card - 1)) *
                      Nat.choose (A.card - 2) (s - 2)) := by ring
              _ = (missingOrderedPairs G A).card *
                    (Nat.choose A.card s * (s * (s - 1))) := by rw [← hchoose]
              _ = _ := by ring
  have hchoosePos : 0 < Nat.choose A.card s := Nat.choose_pos hsA
  have hdensity : (missingOrderedPairs G S).card * (A.card * (A.card - 1)) ≤
      (missingOrderedPairs G A).card * (s * (s - 1)) :=
    Nat.le_of_mul_le_mul_left hscaled hchoosePos
  have hA2 : 2 ≤ A.card := hs.trans hsA
  have hfinalScaled :
      (R * (missingOrderedPairs G S).card) * (A.card * (A.card - 1)) ≤
        (2 * (s * s)) * (A.card * (A.card - 1)) := by
    calc
      (R * (missingOrderedPairs G S).card) * (A.card * (A.card - 1)) =
          R * ((missingOrderedPairs G S).card *
            (A.card * (A.card - 1))) := by ring
      _ ≤ R * ((missingOrderedPairs G A).card * (s * (s - 1))) :=
        Nat.mul_le_mul_left R hdensity
      _ = (R * (missingOrderedPairs G A).card) * (s * (s - 1)) := by ring
      _ ≤ (A.card * A.card) * (s * (s - 1)) :=
        Nat.mul_le_mul_right _ hmissing
      _ ≤ (2 * (A.card * (A.card - 1))) * (s * s) := by
        have hpred : A.card - 1 + 1 = A.card := by omega
        have hk : 1 ≤ A.card - 1 := by omega
        have hn : A.card * A.card ≤ 2 * (A.card * (A.card - 1)) := by
          nth_rewrite 1 [← hpred]
          nth_rewrite 2 [← hpred]
          nlinarith
        exact Nat.mul_le_mul hn (Nat.mul_le_mul_left s (Nat.sub_le s 1))
      _ = (2 * (s * s)) * (A.card * (A.card - 1)) := by ring
  have hpositive : 0 < A.card * (A.card - 1) :=
    Nat.mul_pos (by omega) (by omega)
  exact ⟨S, hSdata.1, hSdata.2,
    Nat.le_of_mul_le_mul_right hfinalScaled hpositive⟩

end Erdos717
