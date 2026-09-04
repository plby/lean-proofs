/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairFamilyTwoAwayWeight

/-!
# Fixed-pair weights for one exact absorber-bank class

For a nontrivial exact root, packinghood makes the missing triangle through a
fixed pair unique and strong minimality supplies one inverse ambient factor.
For the one-triangle root, the missing triangle is exposed explicitly; there
are at most `|V|` choices and strong minimality supplies two inverse factors.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- In the one-triangle-root case, remember the missing triangle explicitly.
This is an injection because the code retains both the family and the missing
triangle. -/
def activePairExactThroughEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B K : TripleSystemOn V} {U : TripleOn V} {P : PairOn V}
    (A : TripleSystemOn V) :
    ActivePairFamilyTwoAwayWitness
        (exactBankOutsideExtensions r j B (insert U A) K) U P A ↪
      Σ T : universeTriplesContainingPair P.1,
        exactBankOutsideExtensionsThrough r j B (insert U A) K T.1 := by
  classical
  refine
    { toFun := fun z ↦ ⟨
        ⟨z.1.1.missing,
          mem_universeTriplesContainingPair_iff.mpr z.1.2.1⟩,
        ⟨z.1.1.family, mem_exactBankOutsideExtensionsThrough_iff.mpr
          ⟨z.1.1.family_mem, z.1.1.missing_mem, ?_⟩⟩⟩
      inj' := ?_ }
  · intro hmem
    rw [mem_insert] at hmem
    rcases hmem with hU | hA
    · exact z.1.1.missing_ne hU
    · have hrem := z.2 hA
      exact (mem_erase.mp (mem_erase.mp hrem).2).1 rfl
  · intro z w hzw
    have hmissing : z.1.1.missing = w.1.1.missing :=
      congrArg (fun c ↦ c.1.1) hzw
    have hfamily : z.1.1.family = w.1.1.family :=
      congrArg (fun c ↦ c.2.1) hzw
    apply Subtype.ext
    exact pairFamilyTwoAwayWitness_ext hfamily hmissing

lemma card_activePairExact_le_sum_through
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B K : TripleSystemOn V} {U : TripleOn V} {P : PairOn V}
    (A : TripleSystemOn V) :
    Fintype.card (ActivePairFamilyTwoAwayWitness
        (exactBankOutsideExtensions r j B (insert U A) K) U P A) ≤
      ∑ T : universeTriplesContainingPair P.1,
        (exactBankOutsideExtensionsThrough r j B (insert U A) K T.1).card := by
  calc
    Fintype.card (ActivePairFamilyTwoAwayWitness
        (exactBankOutsideExtensions r j B (insert U A) K) U P A) ≤
        Fintype.card (Σ T : universeTriplesContainingPair P.1,
          exactBankOutsideExtensionsThrough r j B (insert U A) K T.1) :=
      Fintype.card_le_of_embedding (activePairExactThroughEmbedding A)
    _ = ∑ T : universeTriplesContainingPair P.1,
        (exactBankOutsideExtensionsThrough r j B (insert U A) K T.1).card := by
      simp

/-- The pair-local two-away extension weight of a single exact bank class is
bounded independently of the ambient vertex set. -/
theorem extensionWeight_pairFamily_exactBank_le_constant
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B K : TripleSystemOn V} {U : TripleOn V} {P : PairOn V}
    (A : TripleSystemOn V) (hr : 5 ≤ r) (hj : 4 ≤ j) :
    extensionWeight
        (fun z : PairFamilyTwoAwayWitness
            (exactBankOutsideExtensions r j B (insert U A) K) U P ↦
          pairFamilyTwoAwayRemainder z)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A ≤
      (2 ^ (r ^ 3) * (r + 1) : ℕ) := by
  classical
  let G := exactBankOutsideExtensions r j B (insert U A) K
  let N : ℝ≥0 := (Fintype.card V : ℝ≥0) + 1
  let p : ℝ≥0 := N⁻¹
  let C : ℝ≥0 := (2 ^ (r ^ 3) * (r + 1) : ℕ)
  change extensionWeight
      (fun z : PairFamilyTwoAwayWitness G U P ↦
        pairFamilyTwoAwayRemainder z)
      (constantTripleWeight p) A ≤ C
  rw [extensionWeight_pairFamilyTwoAway_eq
    (m := j - 2) exactBankOutsideExtensions_fixed_card]
  by_cases hactive : IsEmpty (ActivePairFamilyTwoAwayWitness G U P A)
  · have hzero : Fintype.card
        (ActivePairFamilyTwoAwayWitness G U P A) = 0 := Fintype.card_eq_zero
    simp [hzero]
  · let : Nonempty (ActivePairFamilyTwoAwayWitness G U P A) :=
      not_isEmpty_iff.mp hactive
    let z : ActivePairFamilyTwoAwayWitness G U P A :=
      Classical.choice inferInstance
    have hUnotA : U ∉ A := by
      intro hUA
      have hrem := z.2 hUA
      exact (mem_erase.mp hrem).1 rfl
    have hRcard : (insert U A).card = A.card + 1 :=
      card_insert_of_notMem hUnotA
    have hAcard : A.card + 2 ≤ j - 2 := by
      have hsub := card_le_card z.2
      rw [pairFamilyTwoAwayRemainder_card
        exactBankOutsideExtensions_fixed_card z.1] at hsub
      omega
    have hpow :
        N * p ^ (j - 2 - (insert U A).card) =
          p ^ (j - 2 - 2 - A.card) := by
      have hexp : j - 2 - (insert U A).card =
          (j - 2 - 2 - A.card) + 1 := by omega
      rw [hexp, pow_succ]
      calc
        N * (p ^ (j - 2 - 2 - A.card) * p) =
            p ^ (j - 2 - 2 - A.card) * (N * p) := by ring
        _ = p ^ (j - 2 - 2 - A.card) := by
          have hN : N ≠ 0 := by dsimp [N]; positivity
          rw [show N * p = 1 by simp [p, hN], mul_one]
    obtain ⟨_hScard, hRS, E, hE, hEout, hEin⟩ :=
      mem_exactBankOutsideExtensions_iff.mp z.1.1.family_mem
    have hSsubE : z.1.1.family ⊆ E := by
      intro T hTS
      exact (mem_sdiff.mp (by rw [hEout]; exact hTS)).1
    have hrootE : insert U A ∪ K ⊆ E := by
      intro T hT
      rcases mem_union.mp hT with hTR | hTK
      · exact hSsubE (hRS hTR)
      · have hTEB : T ∈ E ∩ B := by rw [hEin]; exact hTK
        exact (mem_inter.mp hTEB).1
    have hmissingNotRoot : z.1.1.missing ∉ insert U A ∪ K := by
      intro hT
      rcases mem_union.mp hT with hTR | hTK
      · rw [mem_insert] at hTR
        rcases hTR with hTU | hTA
        · exact z.1.1.missing_ne hTU
        · have hrem := z.2 hTA
          exact (mem_erase.mp (mem_erase.mp hrem).2).1 rfl
      · have hTK' : z.1.1.missing ∈ E ∩ B := by rw [hEin]; exact hTK
        have hTout : z.1.1.missing ∈ E \ B := by
          rw [hEout]
          exact z.1.1.missing_mem
        exact (mem_sdiff.mp hTout).2 (mem_inter.mp hTK').2
    have hrootSmall : (insert U A ∪ K).card ≤ r - 3 := by
      have hproper : insert U A ∪ K ⊂ E := by
        apply ssubset_iff_subset_ne.mpr
        refine ⟨hrootE, ?_⟩
        intro heq
        exact hmissingNotRoot (heq.symm ▸ hSsubE z.1.1.missing_mem)
      have hlt := card_lt_card hproper
      rw [hE.1.1] at hlt
      omega
    by_cases hroot2 : 2 ≤ (insert U A ∪ K).card
    · have hpacking : ∀ S ∈ G, IsPackingOn S := by
        intro S hSG
        exact exactBankOutsideExtensions_isPacking hr hSG
      have hactiveCard := card_activePairFamilyTwoAwayWitness_le
        (G := G) (U := U) (P := P) A hpacking
      rw [familyExtensions_exactBankOutsideExtensions_self] at hactiveCard
      have hactiveCast :
          (Fintype.card (ActivePairFamilyTwoAwayWitness G U P A) : ℝ≥0) ≤
            (G.card : ℝ≥0) := by exact_mod_cast hactiveCard
      have hstrong := extensionWeight_exactBankOutsideExtensions_self_le_inv_strong
        (V := V) (r := r) (j := j) (B := B) (R := insert U A) (K := K)
        hr (by omega) hroot2 hrootSmall
      change extensionWeight (fun S : G ↦ S.1)
          (constantTripleWeight p) (insert U A) ≤ C * p at hstrong
      rw [extensionWeight_exactBankOutsideExtensions,
        familyExtensions_exactBankOutsideExtensions_self] at hstrong
      calc
        (Fintype.card (ActivePairFamilyTwoAwayWitness G U P A) : ℝ≥0) *
            p ^ (j - 2 - 2 - A.card) ≤
          (G.card : ℝ≥0) * p ^ (j - 2 - 2 - A.card) := by
            simpa only [mul_comm] using
              mul_le_mul_right hactiveCast (p ^ (j - 2 - 2 - A.card))
        _ = N * ((G.card : ℝ≥0) *
            p ^ (j - 2 - (insert U A).card)) := by rw [← hpow]; ring
        _ ≤ N * (C * p) := by
          simpa only [mul_comm] using mul_le_mul_right hstrong N
        _ = C := by
          have hN : N ≠ 0 := by dsimp [N]; positivity
          calc
            N * (C * p) = C * (N * p) := by ring
            _ = C := by simp [p, hN]
    · have hrootPos : 1 ≤ (insert U A).card := by
        exact card_pos.mpr ⟨U, mem_insert_self U A⟩
      have hrootUnion : (insert U A ∪ K).card = 1 := by
        have hle : (insert U A ∪ K).card ≤ 1 := by omega
        have hsub : insert U A ⊆ insert U A ∪ K := subset_union_left
        have := card_le_card hsub
        omega
      have hactiveCard := card_activePairExact_le_sum_through
        (r := r) (j := j) (B := B) (K := K) (U := U) (P := P) A
      have hactiveCast :
          (Fintype.card (ActivePairFamilyTwoAwayWitness G U P A) : ℝ≥0) ≤
            (∑ T : universeTriplesContainingPair P.1,
              (exactBankOutsideExtensionsThrough r j B (insert U A) K T.1).card : ℕ) := by
        exact_mod_cast hactiveCard
      have hsum :
          ((∑ T : universeTriplesContainingPair P.1,
              (exactBankOutsideExtensionsThrough r j B (insert U A) K T.1).card : ℕ) : ℝ≥0) *
              p ^ (j - 2 - (insert U A).card) ≤
            (Fintype.card (universeTriplesContainingPair P.1) : ℝ≥0) *
              (C * p ^ 2) := by
        rw [Nat.cast_sum, sum_mul]
        calc
          (∑ T : universeTriplesContainingPair P.1,
              ((exactBankOutsideExtensionsThrough r j B (insert U A) K T.1).card : ℝ≥0) *
                p ^ (j - 2 - (insert U A).card)) ≤
            ∑ _T : universeTriplesContainingPair P.1, C * p ^ 2 := by
              apply sum_le_sum
              intro T _hT
              have hsmallT : (({T.1} ∪ insert U A) ∪ K).card ≤ r - 3 := by
                have heq : ({T.1} ∪ insert U A) ∪ K =
                    {T.1} ∪ (insert U A ∪ K) := by ext S; simp [or_assoc]
                rw [heq]
                have hc := card_union_le ({T.1} : TripleSystemOn V)
                  (insert U A ∪ K)
                simp only [card_singleton, hrootUnion] at hc
                omega
              have hb := extensionWeight_exactBankOutsideExtensionsThrough_le_inv_sq
                (V := V) (r := r) (j := j) (B := B) (R := insert U A)
                (K := K) (T := T.1) hr (by omega) hrootPos hsmallT
              change extensionWeight
                  (fun S : exactBankOutsideExtensionsThrough r j B (insert U A) K T.1 ↦ S.1)
                  (fun _ ↦ p) (insert U A) ≤ C * p ^ 2 at hb
              rw [extensionWeight_constant_eq _ (j - 2)
                exactBankOutsideExtensionsThrough_fixed_card p (insert U A),
                familyExtensions_exactBankOutsideExtensionsThrough_self] at hb
              exact hb
          _ = (Fintype.card (universeTriplesContainingPair P.1) : ℝ≥0) *
              (C * p ^ 2) := by
                rw [sum_const, nsmul_eq_mul, card_univ]
      have hpairCard :
          (Fintype.card (universeTriplesContainingPair P.1) : ℝ≥0) ≤ N := by
        rw [Fintype.card_coe]
        have hc := card_universeTriplesContainingPair_le V P.1 P.2
        have hc' : ((universeTriplesContainingPair P.1).card : ℝ≥0) ≤
            (Fintype.card V : ℝ≥0) := by
          exact_mod_cast hc
        exact hc'.trans (by dsimp [N]; exact le_add_right le_rfl)
      calc
        (Fintype.card (ActivePairFamilyTwoAwayWitness G U P A) : ℝ≥0) *
            p ^ (j - 2 - 2 - A.card) ≤
          ((∑ T : universeTriplesContainingPair P.1,
              (exactBankOutsideExtensionsThrough r j B (insert U A) K T.1).card : ℕ) : ℝ≥0) *
            p ^ (j - 2 - 2 - A.card) := by
              simpa only [mul_comm] using
                mul_le_mul_right hactiveCast (p ^ (j - 2 - 2 - A.card))
        _ = N * (((∑ T : universeTriplesContainingPair P.1,
              (exactBankOutsideExtensionsThrough r j B (insert U A) K T.1).card : ℕ) : ℝ≥0) *
            p ^ (j - 2 - (insert U A).card)) := by rw [← hpow]; ring
        _ ≤ N * ((Fintype.card (universeTriplesContainingPair P.1) : ℝ≥0) *
            (C * p ^ 2)) := by
              simpa only [mul_comm] using mul_le_mul_right hsum N
        _ ≤ N * (N * (C * p ^ 2)) := by gcongr
        _ = C := by
          have hN : N ≠ 0 := by dsimp [N]; positivity
          calc
            N * (N * (C * p ^ 2)) = C * ((N * p) * (N * p)) := by ring
            _ = C := by simp [p, hN]

end

end Erdos207
