/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairFamilyTwoAwayWeight
import ErdosProblems.Erdos207.SupportBankWeightedBound

/-!
# Aggregate fixed-pair two-away witnesses

Here the selector is part of the witness rather than an external parameter.
For a packing, a family contains at most one triangle through the tracked
pair, while the selector has only as many choices as the bounded family has
members.  This is the extension system corresponding to the complete
two-away incidence of one pair star.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- A fixed-pair two-away family witness with a varying selector. -/
abbrev AggregatePairFamilyTwoAwayWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : ForbiddenFamilyOn V) (P : PairOn V) :=
  Σ U : TripleOn V, PairFamilyTwoAwayWitness G U P

def aggregatePairFamilyTwoAwayRemainder
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : ForbiddenFamilyOn V} {P : PairOn V}
    (z : AggregatePairFamilyTwoAwayWitness G P) : TripleSystemOn V :=
  pairFamilyTwoAwayRemainder z.2

abbrev ActiveAggregatePairFamilyTwoAwayWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : ForbiddenFamilyOn V) (P : PairOn V) (A : TripleSystemOn V) :=
  {z : AggregatePairFamilyTwoAwayWitness G P //
    A ⊆ aggregatePairFamilyTwoAwayRemainder z}

lemma aggregatePairFamilyTwoAwayWitness_ext
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : ForbiddenFamilyOn V} {P : PairOn V}
    {z w : AggregatePairFamilyTwoAwayWitness G P}
    (hselector : z.1 = w.1)
    (hfamily : z.2.1.family = w.2.1.family)
    (hmissing : z.2.1.missing = w.2.1.missing) : z = w := by
  rcases z with ⟨U, z⟩
  rcases w with ⟨W, w⟩
  dsimp only at hselector hfamily hmissing ⊢
  subst W
  have hzw : z = w := pairFamilyTwoAwayWitness_ext hfamily hmissing
  subst w
  rfl

lemma aggregatePairFamilyTwoAwayRemainder_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : ForbiddenFamilyOn V} {P : PairOn V} {m : ℕ}
    (hcard : ∀ S ∈ G, S.card = m)
    (z : AggregatePairFamilyTwoAwayWitness G P) :
    (aggregatePairFamilyTwoAwayRemainder z).card = m - 2 :=
  pairFamilyTwoAwayRemainder_card hcard z.2

/-- Exact constant-weight formula for the aggregate witness family. -/
lemma extensionWeight_aggregatePairFamilyTwoAway_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : ForbiddenFamilyOn V} {P : PairOn V} {m : ℕ}
    (hcard : ∀ S ∈ G, S.card = m)
    (p : ℝ≥0) (A : TripleSystemOn V) :
    extensionWeight
        (fun z : AggregatePairFamilyTwoAwayWitness G P ↦
          aggregatePairFamilyTwoAwayRemainder z)
        (constantTripleWeight p) A =
      (Fintype.card (ActiveAggregatePairFamilyTwoAwayWitness G P A) : ℝ≥0) *
        p ^ (m - 2 - A.card) := by
  classical
  unfold extensionWeight
  calc
    (∑ z : AggregatePairFamilyTwoAwayWitness G P,
        if A ⊆ aggregatePairFamilyTwoAwayRemainder z then
          setWeight (constantTripleWeight p)
            (aggregatePairFamilyTwoAwayRemainder z \ A) else 0) =
      ∑ z : AggregatePairFamilyTwoAwayWitness G P,
        if A ⊆ aggregatePairFamilyTwoAwayRemainder z then
          p ^ (m - 2 - A.card) else 0 := by
      apply sum_congr rfl
      intro z _hz
      by_cases hA : A ⊆ aggregatePairFamilyTwoAwayRemainder z
      · rw [if_pos hA, if_pos hA, setWeight_constantTripleWeight,
          card_sdiff_of_subset hA,
          aggregatePairFamilyTwoAwayRemainder_card hcard]
      · simp [hA]
    _ = (Fintype.card
          (ActiveAggregatePairFamilyTwoAwayWitness G P A) : ℝ≥0) *
        p ^ (m - 2 - A.card) := by
      rw [Fintype.card_subtype, ← Finset.sum_filter]
      simp

/-- Exact-bank active witnesses are coded by the missing triangle through
the tracked pair, their exact family, and their selector as a member of that
family. -/
def activeAggregatePairExactThroughEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B K : TripleSystemOn V} {P : PairOn V}
    (A : TripleSystemOn V) :
    ActiveAggregatePairFamilyTwoAwayWitness
        (exactBankOutsideExtensions r j B A K) P A ↪
      Σ T : universeTriplesContainingPair P.1,
        Σ S : exactBankOutsideExtensionsThrough r j B A K T.1,
          {U : TripleOn V // U ∈ S.1} := by
  classical
  refine
    { toFun := fun z ↦ ⟨
        ⟨z.1.2.1.missing,
          mem_universeTriplesContainingPair_iff.mpr z.1.2.2.1⟩,
        ⟨⟨z.1.2.1.family,
          mem_exactBankOutsideExtensionsThrough_iff.mpr
            ⟨z.1.2.1.family_mem, z.1.2.1.missing_mem, ?_⟩⟩,
          ⟨z.1.1, z.1.2.1.fixed_mem⟩⟩⟩
      inj' := ?_ }
  · intro hmissingA
    have hrem := z.2 hmissingA
    exact (mem_erase.mp (mem_erase.mp hrem).2).1 rfl
  · intro z w hzw
    have hmissing : z.1.2.1.missing = w.1.2.1.missing :=
      congrArg (fun c ↦ c.1.1) hzw
    have hfamily : z.1.2.1.family = w.1.2.1.family :=
      congrArg (fun c ↦ c.2.1.1) hzw
    have hselector : z.1.1 = w.1.1 :=
      congrArg (fun c ↦ c.2.2.1) hzw
    apply Subtype.ext
    exact aggregatePairFamilyTwoAwayWitness_ext hselector hfamily hmissing

/-- The exact code has at most `j-2` selector choices for each distinguished
triangle and exact family. -/
lemma card_activeAggregatePairExact_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B K : TripleSystemOn V} {P : PairOn V}
    (A : TripleSystemOn V) :
    Fintype.card (ActiveAggregatePairFamilyTwoAwayWitness
        (exactBankOutsideExtensions r j B A K) P A) ≤
      (j - 2) * ∑ T : universeTriplesContainingPair P.1,
        (exactBankOutsideExtensionsThrough r j B A K T.1).card := by
  calc
    Fintype.card (ActiveAggregatePairFamilyTwoAwayWitness
        (exactBankOutsideExtensions r j B A K) P A) ≤
      Fintype.card
        (Σ T : universeTriplesContainingPair P.1,
          Σ S : exactBankOutsideExtensionsThrough r j B A K T.1,
            {U : TripleOn V // U ∈ S.1}) :=
      Fintype.card_le_of_embedding
        (activeAggregatePairExactThroughEmbedding A)
    _ = ∑ T : universeTriplesContainingPair P.1,
        ∑ S : exactBankOutsideExtensionsThrough r j B A K T.1,
          S.1.card := by
      simp only [Fintype.card_sigma, Fintype.card_coe]
    _ = ∑ T : universeTriplesContainingPair P.1,
        ∑ _S : exactBankOutsideExtensionsThrough r j B A K T.1,
          (j - 2) := by
      apply sum_congr rfl
      intro T _hT
      apply sum_congr rfl
      intro S _hS
      exact exactBankOutsideExtensionsThrough_fixed_card S.1 S.2
    _ = (j - 2) * ∑ T : universeTriplesContainingPair P.1,
        (exactBankOutsideExtensionsThrough r j B A K T.1).card := by
      simp [mul_sum, Nat.mul_comm]

/-- One exact absorber-bank class has aggregate fixed-pair extension weight
at most a bounded coefficient times the square of the ambient scale.  The
two powers are exactly the cost of deleting the two designated triangles
from the selected remainder. -/
theorem extensionWeight_aggregatePairFamily_exactBank_le_quadratic
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B K : TripleSystemOn V} {P : PairOn V}
    (A : TripleSystemOn V) (hr : 5 ≤ r) (hj : 2 ≤ j) :
    extensionWeight
        (fun z : AggregatePairFamilyTwoAwayWitness
            (exactBankOutsideExtensions r j B A K) P ↦
          aggregatePairFamilyTwoAwayRemainder z)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A ≤
      ((j - 2) * (2 ^ (r ^ 3) * (r + 1)) : ℕ) *
        (Fintype.card V + 1 : ℝ≥0) ^ 2 := by
  classical
  let G := exactBankOutsideExtensions r j B A K
  let N : ℝ≥0 := (Fintype.card V : ℝ≥0) + 1
  let p : ℝ≥0 := N⁻¹
  let C : ℝ≥0 := (2 ^ (r ^ 3) * (r + 1) : ℕ)
  change extensionWeight
      (fun z : AggregatePairFamilyTwoAwayWitness G P ↦
        aggregatePairFamilyTwoAwayRemainder z)
      (constantTripleWeight p) A ≤
    (((j - 2) * (2 ^ (r ^ 3) * (r + 1)) : ℕ) : ℝ≥0) * N ^ 2
  rw [Nat.cast_mul]
  change extensionWeight
      (fun z : AggregatePairFamilyTwoAwayWitness G P ↦
        aggregatePairFamilyTwoAwayRemainder z)
      (constantTripleWeight p) A ≤
    ((j - 2 : ℕ) : ℝ≥0) * C * N ^ 2
  rw [extensionWeight_aggregatePairFamilyTwoAway_eq
    (m := j - 2) exactBankOutsideExtensions_fixed_card]
  by_cases hactive : IsEmpty
      (ActiveAggregatePairFamilyTwoAwayWitness G P A)
  · have hzero : Fintype.card
        (ActiveAggregatePairFamilyTwoAwayWitness G P A) = 0 :=
      Fintype.card_eq_zero
    simp [hzero]
  · let : Nonempty (ActiveAggregatePairFamilyTwoAwayWitness G P A) :=
      not_isEmpty_iff.mp hactive
    let z : ActiveAggregatePairFamilyTwoAwayWitness G P A :=
      Classical.choice inferInstance
    have htwo : 1 < z.1.2.1.family.card := by
      exact one_lt_card.mpr
        ⟨z.1.1, z.1.2.1.fixed_mem, z.1.2.1.missing,
          z.1.2.1.missing_mem, z.1.2.1.missing_ne.symm⟩
    rw [exactBankOutsideExtensions_fixed_card
      z.1.2.1.family z.1.2.1.family_mem] at htwo
    have hAcard : A.card + 2 ≤ j - 2 := by
      have hsub := card_le_card z.2
      rw [aggregatePairFamilyTwoAwayRemainder_card
        exactBankOutsideExtensions_fixed_card z.1] at hsub
      omega
    have hN : N ≠ 0 := by dsimp [N]; positivity
    have hpow :
        N ^ 2 * p ^ (j - 2 - A.card) =
          p ^ (j - 2 - 2 - A.card) := by
      have hexp : j - 2 - A.card =
          (j - 2 - 2 - A.card) + 2 := by omega
      rw [hexp, pow_add]
      calc
        N ^ 2 * (p ^ (j - 2 - 2 - A.card) * p ^ 2) =
            p ^ (j - 2 - 2 - A.card) * (N * p) * (N * p) := by
          ring
        _ = p ^ (j - 2 - 2 - A.card) := by simp [p, hN]
    have hactiveCard := card_activeAggregatePairExact_le
      (r := r) (j := j) (B := B) (K := K) (P := P) A
    have hactiveCast :
        (Fintype.card
          (ActiveAggregatePairFamilyTwoAwayWitness G P A) : ℝ≥0) ≤
          (((j - 2) * ∑ T : universeTriplesContainingPair P.1,
            (exactBankOutsideExtensionsThrough r j B A K T.1).card : ℕ) :
              ℝ≥0) := by
      exact_mod_cast hactiveCard
    have hsum :
        (((∑ T : universeTriplesContainingPair P.1,
            (exactBankOutsideExtensionsThrough r j B A K T.1).card : ℕ) :
              ℝ≥0) * p ^ (j - 2 - A.card)) ≤ C := by
      rw [Nat.cast_sum, sum_mul]
      calc
        (∑ T : universeTriplesContainingPair P.1,
            ((exactBankOutsideExtensionsThrough r j B A K T.1).card : ℝ≥0) *
              p ^ (j - 2 - A.card)) ≤
          ∑ _T : universeTriplesContainingPair P.1, C * p := by
            apply sum_le_sum
            intro T _hT
            have hb := extensionWeight_exactBankOutsideExtensionsThrough_le_inv
              (V := V) (r := r) (j := j) (B := B) (R := A)
              (K := K) (T := T.1) hr hj
            change extensionWeight
                (fun S : exactBankOutsideExtensionsThrough r j B A K T.1 ↦ S.1)
                (fun _ ↦ p) A ≤ C * p at hb
            rw [extensionWeight_constant_eq _ (j - 2)
              exactBankOutsideExtensionsThrough_fixed_card p A,
              familyExtensions_exactBankOutsideExtensionsThrough_self] at hb
            exact hb
        _ = (Fintype.card (universeTriplesContainingPair P.1) : ℝ≥0) *
            (C * p) := by
          rw [sum_const, nsmul_eq_mul, card_univ]
        _ ≤ N * (C * p) := by
          gcongr
          rw [Fintype.card_coe]
          have hc := card_universeTriplesContainingPair_le V P.1 P.2
          have hc' : ((universeTriplesContainingPair P.1).card : ℝ≥0) ≤
              (Fintype.card V : ℝ≥0) := by
            exact_mod_cast hc
          exact hc'.trans (by dsimp [N]; exact le_add_right le_rfl)
        _ = C := by
          calc
            N * (C * p) = C * (N * p) := by ring
            _ = C := by simp [p, hN]
    calc
      (Fintype.card
          (ActiveAggregatePairFamilyTwoAwayWitness G P A) : ℝ≥0) *
          p ^ (j - 2 - 2 - A.card) ≤
        ((((j - 2) * ∑ T : universeTriplesContainingPair P.1,
            (exactBankOutsideExtensionsThrough r j B A K T.1).card : ℕ) :
              ℝ≥0) * p ^ (j - 2 - 2 - A.card)) := by
        simpa only [mul_comm] using
          mul_le_mul_right hactiveCast (p ^ (j - 2 - 2 - A.card))
      _ = ((j - 2 : ℕ) : ℝ≥0) * N ^ 2 *
          ((((∑ T : universeTriplesContainingPair P.1,
            (exactBankOutsideExtensionsThrough r j B A K T.1).card : ℕ) :
              ℝ≥0) * p ^ (j - 2 - A.card))) := by
        rw [Nat.cast_mul, ← hpow]
        ring
      _ ≤ ((j - 2 : ℕ) : ℝ≥0) * N ^ 2 * C := by
        gcongr
      _ = ((j - 2 : ℕ) : ℝ≥0) * C * N ^ 2 := by ring

end

end Erdos207
