/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TimedStoppedPairTwoAway
import ErdosProblems.Erdos207.RestrictedAbsorberBank

/-!
# Scalar bounds for padded-absorber threat coefficients

The probabilistic phase is chosen only after the absorber has been embedded.
For eventual parameter selection it is important that its two extension
coefficients be bounded by expressions involving only the advertised graph
support and bank-cardinality bounds.  This file removes the last dependence
on the particular existentially chosen absorber.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Uniform upper bound for one exact-bank pair-local class when the bank has
at most `b` triangles.  Only bank subfamilies of size at most `q` occur in a
configuration of order at most `q`, so this bound is polynomial in `b`. -/
def pairExactBankCoefficientUpper (q b : ℕ) : ℕ :=
  q * ((q + 1) * (b + 1) ^ q) * (2 ^ (q ^ 3) * (q + 1))

/-- Uniform upper bound for the complete pair-local two-away coefficient. -/
def pairTwoAwayCoefficientUpper (q b : ℕ) : ℕ :=
  (q + 1) * pairExactBankCoefficientUpper q b

/-- Uniform upper bound for the refined A2 budget when the absorber graph
support has size at most `c` and the bank has size at most `b`. -/
def refinedAbsorberBudgetUpper (q M c b : ℕ) : ℕ :=
  (q + 1) * 2 ^ M * (2 ^ (q ^ 3) * (q + 1)) +
    (c + 1) * (q + 1) * (b + 1) ^ q *
      (2 ^ (q ^ 3) * (q + 1))

/-- Uniform upper bound for the global two-away coefficient in ambient order
`n`. -/
def globalTwoAwayCoefficientUpper (q M c b n : ℕ) : ℕ :=
  (q + 1) * q * (n + 1) * refinedAbsorberBudgetUpper q M c b + 3 * n

/-- The global Markov tail with the absorber-specific coefficient replaced by
its scalar upper bound. -/
def globalTwoAwayTailUpper
    (q M c b n s K : ℕ) : ℝ≥0 :=
  ((twoAwayMomentJointConstant q s : ℝ≥0) *
      (((2 : ℝ≥0) ^ twoAwayMomentUnionCutoff q s *
        globalTwoAwayCoefficientUpper q M c b n) ^ s)) /
    ((K + 1 : ℕ) : ℝ≥0) ^ s

/-- Scalar union-bound expression for the two-cutoff phase. -/
def paddedPhaseFailureUpper
    (q M c b n phaseSteps sPair sGlobal Kpair Kglobal : ℕ)
    (theta a variance : ℝ) : ℝ :=
  ((n ^ 2 : ℕ) : ℝ) *
      (2 * Real.exp
        (-theta * a + theta ^ 2 * (phaseSteps : ℝ) * variance)) +
    ((((n ^ 3 : ℕ) : ℝ≥0) * ((n ^ 2 : ℕ) : ℝ≥0) *
      pairTwoAwayTail q sPair Kpair
        (pairTwoAwayCoefficientUpper q b : ℕ) : ℝ≥0) : ℝ) +
    ((((n ^ 3 : ℕ) : ℝ≥0) *
      globalTwoAwayTailUpper q M c b n sGlobal Kglobal : ℝ≥0) : ℝ)

lemma card_Icc_five_le (q : ℕ) : (Icc 5 q).card ≤ q := by
  rw [Nat.card_Icc]
  omega

theorem card_pairOn_le_sq
    (V : Type*) [Fintype V] [DecidableEq V] :
    Fintype.card (PairOn V) ≤ Fintype.card V ^ 2 := by
  change Fintype.card {s : Finset V // s.card = 2} ≤ _
  rw [Fintype.card_finset_len]
  exact Nat.choose_le_pow _ _

theorem pairExactBankExtensionCoefficient_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q b : ℕ} {B : TripleSystemOn V} (hB : B.card ≤ b) :
    pairExactBankExtensionCoefficient q B ≤
      pairExactBankCoefficientUpper q b := by
  classical
  unfold pairExactBankExtensionCoefficient pairExactBankCoefficientUpper
  let C := 2 ^ (q ^ 3) * (q + 1)
  calc
    (∑ r : (Icc 5 q : Finset ℕ), ∑ _K : subsetsUpToCard B q,
        2 ^ (r.1 ^ 3) * (r.1 + 1)) ≤
        ∑ _r : (Icc 5 q : Finset ℕ), ∑ _K : subsetsUpToCard B q, C := by
      apply sum_le_sum
      intro r _hr
      apply sum_le_sum
      intro _K _hK
      have hrq : r.1 ≤ q := (mem_Icc.mp r.2).2
      dsimp only [C]
      exact Nat.mul_le_mul
        (pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ))
          (pow_le_pow_left₀ (by omega) hrq 3))
        (by omega)
    _ = (Icc 5 q).card * (subsetsUpToCard B q).card * C := by
      simp [C, mul_assoc]
    _ ≤ q * ((q + 1) * (b + 1) ^ q) * C := by
      have hsub : (subsetsUpToCard B q).card ≤
          (q + 1) * (b + 1) ^ q := by
        calc
          (subsetsUpToCard B q).card ≤
              (q + 1) * (B.card + 1) ^ q :=
            card_subsetsUpToCard_le B q
          _ ≤ (q + 1) * (b + 1) ^ q := by
            gcongr
      exact Nat.mul_le_mul
        (Nat.mul_le_mul (card_Icc_five_le q)
          hsub)
        (le_refl C)

theorem pairTwoAwayThreatExtensionCoefficient_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q b : ℕ} {B : TripleSystemOn V} (hB : B.card ≤ b) :
    pairTwoAwayThreatExtensionCoefficient q B ≤
      pairTwoAwayCoefficientUpper q b := by
  unfold pairTwoAwayThreatExtensionCoefficient pairTwoAwayCoefficientUpper
  exact Nat.mul_le_mul_left (q + 1)
    (pairExactBankExtensionCoefficient_le hB)

theorem refinedIndexedAbsorberBudget_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M c b : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V}
    (hH : (graphSupportFinset H).card ≤ c) (hB : B.card ≤ b) :
    refinedIndexedAbsorberBudget q M H X B ≤
      refinedAbsorberBudgetUpper q M c b := by
  unfold refinedIndexedAbsorberBudget refinedAbsorberBudgetUpper
  have hHX : (graphSupportFinset H \ X).card ≤ c :=
    (card_le_card sdiff_subset).trans hH
  have hB1 : B.card + 1 ≤ b + 1 := by omega
  gcongr

theorem twoAwayThreatExtensionCoefficient_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M c b : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V}
    (hH : (graphSupportFinset H).card ≤ c) (hB : B.card ≤ b) :
    twoAwayThreatExtensionCoefficient q M H X B ≤
      globalTwoAwayCoefficientUpper q M c b (Fintype.card V) := by
  unfold twoAwayThreatExtensionCoefficient globalTwoAwayCoefficientUpper
  exact Nat.add_le_add
    (Nat.mul_le_mul_left ((q + 1) * q * (Fintype.card V + 1))
      (refinedIndexedAbsorberBudget_le hH hB))
    (le_refl (3 * Fintype.card V))

theorem pairTwoAwayTail_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q b s K : ℕ} {B : TripleSystemOn V} (hB : B.card ≤ b) :
    pairTwoAwayTail q s K
        (pairTwoAwayThreatExtensionCoefficient q B : ℕ) ≤
      pairTwoAwayTail q s K (pairTwoAwayCoefficientUpper q b : ℕ) := by
  unfold pairTwoAwayTail
  gcongr
  exact_mod_cast pairTwoAwayThreatExtensionCoefficient_le hB

theorem envelopeTwoAwayTail_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M c b s K : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V}
    (hH : (graphSupportFinset H).card ≤ c) (hB : B.card ≤ b) :
    envelopeTwoAwayTail q M s H X B K ≤
      globalTwoAwayTailUpper q M c b (Fintype.card V) s K := by
  unfold envelopeTwoAwayTail globalTwoAwayTailUpper
  gcongr
  exact_mod_cast twoAwayThreatExtensionCoefficient_le hH hB

theorem paddedPhaseFailure_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M c b n phaseSteps sPair sGlobal Kpair Kglobal : ℕ}
    {H : SimpleGraph V} {X : Finset V} {B : TripleSystemOn V}
    (theta a variance : ℝ) (hn : Fintype.card V = n)
    (hH : (graphSupportFinset H).card ≤ c) (hB : B.card ≤ b) :
    (Fintype.card (PairOn V) : ℝ) *
          (2 * Real.exp
            (-theta * a + theta ^ 2 * (phaseSteps : ℝ) * variance)) +
        (((Fintype.card (TripleOn V) : ℝ≥0) *
          (Fintype.card (PairOn V) : ℝ≥0) *
          pairTwoAwayTail q sPair Kpair
            (pairTwoAwayThreatExtensionCoefficient q B : ℕ) : ℝ≥0) : ℝ) +
        (((Fintype.card (TripleOn V) : ℝ≥0) *
          envelopeTwoAwayTail q M sGlobal H X B Kglobal : ℝ≥0) : ℝ) ≤
      paddedPhaseFailureUpper q M c b n phaseSteps sPair sGlobal
        Kpair Kglobal theta a variance := by
  have hpairNat : Fintype.card (PairOn V) ≤ n ^ 2 := by
    simpa only [hn] using card_pairOn_le_sq V
  have htripleNat : Fintype.card (TripleOn V) ≤ n ^ 3 := by
    simpa only [hn] using card_tripleOn_le_cube V
  have hpairReal : (Fintype.card (PairOn V) : ℝ) ≤ ((n ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hpairNat
  have hpairNN : (Fintype.card (PairOn V) : ℝ≥0) ≤
      ((n ^ 2 : ℕ) : ℝ≥0) := by
    exact_mod_cast hpairNat
  have htripleNN : (Fintype.card (TripleOn V) : ℝ≥0) ≤
      ((n ^ 3 : ℕ) : ℝ≥0) := by
    exact_mod_cast htripleNat
  unfold paddedPhaseFailureUpper
  apply add_le_add
  · apply add_le_add
    · gcongr
    · exact_mod_cast (show
        (Fintype.card (TripleOn V) : ℝ≥0) *
            (Fintype.card (PairOn V) : ℝ≥0) *
            pairTwoAwayTail q sPair Kpair
              (pairTwoAwayThreatExtensionCoefficient q B : ℕ) ≤
          ((n ^ 3 : ℕ) : ℝ≥0) * ((n ^ 2 : ℕ) : ℝ≥0) *
            pairTwoAwayTail q sPair Kpair
              (pairTwoAwayCoefficientUpper q b : ℕ) by
        gcongr
        exact pairTwoAwayTail_le hB)
  · exact_mod_cast (show
        (Fintype.card (TripleOn V) : ℝ≥0) *
            envelopeTwoAwayTail q M sGlobal H X B Kglobal ≤
          ((n ^ 3 : ℕ) : ℝ≥0) *
            globalTwoAwayTailUpper q M c b n sGlobal Kglobal by
        gcongr
        simpa only [hn] using envelopeTwoAwayTail_le hH hB)

end

end Erdos207
