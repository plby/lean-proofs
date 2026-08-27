/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteConditioning

/-!
# Cardinality tails from joint-inclusion estimates

A large intersection with a fixed finite test family contains an `r`-element
subfamily.  A union bound over those witnesses converts prescribed-subfamily
joint-inclusion estimates into a cardinality tail bound.  This is the finite
falling-factorial estimate needed for the degree-loss events in the KSSS
master iteration.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

namespace FiniteLaw

variable {Omega X : Type*} [Fintype Omega] [DecidableEq X]

/-- If at least `r` members of `S` were selected, some `r`-element subset of
`S` was selected in its entirety. -/
lemma card_inter_selected_ge_imp_exists_powersetCard_subset
    (selected : Omega -> Finset X) (S : Finset X) (r : Nat) (omega : Omega)
    (hlarge : r <= (S ∩ selected omega).card) :
    Exists fun Q => Q ∈ S.powersetCard r ∧ Q ⊆ selected omega := by
  obtain ⟨Q, hQsub, hQcard⟩ :=
    Finset.exists_subset_card_eq hlarge
  exact ⟨Q, mem_powersetCard.mpr
    ⟨hQsub.trans inter_subset_left, hQcard⟩,
    hQsub.trans inter_subset_right⟩

/-- A prescribed-subfamily inclusion estimate gives a binomial union-bound
tail for the number of selected members of `S`. -/
theorem probability_card_inter_selected_ge_le_of_jointInclusion
    (L : FiniteLaw Omega) (selected : Omega -> Finset X)
    (S : Finset X) (alpha : NNReal) (r : Nat)
    (hjoint : ∀ Q ∈ S.powersetCard r,
      L.probability (fun omega => Q ⊆ selected omega) <= alpha ^ r) :
    L.probability (fun omega => r <= (S ∩ selected omega).card) <=
      (S.powersetCard r).card * alpha ^ r := by
  calc
    L.probability (fun omega => r <= (S ∩ selected omega).card) <=
        L.probability (fun omega =>
          Exists fun Q => Q ∈ S.powersetCard r ∧ Q ⊆ selected omega) := by
      apply L.probability_mono
      intro omega hlarge
      exact card_inter_selected_ge_imp_exists_powersetCard_subset
        selected S r omega hlarge
    _ <= ∑ Q ∈ S.powersetCard r,
        L.probability (fun omega => Q ⊆ selected omega) := by
      exact L.probability_exists_le (S.powersetCard r)
        (fun Q omega => Q ⊆ selected omega)
    _ <= ∑ _Q ∈ S.powersetCard r, alpha ^ r := by
      exact sum_le_sum fun Q hQ => hjoint Q hQ
    _ = (S.powersetCard r).card * alpha ^ r := by
      simp

/-- Version with a joint-inclusion bound stated by the cardinality of every
prescribed family. -/
theorem probability_card_inter_selected_ge_le_of_card_jointInclusion
    (L : FiniteLaw Omega) (selected : Omega -> Finset X)
    (S : Finset X) (alpha : NNReal) (r : Nat)
    (hjoint : ∀ Q : Finset X,
      L.probability (fun omega => Q ⊆ selected omega) <= alpha ^ Q.card) :
    L.probability (fun omega => r <= (S ∩ selected omega).card) <=
      (S.powersetCard r).card * alpha ^ r := by
  apply L.probability_card_inter_selected_ge_le_of_jointInclusion
  intro Q hQ
  simpa [(mem_powersetCard.mp hQ).2] using hjoint Q

/-- Simultaneously impose finitely many strict cardinality caps.  The
binomial tail sum proves that the common good event has positive
probability.  Conditioning on it enforces every cap throughout the support,
and the original exponential joint-inclusion estimate survives with the
standard reciprocal loss absorbed into its base. -/
theorem exists_conditionOn_cardCaps_of_jointInclusion
    {J : Type*} [DecidableEq J]
    (L : FiniteLaw Omega) (selected : Omega -> Finset X)
    (tests : J -> Finset X) (caps : J -> Nat) (indices : Finset J)
    (alpha : NNReal)
    (hjoint : ∀ Q : Finset X,
      L.probability (fun omega => Q ⊆ selected omega) <= alpha ^ Q.card)
    (hsmall : ∑ j ∈ indices,
        ((tests j).powersetCard (caps j)).card * alpha ^ caps j < 1) :
    let Good : Omega -> Prop := fun omega => ∀ j ∈ indices,
      ((tests j) ∩ selected omega).card < caps j
    Exists fun hGood : 0 < L.probability Good =>
      (L.conditionOn Good hGood).SupportedOn Good ∧
      ∀ Q : Finset X,
        (L.conditionOn Good hGood).probability
            (fun omega => Q ⊆ selected omega) <=
          (alpha / L.probability Good) ^ Q.card := by
  dsimp only
  let Good : Omega -> Prop := fun omega => ∀ j ∈ indices,
    ((tests j) ∩ selected omega).card < caps j
  have hbad : L.probability (fun omega => ¬ Good omega) < 1 := by
    calc
      L.probability (fun omega => ¬ Good omega) <=
          L.probability (fun omega => Exists fun j => j ∈ indices ∧
            caps j <= ((tests j) ∩ selected omega).card) := by
        apply L.probability_mono
        intro omega hnot
        dsimp only [Good] at hnot
        push_neg at hnot
        exact hnot
      _ <= ∑ j ∈ indices,
          L.probability (fun omega =>
            caps j <= ((tests j) ∩ selected omega).card) := by
        exact L.probability_exists_le indices (fun j omega =>
          caps j <= ((tests j) ∩ selected omega).card)
      _ <= ∑ j ∈ indices,
          ((tests j).powersetCard (caps j)).card * alpha ^ caps j := by
        exact sum_le_sum fun j _hj =>
          L.probability_card_inter_selected_ge_le_of_card_jointInclusion
            selected (tests j) alpha (caps j) hjoint
      _ < 1 := hsmall
  have hGood : 0 < L.probability Good := by
    calc
      0 < 1 - L.probability (fun omega => ¬ Good omega) :=
        tsub_pos_iff_lt.mpr hbad
      _ = L.probability (fun omega => ¬ ¬ Good omega) :=
        (L.probability_not (fun omega => ¬ Good omega)).symm
      _ = L.probability Good := by
        congr 1
        funext omega
        simp
  refine ⟨hGood, L.conditionOn_supported Good hGood, ?_⟩
  intro Q
  by_cases hQ : Q = ∅
  · subst Q
    simpa using (L.conditionOn Good hGood).probability_le_one
      (fun omega => (∅ : Finset X) ⊆ selected omega)
  · have hcard : 0 < Q.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hQ)
    have hprob_le_one : L.probability Good <= 1 := L.probability_le_one Good
    have hpow_le : (L.probability Good) ^ Q.card <= L.probability Good :=
      pow_le_of_le_one zero_le hprob_le_one hcard.ne'
    calc
      (L.conditionOn Good hGood).probability
          (fun omega => Q ⊆ selected omega) <=
          L.probability (fun omega => Q ⊆ selected omega) /
            L.probability Good :=
        L.conditionOn_probability_le Good
          (fun omega => Q ⊆ selected omega) hGood
      _ <= alpha ^ Q.card / L.probability Good := by
        gcongr
        exact hjoint Q
      _ <= alpha ^ Q.card / (L.probability Good) ^ Q.card := by
        exact div_le_div_of_nonneg_left zero_le (pow_pos hGood _) hpow_le
      _ = (alpha / L.probability Good) ^ Q.card := by
        rw [div_pow]

/-- Uniform-error version of
`exists_conditionOn_cardCaps_of_jointInclusion`.  If the total binomial
tail is at most `epsilon < 1`, the good event has probability at least
`1 - epsilon`, and every conditioned joint-inclusion probability is bounded
with base `alpha / (1 - epsilon)`. -/
theorem exists_conditionOn_cardCaps_of_jointInclusion_of_sum_le
    {J : Type*} [DecidableEq J]
    (L : FiniteLaw Omega) (selected : Omega -> Finset X)
    (tests : J -> Finset X) (caps : J -> Nat) (indices : Finset J)
    (alpha epsilon : NNReal)
    (hjoint : ∀ Q : Finset X,
      L.probability (fun omega => Q ⊆ selected omega) <= alpha ^ Q.card)
    (hsum : ∑ j ∈ indices,
        ((tests j).powersetCard (caps j)).card * alpha ^ caps j <= epsilon)
    (hepsilon : epsilon < 1) :
    let Good : Omega -> Prop := fun omega => ∀ j ∈ indices,
      ((tests j) ∩ selected omega).card < caps j
    Exists fun hGood : 0 < L.probability Good =>
      (L.conditionOn Good hGood).SupportedOn Good ∧
      (∀ Q : Finset X,
        (L.conditionOn Good hGood).probability
            (fun omega => Q ⊆ selected omega) <=
          (alpha / (1 - epsilon)) ^ Q.card) ∧
      1 - epsilon <= L.probability Good := by
  dsimp only
  let Good : Omega -> Prop := fun omega => ∀ j ∈ indices,
    ((tests j) ∩ selected omega).card < caps j
  obtain ⟨hGood, hsupported, hconditioned⟩ :=
    L.exists_conditionOn_cardCaps_of_jointInclusion
      selected tests caps indices alpha hjoint (hsum.trans_lt hepsilon)
  have hbad : L.probability (fun omega => ¬ Good omega) <= epsilon := by
    calc
      L.probability (fun omega => ¬ Good omega) <=
          L.probability (fun omega => Exists fun j => j ∈ indices ∧
            caps j <= ((tests j) ∩ selected omega).card) := by
        apply L.probability_mono
        intro omega hnot
        dsimp only [Good] at hnot
        push Not at hnot
        exact hnot
      _ <= ∑ j ∈ indices,
          L.probability (fun omega =>
            caps j <= ((tests j) ∩ selected omega).card) := by
        exact L.probability_exists_le indices (fun j omega =>
          caps j <= ((tests j) ∩ selected omega).card)
      _ <= ∑ j ∈ indices,
          ((tests j).powersetCard (caps j)).card * alpha ^ caps j := by
        exact sum_le_sum fun j _hj =>
          L.probability_card_inter_selected_ge_le_of_card_jointInclusion
            selected (tests j) alpha (caps j) hjoint
      _ <= epsilon := hsum
  have hlower : 1 - epsilon <= L.probability Good := by
    calc
      1 - epsilon <= 1 - L.probability (fun omega => ¬ Good omega) :=
        tsub_le_tsub_left hbad 1
      _ = L.probability (fun omega => ¬ ¬ Good omega) :=
        (L.probability_not (fun omega => ¬ Good omega)).symm
      _ = L.probability Good := by
        congr 1
        funext omega
        simp
  refine ⟨hGood, hsupported, ?_, hlower⟩
  intro Q
  apply (hconditioned Q).trans
  apply pow_le_pow_left'
  exact div_le_div_of_nonneg_left zero_le
    (tsub_pos_iff_lt.mpr hepsilon) hlower

end FiniteLaw

end

end Erdos207
