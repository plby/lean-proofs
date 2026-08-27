/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberOrderGeometricTails
import ErdosProblems.Erdos207.AbsorberCoefficientBounds

/-! # Polynomially many crude statistics at a greedy state -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

abbrev CrudeOrderIndex (q d : ℕ) :=
  {p : Fin (q + 1) × Fin (q + 1) // p.2.val + d ≤ p.1.val}

def CrudeOrderIndex.order {q d : ℕ} (i : CrudeOrderIndex q d) : ℕ := i.1.1.val
def CrudeOrderIndex.chosen {q d : ℕ} (i : CrudeOrderIndex q d) : ℕ := i.1.2.val

theorem CrudeOrderIndex.budget {q d : ℕ} (i : CrudeOrderIndex q d) :
    i.chosen + d ≤ i.order := i.2

theorem CrudeOrderIndex.order_le {q d : ℕ} (i : CrudeOrderIndex q d) : i.order ≤ q :=
  Nat.le_of_lt_succ i.1.1.isLt

abbrev DistinctTripleRoots (V : Type*) [DecidableEq V] :=
  {p : TripleOn V × TripleOn V // p.1 ≠ p.2}

abbrev CrudeStatisticIndex (V : Type*) [DecidableEq V] (q : ℕ) :=
  (CrudeOrderIndex q 5 × DistinctTripleRoots V) ⊕
    ((TripleOn V × PairOn V) ⊕ ((TripleOn V × TripleOn V) ⊕ (CrudeOrderIndex q 4 × TripleOn V)))

structure CrudeThresholds where
  rooted : ℕ → ℕ → ℝ≥0
  pair : ℝ≥0
  common : ℝ≥0
  gain : ℕ → ℕ → ℝ≥0

def crudeStatistic {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) : CrudeStatisticIndex V q → ℝ≥0
  | .inl (i, roots) => (greedyRootedConfigurationClass (forbiddenFamilyOfOrder F i.order)
      S {roots.1.1, roots.1.2} i.chosen).card
  | .inr (.inl (T, P)) => selectedCount
      (fun u : PairTwoAwayThreatWitness V F T P ↦ pairTwoAwayThreatRemainder u) S.chosen
  | .inr (.inr (.inl (T, T'))) => selectedCount
      (fun u : CommonThreatWitness F F T T' ↦ u.remainder) S.chosen
  | .inr (.inr (.inr (i, T))) =>
      greedyActiveGainDefectCount (forbiddenFamilyOfOrder F i.order) F S T i.chosen

def crudeThreshold {V : Type*} [DecidableEq V] {q : ℕ}
    (K : CrudeThresholds) : CrudeStatisticIndex V q → ℝ≥0
  | .inl (i, _) => K.rooted i.order i.chosen
  | .inr (.inl _) => K.pair
  | .inr (.inr (.inl _)) => K.common
  | .inr (.inr (.inr (i, _))) => K.gain i.order i.chosen

def CrudeStateBounds {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (q : ℕ) (K : CrudeThresholds) : Prop :=
  ∀ i : CrudeStatisticIndex V q, crudeStatistic F S i < crudeThreshold K i

theorem card_crudeOrderIndex_le (q d : ℕ) :
    Fintype.card (CrudeOrderIndex q d) ≤ (q + 1) ^ 2 := by
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using
    Fintype.card_subtype_le (fun p : Fin (q + 1) × Fin (q + 1) ↦ p.2.val + d ≤ p.1.val)

theorem card_distinctTripleRoots_le (V : Type*) [Fintype V] [DecidableEq V] :
    Fintype.card (DistinctTripleRoots V) ≤ Fintype.card (TripleOn V) ^ 2 := by
  simpa only [Fintype.card_prod, pow_two] using
    Fintype.card_subtype_le (fun p : TripleOn V × TripleOn V ↦ p.1 ≠ p.2)

theorem card_crudeStatisticIndex_le (V : Type*) [Fintype V] [DecidableEq V] (q : ℕ) :
    Fintype.card (CrudeStatisticIndex V q) ≤
      (q + 1) ^ 2 * Fintype.card (TripleOn V) ^ 2 +
        (Fintype.card (TripleOn V) * Fintype.card (PairOn V) +
          (Fintype.card (TripleOn V) ^ 2 + (q + 1) ^ 2 * Fintype.card (TripleOn V))) := by
  simp only [CrudeStatisticIndex, Fintype.card_sum, Fintype.card_prod, ← pow_two]
  exact Nat.add_le_add
    (Nat.mul_le_mul (card_crudeOrderIndex_le q 5) (card_distinctTripleRoots_le V))
    (Nat.add_le_add le_rfl (Nat.add_le_add le_rfl
      (Nat.mul_le_mul_right _ (card_crudeOrderIndex_le q 4))))

theorem card_crudeStatisticIndex_le_polynomial
    (V : Type*) [Fintype V] [DecidableEq V] (q : ℕ) :
    Fintype.card (CrudeStatisticIndex V q) ≤ 4 * (q + 1) ^ 2 * (Fintype.card V + 1) ^ 6 := by
  let N := Fintype.card V + 1
  let a := (q + 1) ^ 2
  have hNV : Fintype.card V ≤ N := Nat.le_succ _
  have ht : Fintype.card (TripleOn V) ≤ N ^ 3 :=
    (card_tripleOn_le_cube V).trans (Nat.pow_le_pow_left hNV 3)
  have hp : Fintype.card (PairOn V) ≤ N ^ 2 :=
    (card_pairOn_le_sq V).trans (Nat.pow_le_pow_left hNV 2)
  have hN : 1 ≤ N := by dsimp [N]; omega
  have ha : 1 ≤ a := by
    have h : 0 < a := by dsimp [a]; positivity
    omega
  have hN3 : N ^ 3 ≤ N ^ 6 := Nat.pow_le_pow_right hN (by omega)
  have hN5 : N ^ 5 ≤ N ^ 6 := Nat.pow_le_pow_right hN (by omega)
  have htt : Fintype.card (TripleOn V) ^ 2 ≤ N ^ 6 := by
    calc
      _ ≤ (N ^ 3) ^ 2 := Nat.pow_le_pow_left ht 2
      _ = _ := by ring
  have htp : Fintype.card (TripleOn V) * Fintype.card (PairOn V) ≤ a * N ^ 6 := by
    calc
      _ ≤ N ^ 3 * N ^ 2 := Nat.mul_le_mul ht hp
      _ = N ^ 5 := by ring
      _ ≤ N ^ 6 := hN5
      _ ≤ a * N ^ 6 := Nat.le_mul_of_pos_left _ ha
  have htt' : Fintype.card (TripleOn V) ^ 2 ≤ a * N ^ 6 :=
    htt.trans (Nat.le_mul_of_pos_left _ ha)
  have ht' : a * Fintype.card (TripleOn V) ≤ a * N ^ 6 := Nat.mul_le_mul_left _ (ht.trans hN3)
  have htt'' : a * Fintype.card (TripleOn V) ^ 2 ≤ a * N ^ 6 := Nat.mul_le_mul_left _ htt
  have hsum := card_crudeStatisticIndex_le V q
  change Fintype.card (CrudeStatisticIndex V q) ≤ 4 * a * N ^ 6
  change Fintype.card (CrudeStatisticIndex V q) ≤
    a * Fintype.card (TripleOn V) ^ 2 + (Fintype.card (TripleOn V) * Fintype.card (PairOn V) +
      (Fintype.card (TripleOn V) ^ 2 + a * Fintype.card (TripleOn V))) at hsum
  calc
    _ ≤ a * N ^ 6 + (a * N ^ 6 + (a * N ^ 6 + a * N ^ 6)) :=
      hsum.trans (Nat.add_le_add htt'' (Nat.add_le_add htp (Nat.add_le_add htt' ht')))
    _ = _ := by ring

end

end Erdos207
