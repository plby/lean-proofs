/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexIndexedWeight
import ErdosProblems.Erdos207.VortexIndexedSharpWeight

/-!
# Aggregating the indexed vortex bounds

Minimal forbidden outside parts arising from configurations of order at
least five are partitioned by their number of outside triangles.  The
partition is exact (different indices have different cardinalities), so the
level-weighted extension sum is the sum of the indexed extension sums.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The union of all order-at-least-five absorber-induced families, indexed
by the size parameter used in KSSS. -/
def absorberIndexedForbiddenConfigurationsOn
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) : ForbiddenFamilyOn V :=
  (Icc 3 q).biUnion fun j ↦ absorberInducedConfigurationsOn q j B

@[simp]
lemma mem_absorberIndexedForbiddenConfigurationsOn_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B S : TripleSystemOn V} :
    S ∈ absorberIndexedForbiddenConfigurationsOn q B ↔
      ∃ j, 3 ≤ j ∧ j ≤ q ∧
        S ∈ absorberInducedConfigurationsOn q j B := by
  simp [absorberIndexedForbiddenConfigurationsOn, and_assoc]

lemma absorberIndexedForbiddenConfigurationsOn_subset_erdosForbidden
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} :
    absorberIndexedForbiddenConfigurationsOn q B ⊆
      absorberErdosForbiddenConfigurationsOn q B := by
  intro S hS
  obtain ⟨j, hj3, _hjq, hSj⟩ :=
    mem_absorberIndexedForbiddenConfigurationsOn_iff.mp hS
  exact absorberInducedConfigurationsOn_subset_erdosForbidden hj3 hSj

/-- The indexed union is exactly the portion of the absorber forbidden
family witnessed by a minimal configuration of order at least five. -/
lemma mem_absorberIndexedForbiddenConfigurationsOn_iff_highOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B S : TripleSystemOn V} :
    S ∈ absorberIndexedForbiddenConfigurationsOn q B ↔
      S.Nonempty ∧ ∃ rho, 5 ≤ rho ∧ rho ≤ q ∧
        ∃ E : TripleSystemOn V, IsErdosConfigOn rho E ∧ E \ B = S := by
  constructor
  · intro hS
    obtain ⟨j, hj3, _hjq, hSj⟩ :=
      mem_absorberIndexedForbiddenConfigurationsOn_iff.mp hS
    obtain ⟨hcard, rho, hrho5, hrhoq, E, hE, hEout⟩ :=
      mem_absorberInducedConfigurationsOn_iff.mp hSj
    refine ⟨?_, rho, hrho5, hrhoq, E, hE, hEout⟩
    rw [nonempty_iff_ne_empty]
    intro hEmpty
    rw [hEmpty, card_empty] at hcard
    omega
  · rintro ⟨hS, rho, hrho5, hrhoq, E, hE, hEout⟩
    let j := S.card + 2
    have hj3 : 3 ≤ j := by
      have hpos := card_pos.mpr hS
      dsimp only [j]
      omega
    have hSE : S ⊆ E := by
      intro T hTS
      have hTEB : T ∈ E \ B := by simpa only [hEout] using hTS
      exact (mem_sdiff.mp hTEB).1
    have hcardSE := card_le_card hSE
    have hEcard := hE.1.1
    have hjq : j ≤ q := by
      dsimp only [j]
      omega
    apply mem_absorberIndexedForbiddenConfigurationsOn_iff.mpr
    refine ⟨j, hj3, hjq, ?_⟩
    apply mem_absorberInducedConfigurationsOn_iff.mpr
    refine ⟨by dsimp only [j]; omega,
      rho, hrho5, hrhoq, E, hE, hEout⟩

lemma absorberInduced_pairwiseDisjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) :
    Set.PairwiseDisjoint (↑(Icc 3 q))
      (fun j ↦ absorberInducedConfigurationsOn q j B) := by
  intro i hi j hj hij
  apply disjoint_left.mpr
  intro S hSi hSj
  have hi3 := (mem_Icc.mp hi).1
  have hj3 := (mem_Icc.mp hj).1
  have hcardi := (mem_absorberInducedConfigurationsOn_iff.mp hSi).1
  have hcardj := (mem_absorberInducedConfigurationsOn_iff.mp hSj).1
  omega

/-- Exact decomposition of a weighted extension sum over the indexed union. -/
theorem extensionWeight_absorberIndexedForbidden_eq_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B : TripleSystemOn V) (p : TripleOn V → ℝ≥0)
    (R : TripleSystemOn V) :
    extensionWeight
        (fun E : absorberIndexedForbiddenConfigurationsOn q B ↦ E.1)
        p R =
      ∑ j ∈ Icc 3 q,
        extensionWeight
          (fun E : absorberInducedConfigurationsOn q j B ↦ E.1) p R := by
  classical
  unfold extensionWeight
  calc
    (∑ E : absorberIndexedForbiddenConfigurationsOn q B,
        if R ⊆ E.1 then setWeight p (E.1 \ R) else 0) =
        ∑ E ∈ absorberIndexedForbiddenConfigurationsOn q B,
          if R ⊆ E then setWeight p (E \ R) else 0 := by
      exact (Finset.sum_subtype _ (by simp)
        (fun E ↦ if R ⊆ E then setWeight p (E \ R) else 0)).symm
    _ = ∑ j ∈ Icc 3 q,
        ∑ E ∈ absorberInducedConfigurationsOn q j B,
          if R ⊆ E then setWeight p (E \ R) else 0 := by
      exact Finset.sum_biUnion (absorberInduced_pairwiseDisjoint q B)
    _ = ∑ j ∈ Icc 3 q,
        ∑ E : absorberInducedConfigurationsOn q j B,
          if R ⊆ E.1 then setWeight p (E.1 \ R) else 0 := by
      apply sum_congr rfl
      intro j _hj
      exact Finset.sum_subtype _ (by simp)
        (fun E ↦ if R ⊆ E then setWeight p (E \ R) else 0)

/-- Sum of the W1 coefficients for the order-at-least-five indexed union. -/
def indexedForbiddenVortexExtensionCoefficient
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (q : ℕ) (B : TripleSystemOn V) : ℕ :=
  ∑ j ∈ Icc 3 q, (j + 1) ^ ell *
    indexedInducedVortexSpreadCoefficient q ell B W.terminalSize

/-- The whole order-at-least-five forbidden family has an
ambient-size-free level-weighted extension bound above every nonempty root. -/
theorem extensionWeight_absorberIndexedForbidden_vortex_nonempty_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell q : ℕ}
    (W : Vortex V ell) (B : TripleSystemOn V) (c : ℝ≥0)
    (hc : c ≤ 1)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    (R : TripleSystemOn V) (hR : R.Nonempty) :
    extensionWeight
        (fun E : absorberIndexedForbiddenConfigurationsOn q B ↦ E.1)
        (vortexTripleWeight W c) R ≤
      (indexedForbiddenVortexExtensionCoefficient W q B : ℝ≥0) := by
  rw [extensionWeight_absorberIndexedForbidden_eq_sum]
  unfold indexedForbiddenVortexExtensionCoefficient
  push_cast
  apply sum_le_sum
  intro j hj
  have hj3 := (mem_Icc.mp hj).1
  by_cases hRcard : R.card ≤ j - 2
  · simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
      (extensionWeight_absorberInduced_vortex_nonempty_le
        (q := q) (j := j) W B c hj3 hc houter hterminal R hR hRcard)
  · have hzero : extensionWeight
        (fun E : absorberInducedConfigurationsOn q j B ↦ E.1)
        (vortexTripleWeight W c) R = 0 := by
      unfold extensionWeight
      apply sum_eq_zero
      intro E _hE
      rw [if_neg]
      intro hRE
      apply hRcard
      calc
        R.card ≤ E.1.card := card_le_card hRE
        _ = j - 2 :=
          (mem_absorberInducedConfigurationsOn_iff.mp E.2).1
    rw [hzero]
    exact bot_le

/-- Aggregate W1 estimate retaining the density power belonging to every
unplanted triangle. -/
theorem extensionWeight_absorberIndexedForbidden_vortex_nonempty_le_sharp
    {V : Type*} [Fintype V] [DecidableEq V] {ell q : ℕ}
    (W : Vortex V ell) (B : TripleSystemOn V) (c : ℝ≥0)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    (R : TripleSystemOn V) (hR : R.Nonempty) :
    extensionWeight
        (fun E : absorberIndexedForbiddenConfigurationsOn q B ↦ E.1)
        (vortexTripleWeight W c) R ≤
      ∑ j ∈ Icc 3 q,
        (((j + 1) ^ ell *
          indexedInducedVortexSpreadCoefficient q ell B W.terminalSize : ℕ) :
            ℝ≥0) * c ^ (j - 2 - R.card) := by
  rw [extensionWeight_absorberIndexedForbidden_eq_sum]
  apply sum_le_sum
  intro j hj
  have hj3 := (mem_Icc.mp hj).1
  by_cases hRcard : R.card ≤ j - 2
  · exact extensionWeight_absorberInduced_vortex_nonempty_le_sharp
      (q := q) (j := j) W B c hj3 houter hterminal R hR hRcard
  · have hzero : extensionWeight
        (fun E : absorberInducedConfigurationsOn q j B ↦ E.1)
        (vortexTripleWeight W c) R = 0 := by
      unfold extensionWeight
      apply sum_eq_zero
      intro E _hE
      rw [if_neg]
      intro hRE
      apply hRcard
      calc
        R.card ≤ E.1.card := card_le_card hRE
        _ = j - 2 :=
          (mem_absorberInducedConfigurationsOn_iff.mp E.2).1
    rw [hzero]
    exact bot_le

/-- W4 gives the sharper aggregate coefficient at a singleton root. -/
theorem extensionWeight_absorberIndexedForbidden_vortex_singleton_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell q : ℕ}
    (W : Vortex V ell) (B : TripleSystemOn V) (c : ℝ≥0)
    (hc : c ≤ 1)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize) (T : TripleOn V) :
    extensionWeight
        (fun E : absorberIndexedForbiddenConfigurationsOn q B ↦ E.1)
        (vortexTripleWeight W c) {T} ≤
      ((∑ j ∈ Icc 3 q,
        (j + 1) ^ ell * inducedVortexCoefficient q ell B : ℕ) : ℝ≥0) := by
  rw [extensionWeight_absorberIndexedForbidden_eq_sum]
  push_cast
  apply sum_le_sum
  intro j hj
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
    (extensionWeight_absorberInduced_vortex_singleton_le
      (q := q) (j := j) W B c (mem_Icc.mp hj).1 hc houter hterminal T)

/-- The aggregate W4 estimate retaining the exact phase-density power in
each indexed family. -/
theorem extensionWeight_absorberIndexedForbidden_vortex_singleton_le_sharp
    {V : Type*} [Fintype V] [DecidableEq V] {ell q : ℕ}
    (W : Vortex V ell) (B : TripleSystemOn V) (c : ℝ≥0)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize) (T : TripleOn V) :
    extensionWeight
        (fun E : absorberIndexedForbiddenConfigurationsOn q B ↦ E.1)
        (vortexTripleWeight W c) {T} ≤
      ∑ j ∈ Icc 3 q,
        (((j + 1) ^ ell * inducedVortexCoefficient q ell B : ℕ) : ℝ≥0) *
          c ^ (j - 3) := by
  rw [extensionWeight_absorberIndexedForbidden_eq_sum]
  apply sum_le_sum
  intro j hj
  exact extensionWeight_absorberInduced_vortex_singleton_le_sharp
    (q := q) (j := j) W B c (mem_Icc.mp hj).1 houter hterminal T

end

end Erdos207
