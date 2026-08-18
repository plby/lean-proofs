/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.RandomPartitionSharp
import ErdosProblems.Erdos186.CFP.RandomGreedyDenseWitness

/-!
# Additive random colouring with populated colour classes

The strong-inheritance theorem only records the stability and common-span
conclusions of the robust colouring.  The later greedy process also needs a
uniform lower bound for the cardinality of every colour.  We retain that
source fact by adjoining the whole source as one extra obstacle.  This costs
one event in the logarithmic term and no additional geometric hypothesis.
-/

namespace Erdos186.CFP.RandomPartition

open Stability

noncomputable section

/-- Sharp additive inheritance together with the population bound needed by
the greedy process.  The extra `+ 1` in the event count is precisely the
whole-source obstacle. -/
theorem exists_populated_coloring_stronglyStableFor_with_commonSpan_of_polynomial_bound_additive
    {A : Finset ℤ} {box : (d : ℕ) → GAP 1 d}
    {x maxRank differenceBound C0 q t n exponent : ℕ}
    {relevant : Finset ℕ} {φ : (d : ℕ) → ℤ → LatticePoint d}
    (hstable : StronglyStableFor A box x maxRank differenceBound relevant φ C0)
    (hφzero : ∀ d ∈ relevant, φ d 0 = 0)
    (hfamily : CanonicalObstaclePolynomialBound A box maxRank differenceBound
      relevant φ n exponent)
    (_hq : 0 < q)
    (hcapacity :
      (2 * q + 1) *
          (t + (Nat.log 2 ((n ^ exponent + 1) * (q + 1)) + 1)) ≤
        x / C0 + 1)
    (hpopulation :
      (2 * q + 1) *
          (t + (Nat.log 2 ((n ^ exponent + 1) * (q + 1)) + 1)) ≤
        A.card) :
    ∃ c : {a // a ∈ A} → Fin (q + 1),
      (∀ i, t < (colorClass c i).card) ∧
      (∀ i, StronglyStableFor (anchoredColorClass A c i) box t maxRank
        differenceBound relevant φ C0) ∧
      (∀ i d, d ∈ relevant →
        generatedSubgroup (φ d) (anchoredColorClass A c i) =
          generatedSubgroup (φ d) A) := by
  classical
  let W := WeakTraceIndex A box maxRank differenceBound
  let family : WeakBoxFamily W A box maxRank differenceBound :=
    canonicalWeakBoxFamily A box maxRank differenceBound
  let I := StrongObstacleIndex (W := W) A relevant φ
  let obstacle : Option I → Finset {a // a ∈ A}
    | none => Finset.univ
    | some o => strongObstacle family o
  let k := Nat.log 2 ((n ^ exponent + 1) * (q + 1)) + 1
  let G : {d // d ∈ relevant} → Type := fun d ↦ LatticePoint d.1
  let ψ : ∀ d, {a // a ∈ A} → G d := fun d a ↦ φ d.1 a.1
  have hspanSubtype :
      SpanRobust (⟨0, hstable.weaklyStable.zero_mem⟩ : {a // a ∈ A})
        Finset.univ (x / C0) relevant (fun d a ↦ φ d a.1) :=
    spanRobust_subtype hstable.spanRobust hstable.weaklyStable.zero_mem
  have hobstacle : ∀ o : Option I,
      (2 * q + 1) * (t + k) ≤ (obstacle o).card := by
    intro o
    cases o with
    | none =>
        simpa only [obstacle, Finset.card_univ, Fintype.card_coe] using
          hpopulation
    | some o =>
        change (2 * q + 1) * (t + k) ≤ (strongObstacle family o).card
        cases o with
        | inl w =>
            have hw := card_weakBoxObstacle_gt hstable.weaklyStable family w
            have hdiv : x / C0 ≤ x := Nat.div_le_self _ _
            exact hcapacity.trans ((Nat.succ_le_succ hdiv).trans
              (Nat.succ_le_iff.mpr hw))
        | inr w =>
            obtain ⟨S, hgen⟩ :=
              exists_closure_eq_of_mem_generatedSubgroupValues G ψ w.1 w.2.2.1
            have hgen' : generatedSubgroup (ψ w.1) S = w.2.1 := by
              simpa [generatedSubgroup] using hgen
            have hproperFull :
                w.2.1 < generatedSubgroup (ψ w.1) Finset.univ := by
              simpa [generatedSubgroup] using
                distinctSpanIndex_lt_closure_univ G ψ w
            have hw := card_outside_generatedSubgroup_gt hspanSubtype
              (Finset.mem_univ _) (hφzero w.1.1 w.1.2) w.1.2
              (B := S) (by rw [hgen']; exact hproperFull)
            have hobs : distinctSpanObstacle G ψ w =
                outsideGeneratedSubgroup (ψ w.1) Finset.univ S := by
              ext a
              simp [distinctSpanObstacle, outsideGeneratedSubgroup, hgen']
            change _ ≤ (distinctSpanObstacle G ψ w).card
            rw [hobs]
            exact hcapacity.trans (Nat.succ_le_iff.mpr hw)
  have heventsLe : Fintype.card (Option I) * (q + 1) ≤
      (n ^ exponent + 1) * (q + 1) := by
    apply Nat.mul_le_mul_right
    simpa only [Fintype.card_option] using Nat.add_le_add_right hfamily 1
  have hevents : Fintype.card (Option I) * (q + 1) < 2 ^ k :=
    heventsLe.trans_lt (by
      dsimp [k]
      exact Nat.lt_pow_succ_log_self Nat.one_lt_two _)
  obtain ⟨c, hc⟩ := exists_coloring_robust_on_obstacles_additive
    (obstacle := obstacle) hevents hobstacle
  refine ⟨c, ?_,
    stronglyStableFor_anchoredColorClass_of_robust_obstacles
      hstable family c (fun o i ↦ hc (some o) i),
    anchoredColorClass_generatedSubgroup_eq_of_robust_obstacles
      hstable family c (fun o i ↦ hc (some o) i)⟩
  intro i
  simpa only [obstacle, Finset.inter_univ] using hc none i

/-- Restrict a colouring to the nonzero source.  The anchor is reinserted by
`anchoredColorClass`, so the anchored classes do not change. -/
def restrictEraseZeroColoring (B : Finset ℤ) {q : ℕ}
    (c : {a // a ∈ B} → Fin (q + 1)) :
    {a // a ∈ B.erase 0} → Fin (q + 1) :=
  fun a ↦ c ⟨a.1, Finset.erase_subset 0 B a.2⟩

theorem anchoredColorClass_restrictEraseZeroColoring
    (B : Finset ℤ) {q : ℕ}
    (c : {a // a ∈ B} → Fin (q + 1)) (i : Fin (q + 1)) :
    anchoredColorClass (B.erase 0) (restrictEraseZeroColoring B c) i =
      anchoredColorClass B c i := by
  ext z
  simp only [anchoredColorClass, Finset.mem_insert, Finset.mem_map,
    mem_colorClass_iff]
  constructor
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · exact Or.inl rfl
    · right
      refine ⟨⟨a.1, Finset.erase_subset 0 B a.2⟩, ?_, rfl⟩
      exact ha
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · exact Or.inl rfl
    · by_cases ha0 : a.1 = 0
      · exact Or.inl ha0
      · right
        let a' : {z // z ∈ B.erase 0} :=
          ⟨a.1, Finset.mem_erase.mpr ⟨ha0, a.2⟩⟩
        refine ⟨a', ?_, rfl⟩
        change c ⟨a.1, Finset.erase_subset 0 B a'.2⟩ = i
        simpa only [a'] using ha

/-- A populated colouring of a zero-containing core, restricted to its
nonzero part.  A colour can lose at most the point zero, so the strict
population bound becomes the weak bound exactly required by greedy
selection. -/
theorem exists_populated_eraseZero_coloring_stronglyStableFor_with_commonSpan_of_polynomial_bound_additive
    {B : Finset ℤ} {box : (d : ℕ) → GAP 1 d}
    {x maxRank differenceBound C0 q t n exponent : ℕ}
    {relevant : Finset ℕ} {φ : (d : ℕ) → ℤ → LatticePoint d}
    (hstable : StronglyStableFor B box x maxRank differenceBound relevant φ C0)
    (hφzero : ∀ d ∈ relevant, φ d 0 = 0)
    (hfamily : CanonicalObstaclePolynomialBound B box maxRank differenceBound
      relevant φ n exponent)
    (hq : 0 < q)
    (hcapacity :
      (2 * q + 1) *
          (t + (Nat.log 2 ((n ^ exponent + 1) * (q + 1)) + 1)) ≤
        x / C0 + 1)
    (hpopulation :
      (2 * q + 1) *
          (t + (Nat.log 2 ((n ^ exponent + 1) * (q + 1)) + 1)) ≤
        B.card) :
    ∃ c : {a // a ∈ B.erase 0} → Fin (q + 1),
      (∀ i, t ≤ (integerColorClass (B.erase 0) c i).card) ∧
      (∀ i, StronglyStableFor (anchoredColorClass (B.erase 0) c i) box t
        maxRank differenceBound relevant φ C0) ∧
      (∀ i d, d ∈ relevant →
        generatedSubgroup (φ d) (anchoredColorClass (B.erase 0) c i) =
          generatedSubgroup (φ d) B) := by
  classical
  obtain ⟨c, hcard, hstableColor, hspan⟩ :=
    exists_populated_coloring_stronglyStableFor_with_commonSpan_of_polynomial_bound_additive
      hstable hφzero hfamily hq hcapacity hpopulation
  let c' := restrictEraseZeroColoring B c
  refine ⟨c', ?_, ?_, ?_⟩
  · intro i
    have hsubset : integerColorClass B c i ⊆
        insert 0 (integerColorClass (B.erase 0) c' i) := by
      intro z hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hz
      by_cases ha0 : a.1 = 0
      · exact Finset.mem_insert.mpr (Or.inl ha0)
      · apply Finset.mem_insert.mpr
        right
        let a' : {z // z ∈ B.erase 0} :=
          ⟨a.1, Finset.mem_erase.mpr ⟨ha0, a.2⟩⟩
        apply Finset.mem_map.mpr
        refine ⟨a', ?_, rfl⟩
        apply mem_colorClass_iff.mpr
        change c ⟨a.1, Finset.erase_subset 0 B a'.2⟩ = i
        simpa only [c', restrictEraseZeroColoring, a'] using
          (mem_colorClass_iff.mp ha)
    have hcardFull : (colorClass c i).card =
        (integerColorClass B c i).card := by
      simp only [integerColorClass, Finset.card_map]
    have hcardLe : (colorClass c i).card ≤
        (integerColorClass (B.erase 0) c' i).card + 1 := by
      rw [hcardFull]
      exact (Finset.card_le_card hsubset).trans (Finset.card_insert_le _ _)
    have hstrict : t <
        (integerColorClass (B.erase 0) c' i).card + 1 :=
      (hcard i).trans_le hcardLe
    omega
  · intro i
    rw [anchoredColorClass_restrictEraseZeroColoring B c i]
    exact hstableColor i
  · intro i d hd
    rw [anchoredColorClass_restrictEraseZeroColoring B c i]
    exact hspan i d hd

/-- One extra retained point makes the nonzero colour classes strictly
larger than the deletion budget.  Stability is then restricted back from
`t+1` deletions to `t`; this is the exact interface required by the dyadic
range adapter. -/
theorem exists_strictlyPopulated_eraseZero_coloring_stronglyStableFor_with_commonSpan_of_polynomial_bound_additive
    {B : Finset ℤ} {box : (d : ℕ) → GAP 1 d}
    {x maxRank differenceBound C0 q t n exponent : ℕ}
    {relevant : Finset ℕ} {φ : (d : ℕ) → ℤ → LatticePoint d}
    (hstable : StronglyStableFor B box x maxRank differenceBound relevant φ C0)
    (hφzero : ∀ d ∈ relevant, φ d 0 = 0)
    (hfamily : CanonicalObstaclePolynomialBound B box maxRank differenceBound
      relevant φ n exponent)
    (hq : 0 < q)
    (hcapacity :
      (2 * q + 1) *
          ((t + 1) +
            (Nat.log 2 ((n ^ exponent + 1) * (q + 1)) + 1)) ≤
        x / C0 + 1)
    (hpopulation :
      (2 * q + 1) *
          ((t + 1) +
            (Nat.log 2 ((n ^ exponent + 1) * (q + 1)) + 1)) ≤
        B.card) :
    ∃ c : {a // a ∈ B.erase 0} → Fin (q + 1),
      (∀ i, t < (integerColorClass (B.erase 0) c i).card) ∧
      (∀ i, StronglyStableFor (anchoredColorClass (B.erase 0) c i) box t
        maxRank differenceBound relevant φ C0) ∧
      (∀ i d, d ∈ relevant →
        generatedSubgroup (φ d) (anchoredColorClass (B.erase 0) c i) =
          generatedSubgroup (φ d) B) := by
  obtain ⟨c, hcard, hstableColor, hspan⟩ :=
    exists_populated_eraseZero_coloring_stronglyStableFor_with_commonSpan_of_polynomial_bound_additive
      (t := t + 1) hstable hφzero hfamily hq hcapacity hpopulation
  refine ⟨c, ?_, ?_, hspan⟩
  · intro i
    exact Nat.lt_of_succ_le (hcard i)
  · intro i
    exact (hstableColor i).mono_deletionBudget (by omega)

end

end Erdos186.CFP.RandomPartition

#print axioms
  Erdos186.CFP.RandomPartition.exists_populated_coloring_stronglyStableFor_with_commonSpan_of_polynomial_bound_additive
#print axioms
  Erdos186.CFP.RandomPartition.exists_populated_eraseZero_coloring_stronglyStableFor_with_commonSpan_of_polynomial_bound_additive
#print axioms
  Erdos186.CFP.RandomPartition.exists_strictlyPopulated_eraseZero_coloring_stronglyStableFor_with_commonSpan_of_polynomial_bound_additive
