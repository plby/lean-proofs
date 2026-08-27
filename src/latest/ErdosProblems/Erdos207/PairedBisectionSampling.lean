/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.BalancedBisection

/-!
# Independent paired sampling of balanced bisections

Fix one balanced bisection and pair its left and right vertices by a
bijection.  One independent fair bit per pair decides which endpoint goes
to the new left side.  Every outcome is still exactly balanced, while the
independent coordinates permit the exponential lower-tail estimate needed
for link degrees.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

namespace BalancedBisection

/-- Pair the two equally sized sides of a balanced bisection. -/
def pairEquiv
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) : ↥B.left ≃ ↥B.right :=
  Fintype.equivOfCardEq (by simpa using B.card_right.symm)

/-- The endpoint put on the sampled left side by one pair bit. -/
def pairedLeftVertex
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (ω : ↥B.left → Bool)
    (a : ↥B.left) : V :=
  if ω a then a.1 else (B.pairEquiv a).1

/-- The other endpoint, put on the sampled right side. -/
def pairedRightVertex
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (ω : ↥B.left → Bool)
    (a : ↥B.left) : V :=
  if ω a then (B.pairEquiv a).1 else a.1

lemma pairedLeftVertex_injective
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (ω : ↥B.left → Bool) :
    Function.Injective (B.pairedLeftVertex ω) := by
  intro a c h
  by_cases ha : ω a = true <;> by_cases hc : ω c = true
  · simp only [pairedLeftVertex, ha, if_true, hc] at h
    exact Subtype.ext h
  · have hc' : ω c = false := Bool.eq_false_of_not_eq_true hc
    simp only [pairedLeftVertex, ha, if_true, hc', Bool.false_eq_true,
      if_false] at h
    have haR : a.1 ∈ B.right := by simpa only [h] using (B.pairEquiv c).2
    exact (Finset.disjoint_left.mp B.disjoint_left_right a.2 haR).elim
  · have ha' : ω a = false := Bool.eq_false_of_not_eq_true ha
    simp only [pairedLeftVertex, ha', Bool.false_eq_true, if_false, hc,
      if_true] at h
    have hcR : c.1 ∈ B.right := by simpa only [h] using (B.pairEquiv a).2
    exact (Finset.disjoint_left.mp B.disjoint_left_right c.2 hcR).elim
  · have ha' : ω a = false := Bool.eq_false_of_not_eq_true ha
    have hc' : ω c = false := Bool.eq_false_of_not_eq_true hc
    simp only [pairedLeftVertex, ha', hc', Bool.false_eq_true, if_false] at h
    exact B.pairEquiv.injective (Subtype.ext h)

lemma pairedRightVertex_injective
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (ω : ↥B.left → Bool) :
    Function.Injective (B.pairedRightVertex ω) := by
  intro a c h
  by_cases ha : ω a = true <;> by_cases hc : ω c = true
  · simp only [pairedRightVertex, ha, hc, if_true] at h
    exact B.pairEquiv.injective (Subtype.ext h)
  · have hc' : ω c = false := Bool.eq_false_of_not_eq_true hc
    simp only [pairedRightVertex, ha, if_true, hc', Bool.false_eq_true,
      if_false] at h
    have hcR : c.1 ∈ B.right := by simpa only [h] using (B.pairEquiv a).2
    exact (Finset.disjoint_left.mp B.disjoint_left_right c.2 hcR).elim
  · have ha' : ω a = false := Bool.eq_false_of_not_eq_true ha
    simp only [pairedRightVertex, ha', Bool.false_eq_true, if_false, hc,
      if_true] at h
    have haR : a.1 ∈ B.right := by simpa only [h] using (B.pairEquiv c).2
    exact (Finset.disjoint_left.mp B.disjoint_left_right a.2 haR).elim
  · have ha' : ω a = false := Bool.eq_false_of_not_eq_true ha
    have hc' : ω c = false := Bool.eq_false_of_not_eq_true hc
    simp only [pairedRightVertex, ha', hc', Bool.false_eq_true, if_false] at h
    exact Subtype.ext h

/-- The sampled left side. -/
def pairedLeft
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (ω : ↥B.left → Bool) : Finset V :=
  univ.image (B.pairedLeftVertex ω)

/-- The sampled right side. -/
def pairedRight
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (ω : ↥B.left → Bool) : Finset V :=
  univ.image (B.pairedRightVertex ω)

@[simp]
lemma mem_pairedLeft_iff
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    {B : BalancedBisection V W} {ω : ↥B.left → Bool} {x : V} :
    x ∈ B.pairedLeft ω ↔ ∃ a : ↥B.left, B.pairedLeftVertex ω a = x := by
  simp [pairedLeft]

@[simp]
lemma mem_pairedRight_iff
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    {B : BalancedBisection V W} {ω : ↥B.left → Bool} {x : V} :
    x ∈ B.pairedRight ω ↔ ∃ a : ↥B.left, B.pairedRightVertex ω a = x := by
  simp [pairedRight]

lemma pairedLeft_card
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (ω : ↥B.left → Bool) :
    (B.pairedLeft ω).card = B.left.card := by
  rw [pairedLeft, card_image_of_injective _ (B.pairedLeftVertex_injective ω),
    card_univ, Fintype.card_coe]

lemma pairedRight_card
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (ω : ↥B.left → Bool) :
    (B.pairedRight ω).card = B.left.card := by
  rw [pairedRight, card_image_of_injective _ (B.pairedRightVertex_injective ω),
    card_univ, Fintype.card_coe]

lemma pairedLeft_subset
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (ω : ↥B.left → Bool) :
    B.pairedLeft ω ⊆ W := by
  intro x hx
  obtain ⟨a, rfl⟩ := mem_pairedLeft_iff.mp hx
  by_cases ha : ω a = true
  · simp only [pairedLeftVertex, ha, if_true]
    exact B.left_subset a.2
  · have ha' : ω a = false := Bool.eq_false_of_not_eq_true ha
    simp only [pairedLeftVertex, ha', Bool.false_eq_true, if_false]
    exact (mem_sdiff.mp (B.pairEquiv a).2).1

lemma pairedRight_subset
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (ω : ↥B.left → Bool) :
    B.pairedRight ω ⊆ W := by
  intro x hx
  obtain ⟨a, rfl⟩ := mem_pairedRight_iff.mp hx
  by_cases ha : ω a = true
  · simp only [pairedRightVertex, ha, if_true]
    exact (mem_sdiff.mp (B.pairEquiv a).2).1
  · have ha' : ω a = false := Bool.eq_false_of_not_eq_true ha
    simp only [pairedRightVertex, ha', Bool.false_eq_true, if_false]
    exact B.left_subset a.2

lemma disjoint_paired
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (ω : ↥B.left → Bool) :
    Disjoint (B.pairedLeft ω) (B.pairedRight ω) := by
  rw [Finset.disjoint_left]
  intro x hxL hxR
  obtain ⟨a, ha⟩ := mem_pairedLeft_iff.mp hxL
  obtain ⟨c, hc⟩ := mem_pairedRight_iff.mp hxR
  have h : B.pairedLeftVertex ω a = B.pairedRightVertex ω c := ha.trans hc.symm
  by_cases hωa : ω a = true <;> by_cases hωc : ω c = true
  · simp only [pairedLeftVertex, pairedRightVertex, hωa, hωc, if_true] at h
    have haR : a.1 ∈ B.right := by simpa only [h] using (B.pairEquiv c).2
    exact (Finset.disjoint_left.mp B.disjoint_left_right a.2 haR).elim
  · have hωc' : ω c = false := Bool.eq_false_of_not_eq_true hωc
    simp only [pairedLeftVertex, pairedRightVertex, hωa, if_true, hωc',
      Bool.false_eq_true, if_false] at h
    have hac : a = c := Subtype.ext h
    subst c
    simp [hωa] at hωc'
  · have hωa' : ω a = false := Bool.eq_false_of_not_eq_true hωa
    simp only [pairedLeftVertex, pairedRightVertex, hωa',
      Bool.false_eq_true, if_false, hωc, if_true] at h
    have hac : a = c := B.pairEquiv.injective (Subtype.ext h)
    subst c
    simp [hωc] at hωa'
  · have hωa' : ω a = false := Bool.eq_false_of_not_eq_true hωa
    have hωc' : ω c = false := Bool.eq_false_of_not_eq_true hωc
    simp only [pairedLeftVertex, pairedRightVertex, hωa', hωc',
      Bool.false_eq_true, if_false] at h
    have hcR : c.1 ∈ B.right := by simpa only [h] using (B.pairEquiv a).2
    exact (Finset.disjoint_left.mp B.disjoint_left_right c.2 hcR).elim

lemma union_paired
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (ω : ↥B.left → Bool) :
    B.pairedLeft ω ∪ B.pairedRight ω = W := by
  apply Subset.antisymm
  · exact union_subset (B.pairedLeft_subset ω) (B.pairedRight_subset ω)
  · intro x hxW
    have hxUnion : x ∈ B.left ∪ B.right := by
      rw [B.union_left_right]
      exact hxW
    rcases mem_union.mp hxUnion with hxL | hxR
    · let a : ↥B.left := ⟨x, hxL⟩
      by_cases ha : ω a = true
      · apply mem_union_left
        exact mem_pairedLeft_iff.mpr ⟨a, by simp [pairedLeftVertex, ha, a]⟩
      · have ha' : ω a = false := Bool.eq_false_of_not_eq_true ha
        apply mem_union_right
        exact mem_pairedRight_iff.mpr ⟨a, by simp [pairedRightVertex, ha', a]⟩
    · let b : ↥B.right := ⟨x, hxR⟩
      let a : ↥B.left := B.pairEquiv.symm b
      have hab : B.pairEquiv a = b := B.pairEquiv.apply_symm_apply b
      by_cases ha : ω a = true
      · apply mem_union_right
        exact mem_pairedRight_iff.mpr ⟨a, by
          simp only [pairedRightVertex, ha, if_true]
          exact congrArg Subtype.val hab⟩
      · have ha' : ω a = false := Bool.eq_false_of_not_eq_true ha
        apply mem_union_left
        exact mem_pairedLeft_iff.mpr ⟨a, by
          simp only [pairedLeftVertex, ha', Bool.false_eq_true, if_false]
          exact congrArg Subtype.val hab⟩

/-- The balanced bisection generated by a family of independent pair bits. -/
def pairedBisection
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (ω : ↥B.left → Bool) :
    BalancedBisection V W where
  left := B.pairedLeft ω
  left_subset := B.pairedLeft_subset ω
  twice_card := by
    rw [B.pairedLeft_card ω, B.twice_card]

@[simp]
lemma pairedBisection_left
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (ω : ↥B.left → Bool) :
    (B.pairedBisection ω).left = B.pairedLeft ω := rfl

@[simp]
lemma pairedBisection_right
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (ω : ↥B.left → Bool) :
    (B.pairedBisection ω).right = B.pairedRight ω := by
  ext x
  constructor
  · intro hx
    have hxW := (mem_sdiff.mp hx).1
    have hxNotLeft := (mem_sdiff.mp hx).2
    have hxUnion : x ∈ B.pairedLeft ω ∪ B.pairedRight ω := by
      rw [B.union_paired ω]
      exact hxW
    rcases mem_union.mp hxUnion with hxL | hxR
    · exact (hxNotLeft hxL).elim
    · exact hxR
  · intro hxR
    apply mem_sdiff.mpr
    refine ⟨B.pairedRight_subset ω hxR, ?_⟩
    intro hxL
    exact Finset.disjoint_left.mp (B.disjoint_paired ω) hxL hxR

/-- Every paired-sampling outcome gives a balanced link partition of `W`. -/
theorem pairedBisection_isResidualPartition
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) (ω : ↥B.left → Bool)
    (center : V) (hcenter : center ∉ W) :
    let K := (B.pairedBisection ω).toBipartiteLink center hcenter
    K.center = center ∧ K.left ∪ K.right = W ∧
      K.left.card = K.right.card := by
  exact ⟨rfl, (B.pairedBisection ω).toBipartiteLink_union center hcenter,
    (B.pairedBisection ω).toBipartiteLink_balanced center hcenter⟩

/-- Independent fair bits on the fixed pairing. -/
def pairedLaw
    {V : Type*} [Fintype V] [DecidableEq V] {W : Finset V}
    (B : BalancedBisection V W) : FiniteLaw (↥B.left → Bool) :=
  FiniteLaw.independentBits (fun _ ↦ (1 / 2 : ℝ≥0)) (fun _ ↦ by norm_num)

end BalancedBisection

end

end Erdos207
