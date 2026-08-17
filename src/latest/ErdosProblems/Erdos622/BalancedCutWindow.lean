/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos622.GoodCut
import ErdosProblems.Erdos622.Counting
import ErdosProblems.Erdos622.BinomialCLT

/-!
# Exact powerset transport across a balanced cut

This file contains the finite bijections needed to transfer the two-block
binomial count used in the almost-bipartite case from arbitrary cut sides to
the standard coordinate sets `Fin n`.
-/

namespace Erdos622

open Set

attribute [local instance] Classical.propDecidable

/-- The cardinality of a filter depends only on the pointwise predicate, not
on the particular decision procedures used to form the two finsets. -/
theorem filter_card_congr
    {α : Type*} [DecidableEq α] (U : Finset α)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ x, P x ↔ Q x) :
    (U.filter P).card = (U.filter Q).card := by
  congr 1
  ext x
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ ↦ h x

/-- `pairCount` is independent of the particular decidability witnesses and
respects pointwise equivalence of its event predicates. -/
theorem pairCount_congr
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (V : Finset β)
    (P Q : Finset α → Finset β → Prop)
    [DecidablePred (Function.uncurry P)]
    [DecidablePred (Function.uncurry Q)]
    (h : ∀ X Y, P X Y ↔ Q X Y) :
    Counting.pairCount U V P = Counting.pairCount U V Q := by
  unfold Counting.pairCount
  congr 1
  ext p
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ ↦ h p.1 p.2

/-- Subsets of a finite set are equivalent to finsets of its subtype. -/
def powersetSubtypeEquiv {α : Type*} [DecidableEq α] (U : Finset α) :
    ↥(U.powerset) ≃ Finset U where
  toFun X := X.1.subtype (· ∈ U)
  invFun Y := ⟨Y.map (Function.Embedding.subtype (· ∈ U)), by
    rw [Finset.mem_powerset]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact y.property⟩
  left_inv X := by
    apply Subtype.ext
    exact Finset.subtype_map_of_mem (Finset.mem_powerset.mp X.2)
  right_inv Y := by
    ext x
    simp

/-- A cardinality equality transports the whole powerset to the powerset of
the standard `n`-element coordinate type. -/
noncomputable def powersetEquivOfCardEq {α : Type*} [DecidableEq α]
    (U : Finset α) {n : ℕ} (hU : U.card = n) :
    ↥(U.powerset) ≃ ↥((Finset.univ : Finset (Fin n)).powerset) :=
  let eUniv : Fin n ≃ ↥(Finset.univ : Finset (Fin n)) :=
    { toFun := fun x ↦ ⟨x, Finset.mem_univ x⟩
      invFun := fun x ↦ x.1
      left_inv := fun _ ↦ rfl
      right_inv := fun x ↦ Subtype.ext rfl }
  (powersetSubtypeEquiv U).trans <|
    (U.equivFinOfCardEq hU).finsetCongr.trans <|
      eUniv.finsetCongr.trans <|
        (powersetSubtypeEquiv (Finset.univ : Finset (Fin n))).symm

/-- The preceding powerset equivalence preserves the size of the selected
subset. -/
theorem powersetEquivOfCardEq_card {α : Type*} [DecidableEq α]
    (U : Finset α) {n : ℕ} (hU : U.card = n)
    (X : U.powerset) :
    ((powersetEquivOfCardEq U hU X :
      ↥((Finset.univ : Finset (Fin n)).powerset)) : Finset (Fin n)).card =
      X.1.card := by
  classical
  simp [powersetEquivOfCardEq, powersetSubtypeEquiv,
    Finset.filter_eq_self.mpr (Finset.mem_powerset.mp X.2)]

/-- Splitting a subset of the ambient vertex set by a cut gives an exact
bijection with a pair of subsets of the two cut sides. -/
theorem cutPowerset_filter_card_eq_pairCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (A B : Finset V) (hcut : IsCut A B)
    (P : Finset V → Finset V → Prop)
    [DecidablePred (Function.uncurry P)]
    [DecidablePred (fun S ↦ P (S ∩ A) (S ∩ B))] :
    (((Finset.univ : Finset V).powerset.filter fun S ↦
        P (S ∩ A) (S ∩ B)).card) =
      Counting.pairCount A B P := by
  classical
  unfold Counting.pairCount
  refine Finset.card_bij'
      (fun S _ ↦ (S ∩ A, S ∩ B))
      (fun p _ ↦ p.1 ∪ p.2) ?_ ?_ ?_ ?_
  · intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hSU, hP⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
        Finset.mem_powerset.mpr Finset.inter_subset_right⟩, hP⟩
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpProd, hpP⟩
    rcases Finset.mem_product.mp hpProd with ⟨hpA, hpB⟩
    have hpAsub : p.1 ⊆ A := Finset.mem_powerset.mp hpA
    have hpBsub : p.2 ⊆ B := Finset.mem_powerset.mp hpB
    have hinterA : (p.1 ∪ p.2) ∩ A = p.1 := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).1 with hx1 | hx2
        · exact hx1
        · exact (Finset.disjoint_left.mp hcut.1 (Finset.mem_inter.mp hx).2
            (hpBsub hx2)).elim
      · intro hx
        exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hx, hpAsub hx⟩
    have hinterB : (p.1 ∪ p.2) ∩ B = p.2 := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).1 with hx1 | hx2
        · exact (Finset.disjoint_left.mp hcut.1 (hpAsub hx1)
            (Finset.mem_inter.mp hx).2).elim
        · exact hx2
      · intro hx
        exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hx, hpBsub hx⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    change P p.1 p.2 at hpP
    simpa only [hinterA, hinterB] using hpP
  · intro S hS
    apply Finset.ext
    intro x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_inter.mp hx).1
      · exact (Finset.mem_inter.mp hx).1
    · intro hxS
      have hxAB : x ∈ A ∪ B := by
        rw [hcut.2]
        exact Finset.mem_univ x
      rcases Finset.mem_union.mp hxAB with hxA | hxB
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxS, hxA⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxS, hxB⟩)
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpProd, _⟩
    rcases Finset.mem_product.mp hpProd with ⟨hpA, hpB⟩
    have hpAsub : p.1 ⊆ A := Finset.mem_powerset.mp hpA
    have hpBsub : p.2 ⊆ B := Finset.mem_powerset.mp hpB
    apply Prod.ext
    · ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).1 with hx1 | hx2
        · exact hx1
        · exact (Finset.disjoint_left.mp hcut.1 (Finset.mem_inter.mp hx).2
            (hpBsub hx2)).elim
      · intro hx
        exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hx, hpAsub hx⟩
    · ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).1 with hx1 | hx2
        · exact (Finset.disjoint_left.mp hcut.1 (hpAsub hx1)
            (Finset.mem_inter.mp hx).2).elim
        · exact hx2
      · intro hx
        exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hx, hpBsub hx⟩

/-- A predicate depending only on the two selected cardinalities has the same
two-block count on arbitrary `n`-element finite sets as on two copies of
`Fin n`. -/
theorem pairCount_card_transport
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (V : Finset β) {n : ℕ}
    (hU : U.card = n) (hV : V.card = n)
    (P : ℕ → ℕ → Prop)
    [DecidablePred (Function.uncurry (fun (X : Finset α) (Y : Finset β) ↦
      P X.card Y.card))]
    [DecidablePred (Function.uncurry
      (fun (X Y : Finset (Fin n)) ↦ P X.card Y.card))] :
    Counting.pairCount U V (fun X Y ↦ P X.card Y.card) =
      Counting.pairCount (Finset.univ : Finset (Fin n))
        (Finset.univ : Finset (Fin n)) (fun X Y ↦ P X.card Y.card) := by
  classical
  let eU := powersetEquivOfCardEq U hU
  let eV := powersetEquivOfCardEq V hV
  unfold Counting.pairCount
  refine Finset.card_bij'
      (fun p hp ↦ ((eU ⟨p.1,
        (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1⟩).1,
        (eV ⟨p.2,
          (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2⟩).1))
      (fun p hp ↦ ((eU.symm ⟨p.1,
        (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1⟩).1,
        (eV.symm ⟨p.2,
          (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2⟩).1))
      ?_ ?_ ?_ ?_
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpProd, hpP⟩
    rcases Finset.mem_product.mp hpProd with ⟨hpU, hpV⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨(eU ⟨p.1, hpU⟩).2,
      (eV ⟨p.2, hpV⟩).2⟩, ?_⟩
    have hcU := powersetEquivOfCardEq_card U hU ⟨p.1, hpU⟩
    have hcV := powersetEquivOfCardEq_card V hV ⟨p.2, hpV⟩
    change P p.1.card p.2.card at hpP
    change P (eU ⟨p.1, hpU⟩).1.card (eV ⟨p.2, hpV⟩).1.card
    dsimp only [eU, eV]
    simpa only [hcU, hcV] using hpP
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpProd, hpP⟩
    rcases Finset.mem_product.mp hpProd with ⟨hpU, hpV⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨(eU.symm ⟨p.1, hpU⟩).2,
      (eV.symm ⟨p.2, hpV⟩).2⟩, ?_⟩
    have hcU := powersetEquivOfCardEq_card U hU
      (eU.symm ⟨p.1, hpU⟩)
    have hcV := powersetEquivOfCardEq_card V hV
      (eV.symm ⟨p.2, hpV⟩)
    rw [eU.apply_symm_apply] at hcU
    rw [eV.apply_symm_apply] at hcV
    change P p.1.card p.2.card at hpP
    change P (eU.symm ⟨p.1, hpU⟩).1.card
      (eV.symm ⟨p.2, hpV⟩).1.card
    simpa only [hcU, hcV] using hpP
  · intro p hp
    apply Prod.ext
    · exact congrArg Subtype.val (eU.symm_apply_apply ⟨p.1,
        (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1⟩)
    · exact congrArg Subtype.val (eV.symm_apply_apply ⟨p.2,
        (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2⟩)
  · intro p hp
    apply Prod.ext
    · exact congrArg Subtype.val (eU.apply_symm_apply ⟨p.1,
        (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1⟩)
    · exact congrArg Subtype.val (eV.apply_symm_apply ⟨p.2,
        (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2⟩)

/-- The DKM complemented-difference statistic is transported from arbitrary
balanced finite blocks to the standard coordinate blocks. -/
theorem pairCount_difference_transport
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (V : Finset β) {n : ℕ}
    (hU : U.card = n) (hV : V.card = n) (a b : ℝ) :
    Counting.pairCount U V
        (fun X Y ↦ BinomialCLT.standardizedBinomialPoint (2 * n)
          (X.card + (n - Y.card)) ∈ Icc a b) =
      Counting.pairCount (Finset.univ : Finset (Fin n))
        (Finset.univ : Finset (Fin n))
        (fun X Y ↦ BinomialCLT.standardizedBinomialPoint (2 * n)
          (X.card + (n - Y.card)) ∈ Icc a b) := by
  simpa only using
    (pairCount_card_transport U V hU hV
      (fun x y ↦ BinomialCLT.standardizedBinomialPoint (2 * n)
        (x + (n - y)) ∈ Icc a b))

/-- Exact finite transport from an ambient balanced cut to the standard
two-block DKM count. -/
theorem balancedCut_difference_count_eq_standard
    {V : Type*} [Fintype V] [DecidableEq V]
    {A B : Finset V} {n : ℕ} (hcut : IsCut A B)
    (hA : A.card = n) (hB : B.card = n) (a b : ℝ) :
    (((Finset.univ : Finset V).powerset.filter fun S ↦
        BinomialCLT.standardizedBinomialPoint (2 * n)
          ((S ∩ A).card + (n - (S ∩ B).card)) ∈ Icc a b).card) =
      Counting.pairCount (Finset.univ : Finset (Fin n))
        (Finset.univ : Finset (Fin n))
        (fun X Y ↦ BinomialCLT.standardizedBinomialPoint (2 * n)
          (X.card + (n - Y.card)) ∈ Icc a b) := by
  calc
    (((Finset.univ : Finset V).powerset.filter fun S ↦
        BinomialCLT.standardizedBinomialPoint (2 * n)
          ((S ∩ A).card + (n - (S ∩ B).card)) ∈ Icc a b).card) =
        Counting.pairCount A B
          (fun X Y ↦ BinomialCLT.standardizedBinomialPoint (2 * n)
            (X.card + (n - Y.card)) ∈ Icc a b) :=
      cutPowerset_filter_card_eq_pairCount A B hcut
        (fun X Y ↦ BinomialCLT.standardizedBinomialPoint (2 * n)
          (X.card + (n - Y.card)) ∈ Icc a b)
    _ = _ := pairCount_difference_transport A B hA hB a b

end Erdos622
