/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.PreprocessedWitness
import ErdosProblems.Erdos186.CFP.RandomPartition
import ErdosProblems.Erdos186.CFP.LatticeQuotientCover

/-!
# Random-partition and dense-box reserve assembly

This module joins two concrete finite parts of the final CFP argument.
First, greedy selections made in distinct color classes give pairwise
disjoint reserve sets.  Second, once their subset-sum sets meet the actual
`DenseBoxLemma` hypotheses in a common one-dimensional box, the dense-box
theorem constructs every geometric field of a
`PreprocessedReserveCertificate`.
-/

namespace Erdos186.CFP

open scoped BigOperators

noncomputable section

namespace RandomPartition

/-- A color class on a finite integer set, mapped back from its subtype. -/
def integerColorClass (A : Finset ℤ) {q : ℕ}
    (c : {a // a ∈ A} → Fin (q + 1)) (i : Fin (q + 1)) : Finset ℤ :=
  (colorClass c i).map ⟨Subtype.val, Subtype.val_injective⟩

theorem integerColorClass_subset (A : Finset ℤ) {q : ℕ}
    (c : {a // a ∈ A} → Fin (q + 1)) (i : Fin (q + 1)) :
    integerColorClass A c i ⊆ A := by
  intro a ha
  obtain ⟨x, _hx, rfl⟩ := Finset.mem_map.mp ha
  exact x.2

theorem integerColorClass_disjoint (A : Finset ℤ) {q : ℕ}
    (c : {a // a ∈ A} → Fin (q + 1)) {i j : Fin (q + 1)}
    (hij : i ≠ j) :
    Disjoint (integerColorClass A c i) (integerColorClass A c j) := by
  let e : {a // a ∈ A} ↪ ℤ := ⟨Subtype.val, Subtype.val_injective⟩
  exact (Finset.disjoint_map e).mpr (colorClass_disjoint c hij)

/-- The actual reserve selected by the greedy process inside one color. -/
def greedyColorReserve (A : Finset ℤ) {q : ℕ}
    (c : {a // a ∈ A} → Fin (q + 1)) (steps : ℕ)
    (i : Fin (q + 1)) : Finset (LatticePoint 1) :=
  Stability.integerPoints
    (Greedy.selected (integerColorClass A c i) steps)

theorem greedyColorReserve_subset (A : Finset ℤ) {q steps : ℕ}
    (c : {a // a ∈ A} → Fin (q + 1)) (i : Fin (q + 1)) :
    greedyColorReserve A c steps i ⊆ Stability.integerPoints A := by
  apply Stability.integerPoints_mono
  exact (Greedy.selected_subset _ _).trans
    (integerColorClass_subset A c i)

/-- Greedy reserves selected in distinct random color classes are pairwise
disjoint. -/
theorem greedyColorReserve_pairwiseDisjoint (A : Finset ℤ) {q steps : ℕ}
    (c : {a // a ∈ A} → Fin (q + 1)) :
    (Set.univ : Set (Fin (q + 1))).PairwiseDisjoint
      (greedyColorReserve A c steps) := by
  intro i _hi j _hj hij
  change Disjoint (greedyColorReserve A c steps i)
    (greedyColorReserve A c steps j)
  rw [Finset.disjoint_left]
  intro x hxi hxj
  obtain ⟨a, hai, hax⟩ := Stability.mem_integerPoints_iff.mp hxi
  obtain ⟨b, hbj, hbx⟩ := Stability.mem_integerPoints_iff.mp hxj
  have hab : a = b := by
    have hp : Stability.integerPoint a = Stability.integerPoint b :=
      hax.trans hbx.symm
    exact Stability.integerPoint_injective hp
  subst b
  have hai' : a ∈ integerColorClass A c i :=
    Greedy.selected_subset _ _ hai
  have haj' : a ∈ integerColorClass A c j :=
    Greedy.selected_subset _ _ hbj
  exact Finset.disjoint_left.mp (integerColorClass_disjoint A c hij) hai' haj'

/-- If every color contains enough points, every greedy reserve has exactly
the requested block size. -/
theorem card_greedyColorReserve (A : Finset ℤ) {q steps : ℕ}
    (c : {a // a ∈ A} → Fin (q + 1))
    (hlarge : ∀ i, steps ≤ (integerColorClass A c i).card)
    (i : Fin (q + 1)) :
    (greedyColorReserve A c steps i).card = steps := by
  rw [greedyColorReserve, Stability.card_integerPoints,
    Greedy.card_selected_eq (hlarge i)]

theorem sum_card_greedyColorReserve (A : Finset ℤ) {q steps : ℕ}
    (c : {a // a ∈ A} → Fin (q + 1))
    (hlarge : ∀ i, steps ≤ (integerColorClass A c i).card) :
    (∑ i, (greedyColorReserve A c steps i).card) = (q + 1) * steps := by
  simp only [card_greedyColorReserve A c hlarge]
  simp

/-- Adjoining the common anchor does not increase the number of points
removed by a bounded greedy selection. -/
theorem anchoredColorClass_card_le_insert_selected_add_loss
    (A : Finset ℤ) {q steps loss : ℕ}
    (c : {a // a ∈ A} → Fin (q + 1)) (i : Fin (q + 1))
    (hsteps : steps ≤ (integerColorClass A c i).card)
    (hnear : (integerColorClass A c i).card ≤ steps + loss) :
    (anchoredColorClass A c i).card ≤
      (insert 0 (Greedy.selected (integerColorClass A c i) steps)).card +
        loss := by
  let C := integerColorClass A c i
  let S := Greedy.selected C steps
  have hSC : S ⊆ C := Greedy.selected_subset C steps
  have hScard : S.card = steps := Greedy.card_selected_eq hsteps
  have hloss : C.card - steps ≤ loss := by
    apply Nat.sub_le_iff_le_add.mpr
    simpa only [C, Nat.add_comm] using hnear
  change (insert 0 C).card ≤ (insert 0 S).card + loss
  by_cases hzeroC : 0 ∈ C
  · rw [Finset.card_insert_of_mem hzeroC]
    by_cases hzeroS : 0 ∈ S
    · rw [Finset.card_insert_of_mem hzeroS, hScard]
      omega
    · rw [Finset.card_insert_of_notMem hzeroS, hScard]
      omega
  · have hzeroS : 0 ∉ S := fun h ↦ hzeroC (hSC h)
    rw [Finset.card_insert_of_notMem hzeroC,
      Finset.card_insert_of_notMem hzeroS, hScard]
    omega

end RandomPartition

/-! ## Generated-lattice reduction -/

/-- Subset sums generate exactly the same integral lattice as their
summands.  This is the algebraic adapter needed to obtain DenseBox
reducedness from the span-preservation clause of the random partition. -/
theorem generatedSublattice_subsetSums {d : ℕ}
    (R : Finset (LatticePoint d)) :
    generatedSublattice (GAP.subsetSums R) = generatedSublattice R := by
  apply le_antisymm
  · rw [generatedSublattice, AddSubgroup.closure_le]
    intro z hz
    obtain ⟨S, hSR, rfl⟩ := GAP.mem_subsetSums_iff.mp hz
    apply AddSubgroup.sum_mem
    intro x hx
    exact AddSubgroup.subset_closure (hSR hx)
  · apply AddSubgroup.closure_mono
    intro x hx
    apply GAP.mem_subsetSums_iff.mpr
    refine ⟨{x}, ?_, by simp⟩
    simpa using hx

/-- A coordinate image generates the same lattice whether it is presented
as a finite image or through the stability API. -/
theorem generatedSublattice_image_eq_generatedSubgroup {d : ℕ}
    (φ : ℤ → LatticePoint d) (S : Finset ℤ) :
    generatedSublattice (S.image φ) =
      Stability.generatedSubgroup φ S := by
  unfold generatedSublattice Stability.generatedSubgroup
  congr 1
  ext x
  simp

/-- A finite-index coordinate subgroup can be completed to the ambient
coordinate subgroup using at most one original generator per quotient
class.  The additional generators are chosen outside the starting set.

This is the finite-quotient generator-completion step used for the sets
`Aᵢ''` in the CFP reserve construction. -/
theorem exists_bounded_generatorCompletion
    {α : Type*} [DecidableEq α] {d : ℕ}
    (φ : α → LatticePoint d) {A B : Finset α} (hBA : B ⊆ A)
    (hfinite : (Stability.generatedSubgroup φ B).relIndex
      (Stability.generatedSubgroup φ A) ≠ 0) :
    ∃ T : Finset α,
      T ⊆ A \ B ∧
      Disjoint B T ∧
      T.card ≤ (Stability.generatedSubgroup φ B).relIndex
        (Stability.generatedSubgroup φ A) ∧
      Stability.generatedSubgroup φ (B ∪ T) =
        Stability.generatedSubgroup φ A := by
  classical
  let H := Stability.generatedSubgroup φ B
  let Gamma := Stability.generatedSubgroup φ A
  have hHG : H ≤ Gamma := Stability.generatedSubgroup_mono hBA
  let J : AddSubgroup Gamma := H.addSubgroupOf Gamma
  let Q := Gamma ⧸ J
  let q : Gamma →+ Q := QuotientAddGroup.mk' J
  let U := A \ B
  let f : {a // a ∈ U} → Q := fun a ↦
    q ⟨φ a.1, Stability.image_mem_generatedSubgroup
      (show a.1 ∈ A from (Finset.mem_sdiff.mp a.2).1)⟩
  let Y : Finset Q := Finset.univ.image f
  have hpreimage (y : {y // y ∈ Y}) :
      ∃ a : {a // a ∈ U}, f a = y.1 := by
    obtain ⟨a, _ha, hfa⟩ := Finset.mem_image.mp y.2
    exact ⟨a, hfa⟩
  choose rep hrep using hpreimage
  let T : Finset α := Finset.univ.image fun y : {y // y ∈ Y} ↦ (rep y).1
  have hTU : T ⊆ U := by
    intro a ha
    obtain ⟨y, _hy, rfl⟩ := Finset.mem_image.mp ha
    exact (rep y).2
  have hdisjoint : Disjoint B T := by
    rw [Finset.disjoint_left]
    intro a haB haT
    exact (Finset.mem_sdiff.mp (hTU haT)).2 haB
  let : H.IsFiniteRelIndex Gamma := ⟨hfinite⟩
  let : Fintype Q := Fintype.ofFinite Q
  have hrelCard : H.relIndex Gamma = Fintype.card Q := by
    change Nat.card Q = Fintype.card Q
    exact Nat.card_eq_fintype_card
  have hTcard : T.card ≤ H.relIndex Gamma := by
    calc
      T.card ≤ (Finset.univ : Finset {y // y ∈ Y}).card :=
        Finset.card_image_le
      _ = Y.card := by simp
      _ ≤ Fintype.card Q := Finset.card_le_card (Finset.subset_univ Y)
      _ = H.relIndex Gamma := hrelCard.symm
  refine ⟨T, hTU, hdisjoint, hTcard, ?_⟩
  apply le_antisymm
  · exact Stability.generatedSubgroup_mono (by
      intro a ha
      rcases Finset.mem_union.mp ha with haB | haT
      · exact hBA haB
      · exact (Finset.mem_sdiff.mp (hTU haT)).1)
  · rw [Stability.generatedSubgroup, AddSubgroup.closure_le]
    intro x hx
    obtain ⟨a, haA, rfl⟩ := hx
    by_cases haB : a ∈ B
    · exact Stability.image_mem_generatedSubgroup
        (Finset.mem_union_left T haB)
    · have haU : a ∈ U := Finset.mem_sdiff.mpr ⟨haA, haB⟩
      have hfaY : f ⟨a, haU⟩ ∈ Y := by
        exact Finset.mem_image.mpr ⟨⟨a, haU⟩, Finset.mem_univ _, rfl⟩
      let y : {y // y ∈ Y} := ⟨f ⟨a, haU⟩, hfaY⟩
      have hrepT : (rep y).1 ∈ T := by
        exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩
      have hquot : q ⟨φ a, Stability.image_mem_generatedSubgroup haA⟩ =
          q ⟨φ (rep y).1, Stability.image_mem_generatedSubgroup
            ((Finset.mem_sdiff.mp (rep y).2).1)⟩ := by
        change f ⟨a, haU⟩ = f (rep y)
        exact (hrep y).symm
      have hdiffJ :
          (⟨φ a, Stability.image_mem_generatedSubgroup haA⟩ : Gamma) -
              ⟨φ (rep y).1, Stability.image_mem_generatedSubgroup
                ((Finset.mem_sdiff.mp (rep y).2).1)⟩ ∈ J := by
        exact QuotientAddGroup.eq_iff_sub_mem.mp hquot
      have hdiffH : φ a - φ (rep y).1 ∈ H := hdiffJ
      have hHK : H ≤ Stability.generatedSubgroup φ (B ∪ T) :=
        Stability.generatedSubgroup_mono (Finset.subset_union_left)
      have hrepK : φ (rep y).1 ∈
          Stability.generatedSubgroup φ (B ∪ T) :=
        Stability.image_mem_generatedSubgroup
          (Finset.mem_union_right B hrepT)
      have hdiffK : φ a - φ (rep y).1 ∈
          Stability.generatedSubgroup φ (B ∪ T) := hHK hdiffH
      have hadd := AddSubgroup.add_mem
        (Stability.generatedSubgroup φ (B ∪ T)) hdiffK hrepK
      change φ a ∈ Stability.generatedSubgroup φ (B ∪ T)
      simpa only [sub_add_cancel] using hadd

/-- A finite set containing zero and generating the whole coordinate
lattice is reduced in the sense required by DenseBox. -/
theorem reduced_of_zero_mem_generatedSublattice_eq_top {d : ℕ}
    {A : Finset (LatticePoint d)} (hzero : 0 ∈ A)
    (hgen : generatedSublattice A = ⊤) : Reduced A := by
  classical
  intro v hv H hH a
  let (i : Fin d) : NeZero (v i) := ⟨Nat.ne_of_gt (hv.1 i)⟩
  let q : LatticePoint d →+ RectangularQuotient v :=
    { toFun := rectangularResidue v
      map_zero' := rectangularResidue_zero v
      map_add' := rectangularResidue_add v }
  let Y : Finset (RectangularQuotient v) := A.image q
  have hqSurj : Function.Surjective q := by
    intro y
    refine ⟨fun i ↦ (y i).val, ?_⟩
    funext i
    simpa [q, rectangularResidue] using ZMod.natCast_zmod_val (y i)
  have hzeroY : 0 ∈ Y := by
    exact Finset.mem_image.mpr ⟨0, hzero, map_zero q⟩
  have hgenY : AddSubgroup.closure (Y : Set (RectangularQuotient v)) = ⊤ := by
    rw [show (Y : Set (RectangularQuotient v)) = q '' (A : Set (LatticePoint d)) by
      simp [Y], ← AddMonoidHom.map_closure, show AddSubgroup.closure
        (A : Set (LatticePoint d)) = ⊤ by simpa [generatedSublattice] using hgen]
    exact AddSubgroup.map_top_of_surjective q hqSurj
  have hnotCoset : NotInProperCoset
      (Y : Set (RectangularQuotient v)) :=
    notInProperCoset_of_zero_mem_closure_eq_top Y hzeroY hgenY
  by_contra hnone
  push Not at hnone
  apply hnotCoset H hH a
  intro y hyY
  obtain ⟨x, hxA, hxy⟩ := Finset.mem_image.mp hyY
  rw [← hxy]
  exact hnone x hxA

theorem reduced_subsetSums_of_generatedSublattice_eq_top {d : ℕ}
    {R : Finset (LatticePoint d)}
    (hgen : generatedSublattice R = ⊤) : Reduced (GAP.subsetSums R) := by
  apply reduced_of_zero_mem_generatedSublattice_eq_top
  · exact GAP.zero_mem_subsetSums R
  · rw [generatedSublattice_subsetSums]
    exact hgen

namespace RandomPartition

/-- The coordinate image of an actual greedy reserve. -/
noncomputable def coordinateGreedyReserve {d : ℕ} (A : Finset ℤ) {q : ℕ}
    (c : {a // a ∈ A} → Fin (q + 1)) (steps : ℕ)
    (φ : ℤ → LatticePoint d) (i : Fin (q + 1)) :
    Finset (LatticePoint d) :=
  (Greedy.selected (integerColorClass A c i) steps).image φ

/-- The source set obtained by adjoining the bounded generator completion
`Aᵢ''` to the greedy block `Aᵢ'`. -/
def completedColorSet (A : Finset ℤ) {q : ℕ}
    (c : {a // a ∈ A} → Fin (q + 1)) (steps : ℕ)
    (completion : Fin (q + 1) → Finset ℤ) (i : Fin (q + 1)) : Finset ℤ :=
  Greedy.selected (integerColorClass A c i) steps ∪ completion i

/-- The one-dimensional reserve associated to a completed source color
set. -/
def completedGreedyColorReserve (A : Finset ℤ) {q : ℕ}
    (c : {a // a ∈ A} → Fin (q + 1)) (steps : ℕ)
    (completion : Fin (q + 1) → Finset ℤ) (i : Fin (q + 1)) :
    Finset (LatticePoint 1) :=
  Stability.integerPoints (completedColorSet A c steps completion i)

/-- The coordinate image used to certify that a completed color reserve
spans the required ambient coordinate lattice. -/
noncomputable def coordinateCompletedColorReserve {d : ℕ}
    (A : Finset ℤ) {q : ℕ}
    (c : {a // a ∈ A} → Fin (q + 1)) (steps : ℕ)
    (completion : Fin (q + 1) → Finset ℤ)
    (φ : ℤ → LatticePoint d) (i : Fin (q + 1)) :
    Finset (LatticePoint d) :=
  (completedColorSet A c steps completion i).image φ

/-- Simultaneous source-correct generator completion for every color.

The additional set in color `i` is chosen from the unselected part of that
same color and costs at most the supplied relative-index bound `K`.  Hence
the completed one-dimensional reserves remain pairwise disjoint, their
total size is at most `(q + 1) * (steps + K)`, and each coordinate image
generates the prescribed ambient subgroup `Gamma`. -/
theorem exists_bounded_greedyColorGeneratorCompletionFamily
    {d q steps K : ℕ} {A : Finset ℤ}
    (c : {a // a ∈ A} → Fin (q + 1))
    (φ : ℤ → LatticePoint d) (Gamma : AddSubgroup (LatticePoint d))
    (hlarge : ∀ i, steps ≤ (integerColorClass A c i).card)
    (hfinite : ∀ i,
      (Stability.generatedSubgroup φ
          (Greedy.selected (integerColorClass A c i) steps)).relIndex
        (Stability.generatedSubgroup φ (integerColorClass A c i)) ≠ 0)
    (hindex : ∀ i,
      (Stability.generatedSubgroup φ
          (Greedy.selected (integerColorClass A c i) steps)).relIndex
        (Stability.generatedSubgroup φ (integerColorClass A c i)) ≤ K)
    (hambient : ∀ i,
      Stability.generatedSubgroup φ (integerColorClass A c i) = Gamma) :
    ∃ completion : Fin (q + 1) → Finset ℤ,
      (∀ i, completion i ⊆ integerColorClass A c i \
        Greedy.selected (integerColorClass A c i) steps) ∧
      (∀ i, Disjoint
        (Greedy.selected (integerColorClass A c i) steps) (completion i)) ∧
      (∀ i, (completion i).card ≤ K) ∧
      (∀ i, (completedGreedyColorReserve A c steps completion i).card =
        steps + (completion i).card) ∧
      (∀ i, completedGreedyColorReserve A c steps completion i ⊆
        Stability.integerPoints A) ∧
      (Set.univ : Set (Fin (q + 1))).PairwiseDisjoint
        (completedGreedyColorReserve A c steps completion) ∧
      (∑ i, (completedGreedyColorReserve A c steps completion i).card) ≤
        (q + 1) * (steps + K) ∧
      (∀ i, generatedSublattice
          (coordinateCompletedColorReserve A c steps completion φ i) =
        Gamma) := by
  classical
  have hexists : ∀ i : Fin (q + 1), ∃ T : Finset ℤ,
      T ⊆ integerColorClass A c i \
          Greedy.selected (integerColorClass A c i) steps ∧
      Disjoint (Greedy.selected (integerColorClass A c i) steps) T ∧
      T.card ≤ K ∧
      Stability.generatedSubgroup φ
          (Greedy.selected (integerColorClass A c i) steps ∪ T) = Gamma := by
    intro i
    obtain ⟨T, hTsub, hTdisjoint, hTcard, hTgen⟩ :=
      exists_bounded_generatorCompletion φ
        (Greedy.selected_subset (integerColorClass A c i) steps) (hfinite i)
    refine ⟨T, hTsub, hTdisjoint, hTcard.trans (hindex i), ?_⟩
    exact hTgen.trans (hambient i)
  choose completion hcompletion using hexists
  refine ⟨completion, fun i ↦ (hcompletion i).1,
    fun i ↦ (hcompletion i).2.1, fun i ↦ (hcompletion i).2.2.1,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [completedGreedyColorReserve, Stability.card_integerPoints,
      completedColorSet, Finset.card_union_of_disjoint
        (hcompletion i).2.1,
      Greedy.card_selected_eq (hlarge i)]
  · intro i
    apply Stability.integerPoints_mono
    intro a ha
    apply integerColorClass_subset A c i
    rcases Finset.mem_union.mp ha with haS | haT
    · exact Greedy.selected_subset _ _ haS
    · exact (Finset.mem_sdiff.mp ((hcompletion i).1 haT)).1
  · intro i _hi j _hj hij
    change Disjoint (completedGreedyColorReserve A c steps completion i)
      (completedGreedyColorReserve A c steps completion j)
    rw [Finset.disjoint_left]
    intro x hxi hxj
    obtain ⟨a, hai, hax⟩ := Stability.mem_integerPoints_iff.mp hxi
    obtain ⟨b, hbj, hbx⟩ := Stability.mem_integerPoints_iff.mp hxj
    have hab : a = b := by
      apply Stability.integerPoint_injective
      exact hax.trans hbx.symm
    subst b
    have hai' : a ∈ integerColorClass A c i := by
      rcases Finset.mem_union.mp hai with haiS | haiT
      · exact Greedy.selected_subset _ _ haiS
      · exact (Finset.mem_sdiff.mp ((hcompletion i).1 haiT)).1
    have haj' : a ∈ integerColorClass A c j := by
      rcases Finset.mem_union.mp hbj with hbjS | hbjT
      · exact Greedy.selected_subset _ _ hbjS
      · exact (Finset.mem_sdiff.mp ((hcompletion j).1 hbjT)).1
    exact Finset.disjoint_left.mp (integerColorClass_disjoint A c hij) hai' haj'
  · calc
      (∑ i, (completedGreedyColorReserve A c steps completion i).card) =
          ∑ i, (steps + (completion i).card) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [completedGreedyColorReserve, Stability.card_integerPoints,
              completedColorSet, Finset.card_union_of_disjoint
                (hcompletion i).2.1,
              Greedy.card_selected_eq (hlarge i)]
      _ ≤ ∑ _i : Fin (q + 1), (steps + K) := by
        exact Finset.sum_le_sum fun i _hi ↦
          Nat.add_le_add_left (hcompletion i).2.2.1 steps
      _ = (q + 1) * (steps + K) := by simp
  · intro i
    rw [coordinateCompletedColorReserve,
      generatedSublattice_image_eq_generatedSubgroup]
    exact (hcompletion i).2.2.2

/-- Strong span robustness supplies the full generated coordinate lattice
for a greedy reserve as soon as the selected set is within the permitted
deletion budget of its anchored color class. -/
theorem coordinateGreedyReserve_generates_of_stronglyStable
    {d deletionBudget maxRank differenceBound C0 q steps : ℕ}
    {A : Finset ℤ} {relevant : Finset ℕ}
    {box : (r : ℕ) → GAP 1 r}
    {φFamily : (r : ℕ) → ℤ → LatticePoint r}
    (c : {a // a ∈ A} → Fin (q + 1)) (i : Fin (q + 1))
    (hd : d ∈ relevant)
    (hstable : Stability.StronglyStableFor
      (anchoredColorClass A c i) box deletionBudget maxRank differenceBound
      relevant φFamily C0)
    (hsteps : steps ≤ (integerColorClass A c i).card)
    (hnear : (integerColorClass A c i).card ≤
      steps + deletionBudget / C0)
    (hφzero : φFamily d 0 = 0)
    (htop : Stability.generatedSubgroup (φFamily d)
      (anchoredColorClass A c i) = ⊤) :
    generatedSublattice
        (coordinateGreedyReserve A c steps (φFamily d) i) = ⊤ := by
  let S := Greedy.selected (integerColorClass A c i) steps
  have hSsub : insert 0 S ⊆ anchoredColorClass A c i := by
    apply Finset.insert_subset
    · simp [anchoredColorClass]
    · intro x hx
      change x ∈ insert 0 (integerColorClass A c i)
      exact Finset.mem_insert_of_mem
        (Greedy.selected_subset (integerColorClass A c i) steps hx)
  have hclose : (anchoredColorClass A c i).card ≤
      (insert 0 S).card + deletionBudget / C0 := by
    exact anchoredColorClass_card_le_insert_selected_add_loss
      A c i hsteps hnear
  have hspan := hstable.generatedSubgroup_eq hd hSsub hclose (by simp)
  have hinsert : Stability.generatedSubgroup (φFamily d) (insert 0 S) =
      Stability.generatedSubgroup (φFamily d) S := by
    unfold Stability.generatedSubgroup
    apply le_antisymm
    · rw [AddSubgroup.closure_le]
      intro x hx
      obtain ⟨a, ha, rfl⟩ := hx
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rw [hφzero]
        exact AddSubgroup.zero_mem _
      · exact AddSubgroup.subset_closure ⟨a, by exact_mod_cast ha, rfl⟩
    · apply AddSubgroup.closure_mono
      exact Set.image_mono (by exact_mod_cast Finset.subset_insert 0 S)
  rw [hinsert, htop] at hspan
  rw [coordinateGreedyReserve,
    generatedSublattice_image_eq_generatedSubgroup]
  exact hspan

end RandomPartition

/-! ## One-dimensional dense-box output -/

/-- The symmetric rank-one progression with carrier `[-radius,radius]`. -/
def symmetricIntervalProgression (radius : ℕ) : GAP 1 1 :=
  GAPBuilders.rankOne (Stability.integerPoint (-(radius : ℤ)))
    (Stability.integerPoint 1) (2 * radius)

theorem symmetricIntervalProgression_symmetric (radius : ℕ) :
    (symmetricIntervalProgression radius).Symmetric := by
  refine ⟨fun _ ↦ radius, ?_⟩
  constructor
  · funext i
    simp [symmetricIntervalProgression]
  · funext j
    simp [symmetricIntervalProgression, Stability.integerPoint]

theorem symmetricIntervalProgression_homogeneous (radius : ℕ) :
    (symmetricIntervalProgression radius).Homogeneous :=
  (symmetricIntervalProgression_symmetric radius).homogeneous

theorem symmetricIntervalProgression_proper (radius : ℕ) :
    (symmetricIntervalProgression radius).Proper := by
  apply GAPBuilders.rankOne_proper
  intro hzero
  have hcomponent := congrFun hzero (0 : Fin 1)
  norm_num [Stability.integerPoint] at hcomponent

theorem symmetricIntervalProgression_dilate_proper (radius k : ℕ) :
    ((symmetricIntervalProgression radius).dilate k).Proper := by
  apply GAPBuilders.dilate_rankOne_proper
  intro hzero
  have hcomponent := congrFun hzero (0 : Fin 1)
  norm_num [Stability.integerPoint] at hcomponent

theorem symmetricIntervalProgression_nondegenerate {radius : ℕ}
    (hradius : 0 < radius) :
    (symmetricIntervalProgression radius).Nondegenerate := by
  intro i
  simp [symmetricIntervalProgression]
  omega

theorem integerPoint_mem_symmetricIntervalProgression {radius : ℕ} {a : ℤ}
    (ha : |a| ≤ (radius : ℤ)) :
    Stability.integerPoint a ∈
      (symmetricIntervalProgression radius).carrier := by
  rw [symmetricIntervalProgression, GAPBuilders.mem_rankOne_carrier_iff]
  have habs : -(radius : ℤ) ≤ a ∧ a ≤ (radius : ℤ) := abs_le.mp ha
  refine ⟨(a + radius).toNat, ?_, ?_⟩
  · have hlo : 0 ≤ a + radius := by omega
    rw [Int.toNat_le]
    omega
  · funext j
    simp only [GAPBuilders.rankOnePoint, Stability.integerPoint_apply]
    have hlo : 0 ≤ a + radius := by omega
    rw [Int.toNat_of_nonneg hlo]
    ring

/-- A convenient division estimate used to turn the DenseBox scale
`ell / C` into a fixed positive proportion of a reserve budget. -/
theorem le_four_mul_mul_div {C ell blockSize s : ℕ}
    (hC : 0 < C) (hCell : C ≤ ell)
    (hs : s ≤ 2 * ell * blockSize) :
    s ≤ (4 * C * blockSize) * (ell / C) := by
  have hdivPos : 0 < ell / C := Nat.div_pos hCell hC
  have hdecomp : C * (ell / C) + ell % C = ell :=
    Nat.div_add_mod ell C
  have hmod : ell % C < C := Nat.mod_lt ell hC
  have hCdiv : C ≤ C * (ell / C) := by
    calc
      C = C * 1 := by simp
      _ ≤ C * (ell / C) := Nat.mul_le_mul_left C hdivPos
  have helllt : ell < C * (ell / C) + C := by omega
  have hell : ell ≤ 2 * C * (ell / C) := by
    calc
      ell ≤ C * (ell / C) + C := Nat.le_of_lt helllt
      _ ≤ C * (ell / C) + C * (ell / C) :=
        Nat.add_le_add_left hCdiv _
      _ = 2 * C * (ell / C) := by ring
  calc
    s ≤ 2 * ell * blockSize := hs
    _ ≤ 2 * (2 * C * (ell / C)) * blockSize := by gcongr
    _ = (4 * C * blockSize) * (ell / C) := by ring

/-- DenseBox constructs the entire reserve certificate in rank one.

The family supplied to DenseBox is the actual family of subset-sum sets of
the pairwise disjoint reserves.  Thus translated coverage is a theorem, not
an input.  Reducedness is derived from the displayed generated-lattice
condition; only density and span preservation remain to be supplied by the
random-partition/greedy stage. -/
theorem exists_rankOne_preprocessedReserveCertificate_of_denseSubsetSums
    (cNum cDen blockSize D : ℕ)
    (hcNum : 0 < cNum) (hc : cNum ≤ cDen)
    (hblock : 0 < blockSize) (hD : 1 ≤ D) :
    ∃ C ell₀ width₀ : ℕ, 0 < C ∧
      ∀ {stableCore : Finset ℤ} {q s radius : ℕ}
        (reserve : Fin (q + 1) → Finset (LatticePoint 1)),
        ell₀ ≤ q + 1 →
        width₀ ≤ (symmetricAxisBox (fun _ : Fin 1 ↦ radius)).minWidth →
        C ≤ q + 1 →
        0 < radius →
        (∀ a ∈ stableCore, |a| ≤ (radius : ℤ)) →
        (Set.univ : Set (Fin (q + 1))).PairwiseDisjoint reserve →
        (∀ i, reserve i ⊆ Stability.integerPoints stableCore) →
        (∀ i, (reserve i).Nonempty) →
        (∑ i, (reserve i).card) ≤ s →
        s ≤ 2 * (q + 1) * blockSize →
        (∀ i, GAP.subsetSums (reserve i) ⊆
          (symmetricAxisBox (fun _ : Fin 1 ↦ radius)).carrier) →
        (∀ i, cNum *
            (symmetricAxisBox (fun _ : Fin 1 ↦ radius)).volume ≤
          cDen * (GAP.subsetSums (reserve i)).card) →
        (∀ i, generatedSublattice (reserve i) = ⊤) →
        Nonempty
          (PreprocessedReserveCertificate stableCore s D 0 1
            (4 * C * blockSize)) := by
  obtain ⟨C, ell₀, width₀, hC, hDense⟩ :=
    denseBoxLemma 1 (by omega) cNum cDen hcNum hc
  refine ⟨C, ell₀, width₀, hC, ?_⟩
  intro stableCore q s radius reserve hell hwidth hCell hradius hcoreBound
    hdisjoint hreserveCore hreserveNonempty hreserveSmall hsUpper
    hsubset hdensity hspan
  let Q := symmetricAxisBox (fun _ : Fin 1 ↦ radius)
  let ell := q + 1
  let k := ell / C
  obtain ⟨translatePoint, hcovered⟩ :=
    hDense ell Q (fun i ↦ GAP.subsetSums (reserve i)) hell hwidth
      hsubset hdensity
      (fun i ↦ reduced_subsetSums_of_generatedSublattice_eq_top (hspan i))
  have hk : 0 < k := Nat.div_pos hCell hC
  have hscaleLower :
      1 * s ≤ (4 * C * blockSize) * k := by
    simpa only [one_mul, ell, k] using
      le_four_mul_mul_div hC hCell hsUpper
  have hellReserve : ell ≤ ∑ i, (reserve i).card := by
    dsimp only [ell]
    calc
      q + 1 = ∑ _i : Fin (q + 1), 1 := by simp
      _ ≤ ∑ i, (reserve i).card :=
        Finset.sum_le_sum (fun i _hi ↦ (hreserveNonempty i).card_pos)
  have hkell : k ≤ ell := Nat.div_le_self ell C
  have hscaleUpper : k ≤ s :=
    hkell.trans (hellReserve.trans hreserveSmall)
  let P := symmetricIntervalProgression radius
  let t : LatticePoint 1 :=
    translatePoint + Stability.integerPoint ((k * radius : ℕ) : ℤ)
  refine ⟨{
    integerCore := stableCore
    integerCore_subset := Finset.Subset.rfl
    stableCore_large := by simp
    ell := ell
    rank := 1
    k := k
    reserve := reserve
    progression := P
    translatePoint := t
    reserve_pairwiseDisjoint := hdisjoint
    rank_le := hD
    reserve_subset_core := hreserveCore
    reserve_small := hreserveSmall
    core_zero_subset := ?_
    homogeneous := symmetricIntervalProgression_homogeneous radius
    covered := ?_
    dilate_proper := symmetricIntervalProgression_dilate_proper radius k
    k_pos := hk
    scaleNum_pos := Nat.zero_lt_one
    scaleDen_pos := by positivity
    scale_lower := hscaleLower
    scale_upper := hscaleUpper
    progression_proper := symmetricIntervalProgression_proper radius
    progression_symmetric := symmetricIntervalProgression_symmetric radius
    progression_nondegenerate :=
      symmetricIntervalProgression_nondegenerate hradius
    covered_translate_homogeneous := ?_ }⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (symmetricIntervalProgression_symmetric radius).zero_mem_carrier
    · obtain ⟨a, ha, rfl⟩ := Stability.mem_integerPoints_iff.mp hx
      exact integerPoint_mem_symmetricIntervalProgression (hcoreBound a ha)
  · intro x hx
    rw [mem_translate_iff] at hx
    obtain ⟨p, hp, hpx⟩ := hx
    dsimp only [P, symmetricIntervalProgression] at hp
    rw [GAPBuilders.dilate_rankOne,
      GAPBuilders.mem_rankOne_carrier_iff] at hp
    obtain ⟨m, hm, hmp⟩ := hp
    apply hcovered
    rw [Elementary.mem_translate_iff]
    refine ⟨fun _ ↦ (m : ℤ), ?_, ?_⟩
    · rw [AxisBox.mem_carrier_iff]
      intro i
      simp only [Q, AxisBox.dilate_lower, Pi.zero_apply,
        AxisBox.dilate_width, symmetricAxisBox, zero_add]
      constructor
      · exact_mod_cast Nat.zero_le m
      · exact_mod_cast Nat.lt_succ_of_le hm
    · calc
        translatePoint + (fun _ ↦ (m : ℤ)) =
            t + GAPBuilders.rankOnePoint
              (fun j ↦ (k : ℤ) *
                Stability.integerPoint (-(radius : ℤ)) j)
              (Stability.integerPoint 1) m := by
                funext j
                simp only [t, GAPBuilders.rankOnePoint,
                  Stability.integerPoint_apply, Pi.add_apply]
                push_cast
                ring
        _ = t + p := congrArg (t + ·) hmp
        _ = x := hpx
  · refine ⟨fun _ ↦ translatePoint 0, ?_⟩
    funext j
    simp only [t, P, symmetricIntervalProgression,
      GAP.dilate_offset, Pi.add_apply, Stability.integerPoint_apply,
      GAPBuilders.rankOne_steps]
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    simp

end

#print axioms generatedSublattice_subsetSums
#print axioms exists_bounded_generatorCompletion
#print axioms RandomPartition.exists_bounded_greedyColorGeneratorCompletionFamily
#print axioms reduced_subsetSums_of_generatedSublattice_eq_top
#print axioms exists_rankOne_preprocessedReserveCertificate_of_denseSubsetSums

end Erdos186.CFP
