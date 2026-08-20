/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.CoreAHT
import ErdosProblems.Erdos916.Blocks

/-!
# Three-terminal path separators

This file isolates the finite component-partitioning step used in the
three-terminal path theorem.  If deletion of one vertex puts three prescribed
vertices in three different connected components, those components (with all
remaining components assigned to the third part) give the `ThreeWayCut`
certificate used by the `(2,3)`-sparsity count.

The formulation deliberately uses reachability in `deleteVertex`, rather than
an informal reference to components, so it can be fed directly by a Menger or
Watkins--Mesner separation argument.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Two ambient vertices different from `x` are connected after deleting
`x`. -/
def ReachableOff (G : SimpleGraph V) (x a b : V) : Prop :=
  ∃ (ha : a ≠ x) (hb : b ≠ x),
    (deleteVertex G x).Reachable
      (⟨a, ha⟩ : {v : V // v ≠ x}) (⟨b, hb⟩ : {v : V // v ≠ x})

namespace ReachableOff

theorem refl {x a : V} (ha : a ≠ x) : ReachableOff G x a a := by
  exact ⟨ha, ha, SimpleGraph.Reachable.refl _⟩

theorem symm {x a b : V} (h : ReachableOff G x a b) :
    ReachableOff G x b a := by
  obtain ⟨ha, hb, hab⟩ := h
  exact ⟨hb, ha, hab.symm⟩

theorem trans {x a b c : V} (hab : ReachableOff G x a b)
    (hbc : ReachableOff G x b c) : ReachableOff G x a c := by
  obtain ⟨ha, hb, hab⟩ := hab
  obtain ⟨_hb, hc, hbc⟩ := hbc
  exact ⟨ha, hc, hab.trans hbc⟩

theorem of_adj_right {x a b : V} (ha : a ≠ x) (hb : b ≠ x)
    (hab : G.Adj a b) : ReachableOff G x a b := by
  exact ⟨ha, hb, (show (deleteVertex G x).Adj
    (⟨a, ha⟩ : {v : V // v ≠ x}) (⟨b, hb⟩ : {v : V // v ≠ x}) from hab).reachable⟩

end ReachableOff

/-- A cut vertex separating `a`, `b`, and `c` pairwise gives the exact
three-way cut certificate needed by `ThreeWayCut.edge_card_add_five_le`.

All components other than those of `a` and `b` are put in the third side.  In
particular the component of `c` makes that side nonempty. -/
theorem exists_threeWayCut_of_pairwise_not_reachableOff
    {x a b c : V}
    (hax : a ≠ x) (hbx : b ≠ x) (hcx : c ≠ x)
    (hab : ¬ReachableOff G x a b)
    (hac : ¬ReachableOff G x a c)
    (hbc : ¬ReachableOff G x b c) :
    ∃ T : ThreeWayCut G, a ∈ T.left ∧ b ∈ T.middle ∧ c ∈ T.right := by
  classical
  let L : Finset V := Finset.univ.filter fun v =>
    v ≠ x ∧ ReachableOff G x a v
  let M : Finset V := Finset.univ.filter fun v =>
    v ≠ x ∧ ReachableOff G x b v
  let R : Finset V := Finset.univ.filter fun v =>
    v ≠ x ∧ ¬ReachableOff G x a v ∧ ¬ReachableOff G x b v
  have hxL : x ∉ L := by simp [L]
  have hxM : x ∉ M := by simp [M]
  have hxR : x ∉ R := by simp [R]
  have hLM : Disjoint L M := by
    rw [Finset.disjoint_left]
    intro v hvL hvM
    simp only [L, M, Finset.mem_filter, Finset.mem_univ, true_and] at hvL hvM
    exact hab (hvL.2.trans hvM.2.symm)
  have hLR : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro v hvL hvR
    simp only [L, R, Finset.mem_filter, Finset.mem_univ, true_and] at hvL hvR
    exact hvR.2.1 hvL.2
  have hMR : Disjoint M R := by
    rw [Finset.disjoint_left]
    intro v hvM hvR
    simp only [M, R, Finset.mem_filter, Finset.mem_univ, true_and] at hvM hvR
    exact hvR.2.2 hvM.2
  have hcover : insert x (L ∪ M ∪ R) = Finset.univ := by
    apply Finset.eq_univ_iff_forall.2
    intro v
    by_cases hvx : v = x
    · simp [hvx]
    · by_cases hav : ReachableOff G x a v
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
          (Finset.mem_union_left _ (by simp [L, hvx, hav])))
      · by_cases hbv : ReachableOff G x b v
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
            (Finset.mem_union_right _ (by simp [M, hvx, hbv])))
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
            (by simp [R, hvx, hav, hbv]))
  have haL : a ∈ L := by
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hax, ReachableOff.refl hax⟩
  have hbM : b ∈ M := by
    simp only [M, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hbx, ReachableOff.refl hbx⟩
  have hcR : c ∈ R := by
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hcx, hac, hbc⟩
  refine ⟨{
    cut := x
    left := L
    middle := M
    right := R
    cut_not_left := hxL
    cut_not_middle := hxM
    cut_not_right := hxR
    left_disjoint_middle := hLM
    left_disjoint_right := hLR
    middle_disjoint_right := hMR
    cover := hcover
    left_nonempty := ⟨a, haL⟩
    middle_nonempty := ⟨b, hbM⟩
    right_nonempty := ⟨c, hcR⟩
    not_adj_left_middle := ?_
    not_adj_left_right := ?_
    not_adj_middle_right := ?_ }, haL, hbM, hcR⟩
  · intro u huL v hvM huv
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at huL
    simp only [M, Finset.mem_filter, Finset.mem_univ, true_and] at hvM
    exact hab (huL.2.trans ((ReachableOff.of_adj_right huL.1 hvM.1 huv).trans
      hvM.2.symm))
  · intro u huL v hvR huv
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at huL
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hvR
    exact hvR.2.1 (huL.2.trans (ReachableOff.of_adj_right huL.1 hvR.1 huv))
  · intro u huM v hvR huv
    simp only [M, Finset.mem_filter, Finset.mem_univ, true_and] at huM
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hvR
    exact hvR.2.2 (huM.2.trans (ReachableOff.of_adj_right huM.1 hvR.1 huv))

/-- The certificate-only form of
`exists_threeWayCut_of_pairwise_not_reachableOff`. -/
theorem threeWayCut_of_pairwise_not_reachableOff
    {x a b c : V}
    (hax : a ≠ x) (hbx : b ≠ x) (hcx : c ≠ x)
    (hab : ¬ReachableOff G x a b)
    (hac : ¬ReachableOff G x a c)
    (hbc : ¬ReachableOff G x b c) :
    Nonempty (ThreeWayCut G) := by
  obtain ⟨T, -⟩ := exists_threeWayCut_of_pairwise_not_reachableOff
    hax hbx hcx hab hac hbc
  exact ⟨T⟩

/-- Direct density form of the separated-three-components case. -/
theorem edge_card_add_five_le_of_pairwise_not_reachableOff
    {x a b c : V}
    (hax : a ≠ x) (hbx : b ≠ x) (hcx : c ≠ x)
    (hab : ¬ReachableOff G x a b)
    (hac : ¬ReachableOff G x a c)
    (hbc : ¬ReachableOff G x b c)
    (hsparse : Is23Sparse G) :
    G.edgeFinset.card + 5 ≤ 2 * Fintype.card V := by
  obtain ⟨T⟩ := threeWayCut_of_pairwise_not_reachableOff
    hax hbx hcx hab hac hbc
  exact T.edge_card_add_five_le hsparse

end Erdos916
