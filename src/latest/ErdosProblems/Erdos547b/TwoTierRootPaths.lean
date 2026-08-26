/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.RootTwoPathReinsert
import ErdosProblems.Erdos547b.TwoPoolAssignment
import ErdosProblems.Erdos547b.TwoTierLeafCompletion

/-! # Reinserting actual pendant two-paths with two degree tiers -/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim617RootPaths.RootTwoPathSystem

open Finset Fintype SimpleGraph

universe u v w

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} {I : Type v} [Fintype I] [DecidableEq I]
variable {B : Type w} [Fintype B] [DecidableEq B]

private theorem twoTierMiddleSet_nonempty_index
    (D : RootTwoPathSystem T I) (x : D.middleSet) :
    ∃ i : I, D.middleVertex i = x := by
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp x.2
  exact ⟨i, hi⟩

private noncomputable def twoTierMiddleIndex
    (D : RootTwoPathSystem T I) (x : D.middleSet) : I :=
  Classical.choose (D.twoTierMiddleSet_nonempty_index x)

private theorem twoTierMiddleIndex_spec
    (D : RootTwoPathSystem T I) (x : D.middleSet) :
    D.middleVertex (D.twoTierMiddleIndex x) = x :=
  Classical.choose_spec (D.twoTierMiddleSet_nonempty_index x)

omit [DecidableEq I] in
private theorem twoTierLeafSet_nonempty_index
    (D : RootTwoPathSystem T I) (x : D.leafSet) :
    ∃ i : I, D.leaf i = x.1 := by
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp x.2
  exact ⟨i, hi⟩

private noncomputable def twoTierLeafIndex
    (D : RootTwoPathSystem T I) (x : D.leafSet) : I :=
  Classical.choose (D.twoTierLeafSet_nonempty_index x)

omit [DecidableEq I] in
private theorem twoTierLeafIndex_spec
    (D : RootTwoPathSystem T I) (x : D.leafSet) :
    D.leaf (D.twoTierLeafIndex x) = x.1 :=
  Classical.choose_spec (D.twoTierLeafSet_nonempty_index x)

theorem exists_copy_of_core_twoTier
    (D : RootTwoPathSystem T I) (G : SimpleGraph B) [DecidableRel G.Adj]
    (f : D.core.Copy G) (High : Finset I) (P Q : Finset B) (hPQ : Disjoint P Q)
    (hfreeP : ∀ x, f x ∉ P) (hfreeQ : ∀ x, f x ∉ Q)
    (hhighLive : ∀ i, High.card ≤ Erdos547EC2.degreeInto G (f (D.parentCoreVertex i)) P)
    (hlowLive : ∀ i, Fintype.card I - High.card ≤ Erdos547EC2.degreeInto G (f (D.parentCoreVertex i)) Q)
    (hhighDegree : ∀ z ∈ P, Fintype.card V - 1 ≤ G.degree z)
    (hlowDegree : ∀ z ∈ Q, Fintype.card V - 1 - High.card ≤ G.degree z) :
    Nonempty (T.Copy G) := by
  classical
  obtain ⟨mid, hmidInj, hmidAdj, hmidHigh, hmidLow⟩ :=
    Erdos547b.ZhaoTwoPoolAssignment.exists_adjacent_twoPools G
      (fun i => f (D.parentCoreVertex i)) High P Q hPQ (fun i _ => hhighLive i) (fun i _ => hlowLive i)
  have hmidChoice (i : I) : mid i ∈ D.middleChoices G f (P ∪ Q) i := by
    have hpool : mid i ∈ P ∪ Q := by
      by_cases hi : i ∈ High
      · exact Finset.mem_union_left _ (hmidHigh i hi)
      · exact Finset.mem_union_right _ (hmidLow i hi)
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (hmidAdj i), hpool⟩, ?_⟩
    intro hused
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hused
    rcases Finset.mem_union.mp hpool with hP | hQ
    · exact hfreeP x (hx.symm ▸ hP)
    · exact hfreeQ x (hx.symm ▸ hQ)
  let gMiddle : D.middleSet → B := fun x ↦ mid (D.twoTierMiddleIndex x)
  have hgMiddleInj : Function.Injective gMiddle := by
    intro x y hxy
    have hidx : D.twoTierMiddleIndex x = D.twoTierMiddleIndex y := hmidInj hxy
    apply Subtype.ext
    calc
      x.1 = D.middleVertex (D.twoTierMiddleIndex x) :=
        (D.twoTierMiddleIndex_spec x).symm
      _ = D.middleVertex (D.twoTierMiddleIndex y) := by rw [hidx]
      _ = y.1 := D.twoTierMiddleIndex_spec y
  have hfg : ∀ x y, f x ≠ gMiddle y := by
    intro x y hxy
    have hnot := Finset.mem_sdiff.mp (hmidChoice (D.twoTierMiddleIndex y)) |>.2
    apply hnot
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_univ _, ?_⟩
    simpa [gMiddle] using hxy
  have hMM : ∀ x y : D.middleSet, D.pruned.Adj x y →
      G.Adj (gMiddle x) (gMiddle y) := by
    intro x y hxy
    exfalso
    have hTxy : T.Adj x.1.1 y.1.1 := hxy
    have hxMiddle : D.middle (D.twoTierMiddleIndex x) = x.1.1 :=
      congrArg Subtype.val (D.twoTierMiddleIndex_spec x)
    have hyMiddle : D.middle (D.twoTierMiddleIndex y) = y.1.1 :=
      congrArg Subtype.val (D.twoTierMiddleIndex_spec y)
    have hfromMiddle : T.Adj (D.middle (D.twoTierMiddleIndex x)) y.1.1 := by
      rw [hxMiddle]
      exact hTxy
    have hcases :=
      D.middle_neighbors (D.twoTierMiddleIndex x) y.1.1 hfromMiddle
    rcases hcases with hp | hl
    · exact D.parent_ne_middle (D.twoTierMiddleIndex x) (D.twoTierMiddleIndex y)
        (hp.symm.trans hyMiddle.symm)
    · exact D.middle_ne_leaf (D.twoTierMiddleIndex y) (D.twoTierMiddleIndex x)
        (hyMiddle.trans hl)
  have hMC : ∀ x : D.middleSet, ∀ y : ↥((D.middleSet :
      Set {x // x ∉ D.leafSet})ᶜ), D.pruned.Adj x y →
      G.Adj (gMiddle x) (f y) := by
    intro x y hxy
    let i := D.twoTierMiddleIndex x
    have hxMiddle : D.middle i = x.1.1 := by
      exact congrArg Subtype.val (D.twoTierMiddleIndex_spec x)
    have hTxy' : T.Adj x.1.1 y.1.1 := hxy
    have hTxy : T.Adj (D.middle i) y.1.1 := by
      rw [hxMiddle]
      exact hTxy'
    have hcases := D.middle_neighbors i y.1.1 hTxy
    rcases hcases with hp | hl
    · have hyParent : y = D.parentCoreVertex i := by
        apply Subtype.ext
        apply Subtype.ext
        exact hp
      have hchoice := Finset.mem_sdiff.mp (hmidChoice i) |>.1
      have hadj : G.Adj (f (D.parentCoreVertex i)) (mid i) :=
        (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hchoice).1
      simpa [gMiddle, i, hyParent] using hadj.symm
    · exact False.elim (y.1.2 (Finset.mem_image.mpr
        ⟨i, Finset.mem_univ _, hl.symm⟩))
  obtain ⟨prunedCopy, hmidMap, hcoreMap⟩ :=
    Erdos547b.ZhaoLemma710Alt.copy_of_induce_compl_and_extension
      D.pruned G D.middleSet f gMiddle hgMiddleInj hfg hMM hMC
  let leafParent : D.leafSet → V := fun x ↦ D.middle (D.twoTierLeafIndex x)
  have hleafParentNot (x : D.leafSet) : leafParent x ∉ D.leafSet :=
    D.middle_not_mem_leafSet (D.twoTierLeafIndex x)
  have hleafParentAdj (x : D.leafSet) : T.Adj (leafParent x) x.1 := by
    simpa [leafParent, D.twoTierLeafIndex_spec x] using
      D.middle_leaf_adj (D.twoTierLeafIndex x)
  have hleafUnique (x : D.leafSet) (y : V) (hxy : T.Adj x.1 y) :
      y = leafParent x := by
    simpa [leafParent, D.twoTierLeafIndex_spec x] using
      D.leaf_neighbors (D.twoTierLeafIndex x) y (by simpa [D.twoTierLeafIndex_spec x] using hxy)
  have hleafMap (x : D.leafSet) :
      prunedCopy ⟨leafParent x, hleafParentNot x⟩ = mid (D.twoTierLeafIndex x) := by
    let i := D.twoTierLeafIndex x
    have hmemMiddle : D.middleVertex i ∈ D.middleSet :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    let xm : D.middleSet := ⟨D.middleVertex i, hmemMiddle⟩
    have hmap : prunedCopy ⟨leafParent x, hleafParentNot x⟩ = mid i := by
      calc
        prunedCopy ⟨leafParent x, hleafParentNot x⟩ = gMiddle xm := by
          have harg :
              (⟨leafParent x, hleafParentNot x⟩ :
                {z // z ∉ D.leafSet}) = xm.1 := by
            apply Subtype.ext
            rfl
          rw [harg]
          exact hmidMap xm
        _ = mid i := by
          simp only [gMiddle]
          have hs := D.twoTierMiddleIndex_spec xm
          have : D.twoTierMiddleIndex xm = i := D.middle_injective (by
            exact congrArg Subtype.val hs)
          rw [this]
    exact hmap
  let HighLeaves : Finset D.leafSet := Finset.univ.filter fun x => D.twoTierLeafIndex x ∈ High
  have hHighCard : HighLeaves.card = High.card := by
    apply Finset.card_bij (fun x _ => D.twoTierLeafIndex x)
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro x _ y _ hxy
      apply Subtype.ext
      exact (D.twoTierLeafIndex_spec x).symm.trans ((congrArg D.leaf hxy).trans (D.twoTierLeafIndex_spec y))
    · intro i hi
      let x : D.leafSet := ⟨D.leaf i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
      have hidx : D.twoTierLeafIndex x = i := D.leaf_injective (D.twoTierLeafIndex_spec x)
      exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hidx.symm ▸ hi⟩, hidx⟩
  have hhighLeaf (x : D.leafSet) (hx : x ∈ HighLeaves) :
      Fintype.card V - 1 ≤ G.degree (prunedCopy ⟨leafParent x, hleafParentNot x⟩) := by
    rw [hleafMap]
    exact hhighDegree _ (hmidHigh _ (Finset.mem_filter.mp hx).2)
  have hlowLeaf (x : D.leafSet) (hx : x ∉ HighLeaves) :
      Fintype.card V - 1 - HighLeaves.card ≤ G.degree (prunedCopy ⟨leafParent x, hleafParentNot x⟩) := by
    rw [hleafMap, hHighCard]
    exact hlowDegree _ (hmidLow _ (fun h => hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
  obtain ⟨full, _, _⟩ :=
    Erdos547b.ZhaoTwoTierLeafCompletion.exists_copy_of_twoTier_leaves
      T G D.leafSet leafParent hleafParentNot hleafParentAdj
      hleafUnique prunedCopy HighLeaves hhighLeaf hlowLeaf
  exact ⟨full⟩

end Erdos547b.ZhaoClaim617RootPaths.RootTwoPathSystem

#print axioms Erdos547b.ZhaoClaim617RootPaths.RootTwoPathSystem.exists_copy_of_core_twoTier
