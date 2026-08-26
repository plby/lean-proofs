/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.RootTwoPathReinsert
import ErdosProblems.Erdos547b.ForestCapacity

/-!
# Component-rooted two-paths for Zhao Claim 6.17

These are the size-two branches below every cut-component root.  Only the
middle and leaf must avoid the recorded cut-parent set; the component root
may itself be a cut parent.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim617CutRootPaths

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim617RootPaths

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

theorem cutGraph_adj_of_not_root_not_parent
    (P : ZhaoForestPartition T globalRoot small) {x y : V}
    (hxroot : x ∉ partitionRoots P)
    (hxparent : x ∉ partitionParents P)
    (hxy : T.Adj x y) : P.cutForest.Adj x y := by
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨hxy, ?_⟩
  intro hcut
  change s(x, y) ∈ zhaoCutEdges P.roots P.parent at hcut
  rw [zhaoCutEdges] at hcut
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hcut
  rcases Sym2.eq_iff.mp hj with hj | hj
  · apply hxroot
    apply Finset.mem_image.mpr
    exact ⟨j.1, Finset.mem_univ _, hj.1⟩
  · apply hxparent
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_univ _, hj.2⟩

/-- A clean size-two descendant branch below a component root. -/
def IsCutRootTwoPathMiddle
    (P : ZhaoForestPartition T globalRoot small) (x : V) : Prop :=
  x ∉ partitionRoots P ∧
  x ∉ partitionParents P ∧
  P.cutForest.degree x = 2 ∧
  ∃ i : Fin P.numParts, ∃ y : V,
    y ∉ partitionRoots P ∧
    y ∉ partitionParents P ∧
    P.roots i ≠ y ∧
    P.cutForest.Adj (P.roots i) x ∧
    P.cutForest.Adj x y ∧
    P.cutForest.degree y = 1

instance (P : ZhaoForestPartition T globalRoot small) (x : V) :
    Decidable (IsCutRootTwoPathMiddle P x) := Classical.propDecidable _

def middles (P : ZhaoForestPartition T globalRoot small) : Finset V :=
  Finset.univ.filter (IsCutRootTwoPathMiddle P)

@[simp] theorem mem_middles
    (P : ZhaoForestPartition T globalRoot small) (x : V) :
    x ∈ middles P ↔ IsCutRootTwoPathMiddle P x := by
  simp [middles]

private theorem middle_spec (P : ZhaoForestPartition T globalRoot small)
    (x : middles P) : IsCutRootTwoPathMiddle P x :=
  (mem_middles P x).mp x.2

noncomputable def rootIndex (P : ZhaoForestPartition T globalRoot small)
    (x : middles P) : Fin P.numParts :=
  Classical.choose (middle_spec P x).2.2.2

private theorem rootIndex_spec (P : ZhaoForestPartition T globalRoot small)
    (x : middles P) : ∃ y : V,
    y ∉ partitionRoots P ∧ y ∉ partitionParents P ∧
    P.roots (rootIndex P x) ≠ y ∧
    P.cutForest.Adj (P.roots (rootIndex P x)) x.1 ∧
    P.cutForest.Adj x.1 y ∧ P.cutForest.degree y = 1 :=
  Classical.choose_spec (middle_spec P x).2.2.2

noncomputable def leaf (P : ZhaoForestPartition T globalRoot small)
    (x : middles P) : V :=
  Classical.choose (rootIndex_spec P x)

private theorem leaf_spec (P : ZhaoForestPartition T globalRoot small)
    (x : middles P) :
    leaf P x ∉ partitionRoots P ∧
    leaf P x ∉ partitionParents P ∧
    P.roots (rootIndex P x) ≠ leaf P x ∧
    P.cutForest.Adj (P.roots (rootIndex P x)) x.1 ∧
    P.cutForest.Adj x.1 (leaf P x) ∧
    P.cutForest.degree (leaf P x) = 1 :=
  Classical.choose_spec (rootIndex_spec P x)

private theorem middle_neighborFinset
    (P : ZhaoForestPartition T globalRoot small) (x : middles P) :
    P.cutForest.neighborFinset x.1 =
      {P.roots (rootIndex P x), leaf P x} := by
  have hrootLeaf : P.roots (rootIndex P x) ≠ leaf P x :=
    (leaf_spec P x).2.2.1
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact (P.cutForest.mem_neighborFinset x.1
        (P.roots (rootIndex P x))).mpr (leaf_spec P x).2.2.2.1.symm
    · exact (P.cutForest.mem_neighborFinset x.1 (leaf P x)).mpr
        (leaf_spec P x).2.2.2.2.1
  · have hcard : #{P.roots (rootIndex P x), leaf P x} = 2 := by
      simp [hrootLeaf]
    have hNcard : #(P.cutForest.neighborFinset x.1) = 2 := by
      rw [P.cutForest.card_neighborFinset_eq_degree]
      exact (middle_spec P x).2.2.1
    rw [hcard, hNcard]

private theorem leaf_neighborFinset
    (P : ZhaoForestPartition T globalRoot small) (x : middles P) :
    P.cutForest.neighborFinset (leaf P x) = {x.1} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    rw [Finset.mem_singleton] at hz
    subst z
    exact (P.cutForest.mem_neighborFinset (leaf P x) x.1).mpr
      (leaf_spec P x).2.2.2.2.1.symm
  · rw [P.cutForest.card_neighborFinset_eq_degree,
      (leaf_spec P x).2.2.2.2.2, Finset.card_singleton]

private theorem parent_ne_leaf
    (P : ZhaoForestPartition T globalRoot small) (x : middles P) :
    P.roots (rootIndex P x) ≠ leaf P x := (leaf_spec P x).2.2.1

noncomputable def pendantFamily
    (P : ZhaoForestPartition T globalRoot small) :
    PendantRootTwoPathFamily T where
  middles := middles P
  parent x := P.roots (rootIndex P x)
  leaf := leaf P
  leaf_injective := by
    intro x y hxy
    apply Subtype.ext
    have hxAdj : P.cutForest.Adj (leaf P x) x.1 :=
      (leaf_spec P x).2.2.2.2.1.symm
    have hyAdj : P.cutForest.Adj (leaf P y) y.1 :=
      (leaf_spec P y).2.2.2.2.1.symm
    rw [hxy] at hxAdj
    have hxMem :=
      (P.cutForest.mem_neighborFinset (leaf P y) x.1).mpr hxAdj
    rw [leaf_neighborFinset P y] at hxMem
    simpa using hxMem
  middle_ne_leaf := by
    intro x y hxy
    have hxdeg := (middle_spec P x).2.2.1
    have hydeg := (leaf_spec P y).2.2.2.2.2
    rw [hxy] at hxdeg
    omega
  parent_ne_middle := by
    intro x y hxy
    exact (middle_spec P y).1 (Finset.mem_image.mpr
      ⟨rootIndex P x, Finset.mem_univ _, hxy⟩)
  parent_ne_leaf := by
    intro x y hxy
    exact (leaf_spec P y).1 (Finset.mem_image.mpr
      ⟨rootIndex P x, Finset.mem_univ _, hxy⟩)
  parent_middle_adj := by
    intro x
    exact (SimpleGraph.deleteEdges_adj.mp (leaf_spec P x).2.2.2.1).1
  middle_leaf_adj := by
    intro x
    exact (SimpleGraph.deleteEdges_adj.mp (leaf_spec P x).2.2.2.2.1).1
  middle_neighbors := by
    intro x z hxz
    have hcut := cutGraph_adj_of_not_root_not_parent P
      (middle_spec P x).1 (middle_spec P x).2.1 hxz
    have hmem := (P.cutForest.mem_neighborFinset x.1 z).mpr hcut
    rw [middle_neighborFinset P x] at hmem
    simpa using hmem
  leaf_neighbors := by
    intro x z hxz
    have hcut := cutGraph_adj_of_not_root_not_parent P
      (leaf_spec P x).1 (leaf_spec P x).2.1 hxz
    have hmem := (P.cutForest.mem_neighborFinset (leaf P x) z).mpr hcut
    rw [leaf_neighborFinset P x] at hmem
    simpa using hmem

private theorem globalRoot_mem_partitionRoots
    (P : ZhaoForestPartition T globalRoot small) :
    globalRoot ∈ partitionRoots P := by
  apply Finset.mem_image.mpr
  exact ⟨⟨0, P.numParts_pos⟩, Finset.mem_univ _, P.first_root⟩

theorem select_leafDist (P : ZhaoForestPartition T globalRoot small)
    (hT : T.IsTree) {q : ℕ} (hq : q ≤ (middles P).card) (i : Fin q) :
    T.dist globalRoot (((pendantFamily P).select hq).middle i) + 1 =
      T.dist globalRoot (((pendantFamily P).select hq).leaf i) := by
  let D := (pendantFamily P).select hq
  have hrootLeaf : D.leaf i ≠ globalRoot := by
    change leaf P ((pendantFamily P).selectedIndex hq i) ≠ globalRoot
    intro h
    have hLeafRoot :
        leaf P ((pendantFamily P).selectedIndex hq i) ∈ partitionRoots P := by
      rw [h]
      exact globalRoot_mem_partitionRoots P
    exact (leaf_spec P ((pendantFamily P).selectedIndex hq i)).1 hLeafRoot
  let p := Erdos547b.TreePartition.parent hT globalRoot hrootLeaf
  have hpAdj : T.Adj (D.leaf i) p :=
    (Erdos547b.TreePartition.parent_adj hT globalRoot hrootLeaf).symm
  have hpEq : p = D.middle i := D.leaf_neighbors i p hpAdj
  simpa [p, hpEq] using
    Erdos547b.TreePartition.parent_dist_add_one hT globalRoot hrootLeaf

theorem select_parentDist (P : ZhaoForestPartition T globalRoot small)
    (hT : T.IsTree) {q : ℕ} (hq : q ≤ (middles P).card) (i : Fin q) :
    T.dist globalRoot (((pendantFamily P).select hq).parent i) + 1 =
      T.dist globalRoot (((pendantFamily P).select hq).middle i) := by
  let D := (pendantFamily P).select hq
  have hrootMiddle : D.middle i ≠ globalRoot := by
    intro h
    change (((pendantFamily P).selectedIndex hq i : middles P) : V) =
      globalRoot at h
    apply (middle_spec P ((pendantFamily P).selectedIndex hq i)).1
    apply Finset.mem_image.mpr
    exact ⟨⟨0, P.numParts_pos⟩, Finset.mem_univ _, P.first_root.trans h.symm⟩
  let p := Erdos547b.TreePartition.parent hT globalRoot hrootMiddle
  have hpAdj : T.Adj (D.middle i) p :=
    (Erdos547b.TreePartition.parent_adj hT globalRoot hrootMiddle).symm
  have hpCases := D.middle_neighbors i p hpAdj
  have hpEq : p = D.parent i := by
    rcases hpCases with h | h
    · exact h
    · have hpDist : T.dist globalRoot p + 1 =
          T.dist globalRoot (D.middle i) :=
        Erdos547b.TreePartition.parent_dist_add_one hT globalRoot hrootMiddle
      have hlDist : T.dist globalRoot (D.middle i) + 1 =
          T.dist globalRoot (D.leaf i) := by
        simpa [D] using select_leafDist P hT hq i
      have hdist : T.dist globalRoot p = T.dist globalRoot (D.leaf i) :=
        congrArg (T.dist globalRoot) h
      rw [hdist] at hpDist
      omega
  simpa [p, hpEq] using
    Erdos547b.TreePartition.parent_dist_add_one hT globalRoot hrootMiddle

noncomputable def selectedCoreRoot
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    {q : ℕ} (hq : q ≤ (middles P).card) :
    {x // x ∉ ((pendantFamily P).select hq).middleSet} :=
  ((pendantFamily P).select hq).coreRootOfOriented hT globalRoot
    (select_parentDist P hT hq) (select_leafDist P hT hq)

theorem selectedCore_isTree
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    {q : ℕ} (hq : q ≤ (middles P).card) :
    ((pendantFamily P).select hq).core.IsTree :=
  RootTwoPathSystem.core_isTree_of_oriented _ hT globalRoot
    (select_parentDist P hT hq) (select_leafDist P hT hq)

end Erdos547b.ZhaoClaim617CutRootPaths

#print axioms Erdos547b.ZhaoClaim617CutRootPaths.pendantFamily
#print axioms Erdos547b.ZhaoClaim617CutRootPaths.selectedCore_isTree
