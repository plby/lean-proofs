/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616ResidualAllocation
import ErdosProblems.Erdos547b.Lemma614HierarchicalFullTree

/-!
# Classification of the strengthened whole-tree hierarchy

Every segment is classified by the literal Zhao cut-forest coordinate of
its segment root.  Component-root segments form a separate root class; every
other segment has a unique canonical root-deleted branch owner.  The branch
owners then split exactly into selected `F₀`, residual `F₁`, and minor `F_b`.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoClaim616HierarchyClassification

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim68BranchGraphTransport
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoLemma59SpecialSegmentation
open Erdos547b.ZhaoLemma614HierarchicalFullTree
open Erdos547b.ZhaoSingleTreeOrderedForest

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

/-- A component root, or a unique canonical root-deleted branch. -/
abbrev CanonicalSourceClass
    (P : ZhaoForestPartition T globalRoot small) :=
  Sum (Fin P.numParts) (BranchIndex P)

/-- Canonical Zhao source class of a literal tree vertex. -/
noncomputable def literalSourceClass
    (P : ZhaoForestPartition T globalRoot small) (x : V) :
    CanonicalSourceClass P := by
  classical
  if hx : x ∈ partitionRoots P then
    exact Sum.inl (P.componentIndex x)
  else
    have hxNonroot : x ∈ partitionNonroots P := by
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩
    exact Sum.inr
      (((partitionBranchEquivNonroots P).symm ⟨x, hxNonroot⟩).1)

@[simp] theorem literalSourceClass_of_root
    (P : ZhaoForestPartition T globalRoot small) (x : V)
    (hx : x ∈ partitionRoots P) :
    literalSourceClass P x = Sum.inl (P.componentIndex x) := by
  simp [literalSourceClass, hx]

@[simp] theorem componentIndex_roots
    (P : ZhaoForestPartition T globalRoot small) (i : Fin P.numParts) :
    P.componentIndex (P.roots i) = i := by
  apply P.components.injective
  change P.components
      (P.components.symm (P.cutForest.connectedComponentMk (P.roots i))) =
    P.components i
  rw [P.components.apply_symm_apply]
  apply SimpleGraph.ConnectedComponent.eq_of_common_vertex (v := P.roots i)
  · exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  · exact P.root_mem i

/-- The canonical numbering of a cut component preserves its graph
distance. -/
theorem componentEquiv_dist_eq
    (P : ZhaoForestPartition T globalRoot small) (i : Fin P.numParts)
    (a b : Fin (P.orderedForest.size i)) :
    (P.components i).toSimpleGraph.dist
        (P.componentEquiv i a) (P.componentEquiv i b) =
      (P.orderedForest.tree i).dist a b := by
  let e : P.orderedForest.tree i ≃g (P.components i).toSimpleGraph :=
    SimpleGraph.Iso.comap (P.componentEquiv i)
      (P.components i).toSimpleGraph
  exact graphIso_dist_eq_of_reachable e ((P.orderedForest.isTree i).connected a b)

theorem literalSourceClass_of_nonroot
    (P : ZhaoForestPartition T globalRoot small) (x : V)
    (hx : x ∉ partitionRoots P) :
    ∃ j : BranchIndex P, literalSourceClass P x = Sum.inr j := by
  simp only [literalSourceClass, dif_neg hx]
  exact ⟨((partitionBranchEquivNonroots P).symm
    ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩⟩).1, rfl⟩

/-- The left summands of `literalSourceClass` are genuine singletons: the
class indexed by `i` contains precisely the distinguished root of component
`i`. -/
theorem literalSourceClass_eq_inl_iff
    (P : ZhaoForestPartition T globalRoot small) (x : V)
    (i : Fin P.numParts) :
    literalSourceClass P x = Sum.inl i ↔ x = P.roots i := by
  constructor
  · intro hclass
    by_cases hx : x ∈ partitionRoots P
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
      have hjRoot : P.roots j ∈ partitionRoots P :=
        Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      rw [literalSourceClass_of_root P (P.roots j) hjRoot,
        componentIndex_roots] at hclass
      exact congrArg P.roots (Sum.inl.inj hclass)
    · obtain ⟨j, hj⟩ := literalSourceClass_of_nonroot P x hx
      rw [hj] at hclass
      cases hclass
  · rintro rfl
    have hiRoot : P.roots i ∈ partitionRoots P :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    rw [literalSourceClass_of_root P (P.roots i) hiRoot,
      componentIndex_roots]

/-- Canonical branch coordinate of a literal non-root vertex. -/
noncomputable def literalBranchCoordinate
    (P : ZhaoForestPartition T globalRoot small) (x : V)
    (hx : x ∉ partitionRoots P) :
    Σ j, Fin ((branchForest P).branches.size j) :=
  (partitionBranchEquivNonroots P).symm
    ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩⟩

@[simp] theorem partitionBranchEquivNonroots_literalBranchCoordinate
    (P : ZhaoForestPartition T globalRoot small) (x : V)
    (hx : x ∉ partitionRoots P) :
    (partitionBranchEquivNonroots P (literalBranchCoordinate P x hx)).1 = x := by
  exact congrArg Subtype.val (Equiv.apply_symm_apply
    (partitionBranchEquivNonroots P)
      ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩⟩)

@[simp] theorem literalSourceClass_partitionBranchEquivNonroots
    (P : ZhaoForestPartition T globalRoot small)
    (z : Σ j, Fin ((branchForest P).branches.size j)) :
    literalSourceClass P (partitionBranchEquivNonroots P z).1 =
      Sum.inr z.1 := by
  have hxNonroot : (partitionBranchEquivNonroots P z).1 ∈ partitionNonroots P :=
    (partitionBranchEquivNonroots P z).2
  have hxNotRoot : (partitionBranchEquivNonroots P z).1 ∉ partitionRoots P :=
    (Finset.mem_sdiff.mp hxNonroot).2
  unfold literalSourceClass
  rw [dif_neg hxNotRoot]
  have hzApply : (partitionBranchEquivNonroots P).symm
      (partitionBranchEquivNonroots P z) = z :=
    Equiv.symm_apply_apply _ z
  exact congrArg (fun w => Sum.inr w.1) hzApply

theorem literalSourceClass_eq_inr_literalBranchCoordinate
    (P : ZhaoForestPartition T globalRoot small) (x : V)
    (hx : x ∉ partitionRoots P) :
    literalSourceClass P x = Sum.inr (literalBranchCoordinate P x hx).1 := by
  unfold literalSourceClass literalBranchCoordinate
  rw [dif_neg hx]

/-- A cut-forest edge between two non-root vertices stays inside one
canonical branch class. -/
theorem literalSourceClass_eq_of_cutAdj_of_nonroots
    (P : ZhaoForestPartition T globalRoot small) {x y : V}
    (hx : x ∈ partitionNonroots P) (hy : y ∈ partitionNonroots P)
    (hxy : P.cutForest.Adj x y) :
    literalSourceClass P x = literalSourceClass P y := by
  let z := (partitionBranchEquivNonroots P).symm ⟨x, hx⟩
  let w := (partitionBranchEquivNonroots P).symm ⟨y, hy⟩
  have hzApply : partitionBranchEquivNonroots P z = ⟨x, hx⟩ :=
    Equiv.apply_symm_apply _ _
  have hwApply : partitionBranchEquivNonroots P w = ⟨y, hy⟩ :=
    Equiv.apply_symm_apply _ _
  have hxValue : x = (partitionBranchEquivNonroots P z).1 := by
    exact (congrArg Subtype.val hzApply).symm
  have hyValue : y = (partitionBranchEquivNonroots P w).1 := by
    exact (congrArg Subtype.val hwApply).symm
  have hordered := (cutForestGraphIso P).toHom.map_rel hxy
  have hbranch : (branchForest P).graph.Adj (Sum.inr z) (Sum.inr w) := by
    apply flattenBranch_reflect_adj P.orderedForest
    change P.orderedForest.graph.Adj
      (P.toOrderedForestVertex x) (P.toOrderedForestVertex y) at hordered
    rw [hxValue, hyValue, partitionBranchEquivNonroots_apply_val,
      partitionBranchEquivNonroots_apply_val,
      toOrderedForestVertex_fromOrderedForestVertex,
      toOrderedForestVertex_fromOrderedForestVertex] at hordered
    exact hordered
  have hidx := (OrderedBranchForest.graph_adj_branch_branch
    (branchForest P) z w).mp hbranch |>.choose
  rw [hxValue, hyValue,
    literalSourceClass_partitionBranchEquivNonroots,
    literalSourceClass_partitionBranchEquivNonroots, hidx]

/-- If a cut-forest edge leaves a component root, its non-root endpoint is
the canonical root of its root-deleted branch. -/
theorem branchCoordinate_eq_root_of_cutAdj_partitionRoot
    (P : ZhaoForestPartition T globalRoot small) {x y : V}
    (hx : x ∈ partitionRoots P) (hy : y ∈ partitionNonroots P)
    (hxy : P.cutForest.Adj x y) :
    let z := (partitionBranchEquivNonroots P).symm ⟨y, hy⟩
    z.2 = (branchForest P).branches.root z.1 := by
  obtain ⟨q, -, hqx⟩ := Finset.mem_image.mp hx
  subst x
  let z := (partitionBranchEquivNonroots P).symm ⟨y, hy⟩
  have hzApply : partitionBranchEquivNonroots P z = ⟨y, hy⟩ :=
    Equiv.apply_symm_apply _ _
  have hordered := (cutForestGraphIso P).toHom.map_rel hxy
  have hbranch : (branchForest P).graph.Adj (Sum.inl q) (Sum.inr z) := by
    apply flattenBranch_reflect_adj P.orderedForest
    change P.orderedForest.graph.Adj
      (P.toOrderedForestVertex (P.roots q)) (P.toOrderedForestVertex y) at hordered
    have hyValue : y = (partitionBranchEquivNonroots P z).1 := by
      exact (congrArg Subtype.val hzApply).symm
    rw [Erdos547b.ZhaoLemma614Full.toOrderedForestVertex_root,
      hyValue, partitionBranchEquivNonroots_apply_val,
      toOrderedForestVertex_fromOrderedForestVertex] at hordered
    simpa only [flattenBranch_root] using hordered
  exact (OrderedBranchForest.graph_adj_root_branch
    (branchForest P) q z).mp hbranch |>.2

/-! ## Orientation of Zhao cut edges -/

/-- In a rooted tree, every vertex strictly closer to the root than `u`
remains reachable from the root after deleting an arbitrary edge incident
with `u`.  The parent-chain proof avoids all path-list bookkeeping. -/
theorem reachable_deleteEdge_of_dist_lt
    (hT : T.IsTree) (root u v x : V)
    (hx : T.dist root x < T.dist root u) :
    (T.deleteEdges ({s(u, v)} : Set (Sym2 V))).Reachable root x := by
  induction hd : T.dist root x using Nat.strong_induction_on generalizing x with
  | h d ih =>
      by_cases hxr : x = root
      · subst x
        exact SimpleGraph.Reachable.refl root
      · let p := TreePartition.parent hT root hxr
        have hpdist := TreePartition.parent_dist_add_one hT root hxr
        have hpdist' : T.dist root p + 1 = T.dist root x := by
          simpa [p] using hpdist
        have hprec :
            (T.deleteEdges ({s(u, v)} : Set (Sym2 V))).Reachable root p := by
          apply ih (T.dist root p)
          · omega
          · omega
          · rfl
        have hpadj :
            (T.deleteEdges ({s(u, v)} : Set (Sym2 V))).Adj p x := by
          apply SimpleGraph.deleteEdges_adj.mpr
          refine ⟨TreePartition.parent_adj hT root hxr, ?_⟩
          intro hedge
          have hedge' : s(p, x) = s(u, v) := by
            simpa only [Set.mem_singleton_iff] using hedge
          rcases Sym2.eq_iff.mp hedge' with hedge' | hedge'
          · have hpu := congrArg (T.dist root) hedge'.1
            omega
          · have hxu := congrArg (T.dist root) hedge'.2
            omega
        exact hprec.trans hpadj.reachable

theorem roots_injective
    (P : ZhaoForestPartition T globalRoot small) :
    Function.Injective P.roots := by
  intro i j hij
  apply P.components.injective
  apply SimpleGraph.ConnectedComponent.eq_of_common_vertex (v := P.roots i)
  · exact P.root_mem i
  · simpa only [hij] using P.root_mem j

/-- Distinct decreasing component indices record distinct cut edges. -/
theorem cutEdge_ne_of_lt
    (P : ZhaoForestPartition T globalRoot small)
    (j k : Fin P.numParts) (hj : j.val ≠ 0) (hk : k.val ≠ 0)
    (hkj : k.val < j.val) :
    s(P.roots k, P.parent k hk) ≠ s(P.roots j, P.parent j hj) := by
  intro hedge
  rcases Sym2.eq_iff.mp hedge with hedge | hedge
  · have hkjEq : k = j := roots_injective P hedge.1
    subst k
    exact Nat.lt_irrefl j.val hkj
  · have hkPart : k = P.parentPart j hj := by
      apply P.components.injective
      apply SimpleGraph.ConnectedComponent.eq_of_common_vertex
        (v := P.roots k)
      · exact P.root_mem k
      · simpa only [hedge.1] using P.parent_mem j hj
    have hjPart : j = P.parentPart k hk := by
      apply P.components.injective
      apply SimpleGraph.ConnectedComponent.eq_of_common_vertex
        (v := P.roots j)
      · exact P.root_mem j
      · simpa only [hedge.2] using P.parent_mem k hk
    have hltK := P.parent_earlier k hk
    rw [← hjPart] at hltK
    omega

/-- Every vertex of an earlier component remains connected to the global
root when only the later cut edge `j` is deleted. -/
theorem reachable_earlierComponent_delete_cutEdge
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (j : Fin P.numParts) (hj : j.val ≠ 0)
    (k : Fin P.numParts) (hkj : k.val < j.val)
    (x : V) (hx : x ∈ (P.components k).supp) :
    (T.deleteEdges
      ({s(P.roots j, P.parent j hj)} : Set (Sym2 V))).Reachable
        globalRoot x := by
  let D := T.deleteEdges
    ({s(P.roots j, P.parent j hj)} : Set (Sym2 V))
  have hcutLe : P.cutForest ≤ D := by
    intro a b hab
    have hab' := SimpleGraph.deleteEdges_adj.mp hab
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨hab'.1, ?_⟩
    intro he
    have heq : s(a, b) = s(P.roots j, P.parent j hj) := by
      simpa only [Set.mem_singleton_iff] using he
    apply hab'.2
    rw [heq]
    change s(P.roots j, P.parent j hj) ∈
      (↑(zhaoCutEdges P.roots P.parent) : Set (Sym2 V))
    simp only [Set.mem_setOf_eq, Finset.mem_coe]
    rw [zhaoCutEdges, Finset.mem_image]
    exact ⟨⟨j, hj⟩, Finset.mem_univ _, rfl⟩
  induction hkval : k.val using Nat.strong_induction_on generalizing k x with
  | h d ih =>
      have hcomponent : P.cutForest.Reachable (P.roots k) x :=
        (P.components k).reachable_of_mem_supp (P.root_mem k) hx
      have hcomponentD : D.Reachable (P.roots k) x :=
        hcomponent.mono hcutLe
      by_cases hk0 : k.val = 0
      · have hk : k = ⟨0, P.numParts_pos⟩ := Fin.ext hk0
        subst k
        rw [P.first_root] at hcomponentD
        exact hcomponentD
      · let p := P.parentPart k hk0
        have hpk : p.val < k.val := P.parent_earlier k hk0
        have hpj : p.val < j.val := hpk.trans hkj
        have hparentReach : D.Reachable globalRoot (P.parent k hk0) := by
          exact ih p.val (by omega) p hpj (P.parent k hk0)
            (P.parent_mem k hk0) rfl
        have hkEdge :
            s(P.roots k, P.parent k hk0) ≠
              s(P.roots j, P.parent j hj) :=
          cutEdge_ne_of_lt P j k hj hk0 hkj
        have hrootAdj : D.Adj (P.parent k hk0) (P.roots k) := by
          apply SimpleGraph.deleteEdges_adj.mpr
          refine ⟨(P.cut_adj k hk0).symm, ?_⟩
          intro he
          have heq : s(P.parent k hk0, P.roots k) =
              s(P.roots j, P.parent j hj) := by
            simpa only [Set.mem_singleton_iff] using he
          apply hkEdge
          simpa only [Sym2.eq_swap] using heq
        exact (hparentReach.trans hrootAdj.reachable).trans hcomponentD

/-- The recorded Zhao parent is the actual neighbor one level closer to the
global root.  This is derived from the partition fields; it is not an extra
orientation assumption. -/
theorem cutParent_dist_add_one
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (j : Fin P.numParts) (hj : j.val ≠ 0) :
    T.dist globalRoot (P.parent j hj) + 1 =
      T.dist globalRoot (P.roots j) := by
  have hrootNe : P.roots j ≠ globalRoot := by
    intro hroot
    have hj0 : j = ⟨0, P.numParts_pos⟩ := by
      apply roots_injective P
      simpa only [P.first_root] using hroot
    exact hj (by simpa [hj0])
  rcases hT.dist_eq_dist_add_one_of_adj globalRoot (P.cut_adj j hj) with
      hgood | hbad
  · exact hgood.symm
  · have hrootLt : T.dist globalRoot (P.roots j) <
        T.dist globalRoot (P.parent j hj) := by omega
    have hrootReach := reachable_deleteEdge_of_dist_lt hT globalRoot
      (P.parent j hj) (P.roots j) (P.roots j) hrootLt
    have hedgeSwap : s(P.parent j hj, P.roots j) =
        s(P.roots j, P.parent j hj) := Sym2.eq_swap
    rw [hedgeSwap] at hrootReach
    let k := P.parentPart j hj
    have hparentReach := reachable_earlierComponent_delete_cutEdge hT P j hj
      k (P.parent_earlier j hj) (P.parent j hj) (P.parent_mem j hj)
    have hendpoints :
        (T.deleteEdges
          ({s(P.roots j, P.parent j hj)} : Set (Sym2 V))).Reachable
            (P.roots j) (P.parent j hj) :=
      hrootReach.symm.trans hparentReach
    have hbridge : T.IsBridge s(P.roots j, P.parent j hj) :=
      (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic)
        (P.cut_adj j hj)
    exact False.elim ((SimpleGraph.isBridge_iff.mp hbridge) hendpoints)

theorem cutRoot_ne_globalRoot
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (j : Fin P.numParts) (hj : j.val ≠ 0) :
    P.roots j ≠ globalRoot := by
  intro hroot
  have hdist := cutParent_dist_add_one hT P j hj
  rw [hroot] at hdist
  simp at hdist

theorem cutParent_eq_treeParent
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (j : Fin P.numParts) (hj : j.val ≠ 0) :
    P.parent j hj = TreePartition.parent hT globalRoot
      (cutRoot_ne_globalRoot hT P j hj) := by
  apply TreePartition.eq_parent_of_adj_of_dist_add_one hT globalRoot
  · exact (P.cut_adj j hj).symm
  · exact cutParent_dist_add_one hT P j hj

/-- A non-partition-root child keeps its actual parent edge in the Zhao cut
forest.  Every deleted edge is oriented toward a partition root by
`cutParent_dist_add_one`, so it cannot end at such a child. -/
theorem cutForest_adj_treeParent_of_nonroot
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (x : V) (hxGlobal : x ≠ globalRoot)
    (hxNonroot : x ∉ partitionRoots P) :
    P.cutForest.Adj
      (TreePartition.parent hT globalRoot hxGlobal) x := by
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨TreePartition.parent_adj hT globalRoot hxGlobal, ?_⟩
  intro hcut
  change s(TreePartition.parent hT globalRoot hxGlobal, x) ∈
    zhaoCutEdges P.roots P.parent at hcut
  rw [zhaoCutEdges, Finset.mem_image] at hcut
  obtain ⟨q, -, hq⟩ := hcut
  have htree := TreePartition.parent_dist_add_one hT globalRoot hxGlobal
  have hrecorded := cutParent_dist_add_one hT P q.1 q.2
  rcases Sym2.eq_iff.mp hq with hq | hq
  · have hrootDist := congrArg (T.dist globalRoot) hq.1
    have hparentDist := congrArg (T.dist globalRoot) hq.2
    omega
  · apply hxNonroot
    apply Finset.mem_image.mpr
    exact ⟨q.1, Finset.mem_univ _, hq.1⟩

theorem actualBranchRoot_mem_zhaoMarkedVertices
    (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (j : BranchIndex P) :
    actualBranchRoot P j ∈ zhaoMarkedVertices P optional := by
  apply Finset.mem_union_left optional
  apply Finset.mem_union_right (Finset.univ.image P.roots)
  apply Finset.mem_image.mpr
  refine ⟨j, Finset.mem_univ _, ?_⟩
  rw [actualBranchRoot_eq_partitionBranchEquiv,
    partitionBranchEquivNonroots_apply_val]
  rfl

/-- Along an actual parent--child edge, the canonical Zhao source class can
change only at a vertex in the strengthened mark set: either a partition
root or the canonical root of a root-deleted component branch. -/
theorem literalSourceClass_change_at_markedVertex
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (x : V) (hxGlobal : x ≠ globalRoot)
    (hchange : literalSourceClass P
          (TreePartition.parent hT globalRoot hxGlobal) ≠
        literalSourceClass P x) :
    x ∈ zhaoMarkedVertices P optional := by
  classical
  by_cases hxRoot : x ∈ partitionRoots P
  · apply Finset.mem_union_left optional
    exact Finset.mem_union_left _ hxRoot
  · have hxNonroot : x ∈ partitionNonroots P :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxRoot⟩
    let p := TreePartition.parent hT globalRoot hxGlobal
    have hcut : P.cutForest.Adj p x :=
      cutForest_adj_treeParent_of_nonroot hT P x hxGlobal hxRoot
    by_cases hpRoot : p ∈ partitionRoots P
    · let z := (partitionBranchEquivNonroots P).symm ⟨x, hxNonroot⟩
      have hzApply : partitionBranchEquivNonroots P z = ⟨x, hxNonroot⟩ :=
        Equiv.apply_symm_apply _ _
      have hzRoot : z.2 = (branchForest P).branches.root z.1 :=
        branchCoordinate_eq_root_of_cutAdj_partitionRoot P hpRoot hxNonroot hcut
      have hxActual : x = actualBranchRoot P z.1 := by
        rw [actualBranchRoot_eq_partitionBranchEquiv, ← hzRoot]
        exact (congrArg Subtype.val hzApply).symm
      rw [hxActual]
      exact actualBranchRoot_mem_zhaoMarkedVertices P optional z.1
    · have hpNonroot : p ∈ partitionNonroots P :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpRoot⟩
      exact False.elim (hchange
        (literalSourceClass_eq_of_cutAdj_of_nonroots P hpNonroot hxNonroot hcut))

/-! ## Whole-tree branch labels -/

/-- Literal tree vertex represented by a coordinate in the canonical
root-deleted branch decomposition of the one-root reindexing of `T`. -/
noncomputable def wholeBranchLiteralVertex
    (hT : T.IsTree)
    (j : Fin (Fintype.card (ChildKey (wholeOrderedTree T hT globalRoot))))
    (a : Fin ((wholeBranchForest T hT globalRoot).branches.size j)) : V :=
  fromSingleCoordinate T hT globalRoot
    (branchGraphIso (wholeOrderedTree T hT globalRoot)
      (Sum.inr (⟨j, a⟩ : BranchVertex
        (wholeBranchForest T hT globalRoot))))

/-- The canonical Zhao component/branch class, read on a coordinate of the
one-root whole-tree branch forest. -/
noncomputable def wholeBranchSourceClass
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (j : Fin (Fintype.card (ChildKey (wholeOrderedTree T hT globalRoot))))
    (a : Fin ((wholeBranchForest T hT globalRoot).branches.size j)) :
    CanonicalSourceClass P :=
  literalSourceClass P (wholeBranchLiteralVertex hT j a)

/-! The following allocation aliases are declared before the coordinate
lemmas that use them.  Keeping these names here also makes the later
nonmixing statements independent of definitional spellings of the mark
set. -/

abbrev AllocationSpecial
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) :=
  zhaoSpecialCoordinates hT P optional

abbrev AllocationHierarchy
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) :=
  wholeHierarchy T hT globalRoot (AllocationSpecial hT P optional)

abbrev SegmentIndex
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) :=
  Fin #(marks (wholeBranchForest T hT globalRoot)
    (AllocationSpecial hT P optional))

theorem fromSingleCoordinate_injective
    (hT : T.IsTree) : Function.Injective
      (fromSingleCoordinate T hT globalRoot) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ hab
  have hij : i = j := Subsingleton.elim _ _
  subst j
  refine Sigma.ext rfl ?_
  exact heq_of_eq ((vertexEquiv (V := V)).injective hab)

@[simp] theorem toSingle_fromSingleCoordinate
    (hT : T.IsTree)
    (z : Σ i, Fin ((wholeOrderedTree T hT globalRoot).size i)) :
    toSingleCoordinate T hT globalRoot
      (fromSingleCoordinate T hT globalRoot z) = z := by
  rcases z with ⟨i, a⟩
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  refine Sigma.ext rfl ?_
  exact heq_of_eq ((vertexEquiv (V := V)).symm_apply_apply a)

@[simp] theorem toWholeBranchForestVertex_wholeBranchLiteralVertex
    (hT : T.IsTree)
    (j : Fin (Fintype.card (ChildKey (wholeOrderedTree T hT globalRoot))))
    (a : Fin ((wholeBranchForest T hT globalRoot).branches.size j)) :
    toWholeBranchForestVertex T hT globalRoot
        (wholeBranchLiteralVertex hT j a) =
      Sum.inr (⟨j, a⟩ : BranchVertex
        (wholeBranchForest T hT globalRoot)) := by
  unfold toWholeBranchForestVertex wholeBranchLiteralVertex
  rw [toSingle_fromSingleCoordinate]
  exact (branchGraphIso (wholeOrderedTree T hT globalRoot)).symm_apply_apply _

@[simp] theorem wholeBranchLiteralVertex_eq_wholeBranchOriginal
    (hT : T.IsTree)
    (j : Fin (Fintype.card (ChildKey (wholeOrderedTree T hT globalRoot))))
    (a : Fin ((wholeBranchForest T hT globalRoot).branches.size j)) :
    wholeBranchLiteralVertex hT j a =
      wholeBranchOriginalVertex T hT globalRoot (Sum.inr ⟨j, a⟩) := by
  rfl

theorem wholeBranchLiteralVertex_ne_globalRoot
    (hT : T.IsTree)
    (j : Fin (Fintype.card (ChildKey (wholeOrderedTree T hT globalRoot))))
    (a : Fin ((wholeBranchForest T hT globalRoot).branches.size j)) :
    wholeBranchLiteralVertex hT j a ≠ globalRoot := by
  intro hroot
  have hcoord := congrArg
    (toWholeBranchForestVertex T hT globalRoot) hroot
  rw [toWholeBranchForestVertex_wholeBranchLiteralVertex,
    toWholeBranchForestVertex_root] at hcoord
  cases hcoord

theorem wholeBranchCoordinate_mem_marks_of_literal_marked
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (j : Fin (Fintype.card (ChildKey (wholeOrderedTree T hT globalRoot))))
    (a : Fin ((wholeBranchForest T hT globalRoot).branches.size j))
    (hmarked : wholeBranchLiteralVertex hT j a ∈
      zhaoMarkedVertices P optional) :
    (⟨j, a⟩ : BranchVertex (wholeBranchForest T hT globalRoot)) ∈
      marks (wholeBranchForest T hT globalRoot)
        (AllocationSpecial hT P optional) := by
  apply special_subset_marks
  apply (mem_branchSpecial _ _ _).2
  apply Finset.mem_image.mpr
  exact ⟨wholeBranchLiteralVertex hT j a, hmarked,
    toWholeBranchForestVertex_wholeBranchLiteralVertex hT j a⟩

theorem wholeHierarchyOriginalVertex_injective
    (hT : T.IsTree)
    (special : Finset (WholeBranchVertex T hT globalRoot)) :
    Function.Injective
      (wholeHierarchyOriginalVertex T hT globalRoot special) := by
  intro x y hxy
  apply flatten_injective (wholeBranchForest T hT globalRoot) special
  apply (branchGraphIso (wholeOrderedTree T hT globalRoot)).injective
  exact fromSingleCoordinate_injective hT hxy

/-- Literal source class inherited by a whole-hierarchy segment. -/
noncomputable def segmentSourceClass
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (i : SegmentIndex hT P optional) :
    CanonicalSourceClass P :=
  literalSourceClass P
    (wholeHierarchyOriginalVertex T hT globalRoot
      (AllocationSpecial hT P optional)
      ((AllocationHierarchy hT P optional).segmentRoot i))

theorem actualBranchRoot_eq_zhaoBranchRoot
    (P : ZhaoForestPartition T globalRoot small) (j : BranchIndex P) :
    actualBranchRoot P j =
      P.fromOrderedForestVertex
        ((branchVertexEquiv P.orderedForest j
          ((branchForest P).branches.root j)).1) := by
  rw [actualBranchRoot_eq_partitionBranchEquiv,
    partitionBranchEquivNonroots_apply_val]
  rfl

theorem zhaoBranchRootVertices_eq_actualBranchRoots
    (P : ZhaoForestPartition T globalRoot small) :
    zhaoBranchRootVertices P = Finset.univ.image (actualBranchRoot P) := by
  apply Finset.image_congr
  intro j _
  exact (actualBranchRoot_eq_zhaoBranchRoot P j).symm

/-- The source-only spelling of the strengthened marks and the literal
whole-tree spelling used by the hierarchy are exactly the same vertex set. -/
theorem zhaoMarkedVertices_eq_allocationMarkedVertices
    (P : ZhaoForestPartition T globalRoot small) (optional : Finset V) :
    zhaoMarkedVertices P optional = allocationMarkedVertices P optional := by
  rw [zhaoMarkedVertices, allocationMarkedVertices, partitionRoots,
    zhaoBranchRootVertices_eq_actualBranchRoots]
  exact Finset.union_assoc _ _ _

/-- Explicit cost of all hierarchy cuts.  The only noncanonical summand is
the caller's optional-special set. -/
theorem card_AllocationSpecial_le
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) :
    #(AllocationSpecial hT P optional) ≤
      P.numParts + Fintype.card (BranchIndex P) + #optional := by
  calc
    #(AllocationSpecial hT P optional) ≤
        #((zhaoMarkedVertices P optional).image
          (toWholeBranchForestVertex T hT globalRoot)) := by
      exact card_branchSpecial_le
        (wholeBranchForest T hT globalRoot)
        ((zhaoMarkedVertices P optional).image
          (toWholeBranchForestVertex T hT globalRoot))
    _ ≤ #(zhaoMarkedVertices P optional) := Finset.card_image_le
    _ = #(allocationMarkedVertices P optional) := by
      rw [zhaoMarkedVertices_eq_allocationMarkedVertices]
    _ ≤ P.numParts + Fintype.card (BranchIndex P) + #optional :=
      card_allocationMarkedVertices_le P optional

/-- The genuinely optional part of the mark set, separated from canonical
component and branch roots. -/
def OptionalSpecialCoordinates
    (hT : T.IsTree) (optional : Finset V) :
    Finset (WholeBranchVertex T hT globalRoot) :=
  wholeSpecialCoordinates T hT globalRoot optional

theorem card_OptionalSpecialCoordinates_le
    (hT : T.IsTree) (optional : Finset V) :
    #(OptionalSpecialCoordinates (globalRoot := globalRoot) hT optional) ≤ #optional := by
  calc
    #(OptionalSpecialCoordinates (globalRoot := globalRoot) hT optional) ≤
        #(optional.image (toWholeBranchForestVertex T hT globalRoot)) := by
      exact card_branchSpecial_le
        (wholeBranchForest T hT globalRoot)
        (optional.image (toWholeBranchForestVertex T hT globalRoot))
    _ ≤ #optional := Finset.card_image_le

theorem card_OptionalSpecialCoordinates_le_small
    (hT : T.IsTree) (optional : Finset V)
    (hoptional : #optional ≤ small) :
    #(OptionalSpecialCoordinates (globalRoot := globalRoot) hT optional) ≤ small :=
  (card_OptionalSpecialCoordinates_le (globalRoot := globalRoot) hT optional).trans hoptional

theorem OptionalSpecialCoordinates_subset_AllocationSpecial
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) :
    OptionalSpecialCoordinates (globalRoot := globalRoot) hT optional ⊆
      AllocationSpecial hT P optional := by
  intro z hz
  apply (mem_branchSpecial _ _ z).2
  have hz' := (mem_branchSpecial _ _ z).1 hz
  rw [zhaoMarkedVertices_eq_allocationMarkedVertices P optional]
  exact Finset.mem_of_subset
    (Finset.image_mono _ (optional_subset_allocationMarkedVertices P optional)) hz'

theorem actualBranchRoot_ne_globalRoot
    (P : ZhaoForestPartition T globalRoot small) (j : BranchIndex P) :
    actualBranchRoot P j ≠ globalRoot := by
  have hnonroot : actualBranchRoot P j ∈ partitionNonroots P := by
    simpa only [actualBranchRoot_eq_partitionBranchEquiv] using
      (partitionBranchEquivNonroots P
        (⟨j, (branchForest P).branches.root j⟩ :
          Σ q, Fin ((branchForest P).branches.size q))).2
  have hglobal : globalRoot ∈ partitionRoots P := by
    apply Finset.mem_image.mpr
    exact ⟨⟨0, P.numParts_pos⟩, Finset.mem_univ _, P.first_root⟩
  intro heq
  apply (Finset.mem_sdiff.mp hnonroot).2
  rw [heq]
  exact hglobal

/-- Every canonical Zhao root-deleted branch contributes its marked root as
the root of a unique hierarchy segment, and that segment has the same
canonical branch class. -/
theorem exists_segmentRoot_of_canonicalBranch
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (j : BranchIndex P) :
    ∃ i : SegmentIndex hT P optional,
      toWholeHierarchyVertex T hT globalRoot
          (AllocationSpecial hT P optional) (actualBranchRoot P j) =
        (AllocationHierarchy hT P optional).segmentRoot i ∧
      segmentSourceClass hT P optional i = Sum.inr j := by
  classical
  let F := wholeBranchForest T hT globalRoot
  let rawSpecial := (zhaoMarkedVertices P optional).image
    (toWholeBranchForestVertex T hT globalRoot)
  have hxImage : toWholeBranchForestVertex T hT globalRoot
      (actualBranchRoot P j) ∈ rawSpecial :=
    Finset.mem_image.mpr
      ⟨actualBranchRoot P j, actualBranchRoot_mem_zhaoMarkedVertices P optional j,
        rfl⟩
  cases hcoord : toWholeBranchForestVertex T hT globalRoot
      (actualBranchRoot P j) with
  | inl q =>
      have hq : q = 0 := Subsingleton.elim _ _
      have hbad : actualBranchRoot P j = globalRoot := by
        apply toWholeBranchForestVertex_injective T hT globalRoot
        rw [hcoord, hq, toWholeBranchForestVertex_root]
      exact False.elim (actualBranchRoot_ne_globalRoot P j hbad)
  | inr z =>
      have hz : (Sum.inr z : F.Vertex) ∈ rawSpecial := by
        rw [hcoord] at hxImage
        exact hxImage
      obtain ⟨i, hi⟩ := unflatten_branchSpecial_is_segmentRoot
        F rawSpecial z hz
      have hi' : toWholeHierarchyVertex T hT globalRoot
            (AllocationSpecial hT P optional) (actualBranchRoot P j) =
          (AllocationHierarchy hT P optional).segmentRoot i := by
        change unflatten F (branchSpecial F rawSpecial)
            (toWholeBranchForestVertex T hT globalRoot
              (actualBranchRoot P j)) = _
        rw [hcoord]
        exact hi
      refine ⟨i, hi', ?_⟩
      have hliteral := congrArg
        (wholeHierarchyOriginalVertex T hT globalRoot
          (AllocationSpecial hT P optional)) hi'
      rw [wholeHierarchyOriginal_toWholeHierarchyVertex] at hliteral
      have hclass : literalSourceClass P (actualBranchRoot P j) = Sum.inr j := by
        rw [actualBranchRoot_eq_partitionBranchEquiv,
          literalSourceClass_partitionBranchEquivNonroots]
      change literalSourceClass P
          (wholeHierarchyOriginalVertex T hT globalRoot
            (AllocationSpecial hT P optional)
            ((AllocationHierarchy hT P optional).segmentRoot i)) = Sum.inr j
      rw [← hliteral]
      exact hclass

abbrev WholeSourceBoundary
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) : Prop :=
  ∀ j a
    (haRoot : a ≠ (wholeBranchForest T hT globalRoot).branches.root j),
    wholeBranchSourceClass hT P j
        (TreePartition.parent
          ((wholeBranchForest T hT globalRoot).branches.isTree j)
          ((wholeBranchForest T hT globalRoot).branches.root j) haRoot) ≠
      wholeBranchSourceClass hT P j a →
    (⟨j, a⟩ : BranchVertex (wholeBranchForest T hT globalRoot)) ∈
      marks (wholeBranchForest T hT globalRoot)
        (AllocationSpecial hT P optional)

abbrev WholeBranchParentTransport (hT : T.IsTree) : Prop :=
  ∀ j a
    (haRoot : a ≠ (wholeBranchForest T hT globalRoot).branches.root j),
    wholeBranchLiteralVertex hT j
        (TreePartition.parent
          ((wholeBranchForest T hT globalRoot).branches.isTree j)
          ((wholeBranchForest T hT globalRoot).branches.root j) haRoot) =
      TreePartition.parent hT globalRoot
        (wholeBranchLiteralVertex_ne_globalRoot hT j a)

/-- The canonical one-root branch decomposition has the required literal
parent transport; no source or host premise is needed. -/
theorem canonicalWholeBranchParentTransport (hT : T.IsTree) :
    WholeBranchParentTransport (globalRoot := globalRoot) hT := by
  intro j a haRoot
  rw [wholeBranchLiteralVertex_eq_wholeBranchOriginal]
  change wholeBranchOriginalVertex T hT globalRoot
      (Sum.inr ⟨j, TreePartition.parent
        ((wholeBranchForest T hT globalRoot).branches.isTree j)
        ((wholeBranchForest T hT globalRoot).branches.root j) haRoot⟩) =
    TreePartition.parent hT globalRoot _
  exact wholeBranch_localParent_original T hT globalRoot j a haRoot

theorem wholeSourceBoundary_of_parentTransport
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (hparent : WholeBranchParentTransport (globalRoot := globalRoot) hT) :
    WholeSourceBoundary hT P optional := by
  intro j a haRoot hchange
  have hchange' : literalSourceClass P
        (TreePartition.parent hT globalRoot
          (wholeBranchLiteralVertex_ne_globalRoot hT j a)) ≠
      literalSourceClass P (wholeBranchLiteralVertex hT j a) := by
    simpa only [wholeBranchSourceClass, hparent j a haRoot] using hchange
  exact wholeBranchCoordinate_mem_marks_of_literal_marked hT P optional j a
    (literalSourceClass_change_at_markedVertex hT P optional
      (wholeBranchLiteralVertex hT j a)
      (wholeBranchLiteralVertex_ne_globalRoot hT j a) hchange')

/-- Concrete strengthened Zhao boundary invariant. -/
theorem canonicalWholeSourceBoundary
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) : WholeSourceBoundary hT P optional :=
  wholeSourceBoundary_of_parentTransport hT P optional
    (canonicalWholeBranchParentTransport (globalRoot := globalRoot) hT)

/-- Abstract nonmixing form: once every parent--child change of the literal
Zhao source class is marked, every coordinate of a hierarchy segment has
the class of that segment's marked root.  The concrete boundary theorem is
proved below from the enlarged Zhao mark set. -/
theorem wholeSegment_sourceClass_eq_of_boundary
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (hboundary : WholeSourceBoundary hT P optional)
    (i : SegmentIndex hT P optional)
    (a : Fin ((AllocationHierarchy hT P optional).segments.size i)) :
    literalSourceClass P
        (wholeHierarchyOriginalVertex T hT globalRoot
          (AllocationSpecial hT P optional) (Sum.inr ⟨i, a⟩)) =
      segmentSourceClass hT P optional i := by
  let F := wholeBranchForest T hT globalRoot
  let q : BranchVertex F := (markEnum F (AllocationSpecial hT P optional) i).1
  have hlabel := label_eq_mark_of_mem_fiber F (AllocationSpecial hT P optional)
    (wholeBranchSourceClass hT P) hboundary q
    (fiberEquiv F (AllocationSpecial hT P optional) i a).1
    (fiberEquiv F (AllocationSpecial hT P optional) i a).2
  have hpoint :
      wholeHierarchyOriginalVertex T hT globalRoot
          (AllocationSpecial hT P optional) (Sum.inr ⟨i, a⟩) =
        wholeBranchLiteralVertex hT q.1
          (fiberEquiv F (AllocationSpecial hT P optional) i a).1 := by
    rfl
  have hroot :
      wholeHierarchyOriginalVertex T hT globalRoot
          (AllocationSpecial hT P optional)
          ((AllocationHierarchy hT P optional).segmentRoot i) =
        wholeBranchLiteralVertex hT q.1 q.2 := by
    unfold wholeHierarchyOriginalVertex
    rw [flatten_segmentRoot]
    rfl
  change literalSourceClass P
      (wholeHierarchyOriginalVertex T hT globalRoot
        (AllocationSpecial hT P optional) (Sum.inr ⟨i, a⟩)) =
    literalSourceClass P
      (wholeHierarchyOriginalVertex T hT globalRoot
        (AllocationSpecial hT P optional)
        ((AllocationHierarchy hT P optional).segmentRoot i))
  rw [hpoint, hroot]
  simpa only [wholeBranchSourceClass] using hlabel

abbrev SegmentMassCoordinate
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (I : Finset (SegmentIndex hT P optional)) :=
  Σ i : {i // i ∈ I},
    Fin ((AllocationHierarchy hT P optional).segments.size i.1)

abbrev BranchMassCoordinate
    (P : ZhaoForestPartition T globalRoot small)
    (A : Finset (BranchIndex P)) :=
  Σ j : {j // j ∈ A}, Fin ((branchForest P).branches.size j.1)

noncomputable def branchCoordinateIn
    (P : ZhaoForestPartition T globalRoot small)
    (A : Finset (BranchIndex P)) (x : V)
    (hx : x ∉ partitionRoots P)
    (hmem : (literalBranchCoordinate P x hx).1 ∈ A) :
    BranchMassCoordinate P A :=
  ⟨⟨(literalBranchCoordinate P x hx).1, hmem⟩,
    (literalBranchCoordinate P x hx).2⟩

@[simp] theorem decode_branchCoordinateIn
    (P : ZhaoForestPartition T globalRoot small)
    (A : Finset (BranchIndex P)) (x : V)
    (hx : x ∉ partitionRoots P)
    (hmem : (literalBranchCoordinate P x hx).1 ∈ A) :
    (partitionBranchEquivNonroots P
      (⟨(branchCoordinateIn P A x hx hmem).1.1,
        (branchCoordinateIn P A x hx hmem).2⟩ :
          Σ j, Fin ((branchForest P).branches.size j))).1 = x := by
  exact partitionBranchEquivNonroots_literalBranchCoordinate P x hx

/-- Segment mass in a chosen class injects into the corresponding literal
canonical Zhao branches, provided the already-proved nonmixing statement is
available for every segment coordinate. -/
theorem sum_segmentSize_le_branchMass_of_class
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (I : Finset (SegmentIndex hT P optional))
    (A : Finset (BranchIndex P))
    (hclass : ∀ i, i ∈ I →
      ∀ a : Fin ((AllocationHierarchy hT P optional).segments.size i),
        ∃ j ∈ A,
          literalSourceClass P
              (wholeHierarchyOriginalVertex T hT globalRoot
                (AllocationSpecial hT P optional) (Sum.inr ⟨i, a⟩)) =
            Sum.inr j) :
    (∑ i ∈ I, (AllocationHierarchy hT P optional).segments.size i) ≤
      ∑ j ∈ A, (branchForest P).branches.size j := by
  classical
  let sourceVertex : SegmentMassCoordinate hT P optional I → V := fun z ↦
    wholeHierarchyOriginalVertex T hT globalRoot
      (AllocationSpecial hT P optional) (Sum.inr ⟨z.1.1, z.2⟩)
  have sourceClass : ∀ z : SegmentMassCoordinate hT P optional I,
      ∃ j ∈ A, literalSourceClass P (sourceVertex z) = Sum.inr j := by
    intro z
    exact hclass z.1.1 z.1.2 z.2
  have sourceNonroot : ∀ z : SegmentMassCoordinate hT P optional I,
      sourceVertex z ∉ partitionRoots P := by
    intro z hz
    obtain ⟨j, -, hj⟩ := sourceClass z
    rw [literalSourceClass_of_root P (sourceVertex z) hz] at hj
    cases hj
  have coordinateMem : ∀ z : SegmentMassCoordinate hT P optional I,
      (literalBranchCoordinate P (sourceVertex z) (sourceNonroot z)).1 ∈ A := by
    intro z
    obtain ⟨j, hjA, hj⟩ := sourceClass z
    have hcoord := literalSourceClass_eq_inr_literalBranchCoordinate P
      (sourceVertex z) (sourceNonroot z)
    have heq :
        (literalBranchCoordinate P (sourceVertex z) (sourceNonroot z)).1 = j :=
      Sum.inr.inj (hcoord.symm.trans hj)
    simpa [heq] using hjA
  let f : SegmentMassCoordinate hT P optional I → BranchMassCoordinate P A :=
    fun z ↦ branchCoordinateIn P A (sourceVertex z)
      (sourceNonroot z) (coordinateMem z)
  let decode : BranchMassCoordinate P A → V := fun z ↦
    (partitionBranchEquivNonroots P
      (⟨z.1.1, z.2⟩ : Σ j, Fin ((branchForest P).branches.size j))).1
  have hdecode : ∀ z : SegmentMassCoordinate hT P optional I,
      decode (f z) = sourceVertex z := by
    intro z
    exact decode_branchCoordinateIn P A (sourceVertex z)
      (sourceNonroot z) (coordinateMem z)
  have hf : Function.Injective f := by
    intro z w hzw
    have hsource : sourceVertex z = sourceVertex w := by
      rw [← hdecode z, ← hdecode w, hzw]
    have hver : (Sum.inr ⟨z.1.1, z.2⟩ :
          (AllocationHierarchy hT P optional).Vertex) =
        Sum.inr ⟨w.1.1, w.2⟩ := by
      apply wholeHierarchyOriginalVertex_injective hT
        (AllocationSpecial hT P optional)
      exact hsource
    have hsigma := Sum.inr.inj hver
    apply Sigma.ext
    · exact Subtype.ext (congrArg Sigma.fst hsigma)
    · exact (Sigma.mk.inj_iff.mp hsigma).2
  have hcard : Fintype.card (SegmentMassCoordinate hT P optional I) ≤
      Fintype.card (BranchMassCoordinate P A) :=
    Fintype.card_le_of_injective f hf
  have hcard' :
      (∑ i : {i // i ∈ I},
        (AllocationHierarchy hT P optional).segments.size i.1) ≤
      ∑ j : {j // j ∈ A}, (branchForest P).branches.size j.1 := by
    simpa only [SegmentMassCoordinate, BranchMassCoordinate,
      Fintype.card_sigma, Fintype.card_fin] using hcard
  calc
    (∑ i ∈ I, (AllocationHierarchy hT P optional).segments.size i) =
        ∑ i : {i // i ∈ I},
          (AllocationHierarchy hT P optional).segments.size i.1 :=
      (Finset.sum_attach I _).symm
    _ ≤ ∑ j : {j // j ∈ A}, (branchForest P).branches.size j.1 := hcard'
    _ = ∑ j ∈ A, (branchForest P).branches.size j :=
      Finset.sum_attach A _

/-- One segment whose marked root carries each branch class gives the exact
root-count subtraction needed to turn vertex mass into matching-edge
demand. -/
theorem card_branch_le_segment_of_rootClasses
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (I : Finset (SegmentIndex hT P optional))
    (A : Finset (BranchIndex P))
    (hroot : ∀ j, j ∈ A → ∃ i ∈ I,
      segmentSourceClass hT P optional i = Sum.inr j) :
    #A ≤ #I := by
  classical
  let index : (j : {j // j ∈ A}) → SegmentIndex hT P optional :=
    fun j ↦ Classical.choose (hroot j.1 j.2)
  have index_mem : ∀ j : {j // j ∈ A}, index j ∈ I := fun j ↦
    (Classical.choose_spec (hroot j.1 j.2)).1
  have index_class : ∀ j : {j // j ∈ A},
      segmentSourceClass hT P optional (index j) = Sum.inr j.1 := fun j ↦
    (Classical.choose_spec (hroot j.1 j.2)).2
  let f : {j // j ∈ A} → {i // i ∈ I} := fun j ↦
    ⟨index j, index_mem j⟩
  have hf : Function.Injective f := by
    intro j k hjk
    apply Subtype.ext
    have hindex : index j = index k := congrArg Subtype.val hjk
    have hclass := congrArg
      (segmentSourceClass hT P optional) hindex
    rw [index_class j, index_class k] at hclass
    exact Sum.inr.inj hclass
  have hcard := Fintype.card_le_of_injective f hf
  simpa using hcard

noncomputable def rootSegments
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) : Finset (SegmentIndex hT P optional) :=
  by
    classical
    exact Finset.univ.filter fun i =>
      match segmentSourceClass hT P optional i with
      | Sum.inl _ => True
      | Sum.inr _ => False

noncomputable def F0Segments
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    Finset (SegmentIndex hT P optional) :=
  by
    classical
    exact Finset.univ.filter fun i =>
      match segmentSourceClass hT P optional i with
      | Sum.inl _ => False
      | Sum.inr j => j ∈ S.selected

noncomputable def F1Segments
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    Finset (SegmentIndex hT P optional) :=
  by
    classical
    exact Finset.univ.filter fun i =>
      match segmentSourceClass hT P optional i with
      | Sum.inl _ => False
      | Sum.inr j => j ∈ majorResidualBranches P S

noncomputable def FbSegments
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) : Finset (SegmentIndex hT P optional) :=
  by
    classical
    exact Finset.univ.filter fun i =>
      match segmentSourceClass hT P optional i with
      | Sum.inl _ => False
      | Sum.inr j => j ∈ minorBranches P

@[simp] theorem mem_rootSegments_iff
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (i : SegmentIndex hT P optional) :
    i ∈ rootSegments hT P optional ↔
      ∃ q, segmentSourceClass hT P optional i = Sum.inl q := by
  cases h : segmentSourceClass hT P optional i with
  | inl q => simp [rootSegments, h]
  | inr j => simp [rootSegments, h]

@[simp] theorem mem_F0Segments_iff
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (i : SegmentIndex hT P optional) :
    i ∈ F0Segments hT P optional S ↔
      ∃ j ∈ S.selected,
        segmentSourceClass hT P optional i = Sum.inr j := by
  cases h : segmentSourceClass hT P optional i with
  | inl q => simp [F0Segments, h]
  | inr j => simp [F0Segments, h]

@[simp] theorem mem_F1Segments_iff
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (i : SegmentIndex hT P optional) :
    i ∈ F1Segments hT P optional S ↔
      ∃ j ∈ majorResidualBranches P S,
        segmentSourceClass hT P optional i = Sum.inr j := by
  cases h : segmentSourceClass hT P optional i with
  | inl q => simp [F1Segments, h]
  | inr j => simp [F1Segments, h]

@[simp] theorem mem_FbSegments_iff
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (i : SegmentIndex hT P optional) :
    i ∈ FbSegments hT P optional ↔
      ∃ j ∈ minorBranches P,
        segmentSourceClass hT P optional i = Sum.inr j := by
  cases h : segmentSourceClass hT P optional i with
  | inl q => simp [FbSegments, h]
  | inr j => simp [FbSegments, h]

/-- The four source classes cover every whole-hierarchy segment. -/
theorem segmentClass_cover
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    rootSegments hT P optional ∪
        (F0Segments hT P optional S ∪
          (F1Segments hT P optional S ∪ FbSegments hT P optional)) =
      Finset.univ := by
  ext i
  cases hclass : segmentSourceClass hT P optional i with
  | inl q => simp [rootSegments, F0Segments, F1Segments, FbSegments, hclass]
  | inr j =>
      have hj : j ∈ S.selected ∪ majorResidualBranches P S ∪ minorBranches P := by
        rw [selected_union_residual_union_minor P S]
        exact Finset.mem_univ j
      simp only [Finset.mem_union] at hj
      rcases hj with (hj | hj) | hj
      · simp [rootSegments, F0Segments, F1Segments, FbSegments, hclass, hj]
      · simp [rootSegments, F0Segments, F1Segments, FbSegments, hclass, hj]
      · simp [rootSegments, F0Segments, F1Segments, FbSegments, hclass, hj]

theorem rootSegments_disjoint_F0
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    Disjoint (rootSegments hT P optional) (F0Segments hT P optional S) := by
  rw [Finset.disjoint_left]
  intro i hiRoot hiF0
  obtain ⟨q, hq⟩ := (mem_rootSegments_iff hT P optional i).mp hiRoot
  obtain ⟨j, -, hj⟩ := (mem_F0Segments_iff hT P optional S i).mp hiF0
  rw [hq] at hj
  cases hj

theorem rootSegments_disjoint_F1
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    Disjoint (rootSegments hT P optional) (F1Segments hT P optional S) := by
  rw [Finset.disjoint_left]
  intro i hiRoot hiF1
  obtain ⟨q, hq⟩ := (mem_rootSegments_iff hT P optional i).mp hiRoot
  obtain ⟨j, -, hj⟩ := (mem_F1Segments_iff hT P optional S i).mp hiF1
  rw [hq] at hj
  cases hj

theorem rootSegments_disjoint_Fb
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) :
    Disjoint (rootSegments hT P optional) (FbSegments hT P optional) := by
  rw [Finset.disjoint_left]
  intro i hiRoot hiFb
  obtain ⟨q, hq⟩ := (mem_rootSegments_iff hT P optional i).mp hiRoot
  obtain ⟨j, -, hj⟩ := (mem_FbSegments_iff hT P optional i).mp hiFb
  rw [hq] at hj
  cases hj

theorem F0Segments_disjoint_F1
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    Disjoint (F0Segments hT P optional S) (F1Segments hT P optional S) := by
  rw [Finset.disjoint_left]
  intro i hiF0 hiF1
  obtain ⟨j, hjSel, hj⟩ := (mem_F0Segments_iff hT P optional S i).mp hiF0
  obtain ⟨k, hkRes, hk⟩ := (mem_F1Segments_iff hT P optional S i).mp hiF1
  have hjk : j = k := Sum.inr.inj (hj.symm.trans hk)
  subst k
  exact (mem_majorResidualBranches P S j).mp hkRes |>.2 hjSel

theorem F0Segments_disjoint_Fb
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    Disjoint (F0Segments hT P optional S) (FbSegments hT P optional) := by
  rw [Finset.disjoint_left]
  intro i hiF0 hiFb
  obtain ⟨j, hjSel, hj⟩ := (mem_F0Segments_iff hT P optional S i).mp hiF0
  obtain ⟨k, hkMinor, hk⟩ := (mem_FbSegments_iff hT P optional i).mp hiFb
  have hjk : j = k := Sum.inr.inj (hj.symm.trans hk)
  subst k
  exact Finset.disjoint_left.mp (halfBranches_disjoint_minorBranches P)
    (S.selected_available hjSel) hkMinor

theorem F1Segments_disjoint_Fb
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    Disjoint (F1Segments hT P optional S) (FbSegments hT P optional) := by
  rw [Finset.disjoint_left]
  intro i hiF1 hiFb
  obtain ⟨j, hjRes, hj⟩ := (mem_F1Segments_iff hT P optional S i).mp hiF1
  obtain ⟨k, hkMinor, hk⟩ := (mem_FbSegments_iff hT P optional i).mp hiFb
  have hjk : j = k := Sum.inr.inj (hj.symm.trans hk)
  subst k
  exact Finset.disjoint_left.mp (halfBranches_disjoint_minorBranches P)
    ((mem_majorResidualBranches P S j).mp hjRes).1 hkMinor

def segmentDeepWeight
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (i : SegmentIndex hT P optional) : ℕ :=
  (AllocationHierarchy hT P optional).segments.size i - 1

theorem sum_segmentDeepWeight_add_card
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (I : Finset (SegmentIndex hT P optional)) :
    (∑ i ∈ I, segmentDeepWeight hT P optional i) + #I =
      ∑ i ∈ I, (AllocationHierarchy hT P optional).segments.size i := by
  calc
    (∑ i ∈ I, segmentDeepWeight hT P optional i) + #I =
        (∑ i ∈ I, segmentDeepWeight hT P optional i) +
          ∑ _i ∈ I, 1 := by simp
    _ = ∑ i ∈ I, (segmentDeepWeight hT P optional i + 1) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ i ∈ I,
        (AllocationHierarchy hT P optional).segments.size i := by
      apply Finset.sum_congr rfl
      intro i _
      exact Nat.sub_add_cancel
        (segmented_size_pos (wholeBranchForest T hT globalRoot)
          (AllocationSpecial hT P optional) i)

theorem sum_branchDeepWeight_add_card
    (P : ZhaoForestPartition T globalRoot small)
    (A : Finset (BranchIndex P)) :
    (∑ j ∈ A, ((branchForest P).branches.size j - 1)) + #A =
      ∑ j ∈ A, (branchForest P).branches.size j := by
  calc
    (∑ j ∈ A, ((branchForest P).branches.size j - 1)) + #A =
        (∑ j ∈ A, ((branchForest P).branches.size j - 1)) +
          ∑ _j ∈ A, 1 := by simp
    _ = ∑ j ∈ A, (((branchForest P).branches.size j - 1) + 1) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ j ∈ A, (branchForest P).branches.size j := by
      apply Finset.sum_congr rfl
      intro j _
      exact Nat.sub_add_cancel (branch_size_pos (branchForest P) j)

/-- Restricted matching demand follows from the two structural facts proved
by the nonmixing classifier: segment mass injects into its source branches,
and every source branch contributes at least one marked segment root. -/
theorem sum_segmentDeepWeight_le_branchDemand
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (I : Finset (SegmentIndex hT P optional))
    (A : Finset (BranchIndex P))
    (hmass : (∑ i ∈ I,
        (AllocationHierarchy hT P optional).segments.size i) ≤
      ∑ j ∈ A, (branchForest P).branches.size j)
    (hroots : #A ≤ #I) :
    (∑ i ∈ I, segmentDeepWeight hT P optional i) ≤
      ∑ j ∈ A, ((branchForest P).branches.size j - 1) := by
  have hseg := sum_segmentDeepWeight_add_card hT P optional I
  have hbranch := sum_branchDeepWeight_add_card P A
  omega

/-- Exact `size - 1` partition across component-root, `F₀`, `F₁`, and `F_b`
segments.  It is independent of all host choices. -/
theorem sum_segmentDeepWeight_by_class
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    (∑ i, segmentDeepWeight hT P optional i) =
      (∑ i ∈ rootSegments hT P optional,
          segmentDeepWeight hT P optional i) +
      (∑ i ∈ F0Segments hT P optional S,
          segmentDeepWeight hT P optional i) +
      (∑ i ∈ F1Segments hT P optional S,
          segmentDeepWeight hT P optional i) +
      (∑ i ∈ FbSegments hT P optional,
          segmentDeepWeight hT P optional i) := by
  let R := rootSegments hT P optional
  let A := F0Segments hT P optional S
  let C := F1Segments hT P optional S
  let D := FbSegments hT P optional
  have hCD : Disjoint C D := F1Segments_disjoint_Fb hT P optional S
  have hACD : Disjoint A (C ∪ D) :=
    Finset.disjoint_union_right.mpr
      ⟨F0Segments_disjoint_F1 hT P optional S,
        F0Segments_disjoint_Fb hT P optional S⟩
  have hRACD : Disjoint R (A ∪ (C ∪ D)) :=
    Finset.disjoint_union_right.mpr
      ⟨rootSegments_disjoint_F0 hT P optional S,
        Finset.disjoint_union_right.mpr
          ⟨rootSegments_disjoint_F1 hT P optional S,
            rootSegments_disjoint_Fb hT P optional⟩⟩
  calc
    (∑ i, segmentDeepWeight hT P optional i) =
        ∑ i ∈ R ∪ (A ∪ (C ∪ D)), segmentDeepWeight hT P optional i := by
      rw [segmentClass_cover hT P optional S]
    _ = (∑ i ∈ R, segmentDeepWeight hT P optional i) +
        ∑ i ∈ A ∪ (C ∪ D), segmentDeepWeight hT P optional i := by
      rw [Finset.sum_union hRACD]
    _ = (∑ i ∈ R, segmentDeepWeight hT P optional i) +
        ((∑ i ∈ A, segmentDeepWeight hT P optional i) +
          ∑ i ∈ C ∪ D, segmentDeepWeight hT P optional i) := by
      rw [Finset.sum_union hACD]
    _ = (∑ i ∈ R, segmentDeepWeight hT P optional i) +
        (∑ i ∈ A, segmentDeepWeight hT P optional i) +
        (∑ i ∈ C, segmentDeepWeight hT P optional i) +
        (∑ i ∈ D, segmentDeepWeight hT P optional i) := by
      rw [Finset.sum_union hCD]
      omega

/-! Component-root classes carry no matching-pair mass.  The strengthened
marking cuts immediately again at every canonical child branch root, and
nonmixing says that every vertex left in a root-class segment is the same
literal component root. -/

theorem rootSegment_size_eq_one
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (i : SegmentIndex hT P optional)
    (hi : i ∈ rootSegments hT P optional) :
    (AllocationHierarchy hT P optional).segments.size i = 1 := by
  obtain ⟨q, hclass⟩ := (mem_rootSegments_iff hT P optional i).mp hi
  have hroot : ∀ a : Fin
        ((AllocationHierarchy hT P optional).segments.size i),
      wholeHierarchyOriginalVertex T hT globalRoot
          (AllocationSpecial hT P optional) (Sum.inr ⟨i, a⟩) =
        P.roots q := by
    intro a
    apply (literalSourceClass_eq_inl_iff P _ q).mp
    exact (wholeSegment_sourceClass_eq_of_boundary hT P optional
      (canonicalWholeSourceBoundary hT P optional) i a).trans hclass
  let f : Fin ((AllocationHierarchy hT P optional).segments.size i) → Unit :=
    fun _ ↦ ()
  have hf : Function.Injective f := by
    intro a b _
    have hver : (Sum.inr (⟨i, a⟩ :
          Σ k, Fin ((AllocationHierarchy hT P optional).segments.size k)) :
          (AllocationHierarchy hT P optional).Vertex) =
        Sum.inr (⟨i, b⟩ :
          Σ k, Fin ((AllocationHierarchy hT P optional).segments.size k)) := by
      apply wholeHierarchyOriginalVertex_injective hT
        (AllocationSpecial hT P optional)
      rw [hroot a, hroot b]
    have hsigma := Sum.inr.inj hver
    exact eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2
  have hle := Fintype.card_le_of_injective f hf
  have hpos := segmented_size_pos (wholeBranchForest T hT globalRoot)
    (AllocationSpecial hT P optional) i
  have hle' : (AllocationHierarchy hT P optional).segments.size i ≤ 1 := by
    simpa [f] using hle
  change 0 < (AllocationHierarchy hT P optional).segments.size i at hpos
  omega

theorem rootSegment_deepWeight_eq_zero
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (i : SegmentIndex hT P optional)
    (hi : i ∈ rootSegments hT P optional) :
    segmentDeepWeight hT P optional i = 0 := by
  simp [segmentDeepWeight, rootSegment_size_eq_one hT P optional i hi]

theorem sum_rootSegment_deepWeight_eq_zero
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) :
    (∑ i ∈ rootSegments hT P optional,
      segmentDeepWeight hT P optional i) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact rootSegment_deepWeight_eq_zero hT P optional i hi

theorem sum_segmentDeepWeight_eq_threeBranchClasses
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    (∑ i, segmentDeepWeight hT P optional i) =
      (∑ i ∈ F0Segments hT P optional S,
        segmentDeepWeight hT P optional i) +
      (∑ i ∈ F1Segments hT P optional S,
        segmentDeepWeight hT P optional i) +
      (∑ i ∈ FbSegments hT P optional,
        segmentDeepWeight hT P optional i) := by
  have hsplit := sum_segmentDeepWeight_by_class hT P optional S
  have hroot := sum_rootSegment_deepWeight_eq_zero hT P optional
  omega

/-! ## Concrete residual demand bounds -/

theorem exists_F0Segment_of_mem
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (j : BranchIndex P) (hj : j ∈ S.selected) :
    ∃ i ∈ F0Segments hT P optional S,
      segmentSourceClass hT P optional i = Sum.inr j := by
  obtain ⟨i, -, hi⟩ := exists_segmentRoot_of_canonicalBranch hT P optional j
  exact ⟨i, (mem_F0Segments_iff hT P optional S i).2 ⟨j, hj, hi⟩, hi⟩

theorem exists_F1Segment_of_mem
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (j : BranchIndex P) (hj : j ∈ majorResidualBranches P S) :
    ∃ i ∈ F1Segments hT P optional S,
      segmentSourceClass hT P optional i = Sum.inr j := by
  obtain ⟨i, -, hi⟩ := exists_segmentRoot_of_canonicalBranch hT P optional j
  exact ⟨i, (mem_F1Segments_iff hT P optional S i).2 ⟨j, hj, hi⟩, hi⟩

theorem exists_FbSegment_of_mem
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (j : BranchIndex P) (hj : j ∈ minorBranches P) :
    ∃ i ∈ FbSegments hT P optional,
      segmentSourceClass hT P optional i = Sum.inr j := by
  obtain ⟨i, -, hi⟩ := exists_segmentRoot_of_canonicalBranch hT P optional j
  exact ⟨i, (mem_FbSegments_iff hT P optional i).2 ⟨j, hj, hi⟩, hi⟩

theorem sum_F0_segmentSize_le_of_boundary
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (hboundary : WholeSourceBoundary hT P optional) :
    (∑ i ∈ F0Segments hT P optional S,
        (AllocationHierarchy hT P optional).segments.size i) ≤
      ∑ j ∈ S.selected, (branchForest P).branches.size j := by
  apply sum_segmentSize_le_branchMass_of_class hT P optional
  intro i hi a
  obtain ⟨j, hj, hclass⟩ :=
    (mem_F0Segments_iff hT P optional S i).mp hi
  exact ⟨j, hj,
    (wholeSegment_sourceClass_eq_of_boundary hT P optional hboundary i a).trans
      hclass⟩

theorem sum_F1_segmentSize_le_of_boundary
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (hboundary : WholeSourceBoundary hT P optional) :
    (∑ i ∈ F1Segments hT P optional S,
        (AllocationHierarchy hT P optional).segments.size i) ≤
      ∑ j ∈ majorResidualBranches P S,
        (branchForest P).branches.size j := by
  apply sum_segmentSize_le_branchMass_of_class hT P optional
  intro i hi a
  obtain ⟨j, hj, hclass⟩ :=
    (mem_F1Segments_iff hT P optional S i).mp hi
  exact ⟨j, hj,
    (wholeSegment_sourceClass_eq_of_boundary hT P optional hboundary i a).trans
      hclass⟩

theorem sum_Fb_segmentSize_le_of_boundary
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (hboundary : WholeSourceBoundary hT P optional) :
    (∑ i ∈ FbSegments hT P optional,
        (AllocationHierarchy hT P optional).segments.size i) ≤
      ∑ j ∈ minorBranches P, (branchForest P).branches.size j := by
  apply sum_segmentSize_le_branchMass_of_class hT P optional
  intro i hi a
  obtain ⟨j, hj, hclass⟩ := (mem_FbSegments_iff hT P optional i).mp hi
  exact ⟨j, hj,
    (wholeSegment_sourceClass_eq_of_boundary hT P optional hboundary i a).trans
      hclass⟩

theorem sum_F0_segmentDeepWeight_le_of_boundary
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (hboundary : WholeSourceBoundary hT P optional) :
    (∑ i ∈ F0Segments hT P optional S,
        segmentDeepWeight hT P optional i) ≤
      ∑ j ∈ S.selected, ((branchForest P).branches.size j - 1) := by
  apply sum_segmentDeepWeight_le_branchDemand hT P optional
  · exact sum_F0_segmentSize_le_of_boundary hT P optional S hboundary
  · apply card_branch_le_segment_of_rootClasses hT P optional
    intro j hj
    exact exists_F0Segment_of_mem hT P optional S j hj

theorem sum_F1_segmentDeepWeight_le_of_boundary
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (hboundary : WholeSourceBoundary hT P optional) :
    (∑ i ∈ F1Segments hT P optional S,
        segmentDeepWeight hT P optional i) ≤
      ∑ j ∈ majorResidualBranches P S,
        ((branchForest P).branches.size j - 1) := by
  apply sum_segmentDeepWeight_le_branchDemand hT P optional
  · exact sum_F1_segmentSize_le_of_boundary hT P optional S hboundary
  · apply card_branch_le_segment_of_rootClasses hT P optional
    intro j hj
    exact exists_F1Segment_of_mem hT P optional S j hj

theorem sum_Fb_segmentDeepWeight_le_of_boundary
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (hboundary : WholeSourceBoundary hT P optional) :
    (∑ i ∈ FbSegments hT P optional,
        segmentDeepWeight hT P optional i) ≤
      ∑ j ∈ minorBranches P,
        ((branchForest P).branches.size j - 1) := by
  apply sum_segmentDeepWeight_le_branchDemand hT P optional
  · exact sum_Fb_segmentSize_le_of_boundary hT P optional hboundary
  · apply card_branch_le_segment_of_rootClasses hT P optional
    intro j hj
    exact exists_FbSegment_of_mem hT P optional j hj

theorem sum_F0_segmentSize_le
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    (∑ i ∈ F0Segments hT P optional S,
        (AllocationHierarchy hT P optional).segments.size i) ≤
      ∑ j ∈ S.selected, (branchForest P).branches.size j :=
  sum_F0_segmentSize_le_of_boundary hT P optional S
    (canonicalWholeSourceBoundary hT P optional)

theorem sum_F1_segmentSize_le
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    (∑ i ∈ F1Segments hT P optional S,
        (AllocationHierarchy hT P optional).segments.size i) ≤
      ∑ j ∈ majorResidualBranches P S,
        (branchForest P).branches.size j :=
  sum_F1_segmentSize_le_of_boundary hT P optional S
    (canonicalWholeSourceBoundary hT P optional)

theorem sum_Fb_segmentSize_le
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) :
    (∑ i ∈ FbSegments hT P optional,
        (AllocationHierarchy hT P optional).segments.size i) ≤
      ∑ j ∈ minorBranches P, (branchForest P).branches.size j :=
  sum_Fb_segmentSize_le_of_boundary hT P optional
    (canonicalWholeSourceBoundary hT P optional)

theorem sum_F0_segmentSize_le_edgeDemand
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    (∑ i ∈ F0Segments hT P optional S,
        (AllocationHierarchy hT P optional).segments.size i) ≤
      OrderedBranchForest.edgeDemand (F0 P S) := by
  simpa only [F0, OrderedBranchForest.edgeDemand_restrict] using
    sum_F0_segmentSize_le hT P optional S

theorem sum_F1_segmentSize_le_edgeDemand
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    (∑ i ∈ F1Segments hT P optional S,
        (AllocationHierarchy hT P optional).segments.size i) ≤
      OrderedBranchForest.edgeDemand (F1 P S) := by
  simpa only [F1, OrderedBranchForest.edgeDemand_restrict] using
    sum_F1_segmentSize_le hT P optional S

theorem sum_Fb_segmentSize_le_edgeDemand
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) :
    (∑ i ∈ FbSegments hT P optional,
        (AllocationHierarchy hT P optional).segments.size i) ≤
      OrderedBranchForest.edgeDemand (Fb P) := by
  simpa only [Fb, OrderedBranchForest.edgeDemand_restrict] using
    sum_Fb_segmentSize_le hT P optional

theorem sum_F0_segmentDeepWeight_le
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    (∑ i ∈ F0Segments hT P optional S,
        segmentDeepWeight hT P optional i) ≤
      ∑ j ∈ S.selected, ((branchForest P).branches.size j - 1) :=
  sum_F0_segmentDeepWeight_le_of_boundary hT P optional S
    (canonicalWholeSourceBoundary hT P optional)

theorem sum_F1_segmentDeepWeight_le
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    (∑ i ∈ F1Segments hT P optional S,
        segmentDeepWeight hT P optional i) ≤
      ∑ j ∈ majorResidualBranches P S,
        ((branchForest P).branches.size j - 1) :=
  sum_F1_segmentDeepWeight_le_of_boundary hT P optional S
    (canonicalWholeSourceBoundary hT P optional)

theorem sum_Fb_segmentDeepWeight_le
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) :
    (∑ i ∈ FbSegments hT P optional,
        segmentDeepWeight hT P optional i) ≤
      ∑ j ∈ minorBranches P,
        ((branchForest P).branches.size j - 1) :=
  sum_Fb_segmentDeepWeight_le_of_boundary hT P optional
    (canonicalWholeSourceBoundary hT P optional)

/-- Consumer-facing forms stated in the exact `deepDemand` quantities of
the three restricted Zhao branch forests. -/
theorem sum_F0_segmentDeepWeight_le_deepDemand
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    (∑ i ∈ F0Segments hT P optional S,
        segmentDeepWeight hT P optional i) ≤
      Erdos547b.ZhaoLemma59Part2Full.deepDemand (F0 P S) := by
  simpa only [F0,
    Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.deepDemand_restrict] using
    sum_F0_segmentDeepWeight_le hT P optional S

theorem sum_F1_segmentDeepWeight_le_deepDemand
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    (∑ i ∈ F1Segments hT P optional S,
        segmentDeepWeight hT P optional i) ≤
      Erdos547b.ZhaoLemma59Part2Full.deepDemand (F1 P S) := by
  simpa only [F1,
    Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.deepDemand_restrict] using
    sum_F1_segmentDeepWeight_le hT P optional S

theorem sum_Fb_segmentDeepWeight_le_deepDemand
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) :
    (∑ i ∈ FbSegments hT P optional,
        segmentDeepWeight hT P optional i) ≤
      Erdos547b.ZhaoLemma59Part2Full.deepDemand (Fb P) := by
  simpa only [Fb,
    Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.deepDemand_restrict] using
    sum_Fb_segmentDeepWeight_le hT P optional

theorem sum_segmentDeepWeight_le_threeDeepDemands
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    (∑ i, segmentDeepWeight hT P optional i) ≤
      Erdos547b.ZhaoLemma59Part2Full.deepDemand (F0 P S) +
      Erdos547b.ZhaoLemma59Part2Full.deepDemand (F1 P S) +
      Erdos547b.ZhaoLemma59Part2Full.deepDemand (Fb P) := by
  rw [sum_segmentDeepWeight_eq_threeBranchClasses hT P optional S]
  exact Nat.add_le_add
    (Nat.add_le_add
      (sum_F0_segmentDeepWeight_le_deepDemand hT P optional S)
      (sum_F1_segmentDeepWeight_le_deepDemand hT P optional S))
    (sum_Fb_segmentDeepWeight_le_deepDemand hT P optional)

theorem segment_size_le_sourceBranch
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) (i : SegmentIndex hT P optional)
    (j : BranchIndex P)
    (hclass : segmentSourceClass hT P optional i = Sum.inr j) :
    (AllocationHierarchy hT P optional).segments.size i ≤
      (branchForest P).branches.size j := by
  have hmass := sum_segmentSize_le_branchMass_of_class hT P optional
    {i} {j} (by
      intro k hk a
      have hki : k = i := by simpa using hk
      subst k
      exact ⟨j, Finset.mem_singleton_self j,
        (wholeSegment_sourceClass_eq_of_boundary hT P optional
          (canonicalWholeSourceBoundary hT P optional) i a).trans hclass⟩)
  simpa using hmass

/-- Every canonical root-deleted branch has at most `small` vertices.  This
is the literal branch-coordinate form of `P.component_mTree`; it removes the
last abstract per-branch size premise from the hierarchy allocator. -/
theorem canonical_branch_size_le_small
    (P : ZhaoForestPartition T globalRoot small) (j : BranchIndex P) :
    (branchForest P).branches.size j ≤ small := by
  let i : Fin P.numParts := (childKeyEquiv P.orderedForest j).1.1
  let c : Fin (P.orderedForest.size i) :=
    (childKeyEquiv P.orderedForest j).1.2
  let rootC : ↑(P.components i) := ⟨P.roots i, P.root_mem i⟩
  let childC : ↑(P.components i) := P.componentEquiv i c
  have hrootC : P.componentEquiv i (P.orderedForest.root i) = rootC := by
    exact Equiv.apply_symm_apply _ _
  have hchildNe : childC ≠ rootC := by
    intro hcr
    have hlocal : c = P.orderedForest.root i := by
      apply (P.componentEquiv i).injective
      simpa only [childC, hrootC] using hcr
    exact (childKeyEquiv P.orderedForest j).2.ne hlocal.symm
  have hdesc : ∀ a : Fin ((branchForest P).branches.size j),
      P.componentEquiv i (branchLocalVertex P.orderedForest j a) ∈
        rootedDescendantsSet (P.components i).toSimpleGraph rootC childC := by
    intro a
    have hlocal := (mem_rootedDescendants.mp
      (branchLocalVertex_mem P.orderedForest j a))
    change (P.components i).toSimpleGraph.dist rootC
        (P.componentEquiv i (branchLocalVertex P.orderedForest j a)) =
      (P.components i).toSimpleGraph.dist rootC childC +
        (P.components i).toSimpleGraph.dist childC
          (P.componentEquiv i (branchLocalVertex P.orderedForest j a))
    rw [← hrootC]
    dsimp only [childC]
    rw [componentEquiv_dist_eq, componentEquiv_dist_eq,
      componentEquiv_dist_eq]
    exact hlocal
  let e : Fin ((branchForest P).branches.size j) ↪
      {x // x ∈ rootedDescendantsSet
        (P.components i).toSimpleGraph rootC childC} :=
    { toFun := fun a ↦
        ⟨P.componentEquiv i (branchLocalVertex P.orderedForest j a), hdesc a⟩
      inj' := by
        intro a b hab
        have hlocal : branchLocalVertex P.orderedForest j a =
            branchLocalVertex P.orderedForest j b := by
          apply (P.componentEquiv i).injective
          exact congrArg Subtype.val hab
        have hsub :
            (branchSetEquiv P.orderedForest j).symm
                (branchVertexEquiv P.orderedForest j a) =
              (branchSetEquiv P.orderedForest j).symm
                (branchVertexEquiv P.orderedForest j b) := by
          apply Subtype.ext
          exact hlocal
        exact (branchVertexEquiv P.orderedForest j).injective
          ((branchSetEquiv P.orderedForest j).symm.injective hsub) }
  have hcard := Nat.card_le_card_of_injective e e.injective
  have hcard' : (branchForest P).branches.size j ≤
      (rootedDescendantsSet
        (P.components i).toSimpleGraph rootC childC).ncard := by
    simpa only [Nat.card_fin, Nat.card_coe_set_eq] using hcard
  exact hcard'.trans ((P.component_mTree i).2 childC hchildNe)

theorem all_canonical_branch_size_le_small
    (P : ZhaoForestPartition T globalRoot small) :
    ∀ j, (branchForest P).branches.size j ≤ small :=
  canonical_branch_size_le_small P

theorem F0_segment_size_le
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (bound : ℕ) (hsmall : ∀ j, (branchForest P).branches.size j ≤ bound)
    (i : SegmentIndex hT P optional) (hi : i ∈ F0Segments hT P optional S) :
    (AllocationHierarchy hT P optional).segments.size i ≤ bound := by
  obtain ⟨j, -, hclass⟩ := (mem_F0Segments_iff hT P optional S i).mp hi
  exact (segment_size_le_sourceBranch hT P optional i j hclass).trans (hsmall j)

theorem F0_segment_size_le_small
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (i : SegmentIndex hT P optional) (hi : i ∈ F0Segments hT P optional S) :
    (AllocationHierarchy hT P optional).segments.size i ≤ small :=
  F0_segment_size_le hT P optional S small
    (all_canonical_branch_size_le_small P) i hi

theorem F1_segment_size_le
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (bound : ℕ) (hsmall : ∀ j, (branchForest P).branches.size j ≤ bound)
    (i : SegmentIndex hT P optional) (hi : i ∈ F1Segments hT P optional S) :
    (AllocationHierarchy hT P optional).segments.size i ≤ bound := by
  obtain ⟨j, -, hclass⟩ := (mem_F1Segments_iff hT P optional S i).mp hi
  exact (segment_size_le_sourceBranch hT P optional i j hclass).trans (hsmall j)

theorem F1_segment_size_le_small
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (i : SegmentIndex hT P optional) (hi : i ∈ F1Segments hT P optional S) :
    (AllocationHierarchy hT P optional).segments.size i ≤ small :=
  F1_segment_size_le hT P optional S small
    (all_canonical_branch_size_le_small P) i hi

theorem Fb_segment_size_le
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (bound : ℕ) (hsmall : ∀ j, (branchForest P).branches.size j ≤ bound)
    (i : SegmentIndex hT P optional) (hi : i ∈ FbSegments hT P optional) :
    (AllocationHierarchy hT P optional).segments.size i ≤ bound := by
  obtain ⟨j, -, hclass⟩ := (mem_FbSegments_iff hT P optional i).mp hi
  exact (segment_size_le_sourceBranch hT P optional i j hclass).trans (hsmall j)

theorem Fb_segment_size_le_small
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    (i : SegmentIndex hT P optional) (hi : i ∈ FbSegments hT P optional) :
    (AllocationHierarchy hT P optional).segments.size i ≤ small :=
  Fb_segment_size_le hT P optional small
    (all_canonical_branch_size_le_small P) i hi

end Erdos547b.ZhaoClaim616HierarchyClassification

#print axioms Erdos547b.ZhaoClaim616HierarchyClassification.segmentClass_cover
#print axioms Erdos547b.ZhaoClaim616HierarchyClassification.sum_segmentDeepWeight_by_class
#print axioms Erdos547b.ZhaoClaim616HierarchyClassification.canonicalWholeSourceBoundary
#print axioms Erdos547b.ZhaoClaim616HierarchyClassification.sum_F0_segmentDeepWeight_le
#print axioms Erdos547b.ZhaoClaim616HierarchyClassification.sum_F1_segmentDeepWeight_le
#print axioms Erdos547b.ZhaoClaim616HierarchyClassification.sum_Fb_segmentDeepWeight_le
#print axioms Erdos547b.ZhaoClaim616HierarchyClassification.canonical_branch_size_le_small
