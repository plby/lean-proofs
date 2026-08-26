/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim610BranchLeaves
import ErdosProblems.Erdos547b.Claim615SourceSelection

/-!
# Leaves contributed by root-deleted branches

The possible local leaf at the root of a branch is the only leaf lost when
the branch is reattached to its owner.  The integral `+1` in Fact 6.9 pays
for precisely this loss.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim610BranchForestLeaves

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim610BranchLeaves
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim68BranchGraphTransport
open Erdos547b.TreePartition

universe u

noncomputable local instance finiteGraphAdjDecidable
    {W : Type*} [Fintype W] (G : SimpleGraph W) : DecidableRel G.Adj :=
  Classical.decRel _

/-- Leaves of branch `j` after its root is attached to its owner. -/
def attachedBranchLeaves {r b : ℕ} (F : OrderedBranchForest r b)
    (j : Fin b) : Finset (Fin (F.branches.size j)) :=
  Finset.univ.filter fun a =>
    F.graph.degree (Sum.inr (⟨j, a⟩ :
      Σ q, Fin (F.branches.size q))) = 1

@[simp] theorem mem_attachedBranchLeaves {r b : ℕ}
    (F : OrderedBranchForest r b) (j : Fin b)
    (a : Fin (F.branches.size j)) :
    a ∈ attachedBranchLeaves F j ↔
      F.graph.degree (Sum.inr (⟨j, a⟩ :
        Σ q, Fin (F.branches.size q))) = 1 := by
  simp [attachedBranchLeaves]

/-- Away from the branch root, a local leaf remains a leaf after attaching
the root to its owner. -/
theorem attached_degree_eq_one_of_local_leaf_of_ne_root
    {r b : ℕ} (F : OrderedBranchForest r b) (j : Fin b)
    (a : Fin (F.branches.size j))
    (haRoot : a ≠ F.branches.root j)
    (haLeaf : (F.branches.tree j).degree a = 1) :
    F.graph.degree (Sum.inr (⟨j, a⟩ :
      Σ q, Fin (F.branches.size q))) = 1 := by
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj] at haLeaf ⊢
  obtain ⟨p, hap, hpUnique⟩ := haLeaf
  refine ⟨Sum.inr (⟨j, p⟩ :
      Σ q, Fin (F.branches.size q)), ?_, ?_⟩
  · exact ⟨rfl, hap⟩
  · intro y hay
    rcases y with i | z
    · exfalso
      have hroot := (F.graph_adj_branch_root
        (⟨j, a⟩ : Σ q, Fin (F.branches.size q)) i).mp hay
      exact haRoot hroot.2
    · rcases z with ⟨k, q⟩
      rcases (F.graph_adj_branch_branch _ _).mp hay with ⟨hjk, haq⟩
      change j = k at hjk
      cases hjk
      have haq' : (F.branches.tree j).Adj a q := by
        simpa using haq
      have hqp : q = p := hpUnique q haq'
      subst q
      rfl

/-- All local leaves except possibly the branch root are attached leaves. -/
theorem localLeaves_erase_root_subset_attachedBranchLeaves
    {r b : ℕ} (F : OrderedBranchForest r b) (j : Fin b) :
    Erdos547b.leavesIn (F.branches.tree j)
        (Finset.univ : Finset (Fin (F.branches.size j))) \ 
        {F.branches.root j} ⊆
      attachedBranchLeaves F j := by
  intro a ha
  have ha' := Finset.mem_sdiff.mp ha
  have haLeaf : (F.branches.tree j).degree a = 1 := by
    simpa [Erdos547b.leavesIn, Erdos547b.IsLeaf] using ha'.1
  have haRoot : a ≠ F.branches.root j := by
    simpa using ha'.2
  rw [mem_attachedBranchLeaves]
  exact attached_degree_eq_one_of_local_leaf_of_ne_root F j a haRoot haLeaf

/-- The cardinal loss from reattaching one branch is at most one. -/
theorem card_localLeaves_le_card_attached_add_one
    {r b : ℕ} (F : OrderedBranchForest r b) (j : Fin b) :
    #(Erdos547b.leavesIn (F.branches.tree j)
        (Finset.univ : Finset (Fin (F.branches.size j)))) ≤
      #(attachedBranchLeaves F j) + 1 := by
  let L := Erdos547b.leavesIn (F.branches.tree j)
    (Finset.univ : Finset (Fin (F.branches.size j)))
  have hsubset : L \ {F.branches.root j} ⊆ attachedBranchLeaves F j :=
    localLeaves_erase_root_subset_attachedBranchLeaves F j
  have hloss : #L ≤ #(L \ {F.branches.root j}) + 1 := by
    by_cases hr : F.branches.root j ∈ L
    · rw [Finset.card_sdiff_of_subset]
      · simp only [Finset.card_singleton]
        omega
      · simpa only [Finset.singleton_subset_iff] using hr
    · have heq : L \ {F.branches.root j} = L := by
        ext a
        simp only [Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        · exact And.left
        · intro ha
          exact ⟨ha, fun h => hr (h ▸ ha)⟩
      rw [heq]
      omega
  exact hloss.trans (Nat.add_le_add_right (Finset.card_le_card hsubset) 1)

/-- An unbalanced branch contributes its full Fact-6.9 real lower bound to
the leaves of the attached forest. -/
theorem factor_mul_size_le_attachedBranchLeaves
    {r b : ℕ} (F : OrderedBranchForest r b) (j : Fin b)
    (alpha : ℝ) (halpha0 : 0 ≤ alpha) (halphaHalf : alpha ≤ 1 / 2)
    (hunbalanced : ¬(alpha <
        (#(treeColourClass (F.branches.tree j) (F.branches.isTree j)
          (F.branches.root j) 0) : ℝ) / F.branches.size j ∧
      (#(treeColourClass (F.branches.tree j) (F.branches.isTree j)
          (F.branches.root j) 0) : ℝ) / F.branches.size j <
        1 - alpha)) :
    (1 - 2 * alpha) * F.branches.size j ≤
      #(attachedBranchLeaves F j) := by
  have hsizePos : 0 < F.branches.size j := by
    have := (F.branches.root j).isLt
    omega
  by_cases hsizeOne : F.branches.size j = 1
  · have hrootMem : F.branches.root j ∈ attachedBranchLeaves F j := by
      rw [mem_attachedBranchLeaves,
        SimpleGraph.degree_eq_one_iff_existsUnique_adj]
      refine ⟨Sum.inl (F.owner j), ⟨rfl, rfl⟩, ?_⟩
      intro y hy
      rcases y with i | z
      · have hi := (F.graph_adj_branch_root
          (⟨j, F.branches.root j⟩ :
            Σ q, Fin (F.branches.size q)) i).mp hy
        exact congrArg Sum.inl hi.1.symm
      · rcases z with ⟨k, q⟩
        rcases (F.graph_adj_branch_branch _ _).mp hy with ⟨hjk, hadj⟩
        change j = k at hjk
        cases hjk
        have hq : q = F.branches.root j := by
          apply Fin.ext
          have hqLt := q.isLt
          have hrLt := (F.branches.root j).isLt
          omega
        subst q
        have hadj' : (F.branches.tree j).Adj
            (F.branches.root j) (F.branches.root j) := by
          simpa using hadj
        exact False.elim ((F.branches.tree j).loopless.irrefl _ hadj')
    have hcard : 1 ≤ #(attachedBranchLeaves F j) := by
      simpa using Finset.card_pos.mpr ⟨_, hrootMem⟩
    have hfactor : 1 - 2 * alpha ≤ 1 := by linarith
    calc
      (1 - 2 * alpha) * F.branches.size j = 1 - 2 * alpha := by
        rw [hsizeOne, Nat.cast_one, mul_one]
      _ ≤ 1 := hfactor
      _ ≤ #(attachedBranchLeaves F j) := by exact_mod_cast hcard
  · have hcardTwo : 2 ≤ F.branches.size j := by omega
    have hcardTwo' : 2 ≤ Fintype.card (Fin (F.branches.size j)) := by
      simpa using hcardTwo
    have hunbalanced' : ¬(alpha <
        (#(treeColourClass (F.branches.tree j) (F.branches.isTree j)
          (F.branches.root j) 0) : ℝ) /
            Fintype.card (Fin (F.branches.size j)) ∧
      (#(treeColourClass (F.branches.tree j) (F.branches.isTree j)
          (F.branches.root j) 0) : ℝ) /
            Fintype.card (Fin (F.branches.size j)) < 1 - alpha) := by
      simpa only [Fintype.card_fin] using hunbalanced
    have hfact := many_leaves_of_ratio_not_between_add_one
      (F.branches.tree j) (F.branches.isTree j) (F.branches.root j)
      hcardTwo' alpha halpha0 halphaHalf hunbalanced'
    rw [Fintype.card_fin] at hfact
    have hloss := card_localLeaves_le_card_attached_add_one F j
    have hlossR :
        (#(Erdos547b.leavesIn (F.branches.tree j)
          (Finset.univ : Finset (Fin (F.branches.size j)))) : ℝ) ≤
          #(attachedBranchLeaves F j) + 1 := by
      exact_mod_cast hloss
    have hcombined :
        (1 - 2 * alpha) * F.branches.size j + 1 ≤
          (#(attachedBranchLeaves F j) : ℝ) + 1 :=
      hfact.trans hlossR
    exact (add_le_add_iff_right (1 : ℝ)).mp hcombined

/-- The attached leaves carried by a finite family of branches, as literal
vertices of the reconstructed forest. -/
def attachedBranchLeafVertices {r b : ℕ} (F : OrderedBranchForest r b)
    (s : Finset (Fin b)) : Finset F.Vertex :=
  s.biUnion fun j =>
    (attachedBranchLeaves F j).image fun a =>
      (Sum.inr (⟨j, a⟩ : Σ q, Fin (F.branches.size q)) : F.Vertex)

private theorem attachedBranchLeafVertexFibers_pairwiseDisjoint
    {r b : ℕ} (F : OrderedBranchForest r b) (s : Finset (Fin b)) :
    (↑s : Set (Fin b)).PairwiseDisjoint fun j =>
      (attachedBranchLeaves F j).image fun a =>
        (Sum.inr (⟨j, a⟩ : Σ q, Fin (F.branches.size q)) : F.Vertex) := by
  intro j _ k _ hjk
  change Disjoint
    ((attachedBranchLeaves F j).image fun a =>
      (Sum.inr (⟨j, a⟩ : Σ q, Fin (F.branches.size q)) : F.Vertex))
    ((attachedBranchLeaves F k).image fun a =>
      (Sum.inr (⟨k, a⟩ : Σ q, Fin (F.branches.size q)) : F.Vertex))
  rw [Finset.disjoint_left]
  intro v hvj hvk
  obtain ⟨a, ha, hva⟩ := Finset.mem_image.mp hvj
  obtain ⟨q, hq, hvq⟩ := Finset.mem_image.mp hvk
  have heq :
      (⟨j, a⟩ : Σ z, Fin (F.branches.size z)) = ⟨k, q⟩ :=
    Sum.inr.inj (hva.trans hvq.symm)
  exact hjk (congrArg Sigma.fst heq)

theorem card_attachedBranchLeafVertices
    {r b : ℕ} (F : OrderedBranchForest r b) (s : Finset (Fin b)) :
    #(attachedBranchLeafVertices F s) =
      ∑ j ∈ s, #(attachedBranchLeaves F j) := by
  rw [attachedBranchLeafVertices, Finset.card_biUnion
    (attachedBranchLeafVertexFibers_pairwiseDisjoint F s)]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.card_image_iff.mpr]
  intro a _ q _ haq
  exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj haq)).2

theorem attachedBranchLeafVertices_subset_graphLeaves
    {r b : ℕ} (F : OrderedBranchForest r b) (s : Finset (Fin b)) :
    attachedBranchLeafVertices F s ⊆ Erdos547b.ZhaoClaim68.graphLeaves F.graph := by
  intro v hv
  obtain ⟨j, _, hvj⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hvj
  have hdegree := (mem_attachedBranchLeaves F j a).mp ha
  simpa [Erdos547b.ZhaoClaim68.graphLeaves] using hdegree

/-- Sum the branchwise Fact-6.9 contribution over any unbalanced family. -/
theorem factor_mul_branchMass_le_attachedBranchLeafVertices
    {r b : ℕ} (F : OrderedBranchForest r b) (s : Finset (Fin b))
    (alpha : ℝ) (halpha0 : 0 ≤ alpha) (halphaHalf : alpha ≤ 1 / 2)
    (hunbalanced : ∀ j ∈ s, ¬(alpha <
        (#(treeColourClass (F.branches.tree j) (F.branches.isTree j)
          (F.branches.root j) 0) : ℝ) / F.branches.size j ∧
      (#(treeColourClass (F.branches.tree j) (F.branches.isTree j)
          (F.branches.root j) 0) : ℝ) / F.branches.size j <
        1 - alpha)) :
    (1 - 2 * alpha) * (∑ j ∈ s, F.branches.size j : ℕ) ≤
      #(attachedBranchLeafVertices F s) := by
  calc
    (1 - 2 * alpha) * (∑ j ∈ s, F.branches.size j : ℕ) =
        ∑ j ∈ s, (1 - 2 * alpha) * F.branches.size j := by
      push_cast
      rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ s, (#(attachedBranchLeaves F j) : ℝ) := by
      exact Finset.sum_le_sum fun j hj =>
        factor_mul_size_le_attachedBranchLeaves F j alpha halpha0
          halphaHalf (hunbalanced j hj)
    _ = (#(attachedBranchLeafVertices F s) : ℝ) := by
      rw [card_attachedBranchLeafVertices]
      norm_cast

/-- Consequently the same aggregate lower bound holds for all leaves of the
reconstructed forest. -/
theorem factor_mul_branchMass_le_graphLeaves
    {r b : ℕ} (F : OrderedBranchForest r b) (s : Finset (Fin b))
    (alpha : ℝ) (halpha0 : 0 ≤ alpha) (halphaHalf : alpha ≤ 1 / 2)
    (hunbalanced : ∀ j ∈ s, ¬(alpha <
        (#(treeColourClass (F.branches.tree j) (F.branches.isTree j)
          (F.branches.root j) 0) : ℝ) / F.branches.size j ∧
      (#(treeColourClass (F.branches.tree j) (F.branches.isTree j)
          (F.branches.root j) 0) : ℝ) / F.branches.size j <
        1 - alpha)) :
    (1 - 2 * alpha) * (∑ j ∈ s, F.branches.size j : ℕ) ≤
      #(Erdos547b.ZhaoClaim68.graphLeaves F.graph) := by
  exact (factor_mul_branchMass_le_attachedBranchLeafVertices F s alpha
    halpha0 halphaHalf hunbalanced).trans (by
      exact_mod_cast Finset.card_le_card
        (attachedBranchLeafVertices_subset_graphLeaves F s))

universe v

/-- Graph isomorphisms preserve finite degrees, stated with the locally
chosen finite-neighborhood instances on both graphs. -/
theorem degree_eq_of_graphIso
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {G : SimpleGraph A} {H : SimpleGraph B}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) (x : A) : G.degree x = H.degree (e x) := by
  calc
    G.degree x = Fintype.card (G.neighborSet x) :=
      (G.card_neighborSet_eq_degree x).symm
    _ = Fintype.card (H.neighborSet (e x)) :=
      Fintype.card_congr (e.mapNeighborSet x)
    _ = H.degree (e x) := H.card_neighborSet_eq_degree (e x)

/-- A graph isomorphism restricts to an equivalence of leaf finsets. -/
noncomputable def graphLeavesEquivOfIso
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {G : SimpleGraph A} {H : SimpleGraph B}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) :
    {x // x ∈ Erdos547b.ZhaoClaim68.graphLeaves G} ≃
      {y // y ∈ Erdos547b.ZhaoClaim68.graphLeaves H} where
  toFun x := ⟨e x.1, by
    rw [Erdos547b.ZhaoClaim68.graphLeaves, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← degree_eq_of_graphIso e x.1]
    exact (Finset.mem_filter.mp x.2).2⟩
  invFun y := ⟨e.symm y.1, by
    rw [Erdos547b.ZhaoClaim68.graphLeaves, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← degree_eq_of_graphIso e.symm y.1]
    exact (Finset.mem_filter.mp y.2).2⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  right_inv y := by
    apply Subtype.ext
    exact e.apply_symm_apply y.1

theorem card_graphLeaves_eq_of_iso
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {G : SimpleGraph A} {H : SimpleGraph B}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) :
    #(Erdos547b.ZhaoClaim68.graphLeaves G) =
      #(Erdos547b.ZhaoClaim68.graphLeaves H) := by
  have hcard := Fintype.card_congr (graphLeavesEquivOfIso e)
  simpa only [Fintype.card_coe] using hcard

/-- The reconstructed branch forest is canonically the literal cut forest. -/
noncomputable def branchForestCutIso
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {globalRoot : V} {small : ℕ}
    (P : ZhaoForestPartition T globalRoot small) :
    (branchForest P).graph ≃g P.cutForest :=
  (branchGraphIso P.orderedForest).trans (cutForestGraphIso P).symm

theorem card_graphLeaves_branchForest_eq_cutForest
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {globalRoot : V} {small : ℕ}
    (P : ZhaoForestPartition T globalRoot small) :
    #(Erdos547b.ZhaoClaim68.graphLeaves (branchForest P).graph) =
      #(Erdos547b.ZhaoClaim68.graphLeaves P.cutForest) :=
  card_graphLeaves_eq_of_iso (branchForestCutIso P)

/-- Branchwise Fact 6.9, aggregated and transported to the literal Zhao cut
forest. -/
theorem factor_mul_branchMass_le_cutForestLeaves
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {globalRoot : V} {small : ℕ}
    (P : ZhaoForestPartition T globalRoot small)
    (s : Finset (BranchIndex P))
    (alpha : ℝ) (halpha0 : 0 ≤ alpha) (halphaHalf : alpha ≤ 1 / 2)
    (hunbalanced : ∀ j ∈ s, ¬(alpha < branchRatio P j ∧
      branchRatio P j < 1 - alpha)) :
    (1 - 2 * alpha) * branchMass P s ≤
      #(Erdos547b.ZhaoClaim68.graphLeaves P.cutForest) := by
  have h := factor_mul_branchMass_le_graphLeaves (branchForest P) s alpha
    halpha0 halphaHalf (by
      intro j hj
      simpa only [branchRatio, branchColourClass, treeColourClass] using
        hunbalanced j hj)
  rw [card_graphLeaves_branchForest_eq_cutForest P] at h
  simpa only [branchMass] using h

/-- Every new leaf created by cutting the tree is an endpoint of one of the
recorded cut edges. -/
theorem cutForestLeaves_subset_originalLeaves_union_endpoints
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {globalRoot : V} {small : ℕ}
    (P : ZhaoForestPartition T globalRoot small) :
    Erdos547b.ZhaoClaim68.graphLeaves P.cutForest ⊆
      Erdos547b.ZhaoClaim68.graphLeaves T ∪
        (Erdos547b.ZhaoClaim68.partitionRoots P ∪
          Erdos547b.ZhaoClaim68.partitionParents P) := by
  intro x hx
  by_cases hxT : x ∈ Erdos547b.ZhaoClaim68.graphLeaves T
  · exact Finset.mem_union_left _ hxT
  · apply Finset.mem_union_right
    let cuts := zhaoCutEdges P.roots P.parent
    have hxF : P.cutForest.degree x = 1 :=
      (Finset.mem_filter.mp hx).2
    have hxTne : T.degree x ≠ 1 := by
      simpa [Erdos547b.ZhaoClaim68.graphLeaves] using hxT
    have hle : P.cutForest.degree x ≤ T.degree x :=
      SimpleGraph.degree_le_of_le (G := P.cutForest) (H := T) (v := x)
        (T.deleteEdges_le _)
    have hlt : P.cutForest.degree x < T.degree x := by omega
    have hproper : P.cutForest.neighborFinset x ⊂ T.neighborFinset x := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨?_, ?_⟩
      · intro y hy
        exact (T.mem_neighborFinset x y).mpr
          (SimpleGraph.deleteEdges_adj.mp
            ((P.cutForest.mem_neighborFinset x y).mp hy)).1
      · intro heq
        have hcard := congrArg Finset.card heq
        rw [P.cutForest.card_neighborFinset_eq_degree,
          T.card_neighborFinset_eq_degree] at hcard
        exact (Nat.ne_of_lt hlt) hcard
    obtain ⟨y, hyT, hyF⟩ := Finset.exists_of_ssubset hproper
    have hTadj : T.Adj x y := (T.mem_neighborFinset x y).mp hyT
    have hnotFadj : ¬P.cutForest.Adj x y := by
      simpa using hyF
    have hcut : s(x, y) ∈ cuts := by
      by_contra hnotcut
      exact hnotFadj (SimpleGraph.deleteEdges_adj.mpr ⟨hTadj, hnotcut⟩)
    obtain ⟨j, -, hedge⟩ := Finset.mem_image.mp hcut
    rcases Sym2.eq_iff.mp hedge with hxy | hxy
    · exact Finset.mem_union_left _ <| Finset.mem_image.mpr
        ⟨j.1, Finset.mem_univ _, hxy.1⟩
    · exact Finset.mem_union_right _ <| Finset.mem_image.mpr
        ⟨j, Finset.mem_univ _, hxy.2⟩

/-- Cutting the `numParts - 1` recorded edges creates at most two leaves per
recorded part (the slightly looser `2*numParts` form is convenient for the
eventual arithmetic). -/
theorem card_cutForestLeaves_le_originalLeaves_add_two_mul_numParts
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {globalRoot : V} {small : ℕ}
    (P : ZhaoForestPartition T globalRoot small) :
    #(Erdos547b.ZhaoClaim68.graphLeaves P.cutForest) ≤
      #(Erdos547b.ZhaoClaim68.graphLeaves T) + 2 * P.numParts := by
  have hroots := Erdos547b.ZhaoClaim68.partitionRoots_card P
  have hparents := Erdos547b.ZhaoClaim68.card_partitionParents_le_numParts P
  calc
    #(Erdos547b.ZhaoClaim68.graphLeaves P.cutForest) ≤
        #(Erdos547b.ZhaoClaim68.graphLeaves T ∪
          (Erdos547b.ZhaoClaim68.partitionRoots P ∪
            Erdos547b.ZhaoClaim68.partitionParents P)) :=
      Finset.card_le_card
        (cutForestLeaves_subset_originalLeaves_union_endpoints P)
    _ ≤ #(Erdos547b.ZhaoClaim68.graphLeaves T) +
        #(Erdos547b.ZhaoClaim68.partitionRoots P ∪
          Erdos547b.ZhaoClaim68.partitionParents P) :=
      Finset.card_union_le _ _
    _ ≤ #(Erdos547b.ZhaoClaim68.graphLeaves T) +
        (#(Erdos547b.ZhaoClaim68.partitionRoots P) +
          #(Erdos547b.ZhaoClaim68.partitionParents P)) :=
      Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ ≤ #(Erdos547b.ZhaoClaim68.graphLeaves T) + 2 * P.numParts := by
      rw [hroots]
      omega

/-- The complete Claim-6.10 leaf estimate for any unbalanced branch family. -/
theorem factor_mul_branchMass_sub_cutLoss_le_originalLeaves
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    {globalRoot : V} {small : ℕ}
    (P : ZhaoForestPartition T globalRoot small)
    (s : Finset (BranchIndex P))
    (alpha : ℝ) (halpha0 : 0 ≤ alpha) (halphaHalf : alpha ≤ 1 / 2)
    (hunbalanced : ∀ j ∈ s, ¬(alpha < branchRatio P j ∧
      branchRatio P j < 1 - alpha)) :
    (1 - 2 * alpha) * branchMass P s - 2 * P.numParts ≤
      #(Erdos547b.ZhaoClaim68.graphLeaves T) := by
  have hbranch := factor_mul_branchMass_le_cutForestLeaves P s alpha
    halpha0 halphaHalf hunbalanced
  have hloss := card_cutForestLeaves_le_originalLeaves_add_two_mul_numParts P
  have hlossR :
      (#(Erdos547b.ZhaoClaim68.graphLeaves P.cutForest) : ℝ) ≤
        #(Erdos547b.ZhaoClaim68.graphLeaves T) + 2 * P.numParts := by
    exact_mod_cast hloss
  linarith

end Erdos547b.ZhaoClaim610BranchForestLeaves

#print axioms Erdos547b.ZhaoClaim610BranchForestLeaves.factor_mul_size_le_attachedBranchLeaves
#print axioms Erdos547b.ZhaoClaim610BranchForestLeaves.factor_mul_branchMass_le_graphLeaves
#print axioms Erdos547b.ZhaoClaim610BranchForestLeaves.factor_mul_branchMass_le_cutForestLeaves
#print axioms Erdos547b.ZhaoClaim610BranchForestLeaves.factor_mul_branchMass_sub_cutLoss_le_originalLeaves
