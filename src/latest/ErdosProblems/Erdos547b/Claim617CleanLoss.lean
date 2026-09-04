/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim617BranchCount
import ErdosProblems.Erdos547b.Claim712NaturalSubtree

/-!
# Clean-loss injection for corrected Claim-6.17 branches

A clean size-two branch contributes its root child as a usable middle.  A
dirty branch is charged to the first recorded parent among its middle and
leaf.  Distinct root-child descendant sets are disjoint, so both maps are
injective.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim617CleanLoss

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.RegularPair
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617CutRootPaths
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim68BranchGraphTransport
open SimpleGraphRose547

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

private theorem component_adj_iff
    (P : ZhaoForestPartition T globalRoot small) (i : Fin P.numParts)
    (a b : Fin (P.orderedForest.size i)) :
    P.cutForest.Adj
        (P.fromOrderedForestVertex ⟨i, a⟩)
        (P.fromOrderedForestVertex ⟨i, b⟩) ↔
      (P.orderedForest.tree i).Adj a b := by
  change P.cutForest.Adj (P.componentEquiv i a).1
      (P.componentEquiv i b).1 ↔
    (P.components i).toSimpleGraph.Adj
      (P.componentEquiv i a) (P.componentEquiv i b)
  rw [(P.components i).toSimpleGraph_adj
    (P.componentEquiv i a).2 (P.componentEquiv i b).2]

theorem component_degree_eq
    (P : ZhaoForestPartition T globalRoot small) (i : Fin P.numParts)
    (a : Fin (P.orderedForest.size i)) :
    P.cutForest.degree (P.fromOrderedForestVertex ⟨i, a⟩) =
      ((P.orderedForest.tree i).neighborSet a).ncard := by
  classical
  let x : V := P.fromOrderedForestVertex ⟨i, a⟩
  let : Fintype {b // (P.orderedForest.tree i).Adj a b} := Fintype.ofFinite _
  let : Fintype {y // P.cutForest.Adj x y} := Fintype.ofFinite _
  let e : {b // (P.orderedForest.tree i).Adj a b} ≃
      {y // P.cutForest.Adj x y} :=
    { toFun := fun b => ⟨P.fromOrderedForestVertex ⟨i, b.1⟩,
          (component_adj_iff P i a b.1).mpr b.2⟩
      invFun := fun y => by
        have hxC : x ∈ (P.components i).supp := (P.componentEquiv i a).2
        have hyC : y.1 ∈ (P.components i).supp :=
          (P.components i).mem_supp_of_adj_mem_supp hxC y.2
        let b := (P.componentEquiv i).symm ⟨y.1, hyC⟩
        refine ⟨b, ?_⟩
        apply (component_adj_iff P i a b).mp
        have hb : P.fromOrderedForestVertex ⟨i, b⟩ = y.1 := by
          exact congrArg Subtype.val
            (Equiv.apply_symm_apply (P.componentEquiv i) ⟨y.1, hyC⟩)
        simpa [hb] using y.2
      left_inv := by
        intro b
        apply Subtype.ext
        change (P.componentEquiv i).symm (P.componentEquiv i b.1) = b.1
        exact (P.componentEquiv i).symm_apply_apply b.1
      right_inv := by
        intro y
        apply Subtype.ext
        change (P.componentEquiv i ((P.componentEquiv i).symm
          ⟨y.1, (P.components i).mem_supp_of_adj_mem_supp
            (P.componentEquiv i a).2 y.2⟩)).1 = y.1
        exact congrArg Subtype.val
          (Equiv.apply_symm_apply (P.componentEquiv i)
            ⟨y.1, (P.components i).mem_supp_of_adj_mem_supp
              (P.componentEquiv i a).2 y.2⟩) }
  rw [degree_eq_natCard]
  change Nat.card {y // P.cutForest.Adj x y} =
    Nat.card {b // (P.orderedForest.tree i).Adj a b}
  exact Nat.card_congr e.symm

abbrev TwoBranchIndex (P : ZhaoForestPartition T globalRoot small) :=
  {j // j ∈ sizeTwoBranches P}

private noncomputable def branchRootVertex
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    {z // z ∈ branchSet P.orderedForest j.1} :=
  (branchSetEquiv P.orderedForest j.1)
    ⟨(childKeyEquiv P.orderedForest j.1).1.2,
      self_mem_rootedDescendants _ _ _⟩

private theorem branchSet_card_two
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    Nat.card {z // z ∈ branchSet P.orderedForest j.1} = 2 := by
  exact (mem_sizeTwoBranches P j.1).mp j.2 |>.2

private noncomputable def branchOtherVertex
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    {z // z ∈ branchSet P.orderedForest j.1} := by
  letI : Fintype {z // z ∈ branchSet P.orderedForest j.1} := Fintype.ofFinite _
  have hcard : Fintype.card {z // z ∈ branchSet P.orderedForest j.1} = 2 := by
    rw [Fintype.card_eq_nat_card, branchSet_card_two P j]
  haveI : Nontrivial {z // z ∈ branchSet P.orderedForest j.1} :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact Classical.choose (exists_ne (branchRootVertex P j))

private theorem branchOther_ne_root
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    branchOtherVertex P j ≠ branchRootVertex P j := by
  classical
  let : Fintype {z // z ∈ branchSet P.orderedForest j.1} := Fintype.ofFinite _
  have hcard : Fintype.card {z // z ∈ branchSet P.orderedForest j.1} = 2 := by
    rw [Fintype.card_eq_nat_card, branchSet_card_two P j]
  let : Nontrivial {z // z ∈ branchSet P.orderedForest j.1} :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact Classical.choose_spec (exists_ne (branchRootVertex P j))

private theorem branchVertex_eq_root_or_other
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P)
    (z : {z // z ∈ branchSet P.orderedForest j.1}) :
    z = branchRootVertex P j ∨ z = branchOtherVertex P j := by
  classical
  let : Fintype {z // z ∈ branchSet P.orderedForest j.1} := Fintype.ofFinite _
  have hcard : Fintype.card {z // z ∈ branchSet P.orderedForest j.1} = 2 := by
    rw [Fintype.card_eq_nat_card, branchSet_card_two P j]
  by_cases hz : z = branchRootVertex P j
  · exact Or.inl hz
  · right
    by_contra hzo
    have hthree : 3 ≤ Fintype.card
        {z // z ∈ branchSet P.orderedForest j.1} := by
      calc
        3 = #({z, branchRootVertex P j, branchOtherVertex P j} :
            Finset {z // z ∈ branchSet P.orderedForest j.1}) := by
          symm
          exact Finset.card_triple_eq_three_iff.mpr
            ⟨hz, hzo, (branchOther_ne_root P j).symm⟩
        _ ≤ #Finset.univ := Finset.card_le_card (Finset.subset_univ _)
        _ = _ := Finset.card_univ
    omega

private noncomputable def branchOtherLocal
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    {a // a ∈ rootedDescendants
      (P.orderedForest.tree (childKeyEquiv P.orderedForest j.1).1.1)
      (P.orderedForest.root (childKeyEquiv P.orderedForest j.1).1.1)
      (childKeyEquiv P.orderedForest j.1).1.2} :=
  (branchSetEquiv P.orderedForest j.1).symm (branchOtherVertex P j)

private noncomputable def branchOtherCoordinate
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    Fin (P.orderedForest.size
      (childKeyEquiv P.orderedForest j.1).1.1) :=
  (branchOtherLocal P j).1

private theorem branchOtherCoordinate_mem
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    branchOtherCoordinate P j ∈ rootedDescendants
      (P.orderedForest.tree (childKeyEquiv P.orderedForest j.1).1.1)
      (P.orderedForest.root (childKeyEquiv P.orderedForest j.1).1.1)
      (childKeyEquiv P.orderedForest j.1).1.2 :=
  (branchOtherLocal P j).2

private theorem branchOtherVertex_eq
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    (branchOtherVertex P j).1 =
      ⟨(childKeyEquiv P.orderedForest j.1).1.1,
        branchOtherCoordinate P j⟩ := by
  have h := Equiv.apply_symm_apply
    (branchSetEquiv P.orderedForest j.1) (branchOtherVertex P j)
  exact (congrArg Subtype.val h).symm

private theorem branchRootVertex_eq
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    (branchRootVertex P j).1 = (childKeyEquiv P.orderedForest j.1).1 := rfl

private theorem branch_root_other_adj
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    P.orderedForest.graph.Adj
      (branchRootVertex P j).1 (branchOtherVertex P j).1 := by
  classical
  let H := P.orderedForest.graph.induce (branchSet P.orderedForest j.1)
  let : Fintype {z // z ∈ branchSet P.orderedForest j.1} := Fintype.ofFinite _
  have hcard : Fintype.card {z // z ∈ branchSet P.orderedForest j.1} = 2 := by
    rw [Fintype.card_eq_nat_card, branchSet_card_two P j]
  have : Nontrivial {z // z ∈ branchSet P.orderedForest j.1} :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have htree : H.IsTree := by
    let e : branchLocalGraph P.orderedForest j.1 ≃g H :=
      { toEquiv := branchSetEquiv P.orderedForest j.1
        map_rel_iff' := by
          intro x y
          change P.orderedForest.graph.Adj
            ⟨(childKeyEquiv P.orderedForest j.1).1.1, x.1⟩
            ⟨(childKeyEquiv P.orderedForest j.1).1.1, y.1⟩ ↔ _
          rw [orderedGraph_adj_mk]
          constructor
          · rintro ⟨h, hxy⟩
            exact hxy
          · intro hxy
            exact ⟨rfl, hxy⟩ }
    exact e.isTree_iff.mp (branchInduce_isTree P.orderedForest j.1)
  have hpos : 0 < H.degree (branchRootVertex P j) :=
    htree.preconnected.degree_pos_of_nontrivial _
  obtain ⟨z, hz⟩ := (H.degree_pos_iff_exists_adj _).mp hpos
  rcases branchVertex_eq_root_or_other P j z with hzroot | hzother
  · subst z
    exact False.elim (@irrefl _ H.Adj H.loopless _ hz)
  · subst z
    exact hz

private theorem local_root_other_adj
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    (P.orderedForest.tree (childKeyEquiv P.orderedForest j.1).1.1).Adj
      (childKeyEquiv P.orderedForest j.1).1.2
      (branchOtherCoordinate P j) := by
  have h := branch_root_other_adj P j
  rw [branchRootVertex_eq P j, branchOtherVertex_eq P j,
    OrderedRootedForest.graph_adj] at h
  obtain ⟨i, a, b, ha, hb, hab⟩ := h
  have hi := (Sigma.mk.inj_iff.mp ha).1
  subst i
  have ha' : a = (childKeyEquiv P.orderedForest j.1).1.2 :=
    (eq_of_heq (Sigma.mk.inj_iff.mp ha).2).symm
  have hb' : b = branchOtherCoordinate P j :=
    (eq_of_heq (Sigma.mk.inj_iff.mp hb).2).symm
  simpa [ha', hb'] using hab

private theorem local_root_neighborSet
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    (P.orderedForest.tree (childKeyEquiv P.orderedForest j.1).1.1).neighborSet
        (childKeyEquiv P.orderedForest j.1).1.2 =
      {(P.orderedForest.root (childKeyEquiv P.orderedForest j.1).1.1),
        branchOtherCoordinate P j} := by
  let F := P.orderedForest
  let i := (childKeyEquiv F j.1).1.1
  let c := (childKeyEquiv F j.1).1.2
  let y := branchOtherCoordinate P j
  apply Set.Subset.antisymm
  · intro z hz
    change (F.tree i).Adj c z at hz
    by_cases hzroot : z = F.root i
    · exact Set.mem_insert_iff.mpr (Or.inl hzroot)
    · have hcDist : (F.tree i).dist (F.root i) c = 1 :=
        (F.tree i).dist_eq_one_iff_adj.mpr (childKeyEquiv F j.1).2
      have hzDist : (F.tree i).dist (F.root i) z =
          (F.tree i).dist (F.root i) c + 1 := by
        rcases (F.isTree i).dist_eq_dist_add_one_of_adj (F.root i) hz with h | h
        · have hz0 : (F.tree i).dist (F.root i) z = 0 := by omega
          exact False.elim (hzroot ((F.isTree i).connected.dist_eq_zero_iff.mp hz0).symm)
        · exact h
      have hzDesc : z ∈ rootedDescendants (F.tree i) (F.root i) c := by
        rw [mem_rootedDescendants]
        have hcz : (F.tree i).dist c z = 1 :=
          (F.tree i).dist_eq_one_iff_adj.mpr hz
        omega
      let zs : {z // z ∈ branchSet F j.1} :=
        ⟨⟨i, z⟩, ⟨rfl, ⟨rfl, hzDesc⟩⟩⟩
      rcases branchVertex_eq_root_or_other P j zs with hroot | hother
      · have : z = c := eq_of_heq
          (Sigma.mk.inj_iff.mp (congrArg Subtype.val hroot)).2
        exact False.elim (@irrefl _ (F.tree i).Adj (F.tree i).loopless _ (this ▸ hz))
      · have hsigma := congrArg Subtype.val hother
        rw [branchOtherVertex_eq P j] at hsigma
        exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr
          (eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2)))
  · intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hy
    · exact (childKeyEquiv F j.1).2.symm
    · rw [Set.mem_singleton_iff] at hy
      subst z
      exact local_root_other_adj P j

private theorem local_other_neighborSet
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    (P.orderedForest.tree (childKeyEquiv P.orderedForest j.1).1.1).neighborSet
        (branchOtherCoordinate P j) =
      {(childKeyEquiv P.orderedForest j.1).1.2} := by
  let F := P.orderedForest
  let i := (childKeyEquiv F j.1).1.1
  let c := (childKeyEquiv F j.1).1.2
  let y := branchOtherCoordinate P j
  apply Set.Subset.antisymm
  · intro z hz
    have hyc : y ≠ c := by
      intro h
      apply branchOther_ne_root P j
      apply Subtype.ext
      rw [branchOtherVertex_eq P j, branchRootVertex_eq P j]
      exact Sigma.ext rfl (by simpa [y, c] using h)
    have hzDesc := adj_mem_rootedDescendants_of_mem_of_ne (F.isTree i)
      (branchOtherCoordinate_mem P j) hyc hz
    let zs : {z // z ∈ branchSet F j.1} :=
      ⟨⟨i, z⟩, ⟨rfl, ⟨rfl, hzDesc⟩⟩⟩
    rcases branchVertex_eq_root_or_other P j zs with hroot | hother
    · have hsigma := congrArg Subtype.val hroot
      rw [branchRootVertex_eq P j] at hsigma
      exact Set.mem_singleton_iff.mpr
        (eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2)
    · have hsigma := congrArg Subtype.val hother
      rw [branchOtherVertex_eq P j] at hsigma
      have hzy : z = y := eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2
      exact False.elim (@irrefl _ (F.tree i).Adj (F.tree i).loopless _ (hzy ▸ hz))
  · intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact (local_root_other_adj P j).symm

private noncomputable def branchMiddle
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) : V :=
  P.fromOrderedForestVertex (branchRootVertex P j).1

private noncomputable def branchLeaf
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) : V :=
  P.fromOrderedForestVertex (branchOtherVertex P j).1

private theorem branchMiddle_degree
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    P.cutForest.degree (branchMiddle P j) = 2 := by
  have hne : P.orderedForest.root (childKeyEquiv P.orderedForest j.1).1.1 ≠
      branchOtherCoordinate P j := by
    intro h
    exact root_not_mem_rootedDescendants_child
      (childKey_isChild P.orderedForest j.1)
      (h ▸ branchOtherCoordinate_mem P j)
  rw [branchMiddle, branchRootVertex_eq P j, component_degree_eq,
    local_root_neighborSet P j, Set.ncard_pair hne]

private theorem branchLeaf_degree
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    P.cutForest.degree (branchLeaf P j) = 1 := by
  rw [branchLeaf, branchOtherVertex_eq P j, component_degree_eq,
    local_other_neighborSet P j, Set.ncard_singleton]

private theorem branchMiddle_not_root
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    branchMiddle P j ∉ partitionRoots P := by
  intro h
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp h
  have hfrom : P.fromOrderedForestVertex (branchRootVertex P j).1 =
      P.fromOrderedForestVertex ⟨k, P.orderedForest.root k⟩ := by
    rw [← Erdos547b.ZhaoLemma614Full.toOrderedForestVertex_root P k,
      P.from_toOrderedForestVertex]
    exact hk.symm
  have hsigma := Erdos547b.ZhaoLemma614Full.fromOrderedForestVertex_injective P hfrom
  have hmem := (branchRootVertex P j).2
  rw [hsigma] at hmem
  exact anyRoot_not_mem_branchSet P.orderedForest k j.1 hmem

private theorem branchLeaf_not_root
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    branchLeaf P j ∉ partitionRoots P := by
  intro h
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp h
  have hfrom : P.fromOrderedForestVertex (branchOtherVertex P j).1 =
      P.fromOrderedForestVertex ⟨k, P.orderedForest.root k⟩ := by
    rw [← Erdos547b.ZhaoLemma614Full.toOrderedForestVertex_root P k,
      P.from_toOrderedForestVertex]
    exact hk.symm
  have hsigma := Erdos547b.ZhaoLemma614Full.fromOrderedForestVertex_injective P hfrom
  have hmem := (branchOtherVertex P j).2
  rw [hsigma] at hmem
  exact anyRoot_not_mem_branchSet P.orderedForest k j.1 hmem

private theorem branchRoot_middle_adj
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    P.cutForest.Adj
      (P.roots (childKeyEquiv P.orderedForest j.1).1.1)
      (branchMiddle P j) := by
  rw [branchMiddle, branchRootVertex_eq P j,
    ← P.from_toOrderedForestVertex (P.roots _),
    Erdos547b.ZhaoLemma614Full.toOrderedForestVertex_root,
    component_adj_iff]
  exact (childKeyEquiv P.orderedForest j.1).2

private theorem branch_middle_leaf_adj
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    P.cutForest.Adj (branchMiddle P j) (branchLeaf P j) := by
  rw [branchMiddle, branchLeaf, branchRootVertex_eq P j,
    branchOtherVertex_eq P j, component_adj_iff]
  exact local_root_other_adj P j

private theorem branchRoot_ne_leaf
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    P.roots (childKeyEquiv P.orderedForest j.1).1.1 ≠ branchLeaf P j := by
  intro h
  apply branchLeaf_not_root P j
  rw [← h]
  exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

def IsClean (P : ZhaoForestPartition T globalRoot small)
    (j : TwoBranchIndex P) : Prop :=
  branchMiddle P j ∉ partitionParents P ∧
    branchLeaf P j ∉ partitionParents P

instance (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    Decidable (IsClean P j) := Classical.propDecidable _

def cleanBranches (P : ZhaoForestPartition T globalRoot small) :
    Finset (TwoBranchIndex P) := Finset.univ.filter (IsClean P)

@[simp] theorem mem_cleanBranches
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    j ∈ cleanBranches P ↔ IsClean P j := by simp [cleanBranches]

private theorem clean_branch_isMiddle
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P)
    (hj : IsClean P j) : IsCutRootTwoPathMiddle P (branchMiddle P j) := by
  refine ⟨branchMiddle_not_root P j, hj.1, branchMiddle_degree P j,
    (childKeyEquiv P.orderedForest j.1).1.1, ?_⟩
  exact ⟨branchLeaf P j, branchLeaf_not_root P j, hj.2,
    branchRoot_ne_leaf P j, branchRoot_middle_adj P j,
    branch_middle_leaf_adj P j, branchLeaf_degree P j⟩

noncomputable def cleanMiddleMap (P : ZhaoForestPartition T globalRoot small) :
    {j // j ∈ cleanBranches P} → middles P :=
  fun j => ⟨branchMiddle P j.1,
    mem_middles P _ |>.mpr (clean_branch_isMiddle P j.1
      ((mem_cleanBranches P j.1).mp j.2))⟩

theorem cleanMiddleMap_injective
    (P : ZhaoForestPartition T globalRoot small) :
    Function.Injective (cleanMiddleMap P) := by
  intro j k hjk
  have hamb : branchMiddle P j.1 = branchMiddle P k.1 :=
    congrArg Subtype.val hjk
  have hsigma := Erdos547b.ZhaoLemma614Full.fromOrderedForestVertex_injective P hamb
  have hkeyVal : (childKeyEquiv P.orderedForest j.1.1).1 =
      (childKeyEquiv P.orderedForest k.1.1).1 := by
    simpa [branchMiddle, branchRootVertex_eq] using hsigma
  have hkey : childKeyEquiv P.orderedForest j.1.1 =
      childKeyEquiv P.orderedForest k.1.1 := Subtype.ext hkeyVal
  have hidx : j.1.1 = k.1.1 := (childKeyEquiv P.orderedForest).injective hkey
  exact Subtype.ext (Subtype.ext hidx)

def dirtyBranches (P : ZhaoForestPartition T globalRoot small) :
    Finset (TwoBranchIndex P) := Finset.univ \ cleanBranches P

@[simp] theorem mem_dirtyBranches
    (P : ZhaoForestPartition T globalRoot small) (j : TwoBranchIndex P) :
    j ∈ dirtyBranches P ↔ ¬ IsClean P j := by simp [dirtyBranches]

private noncomputable def dirtyForestVertex
    (P : ZhaoForestPartition T globalRoot small)
    (j : {j // j ∈ dirtyBranches P}) :
    {z // z ∈ branchSet P.orderedForest j.1.1} :=
  if branchMiddle P j.1 ∈ partitionParents P then
    branchRootVertex P j.1 else branchOtherVertex P j.1

private theorem dirtyForestVertex_parent
    (P : ZhaoForestPartition T globalRoot small)
    (j : {j // j ∈ dirtyBranches P}) :
    P.fromOrderedForestVertex (dirtyForestVertex P j).1 ∈ partitionParents P := by
  have hdirty : ¬ IsClean P j.1 := (mem_dirtyBranches P j.1).mp j.2
  rw [dirtyForestVertex]
  split_ifs with hm
  · simpa [branchMiddle] using hm
  · have hl : branchLeaf P j.1 ∈ partitionParents P := by
      by_contra hleaf
      exact hdirty ⟨hm, hleaf⟩
    simpa [branchLeaf] using hl

noncomputable def dirtyParentMap (P : ZhaoForestPartition T globalRoot small) :
    {j // j ∈ dirtyBranches P} → {x // x ∈ partitionParents P} :=
  fun j => ⟨P.fromOrderedForestVertex (dirtyForestVertex P j).1,
    dirtyForestVertex_parent P j⟩

theorem dirtyParentMap_injective
    (P : ZhaoForestPartition T globalRoot small) :
    Function.Injective (dirtyParentMap P) := by
  intro j k hjk
  have hamb : P.fromOrderedForestVertex (dirtyForestVertex P j).1 =
      P.fromOrderedForestVertex (dirtyForestVertex P k).1 :=
    congrArg Subtype.val hjk
  have hsigma := Erdos547b.ZhaoLemma614Full.fromOrderedForestVertex_injective P hamb
  have hidx : j.1.1 = k.1.1 := by
    by_contra hne
    have hmemk : (dirtyForestVertex P j).1 ∈ branchSet P.orderedForest k.1.1 := by
      rw [hsigma]
      exact (dirtyForestVertex P k).2
    exact (Set.disjoint_left.mp (branchSet_disjoint P.orderedForest hne))
      (dirtyForestVertex P j).2 hmemk
  exact Subtype.ext (Subtype.ext hidx)

theorem sizeTwoBranches_card_le_middles_add_parents
    (P : ZhaoForestPartition T globalRoot small) :
    (sizeTwoBranches P).card ≤
      (middles P).card + (partitionParents P).card := by
  have hclean : (cleanBranches P).card ≤ (middles P).card := by
    rw [← Fintype.card_coe, ← Fintype.card_coe]
    exact Fintype.card_le_of_injective (cleanMiddleMap P)
      (cleanMiddleMap_injective P)
  have hdirty : (dirtyBranches P).card ≤ (partitionParents P).card := by
    rw [← Fintype.card_coe, ← Fintype.card_coe]
    exact Fintype.card_le_of_injective (dirtyParentMap P)
      (dirtyParentMap_injective P)
  have hsplit : (dirtyBranches P).card + (cleanBranches P).card =
      (sizeTwoBranches P).card := by
    have h := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (cleanBranches P))
    simpa [dirtyBranches] using h
  omega

/-- Counting clean branches keeps the major-half ownership information. -/
theorem sizeTwoBranches_card_le_clean_add_parents
    (P : ZhaoForestPartition T globalRoot small) :
    (sizeTwoBranches P).card ≤
      (cleanBranches P).card + (partitionParents P).card := by
  have hdirty : (dirtyBranches P).card ≤ (partitionParents P).card := by
    rw [← Fintype.card_coe, ← Fintype.card_coe]
    exact Fintype.card_le_of_injective (dirtyParentMap P) (dirtyParentMap_injective P)
  have hsplit : (dirtyBranches P).card + (cleanBranches P).card =
      (sizeTwoBranches P).card := by
    simpa [dirtyBranches] using Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (cleanBranches P))
  omega

def cleanRootIndex (P : ZhaoForestPartition T globalRoot small)
    (j : {j // j ∈ cleanBranches P}) : Fin P.numParts :=
  (childKeyEquiv P.orderedForest j.1.1).1.1

/-- The entire family of clean major-half branches, with literal source
vertices and attachment roots, before selecting a rounded subfamily. -/
noncomputable def cleanPaths (P : ZhaoForestPartition T globalRoot small) :
    Erdos547b.ZhaoClaim617RootPaths.RootTwoPathSystem T
      {j // j ∈ cleanBranches P} where
  parent j := P.roots (cleanRootIndex P j)
  middle j := branchMiddle P j.1
  leaf j := branchLeaf P j.1
  middle_injective := by
    intro j k h
    apply cleanMiddleMap_injective P
    exact Subtype.ext h
  leaf_injective := by
    intro j k h
    have hsigma := Erdos547b.ZhaoLemma614Full.fromOrderedForestVertex_injective P h
    have hjk : j.1.1 = k.1.1 := by
      by_contra hne
      have hmem : (branchOtherVertex P j.1).1 ∈ branchSet P.orderedForest k.1.1 := by
        rw [hsigma]
        exact (branchOtherVertex P k.1).2
      exact Set.disjoint_left.mp (branchSet_disjoint P.orderedForest hne)
        (branchOtherVertex P j.1).2 hmem
    exact Subtype.ext (Subtype.ext hjk)
  middle_ne_leaf := by
    intro j k h
    have hm := branchMiddle_degree P j.1
    rw [h, branchLeaf_degree P k.1] at hm
    omega
  parent_ne_middle := by
    intro j k h
    apply branchMiddle_not_root P k.1
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, h⟩
  parent_ne_leaf := by
    intro j k h
    apply branchLeaf_not_root P k.1
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, h⟩
  parent_middle_adj j := (SimpleGraph.deleteEdges_adj.mp (branchRoot_middle_adj P j.1)).1
  middle_leaf_adj j := (SimpleGraph.deleteEdges_adj.mp (branch_middle_leaf_adj P j.1)).1
  middle_neighbors := by
    intro j x hx
    have hclean := (mem_cleanBranches P j.1).mp j.2
    have hcut := cutGraph_adj_of_not_root_not_parent P
      (branchMiddle_not_root P j.1) hclean.1 hx
    have hpair : P.cutForest.neighborFinset (branchMiddle P j.1) =
        {P.roots (cleanRootIndex P j), branchLeaf P j.1} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact (P.cutForest.mem_neighborFinset _ _).mpr (branchRoot_middle_adj P j.1).symm
        · exact (P.cutForest.mem_neighborFinset _ _).mpr (branch_middle_leaf_adj P j.1)
      · rw [P.cutForest.card_neighborFinset_eq_degree, branchMiddle_degree]
        change 2 ≤ #({P.roots (childKeyEquiv P.orderedForest j.1.1).1.1,
          branchLeaf P j.1} : Finset V)
        rw [Finset.card_pair (branchRoot_ne_leaf P j.1)]
    have hmem := (P.cutForest.mem_neighborFinset _ _).mpr hcut
    simpa only [hpair, Finset.mem_insert, Finset.mem_singleton] using hmem
  leaf_neighbors := by
    intro j x hx
    have hclean := (mem_cleanBranches P j.1).mp j.2
    have hcut := cutGraph_adj_of_not_root_not_parent P
      (branchLeaf_not_root P j.1) hclean.2 hx
    obtain ⟨y, _, hy⟩ := (P.cutForest.degree_eq_one_iff_existsUnique_adj).mp
      (branchLeaf_degree P j.1)
    exact (hy x hcut).trans (hy _ (branch_middle_leaf_adj P j.1).symm).symm

theorem cleanPaths_parent (P : ZhaoForestPartition T globalRoot small)
    (j : {j // j ∈ cleanBranches P}) :
    (cleanPaths P).parent j = P.roots (cleanRootIndex P j) := rfl

theorem cleanPaths_parent_parity (P : ZhaoForestPartition T globalRoot small)
    (j : {j // j ∈ cleanBranches P}) :
    T.dist globalRoot ((cleanPaths P).parent j) % 2 =
      (Erdos547b.ZhaoClaim68ParityHalf.majorParity P).val := by
  exact (Finset.mem_filter.mp ((mem_sizeTwoBranches P j.1.1).mp j.1.2).1).2

theorem cleanPaths_middle_not_root (P : ZhaoForestPartition T globalRoot small)
    (j : {j // j ∈ cleanBranches P}) :
    (cleanPaths P).middle j ∉ partitionRoots P := branchMiddle_not_root P j.1

theorem cleanPaths_leaf_not_root (P : ZhaoForestPartition T globalRoot small)
    (j : {j // j ∈ cleanBranches P}) :
    (cleanPaths P).leaf j ∉ partitionRoots P := branchLeaf_not_root P j.1

theorem cleanPaths_middle_not_parent (P : ZhaoForestPartition T globalRoot small)
    (j : {j // j ∈ cleanBranches P}) :
    (cleanPaths P).middle j ∉ partitionParents P := ((mem_cleanBranches P j.1).mp j.2).1

theorem cleanPaths_leaf_not_parent (P : ZhaoForestPartition T globalRoot small)
    (j : {j // j ∈ cleanBranches P}) :
    (cleanPaths P).leaf j ∉ partitionParents P := ((mem_cleanBranches P j.1).mp j.2).2

/-- A clean branch is exactly its two recorded nonroot vertices. -/
theorem cleanPaths_branchSet_iff (P : ZhaoForestPartition T globalRoot small)
    (e : {j // j ∈ cleanBranches P}) (z : ForestVertex P.orderedForest) :
    z ∈ branchSet P.orderedForest e.1.1 ↔
      P.fromOrderedForestVertex z = (cleanPaths P).middle e ∨
      P.fromOrderedForestVertex z = (cleanPaths P).leaf e := by
  constructor
  · intro hz
    rcases branchVertex_eq_root_or_other P e.1 ⟨z, hz⟩ with h | h
    · exact Or.inl (congrArg P.fromOrderedForestVertex (congrArg Subtype.val h))
    · exact Or.inr (congrArg P.fromOrderedForestVertex (congrArg Subtype.val h))
  · rintro (h | h)
    · have hz : z = (branchRootVertex P e.1).1 :=
        Erdos547b.ZhaoLemma614Full.fromOrderedForestVertex_injective P h
      rw [hz]
      exact (branchRootVertex P e.1).2
    · have hz : z = (branchOtherVertex P e.1).1 :=
        Erdos547b.ZhaoLemma614Full.fromOrderedForestVertex_injective P h
      rw [hz]
      exact (branchOtherVertex P e.1).2

end Erdos547b.ZhaoClaim617CleanLoss

#print axioms Erdos547b.ZhaoClaim617CleanLoss.sizeTwoBranches_card_le_middles_add_parents
#print axioms Erdos547b.ZhaoClaim617CleanLoss.sizeTwoBranches_card_le_clean_add_parents
#print axioms Erdos547b.ZhaoClaim617CleanLoss.cleanPaths
#print axioms Erdos547b.ZhaoClaim617CleanLoss.cleanPaths_parent_parity
#print axioms Erdos547b.ZhaoClaim617CleanLoss.cleanPaths_branchSet_iff
