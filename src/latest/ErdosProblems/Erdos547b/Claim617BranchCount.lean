/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim68BranchAdapter
import ErdosProblems.Erdos547b.Claim68BranchGraphTransport
import ErdosProblems.Erdos547b.Claim68ParityHalf
import ErdosProblems.Erdos547b.Claim617CutRootPaths

/-!
# Corrected branch mass count for Zhao Claim 6.17

The selected half is a union of whole cut components.  Size-one branches are
the Level-one leaves, size-two branches are the reserved two-paths, and
branches of size at least three form the Claim-6.16 remainder.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim617BranchCount

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.RegularPair
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim68BranchGraphTransport
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoClaim617CutRootPaths

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

noncomputable local instance finiteGraphLocallyFinite
    {W : Type*} [Finite W] (G : SimpleGraph W) : G.LocallyFinite :=
  fun _ ↦ Fintype.ofFinite _

abbrev branchForest (P : ZhaoForestPartition T globalRoot small) :=
  toOrderedBranchForest P.orderedForest

theorem component_adj_iff
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

/-- A reconstructed Level-one vertex is a leaf precisely when its whole
root-deleted branch consists of that vertex. -/
theorem branchRoot_degree_eq_one_iff {r b : ℕ}
    (F : OrderedBranchForest r b) (j : Fin b) :
    F.graph.degree
        (Sum.inr (⟨j, F.branches.root j⟩ :
          Σ q, Fin (F.branches.size q))) = 1 ↔
      F.branches.size j = 1 := by
  classical
  constructor
  · intro hdegree
    have hpos : 0 < F.branches.size j :=
      Nat.zero_lt_of_lt (F.branches.root j).isLt
    by_contra hne
    have htwo : 2 ≤ F.branches.size j := by omega
    letI : Nontrivial (Fin (F.branches.size j)) :=
      Fin.nontrivial_iff_two_le.mpr htwo
    have hrootPos : 0 <
        (F.branches.tree j).degree (F.branches.root j) :=
      (F.branches.isTree j).preconnected.degree_pos_of_nontrivial _
    obtain ⟨a, ha⟩ :=
      ((F.branches.tree j).degree_pos_iff_exists_adj _).mp hrootPos
    let v : F.Vertex := Sum.inr ⟨j, F.branches.root j⟩
    let u : F.Vertex := Sum.inl (F.owner j)
    let w : F.Vertex := Sum.inr ⟨j, a⟩
    have huv : F.graph.Adj v u := ⟨rfl, rfl⟩
    have hvw : F.graph.Adj v w := ⟨rfl, ha⟩
    have huw : u ≠ w := by simp [u, w]
    have hpair : ({u, w} : Finset F.Vertex) ⊆ F.graph.neighborFinset v := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (F.graph.mem_neighborFinset _ _).mpr huv
      · exact (F.graph.mem_neighborFinset _ _).mpr hvw
    have hdegTwo : 2 ≤ F.graph.degree v := by
      calc
        2 = #({u, w} : Finset F.Vertex) := by simp [huw]
        _ ≤ #(F.graph.neighborFinset v) := Finset.card_le_card hpair
        _ = F.graph.degree v := F.graph.card_neighborFinset_eq_degree v
    change F.graph.degree v = 1 at hdegree
    omega
  · intro hsize
    rw [← F.graph.card_neighborFinset_eq_degree]
    have hneighbors :
        F.graph.neighborFinset
            (Sum.inr (⟨j, F.branches.root j⟩ :
              Σ q, Fin (F.branches.size q))) =
          {Sum.inl (F.owner j)} := by
      ext x
      rw [F.graph.mem_neighborFinset]
      rcases x with i | z
      · simp only [OrderedBranchForest.graph_adj_branch_root,
          Finset.mem_singleton]
        constructor
        · rintro ⟨hi, -⟩
          exact congrArg Sum.inl hi.symm
        · intro hi
          have hi' : i = F.owner j := Sum.inl.inj hi
          subst i
          exact ⟨rfl, trivial⟩
      · simp only [OrderedBranchForest.graph_adj_branch_branch,
          Finset.mem_singleton, Sum.inr.injEq, reduceCtorEq, iff_false]
        rintro ⟨hidx, hadj⟩
        rcases z with ⟨q, a⟩
        dsimp only at hidx
        subst q
        have haVal : a.val = (F.branches.root j).val := by
          have haLt := a.isLt
          have hrLt := (F.branches.root j).isLt
          omega
        have haEq : a = F.branches.root j := Fin.eq_of_val_eq haVal
        subst a
        exact (F.branches.tree j).loopless.irrefl _ hadj
    rw [hneighbors]
    simp

theorem degree_eq_natCard
    {A : Type*} {G : SimpleGraph A} (x : A)
    [Fintype (G.neighborSet x)] :
    G.degree x = Nat.card (G.neighborSet x) := by
  calc
    G.degree x = Fintype.card (G.neighborSet x) :=
      (G.card_neighborSet_eq_degree x).symm
    _ = Nat.card (G.neighborSet x) := Nat.card_eq_fintype_card.symm

theorem degree_eq_of_iso
    {A B : Type*} [Finite A] [Finite B]
    {G : SimpleGraph A} {H : SimpleGraph B}
    (e : G ≃g H) (x : A) : G.degree x = H.degree (e x) := by
  calc
    G.degree x = Nat.card (G.neighborSet x) := degree_eq_natCard x
    _ = Nat.card (H.neighborSet (e x)) := Nat.card_congr (e.mapNeighborSet x)
    _ = H.degree (e x) := (degree_eq_natCard (e x)).symm

/-- Canonical cut-forest coordinates away from component roots are exactly
the literal non-root vertices of the Zhao partition. -/
noncomputable def partitionNonrootCoordinateEquiv
    (P : ZhaoForestPartition T globalRoot small) :
    NonRootCoordinate P.orderedForest ≃ {x // x ∈ partitionNonroots P} := by
  let f : NonRootCoordinate P.orderedForest →
      {x // x ∈ partitionNonroots P} := fun z ↦
    ⟨P.fromOrderedForestVertex z.1, by
      rw [partitionNonroots, Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hroot
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hroot
      have hfrom :
          P.fromOrderedForestVertex
              ⟨i, P.orderedForest.root i⟩ =
            P.fromOrderedForestVertex z.1 := by
        rw [← Erdos547b.ZhaoLemma614Full.toOrderedForestVertex_root P i,
          P.from_toOrderedForestVertex]
        exact hi
      have hsigma :=
        Erdos547b.ZhaoLemma614Full.fromOrderedForestVertex_injective P hfrom
      let IsRoot : ForestVertex P.orderedForest → Prop := fun q ↦
        q.2 = P.orderedForest.root q.1
      have hi : IsRoot ⟨i, P.orderedForest.root i⟩ := rfl
      exact z.2 (Eq.mp (congrArg IsRoot hsigma) hi)⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply Erdos547b.ZhaoLemma614Full.fromOrderedForestVertex_injective P
    exact congrArg Subtype.val hxy
  · intro x
    have hcoord :
        (P.toOrderedForestVertex x.1).2 ≠
          P.orderedForest.root (P.toOrderedForestVertex x.1).1 := by
      intro hroot
      have hxroot : x.1 ∈ partitionRoots P := by
        apply Finset.mem_image.mpr
        let i := (P.toOrderedForestVertex x.1).1
        refine ⟨i, Finset.mem_univ _, ?_⟩
        have hxCoord : P.toOrderedForestVertex x.1 =
            ⟨i, P.orderedForest.root i⟩ :=
          Sigma.ext rfl (heq_of_eq hroot)
        calc
          P.roots i = P.fromOrderedForestVertex
              ⟨i, P.orderedForest.root i⟩ := by
                rw [← P.from_toOrderedForestVertex (P.roots i),
                  Erdos547b.ZhaoLemma614Full.toOrderedForestVertex_root]
          _ = P.fromOrderedForestVertex (P.toOrderedForestVertex x.1) := by
                rw [hxCoord]
          _ = x.1 := P.from_toOrderedForestVertex x.1
      exact (Finset.mem_sdiff.mp x.2).2 hxroot
    refine ⟨⟨P.toOrderedForestVertex x.1, hcoord⟩, ?_⟩
    apply Subtype.ext
    exact P.from_toOrderedForestVertex x.1

/-- Every non-root tree vertex occurs in exactly one root-deleted branch. -/
noncomputable def partitionBranchEquivNonroots
    (P : ZhaoForestPartition T globalRoot small) :
    (Σ j, Fin ((branchForest P).branches.size j)) ≃
      {x // x ∈ partitionNonroots P} :=
  (branchCoordinatesEquivNonroots P.orderedForest).trans
    (partitionNonrootCoordinateEquiv P)

@[simp] theorem partitionBranchEquivNonroots_apply_val
    (P : ZhaoForestPartition T globalRoot small)
    (z : Σ j, Fin ((branchForest P).branches.size j)) :
    (partitionBranchEquivNonroots P z).1 =
      P.fromOrderedForestVertex
        (flattenBranch P.orderedForest (Sum.inr z)) := by
  rfl

@[simp] theorem toOrderedForestVertex_fromOrderedForestVertex
    (P : ZhaoForestPartition T globalRoot small)
    (z : Σ i, Fin (P.orderedForest.size i)) :
    P.toOrderedForestVertex (P.fromOrderedForestVertex z) = z := by
  apply Erdos547b.ZhaoLemma614Full.fromOrderedForestVertex_injective P
  rw [P.from_toOrderedForestVertex]

/-- The canonical component numbering is a graph isomorphism, not merely
the embedding exposed by `cutForestCopy`. -/
noncomputable def cutForestGraphIso
    (P : ZhaoForestPartition T globalRoot small) :
    P.cutForest ≃g P.orderedForest.graph where
  toEquiv :=
    { toFun := P.toOrderedForestVertex
      invFun := P.fromOrderedForestVertex
      left_inv := P.from_toOrderedForestVertex
      right_inv := toOrderedForestVertex_fromOrderedForestVertex P }
  map_rel_iff' := by
    intro x y
    constructor
    · intro hxy
      rcases hx : P.toOrderedForestVertex x with ⟨i, a⟩
      rcases hy : P.toOrderedForestVertex y with ⟨j, b⟩
      have hordered : P.orderedForest.graph.Adj ⟨i, a⟩ ⟨j, b⟩ := by
        simpa [hx, hy] using hxy
      rcases (orderedGraph_adj_mk P.orderedForest).mp hordered with
        ⟨hij, hab⟩
      subst j
      have hcut := (component_adj_iff P i a b).mpr hab
      have hx' : P.fromOrderedForestVertex ⟨i, a⟩ = x := by
        rw [← hx, P.from_toOrderedForestVertex]
      have hy' : P.fromOrderedForestVertex ⟨i, b⟩ = y := by
        rw [← hy, P.from_toOrderedForestVertex]
      rw [hx', hy'] at hcut
      exact hcut
    · intro hxy
      have h := P.cutForestCopy.toHom.map_rel hxy
      change P.orderedForest.graph.Adj (P.cutForestCopy x)
        (P.cutForestCopy y) at h
      change P.orderedForest.graph.Adj (P.toOrderedForestVertex x)
        (P.toOrderedForestVertex y)
      simpa only [Erdos547b.ZhaoLemma614Full.cutForestCopy_apply] using h

@[simp] theorem partitionBranchEquivNonroots_component
    (P : ZhaoForestPartition T globalRoot small)
    (z : Σ j, Fin ((branchForest P).branches.size j)) :
    P.componentIndex ((partitionBranchEquivNonroots P z).1) =
      (branchForest P).owner z.1 := by
  let w := branchCoordinatesEquivNonroots P.orderedForest z
  have hcomponent :
      P.componentIndex (P.fromOrderedForestVertex w.1) = w.1.1 := by
    have h := congrArg Sigma.fst
      (toOrderedForestVertex_fromOrderedForestVertex P w.1)
    exact h
  change P.componentIndex (P.fromOrderedForestVertex w.1) =
    (branchForest P).owner z.1
  rw [hcomponent]
  exact branchCoordinatesEquivNonroots_component P.orderedForest z.1 z.2

/-- Root-deleted branches owned by components in the canonical major parity. -/
def halfBranches (P : ZhaoForestPartition T globalRoot small) :
    Finset (Fin (Fintype.card (ChildKey P.orderedForest))) :=
  Finset.univ.filter fun j =>
    T.dist globalRoot (P.roots ((branchForest P).owner j)) % 2 =
      (majorParity P).val

noncomputable def actualBranchRoot
    (P : ZhaoForestPartition T globalRoot small)
    (j : Fin (Fintype.card (ChildKey P.orderedForest))) : V :=
  (cutForestGraphIso P).symm
    (branchGraphIso P.orderedForest
      (Sum.inr (⟨j, (branchForest P).branches.root j⟩ :
        Σ q, Fin ((branchForest P).branches.size q))))

@[simp] theorem actualBranchRoot_eq_partitionBranchEquiv
    (P : ZhaoForestPartition T globalRoot small)
    (j : Fin (Fintype.card (ChildKey P.orderedForest))) :
    actualBranchRoot P j =
      (partitionBranchEquivNonroots P
        (⟨j, (branchForest P).branches.root j⟩ :
          Σ q, Fin ((branchForest P).branches.size q))).1 := by
  rfl

theorem actualBranchRoot_mem_levelOne
    (P : ZhaoForestPartition T globalRoot small)
    (j : Fin (Fintype.card (ChildKey P.orderedForest))) :
    actualBranchRoot P j ∈ partitionLevelOne P := by
  let v : (branchForest P).Vertex :=
    Sum.inr (⟨j, (branchForest P).branches.root j⟩ :
      Σ q, Fin ((branchForest P).branches.size q))
  have hbranch : (branchForest P).graph.Adj
      (Sum.inl ((branchForest P).owner j)) v := ⟨rfl, rfl⟩
  have hordered : P.orderedForest.graph.Adj
      (branchGraphIso P.orderedForest (Sum.inl ((branchForest P).owner j)))
      (branchGraphIso P.orderedForest v) :=
    (branchGraphIso P.orderedForest).toHom.map_rel hbranch
  have hcut : P.cutForest.Adj
      ((cutForestGraphIso P).symm
        (branchGraphIso P.orderedForest (Sum.inl ((branchForest P).owner j))))
      (actualBranchRoot P j) :=
    (cutForestGraphIso P).symm.toHom.map_rel hordered
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ⟨(branchForest P).owner j, ?_⟩⟩
  have hroot :
      (cutForestGraphIso P).symm
          (branchGraphIso P.orderedForest
            (Sum.inl ((branchForest P).owner j))) =
        P.roots ((branchForest P).owner j) := by
    apply (cutForestGraphIso P).injective
    rw [(cutForestGraphIso P).apply_symm_apply]
    change branchEquiv P.orderedForest
        (Sum.inl ((branchForest P).owner j)) =
      P.toOrderedForestVertex (P.roots ((branchForest P).owner j))
    rw [branchEquiv_apply, flattenBranch_root,
      Erdos547b.ZhaoLemma614Full.toOrderedForestVertex_root]
  rw [hroot] at hcut
  exact hcut

theorem actualBranchRoot_degree
    (P : ZhaoForestPartition T globalRoot small)
    (j : Fin (Fintype.card (ChildKey P.orderedForest))) :
    P.cutForest.degree (actualBranchRoot P j) =
      (branchForest P).graph.degree
        (Sum.inr (⟨j, (branchForest P).branches.root j⟩ :
          Σ q, Fin ((branchForest P).branches.size q))) := by
  let v : (branchForest P).Vertex :=
    Sum.inr (⟨j, (branchForest P).branches.root j⟩ :
      Σ q, Fin ((branchForest P).branches.size q))
  have hcut := degree_eq_of_iso (cutForestGraphIso P) (actualBranchRoot P j)
  have hbranch := degree_eq_of_iso (branchGraphIso P.orderedForest) v
  have happly : cutForestGraphIso P (actualBranchRoot P j) =
      branchGraphIso P.orderedForest v := by
    exact (cutForestGraphIso P).apply_symm_apply _
  rw [happly] at hcut
  exact hcut.trans hbranch.symm

theorem actualBranchRoot_mem_levelOneLeaves_iff
    (P : ZhaoForestPartition T globalRoot small)
    (j : Fin (Fintype.card (ChildKey P.orderedForest))) :
    actualBranchRoot P j ∈ partitionLevelOneLeaves P ↔
      (branchForest P).branches.size j = 1 := by
  rw [partitionLevelOneLeaves, Finset.mem_inter,
    and_iff_right (actualBranchRoot_mem_levelOne P j), graphLeaves,
    Finset.mem_filter, and_iff_right (Finset.mem_univ _)]
  let v : (branchForest P).Vertex :=
    Sum.inr (⟨j, (branchForest P).branches.root j⟩ :
      Σ q, Fin ((branchForest P).branches.size q))
  have hdegreeNat :
      Nat.card (P.cutForest.neighborSet (actualBranchRoot P j)) =
        Nat.card ((branchForest P).graph.neighborSet v) := by
    calc
      Nat.card (P.cutForest.neighborSet (actualBranchRoot P j)) =
          P.cutForest.degree (actualBranchRoot P j) :=
        (degree_eq_natCard (G := P.cutForest) (actualBranchRoot P j)).symm
      _ = (branchForest P).graph.degree v := actualBranchRoot_degree P j
      _ = Nat.card ((branchForest P).graph.neighborSet v) :=
        degree_eq_natCard (G := (branchForest P).graph) v
  have hbranchNat :
      Nat.card ((branchForest P).graph.neighborSet v) = 1 ↔
        (branchForest P).branches.size j = 1 := by
    rw [← degree_eq_natCard (G := (branchForest P).graph) v]
    exact branchRoot_degree_eq_one_iff (branchForest P) j
  rw [degree_eq_natCard, hdegreeNat, hbranchNat]

abbrev HalfBranchCoordinate (P : ZhaoForestPartition T globalRoot small) :=
  Σ j : {j // j ∈ halfBranches P},
    Fin ((branchForest P).branches.size j.1)

/-- The selected parity half is literally the disjoint union of the
root-deleted branches owned by roots of that parity. -/
noncomputable def halfBranchEquivMajorPart
    (P : ZhaoForestPartition T globalRoot small) :
    HalfBranchCoordinate P ≃ {x // x ∈ majorPart P} := by
  let f : HalfBranchCoordinate P → {x // x ∈ majorPart P} := fun z ↦
    let w : Σ j, Fin ((branchForest P).branches.size j) := ⟨z.1.1, z.2⟩
    ⟨(partitionBranchEquivNonroots P w).1, by
      rw [← parityPart_majorParity P]
      apply Finset.mem_filter.mpr
      refine ⟨(partitionBranchEquivNonroots P w).2, ?_⟩
      rw [partitionBranchEquivNonroots_component P w]
      exact (Finset.mem_filter.mp z.1.2).2⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨j, a⟩ ⟨l, b⟩ hab
    have htotal :
        (⟨j.1, a⟩ : Σ q, Fin ((branchForest P).branches.size q)) =
          ⟨l.1, b⟩ := by
      apply (partitionBranchEquivNonroots P).injective
      apply Subtype.ext
      simpa only [f] using congrArg Subtype.val hab
    have hjl : j.1 = l.1 := congrArg Sigma.fst htotal
    rcases j with ⟨j, hj⟩
    rcases l with ⟨l, hl⟩
    dsimp only at hjl
    subst l
    have hab' : a = b := eq_of_heq (Sigma.mk.inj_iff.mp htotal).2
    subst b
    rfl
  · intro x
    have hxParity : x.1 ∈ parityPart P (majorParity P) := by
      simpa using x.2
    have hxNonroot : x.1 ∈ partitionNonroots P :=
      (Finset.mem_filter.mp hxParity).1
    let z := (partitionBranchEquivNonroots P).symm ⟨x.1, hxNonroot⟩
    have hzApply : partitionBranchEquivNonroots P z = ⟨x.1, hxNonroot⟩ :=
      Equiv.apply_symm_apply _ _
    have hzComponent :
        P.componentIndex x.1 = (branchForest P).owner z.1 := by
      have h := partitionBranchEquivNonroots_component P z
      have hzValue := congrArg Subtype.val hzApply
      rw [hzValue] at h
      exact h
    have hzHalf : z.1 ∈ halfBranches P := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← hzComponent]
      exact (Finset.mem_filter.mp hxParity).2
    refine ⟨⟨⟨z.1, hzHalf⟩, z.2⟩, ?_⟩
    apply Subtype.ext
    change (partitionBranchEquivNonroots P z).1 = x.1
    exact congrArg Subtype.val hzApply

@[simp] theorem halfBranchEquivMajorPart_apply_val
    (P : ZhaoForestPartition T globalRoot small)
    (z : HalfBranchCoordinate P) :
    (halfBranchEquivMajorPart P z).1 =
      (partitionBranchEquivNonroots P
        (⟨z.1.1, z.2⟩ :
          Σ j, Fin ((branchForest P).branches.size j))).1 := by
  rfl

abbrev SingletonHalfBranch
    (P : ZhaoForestPartition T globalRoot small) :=
  {j // j ∈ (halfBranches P).filter
    (fun j ↦ (branchForest P).branches.size j = 1)}

/-- The Level-one leaves in the major half are exactly its singleton
root-deleted branches. -/
noncomputable def singletonHalfBranchEquivMajorLevelOneLeaves
    (P : ZhaoForestPartition T globalRoot small) :
    SingletonHalfBranch P ≃
      {x // x ∈ majorPart P ∩ partitionLevelOneLeaves P} := by
  let f : SingletonHalfBranch P →
      {x // x ∈ majorPart P ∩ partitionLevelOneLeaves P} := fun j ↦
    ⟨actualBranchRoot P j.1, by
      apply Finset.mem_inter.mpr
      refine ⟨?_, (actualBranchRoot_mem_levelOneLeaves_iff P j.1).2
        (Finset.mem_filter.mp j.2).2⟩
      rw [← parityPart_majorParity P]
      apply Finset.mem_filter.mpr
      let z : Σ q, Fin ((branchForest P).branches.size q) :=
        ⟨j.1, (branchForest P).branches.root j.1⟩
      refine ⟨(partitionBranchEquivNonroots P z).2, ?_⟩
      have hcomponent :
          P.componentIndex (actualBranchRoot P j.1) =
            (branchForest P).owner j.1 := by
        rw [actualBranchRoot_eq_partitionBranchEquiv,
          partitionBranchEquivNonroots_component]
      rw [hcomponent]
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp j.2).1).2⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro j l hjl
    have htotal :
        (⟨j.1, (branchForest P).branches.root j.1⟩ :
            Σ q, Fin ((branchForest P).branches.size q)) =
          ⟨l.1, (branchForest P).branches.root l.1⟩ := by
      apply (partitionBranchEquivNonroots P).injective
      apply Subtype.ext
      have hval := congrArg Subtype.val hjl
      change actualBranchRoot P j.1 = actualBranchRoot P l.1 at hval
      simpa only [actualBranchRoot_eq_partitionBranchEquiv] using hval
    exact Subtype.ext (congrArg Sigma.fst htotal)
  · intro x
    have hxMajor : x.1 ∈ majorPart P := (Finset.mem_inter.mp x.2).1
    have hxLeaf : x.1 ∈ partitionLevelOneLeaves P :=
      (Finset.mem_inter.mp x.2).2
    let z := (halfBranchEquivMajorPart P).symm ⟨x.1, hxMajor⟩
    have hzApply : halfBranchEquivMajorPart P z = ⟨x.1, hxMajor⟩ :=
      Equiv.apply_symm_apply _ _
    have hxValue :
        x.1 = (partitionBranchEquivNonroots P
          (⟨z.1.1, z.2⟩ :
            Σ j, Fin ((branchForest P).branches.size j))).1 := by
      exact (congrArg Subtype.val hzApply).symm
    have hxLevel : x.1 ∈ partitionLevelOne P :=
      (Finset.mem_inter.mp hxLeaf).1
    obtain ⟨i, hix⟩ := (Finset.mem_filter.mp hxLevel).2
    have hordered := (cutForestGraphIso P).toHom.map_rel hix
    have hordered' : P.orderedForest.graph.Adj
        (flattenBranch P.orderedForest (Sum.inl i))
        (flattenBranch P.orderedForest
          (Sum.inr (⟨z.1.1, z.2⟩ :
            Σ j, Fin ((branchForest P).branches.size j)))) := by
      have hleft : (cutForestGraphIso P).toHom (P.roots i) =
          flattenBranch P.orderedForest (Sum.inl i) := by
        change P.toOrderedForestVertex (P.roots i) =
          flattenBranch P.orderedForest (Sum.inl i)
        rw [Erdos547b.ZhaoLemma614Full.toOrderedForestVertex_root,
          flattenBranch_root]
      have hright : (cutForestGraphIso P).toHom x.1 =
          flattenBranch P.orderedForest
            (Sum.inr (⟨z.1.1, z.2⟩ :
              Σ j, Fin ((branchForest P).branches.size j))) := by
        change P.toOrderedForestVertex x.1 = _
        rw [hxValue, partitionBranchEquivNonroots_apply_val,
          toOrderedForestVertex_fromOrderedForestVertex]
      rw [hleft, hright] at hordered
      exact hordered
    have hbranch := flattenBranch_reflect_adj P.orderedForest hordered'
    have hzRoot : z.2 = (branchForest P).branches.root z.1.1 := hbranch.2
    have hxActual : x.1 = actualBranchRoot P z.1.1 := by
      rw [hxValue, hzRoot, ← actualBranchRoot_eq_partitionBranchEquiv]
    have hsize : (branchForest P).branches.size z.1.1 = 1 := by
      apply (actualBranchRoot_mem_levelOneLeaves_iff P z.1.1).1
      exact hxActual ▸ hxLeaf
    refine ⟨⟨z.1.1, Finset.mem_filter.mpr ⟨z.1.2, hsize⟩⟩, ?_⟩
    apply Subtype.ext
    exact hxActual.symm

theorem majorPart_inter_levelOneLeaves_card
    (P : ZhaoForestPartition T globalRoot small) :
    (majorPart P ∩ partitionLevelOneLeaves P).card =
      ((halfBranches P).filter
        (fun j ↦ (branchForest P).branches.size j = 1)).card := by
  have hcard := Fintype.card_congr
    (singletonHalfBranchEquivMajorLevelOneLeaves P)
  rw [Fintype.card_coe, Fintype.card_coe] at hcard
  exact hcard.symm

theorem majorPart_card_eq_halfBranchMass
    (P : ZhaoForestPartition T globalRoot small) :
    (majorPart P).card =
      ∑ j ∈ halfBranches P, (branchForest P).branches.size j := by
  have hcard := Fintype.card_congr (halfBranchEquivMajorPart P)
  rw [Fintype.card_coe, Fintype.card_sigma] at hcard
  simp only [Fintype.card_fin] at hcard
  calc
    (majorPart P).card =
        ∑ j : {j // j ∈ halfBranches P},
          (branchForest P).branches.size j.1 := hcard.symm
    _ = ∑ j ∈ halfBranches P, (branchForest P).branches.size j :=
      Finset.sum_attach (halfBranches P)
        (fun j ↦ (branchForest P).branches.size j)

def sizeTwoBranches (P : ZhaoForestPartition T globalRoot small) :
    Finset (Fin (Fintype.card (ChildKey P.orderedForest))) :=
  (halfBranches P).filter fun j => (branchForest P).branches.size j = 2

def largeHalfBranches (P : ZhaoForestPartition T globalRoot small) :
    Finset (Fin (Fintype.card (ChildKey P.orderedForest))) :=
  (halfBranches P).filter fun j => 3 ≤ (branchForest P).branches.size j

def nontrivialHalfMass (P : ZhaoForestPartition T globalRoot small) : ℕ :=
  ∑ j ∈ (halfBranches P).filter
      (fun j => 2 ≤ (branchForest P).branches.size j),
    (branchForest P).branches.size j

def largeHalfMass (P : ZhaoForestPartition T globalRoot small) : ℕ :=
  ∑ j ∈ largeHalfBranches P, (branchForest P).branches.size j

theorem singleton_union_nontrivial_halfBranches
    (P : ZhaoForestPartition T globalRoot small) :
    (halfBranches P).filter
          (fun j ↦ (branchForest P).branches.size j = 1) ∪
        (halfBranches P).filter
          (fun j ↦ 2 ≤ (branchForest P).branches.size j) =
      halfBranches P := by
  ext j
  by_cases hj : j ∈ halfBranches P
  · have hpos : 0 < (branchForest P).branches.size j :=
      Nat.zero_lt_of_lt ((branchForest P).branches.root j).isLt
    simp only [Finset.mem_union, Finset.mem_filter, hj, true_and]
    constructor
    · intro _
      trivial
    · intro _
      by_cases hone : (branchForest P).branches.size j = 1
      · exact Or.inl hone
      · exact Or.inr (by omega)
  · simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hj', -⟩ | ⟨hj', -⟩)
      · exact False.elim (hj hj')
      · exact False.elim (hj hj')
    · exact fun hj' ↦ False.elim (hj hj')

theorem singleton_disjoint_nontrivial_halfBranches
    (P : ZhaoForestPartition T globalRoot small) :
    Disjoint
      ((halfBranches P).filter
        (fun j ↦ (branchForest P).branches.size j = 1))
      ((halfBranches P).filter
        (fun j ↦ 2 ≤ (branchForest P).branches.size j)) := by
  rw [Finset.disjoint_left]
  intro j hj1 hj2
  have h1 := (Finset.mem_filter.mp hj1).2
  have h2 := (Finset.mem_filter.mp hj2).2
  omega

theorem sum_singleton_halfBranches
    (P : ZhaoForestPartition T globalRoot small) :
    ∑ j ∈ (halfBranches P).filter
          (fun j ↦ (branchForest P).branches.size j = 1),
        (branchForest P).branches.size j =
      ((halfBranches P).filter
        (fun j ↦ (branchForest P).branches.size j = 1)).card := by
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro j hj
  simpa only using (Finset.mem_filter.mp hj).2

/-- Exact source classification required by Claim 6.17: after deleting the
Level-one leaves, the canonical major parity half has precisely the mass of
its branches of size at least two. -/
theorem majorPart_sdiff_levelOneLeaves_card_eq_nontrivialHalfMass
    (P : ZhaoForestPartition T globalRoot small) :
    (majorPart P \ partitionLevelOneLeaves P).card =
      nontrivialHalfMass P := by
  have hmass :
      ∑ j ∈ halfBranches P, (branchForest P).branches.size j =
        ((halfBranches P).filter
            (fun j ↦ (branchForest P).branches.size j = 1)).card +
          nontrivialHalfMass P := by
    change
      (∑ j ∈ halfBranches P, (branchForest P).branches.size j) =
        ((halfBranches P).filter
            (fun j ↦ (branchForest P).branches.size j = 1)).card +
          ∑ j ∈ (halfBranches P).filter
              (fun j ↦ 2 ≤ (branchForest P).branches.size j),
            (branchForest P).branches.size j
    calc
      (∑ j ∈ halfBranches P, (branchForest P).branches.size j) =
          ∑ j ∈
              (halfBranches P).filter
                  (fun j ↦ (branchForest P).branches.size j = 1) ∪
                (halfBranches P).filter
                  (fun j ↦ 2 ≤ (branchForest P).branches.size j),
            (branchForest P).branches.size j := by
        rw [singleton_union_nontrivial_halfBranches]
      _ =
          (∑ j ∈ (halfBranches P).filter
              (fun j ↦ (branchForest P).branches.size j = 1),
            (branchForest P).branches.size j) +
          ∑ j ∈ (halfBranches P).filter
              (fun j ↦ 2 ≤ (branchForest P).branches.size j),
            (branchForest P).branches.size j := by
        rw [Finset.sum_union (singleton_disjoint_nontrivial_halfBranches P)]
      _ =
          ((halfBranches P).filter
              (fun j ↦ (branchForest P).branches.size j = 1)).card +
            ∑ j ∈ (halfBranches P).filter
                (fun j ↦ 2 ≤ (branchForest P).branches.size j),
              (branchForest P).branches.size j := by
        rw [sum_singleton_halfBranches]
  rw [Finset.card_sdiff, Finset.inter_comm,
    majorPart_inter_levelOneLeaves_card,
    majorPart_card_eq_halfBranchMass]
  omega

/-- Claim 6.8 rewritten on the exact branch mass used by Claims 6.16 and
6.17.  No caller-supplied `partA` or branch-classification premise remains. -/
theorem claim6_8_nontrivialHalfMass_lower
    (P : ZhaoForestPartition T globalRoot small)
    (d : ℝ) (hd : 0 ≤ d) (n : ℕ)
    (hcardT : Fintype.card V = n + 1)
    (horiginalLeaves :
      (((partitionLevelOneLeaves P ∩ graphLeaves T).card : ℕ) : ℝ) <
        11 * Real.sqrt d * n)
    (hhierarchyF : 2 * (P.numParts : ℝ) < 1 + Real.sqrt d * n)
    (hhierarchyA : 3 * (P.numParts : ℝ) < 1 + 2 * Real.sqrt d * n) :
    (n : ℝ) / 2 - 12 * Real.sqrt d * n <
      (nontrivialHalfMass P : ℝ) := by
  have h := (claim6_8_canonicalParityHalf P d hd n hcardT
    horiginalLeaves hhierarchyF hhierarchyA).2
  simpa [majorPart_sdiff_levelOneLeaves_card_eq_nontrivialHalfMass P] using h

theorem nat_lower_le_nontrivialHalfMass_of_real_lt
    (P : ZhaoForestPartition T globalRoot small) (lower : ℕ)
    (h : (lower : ℝ) < (nontrivialHalfMass P : ℝ)) :
    lower + 1 ≤ nontrivialHalfMass P := by
  exact_mod_cast h

@[simp] theorem mem_sizeTwoBranches
    (P : ZhaoForestPartition T globalRoot small) (j) :
    j ∈ sizeTwoBranches P ↔
      j ∈ halfBranches P ∧ (branchForest P).branches.size j = 2 := by
  rw [sizeTwoBranches, Finset.mem_filter]

@[simp] theorem mem_largeHalfBranches
    (P : ZhaoForestPartition T globalRoot small) (j) :
    j ∈ largeHalfBranches P ↔
      j ∈ halfBranches P ∧ 3 ≤ (branchForest P).branches.size j := by
  rw [largeHalfBranches, Finset.mem_filter]

theorem nontrivialBranches_eq_sizeTwo_union_large
    (P : ZhaoForestPartition T globalRoot small) :
    (halfBranches P).filter
        (fun j => 2 ≤ (branchForest P).branches.size j) =
      sizeTwoBranches P ∪ largeHalfBranches P := by
  ext j
  by_cases hj : j ∈ halfBranches P
  · simp only [Finset.mem_filter, Finset.mem_union, mem_sizeTwoBranches,
      mem_largeHalfBranches, hj, true_and]
    omega
  · simp only [Finset.mem_filter, Finset.mem_union,
      mem_sizeTwoBranches, mem_largeHalfBranches]
    constructor
    · rintro ⟨hj', -⟩
      exact False.elim (hj hj')
    · rintro (⟨hj', -⟩ | ⟨hj', -⟩)
      · exact False.elim (hj hj')
      · exact False.elim (hj hj')

theorem sizeTwoBranches_disjoint_large
    (P : ZhaoForestPartition T globalRoot small) :
    Disjoint (sizeTwoBranches P) (largeHalfBranches P) := by
  rw [Finset.disjoint_left]
  intro j hj2 hj3
  have h2 := (mem_sizeTwoBranches P j).mp hj2
  have h3 := (mem_largeHalfBranches P j).mp hj3
  omega

theorem sum_sizeTwoBranches
    (P : ZhaoForestPartition T globalRoot small) :
    ∑ j ∈ sizeTwoBranches P, (branchForest P).branches.size j =
      2 * (sizeTwoBranches P).card := by
  calc
    ∑ j ∈ sizeTwoBranches P, (branchForest P).branches.size j =
        ∑ _j ∈ sizeTwoBranches P, 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (mem_sizeTwoBranches P j).mp hj |>.2
    _ = 2 * (sizeTwoBranches P).card := by simp [Nat.mul_comm]

theorem nontrivialHalfMass_eq_two_mul_add_large
    (P : ZhaoForestPartition T globalRoot small) :
    nontrivialHalfMass P =
      2 * (sizeTwoBranches P).card + largeHalfMass P := by
  rw [nontrivialHalfMass, nontrivialBranches_eq_sizeTwo_union_large,
    Finset.sum_union (sizeTwoBranches_disjoint_large P),
    sum_sizeTwoBranches]
  rfl

theorem pathCount_le_of_branch_masses
    (P : ZhaoForestPartition T globalRoot small)
    (lower bad parentBound q : ℕ)
    (hclaim68 : lower ≤ nontrivialHalfMass P)
    (hclaim616 : largeHalfMass P ≤ bad)
    (hparents : (partitionParents P).card ≤ parentBound)
    (hcleanLoss : (sizeTwoBranches P).card ≤
      (middles P).card + (partitionParents P).card)
    (hhierarchy : bad + 2 * (q + parentBound) ≤ lower) :
    q ≤ (middles P).card := by
  have hsplit := nontrivialHalfMass_eq_two_mul_add_large P
  omega

end Erdos547b.ZhaoClaim617BranchCount

#print axioms Erdos547b.ZhaoClaim617BranchCount.nontrivialHalfMass_eq_two_mul_add_large
#print axioms Erdos547b.ZhaoClaim617BranchCount.majorPart_sdiff_levelOneLeaves_card_eq_nontrivialHalfMass
#print axioms Erdos547b.ZhaoClaim617BranchCount.claim6_8_nontrivialHalfMass_lower
#print axioms Erdos547b.ZhaoClaim617BranchCount.pathCount_le_of_branch_masses
