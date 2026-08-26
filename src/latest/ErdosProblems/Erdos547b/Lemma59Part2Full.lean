/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.ForestMatching
import ErdosProblems.Erdos547b.PrescribedRootForest
import ErdosProblems.Erdos547b.Lemma59Aggregate
import ErdosProblems.Erdos547b.Lemma59BranchRootSelector
import ErdosProblems.Erdos547b.Lemma59GroupedBranchEmbedding
import Mathlib.Combinatorics.Hall.Basic

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma59Part2Full

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59FullOnline

universe u

/-!
`OrderedBranchForest` is the source-shaped presentation used in the proof of
Zhao Lemma 5.9(2).  The vertices `Fin r` are the roots of the original
ordered trees.  Removing those roots leaves the `b` rooted branch trees.
`owner j` says to which original root branch `j` is attached.

This representation is deliberately not an allocation certificate: it is
only source-tree data.  In particular no host embedding, candidate-neighbor
oracle, or continuation is stored in it.
-/

structure OrderedBranchForest (r b : ℕ) where
  branches : OrderedRootedForest b
  owner : Fin b → Fin r

namespace OrderedBranchForest

variable {r b : ℕ}

/-- Vertices of the original forest: original roots, or vertices in one of
the components left after deleting the roots. -/
abbrev Vertex (F : OrderedBranchForest r b) :=
  Sum (Fin r) (Σ j, Fin (F.branches.size j))

/-- The original forest reconstructed from its root-deleted branches. -/
def graph (F : OrderedBranchForest r b) : SimpleGraph F.Vertex where
  Adj x y :=
    match x, y with
    | Sum.inl i, Sum.inl _ => False
    | Sum.inl i, Sum.inr z =>
        F.owner z.1 = i ∧ z.2 = F.branches.root z.1
    | Sum.inr z, Sum.inl i =>
        F.owner z.1 = i ∧ z.2 = F.branches.root z.1
    | Sum.inr z, Sum.inr w =>
        ∃ h : z.1 = w.1,
          (F.branches.tree z.1).Adj z.2 (h ▸ w.2)
  symm := ⟨by
    rintro (i | z) (k | w) h
    · exact h
    · exact h
    · exact h
    · rcases h with ⟨hzw, hadj⟩
      rcases z with ⟨j, a⟩
      rcases w with ⟨k, c⟩
      dsimp only at hzw
      subst k
      refine ⟨rfl, ?_⟩
      simpa using hadj.symm⟩
  loopless := ⟨by
    rintro (i | z) h
    · exact h
    · rcases h with ⟨hzz, hadj⟩
      apply (F.branches.tree z.1).loopless.irrefl z.2
      simpa [hzz] using hadj⟩

@[simp] theorem graph_adj_root_root (F : OrderedBranchForest r b)
    (i k : Fin r) : ¬F.graph.Adj (Sum.inl i) (Sum.inl k) := by
  simp [graph]

@[simp] theorem graph_adj_root_branch (F : OrderedBranchForest r b)
    (i : Fin r) (z : Σ j, Fin (F.branches.size j)) :
    F.graph.Adj (Sum.inl i) (Sum.inr z) ↔
      F.owner z.1 = i ∧ z.2 = F.branches.root z.1 := by
  rfl

@[simp] theorem graph_adj_branch_root (F : OrderedBranchForest r b)
    (z : Σ j, Fin (F.branches.size j)) (i : Fin r) :
    F.graph.Adj (Sum.inr z) (Sum.inl i) ↔
      F.owner z.1 = i ∧ z.2 = F.branches.root z.1 := by
  rfl

@[simp] theorem graph_adj_branch_branch (F : OrderedBranchForest r b)
    (z w : Σ j, Fin (F.branches.size j)) :
    F.graph.Adj (Sum.inr z) (Sum.inr w) ↔
      ∃ h : z.1 = w.1,
        (F.branches.tree z.1).Adj z.2 (h ▸ w.2) := by
  rfl

/-- Original roots. -/
def roots (F : OrderedBranchForest r b) : Finset F.Vertex :=
  Finset.univ.image Sum.inl

/-- Original Level1: the root of every root-deleted branch. -/
def levelOne (F : OrderedBranchForest r b) : Finset F.Vertex :=
  Finset.univ.image fun j ↦
    Sum.inr (Sigma.mk j (F.branches.root j))

/-- Distance level in the reconstructed forest. -/
def level (F : OrderedBranchForest r b) : F.Vertex → ℕ
  | Sum.inl _ => 0
  | Sum.inr z =>
      1 + (F.branches.tree z.1).dist (F.branches.root z.1) z.2

/-- Vertices at level at least two. -/
def levelGeTwo (F : OrderedBranchForest r b) : Finset F.Vertex := by
  classical
  exact Finset.univ.filter fun x ↦
      match x with
      | Sum.inl _ => False
      | Sum.inr z => z.2 ≠ F.branches.root z.1

/-- Zhao's optional odd-level set. -/
def oddVertices (F : OrderedBranchForest r b) : Finset F.Vertex :=
  Finset.univ.filter fun x ↦ F.level x % 2 = 1

@[simp] theorem level_root (F : OrderedBranchForest r b) (i : Fin r) :
    F.level (Sum.inl i) = 0 := rfl

@[simp] theorem level_branchRoot (F : OrderedBranchForest r b) (j : Fin b) :
    F.level (Sum.inr (Sigma.mk j (F.branches.root j))) = 1 := by
  simp [level]

theorem mem_roots_iff (F : OrderedBranchForest r b) (x : F.Vertex) :
    x ∈ F.roots ↔ ∃ i, x = Sum.inl i := by
  constructor
  · intro hx
    obtain ⟨i, -, hix⟩ := Finset.mem_image.mp hx
    exact ⟨i, hix.symm⟩
  · rintro ⟨i, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem mem_levelOne_iff (F : OrderedBranchForest r b) (x : F.Vertex) :
    x ∈ F.levelOne ↔
      ∃ j, x = Sum.inr (Sigma.mk j (F.branches.root j)) := by
  constructor
  · intro hx
    obtain ⟨j, -, hjx⟩ := Finset.mem_image.mp hx
    exact ⟨j, hjx.symm⟩
  · rintro ⟨j, rfl⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

@[simp] theorem card_roots (F : OrderedBranchForest r b) :
    #F.roots = r := by
  rw [roots, card_image_iff.mpr]
  · simp
  · intro i _ k _ h
    exact Sum.inl.inj h

@[simp] theorem card_levelOne (F : OrderedBranchForest r b) :
    #F.levelOne = b := by
  rw [levelOne, card_image_iff.mpr]
  · simp
  · intro i _ k _ h
    exact Sigma.mk.inj_iff.mp (Sum.inr.inj h) |>.1

/-- The exact number of vertices at Level at least two.  Every branch root is
Level1, so branch `j` contributes `size j - 1`. -/
theorem card_levelGeTwo (F : OrderedBranchForest r b) :
    #F.levelGeTwo = ∑ j, (F.branches.size j - 1) := by
  classical
  let Tail := Σ j, {a : Fin (F.branches.size j) //
    a ≠ F.branches.root j}
  let e : Tail ≃ {x // x ∈ F.levelGeTwo} :=
    { toFun := fun z ↦ ⟨Sum.inr ⟨z.1, z.2.1⟩, by
        simp [levelGeTwo, z.2.2]⟩
      invFun := fun x ↦ by
        cases hx : x.1 with
        | inl i =>
            exfalso
            have hp := x.2
            rw [hx] at hp
            simpa [levelGeTwo] using hp
        | inr z =>
            refine ⟨z.1, ⟨z.2, ?_⟩⟩
            have hp := x.2
            rw [hx] at hp
            simpa [levelGeTwo] using hp
      left_inv := by
        rintro ⟨j, a⟩
        rfl
      right_inv := by
        rintro ⟨(i | z), hx⟩
        · simp [levelGeTwo] at hx
        · rfl }
  have hcard : #F.levelGeTwo = Fintype.card Tail := by
    calc
      #F.levelGeTwo = Fintype.card {x // x ∈ F.levelGeTwo} := by simp
      _ = Fintype.card Tail := Fintype.card_congr e.symm
  rw [hcard, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  change Fintype.card {a : Fin (F.branches.size j) //
      ¬a = F.branches.root j} = F.branches.size j - 1
  simpa [Fintype.card_subtype_eq] using
    (Fintype.card_subtype_compl
      (fun a : Fin (F.branches.size j) ↦ a = F.branches.root j))

/-! ## Copy assembly -/

/-- Assemble the original forest after the branch forest has been embedded.
This is the exact graph-theoretic gluing operation hidden by the source's
arrow notation. -/
def copyOfBranchEmbedding
    {B : Type u} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootImage : Fin r → B) (E : F.branches.Embedding G)
    (hrootInjective : Function.Injective rootImage)
    (hrootOutside : ∀ i j a, rootImage i ≠ E.copy j a)
    (hattach : ∀ j,
      G.Adj (rootImage (F.owner j)) (E.copy j (F.branches.root j))) :
    F.graph.Copy G := by
  let f : F.Vertex → B
    | Sum.inl i => rootImage i
    | Sum.inr z => E.copy z.1 z.2
  have hfAdj : ∀ ⦃x y⦄, F.graph.Adj x y → G.Adj (f x) (f y) := by
    rintro (i | z) (k | w) h
    · exact False.elim h
    · rcases h with ⟨hown, hroot⟩
      subst i
      simpa [f, hroot] using hattach w.1
    · rcases h with ⟨hown, hroot⟩
      subst k
      simpa [f, hroot] using (hattach z.1).symm
    · rcases h with ⟨hzw, hadj⟩
      rcases z with ⟨j, a⟩
      rcases w with ⟨k, c⟩
      dsimp only at hzw
      subst k
      apply (E.copy j).toHom.map_rel
      simpa using hadj
  have hfInj : Function.Injective f := by
    rintro (i | z) (k | w) h
    · exact congrArg Sum.inl (hrootInjective h)
    · exact False.elim (hrootOutside i w.1 w.2 h)
    · exact False.elim (hrootOutside k z.1 z.2 h.symm)
    · have hsigma : z = w := by
        apply E.injective
        exact h
      exact congrArg Sum.inr hsigma
  exact ⟨⟨f, fun {_ _} h ↦ hfAdj h⟩, hfInj⟩

@[simp] theorem copyOfBranchEmbedding_root
    {B : Type u} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootImage : Fin r → B) (E : F.branches.Embedding G)
    (hrootInjective : Function.Injective rootImage)
    (hrootOutside : ∀ i j a, rootImage i ≠ E.copy j a)
    (hattach : ∀ j,
      G.Adj (rootImage (F.owner j)) (E.copy j (F.branches.root j)))
    (i : Fin r) :
    copyOfBranchEmbedding F G rootImage E hrootInjective hrootOutside hattach
      (Sum.inl i) = rootImage i := rfl

@[simp] theorem copyOfBranchEmbedding_branch
    {B : Type u} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootImage : Fin r → B) (E : F.branches.Embedding G)
    (hrootInjective : Function.Injective rootImage)
    (hrootOutside : ∀ i j a, rootImage i ≠ E.copy j a)
    (hattach : ∀ j,
      G.Adj (rootImage (F.owner j)) (E.copy j (F.branches.root j)))
    (z : Σ j, Fin (F.branches.size j)) :
    copyOfBranchEmbedding F G rootImage E hrootInjective hrootOutside hattach
      (Sum.inr z) = E.copy z.1 z.2 := rfl

end OrderedBranchForest

/-! ## The genuine three-layer flexible conclusion -/

/-- One realized copy with the three source layers recorded separately. -/
structure ThreeLayerCopy
    {r b : ℕ} {B : Type u} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootImage : Fin r → B) (special : Finset F.Vertex)
    (clusterTarget matchingTarget : Finset B) where
  copy : F.graph.Copy G
  map_root : ∀ i, copy (Sum.inl i) = rootImage i
  map_levelOne : ∀ x ∈ F.levelOne, copy x ∈ clusterTarget
  map_special : ∀ x ∈ special, copy x ∈ clusterTarget
  map_remaining : ∀ x, x ∉ F.roots → x ∉ F.levelOne → x ∉ special →
    copy x ∈ matchingTarget

/-- Zhao's full quantifier order for `F → (A,C,M)`: the optional odd set is
chosen first; then every injective root assignment outside a bounded,
explicitly recorded exceptional set has an actual three-layer copy. -/
structure FlexibleThreeLayerEmbedding
    {r b : ℕ} {B : Type u} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootCluster clusterTarget matchingTarget : Finset B)
    (rootSlack specialSlack : ℕ) where
  bad : Fin r → Finset B
  bad_subset : ∀ i, bad i ⊆ rootCluster
  card_bad : ∀ i, #(bad i) ≤ rootSlack
  realize : ∀ special : Finset F.Vertex,
    special ⊆ F.oddVertices → #special ≤ specialSlack →
    ∀ rootImage : Fin r → B,
      Function.Injective rootImage →
      (∀ i, rootImage i ∈ rootCluster) →
      (∀ i, rootImage i ∉ bad i) →
      Nonempty (ThreeLayerCopy F G rootImage special
        clusterTarget matchingTarget)

/-- Forget the layer distinction after the genuine three-layer construction.
This is the standard flexible-arrow object consumed by Proposition 5.7 and
Lemma 6.14.  The optional-set allowance is zero here, exactly the instance
used in Claim 6.16. -/
theorem FlexibleThreeLayerEmbedding.toZhaoFlexibleEmbedding
    {r b : ℕ} {B : Type u} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootCluster clusterTarget matchingTarget : Finset B)
    (rootSlack : ℕ)
    (E : FlexibleThreeLayerEmbedding F G rootCluster clusterTarget
      matchingTarget rootSlack 0) :
    Nonempty (Erdos547b.ZhaoProp57.FlexibleEmbedding F.graph G F.roots
      rootCluster (clusterTarget ∪ matchingTarget) rootSlack) := by
  classical
  refine ⟨
    { bad := fun x ↦ match x with
        | Sum.inl i => E.bad i
        | Sum.inr _ => ∅
      bad_subset := ?_
      card_bad := ?_
      realize := ?_ }⟩
  · rintro (i | z)
    · exact E.bad_subset i
    · exact Finset.empty_subset _
  · intro x hx
    obtain ⟨i, hxi⟩ := (F.mem_roots_iff x).mp hx
    subst x
    exact E.card_bad i
  · intro rootMap hrootInj hrootMem hrootGood
    let rootImage : Fin r → B := fun i ↦ rootMap (Sum.inl i)
    have hfinInj : Function.Injective rootImage := by
      intro i j hij
      have hs : (Sum.inl i : F.Vertex) = Sum.inl j := by
        apply hrootInj
        · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
        · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
        · exact hij
      exact Sum.inl.inj hs
    have hfinMem (i : Fin r) : rootImage i ∈ rootCluster := by
      apply hrootMem
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hfinGood (i : Fin r) : rootImage i ∉ E.bad i := by
      apply hrootGood
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    obtain ⟨R⟩ := E.realize ∅ (Finset.empty_subset _) (by simp)
      rootImage hfinInj hfinMem hfinGood
    refine ⟨
      { copy := R.copy
        map_root := ?_
        map_nonroot := ?_ }⟩
    · intro x hx
      obtain ⟨i, hxi⟩ := (F.mem_roots_iff x).mp hx
      subst x
      exact R.map_root i
    · intro x hx
      rcases x with i | z
      · exact False.elim (hx (Finset.mem_image.mpr
          ⟨i, Finset.mem_univ _, rfl⟩))
      · rcases z with ⟨j, a⟩
        by_cases hz : a = F.branches.root j
        · apply Finset.mem_union_left
          apply R.map_levelOne
          subst a
          exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
        · apply Finset.mem_union_right
          apply R.map_remaining
          · intro hroot
            simpa [OrderedBranchForest.roots] using hroot
          · intro hlevel
            obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hlevel
            have hs : (Sigma.mk q (F.branches.root q) :
                Σ t, Fin (F.branches.size t)) = ⟨j, a⟩ :=
              Sum.inr.inj hq
            cases hs
            exact hz rfl
          · simp

/-! ## Exact aggregate source counts -/

/-- Number of original ordered trees. -/
def treeCount {r b : ℕ} (_F : OrderedBranchForest r b) : ℕ := r

/-- Source `|Level1(F)|`. -/
def levelOneDemand {r b : ℕ} (_F : OrderedBranchForest r b) : ℕ := b

/-- Source `|Level>=2(F)|`. -/
def deepDemand {r b : ℕ} (F : OrderedBranchForest r b) : ℕ :=
  ∑ j, (F.branches.size j - 1)

@[simp] theorem levelOneDemand_eq_card_levelOne
    {r b : ℕ} (F : OrderedBranchForest r b) :
    levelOneDemand F = #F.levelOne := by
  simp [levelOneDemand]

@[simp] theorem deepDemand_eq_card_levelGeTwo
    {r b : ℕ} (F : OrderedBranchForest r b) :
    deepDemand F = #F.levelGeTwo := by
  rw [OrderedBranchForest.card_levelGeTwo]
  rfl

/-! ## The two aggregate allocations in Lemma 5.9(2) -/

/-- The displayed Level1 and Level>=2 hypotheses of Lemma 5.9(2) produce
the source proof's two assignments.  No assignment is assumed: both are
constructed by `unit_capacity_packing` and `allowed_capacity_packing`.

`clusterCapacity C` is the integer form of
`|P_C| - (epsilon + gamma) N`; `allowedEdges C` is the set of matching edges
having positive reduced density from `C`. -/
theorem exists_sourceAggregateAllocation
    {r b : ℕ} {C K : Type*}
    [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype K] [DecidableEq K] [Nonempty K]
    (F : OrderedBranchForest r b)
    (clusterCapacity : C → ℕ) (allowedEdges : C → Finset K)
    (m base slack : ℕ) (hmpos : 0 < m)
    (hlevelOne : levelOneDemand F ≤ ∑ C0 : C, clusterCapacity C0)
    (hadjacent : ∀ C0 : C, m ≤ #(allowedEdges C0))
    (hsmall : ∀ j : Fin b, F.branches.size j - 1 ≤ slack)
    (hdeep : deepDemand F ≤ m * base) :
    Nonempty (Erdos547b.ZhaoLemma59FullOnline.AggregateAllocation
      Finset.univ (fun j : Fin b ↦ F.branches.size j - 1)
      clusterCapacity allowedEdges base slack) := by
  apply Erdos547b.ZhaoLemma59FullOnline.exists_orderedBranchAggregateAllocation
    F.branches F.owner clusterCapacity allowedEdges m base slack hmpos
  · simpa [levelOneDemand] using hlevelOne
  · exact hadjacent
  · exact hsmall
  · simpa [deepDemand] using hdeep

/-- Hall form of the cluster-allocation step which keeps the source proof's
essential owner dependence.  A branch owned by `i` may only use clusters
`C` with `eligible i C`.  The prefix inequality is exactly the invariant
proved on p.17 of Zhao: when root `i` is reached, its eligible clusters have
enough total residual Level1 capacity even after every earlier tree.

The conclusion is an actual assignment, not an allocation assumption. -/
theorem exists_eligibleClusterAssignment
    {r b : ℕ} {C : Type*} [Fintype C] [DecidableEq C]
    (owner : Fin b → Fin r) (capacity : C → ℕ)
    (eligible : Fin r → C → Prop) [DecidableRel eligible]
    (hprefix : ∀ i : Fin r,
      #{j : Fin b | owner j ≤ i} ≤
        ∑ C0 : C, if eligible i C0 then capacity C0 else 0) :
    ∃ assign : Fin b → C,
      (∀ j, eligible (owner j) (assign j)) ∧
      ∀ C0 : C, #{j : Fin b | assign j = C0} ≤ capacity C0 := by
  classical
  let Slot := Σ C0, Fin (capacity C0)
  let choices : Fin b → Finset Slot := fun j ↦
    Finset.univ.filter fun s ↦ eligible (owner j) s.1
  have hchoicesCard (j : Fin b) :
      #(choices j) =
        ∑ C0 : C, if eligible (owner j) C0 then capacity C0 else 0 := by
    rw [show choices j = Finset.univ.filter
        (fun s : Slot ↦ eligible (owner j) s.1) by rfl]
    rw [Finset.card_filter, ← Finset.univ_sigma_univ]
    calc
      (∑ s ∈ Finset.univ.sigma (fun _C0 : C ↦ Finset.univ),
          if eligible (owner j) s.1 then 1 else 0) =
        ∑ C0 ∈ (Finset.univ : Finset C),
          ∑ _a ∈ (Finset.univ : Finset (Fin (capacity C0))),
            if eligible (owner j) C0 then 1 else 0 :=
          (Finset.sum_sigma' Finset.univ (fun _C0 : C ↦ Finset.univ)
            (fun C0 _a ↦ if eligible (owner j) C0 then 1 else 0)).symm
      _ = ∑ C0 : C,
          if eligible (owner j) C0 then capacity C0 else 0 := by simp
  have hHall : ∀ S : Finset (Fin b), #S ≤ #(S.biUnion choices) := by
    intro S
    by_cases hS : S = ∅
    · simp [hS]
    have hSnon : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    let owners : Finset (Fin r) := S.image owner
    have howners : owners.Nonempty := hSnon.image owner
    let i : Fin r := owners.max' howners
    have hiMem : i ∈ owners := Finset.max'_mem owners howners
    obtain ⟨j, hjS, hjOwner⟩ := Finset.mem_image.mp hiMem
    have hownerj : owner j = i := hjOwner
    have hSsub : S ⊆ Finset.univ.filter (fun k ↦ owner k ≤ i) := by
      intro k hk
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply Finset.le_max' owners (owner k)
      exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    have hchoiceSub : choices j ⊆ S.biUnion choices := by
      intro s hs
      exact Finset.mem_biUnion.mpr ⟨j, hjS, hs⟩
    calc
      #S ≤ #{k : Fin b | owner k ≤ i} := Finset.card_le_card hSsub
      _ ≤ ∑ C0 : C, if eligible i C0 then capacity C0 else 0 := hprefix i
      _ = #(choices j) := by simpa [hownerj] using (hchoicesCard j).symm
      _ ≤ #(S.biUnion choices) := Finset.card_le_card hchoiceSub
  obtain ⟨slot, hslotInj, hslotMem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective choices).mp hHall
  let assign : Fin b → C := fun j ↦ (slot j).1
  refine ⟨assign, ?_, ?_⟩
  · intro j
    have hj := Finset.mem_filter.mp (hslotMem j)
    exact hj.2
  · intro C0
    let source : Finset (Fin b) :=
      Finset.univ.filter fun j ↦ assign j = C0
    let target : Finset Slot :=
      Finset.univ.filter fun s ↦ s.1 = C0
    have hmap : Set.MapsTo slot (source : Set (Fin b)) (target : Set Slot) := by
      intro j hj
      have hj' := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'.2⟩
    have hinjOn : Set.InjOn slot (source : Set (Fin b)) := by
      intro x _ y _ hxy
      exact hslotInj hxy
    have hle : #source ≤ #target :=
      Finset.card_le_card_of_injOn slot hmap hinjOn
    have htarget : #target = capacity C0 := by
      rw [show target = Finset.univ.filter (fun s : Slot ↦ s.1 = C0) by rfl]
      rw [Finset.card_filter, ← Finset.univ_sigma_univ]
      calc
        (∑ s ∈ Finset.univ.sigma (fun _C : C ↦ Finset.univ),
            if s.1 = C0 then 1 else 0) =
          ∑ C ∈ (Finset.univ : Finset C),
            ∑ _a ∈ (Finset.univ : Finset (Fin (capacity C))),
              if C = C0 then 1 else 0 :=
            (Finset.sum_sigma' Finset.univ (fun _C : C ↦ Finset.univ)
              (fun C _a ↦ if C = C0 then 1 else 0)).symm
        _ = capacity C0 := by simp
    simpa [source] using hle.trans_eq htarget

/-- Full owner-sensitive aggregate allocation.  This is the static Hall/bin
packing form of the two-stage allocation actually used in Lemma 5.9(2). -/
theorem exists_eligibleAggregateAllocation
    {r b : ℕ} {C K : Type*}
    [Fintype C] [DecidableEq C]
    [Fintype K] [DecidableEq K] [Nonempty K]
    (F : OrderedBranchForest r b)
    (capacity : C → ℕ) (eligible : Fin r → C → Prop)
    [DecidableRel eligible] (allowedEdges : C → Finset K)
    (m base slack : ℕ) (hmpos : 0 < m)
    (hprefix : ∀ i : Fin r,
      #{j : Fin b | F.owner j ≤ i} ≤
        ∑ C0 : C, if eligible i C0 then capacity C0 else 0)
    (hadjacent : ∀ C0 : C, m ≤ #(allowedEdges C0))
    (hsmall : ∀ j : Fin b, F.branches.size j - 1 ≤ slack)
    (hdeep : deepDemand F ≤ m * base) :
    ∃ alloc : Erdos547b.ZhaoLemma59FullOnline.AggregateAllocation
      Finset.univ (fun j : Fin b ↦ F.branches.size j - 1)
      capacity allowedEdges base slack,
      ∀ j, eligible (F.owner j) (alloc.levelOneCluster j) := by
  classical
  obtain ⟨clusterAssign, hclusterEligible, hclusterLoad⟩ :=
    exists_eligibleClusterAssignment F.owner capacity eligible hprefix
  obtain ⟨edgeAssign, hedgeAllowed, hedgeLoad⟩ :=
    Erdos547b.ZhaoLemma59FullOnline.allowed_capacity_packing
      (Finset.univ : Finset (Fin b))
      (fun j : Fin b ↦ F.branches.size j - 1)
      (fun j ↦ allowedEdges (clusterAssign j)) m base slack hmpos (by
        intro j _
        exact hadjacent (clusterAssign j)) (by
        intro j _
        exact hsmall j) (by
        simpa [deepDemand] using hdeep)
  let alloc : Erdos547b.ZhaoLemma59FullOnline.AggregateAllocation
      Finset.univ (fun j : Fin b ↦ F.branches.size j - 1)
      capacity allowedEdges base slack :=
    { levelOneCluster := clusterAssign
      matchingEdge := edgeAssign
      cluster_load := hclusterLoad
      matching_allowed := hedgeAllowed
      matching_load := hedgeLoad }
  exact ⟨alloc, hclusterEligible⟩

/-! ## Actual graph realization from the aggregate allocation -/

/-- A typical vertex keeps `demand` neighbors after the atypical vertices on
the opposite side of an actual uniform pair are deleted. -/
theorem card_cleanedSide_neighbors_ge
    {B : Type*} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {rho : ℝ} {X Y : Finset B} (demand : ℕ)
    (hunif : G.IsUniform rho X Y) (hrho : rho ≤ 1)
    (hcap : (demand : ℝ) + rho * #Y ≤
      (G.edgeDensity X Y - rho) * #Y)
    {z : B} (hz : z ∈ cleanedSide G rho X Y) :
    demand ≤ #((cleanedSide G rho Y X).filter (G.Adj z)) := by
  classical
  let badY := atypicalVertices G rho Y X
  have hbadY : (#badY : ℝ) ≤ rho * #Y := by
    simpa [badY] using card_atypicalVertices_le G hunif.symm hrho
  have hzX : z ∈ X := (Finset.mem_sdiff.mp hz).1
  have hzGood : z ∉ atypicalVertices G rho X Y :=
    (Finset.mem_sdiff.mp hz).2
  have hzRaw : (G.edgeDensity X Y - rho) * (#Y : ℝ) ≤
      (#(Y.filter (G.Adj z)) : ℝ) := by
    apply le_of_not_gt
    intro hlt
    apply hzGood
    exact Finset.mem_filter.mpr ⟨hzX, hlt⟩
  have hreal : (demand : ℝ) + #badY ≤
      (#(Y.filter (G.Adj z)) : ℝ) := by
    calc
      (demand : ℝ) + #badY ≤ (demand : ℝ) + rho * #Y := by gcongr
      _ ≤ (G.edgeDensity X Y - rho) * #Y := hcap
      _ ≤ (#(Y.filter (G.Adj z)) : ℝ) := hzRaw
  have hnat : demand + #badY ≤ #(Y.filter (G.Adj z)) := by
    exact_mod_cast hreal
  simpa [cleanedSide, badY] using
    card_neighbors_cleaned_ge G Y badY z demand hnat

/-- A vertex selected typical from `C` toward the matching endpoint `X`
keeps the requested degree after `X` is cleaned relative to its mate `Y`. -/
theorem card_selectedEndpoint_neighbors_ge
    {B : Type*} [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {rho : ℝ} {C X Y : Finset B} (demand : ℕ)
    (hunifCX : G.IsUniform rho C X)
    (hunifXY : G.IsUniform rho X Y) (hrho : rho ≤ 1)
    (hcap : (demand : ℝ) + rho * #X ≤
      (G.edgeDensity C X - rho) * #X)
    {z : B} (hz : z ∈ cleanedSide G rho C X) :
    demand ≤ #((cleanedSide G rho X Y).filter (G.Adj z)) := by
  classical
  let badX := atypicalVertices G rho X Y
  have hbadX : (#badX : ℝ) ≤ rho * #X := by
    simpa [badX] using card_atypicalVertices_le G hunifXY hrho
  have hzC : z ∈ C := (Finset.mem_sdiff.mp hz).1
  have hzGood : z ∉ atypicalVertices G rho C X :=
    (Finset.mem_sdiff.mp hz).2
  have hzRaw : (G.edgeDensity C X - rho) * (#X : ℝ) ≤
      (#(X.filter (G.Adj z)) : ℝ) := by
    apply le_of_not_gt
    intro hlt
    apply hzGood
    exact Finset.mem_filter.mpr ⟨hzC, hlt⟩
  have hreal : (demand : ℝ) + #badX ≤
      (#(X.filter (G.Adj z)) : ℝ) := by
    calc
      (demand : ℝ) + #badX ≤ (demand : ℝ) + rho * #X := by gcongr
      _ ≤ (G.edgeDensity C X - rho) * #X := hcap
      _ ≤ (#(X.filter (G.Adj z)) : ℝ) := hzRaw
  have hnat : demand + #badX ≤ #(X.filter (G.Adj z)) := by
    exact_mod_cast hreal
  simpa [cleanedSide, badX] using
    card_neighbors_cleaned_ge G X badX z demand hnat

/-- Union of the cluster family used for Level1. -/
def clusterSupport
    {B : Type*} [DecidableEq B] {c : ℕ}
    (cluster : Fin c → Finset B) : Finset B :=
  Finset.univ.biUnion cluster

/-- Union of the matching sides used for Level>=2. -/
def matchingSupport
    {B : Type*} [DecidableEq B] {k : ℕ}
    (X Y : Fin k → Finset B) : Finset B :=
  Finset.univ.biUnion fun e ↦ X e ∪ Y e

/-- Concrete empty-`S` graph realization of aggregate Lemma 5.9(2).

The Level1 and matching assignments are supplied by the preceding proved
allocator.  Every graph-theoretic step is then derived from actual uniform
pairs: branch roots are selected in their assigned clusters, all branches
sharing a matching edge are embedded simultaneously by the grouped greedy
lemma, and the original roots are glued back by their actual host edges.
There is no copy, continuation, or pointwise `hcross` premise. -/
theorem exists_threeLayerCopy_emptySpecial_of_allocation
    {r b c k : ℕ} {B : Type*}
    [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (rootImage : Fin r → B)
    (cluster : Fin c → Finset B) (X Y : Fin k → Finset B)
    (childSide : Fin b → Fin 2)
    (capacity : Fin c → ℕ) (allowedEdges : Fin c → Finset (Fin k))
    (base slack : ℕ)
    (alloc : AggregateAllocation (Finset.univ : Finset (Fin b))
      (fun j : Fin b ↦ F.branches.size j - 1)
      capacity allowedEdges base slack)
    (hrootInjective : Function.Injective rootImage)
    (hrho : rho ≤ 1)
    (hunifClusterEndpoint : ∀ j,
      G.IsUniform rho (cluster (alloc.levelOneCluster j))
        (if childSide j = 0 then Y (alloc.matchingEdge j)
          else X (alloc.matchingEdge j)))
    (hrootClusterDegree : ∀ j,
      (capacity (alloc.levelOneCluster j) : ℝ) +
          rho * #(cluster (alloc.levelOneCluster j)) ≤
        (#((cluster (alloc.levelOneCluster j)).filter
          (G.Adj (rootImage (F.owner j)))) : ℝ))
    (hclusterDisjoint : ∀ p q, p ≠ q →
      Disjoint (cluster p) (cluster q))
    (hunifMatching : ∀ e, G.IsUniform rho (X e) (Y e))
    (hmatchCapX : ∀ e,
      (GroupedBranches.groupDeep F.branches alloc.matchingEdge e + 1 : ℝ) +
          rho * #(X e) ≤
        (G.edgeDensity (X e) (Y e) - rho) * #(X e))
    (hmatchCapY : ∀ e,
      (GroupedBranches.groupDeep F.branches alloc.matchingEdge e + 1 : ℝ) +
          rho * #(Y e) ≤
        (G.edgeDensity (X e) (Y e) - rho) * #(Y e))
    (hclusterEndpointCap : ∀ j,
      (GroupedBranches.groupDeep F.branches alloc.matchingEdge
          (alloc.matchingEdge j) + 1 : ℝ) +
          rho * #(if childSide j = 0 then Y (alloc.matchingEdge j)
            else X (alloc.matchingEdge j)) ≤
        (G.edgeDensity (cluster (alloc.levelOneCluster j))
          (if childSide j = 0 then Y (alloc.matchingEdge j)
            else X (alloc.matchingEdge j)) - rho) *
            #(if childSide j = 0 then Y (alloc.matchingEdge j)
              else X (alloc.matchingEdge j)))
    (hrootOutside : ∀ i p, rootImage i ∉ cluster p)
    (hrootOutsideX : ∀ i e, rootImage i ∉ X e)
    (hrootOutsideY : ∀ i e, rootImage i ∉ Y e)
    (hclusterMatching : ∀ p e,
      Disjoint (cluster p) (X e ∪ Y e))
    (hmatchingDisjoint : ∀ e f, e ≠ f →
      Disjoint (X e ∪ Y e) (X f ∪ Y f)) :
    Nonempty (ThreeLayerCopy F G rootImage ∅
      (clusterSupport cluster) (matchingSupport X Y)) := by
  classical
  let endpoint : Fin b → Finset B := fun j ↦
    if childSide j = 0 then Y (alloc.matchingEdge j)
    else X (alloc.matchingEdge j)
  obtain ⟨selection⟩ :=
    exists_branchRootSelection_of_uniform G rho rootImage F.owner cluster
      alloc.levelOneCluster endpoint capacity hunifClusterEndpoint hrho
      hrootClusterDegree alloc.cluster_load hclusterDisjoint
  let candidate : Fin k → Fin 2 → Finset B := fun e side ↦
    if side = 0 then cleanedSide G rho (Y e) (X e)
    else cleanedSide G rho (X e) (Y e)
  have hselectedOutside : ∀ i e side,
      selection.image i ∉ candidate e side := by
    intro i e side hmem
    have hcluster := selection.mem_cluster i
    have hraw : selection.image i ∈ X e ∪ Y e := by
      by_cases hs : side = 0
      · have hc : selection.image i ∈ cleanedSide G rho (Y e) (X e) := by
          simpa [candidate, hs] using hmem
        exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hc).1
      · have hc : selection.image i ∈ cleanedSide G rho (X e) (Y e) := by
          simpa [candidate, hs] using hmem
        exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hc).1
    exact Finset.disjoint_left.mp
      (hclusterMatching (alloc.levelOneCluster i) e) hcluster hraw
  have hcandidateDisjoint : ∀ e f, e ≠ f →
      Disjoint (candidate e 0 ∪ candidate e 1)
        (candidate f 0 ∪ candidate f 1) := by
    intro e f hef
    apply (hmatchingDisjoint e f hef).mono
    · intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · have hc : z ∈ cleanedSide G rho (Y e) (X e) := by
          simpa [candidate] using hz
        exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hc).1
      · have hc : z ∈ cleanedSide G rho (X e) (Y e) := by
          simpa [candidate] using hz
        exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hc).1
    · intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · have hc : z ∈ cleanedSide G rho (Y f) (X f) := by
          simpa [candidate] using hz
        exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hc).1
      · have hc : z ∈ cleanedSide G rho (X f) (Y f) := by
          simpa [candidate] using hz
        exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hc).1
  have hselectedDegree : ∀ j,
      GroupedBranches.groupDeep F.branches alloc.matchingEdge
          (alloc.matchingEdge j) + 1 ≤
        #{w ∈ candidate (alloc.matchingEdge j) (childSide j) |
          G.Adj (selection.image j) w} := by
    intro j
    have htyp := selection.typical_endpoint j
    by_cases hs : childSide j = 0
    · have htyp' : selection.image j ∈ cleanedSide G rho
          (cluster (alloc.levelOneCluster j)) (Y (alloc.matchingEdge j)) := by
        simpa [endpoint, hs] using htyp
      simpa [candidate, hs] using
        card_selectedEndpoint_neighbors_ge G
          (GroupedBranches.groupDeep F.branches alloc.matchingEdge
            (alloc.matchingEdge j) + 1)
          (by simpa [hs] using hunifClusterEndpoint j)
          (hunifMatching (alloc.matchingEdge j)).symm hrho
          (by simpa [hs, Nat.cast_add, Nat.cast_one] using
            hclusterEndpointCap j) htyp'
    · have htyp' : selection.image j ∈ cleanedSide G rho
          (cluster (alloc.levelOneCluster j)) (X (alloc.matchingEdge j)) := by
        simpa [endpoint, hs] using htyp
      simpa [candidate, hs] using
        card_selectedEndpoint_neighbors_ge G
          (GroupedBranches.groupDeep F.branches alloc.matchingEdge
            (alloc.matchingEdge j) + 1)
          (by simpa [hs] using hunifClusterEndpoint j)
          (hunifMatching (alloc.matchingEdge j)) hrho
          (by simpa [hs, Nat.cast_add, Nat.cast_one] using
            hclusterEndpointCap j) htyp'
  have hcross : ∀ e side other, side ≠ other → ∀ z ∈ candidate e side,
      GroupedBranches.groupDeep F.branches alloc.matchingEdge e + 1 ≤
        #{w ∈ candidate e other | G.Adj z w} := by
    intro e side other hne z hz
    rcases OrderedRootedForest.fin_two_eq_zero_or_one side with rfl | rfl <;>
      rcases OrderedRootedForest.fin_two_eq_zero_or_one other with rfl | rfl
    · exact False.elim (hne rfl)
    · simpa [candidate] using card_cleanedSide_neighbors_ge G
        (GroupedBranches.groupDeep F.branches alloc.matchingEdge e + 1)
        (hunifMatching e).symm hrho (by
          simpa [G.edgeDensity_comm (X e) (Y e)] using hmatchCapX e) hz
    · simpa [candidate] using card_cleanedSide_neighbors_ge G
        (GroupedBranches.groupDeep F.branches alloc.matchingEdge e + 1)
        (hunifMatching e) hrho (by
          simpa [Nat.cast_add, Nat.cast_one] using hmatchCapY e) hz
    · exact False.elim (hne rfl)
  obtain ⟨E, hEroot, hEmem⟩ :=
    GroupedBranches.exists_embedding_in_grouped_candidates_oriented F.branches G
      alloc.matchingEdge (fun j ↦ GroupedBranches.orientTo (childSide j))
      selection.image candidate selection.injective
      hselectedOutside hcandidateDisjoint (by
        intro i
        simpa only [GroupedBranches.orientTo_one] using hselectedDegree i) hcross
  have horiginalOutside : ∀ i j a, rootImage i ≠ E.copy j a := by
    intro i j a heq
    by_cases ha : a = F.branches.root j
    · have himage : E.copy j a = selection.image j := by
        simpa [ha] using hEroot j
      apply hrootOutside i (alloc.levelOneCluster j)
      rw [heq, himage]
      exact selection.mem_cluster j
    · have hm := hEmem j a ha
      have hraw : E.copy j a ∈ X (alloc.matchingEdge j) ∪
          Y (alloc.matchingEdge j) := by
        by_cases hs : GroupedBranches.orientTo (childSide j)
            ((F.branches.isTree j).coloringTwoOfVert
              (F.branches.root j) a) = 0
        · have hc : E.copy j a ∈ cleanedSide G rho
              (Y (alloc.matchingEdge j)) (X (alloc.matchingEdge j)) := by
            simpa [candidate, hs] using hm
          exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hc).1
        · have hc : E.copy j a ∈ cleanedSide G rho
              (X (alloc.matchingEdge j)) (Y (alloc.matchingEdge j)) := by
            simpa [candidate, hs] using hm
          exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hc).1
      rcases Finset.mem_union.mp hraw with hx | hy
      · exact hrootOutsideX i (alloc.matchingEdge j) (heq ▸ hx)
      · exact hrootOutsideY i (alloc.matchingEdge j) (heq ▸ hy)
  have hattach : ∀ j,
      G.Adj (rootImage (F.owner j)) (E.copy j (F.branches.root j)) := by
    intro j
    rw [hEroot j]
    exact selection.adj_owner j
  let full := F.copyOfBranchEmbedding G rootImage E hrootInjective
    horiginalOutside hattach
  refine ⟨
    { copy := full
      map_root := ?_
      map_levelOne := ?_
      map_special := ?_
      map_remaining := ?_ }⟩
  · intro i
    rfl
  · intro x hx
    obtain ⟨j, hxj⟩ := (F.mem_levelOne_iff x).mp hx
    subst x
    apply Finset.mem_biUnion.mpr
    refine ⟨alloc.levelOneCluster j, Finset.mem_univ _, ?_⟩
    change E.copy j (F.branches.root j) ∈ cluster (alloc.levelOneCluster j)
    rw [hEroot j]
    exact selection.mem_cluster j
  · intro x hx
    simp at hx
  · intro x hxroot hxlevel _hxspecial
    rcases x with i | z
    · exact False.elim (hxroot (Finset.mem_image.mpr
        ⟨i, Finset.mem_univ _, rfl⟩))
    · rcases z with ⟨j, a⟩
      have hznonroot : a ≠ F.branches.root j := by
        intro hz
        apply hxlevel
        subst a
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      have hm := hEmem j a hznonroot
      apply Finset.mem_biUnion.mpr
      refine ⟨alloc.matchingEdge j, Finset.mem_univ _, ?_⟩
      by_cases hs : GroupedBranches.orientTo (childSide j)
          ((F.branches.isTree j).coloringTwoOfVert
            (F.branches.root j) a) = 0
      · have hc : E.copy j a ∈ cleanedSide G rho
            (Y (alloc.matchingEdge j)) (X (alloc.matchingEdge j)) := by
          simpa [candidate, hs] using hm
        change E.copy j a ∈ X (alloc.matchingEdge j) ∪
          Y (alloc.matchingEdge j)
        exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hc).1
      · have hc : E.copy j a ∈ cleanedSide G rho
            (X (alloc.matchingEdge j)) (Y (alloc.matchingEdge j)) := by
          simpa [candidate, hs] using hm
        change E.copy j a ∈ X (alloc.matchingEdge j) ∪
          Y (alloc.matchingEdge j)
        exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hc).1

/-! ## Aggregate typicality from actual regular pairs -/

/-- Number of cluster pairs in which `z` is an atypical vertex on the common
root side `A`. -/
def atypicalClusterCount
    {B C : Type*} [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (A : Finset B) (cluster : C → Finset B) (z : B) : ℕ :=
  #{C0 : C | z ∈ atypicalVertices G rho A (cluster C0)}

/-- Root images atypical to at least `q` members of the cluster family. -/
def aggregateBadRoots
    {B C : Type*} [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (A : Finset B) (cluster : C → Finset B) (q : ℕ) : Finset B :=
  A.filter fun z ↦ q ≤ atypicalClusterCount G rho A cluster z

/-- Double counting the actual atypical incidences.  This is the aggregate
step behind Zhao's assertion that all but `sqrt epsilon N` root choices are
typical to all but a `sqrt epsilon` fraction of the adjacent cluster family.
-/
theorem card_aggregateBadRoots_mul_threshold_le
    {B C : Type*} [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (A : Finset B) (cluster : C → Finset B)
    (q : ℕ)
    (hunif : ∀ C0, G.IsUniform rho A (cluster C0))
    (hrho : rho ≤ 1) :
    (#(aggregateBadRoots G rho A cluster q) : ℝ) * q ≤
      (Fintype.card C : ℝ) * rho * #A := by
  classical
  let bad : C → Finset B := fun C0 ↦
    atypicalVertices G rho A (cluster C0)
  let count : B → ℕ := fun z ↦ #{C0 : C | z ∈ bad C0}
  have hbadSub (C0 : C) : bad C0 ⊆ A := by
    exact Finset.filter_subset _ _
  have hdouble : ∑ z ∈ A, count z = ∑ C0 : C, #(bad C0) := by
    calc
      ∑ z ∈ A, count z =
          ∑ z ∈ A, ∑ C0 : C, if z ∈ bad C0 then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro z _
            simpa [count] using
              (Finset.card_filter (fun C0 : C ↦ z ∈ bad C0) Finset.univ)
      _ = ∑ C0 : C, ∑ z ∈ A, if z ∈ bad C0 then 1 else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ C0 : C, #(bad C0) := by
            apply Finset.sum_congr rfl
            intro C0 _
            have heq : A.filter (fun z ↦ z ∈ bad C0) = bad C0 := by
              ext z
              simp only [Finset.mem_filter]
              constructor
              · exact fun hz ↦ hz.2
              · exact fun hz ↦ ⟨hbadSub C0 hz, hz⟩
            have hs : (∑ z ∈ A, if z ∈ bad C0 then 1 else 0) =
                #(A.filter (fun z ↦ z ∈ bad C0)) := by
              exact Finset.sum_boole (fun z ↦ z ∈ bad C0) A
            rw [hs, heq]
  have hlowerNat :
      #(aggregateBadRoots G rho A cluster q) * q ≤ ∑ z ∈ A, count z := by
    calc
      #(aggregateBadRoots G rho A cluster q) * q =
          ∑ _z ∈ aggregateBadRoots G rho A cluster q, q := by simp
      _ ≤ ∑ z ∈ aggregateBadRoots G rho A cluster q, count z := by
          apply Finset.sum_le_sum
          intro z hz
          exact (Finset.mem_filter.mp hz).2
      _ ≤ ∑ z ∈ A, count z := by
          apply Finset.sum_le_sum_of_subset
          exact Finset.filter_subset _ _
  have hlowerReal :
      (#(aggregateBadRoots G rho A cluster q) : ℝ) * q ≤
        ∑ C0 : C, (#(bad C0) : ℝ) := by
    exact_mod_cast (hlowerNat.trans_eq hdouble)
  calc
    (#(aggregateBadRoots G rho A cluster q) : ℝ) * q ≤
        ∑ C0 : C, (#(bad C0) : ℝ) := hlowerReal
    _ ≤ ∑ _C0 : C, rho * (#A : ℝ) := by
      apply Finset.sum_le_sum
      intro C0 _
      simpa [bad] using card_atypicalVertices_le G (hunif C0) hrho
    _ = (Fintype.card C : ℝ) * rho * #A := by
      simp [mul_assoc]

/-- Division form of the preceding incidence bound. -/
theorem card_aggregateBadRoots_le
    {B C : Type*} [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (A : Finset B) (cluster : C → Finset B)
    (q : ℕ) (hq : 0 < q)
    (hunif : ∀ C0, G.IsUniform rho A (cluster C0))
    (hrho : rho ≤ 1) :
    (#(aggregateBadRoots G rho A cluster q) : ℝ) ≤
      ((Fintype.card C : ℝ) * rho * #A) / q := by
  apply (le_div_iff₀ (by exact_mod_cast hq)).mpr
  simpa [mul_comm] using
    card_aggregateBadRoots_mul_threshold_le G rho A cluster q hunif hrho

/-! ## Source-shaped flexible aggregate theorem (empty optional set) -/

/-- Zhao Lemma 5.9(2), in the form used by Lemma 6.14 when the optional set
`S` is empty.  All allocations, root choices, grouped matching embeddings,
and the final copy are constructed in the proof.

The natural-number reserve
`b + q * capacityMax ≤ sum capacity` is the integer version of
`|Level1(F)| ≤ deg(A,C) - 2 gamma |C| N`: losing fewer than `q` atypical
clusters still leaves enough Level1 capacity.  The deep budget is literally
`|Level>=2(F)| ≤ m * base`; in the source `base=(1-gamma)N`.
-/
theorem lemma5_9_part2_flexible_emptySpecial
    {r b c k : ℕ} {B : Type*}
    [Fintype B] [DecidableEq B]
    [Nonempty (Fin c)] [Nonempty (Fin k)]
    (F : OrderedBranchForest r b)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (A : Finset B)
    (cluster : Fin c → Finset B) (X Y : Fin k → Finset B)
    (capacity : Fin c → ℕ) (capacityMax : ℕ)
    (allowedEdges : Fin c → Finset (Fin k))
    (accessSide : Fin c → Fin k → Fin 2)
    (m base slack q rootSlack : ℕ)
    (hmpos : 0 < m) (hq : 0 < q)
    (_htreeCount : treeCount F ≤ slack)
    (hlevelOneReserve : levelOneDemand F + q * capacityMax ≤
      ∑ C0 : Fin c, capacity C0)
    (hcapacityMax : ∀ C0, capacity C0 ≤ capacityMax)
    (hsmall : ∀ j : Fin b, F.branches.size j - 1 ≤ slack)
    (hdeep : deepDemand F ≤ m * base)
    (hadjacent : ∀ C0, m ≤ #(allowedEdges C0))
    (hrho : rho ≤ 1)
    (hunifRootCluster : ∀ C0, G.IsUniform rho A (cluster C0))
    (hcapacityRoot : ∀ C0,
      (capacity C0 : ℝ) + rho * #(cluster C0) ≤
        (G.edgeDensity A (cluster C0) - rho) * #(cluster C0))
    (hrootSlack : ((c : ℝ) * rho * #A) / q ≤ rootSlack)
    (hunifAccess : ∀ C0 e, e ∈ allowedEdges C0 →
      G.IsUniform rho (cluster C0)
        (if accessSide C0 e = 0 then Y e else X e))
    (haccessCap : ∀ C0 e, e ∈ allowedEdges C0 →
      ((base + slack + 1 : ℕ) : ℝ) +
          rho * #(if accessSide C0 e = 0 then Y e else X e) ≤
        (G.edgeDensity (cluster C0)
          (if accessSide C0 e = 0 then Y e else X e) - rho) *
            #(if accessSide C0 e = 0 then Y e else X e))
    (hunifMatching : ∀ e, G.IsUniform rho (X e) (Y e))
    (hmatchingCapX : ∀ e,
      ((base + slack + 1 : ℕ) : ℝ) + rho * #(X e) ≤
        (G.edgeDensity (X e) (Y e) - rho) * #(X e))
    (hmatchingCapY : ∀ e,
      ((base + slack + 1 : ℕ) : ℝ) + rho * #(Y e) ≤
        (G.edgeDensity (X e) (Y e) - rho) * #(Y e))
    (hrootClusterDisjoint : ∀ C0, Disjoint A (cluster C0))
    (hrootXDisjoint : ∀ e, Disjoint A (X e))
    (hrootYDisjoint : ∀ e, Disjoint A (Y e))
    (hclusterDisjoint : ∀ C0 D0, C0 ≠ D0 →
      Disjoint (cluster C0) (cluster D0))
    (hclusterMatching : ∀ C0 e,
      Disjoint (cluster C0) (X e ∪ Y e))
    (hmatchingDisjoint : ∀ e f, e ≠ f →
      Disjoint (X e ∪ Y e) (X f ∪ Y f)) :
    Nonempty (FlexibleThreeLayerEmbedding F G A
      (clusterSupport cluster) (matchingSupport X Y) rootSlack 0) := by
  classical
  let badRoots := aggregateBadRoots G rho A cluster q
  have hbadCard : (#badRoots : ℝ) ≤ rootSlack := by
    calc
      (#badRoots : ℝ) ≤ ((c : ℝ) * rho * #A) / q := by
        simpa [badRoots] using
          card_aggregateBadRoots_le G rho A cluster q hq hunifRootCluster hrho
      _ ≤ rootSlack := hrootSlack
  have hbadCardNat : #badRoots ≤ rootSlack := by
    exact_mod_cast hbadCard
  refine ⟨
    { bad := fun _ ↦ badRoots
      bad_subset := ?_
      card_bad := ?_
      realize := ?_ }⟩
  · intro i
    exact Finset.filter_subset _ _
  · intro i
    exact hbadCardNat
  · intro special _hspecial hspecialCard rootImage hrootInj hrootMem hrootGood
    have hspecialEmpty : special = ∅ := by
      apply Finset.card_eq_zero.mp
      omega
    subst special
    let eligible : Fin r → Fin c → Prop := fun i C0 ↦
      rootImage i ∉ atypicalVertices G rho A (cluster C0)
    have hfew (i : Fin r) :
        atypicalClusterCount G rho A cluster (rootImage i) < q := by
      apply Nat.lt_of_not_ge
      intro hqbad
      apply hrootGood i
      exact Finset.mem_filter.mpr ⟨hrootMem i, hqbad⟩
    have hprefix (i : Fin r) :
        #{j : Fin b | F.owner j ≤ i} ≤
          ∑ C0 : Fin c, if eligible i C0 then capacity C0 else 0 := by
      let badC : Finset (Fin c) := Finset.univ.filter fun C0 ↦
        ¬eligible i C0
      have hbadCcard : #badC < q := by
        simpa [badC, eligible, atypicalClusterCount] using hfew i
      have hbadCsum : (∑ C0 ∈ badC, capacity C0) ≤ q * capacityMax := by
        calc
          (∑ C0 ∈ badC, capacity C0) ≤ #badC * capacityMax :=
            Finset.sum_le_card_nsmul badC capacity capacityMax (by
              intro C0 _
              exact hcapacityMax C0)
          _ ≤ q * capacityMax := Nat.mul_le_mul_right capacityMax hbadCcard.le
      have hsplit := Finset.sum_filter_add_sum_filter_not
        (Finset.univ : Finset (Fin c)) (eligible i) capacity
      have hgood : levelOneDemand F ≤
          ∑ C0 : Fin c, if eligible i C0 then capacity C0 else 0 := by
        have hgoodFilter : levelOneDemand F ≤
            ∑ C0 ∈ (Finset.univ : Finset (Fin c)) with eligible i C0,
              capacity C0 := by
          have hbadRewrite :
              (∑ C0 ∈ (Finset.univ : Finset (Fin c)) with ¬eligible i C0,
                capacity C0) = ∑ C0 ∈ badC, capacity C0 := by
            rfl
          rw [hbadRewrite] at hsplit
          have hreserve := hlevelOneReserve
          omega
        simpa [Finset.sum_filter] using hgoodFilter
      exact (Finset.card_le_univ
        (Finset.univ.filter fun j : Fin b ↦ F.owner j ≤ i)).trans
          (by simpa [levelOneDemand] using hgood)
    obtain ⟨alloc, hallocEligible⟩ :=
      exists_eligibleAggregateAllocation F capacity eligible allowedEdges
        m base slack hmpos hprefix hadjacent hsmall hdeep
    let childSide : Fin b → Fin 2 := fun j ↦
      accessSide (alloc.levelOneCluster j) (alloc.matchingEdge j)
    have hgroupLe (e : Fin k) :
        GroupedBranches.groupDeep F.branches alloc.matchingEdge e ≤
          base + slack := by
      simpa [GroupedBranches.groupDeep, Finset.sum_filter] using
        alloc.matching_load e
    have hunifCE (j : Fin b) :
        G.IsUniform rho (cluster (alloc.levelOneCluster j))
          (if childSide j = 0 then Y (alloc.matchingEdge j)
            else X (alloc.matchingEdge j)) := by
      exact hunifAccess (alloc.levelOneCluster j) (alloc.matchingEdge j)
        (alloc.matching_allowed j (Finset.mem_univ _))
    have hrootDegree (j : Fin b) :
        (capacity (alloc.levelOneCluster j) : ℝ) +
            rho * #(cluster (alloc.levelOneCluster j)) ≤
          (#((cluster (alloc.levelOneCluster j)).filter
            (G.Adj (rootImage (F.owner j)))) : ℝ) := by
      have hzA := hrootMem (F.owner j)
      have hzGood := hallocEligible j
      have hraw :
          (G.edgeDensity A (cluster (alloc.levelOneCluster j)) - rho) *
              (#(cluster (alloc.levelOneCluster j)) : ℝ) ≤
            (#((cluster (alloc.levelOneCluster j)).filter
              (G.Adj (rootImage (F.owner j)))) : ℝ) := by
        apply le_of_not_gt
        intro hlt
        apply hzGood
        exact Finset.mem_filter.mpr ⟨hzA, hlt⟩
      exact (hcapacityRoot (alloc.levelOneCluster j)).trans hraw
    have hcapX (e : Fin k) :
        (GroupedBranches.groupDeep F.branches alloc.matchingEdge e + 1 : ℝ) +
            rho * #(X e) ≤
          (G.edgeDensity (X e) (Y e) - rho) * #(X e) := by
      calc
        _ ≤ ((base + slack + 1 : ℕ) : ℝ) + rho * #(X e) := by
          gcongr
          exact_mod_cast Nat.add_le_add_right (hgroupLe e) 1
        _ ≤ _ := hmatchingCapX e
    have hcapY (e : Fin k) :
        (GroupedBranches.groupDeep F.branches alloc.matchingEdge e + 1 : ℝ) +
            rho * #(Y e) ≤
          (G.edgeDensity (X e) (Y e) - rho) * #(Y e) := by
      calc
        _ ≤ ((base + slack + 1 : ℕ) : ℝ) + rho * #(Y e) := by
          gcongr
          exact_mod_cast Nat.add_le_add_right (hgroupLe e) 1
        _ ≤ _ := hmatchingCapY e
    have hcapCE (j : Fin b) :
        (GroupedBranches.groupDeep F.branches alloc.matchingEdge
            (alloc.matchingEdge j) + 1 : ℝ) +
            rho * #(if childSide j = 0 then Y (alloc.matchingEdge j)
              else X (alloc.matchingEdge j)) ≤
          (G.edgeDensity (cluster (alloc.levelOneCluster j))
            (if childSide j = 0 then Y (alloc.matchingEdge j)
              else X (alloc.matchingEdge j)) - rho) *
            #(if childSide j = 0 then Y (alloc.matchingEdge j)
              else X (alloc.matchingEdge j)) := by
      calc
        _ ≤ ((base + slack + 1 : ℕ) : ℝ) +
            rho * #(if childSide j = 0 then Y (alloc.matchingEdge j)
              else X (alloc.matchingEdge j)) := by
          gcongr
          exact_mod_cast Nat.add_le_add_right
            (hgroupLe (alloc.matchingEdge j)) 1
        _ ≤ _ := haccessCap (alloc.levelOneCluster j) (alloc.matchingEdge j)
          (alloc.matching_allowed j (Finset.mem_univ _))
    have hrootOutsideCluster : ∀ i C0, rootImage i ∉ cluster C0 := by
      intro i C0 hz
      exact Finset.disjoint_left.mp (hrootClusterDisjoint C0)
        (hrootMem i) hz
    have hrootOutsideX' : ∀ i e, rootImage i ∉ X e := by
      intro i e hz
      exact Finset.disjoint_left.mp (hrootXDisjoint e) (hrootMem i) hz
    have hrootOutsideY' : ∀ i e, rootImage i ∉ Y e := by
      intro i e hz
      exact Finset.disjoint_left.mp (hrootYDisjoint e) (hrootMem i) hz
    simpa [childSide] using
      exists_threeLayerCopy_emptySpecial_of_allocation F G rho rootImage
        cluster X Y childSide capacity allowedEdges base slack alloc hrootInj
        hrho hunifCE hrootDegree hclusterDisjoint hunifMatching hcapX hcapY
        hcapCE hrootOutsideCluster hrootOutsideX' hrootOutsideY'
        hclusterMatching hmatchingDisjoint

#print axioms Erdos547b.ZhaoLemma59Part2Full.OrderedBranchForest.card_levelGeTwo
#print axioms Erdos547b.ZhaoLemma59Part2Full.OrderedBranchForest.copyOfBranchEmbedding
#print axioms Erdos547b.ZhaoLemma59Part2Full.exists_sourceAggregateAllocation
#print axioms Erdos547b.ZhaoLemma59Part2Full.card_aggregateBadRoots_le
#print axioms Erdos547b.ZhaoLemma59Part2Full.exists_eligibleAggregateAllocation
#print axioms Erdos547b.ZhaoLemma59Part2Full.exists_threeLayerCopy_emptySpecial_of_allocation
#print axioms Erdos547b.ZhaoLemma59Part2Full.lemma5_9_part2_flexible_emptySpecial
#print axioms Erdos547b.ZhaoLemma59Part2Full.FlexibleThreeLayerEmbedding.toZhaoFlexibleEmbedding

end Erdos547b.ZhaoLemma59Part2Full
