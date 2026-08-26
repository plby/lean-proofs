/-
Adapted from the Apache-2.0-licensed polynomial-grid-minor-theorem development,
https://github.com/EdouardBonnet/polynomial-grid-minor-theorem,
commit fe2848173913a00d85c64d2a17af63f2cf0d4fbf,
proofs/Lax17Proofs/Source/MengerDefs.lean.
Local changes: module split, import paths, namespace, and Lean 4.33 compatibility.
-/
import ErdosProblems.Erdos73.Paths

namespace Erdos73Infrastructure

universe u v w

/-!
# Definitions for finite vertex-Menger

This file contains only the proof-facing language for finite vertex-Menger:
`(S,T)`-separators and finite families of pairwise vertex-disjoint `S`-to-`T`
paths. The theorem itself is proved in `Menger.lean`.
-/

namespace SimpleGraph


/-- An oriented endpoint-clean `S`-to-`T` path starts in `S`, ends in `T`,
has no vertex of `S` except its source, and has no vertex of `T` except its
target.

This is the convention used in the self-contained finite Menger proof.  It
handles non-disjoint terminal sets: if a nontrivial path starts in `S ∩ T`,
the right-clean condition forces the first right terminal to be the same
vertex, so the cleaned subpath is trivial. -/
structure GraphPath.EndpointClean {V : Type u} [DecidableEq V]
    {G : _root_.SimpleGraph V} (P : GraphPath G) (S T : Finset V) : Prop where
  source_mem : P.source ∈ S
  target_mem : P.target ∈ T
  left_eq_source :
    ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ S → v = P.source
  right_eq_target :
    ∀ ⦃v : V⦄, v ∈ P.vertexSet → v ∈ T → v = P.target

namespace GraphPath

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T X : Finset V} {P : GraphPath G}

theorem EndpointClean.connects (hP : P.EndpointClean S T) :
    P.Connects S T :=
  Or.inl ⟨hP.source_mem, hP.target_mem⟩

theorem EndpointClean.vertexSet_inter_left_subset_singleton
    (hP : P.EndpointClean S T) :
    P.vertexSet ∩ S ⊆ {P.source} := by
  intro v hv
  exact Finset.mem_singleton.2 (hP.left_eq_source
    (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv).2)

theorem EndpointClean.vertexSet_inter_right_subset_singleton
    (hP : P.EndpointClean S T) :
    P.vertexSet ∩ T ⊆ {P.target} := by
  intro v hv
  exact Finset.mem_singleton.2 (hP.right_eq_target
    (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv).2)

theorem EndpointClean.vertexSet_inter_right_eq_singleton
    (hP : P.EndpointClean S T) :
    P.vertexSet ∩ T = {P.target} := by
  apply Finset.Subset.antisymm hP.vertexSet_inter_right_subset_singleton
  intro v hv
  rw [Finset.mem_singleton] at hv
  subst hv
  exact Finset.mem_inter.2 ⟨GraphPath.target_mem_vertexSet P, hP.target_mem⟩

theorem EndpointClean.internallyDisjointFromRight
    (hP : P.EndpointClean S T) :
    P.InternallyDisjointFromSet T := by
  intro v hv hvT
  exact Or.inr (hP.right_eq_target hv hvT)

theorem EndpointClean.internallyDisjointFromLeft
    (hP : P.EndpointClean S T) :
    P.InternallyDisjointFromSet S := by
  intro v hv hvS
  exact Or.inl (hP.left_eq_source hv hvS)

theorem EndpointClean.right_mem_eq_target
    (hP : P.EndpointClean S T) {v : V}
    (hv : v ∈ P.vertexSet) (hvT : v ∈ T) :
    v = P.target :=
  hP.right_eq_target hv hvT

theorem EndpointClean.left_mem_eq_source
    (hP : P.EndpointClean S T) {v : V}
    (hv : v ∈ P.vertexSet) (hvS : v ∈ S) :
    v = P.source :=
  hP.left_eq_source hv hvS

theorem EndpointClean.source_eq_target_of_source_mem_right
    (hP : P.EndpointClean S T) (hsource : P.source ∈ T) :
    P.source = P.target :=
  hP.right_eq_target (GraphPath.source_mem_vertexSet P) hsource

theorem EndpointClean.source_only_at_target_on_right_subset
    (hP : P.EndpointClean S T) {Q : GraphPath G}
    (hQ : Q.vertexSet ⊆ T) :
    P.source ∈ Q.vertexSet → P.source = P.target := by
  intro hsourceQ
  exact hP.source_eq_target_of_source_mem_right (hQ hsourceQ)

noncomputable def appendWithEqOfEndpointCleanRightSubset
    (P Q : GraphPath G) (hP : P.EndpointClean S T)
    (hQ : Q.vertexSet ⊆ T) (h : P.target = Q.source) :
    GraphPath G :=
  P.appendWithEqOfInternallyDisjointFromSetOfSourceOnlyAtTarget
    Q h hP.internallyDisjointFromRight hQ
    (hP.source_only_at_target_on_right_subset hQ)

@[simp] theorem appendWithEqOfEndpointCleanRightSubset_source
    (P Q : GraphPath G) (hP : P.EndpointClean S T)
    (hQ : Q.vertexSet ⊆ T) (h : P.target = Q.source) :
    (P.appendWithEqOfEndpointCleanRightSubset Q hP hQ h).source = P.source := by
  simp [appendWithEqOfEndpointCleanRightSubset]

@[simp] theorem appendWithEqOfEndpointCleanRightSubset_target
    (P Q : GraphPath G) (hP : P.EndpointClean S T)
    (hQ : Q.vertexSet ⊆ T) (h : P.target = Q.source) :
    (P.appendWithEqOfEndpointCleanRightSubset Q hP hQ h).target = Q.target := by
  simp [appendWithEqOfEndpointCleanRightSubset]

theorem appendWithEqOfEndpointCleanRightSubset_vertexSet_subset
    (P Q : GraphPath G) (hP : P.EndpointClean S T)
    (hQ : Q.vertexSet ⊆ T) (h : P.target = Q.source) :
    (P.appendWithEqOfEndpointCleanRightSubset Q hP hQ h).vertexSet ⊆
      P.vertexSet ∪ Q.vertexSet :=
by
  exact GraphPath.appendWithEq_vertexSet_subset P Q h _

theorem appendWithEqOfEndpointCleanRightSubset_endpointClean
    {U : Finset V} (P Q : GraphPath G) (hP : P.EndpointClean S U)
    (hTU : T ⊆ U) (hQsub : Q.vertexSet ⊆ U)
    (hQtarget : Q.target ∈ T)
    (hQleft : ∀ ⦃v : V⦄, v ∈ Q.vertexSet → v ∈ S → v = P.target)
    (hQright : ∀ ⦃v : V⦄, v ∈ Q.vertexSet → v ∈ T → v = Q.target)
    (hPtarget : P.target ∈ T → P.target = Q.target)
    (h : P.target = Q.source) :
    (P.appendWithEqOfEndpointCleanRightSubset Q hP hQsub h).EndpointClean S T := by
  classical
  let A := P.appendWithEqOfEndpointCleanRightSubset Q hP hQsub h
  have hsub :
      A.vertexSet ⊆ P.vertexSet ∪ Q.vertexSet :=
    P.appendWithEqOfEndpointCleanRightSubset_vertexSet_subset Q hP hQsub h
  refine
    { source_mem := ?_
      target_mem := ?_
      left_eq_source := ?_
      right_eq_target := ?_ }
  · simpa [A] using hP.source_mem
  · simpa [A] using hQtarget
  · intro v hv hvS
    rcases Finset.mem_union.1 (hsub hv) with hvP | hvQ
    · simpa [A] using hP.left_eq_source hvP hvS
    · have hv_target : v = P.target := hQleft hvQ hvS
      have htarget_source : P.target = P.source := by
        exact (hP.left_eq_source (GraphPath.target_mem_vertexSet P)
          (by simpa [hv_target] using hvS))
      simpa [A] using hv_target.trans htarget_source
  · intro v hv hvT
    rcases Finset.mem_union.1 (hsub hv) with hvP | hvQ
    · have hv_target : v = P.target := hP.right_eq_target hvP (hTU hvT)
      simpa [A] using hv_target.trans (hPtarget (by simpa [hv_target] using hvT))
    · simpa [A] using hQright hvQ hvT

theorem nodeDisjoint_appendWithEqOfEndpointCleanRightSubset_left
    {U : Finset V} (P Q W : GraphPath G)
    (hPclean : P.EndpointClean S U) (hWclean : W.EndpointClean S U)
    (hQsub : Q.vertexSet ⊆ U) (h : P.target = Q.source)
    (hPW : P.NodeDisjoint W)
    (hWtarget : W.target ∉ Q.vertexSet) :
    (P.appendWithEqOfEndpointCleanRightSubset Q hPclean hQsub h).NodeDisjoint W := by
  classical
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvA hvW
  have hvA' :=
    P.appendWithEqOfEndpointCleanRightSubset_vertexSet_subset Q hPclean hQsub h hvA
  rcases Finset.mem_union.1 hvA' with hvP | hvQ
  · exact Finset.disjoint_left.mp hPW hvP hvW
  · have hvU : v ∈ U := hQsub hvQ
    have hv_target : v = W.target := hWclean.right_eq_target hvW hvU
    exact hWtarget (by simpa [hv_target] using hvQ)

theorem nodeDisjoint_appendWithEqOfEndpointCleanRightSubset_right
    {U : Finset V} (P Q W : GraphPath G)
    (hPclean : P.EndpointClean S U) (hWclean : W.EndpointClean S U)
    (hQsub : Q.vertexSet ⊆ U) (h : P.target = Q.source)
    (hWP : W.NodeDisjoint P)
    (hWtarget : W.target ∉ Q.vertexSet) :
    W.NodeDisjoint
      (P.appendWithEqOfEndpointCleanRightSubset Q hPclean hQsub h) :=
  (nodeDisjoint_appendWithEqOfEndpointCleanRightSubset_left
    P Q W hPclean hWclean hQsub h hWP.symm hWtarget).symm

theorem nodeDisjoint_appendWithEqOfEndpointCleanRightSubset_append
    {U : Finset V} (P Q R W : GraphPath G)
    (hPclean : P.EndpointClean S U) (hRclean : R.EndpointClean S U)
    (hQsub : Q.vertexSet ⊆ U) (hWsub : W.vertexSet ⊆ U)
    (hPQ : P.target = Q.source) (hRW : R.target = W.source)
    (hPR : P.NodeDisjoint R)
    (hRtargetQ : R.target ∉ Q.vertexSet)
    (hPtargetW : P.target ∉ W.vertexSet)
    (hQW : Disjoint Q.vertexSet W.vertexSet) :
    (P.appendWithEqOfEndpointCleanRightSubset Q hPclean hQsub hPQ).NodeDisjoint
      (R.appendWithEqOfEndpointCleanRightSubset W hRclean hWsub hRW) := by
  classical
  rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
  intro v hvA hvB
  have hvA' :=
    P.appendWithEqOfEndpointCleanRightSubset_vertexSet_subset Q hPclean hQsub hPQ hvA
  have hvB' :=
    R.appendWithEqOfEndpointCleanRightSubset_vertexSet_subset W hRclean hWsub hRW hvB
  rcases Finset.mem_union.1 hvA' with hvP | hvQ
  · rcases Finset.mem_union.1 hvB' with hvR | hvW
    · exact Finset.disjoint_left.mp hPR hvP hvR
    · have hvU : v ∈ U := hWsub hvW
      have hv_target : v = P.target := hPclean.right_eq_target hvP hvU
      exact hPtargetW (by simpa [hv_target] using hvW)
  · rcases Finset.mem_union.1 hvB' with hvR | hvW
    · have hvU : v ∈ U := hQsub hvQ
      have hv_target : v = R.target := hRclean.right_eq_target hvR hvU
      exact hRtargetQ (by simpa [hv_target] using hvQ)
    · exact Finset.disjoint_left.mp hQW hvQ hvW

/-- The standard terminal-cleaning operation produces an oriented
endpoint-clean path. -/
theorem cleanBetweenTerminalSets_endpointClean
    (P : GraphPath G) {S T : Finset V} (h : P.Connects S T) :
    (P.cleanBetweenTerminalSets h).EndpointClean S T := by
  classical
  let O := P.orient h
  let hT : (O.vertexSet ∩ T).Nonempty :=
    ⟨O.target, Finset.mem_inter.2
      ⟨GraphPath.target_mem_vertexSet O,
        GraphPath.orient_target_mem P h⟩⟩
  let R := O.cleanPrefixToSet T hT
  let hS : (R.vertexSet ∩ S).Nonempty :=
    ⟨R.source, Finset.mem_inter.2
      ⟨GraphPath.source_mem_vertexSet R,
        by simpa [R, O] using GraphPath.orient_source_mem P h⟩⟩
  refine
    { source_mem := ?_
      target_mem := ?_
      left_eq_source := ?_
      right_eq_target := ?_ }
  · exact R.cleanSuffixFromSet_source_mem S hS
  · exact O.cleanPrefixToSet_target_mem T hT
  · intro v hv hvS
    have hvSuffix :
        v ∈ (R.cleanSuffixFromSet S hS).vertexSet := by
      simpa [GraphPath.cleanBetweenTerminalSets, O, hT, R, hS] using hv
    have hvlast :
        v = R.lastHitVertex S hS :=
      R.eq_lastHitVertex_of_mem_dropUntil_of_mem_set S hS
        (by simpa [GraphPath.cleanSuffixFromSet] using hvSuffix) hvS
    exact hvlast
  · intro v hv hvT
    have hvSuffix :
        v ∈ (R.cleanSuffixFromSet S hS).vertexSet := by
      simpa [GraphPath.cleanBetweenTerminalSets, O, hT, R, hS] using hv
    have hvR : v ∈ R.vertexSet :=
      R.cleanSuffixFromSet_vertexSet_subset S hS hvSuffix
    have hvfirst :
        v = O.firstHitVertex T hT :=
      O.eq_firstHitVertex_of_mem_takeUntil_of_mem_set T hT
        (by simpa [R, GraphPath.cleanPrefixToSet] using hvR) hvT
    exact hvfirst

/-- The prefix and suffix of a simple path at the same cut vertex meet only at
that cut vertex. -/
theorem eq_of_mem_takeUntil_and_mem_dropUntil
    (P : GraphPath G) {x v : V} (hx : x ∈ P.vertexSet)
    (hvPrefix : v ∈ (P.takeUntil hx).vertexSet)
    (hvSuffix : v ∈ (P.dropUntil hx).vertexSet) :
    v = x := by
  have hvBeforeX : P.Before v x :=
    P.before_of_mem_takeUntil hx hvPrefix
  have hxBeforeV : P.Before x v :=
    ⟨hx, hvSuffix⟩
  exact P.before_antisymm hvBeforeX hxBeforeV

/-- If the cut vertex is not the original target, the prefix ending at that
vertex is a proper subpath on vertices. -/
theorem takeUntil_vertexSet_ssubset_of_ne_target
    (P : GraphPath G) {x : V} (hx : x ∈ P.vertexSet)
    (hne : x ≠ P.target) :
    (P.takeUntil hx).vertexSet ⊂ P.vertexSet := by
  classical
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · exact P.takeUntil_vertexSet_subset hx
  · intro heq
    have htargetPrefix :
        P.target ∈ (P.takeUntil hx).vertexSet := by
      rw [heq]
      exact GraphPath.target_mem_vertexSet P
    have htargetSuffix :
        P.target ∈ (P.dropUntil hx).vertexSet :=
      GraphPath.target_mem_vertexSet (P.dropUntil hx)
    exact hne ((P.eq_of_mem_takeUntil_and_mem_dropUntil hx
      htargetPrefix htargetSuffix).symm)

/-- On the suffix starting at the last vertex of a set, any later vertex that
still lies in the set is the suffix source. -/
theorem eq_source_of_mem_dropUntil_lastHitVertex_of_mem_set
    (P : GraphPath G) (U : Finset V)
    (hne : (P.vertexSet ∩ U).Nonempty) {v : V}
    (hvSuffix :
      v ∈ (P.dropUntil (P.lastHitVertex_mem_vertexSet U hne)).vertexSet)
    (hvU : v ∈ U) :
    v = (P.dropUntil (P.lastHitVertex_mem_vertexSet U hne)).source := by
  dsimp
  exact P.eq_lastHitVertex_of_mem_dropUntil_of_mem_set U hne hvSuffix hvU

theorem EndpointClean.dropUntil_left_eq_source
    (hP : P.EndpointClean S T) {x v : V} (hx : x ∈ P.vertexSet)
    (hv : v ∈ (P.dropUntil hx).vertexSet) (hvS : v ∈ S) :
    v = (P.dropUntil hx).source := by
  have hvOld : v ∈ P.vertexSet := P.dropUntil_vertexSet_subset hx hv
  have hv_source : v = P.source := hP.left_eq_source hvOld hvS
  have hsource_suffix : P.source ∈ (P.dropUntil hx).vertexSet := by
    simpa [hv_source] using hv
  have hsource_x :
      P.source = x :=
    P.eq_of_mem_takeUntil_and_mem_dropUntil hx
      (by
        simpa using GraphPath.source_mem_vertexSet (P.takeUntil hx))
      hsource_suffix
  simpa using hv_source.trans hsource_x

theorem EndpointClean.dropUntil_right_eq_target
    (hP : P.EndpointClean S T) {x v : V} (hx : x ∈ P.vertexSet)
    (hv : v ∈ (P.dropUntil hx).vertexSet) (hvT : v ∈ T) :
    v = (P.dropUntil hx).target := by
  have hvOld : v ∈ P.vertexSet := P.dropUntil_vertexSet_subset hx hv
  simpa using hP.right_eq_target hvOld hvT

end GraphPath

/-- A finite indexed family of pairwise vertex-disjoint oriented endpoint-clean
`S`-to-`T` paths.  This is the proof-facing path-system object for Diestel's
augmentation proof of finite Menger.

The public theorem still uses `PathPacking`; an endpoint-clean system converts
to a `PathPacking` by forgetting the orientation-cleaning data. -/
structure EndpointCleanPathPacking {V : Type u} [DecidableEq V]
    (G : _root_.SimpleGraph V) (S T : Finset V) where
  Index : Type
  [indexFintype : Fintype Index]
  [indexDecidableEq : DecidableEq Index]
  path : Index → GraphPath G
  endpoint_clean : ∀ i, (path i).EndpointClean S T
  node_disjoint : Pairwise fun i j => GraphPath.NodeDisjoint (path i) (path j)

namespace EndpointCleanPathPacking

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T : Finset V}

instance (P : EndpointCleanPathPacking G S T) : Fintype P.Index :=
  P.indexFintype

instance (P : EndpointCleanPathPacking G S T) : DecidableEq P.Index :=
  P.indexDecidableEq

/-- The number of paths in an endpoint-clean path system. -/
noncomputable def card (P : EndpointCleanPathPacking G S T) : ℕ :=
  Fintype.card P.Index

/-- The union of the vertices used by all paths in the system. -/
noncomputable def vertexSet (P : EndpointCleanPathPacking G S T) : Finset V :=
  Finset.univ.biUnion fun i : P.Index => (P.path i).vertexSet

theorem mem_vertexSet (P : EndpointCleanPathPacking G S T) {v : V} :
    v ∈ P.vertexSet ↔ ∃ i : P.Index, v ∈ (P.path i).vertexSet := by
  classical
  simp [vertexSet]

theorem path_vertexSet_subset_vertexSet
    (P : EndpointCleanPathPacking G S T) (i : P.Index) :
    (P.path i).vertexSet ⊆ P.vertexSet := by
  classical
  intro v hv
  exact (P.mem_vertexSet).2 ⟨i, hv⟩

theorem exists_index_of_mem_vertexSet
    (P : EndpointCleanPathPacking G S T) {v : V}
    (hv : v ∈ P.vertexSet) :
    ∃ i : P.Index, v ∈ (P.path i).vertexSet :=
  (P.mem_vertexSet).1 hv

/-- The empty endpoint-clean path system. -/
abbrev empty (G : _root_.SimpleGraph V) (S T : Finset V) :
    EndpointCleanPathPacking G S T where
  Index := Empty
  path := fun i => nomatch i
  endpoint_clean := by
    intro i
    cases i
  node_disjoint := by
    intro i
    cases i

@[simp] theorem empty_card :
    (empty G S T).card = 0 := by
  exact Fintype.card_of_isEmpty

/-- Adjoin one endpoint-clean path that is vertex-disjoint from the old
system. -/
noncomputable abbrev cons (P : EndpointCleanPathPacking G S T)
    (R : GraphPath G) (hR : R.EndpointClean S T)
    (hdisj : Disjoint R.vertexSet P.vertexSet) :
    EndpointCleanPathPacking G S T where
  Index := Option P.Index
  path := fun i =>
    match i with
    | none => R
    | some j => P.path j
  endpoint_clean := by
    intro i
    cases i with
    | none => exact hR
    | some j => exact P.endpoint_clean j
  node_disjoint := by
    intro i j hij
    cases i with
    | none =>
        cases j with
        | none => exact False.elim (hij rfl)
        | some j =>
            rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
            intro v hvR hvj
            exact Finset.disjoint_left.mp hdisj hvR
              (P.path_vertexSet_subset_vertexSet j hvj)
    | some i =>
        cases j with
        | none =>
            rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
            intro v hvi hvR
            exact Finset.disjoint_left.mp hdisj hvR
              (P.path_vertexSet_subset_vertexSet i hvi)
        | some j =>
            exact P.node_disjoint (by
              intro hij'
              apply hij
              simp [hij'])

@[simp] theorem cons_card (P : EndpointCleanPathPacking G S T)
    (R : GraphPath G) (hR : R.EndpointClean S T)
    (hdisj : Disjoint R.vertexSet P.vertexSet) :
    (P.cons R hR hdisj).card = P.card + 1 := by
  change Fintype.card (Option P.Index) = Fintype.card P.Index + 1
  exact Fintype.card_option

/-- Rebuild a path system on the same index type from a new path assignment.
This is a small constructor used by splicing arguments. -/
noncomputable abbrev withSameIndex {T' : Finset V}
    (P : EndpointCleanPathPacking G S T) (f : P.Index → GraphPath G)
    (hclean : ∀ i, (f i).EndpointClean S T')
    (hnode : Pairwise fun i j => GraphPath.NodeDisjoint (f i) (f j)) :
    EndpointCleanPathPacking G S T' where
  Index := P.Index
  path := f
  endpoint_clean := hclean
  node_disjoint := hnode

@[simp] theorem withSameIndex_card {T' : Finset V}
    (P : EndpointCleanPathPacking G S T) (f : P.Index → GraphPath G)
    (hclean : ∀ i, (f i).EndpointClean S T')
    (hnode : Pairwise fun i j => GraphPath.NodeDisjoint (f i) (f j)) :
    (P.withSameIndex f hclean hnode).card = P.card := by
  change Fintype.card P.Index = Fintype.card P.Index
  rfl

/-!
The next constructor is the formal splice used in Diestel's Menger proof.
It starts with a path system whose paths are endpoint-clean for a larger
right-terminal set `U`.  Two selected paths have right endpoints in `U \ T`;
we append tails contained in `U` that end in the smaller terminal set `T`.
All other paths are required to already end in `T` and to have endpoints
outside the appended tails.  Endpoint-cleanliness relative to `U` then gives
the disjointness of the spliced family.
-/

noncomputable abbrev spliceTwo {U : Finset V}
    (P : EndpointCleanPathPacking G S U)
    (i₀ i₁ : P.Index) (hidx : i₀ ≠ i₁)
    (tail₀ tail₁ : GraphPath G)
    (hTU : T ⊆ U)
    (htail₀U : tail₀.vertexSet ⊆ U)
    (htail₁U : tail₁.vertexSet ⊆ U)
    (htail₀T : tail₀.target ∈ T)
    (htail₁T : tail₁.target ∈ T)
    (htail₀Left :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ S → v = (P.path i₀).target)
    (htail₁Left :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ S → v = (P.path i₁).target)
    (htail₀Right :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ T → v = tail₀.target)
    (htail₁Right :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ T → v = tail₁.target)
    (hjoin₀Target : (P.path i₀).target ∈ T → (P.path i₀).target = tail₀.target)
    (hjoin₁Target : (P.path i₁).target ∈ T → (P.path i₁).target = tail₁.target)
    (hjoin₀ : (P.path i₀).target = tail₀.source)
    (hjoin₁ : (P.path i₁).target = tail₁.source)
    (hotherTargetT :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ → (P.path j).target ∈ T)
    (hotherTargetNotTail₀ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₀.vertexSet)
    (hotherTargetNotTail₁ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₁.vertexSet)
    (hi₁TargetNotTail₀ : (P.path i₁).target ∉ tail₀.vertexSet)
    (hi₀TargetNotTail₁ : (P.path i₀).target ∉ tail₁.vertexSet)
    (htails : Disjoint tail₀.vertexSet tail₁.vertexSet) :
    EndpointCleanPathPacking G S T := by
  classical
  let A₀ : GraphPath G :=
    (P.path i₀).appendWithEqOfEndpointCleanRightSubset
      tail₀ (P.endpoint_clean i₀) htail₀U hjoin₀
  let A₁ : GraphPath G :=
    (P.path i₁).appendWithEqOfEndpointCleanRightSubset
      tail₁ (P.endpoint_clean i₁) htail₁U hjoin₁
  let f : P.Index → GraphPath G := fun i =>
    if hi₀ : i = i₀ then A₀ else if hi₁ : i = i₁ then A₁ else P.path i
  refine P.withSameIndex f ?_ ?_
  · intro i
    by_cases hi₀ : i = i₀
    · subst i
      simpa [f, A₀] using
        GraphPath.appendWithEqOfEndpointCleanRightSubset_endpointClean
          (P.path i₀) tail₀ (P.endpoint_clean i₀) hTU htail₀U htail₀T
          htail₀Left htail₀Right hjoin₀Target hjoin₀
    · by_cases hi₁ : i = i₁
      · subst i
        simpa [f, hi₀, A₁] using
          GraphPath.appendWithEqOfEndpointCleanRightSubset_endpointClean
            (P.path i₁) tail₁ (P.endpoint_clean i₁) hTU htail₁U htail₁T
            htail₁Left htail₁Right hjoin₁Target hjoin₁
      · refine
          { source_mem := ?_
            target_mem := ?_
            left_eq_source := ?_
            right_eq_target := ?_ }
        · have hf : f i = P.path i := by simp [f, hi₀, hi₁]
          simpa [hf] using (P.endpoint_clean i).source_mem
        · have hf : f i = P.path i := by simp [f, hi₀, hi₁]
          simpa [hf] using hotherTargetT i hi₀ hi₁
        · intro v hv hvS
          have hf : f i = P.path i := by simp [f, hi₀, hi₁]
          simpa [hf] using
            (P.endpoint_clean i).left_eq_source (by simpa [hf] using hv) hvS
        · intro v hv hvT
          have hf : f i = P.path i := by simp [f, hi₀, hi₁]
          simpa [hf] using
            (P.endpoint_clean i).right_eq_target (by simpa [hf] using hv) (hTU hvT)
  · intro i j hij
    by_cases hi₀ : i = i₀
    · subst i
      by_cases hj₀ : j = i₀
      · exact False.elim (hij hj₀.symm)
      · by_cases hj₁ : j = i₁
        · subst j
          simpa [f, A₀, A₁, hj₀, hidx.symm] using
            GraphPath.nodeDisjoint_appendWithEqOfEndpointCleanRightSubset_append
              (P.path i₀) tail₀ (P.path i₁) tail₁
              (P.endpoint_clean i₀) (P.endpoint_clean i₁)
              htail₀U htail₁U hjoin₀ hjoin₁
              (P.node_disjoint hidx) hi₁TargetNotTail₀
              hi₀TargetNotTail₁ htails
        · simpa [f, A₀, hj₀, hj₁] using
            GraphPath.nodeDisjoint_appendWithEqOfEndpointCleanRightSubset_left
              (P.path i₀) tail₀ (P.path j)
              (P.endpoint_clean i₀) (P.endpoint_clean j)
              htail₀U hjoin₀
              (P.node_disjoint (by
                intro h
                exact hj₀ h.symm))
              (hotherTargetNotTail₀ j hj₀ hj₁)
    · by_cases hi₁ : i = i₁
      · subst i
        by_cases hj₀ : j = i₀
        · subst j
          simpa [f, A₀, A₁, hi₀, hidx] using
            GraphPath.nodeDisjoint_appendWithEqOfEndpointCleanRightSubset_append
              (P.path i₁) tail₁ (P.path i₀) tail₀
              (P.endpoint_clean i₁) (P.endpoint_clean i₀)
              htail₁U htail₀U hjoin₁ hjoin₀
              (P.node_disjoint hidx.symm) hi₀TargetNotTail₁
              hi₁TargetNotTail₀ htails.symm
        · by_cases hj₁ : j = i₁
          · exact False.elim (hij hj₁.symm)
          · simpa [f, A₁, hi₀, hj₀, hj₁] using
              GraphPath.nodeDisjoint_appendWithEqOfEndpointCleanRightSubset_left
                (P.path i₁) tail₁ (P.path j)
                (P.endpoint_clean i₁) (P.endpoint_clean j)
                htail₁U hjoin₁
                (P.node_disjoint (by
                  intro h
                  exact hj₁ h.symm))
                (hotherTargetNotTail₁ j hj₀ hj₁)
      · by_cases hj₀ : j = i₀
        · subst j
          simpa [f, A₀, hi₀, hi₁] using
            GraphPath.nodeDisjoint_appendWithEqOfEndpointCleanRightSubset_right
              (P.path i₀) tail₀ (P.path i)
              (P.endpoint_clean i₀) (P.endpoint_clean i)
              htail₀U hjoin₀
              (P.node_disjoint (by
                intro h
                exact hi₀ h))
              (hotherTargetNotTail₀ i hi₀ hi₁)
        · by_cases hj₁ : j = i₁
          · subst j
            simpa [f, A₁, hi₀, hi₁, hidx.symm] using
              GraphPath.nodeDisjoint_appendWithEqOfEndpointCleanRightSubset_right
                (P.path i₁) tail₁ (P.path i)
                (P.endpoint_clean i₁) (P.endpoint_clean i)
                htail₁U hjoin₁
                (P.node_disjoint (by
                  intro h
                  exact hi₁ h))
                (hotherTargetNotTail₁ i hi₀ hi₁)
          · simpa [f, hi₀, hi₁, hj₀, hj₁] using P.node_disjoint hij

@[simp] theorem spliceTwo_card {U : Finset V}
    (P : EndpointCleanPathPacking G S U)
    (i₀ i₁ : P.Index) (hidx : i₀ ≠ i₁)
    (tail₀ tail₁ : GraphPath G)
    (hTU : T ⊆ U)
    (htail₀U : tail₀.vertexSet ⊆ U)
    (htail₁U : tail₁.vertexSet ⊆ U)
    (htail₀T : tail₀.target ∈ T)
    (htail₁T : tail₁.target ∈ T)
    (htail₀Left :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ S → v = (P.path i₀).target)
    (htail₁Left :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ S → v = (P.path i₁).target)
    (htail₀Right :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ T → v = tail₀.target)
    (htail₁Right :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ T → v = tail₁.target)
    (hjoin₀Target : (P.path i₀).target ∈ T → (P.path i₀).target = tail₀.target)
    (hjoin₁Target : (P.path i₁).target ∈ T → (P.path i₁).target = tail₁.target)
    (hjoin₀ : (P.path i₀).target = tail₀.source)
    (hjoin₁ : (P.path i₁).target = tail₁.source)
    (hotherTargetT :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ → (P.path j).target ∈ T)
    (hotherTargetNotTail₀ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₀.vertexSet)
    (hotherTargetNotTail₁ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₁.vertexSet)
    (hi₁TargetNotTail₀ : (P.path i₁).target ∉ tail₀.vertexSet)
    (hi₀TargetNotTail₁ : (P.path i₀).target ∉ tail₁.vertexSet)
    (htails : Disjoint tail₀.vertexSet tail₁.vertexSet) :
    (P.spliceTwo i₀ i₁ hidx tail₀ tail₁ hTU htail₀U htail₁U
      htail₀T htail₁T htail₀Left htail₁Left htail₀Right htail₁Right
      hjoin₀Target hjoin₁Target hjoin₀ hjoin₁ hotherTargetT
      hotherTargetNotTail₀ hotherTargetNotTail₁ hi₁TargetNotTail₀
      hi₀TargetNotTail₁ htails).card = P.card := by
  change Fintype.card P.Index = Fintype.card P.Index
  rfl

theorem spliceTwo_target_left {U : Finset V}
    (P : EndpointCleanPathPacking G S U)
    (i₀ i₁ : P.Index) (hidx : i₀ ≠ i₁)
    (tail₀ tail₁ : GraphPath G)
    (hTU : T ⊆ U)
    (htail₀U : tail₀.vertexSet ⊆ U)
    (htail₁U : tail₁.vertexSet ⊆ U)
    (htail₀T : tail₀.target ∈ T)
    (htail₁T : tail₁.target ∈ T)
    (htail₀Left :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ S → v = (P.path i₀).target)
    (htail₁Left :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ S → v = (P.path i₁).target)
    (htail₀Right :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ T → v = tail₀.target)
    (htail₁Right :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ T → v = tail₁.target)
    (hjoin₀Target : (P.path i₀).target ∈ T → (P.path i₀).target = tail₀.target)
    (hjoin₁Target : (P.path i₁).target ∈ T → (P.path i₁).target = tail₁.target)
    (hjoin₀ : (P.path i₀).target = tail₀.source)
    (hjoin₁ : (P.path i₁).target = tail₁.source)
    (hotherTargetT :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ → (P.path j).target ∈ T)
    (hotherTargetNotTail₀ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₀.vertexSet)
    (hotherTargetNotTail₁ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₁.vertexSet)
    (hi₁TargetNotTail₀ : (P.path i₁).target ∉ tail₀.vertexSet)
    (hi₀TargetNotTail₁ : (P.path i₀).target ∉ tail₁.vertexSet)
    (htails : Disjoint tail₀.vertexSet tail₁.vertexSet) :
    ((P.spliceTwo i₀ i₁ hidx tail₀ tail₁ hTU htail₀U htail₁U
      htail₀T htail₁T htail₀Left htail₁Left htail₀Right htail₁Right
      hjoin₀Target hjoin₁Target hjoin₀ hjoin₁ hotherTargetT
      hotherTargetNotTail₀ hotherTargetNotTail₁ hi₁TargetNotTail₀
      hi₀TargetNotTail₁ htails).path i₀).target = tail₀.target := by
  classical
  simp [spliceTwo, withSameIndex]

theorem spliceTwo_target_right {U : Finset V}
    (P : EndpointCleanPathPacking G S U)
    (i₀ i₁ : P.Index) (hidx : i₀ ≠ i₁)
    (tail₀ tail₁ : GraphPath G)
    (hTU : T ⊆ U)
    (htail₀U : tail₀.vertexSet ⊆ U)
    (htail₁U : tail₁.vertexSet ⊆ U)
    (htail₀T : tail₀.target ∈ T)
    (htail₁T : tail₁.target ∈ T)
    (htail₀Left :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ S → v = (P.path i₀).target)
    (htail₁Left :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ S → v = (P.path i₁).target)
    (htail₀Right :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ T → v = tail₀.target)
    (htail₁Right :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ T → v = tail₁.target)
    (hjoin₀Target : (P.path i₀).target ∈ T → (P.path i₀).target = tail₀.target)
    (hjoin₁Target : (P.path i₁).target ∈ T → (P.path i₁).target = tail₁.target)
    (hjoin₀ : (P.path i₀).target = tail₀.source)
    (hjoin₁ : (P.path i₁).target = tail₁.source)
    (hotherTargetT :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ → (P.path j).target ∈ T)
    (hotherTargetNotTail₀ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₀.vertexSet)
    (hotherTargetNotTail₁ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₁.vertexSet)
    (hi₁TargetNotTail₀ : (P.path i₁).target ∉ tail₀.vertexSet)
    (hi₀TargetNotTail₁ : (P.path i₀).target ∉ tail₁.vertexSet)
    (htails : Disjoint tail₀.vertexSet tail₁.vertexSet) :
    ((P.spliceTwo i₀ i₁ hidx tail₀ tail₁ hTU htail₀U htail₁U
      htail₀T htail₁T htail₀Left htail₁Left htail₀Right htail₁Right
      hjoin₀Target hjoin₁Target hjoin₀ hjoin₁ hotherTargetT
      hotherTargetNotTail₀ hotherTargetNotTail₁ hi₁TargetNotTail₀
      hi₀TargetNotTail₁ htails).path i₁).target = tail₁.target := by
  classical
  simp [spliceTwo, withSameIndex, hidx.symm]

theorem spliceTwo_target_other {U : Finset V}
    (P : EndpointCleanPathPacking G S U)
    (i₀ i₁ j : P.Index) (hidx : i₀ ≠ i₁)
    (hj₀ : j ≠ i₀) (hj₁ : j ≠ i₁)
    (tail₀ tail₁ : GraphPath G)
    (hTU : T ⊆ U)
    (htail₀U : tail₀.vertexSet ⊆ U)
    (htail₁U : tail₁.vertexSet ⊆ U)
    (htail₀T : tail₀.target ∈ T)
    (htail₁T : tail₁.target ∈ T)
    (htail₀Left :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ S → v = (P.path i₀).target)
    (htail₁Left :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ S → v = (P.path i₁).target)
    (htail₀Right :
      ∀ ⦃v : V⦄, v ∈ tail₀.vertexSet → v ∈ T → v = tail₀.target)
    (htail₁Right :
      ∀ ⦃v : V⦄, v ∈ tail₁.vertexSet → v ∈ T → v = tail₁.target)
    (hjoin₀Target : (P.path i₀).target ∈ T → (P.path i₀).target = tail₀.target)
    (hjoin₁Target : (P.path i₁).target ∈ T → (P.path i₁).target = tail₁.target)
    (hjoin₀ : (P.path i₀).target = tail₀.source)
    (hjoin₁ : (P.path i₁).target = tail₁.source)
    (hotherTargetT :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ → (P.path j).target ∈ T)
    (hotherTargetNotTail₀ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₀.vertexSet)
    (hotherTargetNotTail₁ :
      ∀ j : P.Index, j ≠ i₀ → j ≠ i₁ →
        (P.path j).target ∉ tail₁.vertexSet)
    (hi₁TargetNotTail₀ : (P.path i₁).target ∉ tail₀.vertexSet)
    (hi₀TargetNotTail₁ : (P.path i₀).target ∉ tail₁.vertexSet)
    (htails : Disjoint tail₀.vertexSet tail₁.vertexSet) :
    ((P.spliceTwo i₀ i₁ hidx tail₀ tail₁ hTU htail₀U htail₁U
      htail₀T htail₁T htail₀Left htail₁Left htail₀Right htail₁Right
      hjoin₀Target hjoin₁Target hjoin₀ hjoin₁ hotherTargetT
      hotherTargetNotTail₀ hotherTargetNotTail₁ hi₁TargetNotTail₀
      hi₀TargetNotTail₁ htails).path j).target = (P.path j).target := by
  classical
  simp [spliceTwo, withSameIndex, hj₀, hj₁]

/-- Replace one path by a new endpoint-clean path contained in the old path,
possibly after changing the right terminal set.  The endpoint-clean hypotheses
for the unchanged paths are explicit because Diestel's proof enlarges the
target set in a way that must be verified geometrically. -/
noncomputable abbrev replacePath {T' : Finset V}
    (P : EndpointCleanPathPacking G S T) (i₀ : P.Index)
    (Q : GraphPath G) (hQ : Q.EndpointClean S T')
    (hold : ∀ i : P.Index, i ≠ i₀ → (P.path i).EndpointClean S T')
    (hsub : Q.vertexSet ⊆ (P.path i₀).vertexSet) :
    EndpointCleanPathPacking G S T' where
  Index := P.Index
  path := fun i => if i = i₀ then Q else P.path i
  endpoint_clean := by
    intro i
    by_cases hi : i = i₀
    · simpa [hi]
    · simpa [hi] using hold i hi
  node_disjoint := by
    intro i j hij
    by_cases hi : i = i₀
    · by_cases hj : j = i₀
      · exact False.elim (hij (hi.trans hj.symm))
      · rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
        intro v hvQ hvj
        exact Finset.disjoint_left.mp
          (P.node_disjoint (by
            intro h
            exact hj h.symm))
          (hsub (by simpa [hi] using hvQ))
          (by simpa [hj] using hvj)
    · by_cases hj : j = i₀
      · rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
        intro v hvi hvQ
        exact Finset.disjoint_left.mp
          (P.node_disjoint (by
            intro h
            exact hi h))
          (by simpa [hi] using hvi)
          (hsub (by simpa [hj] using hvQ))
      · simpa [hi, hj] using P.node_disjoint hij

@[simp] theorem replacePath_card {T' : Finset V}
    (P : EndpointCleanPathPacking G S T) (i₀ : P.Index)
    (Q : GraphPath G) (hQ : Q.EndpointClean S T')
    (hold : ∀ i : P.Index, i ≠ i₀ → (P.path i).EndpointClean S T')
    (hsub : Q.vertexSet ⊆ (P.path i₀).vertexSet) :
    (P.replacePath i₀ Q hQ hold hsub).card = P.card := by
  change Fintype.card P.Index = Fintype.card P.Index
  rfl

theorem replacePath_vertexSet_subset {T' : Finset V}
    (P : EndpointCleanPathPacking G S T) (i₀ : P.Index)
    (Q : GraphPath G) (hQ : Q.EndpointClean S T')
    (hold : ∀ i : P.Index, i ≠ i₀ → (P.path i).EndpointClean S T')
    (hsub : Q.vertexSet ⊆ (P.path i₀).vertexSet) :
    (P.replacePath i₀ Q hQ hold hsub).vertexSet ⊆ P.vertexSet := by
  classical
  intro v hv
  rcases ((P.replacePath i₀ Q hQ hold hsub).mem_vertexSet).1 hv with
    ⟨i, hvi⟩
  by_cases hi : i = i₀
  · have hviQ : v ∈ Q.vertexSet := by
      change v ∈ (if i = i₀ then Q else P.path i).vertexSet at hvi
      simpa [hi] using hvi
    exact (P.mem_vertexSet).2 ⟨i₀, hsub hviQ⟩
  · have hviOld : v ∈ (P.path i).vertexSet := by
      change v ∈ (if i = i₀ then Q else P.path i).vertexSet at hvi
      simpa [hi] using hvi
    exact (P.mem_vertexSet).2 ⟨i, hviOld⟩

theorem replacePath_vertexSet_ssubset {T' : Finset V}
    (P : EndpointCleanPathPacking G S T) (i₀ : P.Index)
    (Q : GraphPath G) (hQ : Q.EndpointClean S T')
    (hold : ∀ i : P.Index, i ≠ i₀ → (P.path i).EndpointClean S T')
    (hsub : Q.vertexSet ⊆ (P.path i₀).vertexSet)
    (hproper : Q.vertexSet ⊂ (P.path i₀).vertexSet) :
    (P.replacePath i₀ Q hQ hold hsub).vertexSet ⊂ P.vertexSet := by
  classical
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · exact P.replacePath_vertexSet_subset i₀ Q hQ hold hsub
  · intro heq
    have hnotSubset : ¬ (P.path i₀).vertexSet ⊆ Q.vertexSet := by
      intro hrev
      exact (Finset.ssubset_iff_subset_ne.mp hproper).2
        (Finset.Subset.antisymm hsub hrev)
    rw [Finset.not_subset] at hnotSubset
    rcases hnotSubset with ⟨y, hyOld, hyQ⟩
    have hyP : y ∈ P.vertexSet := (P.mem_vertexSet).2 ⟨i₀, hyOld⟩
    have hyNew :
        y ∈ (P.replacePath i₀ Q hQ hold hsub).vertexSet := by
      rw [heq]
      exact hyP
    rcases ((P.replacePath i₀ Q hQ hold hsub).mem_vertexSet).1 hyNew with
      ⟨j, hyj⟩
    by_cases hj : j = i₀
    · have hyQ' : y ∈ Q.vertexSet := by
        change y ∈ (if j = i₀ then Q else P.path j).vertexSet at hyj
        simpa [hj] using hyj
      exact hyQ hyQ'
    · have hyOldj : y ∈ (P.path j).vertexSet := by
        change y ∈ (if j = i₀ then Q else P.path j).vertexSet at hyj
        simpa [hj] using hyj
      exact Finset.disjoint_left.mp
        (P.node_disjoint (by
          intro h
          exact hj h.symm))
        hyOld hyOldj

end EndpointCleanPathPacking

end SimpleGraph

end Erdos73Infrastructure

