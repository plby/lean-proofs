/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayEndpointCoveredClaim2
import ErdosProblems.Erdos599.HalfwayGroupedContactTransaction

/-!
# Contact segmentation with endpoint-covered pieces

The original `ContactPiece` has only two constructors: a genuinely safe
outside piece and a piece wholly contained in the closing set.  Cutting a
safe alternating route at a reference contact produces a third case: a
piece which is not safe only because a newly exposed endpoint is covered by
the reference warp.

This file gives that third case a transaction semantics.  A classified
piece contributes a shortcut only in the genuine Claim-2 case.  A covered
piece contributes no shortcut: its forward edges are already present in the
literal real relation, and its backward reference edges are deleted.  The
resulting shortcut relation is an injectively indexed subchain, so its
bi-uniqueness, acyclicity, and reverse-ray exclusion are proved directly.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating
open Alternating.RelationDecomposition

universe u v

variable {V : Type u}
variable {Gamma : DWeb V} {Y closureFamily : Set Gamma.DPath}
variable {X before innerRoof outerRoof : Set V}
variable {kappa : Cardinal.{u}}

/-- A finite occurrence interval equipped with the positive endpoint-covered
classification.  The forward-edge field records the exact adapter into the
ambient literal real relation. -/
structure ClassifiedFiniteContactPiece
    (Q : AltPath Gamma.graph) (X : Set V) (u v : V) where
  path : AltPath Gamma.graph
  starts_at : path.initial = u
  ends_at : path.terminal? = some v
  classification : FiniteSegmentClassification
    (Y := Y) (X := X) (kappa := kappa) path u v
  forwardEdges_subset_original :
    path.directionEdges .forward ⊆ Q.directionEdges .forward
  vertexSet_subset_original : path.vertexSet ⊆ Q.vertexSet
  edgeSet_subset_original : path.edgeSet ⊆ Q.edgeSet

namespace ClassifiedFiniteContactPiece

variable {Q : AltPath Gamma.graph} {u v : V}

/-- Only a genuine Claim-2 classification creates a contact shortcut. -/
def shortcutEdges
    (P : ClassifiedFiniteContactPiece
      (Y := Y) (kappa := kappa) Q X u v) : Set (V × V) :=
  match P.classification with
  | .imaginary _ => {(u, v)}
  | .initialCovered _ => ∅
  | .terminalCovered _ => ∅

/-- The full contribution of one classified piece before merging with the
global real base. -/
def retainedEdges
    (P : ClassifiedFiniteContactPiece
      (Y := Y) (kappa := kappa) Q X u v) : Set (V × V) :=
  P.classification.retainedEdges

theorem mem_shortcutEdges_eq
    (P : ClassifiedFiniteContactPiece
      (Y := Y) (kappa := kappa) Q X u v)
    {e : V × V} (he : e ∈ P.shortcutEdges) : e = (u, v) := by
  cases hC : P.classification with
  | imaginary _ => simpa [shortcutEdges, hC] using he
  | initialCovered _ => simp [shortcutEdges, hC] at he
  | terminalCovered _ => simp [shortcutEdges, hC] at he

theorem shortcutEdges_subset_imaginaryGraph
    (P : ClassifiedFiniteContactPiece
      (Y := Y) (kappa := kappa) Q X u v) :
    P.shortcutEdges ⊆
      {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  cases hC : P.classification with
  | imaginary h =>
      rintro e he
      have heq : e = (u, v) := P.mem_shortcutEdges_eq he
      subst e
      exact Or.inr h
  | initialCovered _ => simp [shortcutEdges, hC]
  | terminalCovered _ => simp [shortcutEdges, hC]

/-- Exact merge law for one piece.  A covered piece is absorbed by the
ambient forward relation; an imaginary piece is its singleton shortcut. -/
theorem retainedEdges_subset_originalForward_union_shortcut
    (P : ClassifiedFiniteContactPiece
      (Y := Y) (kappa := kappa) Q X u v) :
    P.retainedEdges ⊆ Q.directionEdges .forward ∪ P.shortcutEdges := by
  cases hC : P.classification with
  | imaginary _ =>
      intro e he
      exact Or.inr (by simpa [retainedEdges, shortcutEdges, hC] using he)
  | initialCovered _ =>
      intro e he
      exact Or.inl (P.forwardEdges_subset_original (by
        simpa [retainedEdges, hC] using he))
  | terminalCovered _ =>
      intro e he
      exact Or.inl (P.forwardEdges_subset_original (by
        simpa [retainedEdges, hC] using he))

end ClassifiedFiniteContactPiece

/-- An infinite final occurrence interval.  A genuine Claim-2 branch marks
its initial vertex popular and contributes no edge.  A covered branch retains
only its forward edges through the ambient real relation. -/
structure ClassifiedInfiniteContactTail
    (Q : AltPath Gamma.graph) (X : Set V) (persistent : Set V) (u : V) where
  path : AltPath Gamma.graph
  starts_at : path.initial = u
  infinite : path.IsInfinite
  classification : InfiniteSegmentClassification
    (Y := Y) (X := X) (kappa := kappa) persistent path u
  forwardEdges_subset_original :
    path.directionEdges .forward ⊆ Q.directionEdges .forward
  vertexSet_subset_original : path.vertexSet ⊆ Q.vertexSet
  edgeSet_subset_original : path.edgeSet ⊆ Q.edgeSet

namespace ClassifiedInfiniteContactTail

variable {Q : AltPath Gamma.graph} {persistent : Set V} {u : V}

/-- An infinite tail contributes only already-present forward real edges in
the covered branch.  Popularity is vertex data, not a shortcut edge. -/
def retainedEdges
    (T : ClassifiedInfiniteContactTail
      (Y := Y) (kappa := kappa) Q X persistent u) : Set (V × V) :=
  match T.classification with
  | .popular _ => ∅
  | .initialCovered _ => T.path.directionEdges .forward

theorem retainedEdges_subset_originalForward
    (T : ClassifiedInfiniteContactTail
      (Y := Y) (kappa := kappa) Q X persistent u) :
    T.retainedEdges ⊆ Q.directionEdges .forward := by
  cases hC : T.classification with
  | popular _ => simpa [retainedEdges, hC] using
      (Set.empty_subset (Q.directionEdges .forward))
  | initialCovered _ => simpa [retainedEdges, hC] using
      T.forwardEdges_subset_original

end ClassifiedInfiniteContactTail

/-! ## A generic injectively indexed classified contact chain -/

/-- The finite pieces of any finite or omega contact decomposition.  This
abstraction isolates all relation-level facts from the concrete splitter. -/
structure ClassifiedContactChain
    (Q : AltPath Gamma.graph) (X : Set V) (I J : Type v) where
  point : J → V
  index_nonempty : Nonempty J
  point_injective : Function.Injective point
  source : I → J
  target : I → J
  source_injective : Function.Injective source
  target_injective : Function.Injective target
  indexRank : J → Nat
  rank_step : ∀ i, indexRank (source i) < indexRank (target i)
  piece : ∀ i, ClassifiedFiniteContactPiece
    (Y := Y) (kappa := kappa) Q X (point (source i)) (point (target i))

namespace ClassifiedContactChain

variable {Q : AltPath Gamma.graph} {I J : Type v}

def contactSet
    (C : ClassifiedContactChain (Y := Y) (kappa := kappa) Q X I J) : Set V :=
  Set.range C.point

def shortcutEdges
    (C : ClassifiedContactChain (Y := Y) (kappa := kappa) Q X I J) :
    Set (V × V) :=
  ⋃ i, (C.piece i).shortcutEdges

noncomputable def contactRank
    (C : ClassifiedContactChain (Y := Y) (kappa := kappa) Q X I J) : V → Nat :=
  by
    letI : Nonempty J := C.index_nonempty
    exact fun x ↦ C.indexRank (Function.invFun C.point x)

theorem mem_shortcutEdges_eq
    (C : ClassifiedContactChain (Y := Y) (kappa := kappa) Q X I J)
    {e : V × V} (he : e ∈ C.shortcutEdges) :
    ∃ i, e = (C.point (C.source i), C.point (C.target i)) := by
  simp only [shortcutEdges, Set.mem_iUnion] at he
  obtain ⟨i, he⟩ := he
  exact ⟨i, (C.piece i).mem_shortcutEdges_eq he⟩

theorem endpoints_mem_contactSet
    (C : ClassifiedContactChain (Y := Y) (kappa := kappa) Q X I J)
    {e : V × V} (he : e ∈ C.shortcutEdges) :
    e.1 ∈ C.contactSet ∧ e.2 ∈ C.contactSet := by
  obtain ⟨i, rfl⟩ := C.mem_shortcutEdges_eq he
  exact ⟨⟨C.source i, rfl⟩, ⟨C.target i, rfl⟩⟩

theorem shortcutEdges_subset_imaginaryGraph
    (C : ClassifiedContactChain (Y := Y) (kappa := kappa) Q X I J) :
    C.shortcutEdges ⊆
      {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  intro e he
  simp only [shortcutEdges, Set.mem_iUnion] at he
  obtain ⟨i, he⟩ := he
  exact (C.piece i).shortcutEdges_subset_imaginaryGraph he

theorem contactRank_lt_of_mem_shortcutEdges
    (C : ClassifiedContactChain (Y := Y) (kappa := kappa) Q X I J)
    {x y : V} (hxy : (x, y) ∈ C.shortcutEdges) :
    C.contactRank x < C.contactRank y := by
  letI : Nonempty J := C.index_nonempty
  obtain ⟨i, hpair⟩ := C.mem_shortcutEdges_eq hxy
  have hx : x = C.point (C.source i) := congrArg Prod.fst hpair
  have hy : y = C.point (C.target i) := congrArg Prod.snd hpair
  subst x
  subst y
  simp only [contactRank]
  rw [Function.leftInverse_invFun C.point_injective,
    Function.leftInverse_invFun C.point_injective]
  exact C.rank_step i

theorem shortcutEdges_biUnique
    (C : ClassifiedContactChain (Y := Y) (kappa := kappa) Q X I J) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ C.shortcutEdges) := by
  constructor
  · intro a b c hac hbc
    obtain ⟨i, hi⟩ := C.mem_shortcutEdges_eq hac
    obtain ⟨j, hj⟩ := C.mem_shortcutEdges_eq hbc
    have htargetPoint : C.point (C.target i) = C.point (C.target j) := by
      exact (congrArg Prod.snd hi).symm.trans (congrArg Prod.snd hj)
    have hij : i = j := C.target_injective
      (C.point_injective htargetPoint)
    subst j
    exact (congrArg Prod.fst hi).trans (congrArg Prod.fst hj).symm
  · intro a b c hab hac
    obtain ⟨i, hi⟩ := C.mem_shortcutEdges_eq hab
    obtain ⟨j, hj⟩ := C.mem_shortcutEdges_eq hac
    have hsourcePoint : C.point (C.source i) = C.point (C.source j) := by
      exact (congrArg Prod.fst hi).symm.trans (congrArg Prod.fst hj)
    have hij : i = j := C.source_injective
      (C.point_injective hsourcePoint)
    subst j
    exact (congrArg Prod.snd hi).trans (congrArg Prod.snd hj).symm

theorem shortcutEdges_acyclic
    (C : ClassifiedContactChain (Y := Y) (kappa := kappa) Q X I J) :
    ¬ ContainsDirectedCycle C.shortcutEdges :=
  Alternating.GenericSimultaneousSwitch.not_containsDirectedCycle_of_wellFoundedRank C.shortcutEdges C.contactRank
    C.contactRank_lt_of_mem_shortcutEdges

theorem shortcutEdges_no_reverse_ray
    (C : ClassifiedContactChain (Y := Y) (kappa := kappa) Q X I J) :
    ¬ ContainsReverseDirectedRay C.shortcutEdges :=
  Alternating.GenericSimultaneousSwitch.not_containsReverseDirectedRay_of_wellFoundedRank C.shortcutEdges C.contactRank
    C.contactRank_lt_of_mem_shortcutEdges

end ClassifiedContactChain

/-! ## Canonical finite and omega chains -/

/-- A finite classified contact decomposition. -/
structure FiniteClassifiedContactSegmentation
    (Q : AltPath Gamma.graph) (X : Set V) where
  count : ℕ
  point : Fin (count + 1) → V
  point_injective : Function.Injective point
  piece : (i : Fin count) → ClassifiedFiniteContactPiece
    (Y := Y) (kappa := kappa) Q X (point i.castSucc) (point i.succ)
  initial_eq : point ⟨0, Nat.zero_lt_succ _⟩ = Q.initial
  terminal_eq : Q.terminal? = some (point ⟨count, Nat.lt_succ_self _⟩)
  vertexSet_exact : Q.vertexSet =
    Set.range point ∪ ⋃ i, (piece i).path.vertexSet
  edgeSet_exact : Q.edgeSet = ⋃ i, (piece i).path.edgeSet

namespace FiniteClassifiedContactSegmentation

variable {Q : AltPath Gamma.graph}

def toChain
    (S : FiniteClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X) :
    ClassifiedContactChain (Y := Y) (kappa := kappa) Q X
      (Fin S.count) (Fin (S.count + 1)) where
  point := S.point
  index_nonempty := inferInstance
  point_injective := S.point_injective
  source := Fin.castSucc
  target := Fin.succ
  source_injective := Fin.castSucc_injective _
  target_injective := Fin.succ_injective _
  indexRank := fun i ↦ i.1
  rank_step := fun i ↦ Fin.castSucc_lt_succ
  piece := S.piece

end FiniteClassifiedContactSegmentation

/-- An infinite decomposition with finitely many finite pieces and one
classified infinite tail. -/
structure EventuallyClassifiedContactSegmentation
    (Q : AltPath Gamma.graph) (X : Set V) (persistent : Set V) where
  count : ℕ
  point : Fin (count + 1) → V
  point_injective : Function.Injective point
  piece : (i : Fin count) → ClassifiedFiniteContactPiece
    (Y := Y) (kappa := kappa) Q X (point i.castSucc) (point i.succ)
  tail : ClassifiedInfiniteContactTail
    (Y := Y) (kappa := kappa) Q X persistent
      (point ⟨count, Nat.lt_succ_self _⟩)
  initial_eq : point ⟨0, Nat.zero_lt_succ _⟩ = Q.initial
  vertexSet_exact : Q.vertexSet =
    Set.range point ∪ (⋃ i, (piece i).path.vertexSet) ∪ tail.path.vertexSet
  edgeSet_exact : Q.edgeSet =
    (⋃ i, (piece i).path.edgeSet) ∪ tail.path.edgeSet

namespace EventuallyClassifiedContactSegmentation

variable {Q : AltPath Gamma.graph} {persistent : Set V}

def toChain
    (S : EventuallyClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent) :
    ClassifiedContactChain (Y := Y) (kappa := kappa) Q X
      (Fin S.count) (Fin (S.count + 1)) where
  point := S.point
  index_nonempty := inferInstance
  point_injective := S.point_injective
  source := Fin.castSucc
  target := Fin.succ
  source_injective := Fin.castSucc_injective _
  target_injective := Fin.succ_injective _
  indexRank := fun i ↦ i.1
  rank_step := fun i ↦ Fin.castSucc_lt_succ
  piece := S.piece

end EventuallyClassifiedContactSegmentation

/-- An infinite decomposition with an omega chain of finite classified
pieces. -/
structure OmegaClassifiedContactSegmentation
    (Q : AltPath Gamma.graph) (X : Set V) where
  point : ℕ → V
  point_injective : Function.Injective point
  piece : (i : ℕ) → ClassifiedFiniteContactPiece
    (Y := Y) (kappa := kappa) Q X (point i) (point (i + 1))
  initial_eq : point 0 = Q.initial
  vertexSet_exact : Q.vertexSet =
    Set.range point ∪ ⋃ i, (piece i).path.vertexSet
  edgeSet_exact : Q.edgeSet = ⋃ i, (piece i).path.edgeSet

namespace OmegaClassifiedContactSegmentation

variable {Q : AltPath Gamma.graph}

def toChain
    (S : OmegaClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X) :
    ClassifiedContactChain (Y := Y) (kappa := kappa) Q X ℕ ℕ where
  point := S.point
  index_nonempty := inferInstance
  point_injective := S.point_injective
  source := id
  target := Nat.succ
  source_injective := Function.injective_id
  target_injective := fun _ _ h ↦ Nat.succ.inj h
  indexRank := id
  rank_step := Nat.lt_succ_self
  piece := by
    intro i
    simpa [Nat.succ_eq_add_one] using S.piece i

end OmegaClassifiedContactSegmentation

/-- The three trace-shape outputs of a classified contact splitter. -/
inductive ClassifiedContactSegmentation
    (Q : AltPath Gamma.graph) (X : Set V) (persistent : Set V)
  | finite : FiniteClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X →
      ClassifiedContactSegmentation Q X persistent
  | eventually : EventuallyClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent →
      ClassifiedContactSegmentation Q X persistent
  | omega : OmegaClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X →
      ClassifiedContactSegmentation Q X persistent

namespace ClassifiedContactSegmentation

variable {Q : AltPath Gamma.graph} {persistent : Set V}

def contactSet
    (S : ClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent) : Set V :=
  match S with
  | .finite T => T.toChain.contactSet
  | .eventually T => T.toChain.contactSet
  | .omega T => T.toChain.contactSet

def shortcutEdges
    (S : ClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent) : Set (V × V) :=
  match S with
  | .finite T => T.toChain.shortcutEdges
  | .eventually T => T.toChain.shortcutEdges
  | .omega T => T.toChain.shortcutEdges

noncomputable def contactRank
    (S : ClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent) : V → Nat :=
  match S with
  | .finite T => T.toChain.contactRank
  | .eventually T => T.toChain.contactRank
  | .omega T => T.toChain.contactRank

theorem contactSet_subset_vertexSet
    (S : ClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent) :
    S.contactSet ⊆ Q.vertexSet := by
  intro x hx
  cases S with
  | finite T =>
      rw [T.vertexSet_exact]
      exact Or.inl hx
  | eventually T =>
      rw [T.vertexSet_exact]
      exact Or.inl (Or.inl hx)
  | omega T =>
      rw [T.vertexSet_exact]
      exact Or.inl hx

theorem shortcutEdges_subset_imaginaryGraph
    (S : ClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent) :
    S.shortcutEdges ⊆
      {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  cases S with
  | finite T => exact T.toChain.shortcutEdges_subset_imaginaryGraph
  | eventually T => exact T.toChain.shortcutEdges_subset_imaginaryGraph
  | omega T => exact T.toChain.shortcutEdges_subset_imaginaryGraph

theorem endpoints_mem_contactSet
    (S : ClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent)
    {e : V × V} (he : e ∈ S.shortcutEdges) :
    e.1 ∈ S.contactSet ∧ e.2 ∈ S.contactSet := by
  cases S with
  | finite T => exact T.toChain.endpoints_mem_contactSet he
  | eventually T => exact T.toChain.endpoints_mem_contactSet he
  | omega T => exact T.toChain.endpoints_mem_contactSet he

theorem contactRank_lt_of_mem_shortcutEdges
    (S : ClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent)
    {x y : V} (hxy : (x, y) ∈ S.shortcutEdges) :
    S.contactRank x < S.contactRank y := by
  cases S with
  | finite T => exact T.toChain.contactRank_lt_of_mem_shortcutEdges hxy
  | eventually T => exact T.toChain.contactRank_lt_of_mem_shortcutEdges hxy
  | omega T => exact T.toChain.contactRank_lt_of_mem_shortcutEdges hxy

theorem shortcutEdges_biUnique
    (S : ClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ S.shortcutEdges) := by
  cases S with
  | finite T => exact T.toChain.shortcutEdges_biUnique
  | eventually T => exact T.toChain.shortcutEdges_biUnique
  | omega T => exact T.toChain.shortcutEdges_biUnique

theorem shortcutEdges_acyclic
    (S : ClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent) :
    ¬ ContainsDirectedCycle S.shortcutEdges :=
  Alternating.GenericSimultaneousSwitch.not_containsDirectedCycle_of_wellFoundedRank S.shortcutEdges S.contactRank
    S.contactRank_lt_of_mem_shortcutEdges

theorem shortcutEdges_no_reverse_ray
    (S : ClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent) :
    ¬ ContainsReverseDirectedRay S.shortcutEdges :=
  Alternating.GenericSimultaneousSwitch.not_containsReverseDirectedRay_of_wellFoundedRank S.shortcutEdges S.contactRank
    S.contactRank_lt_of_mem_shortcutEdges

end ClassifiedContactSegmentation

/-! ## Grouped family wrapper -/

/-- Classified contact chains grouped by recombined macro owner.  Common
contacts must have a common group; bi-uniqueness and rank are then proved in
that one concatenated group rather than at the raw fractured-source level. -/
structure GroupedClassifiedContactSegmentedAssignment
    {Z : Set Gamma.DPath} (A : SimultaneousAssignment Z Y)
    (X persistent : Set V) (G : Type v) where
  segmentation : ∀ s, ClassifiedContactSegmentation
    (Y := Y) (kappa := kappa) (A.assigned s) X persistent
  group : {z : V // z ∈ Gamma.initialSet Z \ Gamma.initialSet Y} → G
  contact_groups_agree : ∀ s t x,
    x ∈ (segmentation s).contactSet →
    x ∈ (segmentation t).contactSet → group s = group t
  grouped_biunique : ∀ g,
    Relator.BiUnique (fun x y ↦ ∃ s, group s = g ∧
      (x, y) ∈ (segmentation s).shortcutEdges)
  localRank : G → V → Nat
  localRank_step : ∀ s {x y},
    (x, y) ∈ (segmentation s).shortcutEdges →
      localRank (group s) x < localRank (group s) y

namespace GroupedClassifiedContactSegmentedAssignment

variable {Z : Set Gamma.DPath} {A : SimultaneousAssignment Z Y}
variable {persistent : Set V} {G : Type v}

def edge
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G) : Set (V × V) :=
  ⋃ s, (S.segmentation s).shortcutEdges

def contactCarrier
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G) : Set V :=
  {x | ∃ e ∈ S.edge, e.1 = x ∨ e.2 = x}

theorem edge_subset_imaginaryGraph
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G) :
    S.edge ⊆ {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  intro e he
  simp only [edge, Set.mem_iUnion] at he
  obtain ⟨s, he⟩ := he
  exact (S.segmentation s).shortcutEdges_subset_imaginaryGraph he

theorem endpoints_mem_contactCarrier
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (e : V × V) (he : e ∈ S.edge) :
    e.1 ∈ S.contactCarrier ∧ e.2 ∈ S.contactCarrier :=
  ⟨⟨e, he, Or.inl rfl⟩, ⟨e, he, Or.inr rfl⟩⟩

theorem edge_biUnique
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ S.edge) := by
  constructor
  · intro a b c hac hbc
    simp only [edge, Set.mem_iUnion] at hac hbc
    obtain ⟨s, hac⟩ := hac
    obtain ⟨t, hbc⟩ := hbc
    have hcs := (S.segmentation s).endpoints_mem_contactSet hac |>.2
    have hct := (S.segmentation t).endpoints_mem_contactSet hbc |>.2
    have hgroup := S.contact_groups_agree s t c hcs hct
    exact (S.grouped_biunique (S.group s)).1
      ⟨s, rfl, hac⟩ ⟨t, hgroup.symm, hbc⟩
  · intro a b c hab hac
    simp only [edge, Set.mem_iUnion] at hab hac
    obtain ⟨s, hab⟩ := hab
    obtain ⟨t, hac⟩ := hac
    have has := (S.segmentation s).endpoints_mem_contactSet hab |>.1
    have hat := (S.segmentation t).endpoints_mem_contactSet hac |>.1
    have hgroup := S.contact_groups_agree s t a has hat
    exact (S.grouped_biunique (S.group s)).2
      ⟨s, rfl, hab⟩ ⟨t, hgroup.symm, hac⟩

noncomputable def contactGroup
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G) (x : V) : Option G := by
  classical
  exact if h : ∃ s, x ∈ (S.segmentation s).contactSet then
    some (S.group (Classical.choose h))
  else none

theorem contactGroup_eq_some_of_mem
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (s : {z : V // z ∈ Gamma.initialSet Z \ Gamma.initialSet Y})
    {x : V} (hx : x ∈ (S.segmentation s).contactSet) :
    S.contactGroup x = some (S.group s) := by
  rw [contactGroup, dif_pos ⟨s, hx⟩]
  congr 1
  exact S.contact_groups_agree (Classical.choose
    (show ∃ t, x ∈ (S.segmentation t).contactSet from ⟨s, hx⟩)) s x
      (Classical.choose_spec
        (show ∃ t, x ∈ (S.segmentation t).contactSet from ⟨s, hx⟩)) hx

noncomputable def rank
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G) (x : V) : Nat :=
  match S.contactGroup x with
  | none => 0
  | some g => S.localRank g x

theorem rank_lt_of_mem_edge
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    {x y : V} (hxy : (x, y) ∈ S.edge) : S.rank x < S.rank y := by
  simp only [edge, Set.mem_iUnion] at hxy
  obtain ⟨s, hxy⟩ := hxy
  have hx := (S.segmentation s).endpoints_mem_contactSet hxy |>.1
  have hy := (S.segmentation s).endpoints_mem_contactSet hxy |>.2
  simp only [rank, S.contactGroup_eq_some_of_mem s hx,
    S.contactGroup_eq_some_of_mem s hy]
  exact S.localRank_step s hxy

theorem edge_acyclic
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G) :
    ¬ ContainsDirectedCycle S.edge :=
  Alternating.GenericSimultaneousSwitch.not_containsDirectedCycle_of_wellFoundedRank S.edge S.rank S.rank_lt_of_mem_edge

theorem edge_no_reverse_ray
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G) :
    ¬ ContainsReverseDirectedRay S.edge :=
  Alternating.GenericSimultaneousSwitch.not_containsReverseDirectedRay_of_wellFoundedRank S.edge S.rank S.rank_lt_of_mem_edge

end GroupedClassifiedContactSegmentedAssignment

end LinkageBlueprint
end Blueprint
end Erdos599

