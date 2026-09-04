/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClassifiedContactSegmentation

/-!
# Classified contact segmentation with closed finite pieces

Two consecutive contacts of a compressed traversal can be joined by an edge
which lies wholly in the closed set.  Such a piece has no outside Claim-2
classification and must not create a shortcut.  It does, however, retain its
literal forward edges in the real base.

This module adds a parallel mixed hierarchy and leaves the existing
classified-only hierarchy unchanged.  Shortcut membership in the new
hierarchy always comes from a genuine `ClassifiedFiniteContactPiece`; closed
pieces contribute the empty shortcut set.
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
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {X : Set V} {kappa : Cardinal.{u}}

/-- A finite contact interval lying wholly in the closed set.  Only its
literal forward edges survive; it carries no imaginary shortcut. -/
structure ClosedFiniteContactPiece
    (Q : AltPath Gamma.graph) (X : Set V) (u v : V) where
  path : AltPath Gamma.graph
  starts_at : path.initial = u
  ends_at : path.terminal? = some v
  contained : path.vertexSet ⊆ X
  forwardEdges_subset_original :
    path.directionEdges .forward ⊆ Q.directionEdges .forward
  vertexSet_subset_original : path.vertexSet ⊆ Q.vertexSet
  edgeSet_subset_original : path.edgeSet ⊆ Q.edgeSet

/-- A genuine classified outside piece or a piece wholly contained in the
closed set. -/
inductive ClassifiedOrClosedFiniteContactPiece
    (Q : AltPath Gamma.graph) (X : Set V) (u v : V) : Type u
  | classified : ClassifiedFiniteContactPiece
      (Y := Y) (kappa := kappa) Q X u v →
      ClassifiedOrClosedFiniteContactPiece Q X u v
  | closed : ClosedFiniteContactPiece Q X u v →
      ClassifiedOrClosedFiniteContactPiece Q X u v

namespace ClassifiedOrClosedFiniteContactPiece

variable {Q : AltPath Gamma.graph} {u v : V}

def path
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := Y) (kappa := kappa) Q X u v) : AltPath Gamma.graph :=
  match P with
  | .classified C => C.path
  | .closed C => C.path

theorem starts_at
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := Y) (kappa := kappa) Q X u v) :
    P.path.initial = u := by
  cases P with
  | classified C => exact C.starts_at
  | closed C => exact C.starts_at

theorem ends_at
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := Y) (kappa := kappa) Q X u v) :
    P.path.terminal? = some v := by
  cases P with
  | classified C => exact C.ends_at
  | closed C => exact C.ends_at

theorem forwardEdges_subset_original
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := Y) (kappa := kappa) Q X u v) :
    P.path.directionEdges .forward ⊆ Q.directionEdges .forward := by
  cases P with
  | classified C => exact C.forwardEdges_subset_original
  | closed C => exact C.forwardEdges_subset_original

theorem vertexSet_subset_original
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := Y) (kappa := kappa) Q X u v) :
    P.path.vertexSet ⊆ Q.vertexSet := by
  cases P with
  | classified C => exact C.vertexSet_subset_original
  | closed C => exact C.vertexSet_subset_original

theorem edgeSet_subset_original
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := Y) (kappa := kappa) Q X u v) :
    P.path.edgeSet ⊆ Q.edgeSet := by
  cases P with
  | classified C => exact C.edgeSet_subset_original
  | closed C => exact C.edgeSet_subset_original

/-- Only the classified constructor can contribute a shortcut. -/
def shortcutEdges
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := Y) (kappa := kappa) Q X u v) : Set (V × V) :=
  match P with
  | .classified C => C.shortcutEdges
  | .closed _ => ∅

/-- Closed pieces retain their literal forward edges. -/
def retainedEdges
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := Y) (kappa := kappa) Q X u v) : Set (V × V) :=
  match P with
  | .classified C => C.retainedEdges
  | .closed C => C.path.directionEdges .forward

theorem classified_of_mem_shortcutEdges
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := Y) (kappa := kappa) Q X u v)
    {e : V × V} (he : e ∈ P.shortcutEdges) :
    ∃ C : ClassifiedFiniteContactPiece
        (Y := Y) (kappa := kappa) Q X u v,
      P = .classified C ∧ e ∈ C.shortcutEdges := by
  cases P with
  | classified C => exact ⟨C, rfl, he⟩
  | closed C => simp [shortcutEdges] at he

theorem mem_shortcutEdges_eq
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := Y) (kappa := kappa) Q X u v)
    {e : V × V} (he : e ∈ P.shortcutEdges) : e = (u, v) := by
  obtain ⟨C, _hP, heC⟩ := P.classified_of_mem_shortcutEdges he
  exact C.mem_shortcutEdges_eq heC

theorem shortcutEdges_subset_imaginaryGraph
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := Y) (kappa := kappa) Q X u v) :
    P.shortcutEdges ⊆
      {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  intro e he
  obtain ⟨C, _hP, heC⟩ := P.classified_of_mem_shortcutEdges he
  exact C.shortcutEdges_subset_imaginaryGraph heC

theorem retainedEdges_subset_originalForward_union_shortcut
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := Y) (kappa := kappa) Q X u v) :
    P.retainedEdges ⊆ Q.directionEdges .forward ∪ P.shortcutEdges := by
  cases P with
  | classified C =>
      exact C.retainedEdges_subset_originalForward_union_shortcut
  | closed C =>
      intro e he
      exact Or.inl (C.forwardEdges_subset_original he)

theorem closed_contained
    {C : ClosedFiniteContactPiece Q X u v} :
    (ClassifiedOrClosedFiniteContactPiece.closed
      (Y := Y) (kappa := kappa) C).path.vertexSet ⊆ X :=
  C.contained

end ClassifiedOrClosedFiniteContactPiece

/-! ## Mixed contact chains -/

structure ClosedClassifiedContactChain
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
  piece : ∀ i, ClassifiedOrClosedFiniteContactPiece
    (Y := Y) (kappa := kappa) Q X (point (source i)) (point (target i))

namespace ClosedClassifiedContactChain

variable {Q : AltPath Gamma.graph} {I J : Type v}

def contactSet
    (C : ClosedClassifiedContactChain
      (Y := Y) (kappa := kappa) Q X I J) : Set V :=
  Set.range C.point

def shortcutEdges
    (C : ClosedClassifiedContactChain
      (Y := Y) (kappa := kappa) Q X I J) : Set (V × V) :=
  ⋃ i, (C.piece i).shortcutEdges

def retainedEdges
    (C : ClosedClassifiedContactChain
      (Y := Y) (kappa := kappa) Q X I J) : Set (V × V) :=
  ⋃ i, (C.piece i).retainedEdges

noncomputable def contactRank
    (C : ClosedClassifiedContactChain
      (Y := Y) (kappa := kappa) Q X I J) : V → Nat := by
  letI : Nonempty J := C.index_nonempty
  exact fun x ↦ C.indexRank (Function.invFun C.point x)

theorem mem_shortcutEdges_eq
    (C : ClosedClassifiedContactChain
      (Y := Y) (kappa := kappa) Q X I J)
    {e : V × V} (he : e ∈ C.shortcutEdges) :
    ∃ i, e = (C.point (C.source i), C.point (C.target i)) := by
  simp only [shortcutEdges, Set.mem_iUnion] at he
  obtain ⟨i, he⟩ := he
  exact ⟨i, (C.piece i).mem_shortcutEdges_eq he⟩

theorem endpoints_mem_contactSet
    (C : ClosedClassifiedContactChain
      (Y := Y) (kappa := kappa) Q X I J)
    {e : V × V} (he : e ∈ C.shortcutEdges) :
    e.1 ∈ C.contactSet ∧ e.2 ∈ C.contactSet := by
  obtain ⟨i, rfl⟩ := C.mem_shortcutEdges_eq he
  exact ⟨⟨C.source i, rfl⟩, ⟨C.target i, rfl⟩⟩

theorem shortcutEdges_subset_imaginaryGraph
    (C : ClosedClassifiedContactChain
      (Y := Y) (kappa := kappa) Q X I J) :
    C.shortcutEdges ⊆
      {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  intro e he
  simp only [shortcutEdges, Set.mem_iUnion] at he
  obtain ⟨i, he⟩ := he
  exact (C.piece i).shortcutEdges_subset_imaginaryGraph he

theorem retainedEdges_subset_originalForward_union_shortcut
    (C : ClosedClassifiedContactChain
      (Y := Y) (kappa := kappa) Q X I J) :
    C.retainedEdges ⊆ Q.directionEdges .forward ∪ C.shortcutEdges := by
  intro e he
  simp only [retainedEdges, Set.mem_iUnion] at he
  obtain ⟨i, he⟩ := he
  rcases (C.piece i).retainedEdges_subset_originalForward_union_shortcut he with
      heForward | heShortcut
  · exact Or.inl heForward
  · exact Or.inr (Set.mem_iUnion.2 ⟨i, heShortcut⟩)

theorem contactRank_lt_of_mem_shortcutEdges
    (C : ClosedClassifiedContactChain
      (Y := Y) (kappa := kappa) Q X I J)
    {x y : V} (hxy : (x, y) ∈ C.shortcutEdges) :
    C.contactRank x < C.contactRank y := by
  let : Nonempty J := C.index_nonempty
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
    (C : ClosedClassifiedContactChain
      (Y := Y) (kappa := kappa) Q X I J) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ C.shortcutEdges) := by
  constructor
  · intro a b c hac hbc
    obtain ⟨i, hi⟩ := C.mem_shortcutEdges_eq hac
    obtain ⟨j, hj⟩ := C.mem_shortcutEdges_eq hbc
    have ht : C.point (C.target i) = C.point (C.target j) :=
      (congrArg Prod.snd hi).symm.trans (congrArg Prod.snd hj)
    have hij : i = j := C.target_injective (C.point_injective ht)
    subst j
    exact (congrArg Prod.fst hi).trans (congrArg Prod.fst hj).symm
  · intro a b c hab hac
    obtain ⟨i, hi⟩ := C.mem_shortcutEdges_eq hab
    obtain ⟨j, hj⟩ := C.mem_shortcutEdges_eq hac
    have hs : C.point (C.source i) = C.point (C.source j) :=
      (congrArg Prod.fst hi).symm.trans (congrArg Prod.fst hj)
    have hij : i = j := C.source_injective (C.point_injective hs)
    subst j
    exact (congrArg Prod.snd hi).trans (congrArg Prod.snd hj).symm

theorem shortcutEdges_acyclic
    (C : ClosedClassifiedContactChain
      (Y := Y) (kappa := kappa) Q X I J) :
    ¬ ContainsDirectedCycle C.shortcutEdges :=
  Alternating.GenericSimultaneousSwitch.not_containsDirectedCycle_of_wellFoundedRank
    C.shortcutEdges C.contactRank C.contactRank_lt_of_mem_shortcutEdges

theorem shortcutEdges_no_reverse_ray
    (C : ClosedClassifiedContactChain
      (Y := Y) (kappa := kappa) Q X I J) :
    ¬ ContainsReverseDirectedRay C.shortcutEdges :=
  Alternating.GenericSimultaneousSwitch.not_containsReverseDirectedRay_of_wellFoundedRank
    C.shortcutEdges C.contactRank C.contactRank_lt_of_mem_shortcutEdges

end ClosedClassifiedContactChain

/-! ## The three mixed segmentation shapes -/

structure FiniteClosedClassifiedContactSegmentation
    (Q : AltPath Gamma.graph) (X : Set V) where
  count : ℕ
  point : Fin (count + 1) → V
  point_injective : Function.Injective point
  piece : (i : Fin count) → ClassifiedOrClosedFiniteContactPiece
    (Y := Y) (kappa := kappa) Q X (point i.castSucc) (point i.succ)
  initial_eq : point ⟨0, Nat.zero_lt_succ _⟩ = Q.initial
  terminal_eq : Q.terminal? = some (point ⟨count, Nat.lt_succ_self _⟩)
  vertexSet_exact : Q.vertexSet =
    Set.range point ∪ ⋃ i, (piece i).path.vertexSet
  edgeSet_exact : Q.edgeSet = ⋃ i, (piece i).path.edgeSet

namespace FiniteClosedClassifiedContactSegmentation

variable {Q : AltPath Gamma.graph}

def toChain
    (S : FiniteClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X) :
    ClosedClassifiedContactChain (Y := Y) (kappa := kappa) Q X
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

end FiniteClosedClassifiedContactSegmentation

structure EventuallyClosedClassifiedContactSegmentation
    (Q : AltPath Gamma.graph) (X persistent : Set V) where
  count : ℕ
  point : Fin (count + 1) → V
  point_injective : Function.Injective point
  piece : (i : Fin count) → ClassifiedOrClosedFiniteContactPiece
    (Y := Y) (kappa := kappa) Q X (point i.castSucc) (point i.succ)
  tail : ClassifiedInfiniteContactTail
    (Y := Y) (kappa := kappa) Q X persistent
      (point ⟨count, Nat.lt_succ_self _⟩)
  initial_eq : point ⟨0, Nat.zero_lt_succ _⟩ = Q.initial
  vertexSet_exact : Q.vertexSet =
    Set.range point ∪ (⋃ i, (piece i).path.vertexSet) ∪ tail.path.vertexSet
  edgeSet_exact : Q.edgeSet =
    (⋃ i, (piece i).path.edgeSet) ∪ tail.path.edgeSet

namespace EventuallyClosedClassifiedContactSegmentation

variable {Q : AltPath Gamma.graph} {persistent : Set V}

def toChain
    (S : EventuallyClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent) :
    ClosedClassifiedContactChain (Y := Y) (kappa := kappa) Q X
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

end EventuallyClosedClassifiedContactSegmentation

structure OmegaClosedClassifiedContactSegmentation
    (Q : AltPath Gamma.graph) (X : Set V) where
  point : ℕ → V
  point_injective : Function.Injective point
  piece : (i : ℕ) → ClassifiedOrClosedFiniteContactPiece
    (Y := Y) (kappa := kappa) Q X (point i) (point (i + 1))
  initial_eq : point 0 = Q.initial
  vertexSet_exact : Q.vertexSet =
    Set.range point ∪ ⋃ i, (piece i).path.vertexSet
  edgeSet_exact : Q.edgeSet = ⋃ i, (piece i).path.edgeSet

namespace OmegaClosedClassifiedContactSegmentation

variable {Q : AltPath Gamma.graph}

def toChain
    (S : OmegaClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X) :
    ClosedClassifiedContactChain (Y := Y) (kappa := kappa) Q X ℕ ℕ where
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

end OmegaClosedClassifiedContactSegmentation

inductive ClosedClassifiedContactSegmentation
    (Q : AltPath Gamma.graph) (X persistent : Set V)
  | finite : FiniteClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X →
      ClosedClassifiedContactSegmentation Q X persistent
  | eventually : EventuallyClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent →
      ClosedClassifiedContactSegmentation Q X persistent
  | omega : OmegaClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X →
      ClosedClassifiedContactSegmentation Q X persistent

namespace ClosedClassifiedContactSegmentation

variable {Q : AltPath Gamma.graph} {persistent : Set V}

def contactSet
    (S : ClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent) : Set V :=
  match S with
  | .finite T => T.toChain.contactSet
  | .eventually T => T.toChain.contactSet
  | .omega T => T.toChain.contactSet

def shortcutEdges
    (S : ClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent) : Set (V × V) :=
  match S with
  | .finite T => T.toChain.shortcutEdges
  | .eventually T => T.toChain.shortcutEdges
  | .omega T => T.toChain.shortcutEdges

def retainedEdges
    (S : ClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent) : Set (V × V) :=
  match S with
  | .finite T => T.toChain.retainedEdges
  | .eventually T => T.toChain.retainedEdges ∪ T.tail.retainedEdges
  | .omega T => T.toChain.retainedEdges

noncomputable def contactRank
    (S : ClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent) : V → Nat :=
  match S with
  | .finite T => T.toChain.contactRank
  | .eventually T => T.toChain.contactRank
  | .omega T => T.toChain.contactRank

theorem contactSet_subset_vertexSet
    (S : ClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent) :
    S.contactSet ⊆ Q.vertexSet := by
  intro x hx
  cases S with
  | finite T => rw [T.vertexSet_exact]; exact Or.inl hx
  | eventually T => rw [T.vertexSet_exact]; exact Or.inl (Or.inl hx)
  | omega T => rw [T.vertexSet_exact]; exact Or.inl hx

theorem shortcutEdges_subset_imaginaryGraph
    (S : ClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent) :
    S.shortcutEdges ⊆
      {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  cases S with
  | finite T => exact T.toChain.shortcutEdges_subset_imaginaryGraph
  | eventually T => exact T.toChain.shortcutEdges_subset_imaginaryGraph
  | omega T => exact T.toChain.shortcutEdges_subset_imaginaryGraph

theorem retainedEdges_subset_originalForward_union_shortcut
    (S : ClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent) :
    S.retainedEdges ⊆ Q.directionEdges .forward ∪ S.shortcutEdges := by
  cases S with
  | finite T =>
      exact T.toChain.retainedEdges_subset_originalForward_union_shortcut
  | eventually T =>
      rintro e (he | he)
      · exact T.toChain.retainedEdges_subset_originalForward_union_shortcut he
      · exact Or.inl (T.tail.retainedEdges_subset_originalForward he)
  | omega T =>
      exact T.toChain.retainedEdges_subset_originalForward_union_shortcut

theorem endpoints_mem_contactSet
    (S : ClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent)
    {e : V × V} (he : e ∈ S.shortcutEdges) :
    e.1 ∈ S.contactSet ∧ e.2 ∈ S.contactSet := by
  cases S with
  | finite T => exact T.toChain.endpoints_mem_contactSet he
  | eventually T => exact T.toChain.endpoints_mem_contactSet he
  | omega T => exact T.toChain.endpoints_mem_contactSet he

theorem contactRank_lt_of_mem_shortcutEdges
    (S : ClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent)
    {x y : V} (hxy : (x, y) ∈ S.shortcutEdges) :
    S.contactRank x < S.contactRank y := by
  cases S with
  | finite T => exact T.toChain.contactRank_lt_of_mem_shortcutEdges hxy
  | eventually T => exact T.toChain.contactRank_lt_of_mem_shortcutEdges hxy
  | omega T => exact T.toChain.contactRank_lt_of_mem_shortcutEdges hxy

theorem shortcutEdges_biUnique
    (S : ClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ S.shortcutEdges) := by
  cases S with
  | finite T => exact T.toChain.shortcutEdges_biUnique
  | eventually T => exact T.toChain.shortcutEdges_biUnique
  | omega T => exact T.toChain.shortcutEdges_biUnique

theorem shortcutEdges_acyclic
    (S : ClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent) :
    ¬ ContainsDirectedCycle S.shortcutEdges :=
  Alternating.GenericSimultaneousSwitch.not_containsDirectedCycle_of_wellFoundedRank
    S.shortcutEdges S.contactRank S.contactRank_lt_of_mem_shortcutEdges

theorem shortcutEdges_no_reverse_ray
    (S : ClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent) :
    ¬ ContainsReverseDirectedRay S.shortcutEdges :=
  Alternating.GenericSimultaneousSwitch.not_containsReverseDirectedRay_of_wellFoundedRank
    S.shortcutEdges S.contactRank S.contactRank_lt_of_mem_shortcutEdges

end ClosedClassifiedContactSegmentation

/-! ## Grouped mixed assignments -/

structure GroupedClosedClassifiedContactSegmentedAssignment
    {Z : Set Gamma.DPath} (A : SimultaneousAssignment Z Y)
    (X persistent : Set V) (G : Type v) where
  segmentation : ∀ s, ClosedClassifiedContactSegmentation
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

namespace GroupedClosedClassifiedContactSegmentedAssignment

variable {Z : Set Gamma.DPath} {A : SimultaneousAssignment Z Y}
variable {persistent : Set V} {G : Type v}

def edge
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G) : Set (V × V) :=
  ⋃ s, (S.segmentation s).shortcutEdges

def retainedEdges
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G) : Set (V × V) :=
  ⋃ s, (S.segmentation s).retainedEdges

def contactCarrier
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G) : Set V :=
  {x | ∃ e ∈ S.edge, e.1 = x ∨ e.2 = x}

theorem edge_subset_imaginaryGraph
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G) :
    S.edge ⊆ {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  intro e he
  simp only [edge, Set.mem_iUnion] at he
  obtain ⟨s, he⟩ := he
  exact (S.segmentation s).shortcutEdges_subset_imaginaryGraph he

theorem retainedEdges_subset_assignedForward_union_edge
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G) :
    S.retainedEdges ⊆
      (⋃ s, (A.assigned s).directionEdges .forward) ∪ S.edge := by
  intro e he
  simp only [retainedEdges, Set.mem_iUnion] at he
  obtain ⟨s, he⟩ := he
  rcases (S.segmentation s).retainedEdges_subset_originalForward_union_shortcut
      he with heForward | heShortcut
  · exact Or.inl (Set.mem_iUnion.2 ⟨s, heForward⟩)
  · exact Or.inr (Set.mem_iUnion.2 ⟨s, heShortcut⟩)

theorem endpoints_mem_contactCarrier
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (e : V × V) (he : e ∈ S.edge) :
    e.1 ∈ S.contactCarrier ∧ e.2 ∈ S.contactCarrier :=
  ⟨⟨e, he, Or.inl rfl⟩, ⟨e, he, Or.inr rfl⟩⟩

theorem edge_biUnique
    (S : GroupedClosedClassifiedContactSegmentedAssignment
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
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G) (x : V) : Option G := by
  classical
  exact if h : ∃ s, x ∈ (S.segmentation s).contactSet then
    some (S.group (Classical.choose h)) else none

theorem contactGroup_eq_some_of_mem
    (S : GroupedClosedClassifiedContactSegmentedAssignment
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
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G) (x : V) : Nat :=
  match S.contactGroup x with
  | none => 0
  | some g => S.localRank g x

theorem rank_lt_of_mem_edge
    (S : GroupedClosedClassifiedContactSegmentedAssignment
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
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G) :
    ¬ ContainsDirectedCycle S.edge :=
  Alternating.GenericSimultaneousSwitch.not_containsDirectedCycle_of_wellFoundedRank
    S.edge S.rank S.rank_lt_of_mem_edge

theorem edge_no_reverse_ray
    (S : GroupedClosedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G) :
    ¬ ContainsReverseDirectedRay S.edge :=
  Alternating.GenericSimultaneousSwitch.not_containsReverseDirectedRay_of_wellFoundedRank
    S.edge S.rank S.rank_lt_of_mem_edge

end GroupedClosedClassifiedContactSegmentedAssignment

#print axioms ClassifiedOrClosedFiniteContactPiece.retainedEdges_subset_originalForward_union_shortcut
#print axioms ClosedClassifiedContactChain.shortcutEdges_biUnique
#print axioms ClosedClassifiedContactSegmentation.retainedEdges_subset_originalForward_union_shortcut
#print axioms GroupedClosedClassifiedContactSegmentedAssignment.edge_biUnique
#print axioms GroupedClosedClassifiedContactSegmentedAssignment.retainedEdges_subset_assignedForward_union_edge

end LinkageBlueprint
end Blueprint
end Erdos599
