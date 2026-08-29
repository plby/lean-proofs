/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Basic
import Mathlib.Data.List.Chain

/-!
# Erdős Problem 599: directed webs, warps, and roofs

This file isolates the directed language used in the Aharoni--Berger proof.
The public statement in `Basic.lean` is about undirected simple graphs, while
the proof is naturally carried out in a *web*: a directed graph with specified
source and target sets.

Finite paths are represented by nonempty, duplicate-free lists whose
successive vertices follow the edge relation.  Rays are represented separately
by injective sequences indexed by `ℕ`; in particular, a ray is never silently
treated as a finite path with a terminal vertex.  A warp may contain both.

The definitions of `roof`, `essential`, and `strictRoof` are the ones needed
for the normalized quotient construction:

* `roof S` consists of the vertices from which every finite path to the target
  meets `S`;
* `essential S` consists of the `s ∈ S` which can reach the target while
  avoiding `S \ {s}`;
* `strictRoof S = roof S \ essential S`.

Only elementary consequences are proved here.  The infinite augmenting-path
argument belongs in the later proof modules.
-/

namespace Erdos599
namespace WebTheory

open Set

universe u

variable {V : Type u} {Adj : V → V → Prop}

/-- A directed web is a directed edge relation together with distinguished
source and target sets.  The edge relation is an explicit type parameter so
that this layer can later be adapted to another directed-path API. -/
structure Web (Adj : V → V → Prop) where
  source : Set V
  target : Set V

/-- A finite directed simple path.  The list of vertices is nonempty by
construction: it is `first :: tail`. -/
structure FinitePath (Adj : V → V → Prop) where
  first : V
  tail : List V
  nodup : (first :: tail).Nodup
  adjacent : List.IsChain Adj (first :: tail)

namespace FinitePath

/-- The nonempty list of vertices of a finite path. -/
def vertices (p : FinitePath Adj) : List V :=
  p.first :: p.tail

@[simp]
theorem vertices_ne_nil (p : FinitePath Adj) : p.vertices ≠ [] := by
  simp [vertices]

@[simp]
theorem vertices_head (p : FinitePath Adj) :
    p.vertices.head p.vertices_ne_nil = p.first := by
  simp [vertices]

/-- The terminal vertex of a finite path. -/
def last (p : FinitePath Adj) : V :=
  p.vertices.getLast p.vertices_ne_nil

/-- The set of vertices used by a finite path. -/
def support (p : FinitePath Adj) : Set V :=
  {v | v ∈ p.vertices}

@[simp]
theorem mem_support (p : FinitePath Adj) (v : V) :
    v ∈ p.support ↔ v ∈ p.vertices :=
  Iff.rfl

@[simp]
theorem first_mem_support (p : FinitePath Adj) : p.first ∈ p.support := by
  simp [support, vertices]

@[simp]
theorem last_mem_support (p : FinitePath Adj) : p.last ∈ p.support := by
  exact List.getLast_mem p.vertices_ne_nil

theorem support_finite (p : FinitePath Adj) : p.support.Finite := by
  change {v | v ∈ p.vertices}.Finite
  exact p.vertices.finite_toSet

/-- One finite path is a suffix-trimming of another if its vertex list is a
suffix.  This is deliberately a relation rather than an operation: later
arguments usually obtain the trimming point from a finite-choice lemma. -/
def IsSuffixTrim (q p : FinitePath Adj) : Prop :=
  q.vertices <:+ p.vertices

theorem support_subset_of_isSuffixTrim {q p : FinitePath Adj}
    (h : q.IsSuffixTrim p) : q.support ⊆ p.support := by
  intro v hv
  change v ∈ q.vertices at hv
  change v ∈ p.vertices
  rcases h with ⟨pre, hp⟩
  rw [← hp]
  exact List.mem_append_right pre hv

/-- Prefix-trimming, used when only the initial part of a path is retained. -/
def IsPrefixTrim (q p : FinitePath Adj) : Prop :=
  q.vertices <+: p.vertices

theorem support_subset_of_isPrefixTrim {q p : FinitePath Adj}
    (h : q.IsPrefixTrim p) : q.support ⊆ p.support := by
  intro v hv
  change v ∈ q.vertices at hv
  change v ∈ p.vertices
  rcases h with ⟨suf, hp⟩
  rw [← hp]
  exact List.mem_append_left suf hv

end FinitePath

/-- A one-way infinite directed simple path. -/
structure Ray (Adj : V → V → Prop) where
  vertex : ℕ → V
  injective : Function.Injective vertex
  adjacent : ∀ n : ℕ, Adj (vertex n) (vertex (n + 1))

namespace Ray

/-- The initial vertex of a ray. -/
def first (r : Ray Adj) : V :=
  r.vertex 0

/-- The (generally infinite) set of vertices used by a ray. -/
def support (r : Ray Adj) : Set V :=
  Set.range r.vertex

@[simp]
theorem mem_support (r : Ray Adj) (v : V) :
    v ∈ r.support ↔ ∃ n : ℕ, r.vertex n = v :=
  Iff.rfl

@[simp]
theorem first_mem_support (r : Ray Adj) : r.first ∈ r.support := by
  exact ⟨0, rfl⟩

end Ray

/-- A member of a warp is either a finite path or a ray. -/
inductive PathLike (Adj : V → V → Prop)
  | finite (path : FinitePath Adj)
  | ray (path : Ray Adj)

namespace PathLike

/-- The initial vertex of a finite path or ray. -/
def first : PathLike Adj → V
  | .finite p => p.first
  | .ray r => r.first

/-- The support of a finite path or ray. -/
def support : PathLike Adj → Set V
  | .finite p => p.support
  | .ray r => r.support

/-- A finite path has a terminal vertex, while a ray does not. -/
def terminal? : PathLike Adj → Option V
  | .finite p => some p.last
  | .ray _ => none

@[simp]
theorem first_mem_support (p : PathLike Adj) : p.first ∈ p.support := by
  cases p with
  | finite p => exact p.first_mem_support
  | ray r => exact r.first_mem_support

end PathLike

/-- A path family is an arbitrary set of finite paths and rays. -/
abbrev PathFamily (Adj : V → V → Prop) := Set (PathLike Adj)

/-- A warp is a path family with pairwise vertex-disjoint members. -/
structure Warp (Adj : V → V → Prop) where
  paths : PathFamily Adj
  pairwiseDisjoint :
    ∀ {p : PathLike Adj}, p ∈ paths →
      ∀ {q : PathLike Adj}, q ∈ paths → p ≠ q →
      Disjoint p.support q.support

namespace Warp

theorem disjoint {W : Warp Adj} {p q : PathLike Adj}
    (hp : p ∈ W.paths) (hq : q ∈ W.paths) (hpq : p ≠ q) :
    Disjoint p.support q.support :=
  W.pairwiseDisjoint hp hq hpq

end Warp

/-- A family containing only finite paths, with pairwise disjoint supports. -/
structure FiniteWarp (Adj : V → V → Prop) where
  paths : Set (FinitePath Adj)
  pairwiseDisjoint :
    ∀ {p : FinitePath Adj}, p ∈ paths →
      ∀ {q : FinitePath Adj}, q ∈ paths → p ≠ q →
      Disjoint p.support q.support

/-- A linkage of a web is a disjoint finite-path family running from the
source to the target and covering every source vertex.  The covering clause is
what distinguishes a linkage from an arbitrary packing of source--target
paths. -/
structure Linkage (W : Web Adj) extends FiniteWarp Adj where
  starts_in_source : ∀ {p : FinitePath Adj}, p ∈ paths → p.first ∈ W.source
  ends_in_target : ∀ {p : FinitePath Adj}, p ∈ paths → p.last ∈ W.target
  covers_source : ∀ {a : V}, a ∈ W.source → ∃ p ∈ paths, p.first = a

namespace Linkage

theorem unique_path_from_source {W : Web Adj} (L : Linkage W)
    {a : V} {p q : FinitePath Adj} (hp : p ∈ L.paths) (hq : q ∈ L.paths)
    (hpa : p.first = a) (hqa : q.first = a) : p = q := by
  by_contra hpq
  have hd := L.pairwiseDisjoint hp hq hpq
  apply Set.disjoint_left.1 hd p.first_mem_support
  rw [hpa, ← hqa]
  exact q.first_mem_support

end Linkage

namespace Web

/-- A finite path meets a set of vertices. -/
def Meets (p : FinitePath Adj) (S : Set V) : Prop :=
  ∃ v : V, v ∈ p.support ∧ v ∈ S

/-- A finite path avoids a set of vertices. -/
def Avoids (p : FinitePath Adj) (S : Set V) : Prop :=
  ∀ {v : V}, v ∈ p.support → v ∉ S

theorem avoids_iff_not_meets (p : FinitePath Adj) (S : Set V) :
    Avoids p S ↔ ¬ Meets p S := by
  constructor
  · intro h ⟨v, hvp, hvS⟩
    exact h hvp hvS
  · intro h v hvp hvS
    exact h ⟨v, hvp, hvS⟩

theorem not_avoids_iff_meets (p : FinitePath Adj) (S : Set V) :
    ¬ Avoids p S ↔ Meets p S := by
  rw [avoids_iff_not_meets]
  exact not_not

/-- A finite path beginning at `v` and ending in the target. -/
def IsTargetPathFrom (W : Web Adj) (v : V) (p : FinitePath Adj) : Prop :=
  p.first = v ∧ p.last ∈ W.target

/-- Reachability of the target by a finite path avoiding `S`. -/
def CanReachTargetAvoiding (W : Web Adj) (S : Set V) (v : V) : Prop :=
  ∃ p : FinitePath Adj, W.IsTargetPathFrom v p ∧ Avoids p S

/-- The roof of `S`: every finite path from the vertex to the target meets
`S`.  Rays do not enter this definition because they have no target endpoint. -/
def roof (W : Web Adj) (S : Set V) : Set V :=
  {v | ∀ p : FinitePath Adj, W.IsTargetPathFrom v p → Meets p S}

@[simp]
theorem mem_roof_iff (W : Web Adj) (S : Set V) (v : V) :
    v ∈ W.roof S ↔
      ∀ p : FinitePath Adj, W.IsTargetPathFrom v p → Meets p S :=
  Iff.rfl

theorem not_mem_roof_iff (W : Web Adj) (S : Set V) (v : V) :
    v ∉ W.roof S ↔ W.CanReachTargetAvoiding S v := by
  constructor
  · intro hv
    change ¬ ∀ p : FinitePath Adj, W.IsTargetPathFrom v p → Meets p S at hv
    simp only [not_forall] at hv
    obtain ⟨p, htarget, hmeet⟩ := hv
    exact ⟨p, htarget, (avoids_iff_not_meets p S).2 hmeet⟩
  · rintro ⟨p, hp, hav⟩ hv
    exact (avoids_iff_not_meets p S).1 hav (hv p hp)

theorem subset_roof (W : Web Adj) (S : Set V) : S ⊆ W.roof S := by
  intro v hvS p hp
  refine ⟨p.first, p.first_mem_support, ?_⟩
  exact hp.1 ▸ hvS

theorem roof_mono (W : Web Adj) {S T : Set V} (hST : S ⊆ T) :
    W.roof S ⊆ W.roof T := by
  intro v hv p hp
  obtain ⟨x, hxp, hxS⟩ := hv p hp
  exact ⟨x, hxp, hST hxS⟩

@[simp]
theorem roof_univ (W : Web Adj) : W.roof (Set.univ : Set V) = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  exact W.subset_roof Set.univ

/-- The essential part of `S`.  A point `s ∈ S` is essential precisely when
it has a finite path to the target avoiding every other point of `S`. -/
def essential (W : Web Adj) (S : Set V) : Set V :=
  {s | s ∈ S ∧ W.CanReachTargetAvoiding (S \ {s}) s}

@[simp]
theorem mem_essential_iff (W : Web Adj) (S : Set V) (s : V) :
    s ∈ W.essential S ↔
      s ∈ S ∧ W.CanReachTargetAvoiding (S \ {s}) s :=
  Iff.rfl

theorem essential_subset (W : Web Adj) (S : Set V) :
    W.essential S ⊆ S :=
  fun _ hs ↦ hs.1

theorem essential_subset_roof (W : Web Adj) (S : Set V) :
    W.essential S ⊆ W.roof S :=
  (W.essential_subset S).trans (W.subset_roof S)

/-- Witness form of essentiality: the witnessing path meets `S` only at its
initial vertex.  This is the elementary path-trimming fact used repeatedly in
roof arguments. -/
theorem mem_essential_iff_exists_targetPath_meeting_only_at
    (W : Web Adj) (S : Set V) (s : V) :
    s ∈ W.essential S ↔
      s ∈ S ∧ ∃ p : FinitePath Adj,
        W.IsTargetPathFrom s p ∧
          ∀ {v : V}, v ∈ p.support → v ∈ S → v = s := by
  constructor
  · rintro ⟨hsS, p, hp, hav⟩
    refine ⟨hsS, p, hp, ?_⟩
    intro v hvp hvS
    by_contra hvs
    exact hav hvp ⟨hvS, hvs⟩
  · rintro ⟨hsS, p, hp, honly⟩
    refine ⟨hsS, p, hp, ?_⟩
    intro v hvp hvdiff
    exact hvdiff.2 (honly hvp hvdiff.1)

/-- The strict roof is the roof with its essential boundary removed. -/
def strictRoof (W : Web Adj) (S : Set V) : Set V :=
  W.roof S \ W.essential S

@[simp]
theorem mem_strictRoof_iff (W : Web Adj) (S : Set V) (v : V) :
    v ∈ W.strictRoof S ↔ v ∈ W.roof S ∧ v ∉ W.essential S :=
  Iff.rfl

theorem strictRoof_subset_roof (W : Web Adj) (S : Set V) :
    W.strictRoof S ⊆ W.roof S :=
  Set.sdiff_subset

theorem disjoint_strictRoof_essential (W : Web Adj) (S : Set V) :
    Disjoint (W.strictRoof S) (W.essential S) := by
  exact Set.disjoint_left.2 (fun _ hv ↦ hv.2)

theorem roof_eq_strictRoof_union_essential (W : Web Adj) (S : Set V) :
    W.roof S = W.strictRoof S ∪ W.essential S := by
  rw [strictRoof, Set.sdiff_union_of_subset (W.essential_subset_roof S)]

end Web

/-- Restrict a directed edge relation to vertices outside `D`. -/
def deleteAdj (Adj : V → V → Prop) (D : Set V) (u v : V) : Prop :=
  Adj u v ∧ u ∉ D ∧ v ∉ D

/-- Normalized deletion data.  `boundary` is explicitly required to be
disjoint from the deleted region; `retained` is therefore not stored as an
independent, potentially inconsistent field. -/
structure NormalizedDeletionData (V : Type u) where
  deleted : Set V
  boundary : Set V
  boundary_disjoint : Disjoint deleted boundary

namespace NormalizedDeletionData

/-- The retained vertices of normalized deletion data. -/
def retained (D : NormalizedDeletionData V) : Set V :=
  D.deletedᶜ

theorem boundary_subset_retained (D : NormalizedDeletionData V) :
    D.boundary ⊆ D.retained := by
  intro v hv hdeleted
  exact Set.disjoint_left.1 D.boundary_disjoint hdeleted hv

/-- The quotient web obtained by deleting `D.deleted` and exposing
`D.boundary` as the new target. -/
def quotientWeb (D : NormalizedDeletionData V) (W : Web Adj) :
    Web (deleteAdj Adj D.deleted) where
  source := W.source \ D.deleted
  target := D.boundary

@[simp]
theorem quotientWeb_source (D : NormalizedDeletionData V) (W : Web Adj) :
    (D.quotientWeb W).source = W.source \ D.deleted :=
  rfl

@[simp]
theorem quotientWeb_target (D : NormalizedDeletionData V) (W : Web Adj) :
    (D.quotientWeb W).target = D.boundary :=
  rfl

end NormalizedDeletionData

namespace Web

/-- The normalized roof deletion: remove exactly the strict roof and retain
the essential part of the separator as boundary. -/
def roofDeletionData (W : Web Adj) (S : Set V) : NormalizedDeletionData V where
  deleted := W.strictRoof S
  boundary := W.essential S
  boundary_disjoint := W.disjoint_strictRoof_essential S

@[simp]
theorem roofDeletionData_deleted (W : Web Adj) (S : Set V) :
    (W.roofDeletionData S).deleted = W.strictRoof S :=
  rfl

@[simp]
theorem roofDeletionData_boundary (W : Web Adj) (S : Set V) :
    (W.roofDeletionData S).boundary = W.essential S :=
  rfl

/-- The normalized quotient by a separator candidate `S`. -/
def normalizedQuotient (W : Web Adj) (S : Set V) :
    Web (deleteAdj Adj (W.strictRoof S)) :=
  (W.roofDeletionData S).quotientWeb W

@[simp]
theorem normalizedQuotient_source (W : Web Adj) (S : Set V) :
    (W.normalizedQuotient S).source = W.source \ W.strictRoof S :=
  rfl

@[simp]
theorem normalizedQuotient_target (W : Web Adj) (S : Set V) :
    (W.normalizedQuotient S).target = W.essential S :=
  rfl

theorem normalizedQuotient_target_avoids_deleted (W : Web Adj) (S : Set V) :
    Disjoint (W.normalizedQuotient S).target (W.strictRoof S) := by
  simpa using (W.disjoint_strictRoof_essential S).symm

end Web

end WebTheory
end Erdos599
