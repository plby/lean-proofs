/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeSwitching

/-!
# Relation-level certificates for simultaneous switching

This file isolates the set-theoretic part of a simultaneous switch.  The
base relation `B` and the union `R` of all route edges need not be disjoint.
Their literal switch is the symmetric difference

`(B \ R) \cup (R \ B)`.

For local bi-uniqueness it is not necessary to forbid every contact between
`B` and `R`.  A mixed incoming or outgoing conflict is harmless when one of
the two competing edges is canceled by the symmetric difference.  The
`CrossConflictCancellation` predicate records exactly this alternative.

The global obstruction is kept separate.  A rank into any well-founded
linear order, strictly increasing on the retained base edges and on the
added route edges, rules out both directed cycles and reverse-directed
rays.  In particular the rank may be a lexicographic request/component
rank; no natural-number bound on the request family is built into the API.
-/

noncomputable section

open Set

namespace Erdos599
namespace Alternating
namespace GenericSimultaneousSwitch

universe u v

variable {V : Type u} {B R : Set (V × V)}

/-! ## Route unions -/

/-- The literal union of a request-indexed family of route relations. -/
def routeUnion {I : Type v} (route : I → Set (V × V)) : Set (V × V) :=
  ⋃ i, route i

/-- Relation-level ownership data sufficient to show that a route union is
bi-unique.  Different routes may meet and may even share edges: only their
incoming and outgoing incidences are required to be coherent.  Thus this
structure also accommodates the permitted later-request apex contacts. -/
structure RouteUnionCoherent {I : Type v}
    (route : I → Set (V × V)) : Prop where
  route_biUnique : ∀ i, Relator.BiUnique (fun x y ↦ (x, y) ∈ route i)
  incoming : ∀ {i j : I} {x y z : V},
    i ≠ j → (x, z) ∈ route i → (y, z) ∈ route j → x = y
  outgoing : ∀ {i j : I} {x y z : V},
    i ≠ j → (x, y) ∈ route i → (x, z) ∈ route j → y = z

/-- Coherent request ownership gives a bi-unique literal route union. -/
theorem RouteUnionCoherent.biUnique {I : Type v}
    {route : I → Set (V × V)} (h : RouteUnionCoherent route) :
    Relator.BiUnique
      (fun x y ↦ (x, y) ∈ routeUnion route) := by
  constructor
  · intro x y z hxz hyz
    simp only [routeUnion, Set.mem_iUnion] at hxz hyz
    obtain ⟨i, hxz⟩ := hxz
    obtain ⟨j, hyz⟩ := hyz
    by_cases hij : i = j
    · subst j
      exact (h.route_biUnique i).1 hxz hyz
    · exact h.incoming hij hxz hyz
  · intro x y z hxy hxz
    simp only [routeUnion, Set.mem_iUnion] at hxy hxz
    obtain ⟨i, hxy⟩ := hxy
    obtain ⟨j, hxz⟩ := hxz
    by_cases hij : i = j
    · subst j
      exact (h.route_biUnique i).2 hxy hxz
    · exact h.outgoing hij hxy hxz

/-- Every mixed degree conflict is either coherent already or deletes at
least one of its two competing edges in the literal symmetric difference.

The first field is the incoming version and the second is the outgoing
version.  For example, if `B` contains `x → z` and `R` contains `y → z`,
then either the predecessors agree, or the base edge also lies in `R`, or
the route edge also lies in `B`.  The latter two alternatives are precisely
the two cancellation cases. -/
structure CrossConflictCancellation (B R : Set (V × V)) : Prop where
  incoming : ∀ {x y z : V},
    (x, z) ∈ B → (y, z) ∈ R →
      x = y ∨ (x, z) ∈ R ∨ (y, z) ∈ B
  outgoing : ∀ {x y z : V},
    (x, y) ∈ B → (x, z) ∈ R →
      y = z ∨ (x, y) ∈ R ∨ (x, z) ∈ B

/-- It is enough to verify cancellation against each owned route.  The
conclusion still refers to the whole union because a conflicting base edge
may be canceled by a route other than the one witnessing the mixed
incidence. -/
theorem CrossConflictCancellation.of_routewise {I : Type v}
    (route : I → Set (V × V))
    (hin : ∀ {i : I} {x y z : V},
      (x, z) ∈ B → (y, z) ∈ route i →
        x = y ∨ (x, z) ∈ routeUnion route ∨ (y, z) ∈ B)
    (hout : ∀ {i : I} {x y z : V},
      (x, y) ∈ B → (x, z) ∈ route i →
        y = z ∨ (x, y) ∈ routeUnion route ∨ (x, z) ∈ B) :
    CrossConflictCancellation B (routeUnion route) := by
  constructor
  · intro x y z hxz hyz
    simp only [routeUnion, Set.mem_iUnion] at hyz
    obtain ⟨i, hyz⟩ := hyz
    exact hin hxz hyz
  · intro x y z hxy hxz
    simp only [routeUnion, Set.mem_iUnion] at hxz
    obtain ⟨i, hxz⟩ := hxz
    exact hout hxy hxz

/-- Cancellation converts mixed incoming conflicts into equality for the
two surviving colors of the symmetric difference. -/
theorem CrossConflictCancellation.incoming_of_survives
    (h : CrossConflictCancellation B R)
    {x y z : V}
    (hxz : (x, z) ∈ B \ R) (hyz : (y, z) ∈ R \ B) :
    x = y := by
  rcases h.incoming hxz.1 hyz.1 with hxy | hcancel | hcancel
  · exact hxy
  · exact False.elim (hxz.2 hcancel)
  · exact False.elim (hyz.2 hcancel)

/-- Cancellation converts mixed outgoing conflicts into equality for the
two surviving colors of the symmetric difference. -/
theorem CrossConflictCancellation.outgoing_of_survives
    (h : CrossConflictCancellation B R)
    {x y z : V}
    (hxy : (x, y) ∈ B \ R) (hxz : (x, z) ∈ R \ B) :
    y = z := by
  rcases h.outgoing hxy.1 hxz.1 with hyz | hcancel | hcancel
  · exact hyz
  · exact False.elim (hxy.2 hcancel)
  · exact False.elim (hxz.2 hcancel)

/-- A literal simultaneous symmetric difference is bi-unique whenever the
two colors are separately bi-unique and every mixed conflict is canceled.

This statement is deliberately about arbitrary edge relations.  In a
grounding application, `R` can be the union of all erased finite route edge
sets, and the cancellation fields can be proved using route ownership and
the later-request apex invariant. -/
theorem edgeSymmDiff_biUnique
    (hB : Relator.BiUnique (fun x y ↦ (x, y) ∈ B))
    (hR : Relator.BiUnique (fun x y ↦ (x, y) ∈ R))
    (hcross : CrossConflictCancellation B R) :
    Relator.BiUnique
      (fun x y ↦ (x, y) ∈ edgeSymmDiff B R) := by
  constructor
  · intro x y z hxz hyz
    rcases hxz with hxz | hxz <;> rcases hyz with hyz | hyz
    · exact hB.1 hxz.1 hyz.1
    · exact hcross.incoming_of_survives hxz hyz
    · exact (hcross.incoming_of_survives hyz hxz).symm
    · exact hR.1 hxz.1 hyz.1
  · intro x y z hxy hxz
    rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
    · exact hB.2 hxy.1 hxz.1
    · exact hcross.outgoing_of_survives hxy hxz
    · exact (hcross.outgoing_of_survives hxz hxy).symm
    · exact hR.2 hxy.1 hxz.1

section Rank

variable {A : Type v} [LinearOrder A]

/-- A relation strictly increasing in a well-founded linear rank contains
no directed cycle.  The rank type is intentionally universe-polymorphic so
that a request ordinal, or a lexicographic refinement of one, can be used. -/
theorem not_containsDirectedCycle_of_wellFoundedRank
    (E : Set (V × V)) (rank : V → A)
    (hrank : ∀ {x y : V}, (x, y) ∈ E → rank x < rank y) :
    ¬ ContainsDirectedCycle E := by
  rintro ⟨C, hC⟩
  obtain ⟨i, _hi, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin C.length))
      (fun j ↦ rank (C.vertex j))
      ⟨⟨0, C.positive⟩, Finset.mem_univ _⟩
  have hedge : (C.vertex i, C.vertex (C.next i)) ∈ E :=
    hC ⟨i, rfl⟩
  have hle := hmax (C.next i) (Finset.mem_univ _)
  exact (not_lt_of_ge hle) (hrank hedge)

/-- A relation strictly increasing in a well-founded rank contains no ray
when traversed backwards. -/
theorem not_containsReverseDirectedRay_of_wellFoundedRank
    [WellFoundedLT A]
    (E : Set (V × V)) (rank : V → A)
    (hrank : ∀ {x y : V}, (x, y) ∈ E → rank x < rank y) :
    ¬ ContainsReverseDirectedRay E := by
  rintro ⟨Q, hQ⟩
  obtain ⟨n, hn⟩ :=
    WellFounded.not_rel_apply_succ (r := fun x y : A ↦ x < y)
      (fun n ↦ rank (Q.vertex n))
  exact hn (hrank (hQ n))

/-- A rank certificate can be checked color by color.  Only retained base
edges and genuinely added route edges need to satisfy the rank inequality;
edges canceled by the simultaneous switch are irrelevant. -/
structure SymmDiffRank (B R : Set (V × V)) where
  rank : V → A
  base_retained_step : ∀ {x y : V},
    (x, y) ∈ B → (x, y) ∉ R → rank x < rank y
  route_added_step : ∀ {x y : V},
    (x, y) ∈ R → (x, y) ∉ B → rank x < rank y

/-- The colorwise rank certificate applies to every surviving switched
edge. -/
theorem SymmDiffRank.edge_step (h : SymmDiffRank (A := A) B R)
    {x y : V} (hxy : (x, y) ∈ edgeSymmDiff B R) :
    h.rank x < h.rank y := by
  rcases hxy with hxy | hxy
  · exact h.base_retained_step hxy.1 hxy.2
  · exact h.route_added_step hxy.1 hxy.2

/-- Build a symmetric-difference rank route by route. -/
def SymmDiffRank.of_routewise {I : Type v}
    (route : I → Set (V × V)) (rank : V → A)
    (hbase : ∀ {x y : V},
      (x, y) ∈ B → (x, y) ∉ routeUnion route → rank x < rank y)
    (hroute : ∀ (i : I) {x y : V},
      (x, y) ∈ route i → (x, y) ∉ B → rank x < rank y) :
    SymmDiffRank (A := A) B (routeUnion route) where
  rank := rank
  base_retained_step := hbase
  route_added_step := by
    intro x y hxy hxyB
    simp only [routeUnion, Set.mem_iUnion] at hxy
    obtain ⟨i, hxy⟩ := hxy
    exact hroute i hxy hxyB

theorem SymmDiffRank.noDirectedCycle
    (h : SymmDiffRank (A := A) B R) :
    ¬ ContainsDirectedCycle (edgeSymmDiff B R) :=
  not_containsDirectedCycle_of_wellFoundedRank
    (edgeSymmDiff B R) h.rank h.edge_step

theorem SymmDiffRank.noReverseDirectedRay
    [WellFoundedLT A]
    (h : SymmDiffRank (A := A) B R) :
    ¬ ContainsReverseDirectedRay (edgeSymmDiff B R) :=
  not_containsReverseDirectedRay_of_wellFoundedRank
    (edgeSymmDiff B R) h.rank h.edge_step

/-- The complete three-field relation certificate needed by the path/ray
decomposition: local degree control and the two global obstructions. -/
structure Compatible (B R : Set (V × V)) : Prop where
  biUnique : Relator.BiUnique
    (fun x y ↦ (x, y) ∈ edgeSymmDiff B R)
  noDirectedCycle : ¬ ContainsDirectedCycle (edgeSymmDiff B R)
  noReverseDirectedRay :
    ¬ ContainsReverseDirectedRay (edgeSymmDiff B R)

/-- Assemble compatibility from conflict cancellation and a well-founded
rank. -/
theorem compatible_of_cancellation_of_rank
    [WellFoundedLT A]
    (hB : Relator.BiUnique (fun x y ↦ (x, y) ∈ B))
    (hR : Relator.BiUnique (fun x y ↦ (x, y) ∈ R))
    (hcross : CrossConflictCancellation B R)
    (hrank : SymmDiffRank (A := A) B R) :
    Compatible B R :=
  ⟨edgeSymmDiff_biUnique hB hR hcross,
    hrank.noDirectedCycle, hrank.noReverseDirectedRay⟩

end Rank

end GenericSimultaneousSwitch
end Alternating
end Erdos599
