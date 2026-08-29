/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualOrderedTargetContact

/-!
# Biunique ordered equal-stage transactions

For a selected route `q`, the strict initial segment used to root its input is
not itself the post-switch relation.  The sound post-switch object is the
canonical repaired relation of all routes whose source index is at most that
of `q`.  This file packages that relation and its elementary structural
properties.  The remaining substantive step is the transaction lemma which
transfers the rooted target-component contact from the pre-switch
reachability relation to this repaired post-switch relation.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection

variable {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
variable {P : Popular.XSWarp
  (L.popularAuxiliaryInput hL.legal).lambda
  (L.popularAuxiliaryInput hL.legal).lambda.target}

namespace OrderedReservedStationaryDiagonalEqualSelection

/-- The canonical decoder depends on a warp member only through its
underlying finite path; the source/target membership proofs are irrelevant. -/
theorem canonicalErasedRoute_eq_of_path_eq
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    {P Q : Popular.XSWarp J.lambda J.lambda.target}
    {p : WarpPath P} {q : WarpPath Q} (hpq : p.1 = q.1) :
    canonicalErasedRoute J P p = canonicalErasedRoute J Q q := by
  rcases p with ⟨p, hp⟩
  rcases q with ⟨q, hq⟩
  dsimp only at hpq
  subst q
  rfl

/-- The selected auxiliary routes processed no later than a given source
index. -/
def routesThroughIndex
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (a : Stationary.Below kappa) :
    Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target where
  paths := {p | ∃ hp : p ∈ S.routes.paths,
    warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes ⟨p, hp⟩ ≤ a}
  disjoint := by
    rintro p ⟨hp, _⟩ q ⟨hq, _⟩ hpq
    exact S.routes.disjoint hp hq hpq
  starts_in_source := by
    rintro p ⟨hp, _⟩
    exact S.routes.starts_in_source hp
  ends_in_target := by
    rintro p ⟨hp, _⟩
    exact S.routes.ends_in_target hp

/-- The processed-through family is a subwarp of the final ordered family. -/
theorem routesThroughIndex_paths_subset_routes
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (a : Stationary.Below kappa) :
    (S.routesThroughIndex a).paths ⊆ S.routes.paths := by
  rintro p ⟨hp, _⟩
  exact hp

/-- The current route belongs to the family processed through its own
index. -/
theorem mem_routesThroughIndex_self
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (q : WarpPath S.routes) :
    q.1 ∈ (S.routesThroughIndex
      (warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q)).paths :=
  ⟨q.2, le_rfl⟩

/-- Every strict predecessor belongs to the family processed through the
current route. -/
theorem routesBeforeIndex_paths_subset_routesThroughIndex
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (a : Stationary.Below kappa) :
    (routesBeforeIndex S a).paths ⊆ (S.routesThroughIndex a).paths := by
  rintro p ⟨hp, hpa⟩
  exact ⟨hp, hpa.le⟩

/-- Every route processed through `q` is either `q` itself or a strict
predecessor. -/
theorem routesThroughIndex_eq_current_or_mem_before
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (q : WarpPath S.routes)
    (r : WarpPath (S.routesThroughIndex
      (warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q))) :
    r.1 = q.1 ∨ r.1 ∈ (routesBeforeIndex S
      (warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q)).paths := by
  obtain ⟨hr, hrle⟩ := r.2
  rcases lt_or_eq_of_le hrle with hrlt | hreq
  · exact Or.inr ⟨hr, hrlt⟩
  · left
    have hrq : (⟨r.1, hr⟩ : WarpPath S.routes) = q := by
      apply warpPath_eq_of_index_eq
        (L.popularAuxiliaryIndexed hL)
        (L.popularAuxiliaryIndexed_sourceIndexed hL) S.routes
      exact hreq
    exact congrArg Subtype.val hrq

/-- Decoded-carrier disjointness is inherited by the processed-through
family. -/
theorem routesThroughIndex_decodedDisjoint
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (a : Stationary.Below kappa) :
    (S.routesThroughIndex a).paths.PairwiseDisjoint
      (L.popularAuxiliaryInput hL.legal).decodedVertexCarrier := by
  intro p hp q hq hpq
  exact S.routes_decodedDisjoint
    (S.routesThroughIndex_paths_subset_routes a hp)
    (S.routesThroughIndex_paths_subset_routes a hq) hpq

/-- The post-switch relation through one source index is biunique. -/
theorem routesThroughIndex_repairedEdges_biUnique
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (a : Stationary.Below kappa) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
      (L.popularAuxiliaryInput hL.legal) (S.routesThroughIndex a)) := by
  exact canonicalErasedRepairedEdges_biUnique
    (L.popularAuxiliaryInput hL.legal) (S.routesThroughIndex a)
      (S.routesThroughIndex_decodedDisjoint a)

/-- The post-switch relation through one source index consists of genuine
ambient edges. -/
theorem routesThroughIndex_repairedEdges_subset_adj
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (a : Stationary.Below kappa) :
    canonicalErasedRepairedEdges
      (L.popularAuxiliaryInput hL.legal) (S.routesThroughIndex a) ⊆
        {e | Gamma.graph.Adj e.1 e.2} :=
  canonicalErasedRepairedEdges_subset_adj
    (L.popularAuxiliaryInput hL.legal) (S.routesThroughIndex a)

/-- Every forward edge of the current route is present in the repaired
post-switch relation through its index. -/
theorem current_forwardEdges_subset_routesThroughIndex_repaired
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (q : WarpPath S.routes) :
    (canonicalErasedRoute
      (L.popularAuxiliaryInput hL.legal)
      ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
      ⟨q.1, S.routes_subset_equalBase q.2⟩).directionEdges .forward ⊆
      canonicalErasedRepairedEdges
        (L.popularAuxiliaryInput hL.legal)
        (S.routesThroughIndex
          (warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q)) := by
  intro e he
  apply Or.inr
  simp only [canonicalErasedForwardEdges, Set.mem_iUnion]
  let qT : WarpPath (S.routesThroughIndex
      (warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q)) :=
    ⟨q.1, S.mem_routesThroughIndex_self q⟩
  refine ⟨qT, ?_⟩
  simpa only [qT, canonicalErasedRoute] using he

/-- Exact one-step deletion classification.  An edge which was present just
before `q` but is absent after processing `q` is deleted by `q` itself:
either it is one of `q`'s backward edges, or it conflicts at a tail/head with
one of `q`'s forward edges.  No earlier selected route can be responsible,
because the edge already survived their repaired relation. -/
theorem mem_current_backward_or_forwardConflict_of_mem_before_not_mem_through
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (q : WarpPath S.routes) {e : V × V}
    (heBefore : e ∈ canonicalErasedRepairedEdges
      (L.popularAuxiliaryInput hL.legal)
      (routesBeforeIndex S
        (warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q)))
    (heNotThrough : e ∉ canonicalErasedRepairedEdges
      (L.popularAuxiliaryInput hL.legal)
      (S.routesThroughIndex
        (warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q))) :
    e ∈ (canonicalErasedRoute
      (L.popularAuxiliaryInput hL.legal)
      ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
      ⟨q.1, S.routes_subset_equalBase q.2⟩).directionEdges .backward ∨
      ∃ f ∈ (canonicalErasedRoute
        (L.popularAuxiliaryInput hL.legal)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
        ⟨q.1, S.routes_subset_equalBase q.2⟩).directionEdges .forward,
        e.1 = f.1 ∨ e.2 = f.2 := by
  let J := L.popularAuxiliaryInput hL.legal
  let U := L.popularAuxiliaryIndexed hL
  let B := routesBeforeIndex S (warpPathIndex U S.routes q)
  let T := S.routesThroughIndex (warpPathIndex U S.routes q)
  let Q := U.equalSubwarp S.base
  let qQ : WarpPath Q := ⟨q.1, S.routes_subset_equalBase q.2⟩
  have heNotForwardB : e ∉ canonicalErasedForwardEdges J B := by
    intro heForward
    apply heNotThrough
    apply Or.inr
    simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at heForward ⊢
    obtain ⟨r, hr⟩ := heForward
    let rT : WarpPath T :=
      ⟨r.1, S.routesBeforeIndex_paths_subset_routesThroughIndex
        (warpPathIndex U S.routes q) r.2⟩
    refine ⟨rT, ?_⟩
    simpa only [rT, canonicalErasedRoute] using hr
  have heBase : e ∈ canonicalErasedResidualEdges J B \
      canonicalErasedForwardConflictEdges J B := by
    rcases heBefore with heBase | heForward
    · exact heBase
    · exact False.elim (heNotForwardB heForward)
  have heFamily : e ∈ J.familyEdges := heBase.1.1
  by_cases heBackwardT : e ∈ canonicalErasedBackwardEdges J T
  · simp only [canonicalErasedBackwardEdges, Set.mem_iUnion] at heBackwardT
    obtain ⟨r, hr⟩ := heBackwardT
    rcases S.routesThroughIndex_eq_current_or_mem_before q r with hrq | hrB
    · left
      have hroute : canonicalErasedRoute J T r =
          canonicalErasedRoute J Q qQ :=
        canonicalErasedRoute_eq_of_path_eq J hrq
      rw [hroute] at hr
      simpa only [J, Q, qQ] using hr
    · exfalso
      exact heBase.1.2 (by
        simp only [canonicalErasedBackwardEdges, Set.mem_iUnion]
        exact ⟨⟨r.1, hrB⟩, by
          simpa only [canonicalErasedRoute] using hr⟩)
  · have heResidualT : e ∈ canonicalErasedResidualEdges J T :=
      ⟨heFamily, heBackwardT⟩
    have heConflictT : e ∈ canonicalErasedForwardConflictEdges J T := by
      by_contra heNotConflict
      exact heNotThrough (Or.inl ⟨heResidualT, heNotConflict⟩)
    obtain ⟨f, hf, hends⟩ := heConflictT
    simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hf
    obtain ⟨r, hrf⟩ := hf
    rcases S.routesThroughIndex_eq_current_or_mem_before q r with hrq | hrB
    · right
      have hroute : canonicalErasedRoute J T r =
          canonicalErasedRoute J Q qQ :=
        canonicalErasedRoute_eq_of_path_eq J hrq
      rw [hroute] at hrf
      refine ⟨f, ?_, hends⟩
      simpa only [J, Q, qQ] using hrf
    · exfalso
      exact heBase.2 ⟨f, by
        simp only [canonicalErasedForwardEdges, Set.mem_iUnion]
        exact ⟨⟨r.1, hrB⟩, by
          simpa only [canonicalErasedRoute] using hrf⟩, hends⟩

end OrderedReservedStationaryDiagonalEqualSelection
end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.OrderedReservedStationaryDiagonalEqualSelection.routesThroughIndex_repairedEdges_biUnique
#print axioms Erdos599.DWeb.KappaLadder.OrderedReservedStationaryDiagonalEqualSelection.current_forwardEdges_subset_routesThroughIndex_repaired
#print axioms Erdos599.DWeb.KappaLadder.OrderedReservedStationaryDiagonalEqualSelection.mem_current_backward_or_forwardConflict_of_mem_before_not_mem_through
