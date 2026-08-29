/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMarkedResidualTouchedPaths

/-!
# Endpoint support of a localized marked residual switch

After the designated colour is localized to the finitely many components
met by a marked route, a one-point augmentation of the localized designated
family together with the residual family can only change designated endpoint
data on that finite subfamily.  This file records the exact set identities.

The point is stronger than mere containment.  Removing the new endpoint and
the old residual endpoint colour from the augmented boundary leaves exactly
the old localized designated endpoint colour.  Carrier disjointness is the
ingredient that prevents the two old colours from being confused here.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMarkedResidualEndpointSupport

open DWeb
open SingularMarkedResidualTouchedPaths

universe u

variable {V : Type u}

private theorem IsPathBetween.mono_source_of_initial_mem
    {G : DWeb V} {A A' C : Set V} {p : G.DPath}
    (h : IsPathBetween G A C p) (hsub : A' ⊆ A)
    (hinit : p.initial ∈ A') :
    IsPathBetween G A' C p := by
  obtain ⟨q, rfl, hends, hsource⟩ := h
  refine ⟨q, rfl, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxA' | hxC⟩
      · have hxOld : x ∈ q.support ∩ (A ∪ C) :=
          ⟨hxq, Or.inl (hsub hxA')⟩
        exact hends ▸ hxOld
      · have hxOld : x ∈ q.support ∩ (A ∪ C) :=
          ⟨hxq, Or.inr hxC⟩
        exact hends ▸ hxOld
    · rintro x (hxs | hxf)
      · subst x
        exact ⟨q.start_mem_support, Or.inl hinit⟩
      · have hfinishOld : q.finish ∈ q.support ∩ (A ∪ C) := by
          have hxfEq : x = q.finish := Set.mem_singleton_iff.mp hxf
          subst x
          rw [hends]
          exact Or.inr rfl
        have hxfEq : x = q.finish := Set.mem_singleton_iff.mp hxf
        subst x
        rcases hfinishOld.2 with hfinishA | hfinishC
        · have hfinishStart : q.finish = q.start := by
            have : q.finish ∈ ({q.start} : Set V) := by
              rw [← hsource]
              exact ⟨q.finish_mem_support, hfinishA⟩
            exact Set.mem_singleton_iff.mp this
          exact ⟨q.finish_mem_support,
            Or.inl (hfinishStart.symm ▸ hinit)⟩
        · exact ⟨q.finish_mem_support, Or.inr hfinishC⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxA'⟩
      have hxOld : x ∈ q.support ∩ A := ⟨hxq, hsub hxA'⟩
      exact hsource ▸ hxOld
    · rintro x hx
      have hxs : x = q.start := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨q.start_mem_support, hinit⟩

private theorem initialSet_disjoint_of_vertexSet_disjoint
    {G : DWeb V} {T L : Set G.DPath}
    (hTL : Disjoint (G.vertexSet T) (G.vertexSet L)) :
    Disjoint (G.initialSet T) (G.initialSet L) := by
  rw [Set.disjoint_left]
  rintro x ⟨p, hpT, rfl⟩ ⟨q, hqL, hq⟩
  exact Set.disjoint_left.1 hTL
    ⟨p, hpT, p.initial_mem_support⟩
    ⟨q, hqL, hq ▸ q.initial_mem_support⟩

private theorem terminalFrontier_disjoint_of_vertexSet_disjoint
    {G : DWeb V} {T L : Set G.DPath}
    (hTL : Disjoint (G.vertexSet T) (G.vertexSet L)) :
    Disjoint (G.terminalFrontier T) (G.terminalFrontier L) := by
  rw [Set.disjoint_left]
  rintro x ⟨p, hpT, hp⟩ ⟨q, hqL, hq⟩
  exact Set.disjoint_left.1 hTL
    ⟨p, hpT, G.terminal_mem_support hp⟩
    ⟨q, hqL, G.terminal_mem_support hq⟩

/-- Exact endpoint-colour support for a one-point augmentation of two
carrier-disjoint old colours.  After removing the new endpoint and the old
right-colour endpoints, precisely the old left-colour endpoints remain. -/
theorem onePointAugmentation_endpointSupport
    {G : DWeb V} {T L Jplus : Set G.DPath}
    (hTL : Disjoint (G.vertexSet T) (G.vertexSet L))
    (hplus : G.IsOnePointAugmentation (T ∪ L) Jplus) :
    ∃ a ∈ G.source \ G.initialSet (T ∪ L),
      ∃ b ∈ G.target \ G.terminalFrontier (T ∪ L),
        G.initialSet Jplus \ insert a (G.initialSet L) =
            G.initialSet T ∧
          G.terminalFrontier Jplus \
              insert b (G.terminalFrontier L) =
            G.terminalFrontier T := by
  obtain ⟨a, ha, b, hb, _hwarp, _hfinite, hinit, hterm⟩ := hplus
  have hinitDisjoint : Disjoint (G.initialSet T) (G.initialSet L) :=
    initialSet_disjoint_of_vertexSet_disjoint hTL
  have htermDisjoint :
      Disjoint (G.terminalFrontier T) (G.terminalFrontier L) :=
    terminalFrontier_disjoint_of_vertexSet_disjoint hTL
  refine ⟨a, ha, b, hb, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨hxPlus, hxRemove⟩
      rw [hinit, G.initialSet_union] at hxPlus
      rcases hxPlus with hxa | hxT | hxL
      · exact False.elim (hxRemove (Or.inl hxa))
      · exact hxT
      · exact False.elim (hxRemove (Or.inr hxL))
    · intro hxT
      refine ⟨?_, ?_⟩
      · rw [hinit, G.initialSet_union]
        exact Or.inr (Or.inl hxT)
      · rintro (hxa | hxL)
        · subst x
          exact ha.2 (by
            rw [G.initialSet_union]
            exact Or.inl hxT)
        · exact Set.disjoint_left.1 hinitDisjoint hxT hxL
  · ext x
    constructor
    · rintro ⟨hxPlus, hxRemove⟩
      rw [hterm, G.terminalFrontier_union] at hxPlus
      rcases hxPlus with hxb | hxT | hxL
      · exact False.elim (hxRemove (Or.inl hxb))
      · exact hxT
      · exact False.elim (hxRemove (Or.inr hxL))
    · intro hxT
      refine ⟨?_, ?_⟩
      · rw [hterm, G.terminalFrontier_union]
        exact Or.inr (Or.inl hxT)
      · rintro (hxb | hxL)
        · subst x
          exact hb.2 (by
            rw [G.terminalFrontier_union]
            exact Or.inl hxT)
        · exact Set.disjoint_left.1 htermDisjoint hxT hxL

/-- A touched designated subfamily remains an honest target linkage on its
own initial set.  This is the finite source-owner object used by the later
colour repair. -/
theorem touchedDesignatedPaths_isLinkageBetween
    {G : DWeb V} {A : Set V} {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (l : List (OneHoleResidualState V)) :
    IsLinkageBetween G
      (G.initialSet (touchedDesignatedPaths G P l)) G.target
      (touchedDesignatedPaths G P l) := by
  let T := touchedDesignatedPaths G P l
  have hTsub : T ⊆ P := touchedDesignatedPaths_subset G P l
  refine ⟨?_, ?_, rfl, ?_, ?_⟩
  · intro p hp q hq hpq
    exact hP.isWarp (hTsub hp) (hTsub hq) hpq
  · intro p hp
    exact hP.finiteCharacter (hTsub hp)
  · intro x hx
    obtain ⟨p, hpT, hpx⟩ := hx
    exact hP.terminalFrontier_subset ⟨p, hTsub hpT, hpx⟩
  · intro p hp
    apply IsPathBetween.mono_source_of_initial_mem
      (hP.endpointPure p (hTsub hp))
    · intro x hx
      rw [← hP.initialSet_eq]
      obtain ⟨q, hqT, hqx⟩ := hx
      exact ⟨q, hTsub hqT, hqx⟩
    · exact ⟨p, hp, rfl⟩

/-- The localized designated initial colour is supported on the original
designated source set. -/
theorem initialSet_touchedDesignatedPaths_subset
    {G : DWeb V} {A : Set V} {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (l : List (OneHoleResidualState V)) :
    G.initialSet (touchedDesignatedPaths G P l) ⊆ A := by
  intro x hx
  rw [← hP.initialSet_eq]
  obtain ⟨p, hp, hpx⟩ := hx
  exact ⟨p, touchedDesignatedPaths_subset G P l hp, hpx⟩

/-- Only finitely many designated initial vertices occur in the localized
colour. -/
theorem initialSet_touchedDesignatedPaths_finite
    {G : DWeb V} {P : Set G.DPath} (hP : G.IsWarp P)
    (l : List (OneHoleResidualState V)) :
    (G.initialSet (touchedDesignatedPaths G P l)).Finite := by
  have hT := touchedDesignatedPaths_finite hP l
  have himage :
      ((fun p : G.DPath ↦ p.initial) ''
        touchedDesignatedPaths G P l).Finite :=
    hT.image (fun p : G.DPath ↦ p.initial)
  simpa only [DWeb.initialSet] using himage

/-- Only finitely many designated terminal vertices occur in the localized
colour.  Rays simply contribute no terminal. -/
theorem terminalFrontier_touchedDesignatedPaths_finite
    {G : DWeb V} {P : Set G.DPath} (hP : G.IsWarp P)
    (l : List (OneHoleResidualState V)) :
    (G.terminalFrontier (touchedDesignatedPaths G P l)).Finite := by
  let T := touchedDesignatedPaths G P l
  have hT : T.Finite := touchedDesignatedPaths_finite hP l
  have himage : (G.terminal? '' T).Finite := hT.image G.terminal?
  have hpreimage : (some ⁻¹' (G.terminal? '' T)).Finite :=
    himage.preimage
      (Set.injOn_of_injective (Option.some_injective V))
  apply hpreimage.subset
  rintro x ⟨p, hpT, hpx⟩
  exact ⟨p, hpT, hpx⟩

/-- The localized designated source colour is a lower-cardinal request at
every infinite induction cardinal. -/
theorem mk_initialSet_touchedDesignatedPaths_lt
    {G : DWeb V} {P : Set G.DPath} (hP : G.IsWarp P)
    (l : List (OneHoleResidualState V)) {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0.{u} ≤ κ) :
    Cardinal.mk (G.initialSet (touchedDesignatedPaths G P l)) < κ := by
  letI : Finite (G.initialSet (touchedDesignatedPaths G P l)) :=
    Set.finite_coe_iff.mpr
      (initialSet_touchedDesignatedPaths_finite hP l)
  exact Cardinal.mk_lt_aleph0.trans_le hκ

#print axioms onePointAugmentation_endpointSupport
#print axioms touchedDesignatedPaths_isLinkageBetween
#print axioms initialSet_touchedDesignatedPaths_subset
#print axioms initialSet_touchedDesignatedPaths_finite
#print axioms terminalFrontier_touchedDesignatedPaths_finite
#print axioms mk_initialSet_touchedDesignatedPaths_lt

end SingularMarkedResidualEndpointSupport
end CardinalInduction
end Erdos599
