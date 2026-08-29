/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayOutsideMacroEndpointPairing

/-!
# Bi-uniqueness of the globally classified outside-macro relation

The global limiting-reference classification keeps either one imaginary
shortcut or the literal forward edges of the assigned route.  The ordinary
simultaneous-assignment statement does not make its routes disjoint.  In the
actual outside-macro construction, however, every assigned route lies on the
unique honest later-row member beginning at its source.  Distinct sources
therefore have disjoint row owners.  This proves bi-uniqueness of the exact
source-indexed retained relation without postulating a compatibility field.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Yglobal : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace ClubStageGeometry

variable (C : ClubStageGeometry Gamma Yglobal kappa (Order.succ kappa))

private theorem directionEdges_endpoints_mem_vertexSet
    {Q : AltPath Gamma.graph} {d : Direction} {e : V × V}
    (he : e ∈ Q.directionEdges d) :
    e.1 ∈ Q.vertexSet ∧ e.2 ∈ Q.vertexSet := by
  simp only [AltPath.directionEdges, Set.mem_iUnion] at he
  obtain ⟨l, hl, _hd, hel⟩ := he
  have hs := l.path.edgeSet_subset_support_prod hel
  exact ⟨Q.link_support_subset_vertexSet hl hs.1,
    Q.link_support_subset_vertexSet hl hs.2⟩

private theorem finiteRetained_endpoints_mem_macroRoot
    {W : Set Gamma.DPath} {X : Set V}
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsub : outsideReference C.selectedReference X ⊆
      outsideReference W X)
    (s : {z : V // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet C.selectedReference}) (v : V)
    (hsv : (A.assignment.assigned s).terminal? = some v)
    (K : LimitingFiniteContactClassification C X
      (A.assignment.assigned s) s.1 v)
    {e : V × V} (he : e ∈ K.retainedEdges) :
    e.1 ∈ (initialPath (outsideReference W X)
        ⟨s.1, s.property.1⟩).1.support ∧
      e.2 ∈ (initialPath (outsideReference W X)
        ⟨s.1, s.property.1⟩).1.support := by
  have hroute := A.assigned_vertexSet_subset_macroRoot hW hsub s
  cases K with
  | imaginary _ =>
      simp only [LimitingFiniteContactClassification.retainedEdges,
        Set.mem_singleton_iff] at he
      rcases he with ⟨rfl, rfl⟩
      exact ⟨hroute (by
          rw [← A.assignment.starts_at s]
          exact (A.assignment.assigned s).initial_mem_vertexSet),
        hroute ((A.assignment.assigned s).mem_vertexSet_of_terminal_eq hsv)⟩
  | initialCovered _ =>
      have hend := directionEdges_endpoints_mem_vertexSet he
      exact ⟨hroute hend.1, hroute hend.2⟩
  | terminalCovered _ =>
      have hend := directionEdges_endpoints_mem_vertexSet he
      exact ⟨hroute hend.1, hroute hend.2⟩

private theorem infiniteRetained_endpoints_mem_macroRoot
    {W : Set Gamma.DPath} {X persistent : Set V}
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsub : outsideReference C.selectedReference X ⊆
      outsideReference W X)
    (s : {z : V // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet C.selectedReference})
    (K : LimitingInfiniteContactClassification C X persistent
      (A.assignment.assigned s) s.1)
    {e : V × V} (he : e ∈ K.retainedEdges) :
    e.1 ∈ (initialPath (outsideReference W X)
        ⟨s.1, s.property.1⟩).1.support ∧
      e.2 ∈ (initialPath (outsideReference W X)
        ⟨s.1, s.property.1⟩).1.support := by
  cases K with
  | popular _ =>
      simp [LimitingInfiniteContactClassification.retainedEdges] at he
  | initialCovered _ =>
      have hend := directionEdges_endpoints_mem_vertexSet he
      have hroute := A.assigned_vertexSet_subset_macroRoot hW hsub s
      exact ⟨hroute hend.1, hroute hend.2⟩

private theorem source_eq_of_macroRoot_common
    {W : Set Gamma.DPath} {X : Set V} (hW : Gamma.IsWarp W)
    (s t : {z : V // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet C.selectedReference}) {x : V}
    (hxs : x ∈ (initialPath (outsideReference W X)
      ⟨s.1, s.property.1⟩).1.support)
    (hxt : x ∈ (initialPath (outsideReference W X)
      ⟨t.1, t.property.1⟩).1.support) : s = t := by
  let p : outsideReference W X :=
    initialPath (outsideReference W X) ⟨s.1, s.property.1⟩
  let q : outsideReference W X :=
    initialPath (outsideReference W X) ⟨t.1, t.property.1⟩
  have hpq : p.1 = q.1 :=
    DWeb.IsWarp.eq_of_mem_support hW p.2.1 q.2.1 hxs hxt
  apply Subtype.ext
  calc
    s.1 = p.1.initial :=
      (initialPath_initial (outsideReference W X)
        ⟨s.1, s.property.1⟩).symm
    _ = q.1.initial := congrArg Path.initial hpq
    _ = t.1 := initialPath_initial (outsideReference W X)
      ⟨t.1, t.property.1⟩

private theorem finiteRetained_biUnique
    {W : Set Gamma.DPath} {X : Set V}
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (s : {z : V // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet C.selectedReference}) (v : V)
    (K : LimitingFiniteContactClassification C X
      (A.assignment.assigned s) s.1 v) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ K.retainedEdges) := by
  have hfamily := Alternating.IsWarp.familyEdges_biUnique hW
  cases K with
  | imaginary _ =>
      constructor <;> intro x y z h₁ h₂ <;>
        simp only [LimitingFiniteContactClassification.retainedEdges,
          Set.mem_singleton_iff, Prod.mk.injEq] at h₁ h₂ <;> aesop
  | initialCovered _ =>
      constructor
      · intro x y z hxz hyz
        exact hfamily.1
          (A.assigned_forwardEdges_subset_familyEdges s hxz)
          (A.assigned_forwardEdges_subset_familyEdges s hyz)
      · intro x y z hxy hxz
        exact hfamily.2
          (A.assigned_forwardEdges_subset_familyEdges s hxy)
          (A.assigned_forwardEdges_subset_familyEdges s hxz)
  | terminalCovered _ =>
      constructor
      · intro x y z hxz hyz
        exact hfamily.1
          (A.assigned_forwardEdges_subset_familyEdges s hxz)
          (A.assigned_forwardEdges_subset_familyEdges s hyz)
      · intro x y z hxy hxz
        exact hfamily.2
          (A.assigned_forwardEdges_subset_familyEdges s hxy)
          (A.assigned_forwardEdges_subset_familyEdges s hxz)

private theorem infiniteRetained_biUnique
    {W : Set Gamma.DPath} {X persistent : Set V}
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (s : {z : V // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet C.selectedReference})
    (K : LimitingInfiniteContactClassification C X persistent
      (A.assignment.assigned s) s.1) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ K.retainedEdges) := by
  cases K with
  | popular _ =>
      constructor <;> intro x y z h <;>
        simp [LimitingInfiniteContactClassification.retainedEdges] at h
  | initialCovered _ =>
      have hfamily := Alternating.IsWarp.familyEdges_biUnique hW
      constructor
      · intro x y z hxz hyz
        exact hfamily.1
          (A.assigned_forwardEdges_subset_familyEdges s hxz)
          (A.assigned_forwardEdges_subset_familyEdges s hyz)
      · intro x y z hxy hxz
        exact hfamily.2
          (A.assigned_forwardEdges_subset_familyEdges s hxy)
          (A.assigned_forwardEdges_subset_familyEdges s hxz)

/-- Every exact classified outside edge has a unique honest later-row owner
containing both endpoints.  The edge itself may be a limiting-reference
shortcut, so only endpoint incidence, not literal row-edge membership, is
asserted. -/
theorem outsideMacroRetainedEdge_has_rowOwner
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsub : outsideReference C.selectedReference X ⊆
      outsideReference W X)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa)
    {e : V × V}
    (he : e ∈ C.outsideMacroRetainedEdges (persistent := persistent)
      hSafeRoof A hW hsource hterminal hclosed) :
    ∃ p : Gamma.DPath, p ∈ W ∧ e.1 ∈ p.support ∧ e.2 ∈ p.support := by
  rcases he with he | he
  · obtain ⟨s, v, hsv, he⟩ := he
    let p : outsideReference W X :=
      initialPath (outsideReference W X) ⟨s.1, s.property.1⟩
    have hend := C.finiteRetained_endpoints_mem_macroRoot
      A hW hsub s v hsv _ he
    exact ⟨p.1, p.2.1, hend.1, hend.2⟩
  · obtain ⟨s, hinfinite, he⟩ := he
    let p : outsideReference W X :=
      initialPath (outsideReference W X) ⟨s.1, s.property.1⟩
    have hend := C.infiniteRetained_endpoints_mem_macroRoot
      A hW hsub s _ he
    exact ⟨p.1, p.2.1, hend.1, hend.2⟩

/-- Every edge of the exact source-indexed outside contribution is an edge
of the genuine limiting-reference imaginary graph.  Covered branches are
literal ambient forward edges; only the exception-free finite branch uses a
global imaginary shortcut. -/
theorem outsideMacroRetainedEdges_subset_imaginaryGraph
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa) :
    C.outsideMacroRetainedEdges (persistent := persistent)
        hSafeRoof A hW hsource hterminal hclosed ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  rintro e (he | he)
  · obtain ⟨s, v, hsv, he⟩ := he
    exact (C.outsideMacroFiniteClassification hSafeRoof A hW hsource
      hterminal hclosed s v hsv).retainedEdges_subset_imaginaryGraph he
  · obtain ⟨s, hinfinite, he⟩ := he
    have hforward :=
      (C.outsideMacroInfiniteClassification (persistent := persistent)
        hSafeRoof A hW hsource hterminal hclosed s hinfinite)
        |>.retainedEdges_subset_originalForward he
    have hrow := A.assigned_forwardEdges_subset_familyEdges s hforward
    simp only [familyEdges, Set.mem_iUnion] at hrow
    obtain ⟨p, hpW, hep⟩ := hrow
    exact Or.inl (p.edgeSet_subset_adj hep)

/-- The exact globally classified outside-macro relation is bi-unique.

The proof uses the actual macro owner of each assignment route.  It does not
infer disjointness from the abstract simultaneous-assignment API, whose
selected routes need not be pairwise disjoint. -/
theorem outsideMacroRetainedEdges_biUnique
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsub : outsideReference C.selectedReference X ⊆
      outsideReference W X)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa) :
    Relator.BiUnique (fun x y ↦
      (x, y) ∈ C.outsideMacroRetainedEdges (persistent := persistent)
        hSafeRoof A hW hsource hterminal hclosed) := by
  let finiteK := fun s v
      (hsv : (A.assignment.assigned s).terminal? = some v) ↦
    C.outsideMacroFiniteClassification hSafeRoof A hW hsource hterminal
      hclosed s v hsv
  let infiniteK := fun s (hinf : (A.assignment.assigned s).IsInfinite) ↦
    C.outsideMacroInfiniteClassification (persistent := persistent)
      hSafeRoof A hW hsource hterminal hclosed s hinf
  have source_eq_finite_finite : ∀ {s t v w a b c},
      (hsv : (A.assignment.assigned s).terminal? = some v) →
      (htw : (A.assignment.assigned t).terminal? = some w) →
      (a, c) ∈ (finiteK s v hsv).retainedEdges →
      (b, c) ∈ (finiteK t w htw).retainedEdges → s = t := by
    intro s t v w a b c hsv htw hac hbc
    exact C.source_eq_of_macroRoot_common hW s t
      (C.finiteRetained_endpoints_mem_macroRoot A hW hsub s v hsv _ hac).2
      (C.finiteRetained_endpoints_mem_macroRoot A hW hsub t w htw _ hbc).2
  have source_eq_finite_infinite : ∀ {s t v a b c},
      (hsv : (A.assignment.assigned s).terminal? = some v) →
      (htinf : (A.assignment.assigned t).IsInfinite) →
      (a, c) ∈ (finiteK s v hsv).retainedEdges →
      (b, c) ∈ (infiniteK t htinf).retainedEdges → s = t := by
    intro s t v a b c hsv htinf hac hbc
    exact C.source_eq_of_macroRoot_common hW s t
      (C.finiteRetained_endpoints_mem_macroRoot A hW hsub s v hsv _ hac).2
      (C.infiniteRetained_endpoints_mem_macroRoot A hW hsub t _ hbc).2
  have source_eq_infinite_finite : ∀ {s t v a b c},
      (hsinf : (A.assignment.assigned s).IsInfinite) →
      (htv : (A.assignment.assigned t).terminal? = some v) →
      (a, c) ∈ (infiniteK s hsinf).retainedEdges →
      (b, c) ∈ (finiteK t v htv).retainedEdges → s = t := by
    intro s t v a b c hsinf htv hac hbc
    exact C.source_eq_of_macroRoot_common hW s t
      (C.infiniteRetained_endpoints_mem_macroRoot A hW hsub s _ hac).2
      (C.finiteRetained_endpoints_mem_macroRoot A hW hsub t v htv _ hbc).2
  have source_eq_infinite_infinite : ∀ {s t a b c},
      (hsinf : (A.assignment.assigned s).IsInfinite) →
      (htinf : (A.assignment.assigned t).IsInfinite) →
      (a, c) ∈ (infiniteK s hsinf).retainedEdges →
      (b, c) ∈ (infiniteK t htinf).retainedEdges → s = t := by
    intro s t a b c hsinf htinf hac hbc
    exact C.source_eq_of_macroRoot_common hW s t
      (C.infiniteRetained_endpoints_mem_macroRoot A hW hsub s _ hac).2
      (C.infiniteRetained_endpoints_mem_macroRoot A hW hsub t _ hbc).2
  constructor
  · intro a b c hac hbc
    rcases hac with hac | hac <;> rcases hbc with hbc | hbc
    · obtain ⟨s, v, hsv, hac⟩ := hac
      obtain ⟨t, w, htw, hbc⟩ := hbc
      have hst := source_eq_finite_finite hsv htw hac hbc
      subst t
      have hvw : v = w := Option.some.inj (hsv.symm.trans htw)
      subst w
      exact (C.finiteRetained_biUnique A hW s v (finiteK s v hsv)).1 hac hbc
    · obtain ⟨s, v, hsv, hac⟩ := hac
      obtain ⟨t, htinf, hbc⟩ := hbc
      have hst := source_eq_finite_infinite hsv htinf hac hbc
      subst t
      have hnone := (A.assignment.assigned s).isInfinite_iff_terminal?_eq_none.mp
        htinf
      exact False.elim (by rw [hsv] at hnone; cases hnone)
    · obtain ⟨s, hsinf, hac⟩ := hac
      obtain ⟨t, v, htv, hbc⟩ := hbc
      have hst := source_eq_infinite_finite hsinf htv hac hbc
      subst t
      have hnone := (A.assignment.assigned s).isInfinite_iff_terminal?_eq_none.mp
        hsinf
      exact False.elim (by rw [htv] at hnone; cases hnone)
    · obtain ⟨s, hsinf, hac⟩ := hac
      obtain ⟨t, htinf, hbc⟩ := hbc
      have hst := source_eq_infinite_infinite hsinf htinf hac hbc
      subst t
      exact (C.infiniteRetained_biUnique A hW s (infiniteK s hsinf)).1
        hac hbc
  · intro a b c hab hac
    -- The common-source argument is identical, using the first endpoints.
    rcases hab with hab | hab <;> rcases hac with hac | hac
    · obtain ⟨s, v, hsv, hab⟩ := hab
      obtain ⟨t, w, htw, hac⟩ := hac
      have hst : s = t := C.source_eq_of_macroRoot_common hW s t
        (C.finiteRetained_endpoints_mem_macroRoot A hW hsub s v hsv _ hab).1
        (C.finiteRetained_endpoints_mem_macroRoot A hW hsub t w htw _ hac).1
      subst t
      have hvw : v = w := Option.some.inj (hsv.symm.trans htw)
      subst w
      exact (C.finiteRetained_biUnique A hW s v (finiteK s v hsv)).2 hab hac
    · obtain ⟨s, v, hsv, hab⟩ := hab
      obtain ⟨t, htinf, hac⟩ := hac
      have hst : s = t := C.source_eq_of_macroRoot_common hW s t
        (C.finiteRetained_endpoints_mem_macroRoot A hW hsub s v hsv _ hab).1
        (C.infiniteRetained_endpoints_mem_macroRoot A hW hsub t _ hac).1
      subst t
      have hnone := (A.assignment.assigned s).isInfinite_iff_terminal?_eq_none.mp
        htinf
      exact False.elim (by rw [hsv] at hnone; cases hnone)
    · obtain ⟨s, hsinf, hab⟩ := hab
      obtain ⟨t, v, htv, hac⟩ := hac
      have hst : s = t := C.source_eq_of_macroRoot_common hW s t
        (C.infiniteRetained_endpoints_mem_macroRoot A hW hsub s _ hab).1
        (C.finiteRetained_endpoints_mem_macroRoot A hW hsub t v htv _ hac).1
      subst t
      have hnone := (A.assignment.assigned s).isInfinite_iff_terminal?_eq_none.mp
        hsinf
      exact False.elim (by rw [htv] at hnone; cases hnone)
    · obtain ⟨s, hsinf, hab⟩ := hab
      obtain ⟨t, htinf, hac⟩ := hac
      have hst : s = t := C.source_eq_of_macroRoot_common hW s t
        (C.infiniteRetained_endpoints_mem_macroRoot A hW hsub s _ hab).1
        (C.infiniteRetained_endpoints_mem_macroRoot A hW hsub t _ hac).1
      subst t
      exact (C.infiniteRetained_biUnique A hW s (infiniteK s hsinf)).2
        hab hac

#print axioms outsideMacroRetainedEdges_biUnique
#print axioms outsideMacroRetainedEdges_subset_imaginaryGraph
#print axioms outsideMacroRetainedEdge_has_rowOwner

end ClubStageGeometry
end Erdos599.Blueprint.LinkageBlueprint
