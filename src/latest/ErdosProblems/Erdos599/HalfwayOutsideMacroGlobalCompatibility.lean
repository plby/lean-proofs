/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayOutsideMacroEndpointPairing

/-!
# Compatibility of globally classified outside-macro edges

The limiting-reference classification keeps either an imaginary shortcut or
literal forward edges of the actual assigned route.  The concrete
`OutsideMacroFullAssignment` avoids the closing set on its whole route, not
merely in its hammock interior.  Thus every endpoint of the classified
outside relation is outside the closing set, while every edge retained in
the complementary inside relation has both endpoints inside it.

This proves the exact inside/outside cross-compatibility.  It does not assume
or package a missing whole-relation bi-uniqueness theorem.
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

private theorem no_directed_cycle_of_strict_rank
    (E : Set (V × V)) (rank : V → Nat)
    (hrank : ∀ {x y}, (x, y) ∈ E → rank x < rank y) :
    ¬ ContainsDirectedCycle E := by
  rintro ⟨D, hD⟩
  let last : Nat := D.length - 1
  have hlast : last < D.length := Nat.sub_lt D.positive (by omega)
  have hnextLast : D.next ⟨last, hlast⟩ =
      (⟨0, D.positive⟩ : Fin D.length) := by
    apply Fin.ext
    have hs : last + 1 = D.length := Nat.sub_add_cancel D.positive
    simp [DirectedCycle.next, hs]
  have hmono : ∀ n, (hn : n < D.length) →
      rank (D.vertex ⟨0, D.positive⟩) ≤ rank (D.vertex ⟨n, hn⟩) := by
    intro n
    induction n with
    | zero => intro _; exact Nat.le_refl _
    | succ n ih =>
        intro hn
        have hn' : n < D.length := Nat.lt_trans (Nat.lt_succ_self n) hn
        have hnext : D.next (⟨n, hn'⟩ : Fin D.length) =
            ⟨n + 1, hn⟩ := by
          apply Fin.ext
          exact Nat.mod_eq_of_lt hn
        exact (ih hn').trans (Nat.le_of_lt (by
          rw [← hnext]
          exact hrank (hD ⟨⟨n, hn'⟩, rfl⟩)))
  have hback : rank (D.vertex ⟨last, hlast⟩) <
      rank (D.vertex ⟨0, D.positive⟩) := by
    rw [← hnextLast]
    exact hrank (hD ⟨⟨last, hlast⟩, rfl⟩)
  exact (Nat.not_lt_of_ge (hmono last hlast)) hback

private theorem no_reverse_ray_of_strict_rank
    (E : Set (V × V)) (rank : V → Nat)
    (hrank : ∀ {x y}, (x, y) ∈ E → rank x < rank y) :
    ¬ ContainsReverseDirectedRay E := by
  rintro ⟨R, hR⟩
  have hdesc (n : Nat) : rank (R.vertex (n + 1)) < rank (R.vertex n) :=
    hrank (hR n)
  have hbound : ∀ n, rank (R.vertex n) + n ≤ rank (R.vertex 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hs := hdesc n
        omega
  have h := hbound (rank (R.vertex 0) + 1)
  omega

private theorem directionEdges_endpoints_mem_vertexSet
    {Q : AltPath Gamma.graph} {d : Direction} {e : V × V}
    (he : e ∈ Q.directionEdges d) :
    e.1 ∈ Q.vertexSet ∧ e.2 ∈ Q.vertexSet := by
  simp only [AltPath.directionEdges, Set.mem_iUnion] at he
  obtain ⟨l, hl, _hd, hel⟩ := he
  have hs := l.path.edgeSet_subset_support_prod hel
  exact ⟨Q.link_support_subset_vertexSet hl hs.1,
    Q.link_support_subset_vertexSet hl hs.2⟩

private theorem finiteClassification_endpoints_not_mem
    {W : Set Gamma.DPath} {X : Set V}
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (s : {z : V // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet C.selectedReference}) (v : V)
    (hsv : (A.assignment.assigned s).terminal? = some v)
    (K : LimitingFiniteContactClassification C X
      (A.assignment.assigned s) s.1 v)
    {e : V × V} (he : e ∈ K.retainedEdges) :
    e.1 ∉ X ∧ e.2 ∉ X := by
  have havoid : Disjoint (A.assignment.assigned s).vertexSet X := by
    simpa only [OutsideMacroFullAssignment.assignment_assigned] using
      A.full_avoids s
  have hdisjoint := Set.disjoint_left.1 havoid
  cases K with
  | imaginary _ =>
      simp only [LimitingFiniteContactClassification.retainedEdges,
        Set.mem_singleton_iff] at he
      rcases he with ⟨rfl, rfl⟩
      have hs : s.1 ∈ (A.assignment.assigned s).vertexSet := by
        rw [← A.assignment.starts_at s]
        exact (A.assignment.assigned s).initial_mem_vertexSet
      exact ⟨hdisjoint hs,
        hdisjoint ((A.assignment.assigned s).mem_vertexSet_of_terminal_eq
          hsv)⟩
  | initialCovered _ =>
      have hend := directionEdges_endpoints_mem_vertexSet he
      exact ⟨hdisjoint hend.1, hdisjoint hend.2⟩
  | terminalCovered _ =>
      have hend := directionEdges_endpoints_mem_vertexSet he
      exact ⟨hdisjoint hend.1, hdisjoint hend.2⟩

private theorem infiniteClassification_endpoints_not_mem
    {W : Set Gamma.DPath} {X persistent : Set V}
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (s : {z : V // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet C.selectedReference})
    (K : LimitingInfiniteContactClassification C X persistent
      (A.assignment.assigned s) s.1)
    {e : V × V} (he : e ∈ K.retainedEdges) :
    e.1 ∉ X ∧ e.2 ∉ X := by
  cases K with
  | popular _ =>
      simp [LimitingInfiniteContactClassification.retainedEdges] at he
  | initialCovered _ =>
      have hend := directionEdges_endpoints_mem_vertexSet he
      have havoid : Disjoint (A.assignment.assigned s).vertexSet X := by
        simpa only [OutsideMacroFullAssignment.assignment_assigned] using
          A.full_avoids s
      have hdisjoint := Set.disjoint_left.1 havoid
      exact ⟨hdisjoint hend.1, hdisjoint hend.2⟩

/-- Every edge retained by the concrete global classification has both
endpoints outside the closing set. -/
theorem outsideMacroRetainedEdges_endpoints_not_mem
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
      before innerRoof outerRoof kappa)
    {e : V × V}
    (he : e ∈ C.outsideMacroRetainedEdges (persistent := persistent)
      hSafeRoof A hW hsource hterminal hclosed) :
    e.1 ∉ X ∧ e.2 ∉ X := by
  rcases he with he | he
  · obtain ⟨s, v, hsv, he⟩ := he
    exact C.finiteClassification_endpoints_not_mem A s v hsv _ he
  · obtain ⟨s, hinfinite, he⟩ := he
    exact C.infiniteClassification_endpoints_not_mem A s _ he

/-- The literal complementary inside relation.  This is the edge relation
realized by the canonical inside-cut family, isolated here without importing
the obsolete aggregate stage-geometry module. -/
def outsideMacroInsideEdges (W : Set Gamma.DPath) (X : Set V) :
    Set (V × V) := familyEdges W ∩ (X ×ˢ X)

theorem outsideMacroInsideEdges_biUnique
    {W : Set Gamma.DPath} {X : Set V} (hW : Gamma.IsWarp W) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ outsideMacroInsideEdges W X) := by
  constructor
  · intro x y z hxz hyz
    exact (Alternating.IsWarp.familyEdges_leftUnique hW) hxz.1 hyz.1
  · intro x y z hxy hxz
    exact (Alternating.IsWarp.familyEdges_rightUnique hW) hxy.1 hxz.1

/-- An inside edge and a globally classified outside edge cannot have a
common target. -/
theorem outsideMacroInside_retained_cross_in
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
      before innerRoof outerRoof kappa)
    {x y z : V}
    (hxz : (x, z) ∈ outsideMacroInsideEdges W X)
    (hyz : (y, z) ∈ C.outsideMacroRetainedEdges
      (persistent := persistent) hSafeRoof A hW hsource hterminal hclosed) :
    x = y := by
  exact False.elim
    ((C.outsideMacroRetainedEdges_endpoints_not_mem hSafeRoof A hW hsource
      hterminal hclosed hyz).2 hxz.2.2)

/-- An inside edge and a globally classified outside edge cannot have a
common source. -/
theorem outsideMacroInside_retained_cross_out
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
      before innerRoof outerRoof kappa)
    {x y z : V}
    (hxy : (x, y) ∈ outsideMacroInsideEdges W X)
    (hxz : (x, z) ∈ C.outsideMacroRetainedEdges
      (persistent := persistent) hSafeRoof A hW hsource hterminal hclosed) :
    y = z := by
  exact False.elim
    ((C.outsideMacroRetainedEdges_endpoints_not_mem hSafeRoof A hW hsource
      hterminal hclosed hxz).1 hxy.2.1)

/-- Adding the inside edges preserves the common strict row rank. -/
theorem outsideMacroInside_union_retained_rank
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hsub : outsideReference C.selectedReference X ⊆
      outsideReference W X)
    (hnontrivial : A.AssignedEndpointsNontrivial)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa)
    {x y : V}
    (hxy : (x, y) ∈ outsideMacroInsideEdges W X ∪
      C.outsideMacroRetainedEdges (persistent := persistent)
        hSafeRoof A hW hsource hterminal hclosed) :
    outsideMacroRowRank W hW x < outsideMacroRowRank W hW y := by
  rcases hxy with hxy | hxy
  · exact outsideMacroRowRank_lt_of_mem_familyEdges hW hxy.1
  · exact C.outsideMacroRetainedEdges_rank hSafeRoof A hW hWfinite hsub
      hnontrivial hsource hterminal hclosed hxy

/-- The exact inside-plus-global-outside relation is acyclic. -/
theorem outsideMacroInside_union_retained_acyclic
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hsub : outsideReference C.selectedReference X ⊆
      outsideReference W X)
    (hnontrivial : A.AssignedEndpointsNontrivial)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa) :
    ¬ ContainsDirectedCycle
      (outsideMacroInsideEdges W X ∪
        C.outsideMacroRetainedEdges (persistent := persistent)
          hSafeRoof A hW hsource hterminal hclosed) := by
  apply no_directed_cycle_of_strict_rank _ (outsideMacroRowRank W hW)
  exact C.outsideMacroInside_union_retained_rank hSafeRoof A hW hWfinite
    hsub hnontrivial hsource hterminal hclosed

/-- The same rank excludes reverse rays after adjoining the inside edges. -/
theorem outsideMacroInside_union_retained_no_reverse_ray
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hsub : outsideReference C.selectedReference X ⊆
      outsideReference W X)
    (hnontrivial : A.AssignedEndpointsNontrivial)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa) :
    ¬ ContainsReverseDirectedRay
      (outsideMacroInsideEdges W X ∪
        C.outsideMacroRetainedEdges (persistent := persistent)
          hSafeRoof A hW hsource hterminal hclosed) := by
  apply no_reverse_ray_of_strict_rank _ (outsideMacroRowRank W hW)
  exact C.outsideMacroInside_union_retained_rank hSafeRoof A hW hWfinite
    hsub hnontrivial hsource hterminal hclosed

end ClubStageGeometry
end Erdos599.Blueprint.LinkageBlueprint
