/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingCut
import ErdosProblems.Erdos599.RelationComponents
import ErdosProblems.Erdos599.SafeSwitching
import ErdosProblems.Erdos599.AlternatingSourceAssertions

/-!
# The surviving-component relation on a ladder path

The witnesses in `GroundingCut.SurvivingConnected` are directed finite
subpaths, but the relation itself forgets their orientation.  Consequently,
transitivity cannot in general be proved by directly appending the two given
witnesses.  We instead take the finite union of their edge sets, form its
weak component inside the simple parent path, and trim the canonical directed
component path between the desired endpoints.

The resulting equivalence laws show that the maximality equation in
`GroundingCut.IsDeletedFragment` really makes deleted fragments the
equivalence classes of this relation.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingFragmentRelation

open DirectedPath
open Alternating.RelationComponents

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) : Type (max u v) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (_L : Input Gamma I) : Type (max u v) :=
  PopularAuxiliary.Input.LambdaVertex V I

private theorem walk_connected_of_edgeSet_subset
    {E : Set (V × V)} {a b : V} (w : Walk Gamma.graph a b)
    (hw : w.edgeSet ⊆ E) :
    Relation.ReflTransGen (WeakRel E) a b := by
  induction w with
  | nil => exact .refl
  | @cons a c b hac w ih =>
      have htail : w.edgeSet ⊆ E := by
        intro e he
        exact hw (Set.mem_union_right _ he)
      exact (ih htail).head (Or.inl (hw (by simp [Walk.edgeSet])))

private theorem componentMk_eq_of_path
    {E : Set (V × V)} (q : FinitePath Gamma.graph)
    (hqE : q.edgeSet ⊆ E) {x y : V}
    (hends : (q.start = x ∧ q.finish = y) ∨
      (q.start = y ∧ q.finish = x)) :
    componentMk E x = componentMk E y := by
  have hwalk : Relation.ReflTransGen (WeakRel E) q.start q.finish :=
    walk_connected_of_edgeSet_subset q.walk hqE
  have hcomp : componentMk E q.start = componentMk E q.finish :=
    Quotient.sound hwalk
  rcases hends with hends | hends
  · simpa [hends.1, hends.2] using hcomp
  · simpa [hends.1, hends.2] using hcomp.symm

/-- Surviving connectivity is reflexive at every vertex of the parent path. -/
theorem survivingConnected_refl
    (L : Input Gamma I) (C : Set (LV L)) (parent : Gamma.DPath)
    {x : V} (hx : x ∈ parent.support) :
    GroundingCut.SurvivingConnected L C parent x x := by
  let q := FinitePath.trivial Gamma.graph x
  refine ⟨q, Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro y hy
    have hyx : y = x := by
      simpa [q, FinitePath.trivial, FinitePath.support, Walk.support] using hy
    simpa [hyx] using hx
  · simp [q, FinitePath.trivial, FinitePath.edgeSet]
  · simp [q, FinitePath.trivial, FinitePath.edgeSet]

/-- Surviving connectivity is symmetric because its endpoint condition
admits either orientation of the directed witness. -/
theorem survivingConnected_symm
    (L : Input Gamma I) (C : Set (LV L)) (parent : Gamma.DPath)
    {x y : V} :
    GroundingCut.SurvivingConnected L C parent x y →
      GroundingCut.SurvivingConnected L C parent y x := by
  rintro ⟨q, hends, hsupp, hedge, hdis⟩
  exact ⟨q, hends.elim Or.inr Or.inl, hsupp, hedge, hdis⟩

/-- Surviving connectivity is transitive.  The proof retains the corrected
edge-level subpath condition from `GroundingCut.SurvivingConnected`. -/
theorem survivingConnected_trans
    (L : Input Gamma I) (C : Set (LV L)) (parent : Gamma.DPath)
    {x y z : V}
    (hxy : GroundingCut.SurvivingConnected L C parent x y)
    (hyz : GroundingCut.SurvivingConnected L C parent y z) :
    GroundingCut.SurvivingConnected L C parent x z := by
  classical
  rcases hxy with ⟨q, hqends, hqsupp, hqedge, hqdis⟩
  rcases hyz with ⟨r, hrends, hrsupp, hredge, hrdis⟩
  have hxq : x ∈ q.support := by
    rcases hqends with hends | hends
    · rw [← hends.1]
      exact q.start_mem_support
    · rw [← hends.2]
      exact q.finish_mem_support
  by_cases hxz : x = z
  · subst z
    exact survivingConnected_refl L C parent (hqsupp hxq)
  let E : Set (V × V) := q.edgeSet ∪ r.edgeSet
  have hEparent : E ⊆ parent.edgeSet := by
    intro e he
    rcases he with he | he
    · exact hqedge he
    · exact hredge he
  have hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2} :=
    hEparent.trans parent.edgeSet_subset_adj
  have hEdis : Disjoint E (GroundingCut.CE L C) := by
    rw [Set.disjoint_left]
    intro e he hce
    rcases he with he | he
    · exact Set.disjoint_left.1 hqdis he hce
    · exact Set.disjoint_left.1 hrdis he hce
  have hparentUnique := Alternating.Path.edgeSet_biUnique parent
  have hout : ∀ {a b d : V}, (a, b) ∈ E → (a, d) ∈ E → b = d := by
    intro a b d hab had
    exact hparentUnique.2 (hEparent hab) (hEparent had)
  have hin : ∀ {a b d : V}, (a, d) ∈ E → (b, d) ∈ E → a = b := by
    intro a b d had hbd
    exact hparentUnique.1 (hEparent had) (hEparent hbd)
  have hqE : q.edgeSet ⊆ E := Set.subset_union_left
  have hrE : r.edgeSet ⊆ E := Set.subset_union_right
  have hxyComp : componentMk E x = componentMk E y :=
    componentMk_eq_of_path q hqE hqends
  have hyzComp : componentMk E y = componentMk E z :=
    componentMk_eq_of_path r hrE hrends
  let c : Component E := componentMk E x
  have hcomponentSubset : componentSupport E c ⊆ q.support ∪ r.support := by
    rw [show c = componentMk E x from rfl,
      componentSupport_componentMk]
    intro w hw
    induction hw with
    | refl => exact Or.inl hxq
    | @tail a b hxa hab ih =>
        rcases hab with hab | hba
        · rcases hab with hab | hab
          · exact Or.inl (q.edgeSet_subset_support_prod hab).2
          · exact Or.inr (r.edgeSet_subset_support_prod hab).2
        · rcases hba with hba | hba
          · exact Or.inl (q.edgeSet_subset_support_prod hba).1
          · exact Or.inr (r.edgeSet_subset_support_prod hba).1
  have hcfinite : (componentSupport E c).Finite :=
    (q.support_finite.union r.support_finite).subset hcomponentSubset
  let s : FinitePath Gamma.graph :=
    componentPath (D := Gamma.graph) E c hcfinite
  have hsSpec : IsComponentPath E c s :=
    (componentPath_spec (D := Gamma.graph) E c hcfinite).1
  have hsSupport : s.support = componentSupport E c :=
    componentPath_support_eq E hEadj hout hin c hcfinite
  have hxc : x ∈ componentSupport E c := componentMk_mem E x
  have hzc : z ∈ componentSupport E c := by
    change componentMk E z = componentMk E x
    exact (hxyComp.trans hyzComp).symm
  have hxs : x ∈ s.support := hsSupport.symm.subset hxc
  have hzs : z ∈ s.support := hsSupport.symm.subset hzc
  have hsParent : s.support ⊆ parent.support := by
    rw [hsSupport]
    exact hcomponentSubset.trans (Set.union_subset hqsupp hrsupp)
  rcases s.orderedOccurrence_or_reverse hxs hzs hxz with hforward | hbackward
  · rcases hforward with ⟨hforward⟩
    let t : FinitePath Gamma.graph := s.between hforward
    refine ⟨t, Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · exact (s.between_support_subset hforward).trans hsParent
    · exact (s.between_edgeSet_subset hforward).trans
        (hsSpec.1.trans hEparent)
    · rw [Set.disjoint_left]
      intro e het heC
      exact Set.disjoint_left.1 hEdis
        (hsSpec.1 (s.between_edgeSet_subset hforward het)) heC
  · rcases hbackward with ⟨hbackward⟩
    let t : FinitePath Gamma.graph := s.between hbackward
    refine ⟨t, Or.inr ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · exact (s.between_support_subset hbackward).trans hsParent
    · exact (s.between_edgeSet_subset hbackward).trans
        (hsSpec.1.trans hEparent)
    · rw [Set.disjoint_left]
      intro e het heC
      exact Set.disjoint_left.1 hEdis
        (hsSpec.1 (s.between_edgeSet_subset hbackward het)) heC

/-- Any two vertices of one deleted fragment are surviving-connected in its
parent path. -/
theorem survivingConnected_of_mem_fragment
    {L : Input Gamma I} {C : Set (LV L)} {P : L.Fragment}
    (hP : P ∈ GroundingCut.fragments L C) {x y : V}
    (hx : x ∈ P.path.support) (hy : y ∈ P.path.support) :
    GroundingCut.SurvivingConnected L C P.parent x y := by
  have hxClass : x ∈ {z | z ∈ P.parent.support ∧
      GroundingCut.SurvivingConnected L C P.parent P.path.initial z} := by
    rw [← hP.2]
    exact hx
  have hyClass : y ∈ {z | z ∈ P.parent.support ∧
      GroundingCut.SurvivingConnected L C P.parent P.path.initial z} := by
    rw [← hP.2]
    exact hy
  exact survivingConnected_trans L C P.parent
    (survivingConnected_symm L C P.parent hxClass.2) hyClass.2

/-- Two maximal deleted fragments of the same parent which share a vertex
have the same support. -/
theorem fragment_support_eq_of_parent_eq_of_common
    {L : Input Gamma I} {C : Set (LV L)} {P Q : L.Fragment}
    (hP : P ∈ GroundingCut.fragments L C)
    (hQ : Q ∈ GroundingCut.fragments L C)
    (hparent : P.parent = Q.parent) {w : V}
    (hwP : w ∈ P.path.support) (hwQ : w ∈ Q.path.support) :
    P.path.support = Q.path.support := by
  apply Set.Subset.antisymm
  · intro x hx
    have hQiw : GroundingCut.SurvivingConnected L C Q.parent
        Q.path.initial w :=
      survivingConnected_of_mem_fragment hQ Q.path.initial_mem_support hwQ
    have hPwx : GroundingCut.SurvivingConnected L C P.parent w x :=
      survivingConnected_of_mem_fragment hP hwP hx
    have hQwx : GroundingCut.SurvivingConnected L C Q.parent w x := by
      simpa [hparent] using hPwx
    have hQix : GroundingCut.SurvivingConnected L C Q.parent
        Q.path.initial x := survivingConnected_trans L C Q.parent hQiw hQwx
    rw [hQ.2]
    exact ⟨hparent ▸ P.support_subset hx, hQix⟩
  · intro x hx
    have hPiw : GroundingCut.SurvivingConnected L C P.parent
        P.path.initial w :=
      survivingConnected_of_mem_fragment hP P.path.initial_mem_support hwP
    have hQwx : GroundingCut.SurvivingConnected L C Q.parent w x :=
      survivingConnected_of_mem_fragment hQ hwQ hx
    have hPwx : GroundingCut.SurvivingConnected L C P.parent w x := by
      simpa [hparent] using hQwx
    have hPix : GroundingCut.SurvivingConnected L C P.parent
        P.path.initial x := survivingConnected_trans L C P.parent hPiw hPwx
    rw [hP.2]
    exact ⟨hparent.symm ▸ Q.support_subset hx, hPix⟩

end GroundingFragmentRelation
end Erdos599
