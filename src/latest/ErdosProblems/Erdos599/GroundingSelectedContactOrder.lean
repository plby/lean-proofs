/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingCutDecoder
import ErdosProblems.Erdos599.GroundingSimultaneousDecode
import ErdosProblems.Erdos599.PopularLayers

/-!
# Order of an off-apex contact of a selected grounding route

A selected auxiliary route ends at its request apex, which belongs to the
popular cut.  Thus the whole route does not avoid the cut.  If the route
meets an old vertex away from that apex, however, the prefix ending at the
first such meeting does avoid the cut: normalization says that the apex is
the route's only possible cut vertex, and a proper prefix of a simple path
cannot contain its terminal vertex.  Assertion 8.21 may consequently be
applied to every such old-vertex contact.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace GroundingSelectedContactOrder

open DirectedPath
open PopularGroundingBridge

universe u

variable {V I : Type u} {Gamma : DWeb V}

abbrev LV (L : PopularAuxiliary.Input Gamma I) :=
  PopularAuxiliary.Input.LambdaVertex V I

abbrev Path (L : PopularAuxiliary.Input Gamma I) :=
  FinitePath L.lambda.graph

/-- The first prefix of a normalized request-fan member ending at an old
contact distinct from the request apex avoids the complete popular cut. -/
theorem firstHit_oldContact_avoids_cut
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut)
    {p : Path L}
    (hp : p ∈ (GroundingAssembly.normalizedRequestFan S K r).paths)
    {x : V} (hx : (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ∈
      p.support)
    (hoff : (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ≠
      requestAuxVertex r) :
    let hmeet : p.walk.Meets
        ({PopularAuxiliary.Input.LambdaVertex.old x} : Set (LV L)) :=
      ⟨.old x, hx, Set.mem_singleton _⟩
    L.lambda.Avoids
      (p.firstHit ({PopularAuxiliary.Input.LambdaVertex.old x} : Set (LV L))
        hmeet) S.cut := by
  let hmeet : p.walk.Meets
      ({PopularAuxiliary.Input.LambdaVertex.old x} : Set (LV L)) :=
    ⟨.old x, hx, Set.mem_singleton _⟩
  let q := p.firstHit
    ({PopularAuxiliary.Input.LambdaVertex.old x} : Set (LV L)) hmeet
  have hpfinish : p.finish = requestAuxVertex r :=
    Set.mem_singleton_iff.mp
      ((GroundingAssembly.normalizedRequestFan S K r).ends_in_join hp)
  have hpfinishNot :
      p.finish ∉ ({PopularAuxiliary.Input.LambdaVertex.old x} : Set (LV L)) := by
    intro h
    have heq : p.finish = .old x := Set.mem_singleton_iff.mp h
    exact hoff (heq.symm.trans hpfinish)
  have hpfinishNotQ : p.finish ∉ q.support := by
    exact Popular.firstHit_not_mem_of_finish_not_mem p
      ({PopularAuxiliary.Input.LambdaVertex.old x} : Set (LV L))
        hmeet hpfinishNot
  have hapexNotQ : requestAuxVertex r ∉ q.support := by
    intro h
    exact hpfinishNotQ (hpfinish ▸ h)
  change Disjoint q.support S.cut
  rw [Set.disjoint_left]
  intro z hzq hzcut
  have hzp : z ∈ p.support := p.firstHit_support_subset _ hmeet hzq
  have hzApex := GroundingAssembly.normalizedRequestFan_cut_normalized
    S K r hp ⟨hzp, hzcut⟩
  exact hapexNotQ (Set.mem_singleton_iff.mp hzApex ▸ hzq)

/-- Assertion 8.21 for an arbitrary normalized request route at an
off-apex old contact.  The explicit blockability premise is exactly the
premise of the source blocking-point lemma. -/
theorem normalizedRoute_contact_beforeEq_blockingPoint
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut)
    {p : Path L}
    (hp : p ∈ (GroundingAssembly.normalizedRequestFan S K r).paths)
    (P : L.Fragment) (hP : P ∈ GroundingCut.G0 L S.cut)
    (hblockable : GroundingCut.IsBlockable L S.cut P)
    {x : V}
    (hx : (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ∈ p.support)
    (hxP : x ∈ P.path.support)
    (hoff : (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ≠
      requestAuxVertex r) :
    GroundingCut.BeforeEq P.path x
      (GroundingCut.blockingPoint L S.cut P) := by
  let hmeet : p.walk.Meets
      ({PopularAuxiliary.Input.LambdaVertex.old x} : Set (LV L)) :=
    ⟨.old x, hx, Set.mem_singleton _⟩
  let q := p.firstHit
    ({PopularAuxiliary.Input.LambdaVertex.old x} : Set (LV L)) hmeet
  apply GroundingCutDecoder.assertion8_21 L S.cut S.separates P hP q
  · change p.start ∈ L.lambda.source
    exact (GroundingAssembly.normalizedRequestFan S K r).starts_in_source hp
  · exact firstHit_oldContact_avoids_cut S K r hp hx hoff
  · exact Set.mem_singleton_iff.mp (p.firstHit_finish_mem _ hmeet)
  · exact hxP

/-- The component-compatible route selected for a request satisfies the
same Assertion 8.21 order bound at every off-apex old contact. -/
theorem strongSelectedPath_contact_beforeEq_blockingPoint
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (r : Request L S.cut)
    (P : L.Fragment) (hP : P ∈ GroundingCut.G0 L S.cut)
    (hblockable : GroundingCut.IsBlockable L S.cut P)
    {x : V}
    (hx : (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ∈
      (GroundingSimultaneousDecode.strongSelectedPath U S K r).support)
    (hxP : x ∈ P.path.support)
    (hoff : (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ≠
      requestAuxVertex r) :
    GroundingCut.BeforeEq P.path x
      (GroundingCut.blockingPoint L S.cut P) := by
  exact normalizedRoute_contact_beforeEq_blockingPoint S K r
    (hp := (GroundingSimultaneousDecode.strongSelectedPath_mem_controlledRequestFan
      U S K r).1) P hP hblockable hx hxP hoff

end GroundingSelectedContactOrder
end Erdos599
