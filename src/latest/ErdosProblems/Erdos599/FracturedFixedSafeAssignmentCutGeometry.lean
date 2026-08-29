/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedFixedSafeAssignment
import ErdosProblems.Erdos599.OutsideFracturedColouredDichotomy

/-!
# Cut geometry of the actual simultaneous fixed-family assignment

The geometric certificates are retained for the same words whose finite
terminals were selected injectively. No new single-source choices replace
those words after Hall selection.
-/

namespace Erdos599.Blueprint.LinkageBlueprint.FracturedFixedSafeAssignment

open Set DirectedPath Alternating FracturedDuplication FracturedAssignmentPeel
open FracturedCanonicalBoundary FracturedCanonicalSafeProjection
open ColouredSafeReverseReachability FiniteColouredOccurrenceWord

universe u

variable {V : Type u} {Gamma : DWeb V} {Y W : Set Gamma.DPath} {X : Set V}

/-- The actual finite/infinite endpoint avoidance and externality needed
by the closed-hammock argument. -/
structure HasCutGeometry {current Y : Set Gamma.DPath} {s : V}
    (X : Set V) (A : CurrentSafeOccurrence current Y s) : Prop where
  finite_cut : ∀ t, A.terminal? = some t → A.vertexSet ∩ X ⊆ {s, t}
  infinite_cut : A.terminal? = none → A.vertexSet ∩ X ⊆ {s}
  not_contained : ¬ A.vertexSet ⊆ X

/-- Every legal canonical occurrence has cut geometry after the literal
projection used by the simultaneous assignment. -/
theorem projectOccurrence_hasCutGeometry (F : OutsideFracturedWarp W X)
    (hboundary : BoundaryAligned F.holes.paths Y)
    (hY : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet F.holes.paths)
    (hX : Disjoint X (Gamma.vertexSet Y))
    (s : ExposedInitial (canonicalActiveLift F.holes)
      (canonicalPeeledReferenceLift F.holes Y))
    (A : CurrentSafeOccurrence (canonicalActiveLift F.holes)
      (canonicalPeeledReferenceLift F.holes Y) s.1)
    (hterminal : ∀ {t}, A.terminal? = some t →
      t ∈ (web Gamma F.holes).terminalFrontier (canonicalActiveLift F.holes) \
        (web Gamma F.holes).vertexSet (canonicalPeeledReferenceLift F.holes Y)) :
    HasCutGeometry X (projectOccurrence F.holes hboundary hY hYfinite hsource
      (F.noJunctionOnPeeledReference hboundary hY hX) s A hterminal) := by
  cases A with
  | infinite Q hQ hfirst =>
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        simp [projectOccurrence, CurrentSafeOccurrence.terminal?] at ht
      · intro _
        change (infiniteSafeProjection F.holes hY hYfinite Q).vertexSet ∩ X ⊆
          {project s.1}
        simpa only [hfirst] using
          F.infiniteSafeProjection_inter_cut_subset_initial hY hYfinite hX Q
      · exact F.infiniteWord_not_vertexSet_subset_cut hX
          (infiniteSafeProjection F.holes hY hYfinite Q)
  | finite t Q hQ hfirst hlast =>
      have ht := hterminal (t := t) rfl
      have hfirstW : Q.vertex 0 ∈
          (web Gamma F.holes).initialSet (canonicalActiveLift F.holes) := by
        simpa only [hfirst] using s.2.1
      have hfirstOff : Q.vertex 0 ∉ (web Gamma F.holes).vertexSet
          (canonicalPeeledReferenceLift F.holes Y) := by
        simpa only [hfirst] using s.2.2
      have hlastW : Q.vertex (Fin.last Q.length) ∈
          (web Gamma F.holes).terminalFrontier (canonicalActiveLift F.holes) := by
        simpa only [hlast] using ht.1
      refine ⟨?_, ?_, ?_⟩
      · intro v hv
        have htv : project t = v := Option.some.inj hv
        change (finiteSafeProjection F.holes hYfinite Q).vertexSet ∩ X ⊆ {project s.1, v}
        simpa only [hfirst, hlast, htv] using
          F.finiteSafeProjection_inter_cut_subset_endpoints hYfinite hX Q hfirstW
      · intro hnone
        simp [projectOccurrence, CurrentSafeOccurrence.terminal?] at hnone
      · exact F.finiteSafeProjection_not_vertexSet_subset_cut hYfinite hX Q
          hfirstW hfirstOff hlastW

/-- The simultaneous fixed-original assignment with all cut certificates
on its actual chosen words. Terminal injectivity is retained in `A`. -/
theorem exists_outside_assignment_with_cutGeometry (F : OutsideFracturedWarp W X)
    (hsub : Blueprint.HasHereditarySubdivisionIncidence Gamma.graph)
    (hboundary : BoundaryAligned F.holes.paths Y)
    (hY : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet F.holes.paths)
    (hX : Disjoint X (Gamma.vertexSet Y)) :
    ∃ A : Assignment F.holes Y, ∀ s, HasCutGeometry X (A.assigned s) := by
  apply exists_assignment_with_property F.holes hsub hboundary hY F.finiteCharacter
    hYfinite hsource (F.noJunctionOnPeeledReference hboundary hY hX)
    (fun _ A ↦ HasCutGeometry X A)
  · intro s hs
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      have hst : s.1 = t := Option.some.inj ht
      subst t
      rintro x ⟨hx, _hxX⟩
      have hxs : x = s.1 := by simpa [CurrentSafeOccurrence.vertexSet] using hx
      exact Or.inl hxs
    · intro hnone
      cases hnone
    · intro hcontained
      exact F.singleton_not_mem_cut hs (hcontained ⟨0, rfl⟩)
  · intro s hs A hterminal
    exact projectOccurrence_hasCutGeometry F hboundary hY hYfinite hsource hX
      (liftedSource F.holes hboundary F.finiteCharacter s hs) A hterminal

#print axioms projectOccurrence_hasCutGeometry
#print axioms exists_outside_assignment_with_cutGeometry

end Erdos599.Blueprint.LinkageBlueprint.FracturedFixedSafeAssignment
