/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingActiveRequestRootTransfer
import ErdosProblems.Erdos599.GroundingCutDecoder

/-!
# Root transfer from a retained active contact to an inactive control

The greedy activity test records a retained forward contact `x` weakly
before an inactive control `c` on one limiting-ladder path.  This file
isolates the remaining purely directed step: if the finite ladder segment
from `x` to `c` survives in the final relation, rootedness of the retained
contact transfers to `c`.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingErasedDecode

open DirectedPath Alternating PopularAuxiliary.Input
open PopularGroundingBridge GroundingSimultaneousDecode

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- Weak path order gives directed reachability whenever the corresponding
finite forward segment is contained in `E`.  The equality case needs no
edge-survival hypothesis. -/
theorem reflTransGen_of_beforeEq_of_forwardSegment_subset
    (E : Set (V × V)) (P : Gamma.DPath) {x y : V}
    (hxy : GroundingCut.BeforeEq P x y)
    (hsurvives : ∀ p : FinitePath Gamma.graph,
      p.start = x → p.finish = y → p.edgeSet ⊆ P.edgeSet →
        p.edgeSet ⊆ E) :
    Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) x y := by
  by_cases h : x = y
  · subst y
    exact .refl
  · obtain ⟨p, hpstart, hpfinish, hpP⟩ :=
      GroundingCutDecoder.exists_forward_segment_of_before ⟨hxy, h⟩
    have hpE : p.edgeSet ⊆ E :=
      hsurvives p hpstart hpfinish hpP
    have hreach := Relation.ReflTransGen.mono
      (r := fun u v ↦ (u, v) ∈ p.edgeSet)
      (p := fun u v ↦ (u, v) ∈ E)
      (fun _ _ he ↦ hpE he) p.start p.finish
        (_root_.Erdos599.Alternating.Walk.reflTransGen_edgeSet p.walk)
    simpa only [hpstart, hpfinish] using hreach

/-- An inactive control is rooted once retained active contacts are rooted
and the ordered ladder segment from such a contact to the control survives.
This theorem packages the exact output of the recursive activity witness;
it makes no global claim that all edges of the exposed component survive. -/
theorem inactiveControl_rooted_of_retainedContact
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (E : Set (V × V)) (A : Set V)
    (c : ControlRequest L S.cut)
    (hc : ¬ IsActiveControl U S K c)
    (hcontactRoot : ∀ d : ActiveControlRequest U S K, ∀ x,
      x ∈ retainedForwardVertices (L := L) S.cut
          (selectedErasedCompression U S K
            (chosenRequest d.1)).path →
        ∃ a ∈ A, Relation.ReflTransGen
          (fun u v ↦ (u, v) ∈ E) a x)
    (hsegmentSurvives : ∀ (d : ActiveControlRequest U S K)
      (Y : Gamma.DPath),
      Y ∈ exposedLadderPaths L
        (strongSelectedPath U S K (chosenRequest d.1)) →
      ∀ x,
      x ∈ retainedForwardVertices (L := L) S.cut
          (selectedErasedCompression U S K
            (chosenRequest d.1)).path →
      x ∈ Y.support → GroundingCut.BeforeEq Y x c.1 →
      ∀ p : FinitePath Gamma.graph,
        p.start = x → p.finish = c.1 → p.edgeSet ⊆ Y.edgeSet →
          p.edgeSet ⊆ E) :
    ∃ a ∈ A,
      Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a c.1 := by
  obtain ⟨d, _hdc, Y, hY, _hcY, x, hx, hxY, hxc⟩ :=
    exists_active_absorber_of_not_active U S K c hc
  obtain ⟨a, ha, hax⟩ := hcontactRoot d x hx
  refine ⟨a, ha, hax.trans ?_⟩
  exact reflTransGen_of_beforeEq_of_forwardSegment_subset E Y hxc
    (hsegmentSurvives d Y hY x hx hxY hxc)

/-- Boundary-parametric inactive-control transfer.  It is the exact analogue
of `inactiveControl_rooted_of_retainedContact` for the active recursion and
retained prefixes stopped at an arbitrary chosen frontier `T`. -/
theorem inactiveControlAt_rooted_of_retainedContact
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T : Set V) (E : Set (V × V)) (A : Set V)
    (c : ControlRequest L S.cut)
    (hc : ¬ IsActiveControlAt U S K T c)
    (hcontactRoot : ∀ d : ActiveControlRequestAt U S K T, ∀ x,
      x ∈ retainedForwardVerticesAt T
          (selectedErasedCompression U S K
            (chosenRequest d.1)).path →
        ∃ a ∈ A, Relation.ReflTransGen
          (fun u v ↦ (u, v) ∈ E) a x)
    (hsegmentSurvives : ∀ (d : ActiveControlRequestAt U S K T)
      (Y : Gamma.DPath),
      Y ∈ exposedLadderPaths L
        (strongSelectedPath U S K (chosenRequest d.1)) →
      ∀ x,
      x ∈ retainedForwardVerticesAt T
          (selectedErasedCompression U S K
            (chosenRequest d.1)).path →
      x ∈ Y.support → GroundingCut.BeforeEq Y x c.1 →
      ∀ p : FinitePath Gamma.graph,
        p.start = x → p.finish = c.1 → p.edgeSet ⊆ Y.edgeSet →
          p.edgeSet ⊆ E) :
    ∃ a ∈ A,
      Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a c.1 := by
  obtain ⟨d, _hdc, Y, hY, _hcY, x, hx, hxY, hxc⟩ :=
    exists_active_absorberAt_of_not_active U S K T c hc
  obtain ⟨a, ha, hax⟩ := hcontactRoot d x hx
  refine ⟨a, ha, hax.trans ?_⟩
  exact reflTransGen_of_beforeEq_of_forwardSegment_subset E Y hxc
    (hsegmentSurvives d Y hY x hx hxY hxc)

end GroundingErasedDecode
end Erdos599
