/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeLinkArrowCommutation

/-!
# Finite-arrow ancestry for the Section 6 accumulation

The dependent Section 6 successors have finite character.  Thus an old
finite thread which survives the next quotient has a finite successor; this
is the local fact needed in the candidate branch of the finite-arrow
ancestry induction.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- A surviving finite stage member has a finite representative in the next
stage, not merely an unspecified path. -/
theorem exists_sectionSixAccumNext_finite_path_extending_old_finite
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V)
    (s : G.SectionSixAccumStage)
    (p : DirectedPath.FinitePath (G.quotient s.carrier).graph)
    (hp : (Sum.inl p : (G.quotient s.carrier).DPath) ∈ s.wave.1)
    (hpSurvives : p.finish ∉
      (G.quotient s.carrier).strictRoof
        (G.sectionSixAccumNextCarrier F K Y Q T s)) :
    ∃ r : DirectedPath.FinitePath (G.quotient
        (G.sectionSixAccumNextCarrier F K Y Q T s)).graph,
      (Sum.inl r : (G.quotient
        (G.sectionSixAccumNextCarrier F K Y Q T s)).DPath) ∈
          (G.sectionSixAccumOldInNext hNoEnter F K Y Q T s).1 ∧
      r.support = ((G.quotient s.carrier).terminalRoofSuffix
          (G.sectionSixAccumNextCarrier F K Y Q T s) p).support ∧
      r.finish = p.finish ∧
      ∃ q : DirectedPath.FinitePath (G.quotient
          (G.sectionSixAccumNextCarrier F K Y Q T s)).graph,
        (Sum.inl q : (G.quotient
          (G.sectionSixAccumNextCarrier F K Y Q T s)).DPath) ∈
            (G.sectionSixAccumNext hNoEnter F K Y Q T s).wave.1 ∧
        (G.quotient
          (G.sectionSixAccumNextCarrier F K Y Q T s)).Extends
            (Sum.inl r) (Sum.inl q) := by
  obtain ⟨r, hrOld, hrSupport, hrTerminal, q, hqNext, hrq, _hrqSupport⟩ :=
    G.exists_sectionSixAccumNext_path_extending_old_finite
      hNoEnter F K Y Q T s p hp hpSurvives
  obtain ⟨rf, rfl⟩ := G.hasFiniteCharacter_waveToLargerQuotient_basic
    hNoEnter (G.sectionSixAccumStage_carrier_subset_next F K Y Q T s)
      s.wave hrOld
  obtain ⟨qf, rfl⟩ :=
    G.sectionSixAccumNext_hasFiniteCharacter hNoEnter F K Y Q T s hqNext
  have hrFinish : rf.finish = p.finish := by
    simpa only [DWeb.terminal?_finite, Option.some.injEq] using hrTerminal
  exact ⟨rf, hrOld, hrSupport, hrFinish, qf, hqNext, hrq⟩

/-- The endpoint-free ancestry conclusion for one finite accumulated-arrow
member at one dependent stage. -/
def SectionSixAccumFiniteArrowWeakPredecessor
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) (n : ℕ)
    (p : DirectedPath.FinitePath
      (G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).graph) : Prop :=
    (Sum.inl p : (G.quotient
        (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).DPath) =
        (G.quotient
          (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).trivialPath p.start ∨
      ∃ q : DirectedPath.FinitePath (G.quotient
          (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).graph,
        (Sum.inl q : (G.quotient
          (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).DPath) ∈
            (G.sectionSixAccumStage hNoEnter F K Y Q T y n).wave.1 ∧
        ((G.quotient
          (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier).terminalRoofSuffix
            (G.sectionSixAccumClosure hNoEnter F K Y Q T y) q).support =
              p.support ∧
        q.finish = p.finish

/-- The endpoint-free finite-arrow ancestry invariant.  This is the natural
induction statement for finite-character successors: the terminal
essentiality used by the final application is not available at an
intermediate arrow contact. -/
def HasSectionSixAccumFiniteArrowWeakFinalSuffix
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) : Prop :=
  ∀ (n : ℕ)
    (p : DirectedPath.FinitePath
      (G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).graph),
    (Sum.inl p : (G.quotient
        (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).DPath) ∈
      ((G.quotient
        (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).omegaArrowStage
          (G.sectionSixAccumCommonStage hNoEnter F K Y Q T y) n).1 →
    G.SectionSixAccumFiniteArrowWeakPredecessor
      hNoEnter F K Y Q T y n p

/-- The one-step commutation property needed by the endpoint-free ancestry
induction.  It says that applying the common-quotient arrow and advancing the
dependent accumulator have the same finite final-roof suffix. -/
def HasSectionSixAccumFiniteArrowWeakSuccessor
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V) : Prop :=
  ∀ (n : ℕ)
    (f p : DirectedPath.FinitePath
      (G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).graph)
    (hf : (Sum.inl f : (G.quotient
      (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).DPath) ∈
        ((G.quotient
          (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).omegaArrowStage
            (G.sectionSixAccumCommonStage hNoEnter F K Y Q T y) n).1),
    (G.quotient (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).arrowPath
      ((G.quotient
        (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).omegaArrowStage
          (G.sectionSixAccumCommonStage hNoEnter F K Y Q T y) n).1
      (G.sectionSixAccumCommonStage hNoEnter F K Y Q T y (n + 1)).1
      ⟨Sum.inl f, hf⟩ = Sum.inl p →
    G.SectionSixAccumFiniteArrowWeakPredecessor
      hNoEnter F K Y Q T y n f →
    G.SectionSixAccumFiniteArrowWeakPredecessor
      hNoEnter F K Y Q T y (n + 1) p

/-- Once the local arrow/transport square commutes, endpoint-free ancestry is
formal induction on the finite accumulated arrow. -/
theorem sectionSixAccumFiniteArrowWeakFinalSuffix_of_successor
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V)
    (hSucc : G.HasSectionSixAccumFiniteArrowWeakSuccessor
      hNoEnter F K Y Q T y) :
    G.HasSectionSixAccumFiniteArrowWeakFinalSuffix
      hNoEnter F K Y Q T y := by
  intro n
  induction n with
  | zero =>
      intro p hp
      exact G.finite_mem_sectionSixAccumCommonStage_trivial_or_finalSuffix
        hNoEnter F K Y Q T y 0 p (by
          simpa only [DWeb.omegaArrowStage_zero] using hp)
  | succ n ih =>
      intro p hp
      rw [DWeb.omegaArrowStage_succ] at hp
      obtain ⟨a, ha⟩ := hp
      rcases haPath : a.1 with f | r
      · have hf : (Sum.inl f : (G.quotient
            (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).DPath) ∈
          ((G.quotient
            (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).omegaArrowStage
              (G.sectionSixAccumCommonStage hNoEnter F K Y Q T y) n).1 := by
          simpa only [haPath] using a.2
        have haEq : a = ⟨Sum.inl f, hf⟩ := Subtype.ext haPath
        subst a
        exact hSucc n f p hf ha (ih f hf)
      · have hr : (Sum.inr r : (G.quotient
            (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).DPath) ∈
          ((G.quotient
            (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).omegaArrowStage
              (G.sectionSixAccumCommonStage hNoEnter F K Y Q T y) n).1 := by
          simpa only [haPath] using a.2
        have haEq : a = ⟨Sum.inr r, hr⟩ := Subtype.ext haPath
        subst a
        rw [(G.quotient
          (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).arrowPath_ray] at ha
        cases ha

/-- The endpoint-free invariant is stronger than the final-essential form
consumed by the provenance reduction. -/
theorem HasSectionSixAccumFiniteArrowWeakFinalSuffix.strong
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V)
    (h : G.HasSectionSixAccumFiniteArrowWeakFinalSuffix
      hNoEnter F K Y Q T y) :
    G.HasSectionSixAccumFiniteArrowFinalSuffix
      hNoEnter F K Y Q T y := by
  intro _hSource n p hp _hpStart _hpEssential
  exact h n p hp

/-- The endpoint-free invariant immediately supplies the raw pointwise
provenance statement.  Keeping this bridge next to the invariant leaves the
Section 6 specialization responsible only for the elementary source/carrier
disjointness check. -/
theorem HasSectionSixAccumFiniteArrowWeakFinalSuffix.provenance
    (hNoEnter : G.NoEdgeEnters G.source)
    (F K : V → Set V) (Y Q T : Set V) (y : V)
    (h : G.HasSectionSixAccumFiniteArrowWeakFinalSuffix
      hNoEnter F K Y Q T y)
    (hSourceX : Disjoint G.source
      (G.sectionSixAccumClosure hNoEnter F K Y Q T y)) :
    ∀ z ∈ (G.quotient
      (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).vertexSet
        ((G.quotient
          (G.sectionSixAccumClosure hNoEnter F K Y Q T y)).essentialMeetingPaths
            (G.sectionSixAccumCommonWave hNoEnter F K Y Q T y).1
            (G.sectionSixAccumClosure hNoEnter F K Y Q T y)),
      ∃ n, z ∈ G.meetingVertexSet
        (G.sectionSixAccumStageLift
          (G.sectionSixAccumStage hNoEnter F K Y Q T y n))
        (G.sectionSixAccumStage hNoEnter F K Y Q T y n).carrier := by
  exact G.sectionSixAccumProvenance_of_finiteArrowFinalSuffix
    hNoEnter F K Y Q T y
      (HasSectionSixAccumFiniteArrowWeakFinalSuffix.strong
        G hNoEnter F K Y Q T y h) hSourceX

end DWeb

end Erdos599
