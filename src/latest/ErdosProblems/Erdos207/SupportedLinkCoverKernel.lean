/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryInternalResidualLinks
import ErdosProblems.Erdos207.SimultaneousRobustLinkCoverFamilyLaw

/-!
# Totalizing the simultaneous link-cover law on support

Pointwise robust matching produces a suitable law only at master states that
actually occur.  This file chooses that law there and uses a no-op law at
irrelevant zero-mass states.  The no-op fibers still satisfy C4, so the
result is a genuine state-dependent kernel usable by `jointBind`.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Existence of the exact law required from the simultaneous link stage at
one state. -/
def HasSimultaneousLinkCoverFamilyLaw
    {O V : Type*} [Fintype O] [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (available P : TripleSystemOn V)
    (K : O → BipartiteLink V) (alpha : ℝ≥0) : Prop :=
  ∃ law : FiniteLaw (TripleSystemOn V),
    law.SupportedOn (fun M ↦
      IsSimultaneousLinkCover F available P K M ∧
        IsSimultaneousLinkFamily K M) ∧
    ∀ Q : TripleSystemOn V,
      law.probability (fun M ↦ Q ⊆ M) ≤ alpha ^ Q.card

/-- Enlarging the uniform inclusion factor preserves link-law readiness. -/
theorem HasSimultaneousLinkCoverFamilyLaw.mono
    {O V : Type*} [Fintype O] [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {available P : TripleSystemOn V}
    {K : O → BipartiteLink V} {alpha alpha' : ℝ≥0}
    (h : HasSimultaneousLinkCoverFamilyLaw F available P K alpha)
    (haa' : alpha ≤ alpha') :
    HasSimultaneousLinkCoverFamilyLaw F available P K alpha' := by
  obtain ⟨law, hsupport, hC4⟩ := h
  refine ⟨law, hsupport, ?_⟩
  intro Q
  exact (hC4 Q).trans (pow_le_pow_left' haa' Q.card)

/-- The simultaneous robust-Hall/rooted-moment construction supplies the
readiness proposition used to totalize the state-dependent link kernel. -/
theorem hasSimultaneousLinkCoverFamilyLaw_of_robust
    {O V : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (available P Pbase : TripleSystemOn V)
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    [rDecidable : ∀ o, DecidableRel (r o)]
    (Delta groupSize degreeCutoff rootCutoff familyCutoff : ℕ)
    (hcandidates : ∀ o,
      ∀ h : OrientedSmallHallObstruction ↥(K o).left ↥(K o).right,
        (Delta * orientedSmallHallSize h + 1) * groupSize ≤
          (orientedSmallHallCandidates (r o) h).card)
    (hbalanced : ∀ o, (K o).left.card = (K o).right.card)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (kappa : ℝ≥0) (momentOrder : ℕ)
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hkappa : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 ↦
          relativeRootedThreatRemainder P z)
        (fun _ ↦ sigma) kappa)
    (hsmall :
      (Fintype.card (SimultaneousHallGroupIndex O V K Delta) : ℝ≥0) *
          (1 - sigma) ^ groupSize +
        (Fintype.card (DistinctPair V) : ℝ≥0) *
          ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
              momentOrder) /
            (rootCutoff + 1 : ℝ≥0) ^ momentOrder) < 1)
    (hPpacking : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (havailable : ∀ o a b, r o a b →
      linkMatchingTriple (K o).center (K o).leftEmbedding
        (K o).rightEmbedding (K o).center_ne_left
        (K o).center_ne_right (K o).left_ne_right a b ∈ available)
    (hbaseSafe : ∀ o a b, r o a b →
      TriangleAvoidsGraph (coveredGraph Pbase)
        (linkMatchingTriple (K o).center (K o).leftEmbedding
          (K o).rightEmbedding (K o).center_ne_left
          (K o).center_ne_right (K o).left_ne_right a b))
    (hstateControls : ∀ (omega : SimultaneousLinkPair O V K → Bool),
      ∀ (S : Finset O) (P' : TripleSystemOn V),
      P ⊆ P' →
      P' ⊆ P ∪ (available ∩ simultaneousLinkReservoir U center K
        hcenter hout hleft hright omega) →
      IsPackingOn P' → AvoidsForbidden P' F →
      IsProcessedSimultaneousLinkFamily K S (P' \ P) →
      ∀ o, o ∉ S →
        (∀ a : ↥(K o).left, (leaveGraph P').Adj (K o).center a.1) ∧
        (∀ b : ↥(K o).right, (leaveGraph P').Adj (K o).center b.1) ∧
        (∀ a : ↥(K o).left,
          (coveredGraph (P' \ Pbase)).degree a.1 ≤ degreeCutoff) ∧
        (∀ b : ↥(K o).right,
          (coveredGraph (P' \ Pbase)).degree b.1 ≤ degreeCutoff))
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta) :
    HasSimultaneousLinkCoverFamilyLaw F available P K
      (sigma /
        (FiniteLaw.independentBits
          (fun _ : SimultaneousLinkPair O V K ↦ sigma)
          (fun _ ↦ hsigma)).probability
            (IsSimultaneousRobustLinkGood F P U center K hcenter hout
              hleft hright r Delta rootCutoff)) := by
  exact exists_simultaneousRobustLinkCoverFamilyLaw
    F available P Pbase U center K hcenter hout hleft hright r Delta groupSize
      degreeCutoff rootCutoff familyCutoff hcandidates hbalanced sigma
      hsigma kappa momentOrder hfamily hkappa hsmall hPpacking hPavoid
      havailable hbaseSafe hstateControls hdeletionScalar

/-- Choose the genuine cover law at ready states and a deterministic empty
family elsewhere. -/
def supportedSimultaneousLinkCoverKernel
    {Omega O V : Type*} [Fintype O] [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V)
    (available P : Omega → TripleSystemOn V)
    (K : Omega → O → BipartiteLink V) (alpha : ℝ≥0)
    (omega : Omega) : FiniteLaw (TripleSystemOn V) := by
  classical
  if h : HasSimultaneousLinkCoverFamilyLaw F (available omega) (P omega)
      (K omega) alpha then
    exact Classical.choose h
  else
    exact FiniteLaw.pure ∅

theorem supportedSimultaneousLinkCoverKernel_ready
    {Omega O V : Type*} [Fintype O] [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V)
    (available P : Omega → TripleSystemOn V)
    (K : Omega → O → BipartiteLink V) (alpha : ℝ≥0)
    (omega : Omega)
    (hready : HasSimultaneousLinkCoverFamilyLaw F (available omega)
      (P omega) (K omega) alpha) :
    (supportedSimultaneousLinkCoverKernel F available P K alpha omega).SupportedOn
        (fun M ↦
          IsSimultaneousLinkCover F (available omega) (P omega)
              (K omega) M ∧
            IsSimultaneousLinkFamily (K omega) M) ∧
      ∀ Q : TripleSystemOn V,
        (supportedSimultaneousLinkCoverKernel F available P K alpha omega).probability
            (fun M ↦ Q ⊆ M) ≤ alpha ^ Q.card := by
  rw [supportedSimultaneousLinkCoverKernel, dif_pos hready]
  exact Classical.choose_spec hready

/-- The totalized kernel obeys C4 on every fiber, including fallback
fibers. -/
theorem supportedSimultaneousLinkCoverKernel_C4
    {Omega O V : Type*} [Fintype O] [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V)
    (available P : Omega → TripleSystemOn V)
    (K : Omega → O → BipartiteLink V) (alpha : ℝ≥0)
    (omega : Omega) (Q : TripleSystemOn V) :
    (supportedSimultaneousLinkCoverKernel F available P K alpha omega).probability
        (fun M ↦ Q ⊆ M) ≤ alpha ^ Q.card := by
  classical
  by_cases hready : HasSimultaneousLinkCoverFamilyLaw F (available omega)
      (P omega) (K omega) alpha
  · exact (supportedSimultaneousLinkCoverKernel_ready
      F available P K alpha omega hready).2 Q
  · rw [supportedSimultaneousLinkCoverKernel, dif_neg hready]
    rw [FiniteLaw.probability_pure]
    by_cases hQ : Q = ∅
    · subst Q
      simp
    · have hnot : ¬ Q ⊆ (∅ : TripleSystemOn V) := by
        simpa only [subset_empty] using hQ
      simp [hnot]

/-- Structural reserve accounting holds even in fallback fibers: the empty
family is a link family and a packing. -/
theorem supportedSimultaneousLinkCoverKernel_structural
    {Omega O V : Type*} [Fintype O] [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V)
    (available P : Omega → TripleSystemOn V)
    (K : Omega → O → BipartiteLink V) (alpha : ℝ≥0)
    (omega : Omega) :
    (supportedSimultaneousLinkCoverKernel F available P K alpha omega).SupportedOn
        (fun M ↦
          IsSimultaneousLinkFamily (K omega) M ∧ IsPackingOn M) := by
  classical
  by_cases hready : HasSimultaneousLinkCoverFamilyLaw F (available omega)
      (P omega) (K omega) alpha
  · intro M hmass
    have hM := (supportedSimultaneousLinkCoverKernel_ready
      F available P K alpha omega hready).1 M hmass
    exact ⟨hM.2, hM.1.isPacking⟩
  · rw [supportedSimultaneousLinkCoverKernel, dif_neg hready]
    apply FiniteLaw.supportedOn_pure
    constructor
    · intro T hT
      simp at hT
    · intro u v huv T hT
      simp at hT

/-- Readiness on the support of the old law becomes simultaneous-cover
support for the joint law. -/
theorem FiniteLaw.SupportedOn.jointBind_supportedSimultaneousLinkCoverKernel
    {Omega O V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype O] [Fintype V] [DecidableEq V]
    {law : FiniteLaw Omega}
    (F : ForbiddenFamilyOn V)
    (available P : Omega → TripleSystemOn V)
    (K : Omega → O → BipartiteLink V) (alpha : ℝ≥0)
    (hready : law.SupportedOn fun omega ↦
      HasSimultaneousLinkCoverFamilyLaw F (available omega) (P omega)
        (K omega) alpha) :
    let linkLaw := supportedSimultaneousLinkCoverKernel
      F available P K alpha
    (law.jointBind linkLaw).SupportedOn (fun z ↦
      IsSimultaneousLinkCover F (available z.1) (P z.1) (K z.1) z.2 ∧
        IsSimultaneousLinkFamily (K z.1) z.2) := by
  dsimp only
  have hjoint := hready.jointBind
    (K := supportedSimultaneousLinkCoverKernel F available P K alpha)
    (Q := fun omega M ↦
      IsSimultaneousLinkCover F (available omega) (P omega) (K omega) M ∧
        IsSimultaneousLinkFamily (K omega) M)
    (fun omega homega ↦
      (supportedSimultaneousLinkCoverKernel_ready
        F available P K alpha omega homega).1)
  exact fun z hz ↦ (hjoint z hz).2

end

end Erdos207
