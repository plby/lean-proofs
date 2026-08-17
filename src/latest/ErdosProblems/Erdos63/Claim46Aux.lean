/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos63.AdjusterBase
import ErdosProblems.Erdos63.Claim46Growth

/-!
# The auxiliary expansion in Liu--Montgomery Claim 4.6

This file performs the non-circular workspace construction between Claims
4.5 and 4.6.  Before the auxiliary expansion `Z` has been chosen, put into
the workspace the ambient deleted set and, for every surviving candidate,
both its complete adjuster carrier and the unrestricted ball of the required
radius around its two ends.  Any candidate-dependent ball appearing after a
short connection to `Z` has been chosen is a subset of that static ball.

Consequently `exists_lm43_auxiliary_expansion` produces an expansion disjoint
from every set occurring in the `hZWorkspace` premise of
`card_reachingEligibleSubfamily_lt_of_no_targetAdjuster_expansion`.  All
quantitative input is exposed below as literal natural-number inequalities.
-/

open Finset Set SimpleGraph
open scoped SimpleGraph

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

variable {V : Type u} {G : SimpleGraph V}

namespace SmallSimpleAdjusterCandidate

variable {minRadius maxRadius : ℕ}

/-- The static portion of the Claim 4.6 workspace occupied by one candidate:
its whole adjuster together with the unrestricted neighborhood of both ends.

Using the unrestricted ball is intentional.  It is chosen before the target
expansion exists and contains every later ball obtained by deleting the
ambient set, the oriented barrier, and the selected connection path. -/
noncomputable def claim46OccupiedNeighborhood [Fintype V]
    (G : SimpleGraph V)
    (highDegree : Finset V)
    (A : SmallSimpleAdjusterCandidate G minRadius maxRadius)
    (ballRadius : ℕ) : Finset V :=
  A.adjuster.verts ∪
    ballAvoidingFrom G (highDegree : Set V) A.ends ballRadius

/-- The complete static workspace deleted before growing the Claim 4.6
auxiliary expansion. -/
noncomputable def claim46Workspace [Fintype V]
    (G : SimpleGraph V) (deleted highDegree : Finset V)
    (S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius // True})
    (ballRadius : ℕ) : Finset V :=
  deleted ∪ S.biUnion fun A ↦
    claim46OccupiedNeighborhood G highDegree A.1 ballRadius

/-- Predicate-polymorphic version of the static workspace.  The predicate is
kept as a parameter so the definition applies directly to proof-carrying
eligible families without erasing or reconstructing their membership proofs.
-/
noncomputable def claim46WorkspaceOf [Fintype V]
    (G : SimpleGraph V) (deleted highDegree : Finset V)
    {P : SmallSimpleAdjusterCandidate G minRadius maxRadius → Prop}
    (S : Finset {A // P A}) (ballRadius : ℕ) : Finset V :=
  deleted ∪ S.biUnion fun A ↦
    claim46OccupiedNeighborhood G highDegree A.1 ballRadius

theorem deleted_subset_claim46WorkspaceOf [Fintype V]
    (G : SimpleGraph V) (deleted highDegree : Finset V)
    {P : SmallSimpleAdjusterCandidate G minRadius maxRadius → Prop}
    (S : Finset {A // P A}) (ballRadius : ℕ) :
    deleted ⊆ claim46WorkspaceOf G deleted highDegree S ballRadius := by
  intro v hv
  exact Finset.mem_union_left _ hv

theorem candidate_adjuster_verts_subset_claim46WorkspaceOf [Fintype V]
    (G : SimpleGraph V) (deleted highDegree : Finset V)
    {P : SmallSimpleAdjusterCandidate G minRadius maxRadius → Prop}
    (S : Finset {A // P A}) (ballRadius : ℕ)
    {A : {A // P A}} (hA : A ∈ S) :
    A.1.adjuster.verts ⊆
      claim46WorkspaceOf G deleted highDegree S ballRadius := by
  intro v hv
  apply Finset.mem_union_right deleted
  rw [Finset.mem_biUnion]
  refine ⟨A, hA, ?_⟩
  exact Finset.mem_union_left _ hv

theorem candidate_highDegree_ball_subset_claim46WorkspaceOf [Fintype V]
    (G : SimpleGraph V) (deleted highDegree : Finset V)
    {P : SmallSimpleAdjusterCandidate G minRadius maxRadius → Prop}
    (S : Finset {A // P A}) (ballRadius : ℕ)
    {A : {A // P A}} (hA : A ∈ S) :
    ballAvoidingFrom G (highDegree : Set V) A.1.ends ballRadius ⊆
      claim46WorkspaceOf G deleted highDegree S ballRadius := by
  intro v hv
  apply Finset.mem_union_right deleted
  rw [Finset.mem_biUnion]
  refine ⟨A, hA, ?_⟩
  exact Finset.mem_union_right _ hv

/-- The source-paper polynomial workspace bound.  The static balls are grown
in `G-L`; hence every reached vertex has degree at most `Delta`, and the
Moore bound applies to the two candidate ends. -/
theorem card_claim46WorkspaceOf_le [Fintype V]
    (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (deleted highDegree protectedSet : Finset V)
    (separation ballRadius Delta : ℕ)
    (S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation})
    (hdegree : ∀ v ∉ highDegree, G.degree v ≤ Delta) :
    (claim46WorkspaceOf G deleted highDegree S ballRadius).card ≤
      deleted.card + S.card *
        ((2 * maxRadius ^ 2 + 10 * maxRadius) +
          2 * maxRadius ^ 2 * (Delta + 1) ^ ballRadius) := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  letI : DecidableRel G.Adj := originalDecAdj
  let cap : ℕ :=
    (2 * maxRadius ^ 2 + 10 * maxRadius) +
      2 * maxRadius ^ 2 * (Delta + 1) ^ ballRadius
  have hone : ∀ A :
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation},
      (claim46OccupiedNeighborhood G highDegree A.1 ballRadius).card ≤ cap := by
    intro A
    have hball := card_ballAvoidingFrom_le_of_degree_bound G A.1.ends
      highDegree Delta ballRadius A.2.2.1 hdegree
    have hends : A.1.ends.card ≤ 2 * maxRadius ^ 2 := by
      rw [A.1.card_ends]
      exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left A.1.le_max 2)
    have hball' :
        (ballAvoidingFrom G (highDegree : Set V) A.1.ends ballRadius).card ≤
          2 * maxRadius ^ 2 * (Delta + 1) ^ ballRadius := by
      exact hball.trans (Nat.mul_le_mul_right _ hends)
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add A.1.card_adjuster_verts_le_maxRadius hball')
  have hfamily :
      (S.biUnion fun A ↦
        claim46OccupiedNeighborhood G highDegree A.1 ballRadius).card ≤
        S.card * cap := by
    calc
      (S.biUnion fun A ↦
          claim46OccupiedNeighborhood G highDegree A.1 ballRadius).card
          ≤ ∑ A ∈ S,
              (claim46OccupiedNeighborhood G highDegree A.1 ballRadius).card :=
            Finset.card_biUnion_le
      _ ≤ ∑ _A ∈ S, cap := by
        apply Finset.sum_le_sum
        intro A _
        exact hone A
      _ = S.card * cap := by simp
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left hfamily deleted.card)

/-- Every concrete set in the Claim 4.6 `hZWorkspace` premise is contained
in the static workspace.  The target may be any subset chosen after the
workspace was fixed. -/
theorem reachingCandidate_workspace_subset_claim46WorkspaceOf [Fintype V]
    (G : SimpleGraph V)
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius ballRadius highRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hnoHigh : ∀ A ∈ S, ¬ A.1.ReachesAvoidingOwnCore deleted
      (highDegree \ deleted) highRadius)
    (hballHigh : ballRadius ≤ highRadius)
    (i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius}) :
    deleted ∪ (reachingCandidateConnectionData i).adjusted.core ∪
        ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius ⊆
      claim46WorkspaceOf G deleted highDegree S ballRadius := by
  let A : {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
      A.Eligible deleted highDegree protectedSet separation} := i.1
  have hAS : A ∈ S :=
    ((mem_reachingEligibleSubfamily S targetSet connectionRadius i.1).1 i.2).1
  have hdeleted : deleted ⊆
      claim46WorkspaceOf G deleted highDegree S ballRadius :=
    deleted_subset_claim46WorkspaceOf G deleted highDegree S ballRadius
  have hcore : (reachingCandidateConnectionData i).adjusted.core ⊆
      claim46WorkspaceOf G deleted highDegree S ballRadius := by
    intro v hv
    apply candidate_adjuster_verts_subset_claim46WorkspaceOf
      G deleted highDegree S ballRadius hAS
    rw [← (reachingCandidateConnectionData i).verts_eq]
    exact (reachingCandidateConnectionData i).adjusted.core_subset_verts hv
  have hactualHigh :
      ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius =
        ballAvoidingFrom G
          ((deleted : Set V) ∪ (highDegree : Set V) ∪
            (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius :=
    reachingCandidate_ball_eq_highDegree_of_no_highConnection i
      (hnoHigh A hAS) hballHigh
  have hforbidden :
      ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius ⊆
        ballAvoidingFrom G (highDegree : Set V)
          (reachingCandidateSeed i) ballRadius := by
    rw [hactualHigh]
    apply ballAvoidingFrom_forbidden_anti G
    intro z hz
    simp only [Set.mem_union]
    exact Or.inl (Or.inl (Or.inr hz))
  have hseed :
      ballAvoidingFrom G (highDegree : Set V)
          (reachingCandidateSeed i) ballRadius ⊆
        ballAvoidingFrom G (highDegree : Set V) A.1.ends ballRadius :=
    ballAvoidingFrom_seed_mono G (highDegree : Set V)
      (reachingCandidateSeed_subset_ends i) ballRadius
  have hball :
      ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius ⊆
        claim46WorkspaceOf G deleted highDegree S ballRadius :=
    hforbidden.trans <| hseed.trans <|
      candidate_highDegree_ball_subset_claim46WorkspaceOf
        G deleted highDegree S ballRadius hAS
  intro v hv
  rw [Finset.mem_union] at hv
  rcases hv with hv | hv
  · rw [Finset.mem_union] at hv
    rcases hv with hvDeleted | hvCore
    · exact hdeleted hvDeleted
    · exact hcore hvCore
  · exact hball hv

/-- The auxiliary expansion `Z` used in Claim 4.6, with the precise
disjointness statement needed by the later correlated Lemma 3.7 argument.

The workspace passed to `exists_lm43_auxiliary_expansion` is *exactly* the
cardinality of `claim46WorkspaceOf`.  Thus the only quantitative assumptions
are the explicit growth-gain, room, order, and denominator inequalities from
the sharp Claim 4.6 recurrence. -/
theorem exists_claim46_auxiliary_expansion [Fintype V]
    (G : SimpleGraph V)
    (d targetOrder connectionRadius ballRadius highRadius : ℕ)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    {deleted highDegree protectedSet : Finset V} {separation : ℕ}
    (S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation})
    (hnoHigh : ∀ A ∈ S, ¬ A.1.ReachesAvoidingOwnCore deleted
      (highDegree \ deleted) highRadius)
    (hballHigh : ballRadius ≤ highRadius)
    (hn : 32 ≤ Fintype.card V) (hd : 1 ≤ d)
    (hdn : d ≤ Fintype.card V)
    (hworkspace :
      (claim46WorkspaceOf G deleted highDegree S ballRadius).card ≤
      lm43GrowthGain (Fintype.card V) (lm43K (Fintype.card V)))
    (hroom : (claim46WorkspaceOf G deleted highDegree S ballRadius).card +
      lm43K (Fintype.card V) ≤ Fintype.card V)
    (hTargetPos : 0 < targetOrder)
    (hTargetK : targetOrder ≤ lm43K (Fintype.card V))
    (hlarge : 6 * lm43GrowthDenominator (Fintype.card V) ≤
      lm43K (Fintype.card V)) :
    ∃ center : V, ∃ Z : VertexExpansion G center targetOrder
        (lm43FarRadius (Fintype.card V)),
      Disjoint Z.verts
        (claim46WorkspaceOf G deleted highDegree S ballRadius) ∧
      ∀ (targetSet : Finset V), targetSet ⊆ Z.verts →
        ∀ i : {A // A ∈
          reachingEligibleSubfamily S targetSet connectionRadius},
          Disjoint Z.verts
            (deleted ∪ (reachingCandidateConnectionData i).adjusted.core ∪
              ballAvoidingFrom G
                ((deleted : Set V) ∪
                  (reachingCandidateBarrier i : Set V) ∪
                  (reachingCandidatePath i : Set V))
                (reachingCandidateSeed i) ballRadius) := by
  let W := claim46WorkspaceOf G deleted highDegree S ballRadius
  obtain ⟨center, Z, hZW⟩ := exists_lm43_auxiliary_expansion
    G d W.card targetOrder hexp W hn hd hdn (by rfl) hworkspace hroom
      hTargetPos hTargetK hlarge
  refine ⟨center, Z, hZW, ?_⟩
  intro targetSet hTargetSet i
  apply hZW.mono_right
  exact reachingCandidate_workspace_subset_claim46WorkspaceOf
    G (targetSet := targetSet) (ballRadius := ballRadius)
      hnoHigh hballHigh i

/-! ## Claim 4.6 at an inflated auxiliary order -/

/-- Nonexistence at a positive target order implies nonexistence at every
larger auxiliary order: shrink both end expansions by Proposition 3.10 and
use the resulting carrier inclusion. -/
theorem no_auxiliaryAdjuster_of_no_targetAdjuster
    {targetOrder auxiliaryOrder totalRadius : ℕ} {deleted : Finset V}
    (hnoTarget : ¬ ∃ A : Adjuster G targetOrder totalRadius 1,
      Disjoint deleted A.verts)
    (hTargetPos : 0 < targetOrder)
    (hTargetAuxiliary : targetOrder ≤ auxiliaryOrder) :
    ¬ ∃ A : Adjuster G auxiliaryOrder totalRadius 1,
      Disjoint deleted A.verts := by
  rintro ⟨Aaux, hAaux⟩
  obtain ⟨A, _hcore, _hleft, _hright, hverts⟩ :=
    Aaux.exists_shrinkEnds hTargetPos hTargetAuxiliary
  exact hnoTarget ⟨A, hAaux.mono_right hverts⟩

/-- Claim 4.6 with separate output and auxiliary orders.  Lemma 3.7 and `Z`
run at `auxiliaryOrder`; the resulting adjuster is then shrunk to
`targetOrder`.  Shrinking does not increase the radius, so the original
`2 * farRadius` left-end budget remains sufficient. -/
theorem card_reachingEligibleSubfamily_lt_of_no_targetAdjuster_expansion_auxiliaryOrder
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius ballRadius highRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (targetOrder auxiliaryOrder totalRadius deletedCap R degreeInto farRadius : ℕ)
    (scale : LM37CorrelatedScale (Fintype.card V) deletedCap R 2
      ballRadius auxiliaryOrder degreeInto epsilon kappa)
    (hdeleted : deleted.card ≤ deletedCap)
    (hnoTarget : ¬ ∃ A : Adjuster G targetOrder totalRadius 1,
      Disjoint deleted A.verts)
    (hnoHigh : ∀ A ∈ S, ¬ A.1.ReachesAvoidingOwnCore deleted
      (highDegree \ deleted) highRadius)
    (hballHigh : ballRadius ≤ highRadius)
    {center : V} (Z : VertexExpansion G center auxiliaryOrder farRadius)
    (hTargetSet : targetSet ⊆ Z.verts)
    (hZWorkspace : ∀ i :
      {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      Disjoint Z.verts
        (deleted ∪ (reachingCandidateConnectionData i).adjusted.core ∪
          ballAvoidingFrom G
            ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
              (reachingCandidatePath i : Set V))
            (reachingCandidateSeed i) ballRadius))
    (hradius : ballRadius + ballRadius ≤ separation)
    (hprotected : deleted ∪ manyNeighborsInto G deleted degreeInto ⊆ protectedSet)
    (hstart : scale.growth 0 < minRadius ^ 2)
    (hstartOne : scale.growth 1 < minRadius ^ 2)
    (hminSize : scale.minSize ≤ minRadius ^ 2)
    (hneighbor : ∀ ell s, 0 < ell → ell ≤ ballRadius →
      scale.growth (ell - 1) < s →
      scale.stepLoss ell + (11 * maxRadius + 1) + 2 * ell ≤
        scale.neighborBudget s)
    (hlargeBudgetSum : ∀
      (J : Finset
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (f : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius} → ℕ),
      (∀ i ∈ J, scale.cutoff ≤ f i ∧ f i ≤ scale.D) →
      ∑ i ∈ J, scale.neighborBudget (f i) ≤
        scale.largeBudget (∑ i ∈ J, f i))
    (hTargetPos : 0 < targetOrder)
    (hTargetAuxiliary : targetOrder ≤ auxiliaryOrder)
    (hLeftRadius : maxRadius + connectionRadius + 2 * farRadius ≤ totalRadius)
    (hRightRadius : maxRadius + ballRadius ≤ totalRadius) :
    (reachingEligibleSubfamily S targetSet connectionRadius).card < R := by
  apply card_reachingEligibleSubfamily_lt_of_no_targetAdjuster_expansion
    G epsilon kappa hexp hpair auxiliaryOrder totalRadius deletedCap R
      degreeInto farRadius scale hdeleted
      (no_auxiliaryAdjuster_of_no_targetAdjuster
        hnoTarget hTargetPos hTargetAuxiliary)
      hnoHigh hballHigh Z hTargetSet hZWorkspace hradius hprotected hstart
      hstartOne hminSize hneighbor hlargeBudgetSum
      (hTargetPos.trans_le hTargetAuxiliary) hLeftRadius hRightRadius

end SmallSimpleAdjusterCandidate

end Erdos63
