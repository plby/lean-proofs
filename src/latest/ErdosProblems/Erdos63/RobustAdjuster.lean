/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos63.Claim43Final
import ErdosProblems.Erdos63.Claim43Numerics
import ErdosProblems.Erdos63.Claim46Aux
import ErdosProblems.Erdos63.SourceLemma37
import ErdosProblems.Erdos63.SourceRobustAdjuster

/-!
# The robust simple-adjuster assembly

This file assembles the already formalized geometric Claims 4.5 and 4.6 in
Liu--Montgomery's proof of Lemma 4.3.  The statement below deliberately keeps
the graph-free scale inequalities explicit: it is therefore insensitive to
the eventual-asymptotic wrapper used to discharge them.
-/

open Finset Set SimpleGraph
open scoped BigOperators SimpleGraph

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

variable {V : Type u}

namespace SmallSimpleAdjusterCandidate

/-- Claim 4.4's maximality step, separated from its density construction.

Once a small candidate outside the occupied low-degree ball can be produced
whenever the family has fewer than `4 * R` members, maximality forces the
desired lower bound.  Thus `hnew` is exactly the residual Case I/Case II
construction in Claim 4.4; all conflict and eligibility bookkeeping is
discharged here. -/
theorem four_mul_le_card_of_fresh_candidate_outside_maximal_ball
    [Fintype V] {G : SimpleGraph V}
    {deleted highDegree protectedSet : Finset V}
    {separation minRadius maxRadius R : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hmax : ∀ A :
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation},
      ∃ B ∈ S, Conflict A.1 B.1 highDegree separation)
    (hnew : S.card < 4 * R →
      ∃ radius : ℕ, ∃ A : Adjuster G (radius ^ 2) radius 1,
        minRadius ≤ radius ∧ radius ≤ maxRadius ∧
        Disjoint (A.leftEnd.verts ∪ A.rightEnd.verts) highDegree ∧
        Disjoint
          (deleted ∪ ballAvoidingFrom G (highDegree : Set V)
            (((protectedSet ∪ S.biUnion fun B ↦ B.1.adjuster.verts) \
              highDegree)) separation)
          A.verts) :
    4 * R ≤ S.card := by
  by_contra hcard
  have hlt : S.card < 4 * R := by omega
  obtain ⟨radius, A, hmin, hmaxRadius, hends, houtside⟩ := hnew hlt
  exact false_of_new_candidate_outside_maximal_ball hmax hmin hmaxRadius A
    hends houtside

/-- Existential Claim 4.4 wrapper.  The finite maximal family is constructed
internally; the caller supplies only the source-paper density construction
of a fresh candidate under the contrary small-cardinality assumption. -/
theorem exists_maximal_eligible_family_four_mul_le
    [Fintype V] {G : SimpleGraph V}
    (deleted highDegree protectedSet : Finset V)
    (separation minRadius maxRadius R : ℕ)
    (hnew : ∀
      (S : Finset
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation}),
      ((S : Set
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
            ¬ Conflict A.1 B.1 highDegree separation) →
      (∀ A :
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation},
        ∃ B ∈ S, Conflict A.1 B.1 highDegree separation) →
      S.card < 4 * R →
      ∃ radius : ℕ, ∃ A : Adjuster G (radius ^ 2) radius 1,
        minRadius ≤ radius ∧ radius ≤ maxRadius ∧
        Disjoint (A.leftEnd.verts ∪ A.rightEnd.verts) highDegree ∧
        Disjoint
          (deleted ∪ ballAvoidingFrom G (highDegree : Set V)
            (((protectedSet ∪ S.biUnion fun B ↦ B.1.adjuster.verts) \
              highDegree)) separation)
          A.verts) :
    ∃ S : Finset
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation},
      ((S : Set
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
            ¬ Conflict A.1 B.1 highDegree separation) ∧
      (∀ A :
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation},
        ∃ B ∈ S, Conflict A.1 B.1 highDegree separation) ∧
      4 * R ≤ S.card := by
  obtain ⟨S, hpair, hmax⟩ :=
    exists_maximal_eligible_family (G := G) deleted highDegree protectedSet
      separation
  refine ⟨S, hpair, hmax, ?_⟩
  apply four_mul_le_card_of_fresh_candidate_outside_maximal_ball hmax
  exact hnew S hpair hmax

/-- A candidate which does not reach `target` has its two ends disjoint from
`target`.  This is the zero-length-path consequence used in the final
cardinality contradiction of Lemma 4.3. -/
theorem ends_disjoint_target_of_not_reaches
    {G : SimpleGraph V}
    {deleted highDegree protectedSet target : Finset V}
    {separation minRadius maxRadius radius : ℕ}
    (A : SmallSimpleAdjusterCandidate G minRadius maxRadius)
    (hA : A.Eligible deleted highDegree protectedSet separation)
    (hno : ¬ A.ReachesAvoidingOwnCore deleted target radius) :
    Disjoint A.ends target := by
  rw [Finset.disjoint_left]
  intro z hzEnds hzTarget
  apply hno
  apply hasShortAvoidingConnection_of_common_vertex hzEnds hzTarget
  intro hzForbidden
  exact (Finset.disjoint_left.1 (A.ends_disjoint_deleted_union_core hA)
    hzEnds hzForbidden).elim

/-- Eligibility makes the whole `G-L` ball around a candidate's ends avoid
the protected set, up to the separation radius. -/
theorem candidate_highDegree_ball_disjoint_protected
    [Fintype V] {G : SimpleGraph V}
    {deleted highDegree protectedSet : Finset V}
    {separation minRadius maxRadius radius : ℕ}
    (A : SmallSimpleAdjusterCandidate G minRadius maxRadius)
    (hA : A.Eligible deleted highDegree protectedSet separation)
    (hradius : radius ≤ separation) :
    Disjoint
      (ballAvoidingFrom G (highDegree : Set V) A.ends radius)
      protectedSet := by
  rw [Finset.disjoint_left]
  intro z hzBall hzProtected
  by_cases hzHigh : z ∈ highDegree
  · exact ballAvoidingFrom_avoids_forbidden G (highDegree : Set V)
      A.ends radius
      (fun a ha haHigh ↦
        (Finset.disjoint_left.1 hA.2.1 ha (by simpa using haHigh)).elim)
      z hzBall (by simpa using hzHigh)
  · apply hA.2.2
    obtain ⟨a, ha, p, hp, hplen⟩ :=
      (mem_ballAvoidingFrom G (highDegree : Set V) A.ends radius z).1 hzBall
    have hpAvoid : p.Avoids (highDegree : Set V) ∅ := by
      intro w hw hwHigh
      have hwa : w = a := by simpa using hp.2 w hw hwHigh
      exact (Finset.disjoint_left.1 hA.2.1 ha (by simpa [hwa] using hwHigh)).elim
    exact ⟨a, ha, z, Finset.mem_sdiff.2 ⟨hzProtected, hzHigh⟩,
      p, hp.1, hpAvoid, hplen.trans hradius⟩

/-- The graph-free last count after Claims 4.5 and 4.6.

The conflict-free invariant makes all candidate end sets disjoint, while
non-reachability makes their union disjoint from the final target set.  Their
literal cardinalities therefore cannot exceed the ambient vertex set. -/
theorem false_of_crowded_nonreaching_family
    [Fintype V] {G : SimpleGraph V}
    {deleted highDegree protectedSet target : Finset V}
    {separation targetRadius minRadius maxRadius R : ℕ}
    {T : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((T : Set
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
          ¬ Conflict A.1 B.1 highDegree separation))
    (hTcard : T.card = R)
    (hnoTarget : ∀ A ∈ T,
      ¬ A.1.ReachesAvoidingOwnCore deleted target targetRadius)
    (hcrowded : Fintype.card V < 2 * R * minRadius ^ 2 + target.card) : False := by
  let endsUnion : Finset V := T.biUnion fun A ↦ A.1.ends
  have hendsTarget : Disjoint endsUnion target := by
    rw [Finset.disjoint_left]
    intro z hzUnion hzTarget
    rw [Finset.mem_biUnion] at hzUnion
    obtain ⟨A, hAT, hzEnds⟩ := hzUnion
    exact (Finset.disjoint_left.1
      (ends_disjoint_target_of_not_reaches A.1 A.2 (hnoTarget A hAT))
      hzEnds hzTarget).elim
  have hminsum : 2 * R * minRadius ^ 2 ≤
      ∑ A ∈ T, 2 * A.1.radius ^ 2 := by
    calc
      2 * R * minRadius ^ 2 = T.card * (2 * minRadius ^ 2) := by
        rw [hTcard]
        ring
      _ = ∑ _A ∈ T, 2 * minRadius ^ 2 := by simp
      _ ≤ ∑ A ∈ T, 2 * A.1.radius ^ 2 := by
        apply Finset.sum_le_sum
        intro A hA
        exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left A.1.min_le 2)
  have hendsCard : endsUnion.card =
      ∑ A ∈ T, 2 * A.1.radius ^ 2 := by
    simpa only [endsUnion] using card_biUnion_ends_of_conflictFree hpair
  have hunionCard : endsUnion.card + target.card ≤ Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hendsTarget]
    simpa only [Finset.card_univ] using
      Finset.card_le_card (Finset.subset_univ (endsUnion ∪ target))
  have hpacked : 2 * R * minRadius ^ 2 + target.card ≤
      Fintype.card V := by
    exact (Nat.add_le_add_right (hminsum.trans_eq hendsCard.symm) _).trans
      hunionCard
  omega

/-- Claims 4.5 and 4.6, including the two exact discard counts, assembled
into the common survivor family used at the end of Lemma 4.3.

The only family-dependent premise not produced by Claims 4.5 and 4.6 is
`hZWorkspace`.  It is the literal freshness condition on the auxiliary
expansion constructed immediately before Claim 4.6 in the source proof. -/
theorem exists_claim45_claim46_survivor_family
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation highRadius targetRadius ballRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
          ¬ Conflict A.1 B.1 highDegree separation))
    (targetOrder totalRadius Delta deletedCap R degreeInto farRadius : ℕ)
    (hfour : 4 * R ≤ S.card)
    (scale45 : LM37CorrelatedScale (Fintype.card V) deletedCap R 2
      highRadius targetOrder degreeInto epsilon kappa)
    (scale46 : LM37CorrelatedScale (Fintype.card V) deletedCap R 2
      ballRadius targetOrder degreeInto epsilon kappa)
    (hdeleted : deleted.card ≤ deletedCap)
    (hHighDegree : ∀ v ∈ highDegree, Delta ≤ G.degree v)
    (hnoTarget : ¬ ∃ A : Adjuster G targetOrder totalRadius 1,
      Disjoint deleted A.verts)
    (h45radius : highRadius + highRadius ≤ separation)
    (h46radius : ballRadius + ballRadius ≤ separation)
    (hballHigh : ballRadius ≤ highRadius)
    (hprotected : deleted ∪ manyNeighborsInto G deleted degreeInto ⊆
      protectedSet)
    (h45start : scale45.growth 0 < minRadius ^ 2)
    (h45startOne : scale45.growth 1 < minRadius ^ 2)
    (h45minSize : scale45.minSize ≤ minRadius ^ 2)
    (h45neighbor : ∀ ell s, 0 < ell → ell ≤ highRadius →
      scale45.growth (ell - 1) < s →
      scale45.stepLoss ell + (11 * maxRadius + 1) + 2 * ell ≤
        scale45.neighborBudget s)
    (h45largeBudgetSum : ∀
      (J : Finset
        {A // A ∈ reachingEligibleSubfamily S (highDegree \ deleted)
          highRadius})
      (f : {A // A ∈ reachingEligibleSubfamily S (highDegree \ deleted)
          highRadius} → ℕ),
      (∀ i ∈ J, scale45.cutoff ≤ f i ∧ f i ≤ scale45.D) →
      ∑ i ∈ J, scale45.neighborBudget (f i) ≤
        scale45.largeBudget (∑ i ∈ J, f i))
    (hTargetPos : 0 < targetOrder)
    (hRightBudget : targetOrder +
      (deletedCap + 10 * maxRadius + (maxRadius + 1) +
        (highRadius + 1)) ≤ Delta)
    (hLeftBudget : targetOrder +
      (deletedCap + 10 * maxRadius + targetOrder) ≤ Delta)
    (h45TotalRadius : maxRadius + highRadius + 1 ≤ totalRadius)
    {center : V} (Z : VertexExpansion G center targetOrder farRadius)
    (hTargetSet : targetSet ⊆ Z.verts)
    (hZWorkspace : ∀
      (T : Finset
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation}),
      T ⊆ S → T.card = 2 * R →
      (∀ A ∈ T, ¬ A.1.ReachesAvoidingOwnCore deleted
        (highDegree \ deleted) highRadius) →
      ∀ i : {A // A ∈ reachingEligibleSubfamily T targetSet targetRadius},
        Disjoint Z.verts
          (deleted ∪ (reachingCandidateConnectionData i).adjusted.core ∪
            ballAvoidingFrom G
              ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
                (reachingCandidatePath i : Set V))
              (reachingCandidateSeed i) ballRadius))
    (h46start : scale46.growth 0 < minRadius ^ 2)
    (h46startOne : scale46.growth 1 < minRadius ^ 2)
    (h46minSize : scale46.minSize ≤ minRadius ^ 2)
    (h46neighbor : ∀ ell s, 0 < ell → ell ≤ ballRadius →
      scale46.growth (ell - 1) < s →
      scale46.stepLoss ell + (11 * maxRadius + 1) + 2 * ell ≤
        scale46.neighborBudget s)
    (h46largeBudgetSum : ∀
      (T : Finset
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation})
      (J : Finset {A // A ∈ reachingEligibleSubfamily T targetSet targetRadius})
      (f : {A // A ∈ reachingEligibleSubfamily T targetSet targetRadius} → ℕ),
      (∀ i ∈ J, scale46.cutoff ≤ f i ∧ f i ≤ scale46.D) →
      ∑ i ∈ J, scale46.neighborBudget (f i) ≤
        scale46.largeBudget (∑ i ∈ J, f i))
    (hLeftRadius : maxRadius + targetRadius + 2 * farRadius ≤ totalRadius)
    (hRightRadius : maxRadius + ballRadius ≤ totalRadius) :
    ∃ T : Finset
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation},
      T ⊆ S ∧ T.card = R ∧
        (∀ A ∈ T, ¬ A.1.ReachesAvoidingOwnCore deleted
          (highDegree \ deleted) highRadius) ∧
        ∀ A ∈ T, ¬ A.1.ReachesAvoidingOwnCore deleted targetSet targetRadius := by
  have hbad45 := card_reachingEligibleSubfamily_lt_of_no_targetAdjuster
    G epsilon kappa hexp hpair targetOrder totalRadius Delta deletedCap R
      degreeInto scale45 hdeleted (by exact Finset.Subset.rfl) hHighDegree
      hnoTarget h45radius hprotected h45start h45startOne h45minSize
      h45neighbor h45largeBudgetSum hTargetPos hRightBudget hLeftBudget
      h45TotalRadius
  obtain ⟨T, hTS, hTcard, hTnoHigh⟩ :=
    exists_two_mul_nonreaching_subfamily (highRadius := highRadius)
      (R := R) S hfour hbad45
  have hpairT : ((T : Set
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
          ¬ Conflict A.1 B.1 highDegree separation) := by
    intro A hA B hB hAB
    exact hpair (hTS hA) (hTS hB) hAB
  have hbad46 :=
    card_reachingEligibleSubfamily_lt_of_no_targetAdjuster_expansion
      G epsilon kappa hexp hpairT targetOrder totalRadius deletedCap R
        degreeInto farRadius scale46 hdeleted hnoTarget hTnoHigh hballHigh Z
        hTargetSet (hZWorkspace T hTS hTcard hTnoHigh) h46radius hprotected
        h46start h46startOne h46minSize h46neighbor
        (h46largeBudgetSum T) hTargetPos hLeftRadius hRightRadius
  obtain ⟨Q, hQT, hQcard, hQnoHigh, hQnoTarget⟩ :=
    exists_nonreaching_subfamily_card_eq T hTcard hTnoHigh hbad46
  exact ⟨Q, hQT.trans hTS, hQcard, hQnoHigh, hQnoTarget⟩

/-- The complete graph-theoretic assembly after Claim 4.4.

Starting from the `4R` conflict-free family supplied by Claim 4.4, this
theorem applies Claim 4.5, constructs the static-workspace auxiliary
expansion, applies Claim 4.6, performs both exact discard counts, and invokes
the final correlated-growth contradiction.  Every remaining hypothesis is a
natural-number or real inequality, uniformly quantified over a finite family
only where the corresponding scale genuinely depends on that family. -/
theorem false_of_claim45_claim46_and_final
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {deleted highDegree protectedSet : Finset V}
    {separation highRadius targetRadius ballRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
          ¬ Conflict A.1 B.1 highDegree separation))
    (d targetOrder totalRadius Delta deletedCap R degreeInto ballTarget
      finalConnectorQ finalConnectorRadius : ℕ)
    (hfour : 4 * R ≤ S.card)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (scale45 : LM37CorrelatedScale (Fintype.card V) deletedCap R 2
      highRadius targetOrder degreeInto (1 / 1024)
        ((1 / 64) * (d : ℝ)))
    (scale46 : LM37CorrelatedScale (Fintype.card V) deletedCap R 2
      ballRadius targetOrder degreeInto (1 / 1024)
        ((1 / 64) * (d : ℝ)))
    (scaleFinal : LM37CorrelatedScale (Fintype.card V) deletedCap R 0
      ballRadius ballTarget degreeInto (1 / 1024)
        ((1 / 64) * (d : ℝ)))
    (hdeleted : deleted.card ≤ deletedCap)
    (hHighDegree : ∀ v ∈ highDegree, Delta ≤ G.degree v)
    (hnoTarget : ¬ ∃ A : Adjuster G targetOrder totalRadius 1,
      Disjoint deleted A.verts)
    (h45radius : highRadius + highRadius ≤ separation)
    (h46radius : ballRadius + ballRadius ≤ separation)
    (hballHigh : ballRadius ≤ highRadius)
    (hprotected : deleted ∪ manyNeighborsInto G deleted degreeInto ⊆
      protectedSet)
    (h45start : scale45.growth 0 < minRadius ^ 2)
    (h45startOne : scale45.growth 1 < minRadius ^ 2)
    (h45minSize : scale45.minSize ≤ minRadius ^ 2)
    (h45neighbor : ∀ ell s, 0 < ell → ell ≤ highRadius →
      scale45.growth (ell - 1) < s →
      scale45.stepLoss ell + (11 * maxRadius + 1) + 2 * ell ≤
        scale45.neighborBudget s)
    (h45largeBudgetSum : ∀
      (J : Finset
        {A // A ∈ reachingEligibleSubfamily S (highDegree \ deleted)
          highRadius})
      (f : {A // A ∈ reachingEligibleSubfamily S (highDegree \ deleted)
          highRadius} → ℕ),
      (∀ i ∈ J, scale45.cutoff ≤ f i ∧ f i ≤ scale45.D) →
      ∑ i ∈ J, scale45.neighborBudget (f i) ≤
        scale45.largeBudget (∑ i ∈ J, f i))
    (hTargetPos : 0 < targetOrder)
    (hRightBudget : targetOrder +
      (deletedCap + 10 * maxRadius + (maxRadius + 1) +
        (highRadius + 1)) ≤ Delta)
    (hLeftBudget : targetOrder +
      (deletedCap + 10 * maxRadius + targetOrder) ≤ Delta)
    (h45TotalRadius : maxRadius + highRadius + 1 ≤ totalRadius)
    (hn : 32 ≤ Fintype.card V) (hd : 1 ≤ d)
    (hdn : d ≤ Fintype.card V)
    (workspaceCap : ℕ)
    (hLowDegree : ∀ v ∉ highDegree, G.degree v ≤ Delta)
    (hworkspaceCap : deletedCap + 2 * R *
        ((2 * maxRadius ^ 2 + 10 * maxRadius) +
          2 * maxRadius ^ 2 * (Delta + 1) ^ ballRadius) ≤ workspaceCap)
    (hworkspaceGain : workspaceCap ≤
      lm43GrowthGain (Fintype.card V) (lm43K (Fintype.card V)))
    (hworkspaceRoom : workspaceCap + lm43K (Fintype.card V) ≤
      Fintype.card V)
    (hTargetK : targetOrder ≤ lm43K (Fintype.card V))
    (hdenominator : 6 * lm43GrowthDenominator (Fintype.card V) ≤
      lm43K (Fintype.card V))
    (h46start : scale46.growth 0 < minRadius ^ 2)
    (h46startOne : scale46.growth 1 < minRadius ^ 2)
    (h46minSize : scale46.minSize ≤ minRadius ^ 2)
    (h46neighbor : ∀ ell s, 0 < ell → ell ≤ ballRadius →
      scale46.growth (ell - 1) < s →
      scale46.stepLoss ell + (11 * maxRadius + 1) + 2 * ell ≤
        scale46.neighborBudget s)
    (h46largeBudgetSum : ∀
      (T : Finset
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation})
      (targetSet : Finset V)
      (J : Finset
        {A // A ∈ reachingEligibleSubfamily T
          targetSet targetRadius})
      (f : {A // A ∈ reachingEligibleSubfamily T
          targetSet targetRadius} → ℕ),
      (∀ i ∈ J, scale46.cutoff ≤ f i ∧ f i ≤ scale46.D) →
      ∑ i ∈ J, scale46.neighborBudget (f i) ≤
        scale46.largeBudget (∑ i ∈ J, f i))
    (hLeftRadius : maxRadius + targetRadius +
      2 * lm43FarRadius (Fintype.card V) ≤ totalRadius)
    (hRightRadius : maxRadius + ballRadius ≤ totalRadius)
    (hFinalStart : scaleFinal.growth 0 < 2 * minRadius ^ 2)
    (hFinalStartOne : scaleFinal.growth 1 < 2 * minRadius ^ 2)
    (hFinalMinSize : scaleFinal.minSize ≤ 2 * minRadius ^ 2)
    (hFinalNeighbor : ∀ ell s, 0 < ell → ell ≤ ballRadius →
      scaleFinal.growth (ell - 1) < s →
      scaleFinal.stepLoss ell + 10 * maxRadius ≤
        scaleFinal.neighborBudget s)
    (hFinalLargeBudgetSum : ∀
      (Q : Finset
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation})
      (J : Finset Q) (f : Q → ℕ),
      (∀ i ∈ J, scaleFinal.cutoff ≤ f i ∧ f i ≤ scaleFinal.D) →
      ∑ i ∈ J, scaleFinal.neighborBudget (f i) ≤
        scaleFinal.largeBudget (∑ i ∈ J, f i))
    (hBallLower : ((1 / 64) * (d : ℝ)) / 2 ≤ (ballTarget : ℝ))
    (hTargetLower : ((1 / 64) * (d : ℝ)) / 2 ≤
      (targetOrder : ℝ))
    (hBallRate : ∀
      (A : {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}),
      ∀ s : ℕ, ballTarget ≤ s → s ≤ Fintype.card V / 2 →
      (((((deleted ∪ A.1.adjuster.core).card + finalConnectorQ : ℕ)) : ℝ) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ)))
    (hTargetRate : ∀
      (A : {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}),
      ∀ s : ℕ, targetOrder ≤ s → s ≤ Fintype.card V / 2 →
      (((((deleted ∪ A.1.adjuster.core).card + finalConnectorQ : ℕ)) : ℝ) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ)))
    (hBallSteps : Fintype.card V / 2 + 1 ≤
      ballTarget + finalConnectorRadius * finalConnectorQ)
    (hTargetSteps : Fintype.card V / 2 + 1 ≤
      targetOrder + finalConnectorRadius * finalConnectorQ)
    (hFinalRadius : ballRadius + 2 * finalConnectorRadius ≤ targetRadius) : False := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  letI : DecidableRel G.Adj := originalDecAdj
  have hbad45 := card_reachingEligibleSubfamily_lt_of_no_targetAdjuster
    G (1 / 1024) ((1 / 64) * (d : ℝ)) hexp hpair targetOrder totalRadius
      Delta deletedCap R degreeInto scale45 hdeleted (by exact Finset.Subset.rfl)
      hHighDegree hnoTarget h45radius hprotected h45start h45startOne
      h45minSize h45neighbor h45largeBudgetSum hTargetPos hRightBudget
      hLeftBudget h45TotalRadius
  obtain ⟨T, hTS, hTcard, hTnoHigh⟩ :=
    exists_two_mul_nonreaching_subfamily (highRadius := highRadius) (R := R)
      S hfour hbad45
  have hpairT : ((T : Set
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
          ¬ Conflict A.1 B.1 highDegree separation) := by
    intro A hA B hB hAB
    exact hpair (hTS hA) (hTS hB) hAB
  have hTworkspace :
      (claim46WorkspaceOf G deleted highDegree T ballRadius).card ≤
        workspaceCap := by
    calc
      (claim46WorkspaceOf G deleted highDegree T ballRadius).card ≤
          deleted.card + T.card *
            ((2 * maxRadius ^ 2 + 10 * maxRadius) +
              2 * maxRadius ^ 2 * (Delta + 1) ^ ballRadius) :=
        card_claim46WorkspaceOf_le G deleted highDegree protectedSet separation
          ballRadius Delta T hLowDegree
      _ ≤ deletedCap + 2 * R *
            ((2 * maxRadius ^ 2 + 10 * maxRadius) +
              2 * maxRadius ^ 2 * (Delta + 1) ^ ballRadius) := by
        rw [hTcard]
        exact Nat.add_le_add_right hdeleted _
      _ ≤ workspaceCap := hworkspaceCap
  obtain ⟨center, Z, hZW, hZfresh⟩ := exists_claim46_auxiliary_expansion
    G d targetOrder targetRadius ballRadius highRadius hexp T hTnoHigh
      hballHigh hn hd hdn
      (hTworkspace.trans hworkspaceGain)
      ((Nat.add_le_add_right hTworkspace _).trans hworkspaceRoom)
      hTargetPos hTargetK
      hdenominator
  have hbad46 :=
    card_reachingEligibleSubfamily_lt_of_no_targetAdjuster_expansion
      G (1 / 1024) ((1 / 64) * (d : ℝ)) hexp hpairT targetOrder
        totalRadius deletedCap R degreeInto (lm43FarRadius (Fintype.card V))
        scale46 hdeleted hnoTarget hTnoHigh hballHigh Z (by exact Finset.Subset.rfl)
        (hZfresh Z.verts Finset.Subset.rfl) h46radius hprotected h46start
        h46startOne h46minSize h46neighbor (h46largeBudgetSum T Z.verts)
        hTargetPos hLeftRadius
        hRightRadius
  obtain ⟨Q, hQT, hQcard, hQnoHigh, hQnoZ⟩ :=
    exists_nonreaching_subfamily_card_eq T hTcard hTnoHigh hbad46
  have hpairQ : ((Q : Set
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
          ¬ Conflict A.1 B.1 highDegree separation) := by
    intro A hA B hB hAB
    exact hpairT (hQT hA) (hQT hB) hAB
  have hZDisjoint : ∀ i : Q,
      Disjoint Z.verts (deleted ∪ i.1.1.adjuster.core) := by
    intro i
    apply hZW.mono_right
    intro v hv
    rw [Finset.mem_union] at hv
    rcases hv with hvDeleted | hvCore
    · exact deleted_subset_claim46WorkspaceOf
        G deleted highDegree T ballRadius hvDeleted
    · apply candidate_adjuster_verts_subset_claim46WorkspaceOf
        G deleted highDegree T ballRadius (hQT i.2)
      exact i.1.1.adjuster.core_subset_verts hvCore
  have hFinalDegree : ∀ i : Q, ∀ v ∈ ballAvoidingFrom G
      (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
      i.1.1.ends ballRadius,
      (G.neighborFinset v ∩ deleted).card ≤ degreeInto := by
    intro i v hv
    let actual : Finset V := ballAvoidingFrom G
      (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
      i.1.1.ends ballRadius
    let highBall : Finset V := ballAvoidingFrom G (highDegree : Set V)
      i.1.1.ends ballRadius
    let highCoreBall : Finset V := ballAvoidingFrom G
      (((highDegree ∪ i.1.1.adjuster.core : Finset V) : Set V))
      i.1.1.ends ballRadius
    have hactualHighCore : actual ⊆ highCoreBall := by
      simpa only [actual, highCoreBall] using
        candidate_ball_subset_highDegree_ball_of_no_high G i.1.1 i.1.2
          (hQnoHigh i.1 i.2) hballHigh
    have hhighCoreHigh : highCoreBall ⊆ highBall := by
      apply ballAvoidingFrom_forbidden_anti G
      intro z hz
      rw [Finset.coe_union]
      exact Or.inl hz
    have hactualHigh : actual ⊆ highBall :=
      hactualHighCore.trans hhighCoreHigh
    have hhighProtected : Disjoint highBall protectedSet := by
      apply candidate_highDegree_ball_disjoint_protected i.1.1 i.1.2
      omega
    have hactualProtected : Disjoint actual protectedSet :=
      hhighProtected.mono_left hactualHigh
    have hactualDeleted : Disjoint actual deleted :=
      hactualProtected.mono_right
        (Finset.Subset.trans Finset.subset_union_left hprotected)
    have hactualExceptional :
        Disjoint actual (manyNeighborsInto G deleted degreeInto) :=
      hactualProtected.mono_right
        (Finset.Subset.trans Finset.subset_union_right hprotected)
    have hdegree := neighborsInto_le_of_disjoint_manyNeighborsInto
      G deleted actual degreeInto hactualDeleted hactualExceptional v
        (by simpa only [actual] using hv)
    have hinter : G.neighborFinset v ∩ deleted =
        deleted.filter fun w ↦ G.Adj v w := by
      ext w
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        Finset.mem_filter]
      tauto
    rw [hinter]
    exact hdegree
  apply false_of_conflictFree_nonreaching_family
    G (1 / 1024) ((1 / 64) * (d : ℝ)) hexp hpairQ R deletedCap
      degreeInto ballTarget finalConnectorQ finalConnectorRadius scaleFinal
      hQcard hdeleted hQnoHigh hQnoZ hballHigh h46radius hFinalStart
      hFinalStartOne hFinalMinSize hFinalNeighbor hFinalDegree
      (hFinalLargeBudgetSum Q) hZDisjoint hBallLower (by
        simpa only [VertexExpansion.card_verts] using hTargetLower)
      (fun i ↦ hBallRate i.1) (fun i ↦ by
        simpa only [VertexExpansion.card_verts] using hTargetRate i.1)
      hBallSteps (by simpa only [VertexExpansion.card_verts] using hTargetSteps)
      hFinalRadius

/-! ## The source-sample robust assembly -/

/-- Candidate-local conditional Lemma 3.7 interface.  The radius-one lower
bound is obtained either directly from the opposite end, whose order is
`radius ^ 2`, or from the minimum-degree bootstrap.  This is the honest
source dichotomy: the ambient maximum candidate radius is never charged. -/
theorem exists_large_reachingCandidate_ball_of_conditional_source_local
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius ballRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (d deletedCap M degreeInto maxSlowSize : ℕ)
    (bounds : lm37SourceMinSize d < M →
      LM37SourceReachBounds (Fintype.card V) d deletedCap 2
        ballRadius M degreeInto maxSlowSize)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdeleted : deleted.card ≤ deletedCap)
    (hindexPos : 0 < SourceLemma35Numerics.indexCard (Fintype.card V))
    (hindex : SourceLemma35Numerics.indexCard (Fintype.card V) ≤
      (reachingEligibleSubfamily S targetSet connectionRadius).card)
    (hballRadiusPos : 0 < ballRadius)
    (hradius : ballRadius + ballRadius ≤ separation)
    (hprotected : deleted ∪ manyNeighborsInto G deleted degreeInto ⊆
      protectedSet)
    (hball : ∀ i :
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius =
        ballAvoidingFrom G
          ((deleted : Set V) ∪ (highDegree : Set V) ∪
            (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius)
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (hstart : ∀ hM : lm37SourceMinSize d < M,
      (bounds hM).growth 0 < minRadius ^ 2)
    (hstartOne : ∀ hM : lm37SourceMinSize d < M,
      (bounds hM).growth 1 < lm37SourceMinSize d)
    (hseedOrRetained : ∀ i :
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      lm37SourceMinSize d ≤ i.1.1.radius ^ 2 ∨
        lm37SourceMinSize d ≤
          d - degreeInto - (11 * i.1.1.radius + 1) - 2)
    (hneighbor : ∀ hM : lm37SourceMinSize d < M,
      ∀ (i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (ell s : ℕ), 0 < ell → ell ≤ ballRadius →
      i.1.1.radius ^ 2 ≤ s →
      (bounds hM).growth (ell - 1) < s →
      (bounds hM).stepLoss ell + (11 * i.1.1.radius + 1) + 2 * ell ≤
        (bounds hM).neighborBudget s)
    (hlargeBudgetSum : ∀ hM : lm37SourceMinSize d < M,
      ∀ (J : Finset
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (f : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius} → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlowSize) →
      ∑ i ∈ J, (bounds hM).neighborBudget (f i) ≤
        (bounds hM).largeBudget (∑ i ∈ J, f i)) :
    ∃ i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      M ≤ (ballAvoidingFrom G
        ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) ballRadius).card := by
  let I := {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius}
  let Aseed : I → Finset V := fun i ↦ reachingCandidateSeed i
  let Bset : I → Finset V := fun i ↦ reachingCandidateBarrier i
  let Cset : I → Finset V := fun i ↦ reachingCandidatePath i
  by_cases hM : lm37SourceMinSize d < M
  · let scale := (bounds hM).toCorrelatedScale
    apply exists_large_avoiding_ball_of_LM37CorrelatedScale
      G (1 / 1024) ((1 / 64) * (d : ℝ)) hexp deleted Aseed Bset Cset
        deletedCap (SourceLemma35Numerics.indexCard (Fintype.card V)) 2
        ballRadius M degreeInto scale hdeleted
    · simpa [I] using hindex
    · intro i
      dsimp [Aseed]
      rw [card_reachingCandidateSeed]
      exact (hstart hM).trans_le (Nat.pow_le_pow_left i.1.1.min_le 2)
    · intro i
      apply (hstartOne hM).trans_le
      rcases hseedOrRetained i with hseed | hretained
      · exact hseed.trans (by
          rw [← card_reachingCandidateSeed]
          exact Finset.card_le_card
            (subset_ballAvoidingFrom G _ (reachingCandidateSeed i) 1))
      · exact hretained.trans (reachingCandidate_radiusOne_bootstrap G i
          (hdegree (reachingCandidateConnectionData i).adjusted.rightRoot)
          hprotected)
    · intro i
      rcases hseedOrRetained i with hseed | hretained
      · exact hseed.trans (by
          rw [← card_reachingCandidateSeed]
          exact Finset.card_le_card
            (subset_ballAvoidingFrom G _ (reachingCandidateSeed i) 1))
      · exact hretained.trans (reachingCandidate_radiusOne_bootstrap G i
          (hdegree (reachingCandidateConnectionData i).adjusted.rightRoot)
          hprotected)
    · intro i
      simpa [Aseed, Bset, Cset] using reachingCandidate_limitedContact_barrier i
    · simpa [I, Aseed, Bset, Cset] using
        pairwiseDisjoint_reachingCandidate_actual_barrier_balls
          (G := G) hpair hradius hball
    · intro i ell hell hellRadius hslow
      dsimp [Bset]
      have hbarrier := card_reachingCandidateBarrier_le i
      have hseedCard : i.1.1.radius ^ 2 ≤
          (ballAvoidingFrom G
            ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
              (reachingCandidatePath i : Set V))
            (reachingCandidateSeed i) (ell - 1)).card := by
        rw [← card_reachingCandidateSeed]
        exact Finset.card_le_card
          (subset_ballAvoidingFrom G _ (reachingCandidateSeed i) (ell - 1))
      exact (Nat.add_le_add_right
        (Nat.add_le_add_left hbarrier ((bounds hM).stepLoss ell))
        (2 * ell)).trans
          (hneighbor hM i ell _ hell hellRadius hseedCard hslow)
    · intro i v hv
      dsimp [Aseed, Bset, Cset] at hv ⊢
      exact reachingCandidate_degreeInto_deleted_le G i
        (by omega) hprotected (hball i) v hv
    · exact hlargeBudgetSum hM
  · have hcardPos : 0 <
        (reachingEligibleSubfamily S targetSet connectionRadius).card :=
      hindexPos.trans_le hindex
    obtain ⟨A, hA⟩ := Finset.card_pos.mp hcardPos
    let i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius} :=
      ⟨A, hA⟩
    have htarget : M ≤ lm37SourceMinSize d := Nat.le_of_not_gt hM
    rcases hseedOrRetained i with hseed | hretained
    · exact ⟨i, htarget.trans (hseed.trans (by
        rw [← card_reachingCandidateSeed]
        exact Finset.card_le_card
          (subset_ballAvoidingFrom G _ (reachingCandidateSeed i) ballRadius)))⟩
    · have hOne := htarget.trans (hretained.trans
          (reachingCandidate_radiusOne_bootstrap G i
            (hdegree (reachingCandidateConnectionData i).adjusted.rightRoot)
            hprotected))
      exact ⟨i, hOne.trans (Finset.card_le_card
        (ballAvoidingFrom_radius_mono G _ _ (by omega : 1 ≤ ballRadius)))⟩

/-- Conditional Claim 4.5.  When the retained radius-one size already
reaches `targetOrder`, the conditional source theorem takes that direct
branch and no Lemma 3.7 numerical record is evaluated. -/
theorem card_reachingEligibleSubfamily_lt_of_no_targetAdjuster_conditional_source
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (d targetOrder totalRadius Delta deletedCap degreeInto maxSlowSize : ℕ)
    (bounds : lm37SourceMinSize d < targetOrder →
      LM37SourceReachBounds (Fintype.card V) d deletedCap 2
        connectionRadius targetOrder degreeInto maxSlowSize)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdeleted : deleted.card ≤ deletedCap)
    (hindexPos : 0 < SourceLemma35Numerics.indexCard (Fintype.card V))
    (hRadiusPos : 0 < connectionRadius)
    (hTargetSet : targetSet ⊆ highDegree \ deleted)
    (hHighDegree : ∀ v ∈ highDegree, Delta ≤ G.degree v)
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (hnoTarget : ¬ ∃ A : Adjuster G targetOrder totalRadius 1,
      Disjoint deleted A.verts)
    (hradius : connectionRadius + connectionRadius ≤ separation)
    (hprotected : deleted ∪ manyNeighborsInto G deleted degreeInto ⊆
      protectedSet)
    (hstart : ∀ hM : lm37SourceMinSize d < targetOrder,
      (bounds hM).growth 0 < minRadius ^ 2)
    (hstartOne : ∀ hM : lm37SourceMinSize d < targetOrder,
      (bounds hM).growth 1 < lm37SourceMinSize d)
    (hretained : ∀ i :
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      lm37SourceMinSize d ≤ i.1.1.radius ^ 2 ∨
        lm37SourceMinSize d ≤
          d - degreeInto - (11 * i.1.1.radius + 1) - 2)
    (hneighbor : ∀ hM : lm37SourceMinSize d < targetOrder,
      ∀ (i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (ell s : ℕ), 0 < ell → ell ≤ connectionRadius →
      i.1.1.radius ^ 2 ≤ s →
      (bounds hM).growth (ell - 1) < s →
      (bounds hM).stepLoss ell + (11 * i.1.1.radius + 1) + 2 * ell ≤
        (bounds hM).neighborBudget s)
    (hlargeBudgetSum : ∀ hM : lm37SourceMinSize d < targetOrder,
      ∀ (J : Finset
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (f : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius} → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlowSize) →
      ∑ i ∈ J, (bounds hM).neighborBudget (f i) ≤
        (bounds hM).largeBudget (∑ i ∈ J, f i))
    (hTargetPos : 0 < targetOrder)
    (hRightBudget : targetOrder +
      (deletedCap + 10 * maxRadius + (maxRadius + 1) +
        (connectionRadius + 1)) ≤ Delta)
    (hLeftBudget : targetOrder +
      (deletedCap + 10 * maxRadius + targetOrder) ≤ Delta)
    (hTotalRadius : maxRadius + connectionRadius + 1 ≤ totalRadius) :
    (reachingEligibleSubfamily S targetSet connectionRadius).card <
      SourceLemma35Numerics.indexCard (Fintype.card V) := by
  by_contra hcard
  have hindex : SourceLemma35Numerics.indexCard (Fintype.card V) ≤
      (reachingEligibleSubfamily S targetSet connectionRadius).card := by omega
  have hball : ∀ i :
      {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) connectionRadius =
        ballAvoidingFrom G
          ((deleted : Set V) ∪ (highDegree : Set V) ∪
            (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) connectionRadius := by
    intro i
    let P := reachingCandidateConnectionData i
    have hfinishHigh : P.finish ∈ highDegree :=
      (Finset.mem_sdiff.1 (hTargetSet P.finish_mem)).1
    have hnoSecond := no_second_highDegree_connection_of_no_targetAdjuster
      G i targetOrder totalRadius Delta deletedCap hTargetSet hHighDegree
        hnoTarget hTargetPos hdeleted hRightBudget hLeftBudget hTotalRadius
    exact reachingCandidate_ball_eq_highDegree_of_no_second i hfinishHigh hnoSecond
  obtain ⟨i, hiLarge⟩ :=
    exists_large_reachingCandidate_ball_of_conditional_source_local
      G hpair d deletedCap targetOrder degreeInto maxSlowSize bounds hexp
        hdeleted hindexPos hindex hRadiusPos hradius hprotected hball hdegree
        hstart hstartOne hretained hneighbor hlargeBudgetSum
  obtain ⟨A, hA⟩ := exists_targetAdjuster_of_large_reachingCandidate_ball
    G i targetOrder totalRadius Delta deletedCap hTargetSet hHighDegree hiLarge
      hTargetPos hdeleted hLeftBudget hTotalRadius (by omega)
  exact hnoTarget ⟨A, hA⟩

/-- Conditional Claim 4.6, with the same direct radius-one branch. -/
theorem card_reachingEligibleSubfamily_lt_of_no_targetAdjuster_expansion_conditional_source
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius ballRadius highRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (d targetOrder totalRadius deletedCap degreeInto farRadius maxSlowSize : ℕ)
    (bounds : lm37SourceMinSize d < targetOrder →
      LM37SourceReachBounds (Fintype.card V) d deletedCap 2
        ballRadius targetOrder degreeInto maxSlowSize)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdeleted : deleted.card ≤ deletedCap)
    (hindexPos : 0 < SourceLemma35Numerics.indexCard (Fintype.card V))
    (hBallRadiusPos : 0 < ballRadius)
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (hnoTarget : ¬ ∃ A : Adjuster G targetOrder totalRadius 1,
      Disjoint deleted A.verts)
    (hnoHigh : ∀ A ∈ S, ¬ A.1.ReachesAvoidingOwnCore deleted
      (highDegree \ deleted) highRadius)
    (hballHigh : ballRadius ≤ highRadius)
    {center : V} (Z : VertexExpansion G center targetOrder farRadius)
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
    (hprotected : deleted ∪ manyNeighborsInto G deleted degreeInto ⊆
      protectedSet)
    (hstart : ∀ hM : lm37SourceMinSize d < targetOrder,
      (bounds hM).growth 0 < minRadius ^ 2)
    (hstartOne : ∀ hM : lm37SourceMinSize d < targetOrder,
      (bounds hM).growth 1 < lm37SourceMinSize d)
    (hretained : ∀ i :
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      lm37SourceMinSize d ≤ i.1.1.radius ^ 2 ∨
        lm37SourceMinSize d ≤
          d - degreeInto - (11 * i.1.1.radius + 1) - 2)
    (hneighbor : ∀ hM : lm37SourceMinSize d < targetOrder,
      ∀ (i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (ell s : ℕ), 0 < ell → ell ≤ ballRadius →
      i.1.1.radius ^ 2 ≤ s →
      (bounds hM).growth (ell - 1) < s →
      (bounds hM).stepLoss ell + (11 * i.1.1.radius + 1) + 2 * ell ≤
        (bounds hM).neighborBudget s)
    (hlargeBudgetSum : ∀ hM : lm37SourceMinSize d < targetOrder,
      ∀ (J : Finset
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (f : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius} → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlowSize) →
      ∑ i ∈ J, (bounds hM).neighborBudget (f i) ≤
        (bounds hM).largeBudget (∑ i ∈ J, f i))
    (hTargetPos : 0 < targetOrder)
    (hLeftRadius : maxRadius + connectionRadius + 2 * farRadius ≤ totalRadius)
    (hRightRadius : maxRadius + ballRadius ≤ totalRadius) :
    (reachingEligibleSubfamily S targetSet connectionRadius).card <
      SourceLemma35Numerics.indexCard (Fintype.card V) := by
  by_contra hcard
  have hindex : SourceLemma35Numerics.indexCard (Fintype.card V) ≤
      (reachingEligibleSubfamily S targetSet connectionRadius).card := by omega
  have hball : ∀ i :
      {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius =
        ballAvoidingFrom G
          ((deleted : Set V) ∪ (highDegree : Set V) ∪
            (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius := by
    intro i
    have hiS :=
      ((mem_reachingEligibleSubfamily S targetSet connectionRadius i.1).1 i.2).1
    exact reachingCandidate_ball_eq_highDegree_of_no_highConnection i
      (hnoHigh i.1 hiS) hballHigh
  obtain ⟨i, hiLarge⟩ :=
    exists_large_reachingCandidate_ball_of_conditional_source_local
      G hpair d deletedCap targetOrder degreeInto maxSlowSize bounds hexp
        hdeleted hindexPos hindex hBallRadiusPos hradius hprotected hball
        hdegree hstart hstartOne hretained hneighbor hlargeBudgetSum
  have hfinishZ : (reachingCandidateConnectionData i).finish ∈ Z.verts :=
    hTargetSet (reachingCandidateConnectionData i).finish_mem
  obtain ⟨A, hA⟩ :=
    exists_targetAdjuster_of_large_reachingCandidate_ball_expansion
      i targetOrder totalRadius farRadius Z hfinishZ hiLarge (hZWorkspace i)
        hTargetPos hLeftRadius hRightRadius
  exact hnoTarget ⟨A, hA⟩

/-- The final post-Claim-4.6 contradiction with the literal samples from
Liu--Montgomery Lemma 3.5.  Unlike the older correlated-scale wrapper above,
the radius-one step is bootstrapped from the minimum degree, so this theorem
remains usable when `d` is much larger than the polylogarithmic adjuster
radius. -/
theorem false_of_conflictFree_nonreaching_family_source
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation highRadius ballRadius targetRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation}).Pairwise
      fun A B ↦ ¬ Conflict A.1 B.1 highDegree separation))
    (d deletedCap degreeInto maxSlowSize m Dtarget connectorQ
      connectorRadius : ℕ)
    (bounds : lm37SourceMinSize d < 10 * m ^ 2 * Dtarget →
      LM37SourceFinalTwoEndBounds (Fintype.card V) d deletedCap 0
        ballRadius m Dtarget degreeInto maxSlowSize)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hcard : S.card = SourceLemma35Numerics.indexCard (Fintype.card V))
    (hdeleted : deleted.card ≤ deletedCap)
    (hindexPos : 0 < SourceLemma35Numerics.indexCard (Fintype.card V))
    (hBallRadiusPos : 0 < ballRadius)
    (hnoHigh : ∀ A ∈ S, ¬ A.1.ReachesAvoidingOwnCore deleted
      (highDegree \ deleted) highRadius)
    (hnoTarget : ∀ A ∈ S, ¬ A.1.ReachesAvoidingOwnCore deleted
      targetSet targetRadius)
    (hballHigh : ballRadius ≤ highRadius)
    (hseparation : ballRadius + ballRadius ≤ separation)
    (hdegreeMin : ∀ v : V, d ≤ G.degree v)
    (hstart : ∀ hM : lm37SourceMinSize d < 10 * m ^ 2 * Dtarget,
      (bounds hM).growth 0 < 2 * minRadius ^ 2)
    (hstartOne : ∀ hM : lm37SourceMinSize d < 10 * m ^ 2 * Dtarget,
      (bounds hM).growth 1 < lm37SourceMinSize d)
    (hretained : ∀ r, minRadius ≤ r → r ≤ maxRadius →
      lm37SourceMinSize d ≤ 2 * r ^ 2 ∨
        lm37SourceMinSize d ≤ d - degreeInto - 10 * r)
    (hneighbor : ∀ hM : lm37SourceMinSize d < 10 * m ^ 2 * Dtarget,
      ∀ (r ell s : ℕ), minRadius ≤ r → r ≤ maxRadius →
      2 * r ^ 2 ≤ s → 0 < ell → ell ≤ ballRadius →
      (bounds hM).growth (ell - 1) < s →
      (bounds hM).stepLoss ell + 10 * r ≤
        (bounds hM).neighborBudget s)
    (hdegree : ∀ i : S, ∀ v ∈ ballAvoidingFrom G
      (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
      i.1.1.ends ballRadius,
        (G.neighborFinset v ∩ deleted).card ≤ degreeInto)
    (hlargeBudgetSum : ∀ hM : lm37SourceMinSize d < 10 * m ^ 2 * Dtarget,
      ∀ (J : Finset S) (f : S → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlowSize) →
      ∑ i ∈ J, (bounds hM).neighborBudget (f i) ≤
        (bounds hM).largeBudget (∑ i ∈ J, f i))
    (hTargetDisjoint : ∀ i : S,
      Disjoint targetSet (deleted ∪ i.1.1.adjuster.core))
    (hBallLower : ((1 / 64) * (d : ℝ)) / 2 ≤
      (10 * m ^ 2 * Dtarget : ℕ))
    (hTargetLower : ((1 / 64) * (d : ℝ)) / 2 ≤
      (targetSet.card : ℝ))
    (hBallRate : ∀ i : S, ∀ s : ℕ, 10 * m ^ 2 * Dtarget ≤ s →
      s ≤ Fintype.card V / 2 →
      (((((deleted ∪ i.1.1.adjuster.core).card + connectorQ : ℕ)) : ℝ) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ)))
    (hTargetRate : ∀ i : S, ∀ s : ℕ, targetSet.card ≤ s →
      s ≤ Fintype.card V / 2 →
      (((((deleted ∪ i.1.1.adjuster.core).card + connectorQ : ℕ)) : ℝ) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ)))
    (hBallSteps : Fintype.card V / 2 + 1 ≤
      10 * m ^ 2 * Dtarget + connectorRadius * connectorQ)
    (hTargetSteps : Fintype.card V / 2 + 1 ≤
      targetSet.card + connectorRadius * connectorQ)
    (hTotalRadius : ballRadius + 2 * connectorRadius ≤ targetRadius) : False := by
  have hiLargeExists : ∃ i : S, 10 * m ^ 2 * Dtarget ≤
      (ballAvoidingFrom G
        (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
        i.1.1.ends ballRadius).card := by
    let Aseed : S → Finset V := fun i ↦ i.1.1.ends
    let Bset : S → Finset V := fun i ↦ i.1.1.adjuster.core
    let Cset : S → Finset V := fun _ ↦ ∅
    have hpairHigh :
        ((Finset.univ : Finset S) : Set S).PairwiseDisjoint
          (fun i ↦ ballAvoidingFrom G
            ((highDegree : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
            (Aseed i) ballRadius) :=
      pairwiseDisjoint_candidate_avoidingBalls
        (G := G) hpair hseparation Bset Cset
    have hpairActual :
        ((Finset.univ : Finset S) : Set S).PairwiseDisjoint
          (fun i ↦ ballAvoidingFrom G
            ((deleted : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
            (Aseed i) ballRadius) := by
      intro i hi j hj hij
      apply (hpairHigh hi hj hij).mono
      · simpa [Aseed, Bset, Cset, Set.union_empty] using
          source_candidate_ball_subset_highDegree_ball_of_no_high
            G i.1.1 i.1.2 (hnoHigh i.1 i.2) hballHigh
      · simpa [Aseed, Bset, Cset, Set.union_empty] using
          source_candidate_ball_subset_highDegree_ball_of_no_high
            G j.1.1 j.1.2 (hnoHigh j.1 j.2) hballHigh
    suffices hlarge : ∃ i : S, 10 * m ^ 2 * Dtarget ≤
        (ballAvoidingFrom G
          ((deleted : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
          (Aseed i) ballRadius).card by
      obtain ⟨i, hi⟩ := hlarge
      exact ⟨i, by simpa [Aseed, Bset, Cset, Set.union_empty] using hi⟩
    by_cases hM : lm37SourceMinSize d < 10 * m ^ 2 * Dtarget
    · let scale := (bounds hM).toCorrelatedScale
      apply exists_large_avoiding_ball_of_LM37CorrelatedScale
        G (1 / 1024) ((1 / 64) * (d : ℝ)) hexp deleted Aseed Bset Cset
          deletedCap (SourceLemma35Numerics.indexCard (Fintype.card V)) 0
          ballRadius (10 * m ^ 2 * Dtarget) degreeInto scale hdeleted
      · simpa [hcard]
      · intro i
        dsimp [Aseed]
        rw [card_ends]
        exact (hstart hM).trans_le (Nat.mul_le_mul_left 2
          (Nat.pow_le_pow_left i.1.1.min_le 2))
      · intro i
        apply (hstartOne hM).trans_le
        rcases hretained i.1.1.radius i.1.1.min_le i.1.1.le_max with
          hseed | hdegreeRetained
        · exact hseed.trans (by
            rw [← card_ends]
            exact Finset.card_le_card
              (subset_ballAvoidingFrom G _ i.1.1.ends 1))
        · have hx : i.1.1.adjuster.leftRoot ∈ Aseed i := by
            simpa [Aseed] using i.1.1.adjuster.leftEnd.root_mem
          have hdisjoint : Disjoint (Aseed i)
              (deleted ∪ Bset i ∪ Cset i) := by
            simpa [Aseed, Bset, Cset] using
              i.1.1.ends_disjoint_deleted_union_core i.1.2
          have hcore : (Bset i).card ≤ 10 * i.1.1.radius := by
            simpa [Bset] using i.1.1.adjuster.core_card_le
          have hxBall : i.1.1.adjuster.leftRoot ∈ ballAvoidingFrom G
              ((deleted : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
              (Aseed i) ballRadius := subset_ballAvoidingFrom G _ _ _ hx
          have hboot :=
            degree_sub_degreeInto_sub_card_sub_contact_le_card_ballAvoidingFrom_one
              G deleted (Bset i) (Cset i) (Aseed i)
                i.1.1.adjuster.leftRoot d degreeInto (10 * i.1.1.radius) 0
                hx hdisjoint (hdegreeMin i.1.1.adjuster.leftRoot)
                (by simpa [Aseed, Bset, Cset, Set.union_empty] using
                  hdegree i i.1.1.adjuster.leftRoot (by
                    simpa [Aseed, Bset, Cset, Set.union_empty] using hxBall))
                hcore (by
                  intro r
                  simp [Cset, HasLimitedContactAfterDeletion,
                    blockedExternalNeighborhood])
          exact hdegreeRetained.trans (by simpa using hboot)
      · intro i
        rcases hretained i.1.1.radius i.1.1.min_le i.1.1.le_max with
          hseed | hdegreeRetained
        · exact hseed.trans (by
            rw [← card_ends]
            exact Finset.card_le_card
              (subset_ballAvoidingFrom G _ i.1.1.ends 1))
        · have hx : i.1.1.adjuster.leftRoot ∈ Aseed i := by
            simpa [Aseed] using i.1.1.adjuster.leftEnd.root_mem
          have hdisjoint : Disjoint (Aseed i)
              (deleted ∪ Bset i ∪ Cset i) := by
            simpa [Aseed, Bset, Cset] using
              i.1.1.ends_disjoint_deleted_union_core i.1.2
          have hcore : (Bset i).card ≤ 10 * i.1.1.radius := by
            simpa [Bset] using i.1.1.adjuster.core_card_le
          have hxBall : i.1.1.adjuster.leftRoot ∈ ballAvoidingFrom G
              ((deleted : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
              (Aseed i) ballRadius := subset_ballAvoidingFrom G _ _ _ hx
          have hboot :=
            degree_sub_degreeInto_sub_card_sub_contact_le_card_ballAvoidingFrom_one
              G deleted (Bset i) (Cset i) (Aseed i)
                i.1.1.adjuster.leftRoot d degreeInto (10 * i.1.1.radius) 0
                hx hdisjoint (hdegreeMin i.1.1.adjuster.leftRoot)
                (by simpa [Aseed, Bset, Cset, Set.union_empty] using
                  hdegree i i.1.1.adjuster.leftRoot (by
                    simpa [Aseed, Bset, Cset, Set.union_empty] using hxBall))
                hcore (by
                  intro r
                  simp [Cset, HasLimitedContactAfterDeletion,
                    blockedExternalNeighborhood])
          exact hdegreeRetained.trans (by simpa using hboot)
      · intro i r
        simp [Cset, HasLimitedContactAfterDeletion, blockedExternalNeighborhood]
      · exact hpairActual
      · intro i ell hell hellRadius hslow
        dsimp [Bset]
        have hcore : i.1.1.adjuster.core.card ≤ 10 * i.1.1.radius := by
          simpa using i.1.1.adjuster.core_card_le
        have hseedCard : 2 * i.1.1.radius ^ 2 ≤
            (ballAvoidingFrom G
              ((deleted : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
              (Aseed i) (ell - 1)).card := by
          rw [← card_ends]
          exact Finset.card_le_card
            (subset_ballAvoidingFrom G _ i.1.1.ends (ell - 1))
        simpa [scale, LM37SourceBounds.toCorrelatedScale, Cset] using
          (Nat.add_le_add_left hcore ((bounds hM).stepLoss ell)).trans
            (hneighbor hM i.1.1.radius ell _ i.1.1.min_le i.1.1.le_max
              hseedCard hell hellRadius hslow)
      · intro i v hv
        have hv' : v ∈ ballAvoidingFrom G
            (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
            i.1.1.ends ballRadius := by
          simpa [Aseed, Bset, Cset, Set.union_empty] using hv
        exact hdegree i v hv'
      · simpa [scale, LM37SourceBounds.toCorrelatedScale] using
          hlargeBudgetSum hM
    · have hScardPos : 0 < S.card := by simpa [hcard] using hindexPos
      obtain ⟨A, hAS⟩ := Finset.card_pos.mp hScardPos
      let i : S := ⟨A, hAS⟩
      have htarget : 10 * m ^ 2 * Dtarget ≤ lm37SourceMinSize d :=
        Nat.le_of_not_gt hM
      rcases hretained i.1.1.radius i.1.1.min_le i.1.1.le_max with
        hseed | hdegreeRetained
      · exact ⟨i, by
          apply htarget.trans (hseed.trans ?_)
          rw [← card_ends]
          exact Finset.card_le_card
            (subset_ballAvoidingFrom G _ i.1.1.ends ballRadius)⟩
      · let W : Finset V := deleted ∪ i.1.1.adjuster.core
        have hx : i.1.1.adjuster.leftRoot ∈ i.1.1.ends :=
          i.1.1.leftRoot_mem_ends
        have hxBall : i.1.1.adjuster.leftRoot ∈ ballAvoidingFrom G
            (W : Set V) i.1.1.ends ballRadius :=
          subset_ballAvoidingFrom G _ _ _ hx
        have hboot :=
          degree_sub_degreeInto_sub_card_sub_contact_le_card_ballAvoidingFrom_one
            G deleted i.1.1.adjuster.core ∅ i.1.1.ends
              i.1.1.adjuster.leftRoot d degreeInto (10 * i.1.1.radius) 0 hx
              (by simpa [W] using
                i.1.1.ends_disjoint_deleted_union_core i.1.2)
              (hdegreeMin i.1.1.adjuster.leftRoot) (hdegree i _ hxBall)
              (by simpa using i.1.1.adjuster.core_card_le) (by
                intro r
                simp [HasLimitedContactAfterDeletion,
                  blockedExternalNeighborhood])
        have hOne : 10 * m ^ 2 * Dtarget ≤
            (ballAvoidingFrom G (W : Set V) i.1.1.ends 1).card :=
          htarget.trans (hdegreeRetained.trans (by simpa [W] using hboot))
        have hballMono :
            ballAvoidingFrom G (W : Set V) i.1.1.ends 1 ⊆
              ballAvoidingFrom G (W : Set V) i.1.1.ends ballRadius :=
          ballAvoidingFrom_radius_mono G (W : Set V) i.1.1.ends
            (by omega : 1 ≤ ballRadius)
        have hcardMono :
            (ballAvoidingFrom G (W : Set V) i.1.1.ends 1).card ≤
              (ballAvoidingFrom G (W : Set V) i.1.1.ends ballRadius).card :=
          Finset.card_le_card hballMono
        exact ⟨i, by
          simpa [W, Aseed, Bset, Cset, Set.union_empty] using
            hOne.trans hcardMono⟩
  obtain ⟨i, hiLarge⟩ := hiLargeExists
  let W : Finset V := deleted ∪ i.1.1.adjuster.core
  let largeBall : Finset V := ballAvoidingFrom G (W : Set V)
    i.1.1.ends ballRadius
  have hiLarge' : 10 * m ^ 2 * Dtarget ≤ largeBall.card := by
    simpa only [largeBall, W] using hiLarge
  have hEndsW : Disjoint i.1.1.ends W := by
    simpa only [W] using i.1.1.ends_disjoint_deleted_union_core i.1.2
  have hBallW : Disjoint largeBall W :=
    disjoint_ballAvoidingFrom_forbidden G i.1.1.ends W ballRadius hEndsW
  obtain ⟨a, haBall, b, hbTarget, q, hq, hqLength⟩ :=
    exists_avoiding_path_between_of_lmExpander_growth
      G (1 / 1024) ((1 / 64) * (d : ℝ)) hexp W largeBall targetSet
      connectorQ connectorRadius
      (hBallLower.trans (by exact_mod_cast hiLarge')) hTargetLower
      (fun s hs hsN ↦ hBallRate i s (hiLarge'.trans hs) hsN)
      (fun s hs hsN ↦ hTargetRate i s hs hsN)
      (hBallSteps.trans (Nat.add_le_add_right hiLarge'
        (connectorRadius * connectorQ))) hTargetSteps
  obtain ⟨x, hxEnds, p, hp, hpLength⟩ :=
    (mem_ballAvoidingFrom G (W : Set V) i.1.1.ends ballRadius a).1 haBall
  have hpAvoid : p.Avoids (W : Set V) ∅ := by
    intro z hz hzW
    have hzx := hp.2 z hz hzW
    have hzEq : z = x := by simpa using hzx
    exact (Finset.disjoint_left.1 hEndsW hxEnds (hzEq ▸ hzW)).elim
  have haW : a ∉ W := by
    intro haW
    exact (Finset.disjoint_left.1 hBallW haBall haW).elim
  have hbW : b ∉ W := by
    intro hbW
    exact (Finset.disjoint_left.1 (hTargetDisjoint i) hbTarget hbW).elim
  have hqAvoid : q.Avoids (W : Set V) ∅ := by
    intro z hz hzW
    have hzab := hq.2 z hz hzW
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzab
    rcases hzab with rfl | rfl
    · exact (haW hzW).elim
    · exact (hbW hzW).elim
  let w : G.Walk x b := p.append q
  let route : G.Walk x b := w.bypass
  have hroutePath : route.IsPath := w.bypass_isPath
  have hrouteAvoid : route.Avoids (W : Set V) ∅ := by
    intro z hz hzW
    have hzw : z ∈ w.support := w.support_bypass_subset_support hz
    change z ∈ (p.append q).support at hzw
    rw [Walk.mem_support_append_iff] at hzw
    rcases hzw with hzp | hzq
    · exact hpAvoid z hzp hzW
    · exact hqAvoid z hzq hzW
  have hrouteLength : route.length ≤ targetRadius := by
    calc
      route.length ≤ w.length := w.length_bypass_le_length
      _ = p.length + q.length := by simp [w]
      _ ≤ ballRadius + 2 * connectorRadius :=
        Nat.add_le_add hpLength hqLength
      _ ≤ targetRadius := hTotalRadius
  exact (hnoTarget i.1 i.2) ⟨x, hxEnds, b, hbTarget, route,
    hroutePath, hrouteAvoid, hrouteLength⟩

/-- The complete post-Claim-4.4 assembly with the literal source samples in
all three applications of Lemma 3.7.  The family cardinalities are fixed to
`floor(N^(1/8))`, exactly as in the paper.  In particular, none of the three
growth arguments uses the nonuniform `N`-dependent divisor from the earlier
generic wrapper. -/
theorem false_of_claim45_claim46_and_final_source
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {deleted highDegree protectedSet : Finset V}
    {separation highRadius targetRadius ballRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
          ¬ Conflict A.1 B.1 highDegree separation))
    (d targetOrder auxiliaryOrder totalRadius Delta deletedCap degreeInto
      maxSlow45 maxSlow46 maxSlowFinal finalM connectorStart
      connectorWorkspace connectorRadius : ℕ)
    (hfour : 4 * SourceLemma35Numerics.indexCard (Fintype.card V) ≤ S.card)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (bounds45 : lm37SourceMinSize d < targetOrder →
      LM37SourceReachBounds (Fintype.card V) d deletedCap 2
        highRadius targetOrder degreeInto maxSlow45)
    (bounds46 : lm37SourceMinSize d < auxiliaryOrder →
      LM37SourceReachBounds (Fintype.card V) d deletedCap 2
        ballRadius auxiliaryOrder degreeInto maxSlow46)
    (boundsFinal : lm37SourceMinSize d < 10 * finalM ^ 2 * targetOrder →
      LM37SourceFinalTwoEndBounds (Fintype.card V) d deletedCap 0
        ballRadius finalM targetOrder degreeInto maxSlowFinal)
    (hdeleted : deleted.card ≤ deletedCap)
    (hindexPos : 0 < SourceLemma35Numerics.indexCard (Fintype.card V))
    (hHighRadiusPos : 0 < highRadius)
    (hBallRadiusPos : 0 < ballRadius)
    (hHighDegree : ∀ v ∈ highDegree, Delta ≤ G.degree v)
    (hLowDegree : ∀ v ∉ highDegree, G.degree v ≤ Delta)
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (hnoTarget : ¬ ∃ A : Adjuster G targetOrder totalRadius 1,
      Disjoint deleted A.verts)
    (h45radius : highRadius + highRadius ≤ separation)
    (h46radius : ballRadius + ballRadius ≤ separation)
    (hballHigh : ballRadius ≤ highRadius)
    (hprotected : deleted ∪ manyNeighborsInto G deleted degreeInto ⊆
      protectedSet)
    (h45start : ∀ hM : lm37SourceMinSize d < targetOrder,
      (bounds45 hM).growth 0 < minRadius ^ 2)
    (h45startOne : ∀ hM : lm37SourceMinSize d < targetOrder,
      (bounds45 hM).growth 1 < lm37SourceMinSize d)
    (h45retained : ∀ r, minRadius ≤ r → r ≤ maxRadius →
      lm37SourceMinSize d ≤ r ^ 2 ∨
        lm37SourceMinSize d ≤ d - degreeInto - (11 * r + 1) - 2)
    (h45neighbor : ∀ hM : lm37SourceMinSize d < targetOrder,
      ∀ r ell s, minRadius ≤ r → r ≤ maxRadius → r ^ 2 ≤ s →
      0 < ell → ell ≤ highRadius →
      (bounds45 hM).growth (ell - 1) < s →
      (bounds45 hM).stepLoss ell + (11 * r + 1) + 2 * ell ≤
        (bounds45 hM).neighborBudget s)
    (h45largeBudgetSum : ∀ hM : lm37SourceMinSize d < targetOrder,
      ∀ {I : Type u} [DecidableEq I]
      (J : Finset I) (f : I → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlow45) →
      ∑ i ∈ J, (bounds45 hM).neighborBudget (f i) ≤
        (bounds45 hM).largeBudget (∑ i ∈ J, f i))
    (hTargetPos : 0 < targetOrder)
    (hAuxiliaryPos : 0 < auxiliaryOrder)
    (hTargetOrderLeAuxiliary : targetOrder ≤ auxiliaryOrder)
    (hRightBudget : targetOrder +
      (deletedCap + 10 * maxRadius + (maxRadius + 1) +
        (highRadius + 1)) ≤ Delta)
    (hLeftBudget : targetOrder +
      (deletedCap + 10 * maxRadius + targetOrder) ≤ Delta)
    (h45TotalRadius : maxRadius + highRadius + 1 ≤ totalRadius)
    (hn : 32 ≤ Fintype.card V) (hd : 1 ≤ d)
    (hdn : d ≤ Fintype.card V)
    (workspaceCap : ℕ)
    (hworkspaceCap : deletedCap +
        2 * SourceLemma35Numerics.indexCard (Fintype.card V) *
          ((2 * maxRadius ^ 2 + 10 * maxRadius) +
            2 * maxRadius ^ 2 * (Delta + 1) ^ ballRadius) ≤ workspaceCap)
    (hworkspaceGain : workspaceCap ≤
      lm43GrowthGain (Fintype.card V) (lm43K (Fintype.card V)))
    (hworkspaceRoom : workspaceCap + lm43K (Fintype.card V) ≤
      Fintype.card V)
    (hAuxiliaryK : auxiliaryOrder ≤ lm43K (Fintype.card V))
    (hdenominator : 6 * lm43GrowthDenominator (Fintype.card V) ≤
      lm43K (Fintype.card V))
    (h46start : ∀ hM : lm37SourceMinSize d < auxiliaryOrder,
      (bounds46 hM).growth 0 < minRadius ^ 2)
    (h46startOne : ∀ hM : lm37SourceMinSize d < auxiliaryOrder,
      (bounds46 hM).growth 1 < lm37SourceMinSize d)
    (h46retained : ∀ r, minRadius ≤ r → r ≤ maxRadius →
      lm37SourceMinSize d ≤ r ^ 2 ∨
        lm37SourceMinSize d ≤ d - degreeInto - (11 * r + 1) - 2)
    (h46neighbor : ∀ hM : lm37SourceMinSize d < auxiliaryOrder,
      ∀ r ell s, minRadius ≤ r → r ≤ maxRadius → r ^ 2 ≤ s →
      0 < ell → ell ≤ ballRadius →
      (bounds46 hM).growth (ell - 1) < s →
      (bounds46 hM).stepLoss ell + (11 * r + 1) + 2 * ell ≤
        (bounds46 hM).neighborBudget s)
    (h46largeBudgetSum : ∀ hM : lm37SourceMinSize d < auxiliaryOrder,
      ∀ {I : Type u} [DecidableEq I]
      (J : Finset I) (f : I → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlow46) →
      ∑ i ∈ J, (bounds46 hM).neighborBudget (f i) ≤
        (bounds46 hM).largeBudget (∑ i ∈ J, f i))
    (hLeftRadius : maxRadius + targetRadius +
      2 * lm43FarRadius (Fintype.card V) ≤ totalRadius)
    (hRightRadius : maxRadius + ballRadius ≤ totalRadius)
    (hFinalStart : ∀ hM : lm37SourceMinSize d <
        10 * finalM ^ 2 * targetOrder,
      (boundsFinal hM).growth 0 < 2 * minRadius ^ 2)
    (hFinalStartOne : ∀ hM : lm37SourceMinSize d <
        10 * finalM ^ 2 * targetOrder,
      (boundsFinal hM).growth 1 < lm37SourceMinSize d)
    (hFinalRetained : ∀ r, minRadius ≤ r → r ≤ maxRadius →
      lm37SourceMinSize d ≤ 2 * r ^ 2 ∨
        lm37SourceMinSize d ≤ d - degreeInto - 10 * r)
    (hFinalNeighbor : ∀ hM : lm37SourceMinSize d <
        10 * finalM ^ 2 * targetOrder,
      ∀ r ell s, minRadius ≤ r → r ≤ maxRadius →
      r ^ 2 ≤ s → 0 < ell → ell ≤ ballRadius →
      (boundsFinal hM).growth (ell - 1) < s →
      (boundsFinal hM).stepLoss ell + 10 * r ≤
        (boundsFinal hM).neighborBudget s)
    (hFinalLargeBudgetSum : ∀ hM : lm37SourceMinSize d <
        10 * finalM ^ 2 * targetOrder,
      ∀ {I : Type u} [DecidableEq I]
      (J : Finset I) (f : I → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlowFinal) →
      ∑ i ∈ J, (boundsFinal hM).neighborBudget (f i) ≤
        (boundsFinal hM).largeBudget (∑ i ∈ J, f i))
    (hConnectorWorkspace : deletedCap + 10 * maxRadius ≤
      connectorWorkspace)
    (hBallSeed : connectorStart ≤ 10 * finalM ^ 2 * targetOrder ∨
      connectorStart + connectorWorkspace ≤ d)
    (hTargetSeed : connectorStart ≤ auxiliaryOrder ∨
      connectorStart + connectorWorkspace ≤ d)
    (growth : LM42GrowthSchedule (Fintype.card V) connectorStart
      connectorWorkspace connectorRadius (1 / 1024)
        ((1 / 64) * (d : ℝ)))
    (hFinalRadius : ballRadius + 2 * (connectorRadius + 1) ≤ targetRadius) :
    False := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  letI : DecidableRel G.Adj := originalDecAdj
  let R := SourceLemma35Numerics.indexCard (Fintype.card V)
  have hbad45 :=
    card_reachingEligibleSubfamily_lt_of_no_targetAdjuster_conditional_source
    G hpair d targetOrder totalRadius Delta deletedCap degreeInto maxSlow45
      bounds45 hexp hdeleted hindexPos hHighRadiusPos
      (by exact Finset.Subset.rfl) hHighDegree hdegree
      hnoTarget h45radius hprotected h45start h45startOne
      (by
        intro i
        exact h45retained i.1.1.radius i.1.1.min_le i.1.1.le_max)
      (by
        intro hM i ell s hell hellRadius hradiusSq hslow
        exact h45neighbor hM i.1.1.radius ell s i.1.1.min_le i.1.1.le_max
          hradiusSq hell hellRadius hslow)
      (fun hM ↦ by
        intro J f hf
        apply h45largeBudgetSum hM
        exact hf)
      hTargetPos hRightBudget hLeftBudget h45TotalRadius
  obtain ⟨T, hTS, hTcard, hTnoHigh⟩ :=
    exists_two_mul_nonreaching_subfamily (highRadius := highRadius) (R := R)
      S (by simpa only [R] using hfour) (by simpa only [R] using hbad45)
  have hpairT : ((T : Set
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
          ¬ Conflict A.1 B.1 highDegree separation) := by
    intro A hA B hB hAB
    exact hpair (hTS hA) (hTS hB) hAB
  have hTworkspace :
      (claim46WorkspaceOf G deleted highDegree T ballRadius).card ≤
        workspaceCap := by
    calc
      (claim46WorkspaceOf G deleted highDegree T ballRadius).card ≤
          deleted.card + T.card *
            ((2 * maxRadius ^ 2 + 10 * maxRadius) +
              2 * maxRadius ^ 2 * (Delta + 1) ^ ballRadius) :=
        card_claim46WorkspaceOf_le G deleted highDegree protectedSet separation
          ballRadius Delta T hLowDegree
      _ ≤ deletedCap + 2 * R *
            ((2 * maxRadius ^ 2 + 10 * maxRadius) +
              2 * maxRadius ^ 2 * (Delta + 1) ^ ballRadius) := by
        rw [hTcard]
        exact Nat.add_le_add_right hdeleted _
      _ ≤ workspaceCap := by simpa only [R] using hworkspaceCap
  obtain ⟨center, Z, hZW, hZfresh⟩ := exists_claim46_auxiliary_expansion
    G d auxiliaryOrder targetRadius ballRadius highRadius hexp T hTnoHigh
      hballHigh hn hd hdn
      (hTworkspace.trans hworkspaceGain)
      ((Nat.add_le_add_right hTworkspace _).trans hworkspaceRoom)
      hAuxiliaryPos hAuxiliaryK hdenominator
  have hnoAuxiliary :
      ¬ ∃ A : Adjuster G auxiliaryOrder totalRadius 1,
        Disjoint deleted A.verts :=
    no_auxiliaryAdjuster_of_no_targetAdjuster hnoTarget hTargetPos
      hTargetOrderLeAuxiliary
  have hbad46 :=
    card_reachingEligibleSubfamily_lt_of_no_targetAdjuster_expansion_conditional_source
      G hpairT d auxiliaryOrder totalRadius deletedCap degreeInto
        (lm43FarRadius (Fintype.card V)) maxSlow46 bounds46 hexp hdeleted
        hindexPos hBallRadiusPos hdegree hnoAuxiliary hTnoHigh hballHigh Z
        (by exact Finset.Subset.rfl)
        (hZfresh Z.verts Finset.Subset.rfl) h46radius hprotected h46start
        h46startOne
        (by
          intro i
          exact h46retained i.1.1.radius i.1.1.min_le i.1.1.le_max)
        (by
          intro hM i ell s hell hellRadius hradiusSq hslow
          exact h46neighbor hM i.1.1.radius ell s i.1.1.min_le i.1.1.le_max
            hradiusSq hell hellRadius hslow)
        (fun hM ↦ by
          intro J f hf
          apply h46largeBudgetSum hM
          exact hf)
        hAuxiliaryPos hLeftRadius hRightRadius
  obtain ⟨Q, hQT, hQcard, hQnoHigh, hQnoZ⟩ :=
    exists_nonreaching_subfamily_card_eq T hTcard hTnoHigh
      (by simpa only [R] using hbad46)
  have hpairQ : ((Q : Set
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
          ¬ Conflict A.1 B.1 highDegree separation) := by
    intro A hA B hB hAB
    exact hpairT (hQT hA) (hQT hB) hAB
  have hZDisjoint : ∀ i : Q,
      Disjoint Z.verts (deleted ∪ i.1.1.adjuster.core) := by
    intro i
    apply hZW.mono_right
    intro v hv
    rw [Finset.mem_union] at hv
    rcases hv with hvDeleted | hvCore
    · exact deleted_subset_claim46WorkspaceOf
        G deleted highDegree T ballRadius hvDeleted
    · apply candidate_adjuster_verts_subset_claim46WorkspaceOf
        G deleted highDegree T ballRadius (hQT i.2)
      exact i.1.1.adjuster.core_subset_verts hvCore
  have hFinalDegree : ∀ i : Q, ∀ v ∈ ballAvoidingFrom G
      (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
      i.1.1.ends ballRadius,
      (G.neighborFinset v ∩ deleted).card ≤ degreeInto := by
    intro i v hv
    let actual : Finset V := ballAvoidingFrom G
      (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
      i.1.1.ends ballRadius
    let highBall : Finset V := ballAvoidingFrom G (highDegree : Set V)
      i.1.1.ends ballRadius
    let highCoreBall : Finset V := ballAvoidingFrom G
      (((highDegree ∪ i.1.1.adjuster.core : Finset V) : Set V))
      i.1.1.ends ballRadius
    have hactualHighCore : actual ⊆ highCoreBall := by
      simpa only [actual, highCoreBall] using
        candidate_ball_subset_highDegree_ball_of_no_high G i.1.1 i.1.2
          (hQnoHigh i.1 i.2) hballHigh
    have hhighCoreHigh : highCoreBall ⊆ highBall := by
      apply ballAvoidingFrom_forbidden_anti G
      intro z hz
      rw [Finset.coe_union]
      exact Or.inl hz
    have hactualHigh : actual ⊆ highBall :=
      hactualHighCore.trans hhighCoreHigh
    have hhighProtected : Disjoint highBall protectedSet :=
      candidate_highDegree_ball_disjoint_protected i.1.1 i.1.2
        (by omega)
    have hactualProtected : Disjoint actual protectedSet :=
      hhighProtected.mono_left hactualHigh
    have hactualDeleted : Disjoint actual deleted :=
      hactualProtected.mono_right
        (Finset.Subset.trans Finset.subset_union_left hprotected)
    have hactualExceptional :
        Disjoint actual (manyNeighborsInto G deleted degreeInto) :=
      hactualProtected.mono_right
        (Finset.Subset.trans Finset.subset_union_right hprotected)
    have hdegreeV := neighborsInto_le_of_disjoint_manyNeighborsInto
      G deleted actual degreeInto hactualDeleted hactualExceptional v
        (by simpa only [actual] using hv)
    have hinter : G.neighborFinset v ∩ deleted =
        deleted.filter fun w ↦ G.Adj v w := by
      ext w
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        Finset.mem_filter]
      tauto
    rw [hinter]
    exact hdegreeV
  obtain ⟨i, hiLarge⟩ :=
    exists_large_twoEnd_ball_of_conditional_LM37SourceFinalBounds
      G hpairQ d deletedCap degreeInto finalM targetOrder maxSlowFinal
        boundsFinal hexp hindexPos hQcard hdeleted hQnoHigh hballHigh
        hBallRadiusPos h46radius hdegree hFinalStart hFinalStartOne
        (by
          intro j
          exact hFinalRetained j.1.1.radius j.1.1.min_le j.1.1.le_max)
        (by
          intro hM j ell s hell hellRadius hslow hradiusSq
          exact hFinalNeighbor hM j.1.1.radius ell s j.1.1.min_le
            j.1.1.le_max hradiusSq hell hellRadius hslow)
        hFinalDegree (fun hM ↦ by
          intro J f hf
          apply hFinalLargeBudgetSum hM
          exact hf)
  have hTargetNonempty : Z.verts.Nonempty := Z.vertices_nonempty
  have hiWorkspace :
      (deleted ∪ i.1.1.adjuster.core).card ≤ connectorWorkspace := by
    calc
      (deleted ∪ i.1.1.adjuster.core).card ≤
          deleted.card + i.1.1.adjuster.core.card :=
        Finset.card_union_le deleted i.1.1.adjuster.core
      _ ≤ deletedCap + 10 * maxRadius := by
        apply Nat.add_le_add hdeleted
        calc
          i.1.1.adjuster.core.card ≤ 10 * i.1.1.radius := by
            simpa using i.1.1.adjuster.core_card_le
          _ ≤ 10 * maxRadius := Nat.mul_le_mul_left 10 i.1.1.le_max
      _ ≤ connectorWorkspace := hConnectorWorkspace
  exact false_of_large_twoEnd_ball_and_nonreaching_bootstrap
    G (1 / 1024) ((1 / 64) * (d : ℝ)) hexp i
      (10 * finalM ^ 2 * targetOrder) d connectorStart connectorWorkspace
      connectorRadius hiLarge hdegree hQnoZ hTargetNonempty (hZDisjoint i)
      hiWorkspace hBallSeed
      (by simpa only [VertexExpansion.card_verts] using hTargetSeed)
      growth hFinalRadius

end SmallSimpleAdjusterCandidate

end Erdos63
