/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos63.SourceLemma37
import ErdosProblems.Erdos63.Claim46Aux
import ErdosProblems.Erdos63.Claim43Final

/-!
# The source-specific robust simple-adjuster assembly

This file assembles Liu--Montgomery Claims 4.5 and 4.6 and the final
two-ended application of Lemma 3.7 using the source-paper specializations in
`SourceLemma37`.  In particular, every slow-growth loss uses the radius of
the candidate being grown, and the small sample size in the supplied bounds
is the literal square of that radius.

The hypotheses left in the main theorem are the explicit numerical
inequalities needed by the three source scales, the auxiliary expansion, and
the final Lemma 3.4 connector.
-/

open Finset Set SimpleGraph
open scoped BigOperators SimpleGraph

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

variable {V : Type u}

namespace SmallSimpleAdjusterCandidate

/-- Up to the separation radius, eligibility makes the `G-L` ball around a
candidate's ends avoid the protected set. -/
theorem source_candidate_highDegree_core_ball_disjoint_protected
    [Fintype V] {G : SimpleGraph V}
    {deleted highDegree protectedSet : Finset V}
    {separation minRadius maxRadius radius : ℕ}
    (A : SmallSimpleAdjusterCandidate G minRadius maxRadius)
    (hA : A.Eligible deleted highDegree protectedSet separation)
    (hradius : radius ≤ separation) :
    Disjoint
      (ballAvoidingFrom G
        (((highDegree ∪ A.adjuster.core : Finset V) : Set V)) A.ends radius)
      protectedSet := by
  rw [Finset.disjoint_left]
  intro z hzBall hzProtected
  by_cases hzHigh : z ∈ highDegree
  · exact ballAvoidingFrom_avoids_forbidden G
      (((highDegree ∪ A.adjuster.core : Finset V) : Set V))
      A.ends radius
      (fun a ha haForbidden ↦ by
        change a ∈ highDegree ∪ A.adjuster.core at haForbidden
        rw [Finset.mem_union] at haForbidden
        rcases haForbidden with haHigh | haCore
        · exact (Finset.disjoint_left.1 hA.2.1 ha haHigh).elim
        · exact (Finset.disjoint_left.1
            (A.ends_disjoint_deleted_union_core hA) ha
            (Finset.mem_union_right _ haCore)).elim)
      z hzBall (by
        change z ∈ highDegree ∪ A.adjuster.core
        exact Finset.mem_union_left _ hzHigh)
  · apply hA.2.2
    obtain ⟨a, ha, p, hp, hplen⟩ :=
      (mem_ballAvoidingFrom G
        (((highDegree ∪ A.adjuster.core : Finset V) : Set V))
        A.ends radius z).1 hzBall
    have hpAvoid : p.Avoids (highDegree : Set V) ∅ := by
      intro w hw hwHigh
      have hwa : w = a := by
        have hwForbidden :
            w ∈ ((highDegree ∪ A.adjuster.core : Finset V) : Set V) := by
          change w ∈ highDegree ∪ A.adjuster.core
          exact Finset.mem_union_left _ (by simpa using hwHigh)
        simpa using hp.2 w hw hwForbidden
      exact (Finset.disjoint_left.1 hA.2.1 ha
        (by simpa [hwa] using hwHigh)).elim
    exact ⟨a, ha, z, Finset.mem_sdiff.2 ⟨hzProtected, hzHigh⟩,
      p, hp.1, hpAvoid, hplen.trans hradius⟩

/-- The complete source-specific graph-theoretic assembly after Claim 4.4.

Starting with the `4 * floor(N^(1/8))` conflict-free candidates supplied by
Claim 4.4, Claim 4.5 leaves twice the source index.  The static Claim 4.6
workspace then produces the auxiliary expansion, Claim 4.6 leaves exactly
the source index, and the final source two-ended Lemma 3.7 application gives
an actual ball of order `10 * m^2 * D`.  A final avoiding connector to the
auxiliary expansion contradicts the retained non-reachability certificate.

The three neighbor-budget assumptions are candidate-local; no global
`maxRadius` loss is used by any Lemma 3.7 application. -/
theorem false_of_source_claim45_claim46_and_final
    [Fintype V] (G : SimpleGraph V)
    {deleted highDegree protectedSet : Finset V}
    {separation highRadius targetRadius ballRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
          ¬ Conflict A.1 B.1 highDegree separation))
    (d targetOrder totalRadius Delta deletedCap degreeInto
      maxSlow45 maxSlow46 m maxSlowFinal finalConnectorQ
      finalConnectorRadius workspaceCap : ℕ)
    (hfour : 4 * SourceLemma35Numerics.indexCard (Fintype.card V) ≤ S.card)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (bounds45 : LM37SourceReachBounds (Fintype.card V) d deletedCap 2
      highRadius targetOrder degreeInto maxSlow45)
    (bounds46 : LM37SourceReachBounds (Fintype.card V) d deletedCap 2
      ballRadius targetOrder degreeInto maxSlow46)
    (boundsFinal : LM37SourceFinalTwoEndBounds (Fintype.card V) d
      deletedCap 0 ballRadius m targetOrder degreeInto maxSlowFinal)
    (hdeleted : deleted.card ≤ deletedCap)
    (hHighDegree : ∀ v ∈ highDegree, Delta ≤ G.degree v)
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (hnoAdjuster : ¬ ∃ A : Adjuster G targetOrder totalRadius 1,
      Disjoint deleted A.verts)
    (h45radius : highRadius + highRadius ≤ separation)
    (h46radius : ballRadius + ballRadius ≤ separation)
    (hballHigh : ballRadius ≤ highRadius)
    (hprotected : deleted ∪ manyNeighborsInto G deleted degreeInto ⊆
      protectedSet)
    (h45start : bounds45.growth 0 < minRadius ^ 2)
    (h45startOne : bounds45.growth 1 < lm37SourceMinSize d)
    (h45retained : ∀ i :
      {A // A ∈ reachingEligibleSubfamily S (highDegree \ deleted)
        highRadius},
      lm37SourceMinSize d ≤
        d - degreeInto - (11 * i.1.1.radius + 1) - 2)
    (h45neighbor : ∀
      (i : {A // A ∈ reachingEligibleSubfamily S (highDegree \ deleted)
        highRadius}) (ell s : ℕ),
      0 < ell → ell ≤ highRadius → bounds45.growth (ell - 1) < s →
      bounds45.stepLoss ell + (11 * i.1.1.radius + 1) + 2 * ell ≤
        bounds45.neighborBudget s)
    (h45largeBudgetSum : ∀
      (J : Finset
        {A // A ∈ reachingEligibleSubfamily S (highDegree \ deleted)
          highRadius})
      (f : {A // A ∈ reachingEligibleSubfamily S (highDegree \ deleted)
        highRadius} → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlow45) →
      ∑ i ∈ J, bounds45.neighborBudget (f i) ≤
        bounds45.largeBudget (∑ i ∈ J, f i))
    (hTargetPos : 0 < targetOrder)
    (hRightBudget : targetOrder +
      (deletedCap + 10 * maxRadius + (maxRadius + 1) +
        (highRadius + 1)) ≤ Delta)
    (hLeftBudget : targetOrder +
      (deletedCap + 10 * maxRadius + targetOrder) ≤ Delta)
    (h45TotalRadius : maxRadius + highRadius + 1 ≤ totalRadius)
    (hn : 32 ≤ Fintype.card V)
    (hd : 1 ≤ d)
    (hdn : d ≤ Fintype.card V)
    (hLowDegree : ∀ v ∉ highDegree, G.degree v ≤ Delta)
    (hworkspaceCap : deletedCap +
      2 * SourceLemma35Numerics.indexCard (Fintype.card V) *
        ((2 * maxRadius ^ 2 + 10 * maxRadius) +
          2 * maxRadius ^ 2 * (Delta + 1) ^ ballRadius) ≤ workspaceCap)
    (hworkspaceGain : workspaceCap ≤
      lm43GrowthGain (Fintype.card V) (lm43K (Fintype.card V)))
    (hworkspaceRoom : workspaceCap + lm43K (Fintype.card V) ≤
      Fintype.card V)
    (hTargetK : targetOrder ≤ lm43K (Fintype.card V))
    (hdenominator : 6 * lm43GrowthDenominator (Fintype.card V) ≤
      lm43K (Fintype.card V))
    (h46start : bounds46.growth 0 < minRadius ^ 2)
    (h46startOne : bounds46.growth 1 < lm37SourceMinSize d)
    (h46retained : ∀
      (T : Finset
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation})
      (targetSet : Finset V)
      (i : {A // A ∈ reachingEligibleSubfamily T targetSet targetRadius}),
      lm37SourceMinSize d ≤
        d - degreeInto - (11 * i.1.1.radius + 1) - 2)
    (h46neighbor : ∀
      (T : Finset
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation})
      (targetSet : Finset V)
      (i : {A // A ∈ reachingEligibleSubfamily T targetSet targetRadius})
      (ell s : ℕ), 0 < ell → ell ≤ ballRadius →
      bounds46.growth (ell - 1) < s →
      bounds46.stepLoss ell + (11 * i.1.1.radius + 1) + 2 * ell ≤
        bounds46.neighborBudget s)
    (h46largeBudgetSum : ∀
      (T : Finset
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation})
      (targetSet : Finset V)
      (J : Finset {A // A ∈
        reachingEligibleSubfamily T targetSet targetRadius})
      (f : {A // A ∈ reachingEligibleSubfamily T targetSet targetRadius} → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlow46) →
      ∑ i ∈ J, bounds46.neighborBudget (f i) ≤
        bounds46.largeBudget (∑ i ∈ J, f i))
    (hLeftRadius : maxRadius + targetRadius +
      2 * lm43FarRadius (Fintype.card V) ≤ totalRadius)
    (hRightRadius : maxRadius + ballRadius ≤ totalRadius)
    (hFinalStart : boundsFinal.growth 0 < 2 * minRadius ^ 2)
    (hFinalStartOne : boundsFinal.growth 1 < lm37SourceMinSize d)
    (hFinalRetained : ∀
      (Q : Finset
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation})
      (i : Q), lm37SourceMinSize d ≤
        d - degreeInto - 10 * i.1.1.radius)
    (hFinalNeighbor : ∀
      (Q : Finset
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation})
      (i : Q) (ell s : ℕ), 0 < ell → ell ≤ ballRadius →
      boundsFinal.growth (ell - 1) < s →
      boundsFinal.stepLoss ell + 10 * i.1.1.radius ≤
        boundsFinal.neighborBudget s)
    (hFinalLargeBudgetSum : ∀
      (Q : Finset
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation})
      (J : Finset Q) (f : Q → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlowFinal) →
      ∑ i ∈ J, boundsFinal.neighborBudget (f i) ≤
        boundsFinal.largeBudget (∑ i ∈ J, f i))
    (hBallLower : ((1 / 64) * (d : ℝ)) / 2 ≤
      ((10 * m ^ 2 * targetOrder : ℕ) : ℝ))
    (hTargetLower : ((1 / 64) * (d : ℝ)) / 2 ≤ (targetOrder : ℝ))
    (hBallRate : ∀
      (A : {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation})
      (s : ℕ), 10 * m ^ 2 * targetOrder ≤ s →
      s ≤ Fintype.card V / 2 →
      (((deleted ∪ A.1.adjuster.core).card + finalConnectorQ : ℕ) : ℝ) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ))
    (hTargetRate : ∀
      (A : {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation})
      (s : ℕ), targetOrder ≤ s → s ≤ Fintype.card V / 2 →
      (((deleted ∪ A.1.adjuster.core).card + finalConnectorQ : ℕ) : ℝ) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ))
    (hBallSteps : Fintype.card V / 2 + 1 ≤
      10 * m ^ 2 * targetOrder + finalConnectorRadius * finalConnectorQ)
    (hTargetSteps : Fintype.card V / 2 + 1 ≤
      targetOrder + finalConnectorRadius * finalConnectorQ)
    (hFinalRadius : ballRadius + 2 * finalConnectorRadius ≤ targetRadius) :
    False := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  let : DecidableRel G.Adj := originalDecAdj
  have hbad45 :=
    card_reachingEligibleSubfamily_lt_of_no_targetAdjuster_source
      G hpair d targetOrder totalRadius Delta deletedCap degreeInto maxSlow45
        bounds45 hexp hdeleted (by exact Finset.Subset.rfl) hHighDegree hdegree
        hnoAdjuster h45radius hprotected h45start h45startOne h45retained
        h45neighbor h45largeBudgetSum hTargetPos hRightBudget hLeftBudget
        h45TotalRadius
  obtain ⟨T, hTS, hTcard, hTnoHigh⟩ :=
    exists_two_mul_nonreaching_subfamily (highRadius := highRadius)
      (R := SourceLemma35Numerics.indexCard (Fintype.card V))
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
      _ ≤ deletedCap +
          2 * SourceLemma35Numerics.indexCard (Fintype.card V) *
            ((2 * maxRadius ^ 2 + 10 * maxRadius) +
              2 * maxRadius ^ 2 * (Delta + 1) ^ ballRadius) := by
        rw [hTcard]
        exact Nat.add_le_add_right hdeleted _
      _ ≤ workspaceCap := hworkspaceCap
  obtain ⟨center, Z, hZW, hZfresh⟩ := exists_claim46_auxiliary_expansion
    G d targetOrder targetRadius ballRadius highRadius hexp T hTnoHigh
      hballHigh hn hd hdn (hTworkspace.trans hworkspaceGain)
      ((Nat.add_le_add_right hTworkspace _).trans hworkspaceRoom)
      hTargetPos hTargetK hdenominator
  have hbad46 :=
    card_reachingEligibleSubfamily_lt_of_no_targetAdjuster_expansion_source
      G hpairT d targetOrder totalRadius deletedCap degreeInto
        (lm43FarRadius (Fintype.card V)) maxSlow46 bounds46 hexp hdeleted
        hdegree hnoAdjuster hTnoHigh hballHigh Z
        (by exact Finset.Subset.rfl)
        (hZfresh Z.verts Finset.Subset.rfl) h46radius hprotected h46start
        h46startOne (h46retained T Z.verts) (h46neighbor T Z.verts)
        (h46largeBudgetSum T Z.verts) hTargetPos hLeftRadius hRightRadius
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
    let highBall : Finset V := ballAvoidingFrom G
      (((highDegree ∪ i.1.1.adjuster.core : Finset V) : Set V))
      i.1.1.ends ballRadius
    have hactualHigh : actual ⊆ highBall := by
      simpa only [actual, highBall] using
        source_candidate_ball_subset_highDegree_ball_of_no_high
          G i.1.1 i.1.2 (hQnoHigh i.1 i.2) hballHigh
    have hhighProtected : Disjoint highBall protectedSet := by
      apply source_candidate_highDegree_core_ball_disjoint_protected
        i.1.1 i.1.2
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
    have hdegreeInto := neighborsInto_le_of_disjoint_manyNeighborsInto
      G deleted actual degreeInto hactualDeleted hactualExceptional v
        (by simpa only [actual] using hv)
    have hinter : G.neighborFinset v ∩ deleted =
        deleted.filter fun w ↦ G.Adj v w := by
      ext w
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        Finset.mem_filter]
      tauto
    rw [hinter]
    exact hdegreeInto
  obtain ⟨i, hiLarge⟩ :=
    exists_large_twoEnd_ball_of_LM37SourceFinalBounds
      G hpairQ d deletedCap degreeInto m targetOrder maxSlowFinal boundsFinal
        hexp hQcard hdeleted hQnoHigh hballHigh h46radius hdegree
        hFinalStart hFinalStartOne (hFinalRetained Q) (hFinalNeighbor Q)
        hFinalDegree (hFinalLargeBudgetSum Q)
  let W : Finset V := deleted ∪ i.1.1.adjuster.core
  let largeBall : Finset V := ballAvoidingFrom G (W : Set V)
    i.1.1.ends ballRadius
  have hiLarge' : 10 * m ^ 2 * targetOrder ≤ largeBall.card := by
    simpa [largeBall, W] using hiLarge
  have hEndsW : Disjoint i.1.1.ends W := by
    simpa [W] using i.1.1.ends_disjoint_deleted_union_core i.1.2
  have hBallW : Disjoint largeBall W := by
    exact disjoint_ballAvoidingFrom_forbidden G i.1.1.ends W ballRadius hEndsW
  obtain ⟨a, haBall, b, hbTarget, q, hq, hqLength⟩ :=
    exists_avoiding_path_between_of_lmExpander_growth
      G (1 / 1024) ((1 / 64) * (d : ℝ)) hexp W largeBall Z.verts
        finalConnectorQ finalConnectorRadius
        (hBallLower.trans (by exact_mod_cast hiLarge'))
        (by simpa only [VertexExpansion.card_verts] using hTargetLower)
        (fun s hs hsN ↦ hBallRate i.1 s (hiLarge'.trans hs) hsN)
        (fun s hs hsN ↦ hTargetRate i.1 s
          (by simpa only [VertexExpansion.card_verts] using hs) hsN)
        (hBallSteps.trans (Nat.add_le_add_right hiLarge'
          (finalConnectorRadius * finalConnectorQ)))
        (by simpa only [VertexExpansion.card_verts] using hTargetSteps)
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
    exact (Finset.disjoint_left.1 (hZDisjoint i) hbTarget hbW).elim
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
      _ ≤ ballRadius + 2 * finalConnectorRadius :=
        Nat.add_le_add hpLength hqLength
      _ ≤ targetRadius := hFinalRadius
  exact (hQnoZ i.1 i.2) ⟨x, hxEnds, b, hbTarget, route,
    hroutePath, hrouteAvoid, hrouteLength⟩

/-- Once the conditional source growth theorem has supplied the final large
two-ended ball, the minimum-degree bootstrap connector gives the last
contradiction.  Neither endpoint set is required to dominate `kappa / 2`:
the two seed disjunctions are exactly the direct-or-radius-one alternatives
of Lemma 3.4. -/
theorem false_of_large_twoEnd_ball_and_nonreaching_bootstrap
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation targetRadius ballRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : S)
    (ballTarget degreeScale connectorStart connectorWorkspace
      connectorRadius : ℕ)
    (hiLarge : ballTarget ≤ (ballAvoidingFrom G
      (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
      i.1.1.ends ballRadius).card)
    (hdegree : ∀ v : V, degreeScale ≤ G.degree v)
    (hnoTarget : ∀ A ∈ S, ¬ A.1.ReachesAvoidingOwnCore deleted
      targetSet targetRadius)
    (hTargetNonempty : targetSet.Nonempty)
    (hTargetDisjoint : Disjoint targetSet
      (deleted ∪ i.1.1.adjuster.core))
    (hConnectorWorkspace :
      (deleted ∪ i.1.1.adjuster.core).card ≤ connectorWorkspace)
    (hBallSeed : connectorStart ≤ ballTarget ∨
      connectorStart + connectorWorkspace ≤ degreeScale)
    (hTargetSeed : connectorStart ≤ targetSet.card ∨
      connectorStart + connectorWorkspace ≤ degreeScale)
    (growth : LM42GrowthSchedule (Fintype.card V) connectorStart
      connectorWorkspace connectorRadius epsilon kappa)
    (hTotalRadius : ballRadius + 2 * (connectorRadius + 1) ≤ targetRadius) :
    False := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  let : DecidableRel G.Adj := originalDecAdj
  let W : Finset V := deleted ∪ i.1.1.adjuster.core
  let largeBall : Finset V := ballAvoidingFrom G (W : Set V)
    i.1.1.ends ballRadius
  have hiLarge' : ballTarget ≤ largeBall.card := by
    simpa only [largeBall, W] using hiLarge
  have hEndsW : Disjoint i.1.1.ends W := by
    simpa only [W] using i.1.1.ends_disjoint_deleted_union_core i.1.2
  have hBallW : Disjoint largeBall W :=
    disjoint_ballAvoidingFrom_forbidden G i.1.1.ends W ballRadius hEndsW
  have hBallNonempty : largeBall.Nonempty := by
    refine ⟨i.1.1.adjuster.leftRoot, ?_⟩
    apply subset_ballAvoidingFrom G (W : Set V) i.1.1.ends ballRadius
    exact i.1.1.leftRoot_mem_ends
  have hBallSeed' : connectorStart ≤ largeBall.card ∨
      connectorStart + connectorWorkspace ≤ degreeScale := by
    rcases hBallSeed with hdirect | hbootstrap
    · exact Or.inl (hdirect.trans hiLarge')
    · exact Or.inr hbootstrap
  obtain ⟨a, haBall, b, hbTarget, q, hqPath, hqAvoid, hqLength⟩ :=
    exists_short_set_connector_ge G epsilon kappa hexp degreeScale hdegree
      W largeBall targetSet connectorStart connectorWorkspace connectorRadius
      (by simpa only [W] using hConnectorWorkspace) hBallNonempty
      hTargetNonempty hBallSeed' hTargetSeed hBallW
      (by simpa only [W] using hTargetDisjoint)
      (growth.toBallGrowthSchedule G rfl)
  obtain ⟨x, hxEnds, p, hp, hpLength⟩ :=
    (mem_ballAvoidingFrom G (W : Set V) i.1.1.ends ballRadius a).1 haBall
  have hpAvoid : p.Avoids (W : Set V) ∅ := by
    intro z hz hzW
    have hzx := hp.2 z hz hzW
    have hzEq : z = x := by simpa using hzx
    exact (Finset.disjoint_left.1 hEndsW hxEnds (hzEq ▸ hzW)).elim
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
      _ ≤ ballRadius + 2 * (connectorRadius + 1) :=
        Nat.add_le_add hpLength hqLength
      _ ≤ targetRadius := hTotalRadius
  exact (hnoTarget i.1 i.2) ⟨x, hxEnds, b, hbTarget, route,
    hroutePath, hrouteAvoid, hrouteLength⟩

/-- Conditional, minimum-degree-bootstrap assembly of Claims 4.5 and 4.6
and the final two-ended source application.  A source growth certificate is
only requested in the low-degree branch in which the desired order exceeds
the radius-one bootstrap lower bound. -/
theorem false_of_source_claim45_claim46_and_final_conditional_bootstrap
    [Fintype V] (G : SimpleGraph V)
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
      maxSlow45 maxSlow46 m maxSlowFinal workspaceCap connectorStart
      connectorWorkspace connectorRadius : ℕ)
    (hfour : 4 * SourceLemma35Numerics.indexCard (Fintype.card V) ≤ S.card)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (bounds45 : lm37SourceMinSize d < targetOrder →
      LM37SourceReachBounds (Fintype.card V) d deletedCap 2
        highRadius targetOrder degreeInto maxSlow45)
    (bounds46 : lm37SourceMinSize d < auxiliaryOrder →
      LM37SourceReachBounds (Fintype.card V) d deletedCap 2
        ballRadius auxiliaryOrder degreeInto maxSlow46)
    (boundsFinal : lm37SourceMinSize d < 10 * m ^ 2 * targetOrder →
      LM37SourceFinalTwoEndBounds (Fintype.card V) d deletedCap 0
        ballRadius m targetOrder degreeInto maxSlowFinal)
    (hdeleted : deleted.card ≤ deletedCap)
    (hindexPos : 0 < SourceLemma35Numerics.indexCard (Fintype.card V))
    (hHighDegree : ∀ v ∈ highDegree, Delta ≤ G.degree v)
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (hnoAdjuster : ¬ ∃ A : Adjuster G targetOrder totalRadius 1,
      Disjoint deleted A.verts)
    (h45radius : highRadius + highRadius ≤ separation)
    (h46radius : ballRadius + ballRadius ≤ separation)
    (hballHigh : ballRadius ≤ highRadius)
    (hHighRadiusPos : 0 < highRadius)
    (hBallRadiusPos : 0 < ballRadius)
    (hprotected : deleted ∪ manyNeighborsInto G deleted degreeInto ⊆
      protectedSet)
    (h45start : ∀ hM : lm37SourceMinSize d < targetOrder,
      (bounds45 hM).growth 0 < minRadius ^ 2)
    (h45startOne : ∀ hM : lm37SourceMinSize d < targetOrder,
      (bounds45 hM).growth 1 < lm37SourceMinSize d)
    (h45retained : ∀ i :
      {A // A ∈ reachingEligibleSubfamily S (highDegree \ deleted)
        highRadius},
      lm37SourceMinSize d ≤ i.1.1.radius ^ 2 ∨
        lm37SourceMinSize d ≤
          d - degreeInto - (11 * i.1.1.radius + 1) - 2)
    (h45neighbor : ∀ hM : lm37SourceMinSize d < targetOrder,
      ∀ (i : {A // A ∈ reachingEligibleSubfamily S
        (highDegree \ deleted) highRadius}) (ell s : ℕ),
      0 < ell → ell ≤ highRadius → (bounds45 hM).growth (ell - 1) < s →
      i.1.1.radius ^ 2 ≤ s →
      (bounds45 hM).stepLoss ell + (11 * i.1.1.radius + 1) + 2 * ell ≤
        (bounds45 hM).neighborBudget s)
    (h45largeBudgetSum : ∀ hM : lm37SourceMinSize d < targetOrder,
      ∀ (J : Finset {A // A ∈ reachingEligibleSubfamily S
        (highDegree \ deleted) highRadius})
      (f : {A // A ∈ reachingEligibleSubfamily S
        (highDegree \ deleted) highRadius} → ℕ),
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
    (hn : 32 ≤ Fintype.card V)
    (hd : 1 ≤ d)
    (hdn : d ≤ Fintype.card V)
    (hLowDegree : ∀ v ∉ highDegree, G.degree v ≤ Delta)
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
    (h46retained : ∀
      (T : Finset
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation})
      (targetSet : Finset V)
      (i : {A // A ∈ reachingEligibleSubfamily T targetSet targetRadius}),
      lm37SourceMinSize d ≤ i.1.1.radius ^ 2 ∨
        lm37SourceMinSize d ≤
          d - degreeInto - (11 * i.1.1.radius + 1) - 2)
    (h46neighbor : ∀ hM : lm37SourceMinSize d < auxiliaryOrder,
      ∀ (T : Finset
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation})
      (targetSet : Finset V)
      (i : {A // A ∈ reachingEligibleSubfamily T targetSet targetRadius})
      (ell s : ℕ), 0 < ell → ell ≤ ballRadius →
      (bounds46 hM).growth (ell - 1) < s →
      i.1.1.radius ^ 2 ≤ s →
      (bounds46 hM).stepLoss ell + (11 * i.1.1.radius + 1) + 2 * ell ≤
        (bounds46 hM).neighborBudget s)
    (h46largeBudgetSum : ∀ hM : lm37SourceMinSize d < auxiliaryOrder,
      ∀ (T : Finset
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation})
      (targetSet : Finset V)
      (J : Finset {A // A ∈
        reachingEligibleSubfamily T targetSet targetRadius})
      (f : {A // A ∈ reachingEligibleSubfamily T targetSet targetRadius} → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlow46) →
      ∑ i ∈ J, (bounds46 hM).neighborBudget (f i) ≤
        (bounds46 hM).largeBudget (∑ i ∈ J, f i))
    (hLeftRadius : maxRadius + targetRadius +
      2 * lm43FarRadius (Fintype.card V) ≤ totalRadius)
    (hRightRadius : maxRadius + ballRadius ≤ totalRadius)
    (hFinalStart : ∀ hM : lm37SourceMinSize d < 10 * m ^ 2 * targetOrder,
      (boundsFinal hM).growth 0 < 2 * minRadius ^ 2)
    (hFinalStartOne : ∀ hM : lm37SourceMinSize d < 10 * m ^ 2 * targetOrder,
      (boundsFinal hM).growth 1 < lm37SourceMinSize d)
    (hFinalRetained : ∀
      (Q : Finset
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation})
      (i : Q), lm37SourceMinSize d ≤ 2 * i.1.1.radius ^ 2 ∨
        lm37SourceMinSize d ≤ d - degreeInto - 10 * i.1.1.radius)
    (hFinalNeighbor : ∀ hM :
      lm37SourceMinSize d < 10 * m ^ 2 * targetOrder,
      ∀ (Q : Finset
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation})
      (i : Q) (ell s : ℕ), 0 < ell → ell ≤ ballRadius →
      (boundsFinal hM).growth (ell - 1) < s →
      i.1.1.radius ^ 2 ≤ s →
      (boundsFinal hM).stepLoss ell + 10 * i.1.1.radius ≤
        (boundsFinal hM).neighborBudget s)
    (hFinalLargeBudgetSum : ∀ hM :
      lm37SourceMinSize d < 10 * m ^ 2 * targetOrder,
      ∀ (Q : Finset
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation})
      (J : Finset Q) (f : Q → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlowFinal) →
      ∑ i ∈ J, (boundsFinal hM).neighborBudget (f i) ≤
        (boundsFinal hM).largeBudget (∑ i ∈ J, f i))
    (hConnectorWorkspace : deletedCap + 10 * maxRadius ≤
      connectorWorkspace)
    (hBallSeed : connectorStart ≤ 10 * m ^ 2 * targetOrder ∨
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
  let : DecidableRel G.Adj := originalDecAdj
  have hbad45 :=
    card_reachingEligibleSubfamily_lt_of_no_targetAdjuster_source_conditional
      G hpair d targetOrder totalRadius Delta deletedCap degreeInto maxSlow45
        bounds45 hexp hdeleted hindexPos hHighRadiusPos
        (by exact Finset.Subset.rfl) hHighDegree hdegree hnoAdjuster h45radius
        hprotected h45start h45startOne h45retained h45neighbor
        h45largeBudgetSum hTargetPos hRightBudget hLeftBudget h45TotalRadius
  obtain ⟨T, hTS, hTcard, hTnoHigh⟩ :=
    exists_two_mul_nonreaching_subfamily (highRadius := highRadius)
      (R := SourceLemma35Numerics.indexCard (Fintype.card V))
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
      _ ≤ deletedCap +
          2 * SourceLemma35Numerics.indexCard (Fintype.card V) *
            ((2 * maxRadius ^ 2 + 10 * maxRadius) +
              2 * maxRadius ^ 2 * (Delta + 1) ^ ballRadius) := by
        rw [hTcard]
        exact Nat.add_le_add_right hdeleted _
      _ ≤ workspaceCap := hworkspaceCap
  obtain ⟨center, Z, hZW, hZfresh⟩ := exists_claim46_auxiliary_expansion
    G d auxiliaryOrder targetRadius ballRadius highRadius hexp T hTnoHigh
      hballHigh hn hd hdn (hTworkspace.trans hworkspaceGain)
      ((Nat.add_le_add_right hTworkspace _).trans hworkspaceRoom)
      hAuxiliaryPos hAuxiliaryK hdenominator
  have hnoAuxiliary :
      ¬ ∃ A : Adjuster G auxiliaryOrder totalRadius 1,
        Disjoint deleted A.verts :=
    no_auxiliaryAdjuster_of_no_targetAdjuster hnoAdjuster hTargetPos
      hTargetOrderLeAuxiliary
  have hbad46 :=
    card_reachingEligibleSubfamily_lt_of_no_targetAdjuster_expansion_source_conditional
      G hpairT d auxiliaryOrder totalRadius deletedCap degreeInto
        (lm43FarRadius (Fintype.card V)) maxSlow46 bounds46 hexp hdeleted
        hindexPos hBallRadiusPos hdegree hnoAuxiliary hTnoHigh hballHigh Z
        (by exact Finset.Subset.rfl)
        (hZfresh Z.verts Finset.Subset.rfl) h46radius hprotected h46start
        h46startOne (h46retained T Z.verts)
        (fun hM ↦ h46neighbor hM T Z.verts)
        (fun hM ↦ h46largeBudgetSum hM T Z.verts)
        hAuxiliaryPos hLeftRadius hRightRadius
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
    let highBall : Finset V := ballAvoidingFrom G
      (((highDegree ∪ i.1.1.adjuster.core : Finset V) : Set V))
      i.1.1.ends ballRadius
    have hactualHigh : actual ⊆ highBall := by
      simpa only [actual, highBall] using
        source_candidate_ball_subset_highDegree_ball_of_no_high
          G i.1.1 i.1.2 (hQnoHigh i.1 i.2) hballHigh
    have hhighProtected : Disjoint highBall protectedSet := by
      apply source_candidate_highDegree_core_ball_disjoint_protected
        i.1.1 i.1.2
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
    have hdegreeInto := neighborsInto_le_of_disjoint_manyNeighborsInto
      G deleted actual degreeInto hactualDeleted hactualExceptional v
        (by simpa only [actual] using hv)
    have hinter : G.neighborFinset v ∩ deleted =
        deleted.filter fun w ↦ G.Adj v w := by
      ext w
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        Finset.mem_filter]
      tauto
    rw [hinter]
    exact hdegreeInto
  obtain ⟨i, hiLarge⟩ :=
    exists_large_twoEnd_ball_of_conditional_LM37SourceFinalBounds
      G hpairQ d deletedCap degreeInto m targetOrder maxSlowFinal boundsFinal
        hexp hindexPos hQcard hdeleted hQnoHigh hballHigh hBallRadiusPos
        h46radius hdegree hFinalStart hFinalStartOne (hFinalRetained Q)
        (fun hM ↦ hFinalNeighbor hM Q) hFinalDegree
        (fun hM ↦ hFinalLargeBudgetSum hM Q)
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
      (10 * m ^ 2 * targetOrder) d connectorStart connectorWorkspace
      connectorRadius hiLarge hdegree hQnoZ hTargetNonempty (hZDisjoint i)
      hiWorkspace hBallSeed
      (by simpa only [VertexExpansion.card_verts] using hTargetSeed)
      growth hFinalRadius

end SmallSimpleAdjusterCandidate

end Erdos63
