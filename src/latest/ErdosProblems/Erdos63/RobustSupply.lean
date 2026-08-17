/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos63.Claim44
import ErdosProblems.Erdos63.RobustNumerics
import ErdosProblems.Erdos63.SourceRobustAdjuster

/-!
# The finite robust simple-adjuster supply

This file joins the canonical graph-free parameters to Claim 4.4 and the
conditional source-specific post-Claim-4.4 assembly.  Graph hypotheses occur
only in the finite theorem; the eventual wrapper at the end is parameterized
by one graph-free numerical package.
-/

open Finset Set SimpleGraph
open scoped BigOperators SimpleGraph

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

variable {V : Type u}

namespace SmallSimpleAdjusterCandidate

/-- Family-independent Claim 4.6 workspace bound. -/
def lm43Claim46WorkspaceCap
    (deletedCap R maxRadius Delta ballRadius : ℕ) : ℕ :=
  deletedCap + 2 * R *
    ((2 * maxRadius ^ 2 + 10 * maxRadius) +
      2 * maxRadius ^ 2 * (Delta + 1) ^ ballRadius)

/-- Proposition 3.16 bounds the protected set used by Claim 4.4. -/
theorem card_canonicalProtectedSet_le
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (deleted : Finset V) (N d : ℕ)
    (hfree : ¬ oneSubdivisionClique (d / 2) ⊑ G)
    (hdeleted : deleted.card ≤ lm43DeletionCap N d) :
    (deleted ∪ manyNeighborsInto G deleted (lm43DegreeInto N d)).card ≤
      lm43ProtectedCap N d := by
  have hdeletedTen : deleted.card ≤ 10 * lm43TargetOrder N d :=
    hdeleted.trans (lm43DeletionCap_le_ten_target N d)
  have hexceptional :
      (manyNeighborsInto G deleted (lm43DegreeInto N d)).card ≤
        100 * lm43TargetOrder N d ^ 2 := by
    simpa only [lm43DegreeInto] using
      card_manyNeighborsInto_le_hundred_mul_sq G deleted (d / 2)
        (lm43TargetOrder N d) hfree hdeletedTen
  calc
    (deleted ∪ manyNeighborsInto G deleted (lm43DegreeInto N d)).card ≤
        deleted.card +
          (manyNeighborsInto G deleted (lm43DegreeInto N d)).card :=
      Finset.card_union_le _ _
    _ ≤ lm43DeletionCap N d + 100 * lm43TargetOrder N d ^ 2 :=
      Nat.add_le_add hdeleted hexceptional
    _ = lm43ProtectedCap N d := rfl

/-- The canonical Claim 4.4 family, with the exceptional set chosen exactly
as in Liu--Montgomery. -/
theorem exists_canonical_claim44_family
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (deleted : Finset V) (N d : ℕ)
    (numerics : LM43NumericalPackage N d)
    (hcard : Fintype.card V = N)
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (hfree : ¬ oneSubdivisionClique (d / 2) ⊑ G)
    (hdeleted : deleted.card ≤ lm43DeletionCap N d)
    (hnoAdjuster : ¬ ∃ A : Adjuster G (lm43TargetOrder N d)
        (lm43TotalRadius N d) 1, Disjoint deleted A.verts) :
    ∃ S : Finset
        {A : SmallSimpleAdjusterCandidate G (lm43MinRadius N d)
            (lm43MaxRadius N d) //
          A.Eligible deleted
            (highDegreeVertices G (lm43HighCutoff N d))
            (deleted ∪ manyNeighborsInto G deleted (lm43DegreeInto N d))
            (lm43Separation N d)},
      ((S : Set
        {A : SmallSimpleAdjusterCandidate G (lm43MinRadius N d)
            (lm43MaxRadius N d) //
          A.Eligible deleted
            (highDegreeVertices G (lm43HighCutoff N d))
            (deleted ∪ manyNeighborsInto G deleted (lm43DegreeInto N d))
            (lm43Separation N d)}).Pairwise fun A B ↦
          ¬ Conflict A.1 B.1
            (highDegreeVertices G (lm43HighCutoff N d))
            (lm43Separation N d)) ∧
      4 * lm43R N d ≤ S.card := by
  subst N
  obtain ⟨S, hpair, _hmax, hfour⟩ :=
    exists_maximal_eligible_family_card_ge_four_mul
      G deleted
        (deleted ∪ manyNeighborsInto G deleted
          (lm43DegreeInto (Fintype.card V) d))
      d (lm43TargetOrder (Fintype.card V) d)
        (lm43TotalRadius (Fintype.card V) d)
        (lm43HighCutoff (Fintype.card V) d)
        (lm43DeletionCap (Fintype.card V) d)
        (lm43ProtectedCap (Fintype.card V) d)
        (lm43Separation (Fintype.card V) d)
        (lm43MinRadius (Fintype.card V) d)
        (lm43MaxRadius (Fintype.card V) d)
        (lm43R (Fintype.card V) d)
        ((1 / 64) * (lm43CoreDegree (Fintype.card V) d : ℝ))
        numerics.claim44 hdegree hfree hdeleted
        (card_canonicalProtectedSet_le G deleted (Fintype.card V) d
          hfree hdeleted)
        hnoAdjuster
  exact ⟨S, hpair, hfour⟩

/-- The single graph-free pointwise package left by the finite robust
adjuster theorem.  The routed source records retain the provenance of the
three `LM37SourceBounds`, so their candidate-local route estimates and
finite-family aggregation laws are available without adding graph-dependent
or false uniform hypotheses. -/
structure LM43RobustSupplyNumericalPackage (N d : ℕ) : Type where
  routed : LM43RoutedSourceNumericalPackage N d
  claim44 : SmallSimpleAdjusterCandidate.LM44Scale N d
    (lm43TargetOrder N d) (lm43TotalRadius N d) (lm43HighCutoff N d)
    (lm43DeletionCap N d) (lm43ProtectedCap N d) (lm43Separation N d)
    (lm43MinRadius N d) (lm43MaxRadius N d) (lm43R N d)
    ((1 / 64) * (lm43CoreDegree N d : ℝ))
  card_large : 32 ≤ N
  degree_bootstrap : 2 ^ 20 ≤ d
  index_pos : 0 < lm43R N d
  target_pos : 0 < lm43TargetOrder N d
  maxRadius_pos : 0 < lm43MaxRadius N d
  highRadius_pos : 0 < lm43HighRadius N d
  ballRadius_pos : 0 < lm43BallRadius N d
  source_start : lm37FirstSlowGrowth 0 < lm43MinRadius N d ^ 2
  source_start_one : lm37FirstSlowGrowth 1 < lm37SourceMinSize d
  right_budget : lm43TargetOrder N d +
    (lm43DeletionCap N d + 10 * lm43MaxRadius N d +
      (lm43MaxRadius N d + 1) + (lm43HighRadius N d + 1)) ≤
        lm43HighCutoff N d
  left_budget : lm43TargetOrder N d +
    (lm43DeletionCap N d + 10 * lm43MaxRadius N d +
      lm43TargetOrder N d) ≤ lm43HighCutoff N d
  claim45_radius : lm43MaxRadius N d + lm43HighRadius N d + 1 ≤
    lm43TotalRadius N d
  claim46_workspace : lm43Claim46WorkspaceCap (lm43DeletionCap N d)
      (lm43R N d) (lm43MaxRadius N d) (lm43HighCutoff N d)
      (lm43BallRadius N d) ≤
    lm43GrowthGain N (lm43K N)
  claim46_room : lm43Claim46WorkspaceCap (lm43DeletionCap N d)
      (lm43R N d) (lm43MaxRadius N d) (lm43HighCutoff N d)
      (lm43BallRadius N d) + lm43K N ≤ N
  auxiliary_le_K : lm43BallTarget N d ≤ lm43K N
  denominator_le_K : 6 * lm43GrowthDenominator N ≤ lm43K N
  claim46_left_radius : lm43MaxRadius N d + lm43TargetRadius N d +
      2 * lm43FarRadius N ≤ lm43TotalRadius N d
  claim46_right_radius : lm43MaxRadius N d + lm43BallRadius N d ≤
    lm43TotalRadius N d
  finalConnector : LM43AdaptiveFinalConnectorCertificate N d
  output_radius : lm43TotalRadius N d ≤
    2 * Parameters.lmSimpleRadius (1 / 1024) N

/-- The source records used by the graph theorem, constructed from the
routed certificates while reusing exactly the Claim 4.4 field of the public
numerical package. -/
noncomputable def LM43RobustSupplyNumericalPackage.sourceNumerics
    {N d : ℕ} (p : LM43RobustSupplyNumericalPackage N d) :
    LM43NumericalPackage N d :=
  p.routed.toNumericalPackage p.claim44

/-- Fixed-graph Liu--Montgomery Lemma 4.3 at the canonical parameters. -/
theorem exists_canonical_robust_simpleAdjuster
    [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ}
    (p : LM43RobustSupplyNumericalPackage (Fintype.card V) d)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (hfree : ¬ oneSubdivisionClique (d / 2) ⊑ G)
    (deleted : Finset V)
    (hdeleted : deleted.card ≤ lm43DeletionCap (Fintype.card V) d) :
    ∃ A : Adjuster G (lm43TargetOrder (Fintype.card V) d)
        (lm43TotalRadius (Fintype.card V) d) 1,
      Disjoint deleted A.verts := by
  classical
  letI : DecidableRel G.Adj := fun _ _ ↦ Classical.propDecidable _
  have hdegree' : ∀ v : V, d ≤ G.degree v := by
    intro v
    convert hdegree v using 1
    unfold SimpleGraph.degree
    congr 1
    ext w
    simp
  let N := Fintype.card V
  let protectedSet : Finset V :=
    deleted ∪ manyNeighborsInto G deleted (lm43DegreeInto N d)
  let highDegree : Finset V := highDegreeVertices G (lm43HighCutoff N d)
  let sourceNumerics := p.sourceNumerics
  by_contra hno
  have hno' : ¬ ∃ A : Adjuster G (lm43TargetOrder N d)
      (lm43TotalRadius N d) 1, Disjoint deleted A.verts := by
    simpa only [N] using hno
  obtain ⟨S, hpair, hfour⟩ := exists_canonical_claim44_family
    G deleted N d sourceNumerics rfl hdegree' hfree hdeleted hno'
  have hdN : d ≤ N := by
    let v : V := Classical.choice inferInstance
    exact (hdegree' v).trans (Nat.le_of_lt (G.degree_lt_card_verts v))
  have hhigh : ∀ v ∈ highDegree,
      lm43HighCutoff N d ≤ G.degree v := by
    intro v hv
    exact (mem_highDegreeVertices G (lm43HighCutoff N d) v).1 hv
  have hlow : ∀ v ∉ highDegree,
      G.degree v ≤ lm43HighCutoff N d := by
    intro v hv
    exact degree_le_of_not_mem_highDegreeVertices G (lm43HighCutoff N d) hv
  have hprotected :
      deleted ∪ manyNeighborsInto G deleted (lm43DegreeInto N d) ⊆
        protectedSet := by
    exact Finset.Subset.rfl
  have htargetAux : lm43TargetOrder N d ≤ lm43BallTarget N d :=
    lm43TargetOrder_le_ballTarget N d p.maxRadius_pos
  apply false_of_source_claim45_claim46_and_final_conditional_bootstrap
    (bounds45 := sourceNumerics.claim45)
    (bounds46 := sourceNumerics.claim46)
    (boundsFinal := sourceNumerics.final)
    G hpair d (lm43TargetOrder N d) (lm43BallTarget N d)
      (lm43TotalRadius N d) (lm43HighCutoff N d)
      (lm43DeletionCap N d) (lm43DegreeInto N d)
      (lm43MaxSlowSize N d) (lm43MaxSlowSize N d)
      (lm43MaxRadius N d) (lm43MaxSlowSize N d)
      (lm43Claim46WorkspaceCap (lm43DeletionCap N d) (lm43R N d)
        (lm43MaxRadius N d) (lm43HighCutoff N d) (lm43BallRadius N d))
      (lm43FinalConnectorStart N d) (lm43FinalConnectorWorkspace N d)
      (lm43FinalConnectorRadius N d)
  · simpa [N, lm43R, lm43FamilyTarget] using hfour
  · simpa [N] using hexp
  · simpa [N] using hdeleted
  · simpa [lm43R, lm43FamilyTarget] using p.index_pos
  · exact hhigh
  · exact hdegree'
  · simpa [N] using hno'
  · exact lm43_high_radius_separated N d
  · exact lm43_ball_radius_separated N d
  · exact lm43_ball_radius_le_high_radius N d
  · exact p.highRadius_pos
  · exact p.ballRadius_pos
  · exact hprotected
  · intro hM
    simpa [sourceNumerics, LM43RobustSupplyNumericalPackage.sourceNumerics,
      LM43RoutedSourceNumericalPackage.toNumericalPackage,
      concreteLM37RoutedSourceBounds, concreteLM37SourceBounds] using
      p.source_start
  · intro hM
    simpa [sourceNumerics, LM43RobustSupplyNumericalPackage.sourceNumerics,
      LM43RoutedSourceNumericalPackage.toNumericalPackage,
      concreteLM37RoutedSourceBounds, concreteLM37SourceBounds] using
      p.source_start_one
  · intro i
    simpa only [lm43DegreeInto] using
      (lm37SourceMinSize_le_sq_or_reach_retained
        (candidateRadius := i.1.1.radius) p.degree_bootstrap)
  · intro hM i ell s hell hellRadius hslow hsquare
    simpa [sourceNumerics, LM43RobustSupplyNumericalPackage.sourceNumerics,
      LM43RoutedSourceNumericalPackage.toNumericalPackage,
      concreteLM37RoutedSourceBounds, concreteLM37SourceBounds] using
      lm37Source_reach_neighbor_of_radius_sq_le (p.routed.claim45 hM).geometry
        i.1.1.min_le hell hellRadius hslow hsquare
  · intro hM J f hf
    simpa [sourceNumerics, LM43RobustSupplyNumericalPackage.sourceNumerics,
      LM43RoutedSourceNumericalPackage.toNumericalPackage,
      concreteLM37RoutedSourceBounds] using
      concreteLM37SourceBounds_largeBudgetSum N d (lm43DeletionCap N d)
        (lm43R N d) 2 (lm43HighRadius N d) (lm43TargetOrder N d)
        (lm43DegreeInto N d) (lm43MaxSlowSize N d) (lm43R N d)
        (p.routed.claim45 hM).source J f (fun i hi ↦ (hf i hi).1)
  · exact p.target_pos
  · exact (p.target_pos.trans_le htargetAux)
  · exact htargetAux
  · exact p.right_budget
  · exact p.left_budget
  · exact p.claim45_radius
  · exact p.card_large
  · exact (by norm_num : 1 ≤ 2 ^ 20).trans p.degree_bootstrap
  · exact hdN
  · exact hlow
  · exact le_rfl
  · exact p.claim46_workspace
  · exact p.claim46_room
  · exact p.auxiliary_le_K
  · exact p.denominator_le_K
  · intro hM
    simpa [sourceNumerics, LM43RobustSupplyNumericalPackage.sourceNumerics,
      LM43RoutedSourceNumericalPackage.toNumericalPackage,
      concreteLM37RoutedSourceBounds, concreteLM37SourceBounds] using
      p.source_start
  · intro hM
    simpa [sourceNumerics, LM43RobustSupplyNumericalPackage.sourceNumerics,
      LM43RoutedSourceNumericalPackage.toNumericalPackage,
      concreteLM37RoutedSourceBounds, concreteLM37SourceBounds] using
      p.source_start_one
  · intro T targetSet i
    simpa only [lm43DegreeInto] using
      (lm37SourceMinSize_le_sq_or_reach_retained
        (candidateRadius := i.1.1.radius) p.degree_bootstrap)
  · intro hM T targetSet i ell s hell hellRadius hslow hsquare
    simpa [sourceNumerics, LM43RobustSupplyNumericalPackage.sourceNumerics,
      LM43RoutedSourceNumericalPackage.toNumericalPackage,
      concreteLM37RoutedSourceBounds, concreteLM37SourceBounds] using
      lm37Source_reach_neighbor_of_radius_sq_le (p.routed.claim46 hM).geometry
        i.1.1.min_le hell hellRadius hslow hsquare
  · intro hM T targetSet J f hf
    simpa [sourceNumerics, LM43RobustSupplyNumericalPackage.sourceNumerics,
      LM43RoutedSourceNumericalPackage.toNumericalPackage,
      concreteLM37RoutedSourceBounds] using
      concreteLM37SourceBounds_largeBudgetSum N d (lm43DeletionCap N d)
        (lm43R N d) 2 (lm43BallRadius N d) (lm43BallTarget N d)
        (lm43DegreeInto N d) (lm43MaxSlowSize N d) (lm43R N d)
        (p.routed.claim46 hM).source J f (fun i hi ↦ (hf i hi).1)
  · exact p.claim46_left_radius
  · exact p.claim46_right_radius
  · intro hM
    simpa [sourceNumerics, LM43RobustSupplyNumericalPackage.sourceNumerics,
      LM43RoutedSourceNumericalPackage.toNumericalPackage,
      concreteLM37RoutedSourceBounds, concreteLM37SourceBounds] using
      (Nat.lt_of_lt_of_le p.source_start (Nat.le_mul_of_pos_left _ (by omega)))
  · intro hM
    simpa [sourceNumerics, LM43RobustSupplyNumericalPackage.sourceNumerics,
      LM43RoutedSourceNumericalPackage.toNumericalPackage,
      concreteLM37RoutedSourceBounds, concreteLM37SourceBounds] using
      p.source_start_one
  · intro Q i
    simpa only [lm43DegreeInto] using
      (lm37SourceMinSize_le_two_sq_or_final_retained
        (candidateRadius := i.1.1.radius) p.degree_bootstrap)
  · intro hM Q i ell s hell hellRadius hslow hsquare
    simpa [sourceNumerics, LM43RobustSupplyNumericalPackage.sourceNumerics,
      LM43RoutedSourceNumericalPackage.toNumericalPackage,
      concreteLM37RoutedSourceBounds, concreteLM37SourceBounds] using
      lm37Source_final_neighbor_of_radius_sq_le (p.routed.final hM).geometry
        i.1.1.min_le hell hellRadius hslow hsquare
  · intro hM Q J f hf
    simpa [sourceNumerics, LM43RobustSupplyNumericalPackage.sourceNumerics,
      LM43RoutedSourceNumericalPackage.toNumericalPackage,
      concreteLM37RoutedSourceBounds] using
      concreteLM37SourceBounds_largeBudgetSum N d (lm43DeletionCap N d)
        (lm43R N d) 0 (lm43BallRadius N d) (lm43BallTarget N d)
        (lm43DegreeInto N d) (lm43MaxSlowSize N d) (lm43R N d)
        (p.routed.final hM).source J f (fun i hi ↦ (hf i hi).1)
  · exact le_rfl
  · exact p.finalConnector.ball_seed
  · exact p.finalConnector.target_seed
  · exact p.finalConnector.schedule
  · exact p.finalConnector.radius_exact.le

/-- A single graph-free threshold premise is enough to export the literal
finite Lemma 4.3 interface used by `ExactPaths`. -/
def LM43RobustSupplyEventualNumerics : Prop :=
  ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ N : ℕ, d < N →
    Nonempty (LM43RobustSupplyNumericalPackage N d)

/-- Literal finite supply theorem, stated without importing `ExactPaths` so
that the latter can package it definitionally as
`LMRobustSimpleAdjusterSupply`. -/
theorem liuMontgomery_lemma4_3_finite_of_eventualNumerics
    (heventual : LM43RobustSupplyEventualNumerics) :
    ∃ d₀ : ℕ, ∀ {W : Type u} [Fintype W] [Nonempty W]
      (J : SimpleGraph W) [DecidableRel J.Adj]
      (_B : Bipartition J) {d : ℕ},
      d₀ ≤ d →
      IsLMExpander J (1 / 1024) ((1 / 64) * (d : ℝ)) →
      (∀ v : W, d ≤ J.degree v) →
      ¬ oneSubdivisionClique (d / 2) ⊑ J →
      ∀ U : Finset W, U.card ≤ lm47SimpleBudget (Fintype.card W) →
        ∃ A : Adjuster J (lm47InflatedOrder (Fintype.card W))
            (2 * Parameters.lmSimpleRadius (1 / 1024) (Fintype.card W)) 1,
          Disjoint U A.verts := by
  obtain ⟨d₀, hnum⟩ := heventual
  refine ⟨d₀, ?_⟩
  intro W _ _ J _ B d hd hexp hdegree hfree U hU
  let v : W := Classical.choice inferInstance
  have hdN : d < Fintype.card W :=
    (hdegree v).trans_lt (J.degree_lt_card_verts v)
  obtain ⟨p⟩ := hnum d hd (Fintype.card W) hdN
  have hU' : U.card ≤ lm43DeletionCap (Fintype.card W) d := by
    simpa [lm43DeletionCap] using hU
  obtain ⟨A, hA⟩ := exists_canonical_robust_simpleAdjuster
    J p hexp hdegree hfree U hU'
  change ∃ A : Adjuster J (lm43TargetOrder (Fintype.card W) d)
      (2 * Parameters.lmSimpleRadius (1 / 1024) (Fintype.card W)) 1,
    Disjoint U A.verts
  refine ⟨A.radiusMono p.output_radius, ?_⟩
  simpa only [Adjuster.radiusMono_verts] using hA

end SmallSimpleAdjusterCandidate

end Erdos63
