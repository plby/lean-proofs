/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos63.AdjusterBase

/-!
# The final contradiction in Liu--Montgomery Lemma 4.3

After Claims 4.5 and 4.6 the proof retains a conflict-free family of `R`
eligible simple-adjuster candidates.  No member has a short route either to
the high-degree set or to the auxiliary expansion.  The correlated Lemma 3.7
grows the union of both ends of one candidate while avoiding its core and the
ambient deletion.  Lemma 3.4 then connects that large ball to the auxiliary
expansion.  Concatenating the ball witness with the connector, and bypassing
the resulting walk, contradicts the second non-reachability certificate.

The graph-free numerical tails of Lemmas 3.7 and 3.4 are deliberately exposed
as hypotheses.  `Claim43Numerics` supplies the former in the eventual
application; the latter is the usual finite expander-growth certificate.
-/

open Finset Set SimpleGraph
open scoped SimpleGraph

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

variable {V : Type u}

namespace SmallSimpleAdjusterCandidate

/-- A surviving candidate's actual ball, grown in `G-(U∪core)`, is
contained in its high-degree-deleted ball.  The only input beyond eligibility
is precisely the Claim 4.5 non-reachability certificate. -/
theorem candidate_ball_subset_highDegree_ball_of_no_high
    [Fintype V] (G : SimpleGraph V)
    {deleted highDegree protectedSet : Finset V}
    {separation highRadius ballRadius minRadius maxRadius : ℕ}
    (A : SmallSimpleAdjusterCandidate G minRadius maxRadius)
    (hA : A.Eligible deleted highDegree protectedSet separation)
    (hnoHigh : ¬ A.ReachesAvoidingOwnCore deleted
      (highDegree \ deleted) highRadius)
    (hballHigh : ballRadius ≤ highRadius) :
    ballAvoidingFrom G
        (((deleted ∪ A.adjuster.core : Finset V) : Set V))
        A.ends ballRadius ⊆
      ballAvoidingFrom G
        (((highDegree ∪ A.adjuster.core : Finset V) : Set V))
        A.ends ballRadius := by
  classical
  let X : Finset V := deleted ∪ A.adjuster.core
  have hfar : ¬ HasShortAvoidingConnection G X A.ends highDegree ballRadius := by
    intro hreach
    apply hnoHigh
    obtain ⟨x, hx, y, hy, p, hp, hpAvoid, hpLength⟩ := hreach
    have hyDeleted : y ∉ deleted := by
      intro hyDeleted
      apply hpAvoid y (by simp)
      exact Finset.mem_union_left _ hyDeleted
    exact ⟨x, hx, y, Finset.mem_sdiff.2 ⟨hy, hyDeleted⟩,
      p, hp, hpAvoid, hpLength.trans hballHigh⟩
  have heq := ballAvoidingFrom_union_eq_of_no_shortAvoidingConnection
    G X highDegree A.ends ballRadius
      (A.ends_disjoint_deleted_union_core hA) hfar
  rw [← heq]
  apply ballAvoidingFrom_forbidden_anti G
  intro z hz
  rw [Finset.coe_union] at hz
  change z ∈ (X : Set V) ∪ (highDegree : Set V)
  rcases hz with hzHigh | hzCore
  · exact Or.inr hzHigh
  · exact Or.inl (Finset.mem_union_right _ hzCore)

/-- The final post-Claim-4.6 contradiction in finite form.

The family has exactly `R` members and is conflict-free.  `hnoHigh` and
`hnoTarget` are the two certificates carried by the family after the two
discarding steps.  The `LM37CorrelatedScale` and the hypotheses adjacent to
it are the correlated Lemma 3.7 certificate.  The final six hypotheses are
the direct Lemma 3.4 certificate connecting the selected large ball to
`targetSet` (the vertex set of the auxiliary expansion in the source).
-/
theorem false_of_conflictFree_nonreaching_family
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation highRadius ballRadius targetRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation}).Pairwise
      fun A B ↦ ¬ Conflict A.1 B.1 highDegree separation))
    (R deletedCap degreeInto ballTarget connectorQ connectorRadius : ℕ)
    (scale : LM37CorrelatedScale (Fintype.card V) deletedCap R 0
      ballRadius ballTarget degreeInto epsilon kappa)
    (hcard : S.card = R)
    (hdeleted : deleted.card ≤ deletedCap)
    (hnoHigh : ∀ A ∈ S, ¬ A.1.ReachesAvoidingOwnCore deleted
      (highDegree \ deleted) highRadius)
    (hnoTarget : ∀ A ∈ S, ¬ A.1.ReachesAvoidingOwnCore deleted
      targetSet targetRadius)
    (hballHigh : ballRadius ≤ highRadius)
    (hseparation : ballRadius + ballRadius ≤ separation)
    (hstart : scale.growth 0 < 2 * minRadius ^ 2)
    (hstartOne : scale.growth 1 < 2 * minRadius ^ 2)
    (hminSize : scale.minSize ≤ 2 * minRadius ^ 2)
    (hneighbor : ∀ ell s, 0 < ell → ell ≤ ballRadius →
      scale.growth (ell - 1) < s →
      scale.stepLoss ell + 10 * maxRadius ≤ scale.neighborBudget s)
    (hdegree : ∀ i : S, ∀ v ∈ ballAvoidingFrom G
      (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
      i.1.1.ends ballRadius,
        (G.neighborFinset v ∩ deleted).card ≤ degreeInto)
    (hlargeBudgetSum : ∀ (J : Finset S) (f : S → ℕ),
      (∀ i ∈ J, scale.cutoff ≤ f i ∧ f i ≤ scale.D) →
      ∑ i ∈ J, scale.neighborBudget (f i) ≤
        scale.largeBudget (∑ i ∈ J, f i))
    (hTargetDisjoint : ∀ i : S,
      Disjoint targetSet (deleted ∪ i.1.1.adjuster.core))
    (hBallLower : kappa / 2 ≤ (ballTarget : ℝ))
    (hTargetLower : kappa / 2 ≤ (targetSet.card : ℝ))
    (hBallRate : ∀ i : S, ∀ s : ℕ, ballTarget ≤ s →
      s ≤ Fintype.card V / 2 →
      (((((deleted ∪ i.1.1.adjuster.core).card + connectorQ : ℕ)) : ℝ) ≤
        expansionEpsilon epsilon kappa s * (s : ℝ)))
    (hTargetRate : ∀ i : S, ∀ s : ℕ, targetSet.card ≤ s →
      s ≤ Fintype.card V / 2 →
      (((((deleted ∪ i.1.1.adjuster.core).card + connectorQ : ℕ)) : ℝ) ≤
        expansionEpsilon epsilon kappa s * (s : ℝ)))
    (hBallSteps : Fintype.card V / 2 + 1 ≤
      ballTarget + connectorRadius * connectorQ)
    (hTargetSteps : Fintype.card V / 2 + 1 ≤
      targetSet.card + connectorRadius * connectorQ)
    (hTotalRadius : ballRadius + 2 * connectorRadius ≤ targetRadius) : False := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  letI : DecidableRel G.Adj := originalDecAdj
  let Aseed : S → Finset V := fun i ↦ i.1.1.ends
  let Bset : S → Finset V := fun i ↦ i.1.1.adjuster.core
  let Cset : S → Finset V := fun _ ↦ ∅
  have hpairHigh :
      ((Finset.univ : Finset S) : Set S).PairwiseDisjoint
        (fun i ↦ ballAvoidingFrom G
          ((highDegree : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
          (Aseed i) ballRadius) := by
    exact pairwiseDisjoint_candidate_avoidingBalls
      (G := G) hpair hseparation Bset Cset
  have hpairActual :
      ((Finset.univ : Finset S) : Set S).PairwiseDisjoint
        (fun i ↦ ballAvoidingFrom G
          ((deleted : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
          (Aseed i) ballRadius) := by
    intro i hi j hj hij
    apply (hpairHigh hi hj hij).mono
    · simpa [Aseed, Bset, Cset, Set.union_empty] using
        candidate_ball_subset_highDegree_ball_of_no_high
          G i.1.1 i.1.2 (hnoHigh i.1 i.2) hballHigh
    · simpa [Aseed, Bset, Cset, Set.union_empty] using
        candidate_ball_subset_highDegree_ball_of_no_high
          G j.1.1 j.1.2 (hnoHigh j.1 j.2) hballHigh
  obtain ⟨i, hiLarge⟩ := exists_large_avoiding_ball_of_LM37CorrelatedScale
    G epsilon kappa hexp deleted Aseed Bset Cset deletedCap R 0
      ballRadius ballTarget degreeInto scale hdeleted (by simpa [hcard])
      (by
        intro i
        dsimp [Aseed]
        rw [card_ends]
        exact hstart.trans_le (Nat.mul_le_mul_left 2
          (Nat.pow_le_pow_left i.1.1.min_le 2)))
      (by
        intro i
        have hseed : 2 * minRadius ^ 2 ≤ (Aseed i).card := by
          dsimp [Aseed]
          rw [card_ends]
          exact Nat.mul_le_mul_left 2
            (Nat.pow_le_pow_left i.1.1.min_le 2)
        exact hstartOne.trans_le (hseed.trans
          (Finset.card_le_card (subset_ballAvoidingFrom G
            ((deleted : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
            (Aseed i) 1))))
      (by
        intro i
        have hseed : 2 * minRadius ^ 2 ≤ (Aseed i).card := by
          dsimp [Aseed]
          rw [card_ends]
          exact Nat.mul_le_mul_left 2
            (Nat.pow_le_pow_left i.1.1.min_le 2)
        exact hminSize.trans (hseed.trans
          (Finset.card_le_card (subset_ballAvoidingFrom G
            ((deleted : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
            (Aseed i) 1))))
      (by
        intro i r
        simp [Cset, HasLimitedContactAfterDeletion,
          blockedExternalNeighborhood])
      hpairActual
      (by
        intro i ell hell hellRadius hslow
        dsimp [Bset]
        have hcore : i.1.1.adjuster.core.card ≤ 10 * maxRadius := by
          calc
            i.1.1.adjuster.core.card ≤ 10 * i.1.1.radius * 1 :=
              i.1.1.adjuster.core_card_le
            _ ≤ 10 * maxRadius := by
              simpa using Nat.mul_le_mul_left 10 i.1.1.le_max
        simpa [Cset] using
          (Nat.add_le_add_left hcore (scale.stepLoss ell)).trans
            (hneighbor ell _ hell hellRadius hslow))
      (by
        intro i v hv
        have hv' : v ∈ ballAvoidingFrom G
            (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
            i.1.1.ends ballRadius := by
          simpa [Aseed, Bset, Cset, Set.union_empty] using hv
        exact hdegree i v hv')
      hlargeBudgetSum
  let W : Finset V := deleted ∪ i.1.1.adjuster.core
  let largeBall : Finset V := ballAvoidingFrom G (W : Set V)
    i.1.1.ends ballRadius
  have hiLarge' : ballTarget ≤ largeBall.card := by
    simpa [largeBall, W, Aseed, Bset, Cset, Set.union_empty] using hiLarge
  have hEndsW : Disjoint i.1.1.ends W := by
    simpa [W] using i.1.1.ends_disjoint_deleted_union_core i.1.2
  have hBallW : Disjoint largeBall W := by
    exact disjoint_ballAvoidingFrom_forbidden G i.1.1.ends W ballRadius hEndsW
  obtain ⟨a, haBall, b, hbTarget, q, hq, hqLength⟩ :=
    exists_avoiding_path_between_of_lmExpander_growth
      G epsilon kappa hexp W largeBall targetSet connectorQ connectorRadius
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

/-- Minimum-degree-bootstrap version of the final post-Claim-4.6
contradiction.

Unlike `false_of_conflictFree_nonreaching_family`, neither the selected
Lemma 3.7 ball nor `targetSet` is assumed to have cardinality at least
`kappa / 2`.  Instead, both are fed to `exists_short_set_connector_ge`.
Each endpoint either already reaches `connectorStart`, or obtains that seed
after one minimum-degree layer because
`connectorStart + connectorWorkspace ≤ degreeScale`.

`growth` is graph-free: it records the canonical start, the fact that all
subsequent sizes lie above the expander cutoff, and the multiplicative
growth schedule through `connectorRadius` rounds.  The extra bootstrap round
is reflected literally in `hTotalRadius`. -/
theorem false_of_conflictFree_nonreaching_family_bootstrap
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation highRadius ballRadius targetRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted highDegree protectedSet separation}).Pairwise
      fun A B ↦ ¬ Conflict A.1 B.1 highDegree separation))
    (R deletedCap degreeInto ballTarget degreeScale connectorStart
      connectorWorkspace connectorRadius : ℕ)
    (scale : LM37CorrelatedScale (Fintype.card V) deletedCap R 0
      ballRadius ballTarget degreeInto epsilon kappa)
    (hcard : S.card = R)
    (hdeleted : deleted.card ≤ deletedCap)
    (hnoHigh : ∀ A ∈ S, ¬ A.1.ReachesAvoidingOwnCore deleted
      (highDegree \ deleted) highRadius)
    (hnoTarget : ∀ A ∈ S, ¬ A.1.ReachesAvoidingOwnCore deleted
      targetSet targetRadius)
    (hballHigh : ballRadius ≤ highRadius)
    (hseparation : ballRadius + ballRadius ≤ separation)
    (hstart : scale.growth 0 < 2 * minRadius ^ 2)
    (hstartOne : scale.growth 1 < 2 * minRadius ^ 2)
    (hminSize : scale.minSize ≤ 2 * minRadius ^ 2)
    (hneighbor : ∀ ell s, 0 < ell → ell ≤ ballRadius →
      scale.growth (ell - 1) < s →
      scale.stepLoss ell + 10 * maxRadius ≤ scale.neighborBudget s)
    (hdegreeInto : ∀ i : S, ∀ v ∈ ballAvoidingFrom G
      (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
      i.1.1.ends ballRadius,
        (G.neighborFinset v ∩ deleted).card ≤ degreeInto)
    (hlargeBudgetSum : ∀ (J : Finset S) (f : S → ℕ),
      (∀ i ∈ J, scale.cutoff ≤ f i ∧ f i ≤ scale.D) →
      ∑ i ∈ J, scale.neighborBudget (f i) ≤
        scale.largeBudget (∑ i ∈ J, f i))
    (hdegree : ∀ v : V, degreeScale ≤ G.degree v)
    (hTargetNonempty : targetSet.Nonempty)
    (hTargetDisjoint : ∀ i : S,
      Disjoint targetSet (deleted ∪ i.1.1.adjuster.core))
    (hConnectorWorkspace : ∀ i : S,
      (deleted ∪ i.1.1.adjuster.core).card ≤ connectorWorkspace)
    (hBallSeed : connectorStart ≤ ballTarget ∨
      connectorStart + connectorWorkspace ≤ degreeScale)
    (hTargetSeed : connectorStart ≤ targetSet.card ∨
      connectorStart + connectorWorkspace ≤ degreeScale)
    (growth : LM42GrowthSchedule (Fintype.card V) connectorStart
      connectorWorkspace connectorRadius epsilon kappa)
    (hTotalRadius : ballRadius + 2 * (connectorRadius + 1) ≤ targetRadius) : False := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  letI : DecidableRel G.Adj := originalDecAdj
  let Aseed : S → Finset V := fun i ↦ i.1.1.ends
  let Bset : S → Finset V := fun i ↦ i.1.1.adjuster.core
  let Cset : S → Finset V := fun _ ↦ ∅
  have hpairHigh :
      ((Finset.univ : Finset S) : Set S).PairwiseDisjoint
        (fun i ↦ ballAvoidingFrom G
          ((highDegree : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
          (Aseed i) ballRadius) := by
    exact pairwiseDisjoint_candidate_avoidingBalls
      (G := G) hpair hseparation Bset Cset
  have hpairActual :
      ((Finset.univ : Finset S) : Set S).PairwiseDisjoint
        (fun i ↦ ballAvoidingFrom G
          ((deleted : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
          (Aseed i) ballRadius) := by
    intro i hi j hj hij
    apply (hpairHigh hi hj hij).mono
    · simpa [Aseed, Bset, Cset, Set.union_empty] using
        candidate_ball_subset_highDegree_ball_of_no_high
          G i.1.1 i.1.2 (hnoHigh i.1 i.2) hballHigh
    · simpa [Aseed, Bset, Cset, Set.union_empty] using
        candidate_ball_subset_highDegree_ball_of_no_high
          G j.1.1 j.1.2 (hnoHigh j.1 j.2) hballHigh
  obtain ⟨i, hiLarge⟩ := exists_large_avoiding_ball_of_LM37CorrelatedScale
    G epsilon kappa hexp deleted Aseed Bset Cset deletedCap R 0
      ballRadius ballTarget degreeInto scale hdeleted (by simpa [hcard])
      (by
        intro i
        dsimp [Aseed]
        rw [card_ends]
        exact hstart.trans_le (Nat.mul_le_mul_left 2
          (Nat.pow_le_pow_left i.1.1.min_le 2)))
      (by
        intro i
        have hseed : 2 * minRadius ^ 2 ≤ (Aseed i).card := by
          dsimp [Aseed]
          rw [card_ends]
          exact Nat.mul_le_mul_left 2
            (Nat.pow_le_pow_left i.1.1.min_le 2)
        exact hstartOne.trans_le (hseed.trans
          (Finset.card_le_card (subset_ballAvoidingFrom G
            ((deleted : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
            (Aseed i) 1))))
      (by
        intro i
        have hseed : 2 * minRadius ^ 2 ≤ (Aseed i).card := by
          dsimp [Aseed]
          rw [card_ends]
          exact Nat.mul_le_mul_left 2
            (Nat.pow_le_pow_left i.1.1.min_le 2)
        exact hminSize.trans (hseed.trans
          (Finset.card_le_card (subset_ballAvoidingFrom G
            ((deleted : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
            (Aseed i) 1))))
      (by
        intro i r
        simp [Cset, blockedExternalNeighborhood])
      hpairActual
      (by
        intro i ell hell hellRadius hslow
        dsimp [Bset]
        have hcore : i.1.1.adjuster.core.card ≤ 10 * maxRadius := by
          calc
            i.1.1.adjuster.core.card ≤ 10 * i.1.1.radius * 1 :=
              i.1.1.adjuster.core_card_le
            _ ≤ 10 * maxRadius := by
              simpa using Nat.mul_le_mul_left 10 i.1.1.le_max
        simpa [Cset] using
          (Nat.add_le_add_left hcore (scale.stepLoss ell)).trans
            (hneighbor ell _ hell hellRadius hslow))
      (by
        intro i v hv
        have hv' : v ∈ ballAvoidingFrom G
            (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
            i.1.1.ends ballRadius := by
          simpa [Aseed, Bset, Cset, Set.union_empty] using hv
        exact hdegreeInto i v hv')
      hlargeBudgetSum
  let W : Finset V := deleted ∪ i.1.1.adjuster.core
  let largeBall : Finset V := ballAvoidingFrom G (W : Set V)
    i.1.1.ends ballRadius
  have hiLarge' : ballTarget ≤ largeBall.card := by
    simpa [largeBall, W, Aseed, Bset, Cset, Set.union_empty] using hiLarge
  have hEndsW : Disjoint i.1.1.ends W := by
    simpa [W] using i.1.1.ends_disjoint_deleted_union_core i.1.2
  have hBallW : Disjoint largeBall W := by
    exact disjoint_ballAvoidingFrom_forbidden G i.1.1.ends W ballRadius hEndsW
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
      (hConnectorWorkspace i) hBallNonempty hTargetNonempty hBallSeed'
      hTargetSeed hBallW (hTargetDisjoint i)
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

end SmallSimpleAdjusterCandidate

end Erdos63
