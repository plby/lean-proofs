/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCausalReferenceHammockRows
import ErdosProblems.Erdos599.HalfwayFrontierHeight
import ErdosProblems.Erdos599.RegularSafeCompletion
import ErdosProblems.Erdos599.SliceSegmentCore
import ErdosProblems.Erdos599.CoherentHammockTracker
import ErdosProblems.Erdos599.CoherentNondegenerateHammockTracker
import ErdosProblems.Erdos599.CoherentNondegenerateHammockLargeDiagnostic
import ErdosProblems.Erdos599.ColouredSafeEndpointTracker

/-!
# The nontrivial causal Section 9 rows

The preceding causal-reference module isolates the reference/hammock
mechanism, but its empty initial row is only a diagnostic.  This file adds
the literal data inserted by the source construction: a prescribed seed,
strict-prior deferred records and markers, and safe target completions at
unhindered stages.  All data are computed from the strict-prior ladder.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating Ladder
open CardinalInduction
open CardinalInduction.RegularRows

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace CausalSection9Rows

abbrev priorCarrier
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) : Set V :=
  CausalReferenceHammockRows.priorCarrier a prior

def priorCore
    (Gamma : DWeb V) (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) :
    Gamma.KappaLadder (succ kappa) :=
  UnroofedHalfwayRowLadder.priorLadder Gamma a prior

def priorDeferred
    (Gamma : DWeb V) (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) :
    Gamma.KappaLadder (succ kappa) :=
  DWeb.KappaLadder.Deferred.withValidBookkeeping
    (priorCore Gamma a prior)

/-- All strict-prior recorded carriers and markers. -/
def historyIncrement
    (Gamma : DWeb V) (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) : Set V :=
  Gamma.vertexSet
      ((DWeb.KappaLadder.Deferred.bookkeeping
        (priorDeferred Gamma a prior)).recordedBefore a) ∪
    (priorDeferred Gamma a prior).markerSetBelow a

abbrev ActiveStageTarget
    (L : Gamma.KappaLadder (succ kappa))
    (a : Ladder.Stage (succ kappa)) (X : Set V) :=
  {z : V // z ∈ X ∩ L.frontier a}

/-- The source-Theorem-6.1 choice at an unhindered ordinary stage. -/
noncomputable def safeStageTargetChoice
    (L : Gamma.KappaLadder (succ kappa))
    (a : Ladder.Stage (succ kappa)) (X : Set V)
    (hU : (L.stageWeb a).IsUnhindered)
    (z : ActiveStageTarget L a X) :
    RegularSafeCompletion.SafeCompletionChoice (L.stageWeb a) ∅ z.1 :=
  Classical.choice
    (RegularSafeCompletion.exists_safeCompletionChoice
      (L.stageWeb a) ∅ (by simpa using hU) z.2.2 (by simp))

/-- Carriers of all safe target completions requested by the prior closed
set in every strictly earlier unhindered stage.  Thus a vertex first born
in row `alpha` receives its stage-`alpha` safe completion in row
`alpha + 1`, exactly as in the source recursion. -/
noncomputable def targetIncrement
    (Gamma : DWeb V) (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) : Set V := by
  classical
  let L := priorCore Gamma a prior
  exact ⋃ alpha : Set.Iio a,
    if hU : (L.stageWeb alpha.1).IsUnhindered then
      ⋃ z : ActiveStageTarget L alpha.1 (priorCarrier a prior),
        (safeStageTargetChoice L alpha.1
          (priorCarrier a prior) hU z).path.support
    else ∅

/-- The prefix-causal coherent `kappa`-hammock choice for every endpoint
pair eligible in the current strict-prior geometry.  Unlike the two
diagnostic stage choices retained below, these choices remember every
earlier member which is still safe at the current reference. -/
noncomputable def coherentOrdinaryHammockIncrement
    (Gamma : DWeb V) (kappa : Cardinal.{u})
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) : Set V :=
  let L := priorCore Gamma a prior
  ⋃ q : EligiblePair (priorCarrier a prior)
      (Gamma.strictRoof (L.frontier a)) (Gamma.roof (L.frontier a)),
    hammockVertexSet
      (CoherentHammockTracker.chosenAt Gamma kappa L.warpAt
        q.1.1 q.1.2 a)

/-- Additional finite-endpoint choices whose individual paths are roofed
at the same stage where nondegeneracy is certified. Their selector is total,
and its cardinal bound holds even for coincident endpoints; later validity
and strong-edge uses are restricted to distinct endpoints. -/
noncomputable def coherentNondegenerateHammockIncrement
    (Gamma : DWeb V) (kappa : Cardinal.{u})
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) : Set V :=
  let L := priorCore Gamma a prior
  ⋃ q : EligiblePair (priorCarrier a prior)
      (Gamma.strictRoof (L.frontier a)) (Gamma.roof (L.frontier a)),
    match q.1.2 with
    | .vertex v => hammockVertexSet
        (CoherentNondegenerateHammockTracker.chosenAt Gamma kappa L.warpAt
          (fun b ↦ Gamma.roof (L.frontier b)) q.1.1 v a)
    | .infinity => ∅

/-- Successor-sized roof-filtered witnesses are inserted when they exist.
The capped tracker alone need not eventually include a large witness. -/
noncomputable def largeNondegenerateHammockIncrement
    (Gamma : DWeb V) (kappa : Cardinal.{u})
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) : Set V :=
  let L := priorCore Gamma a prior
  ⋃ q : EligiblePair (priorCarrier a prior)
      (Gamma.strictRoof (L.frontier a)) (Gamma.roof (L.frontier a)),
    match q.1.2 with
    | .vertex v => hammockVertexSet
        (CoherentNondegenerateHammockLargeDiagnostic.chosenAt
          Gamma kappa L.warpAt (fun b ↦ Gamma.roof (L.frontier b)) q.1.1 v a)
    | .infinity => ∅

/-- Native endpoint requests use the actual strict-prior stage geometry.
The selector's prefix theorem proves agreement with the final ladder later. -/
noncomputable def nativeEndpointHammockIncrement
    (Gamma : DWeb V) (kappa : Cardinal.{u})
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) : Set V :=
  ColouredSafeEndpointTracker.requestedCarriers
    (priorCore Gamma a prior) a (priorCarrier a prior)

/-- The trackers and the large diagnostic are part of the causal row. No
post-hoc enlargement of an already fixed ladder is assumed. -/
noncomputable def coherentHammockIncrement
    (Gamma : DWeb V) (kappa : Cardinal.{u})
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) : Set V :=
  coherentOrdinaryHammockIncrement Gamma kappa a prior ∪
    (coherentNondegenerateHammockIncrement Gamma kappa a prior ∪
      (largeNondegenerateHammockIncrement Gamma kappa a prior ∪
        nativeEndpointHammockIncrement Gamma kappa a prior))

/-- One nontrivial source row. -/
def increment
    (Gamma : DWeb V) (kappa : Cardinal.{u}) (seed : Set V)
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) : Set V :=
  ((seed ∪ historyIncrement Gamma a prior) ∪
      targetIncrement Gamma a prior) ∪
    (CausalReferenceHammockRows.increment Gamma kappa a prior ∪
      coherentHammockIncrement Gamma kappa a prior)

theorem mk_recordedBefore_priorDeferred_le
    (hkappa : aleph0 ≤ kappa)
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) :
    #((DWeb.KappaLadder.Deferred.bookkeeping
        (priorDeferred Gamma a prior)).recordedBefore a) ≤ kappa := by
  let B := DWeb.KappaLadder.Deferred.bookkeeping
    (priorDeferred Gamma a prior)
  let witness : ∀ p : B.recordedBefore a,
      ∃ b : Ladder.Stage (succ kappa), b < a ∧ B.chosen b = some p.1 :=
    fun p ↦ p.2
  let owner : B.recordedBefore a → Ladder.Stage (succ kappa) :=
    fun p ↦ Classical.choose (witness p)
  have howner_lt : ∀ p, owner p < a := fun p ↦
    (Classical.choose_spec (witness p)).1
  have howner_injective : Function.Injective owner := by
    intro p q hpq
    apply Subtype.ext
    have hp := (Classical.choose_spec (witness p)).2
    have hq := (Classical.choose_spec (witness q)).2
    rw [show Classical.choose (witness p) =
      Classical.choose (witness q) by exact hpq] at hp
    exact Option.some.inj (hp.symm.trans hq)
  have hlt : #(B.recordedBefore a) < succ kappa :=
    RegularCardinal.mk_lt_of_injective_bounded_stage
      a owner howner_injective howner_lt
  exact lt_succ_iff.mp hlt

theorem mk_markerSetBelow_priorDeferred_le
    (hkappa : aleph0 ≤ kappa)
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) :
    #((priorDeferred Gamma a prior).markerSetBelow a) ≤ kappa := by
  let L := priorDeferred Gamma a prior
  let witness : ∀ y : L.markerSetBelow a,
      ∃ b : Ladder.Stage (succ kappa), b < a ∧ L.marker b = some y.1 :=
    fun y ↦ y.2
  let owner : L.markerSetBelow a → Ladder.Stage (succ kappa) :=
    fun y ↦ Classical.choose (witness y)
  have howner_lt : ∀ y, owner y < a := fun y ↦
    (Classical.choose_spec (witness y)).1
  have howner_injective : Function.Injective owner := by
    intro y z hyz
    apply Subtype.ext
    have hy := (Classical.choose_spec (witness y)).2
    have hz := (Classical.choose_spec (witness z)).2
    rw [show Classical.choose (witness y) =
      Classical.choose (witness z) by exact hyz] at hy
    exact Option.some.inj (hy.symm.trans hz)
  have hlt : #(L.markerSetBelow a) < succ kappa :=
    RegularCardinal.mk_lt_of_injective_bounded_stage
      a owner howner_injective howner_lt
  exact lt_succ_iff.mp hlt

theorem mk_historyIncrement_le
    (hkappa : aleph0 ≤ kappa)
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) :
    #(historyIncrement Gamma a prior) ≤ kappa := by
  unfold historyIncrement
  apply (Cardinal.mk_union_le _ _).trans
  apply Cardinal.add_le_of_le hkappa
  · apply _root_.Erdos599.CardinalInduction.HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le hkappa
    exact mk_recordedBefore_priorDeferred_le hkappa a prior
  · exact mk_markerSetBelow_priorDeferred_le hkappa a prior

private def activeTargetEmbedding
    (L : Gamma.KappaLadder (succ kappa))
    (a : Ladder.Stage (succ kappa)) (X : Set V) :
    ActiveStageTarget L a X ↪ X where
  toFun z := ⟨z.1, z.2.1⟩
  inj' := by
    intro z w h
    apply Subtype.ext
    exact congrArg (fun t : X => (t : V)) h

theorem mk_targetIncrement_le_succ
    (hkappa : aleph0 ≤ kappa)
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) :
    #(targetIncrement Gamma a prior) ≤ succ kappa := by
  unfold targetIncrement
  dsimp only
  apply CardinalInduction.RegularRows.mk_iUnion_stageSet_le
    (hkappa.trans (le_succ kappa))
  intro alpha
  split
  next hU =>
    apply (Cardinal.mk_iUnion_le _).trans
    apply Cardinal.mul_le_of_le (hkappa.trans (le_succ kappa))
    · exact (Cardinal.mk_le_of_injective
        (activeTargetEmbedding _ alpha.1
          (priorCarrier a prior)).injective).trans
          (CausalHammockRows.mk_priorCarrier_le_succ hkappa a prior)
    · apply ciSup_le'
      intro z
      exact (safeStageTargetChoice _ alpha.1 _ hU z).path.support_countable
        |>.le_aleph0.trans (hkappa.trans (le_succ kappa))
  next _ => simp

theorem mk_coherentOrdinaryHammockIncrement_le_succ
    (hkappa : aleph0 ≤ kappa)
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) :
    #(coherentOrdinaryHammockIncrement Gamma kappa a prior) ≤ succ kappa := by
  unfold coherentOrdinaryHammockIncrement
  dsimp only
  apply (Cardinal.mk_iUnion_le _).trans
  apply Cardinal.mul_le_of_le (hkappa.trans (le_succ kappa))
  · exact mk_eligiblePair_le (hkappa.trans (le_succ kappa))
      (CausalHammockRows.mk_priorCarrier_le_succ hkappa a prior)
  · apply ciSup_le'
    intro q
    have heq : hammockVertexSet
        (CoherentHammockTracker.chosenAt Gamma kappa
          (priorCore Gamma a prior).warpAt q.1.1 q.1.2 a) =
        ⋃ Q : CoherentHammockTracker.chosenAt Gamma kappa
          (priorCore Gamma a prior).warpAt q.1.1 q.1.2 a,
          Q.1.vertexSet := by
      ext x
      simp only [hammockVertexSet, Set.mem_iUnion]
      constructor
      · rintro ⟨Q, hQ, hxQ⟩
        exact ⟨⟨Q, hQ⟩, hxQ⟩
      · rintro ⟨Q, hxQ⟩
        exact ⟨Q.1, Q.2, hxQ⟩
    rw [heq]
    apply (Cardinal.mk_iUnion_le _).trans
    apply Cardinal.mul_le_of_le (hkappa.trans (le_succ kappa))
    · exact (CoherentHammockTracker.card_at_le Gamma kappa hkappa _ _ _ _).trans
        (le_succ kappa)
    · apply ciSup_le'
      intro Q
      exact (altPath_vertexSet_countable Q.1).le_aleph0.trans
        (hkappa.trans (le_succ kappa))

theorem mk_coherentNondegenerateHammockIncrement_le_succ
    (hkappa : aleph0 ≤ kappa)
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) :
    #(coherentNondegenerateHammockIncrement Gamma kappa a prior)
      ≤ succ kappa := by
  unfold coherentNondegenerateHammockIncrement
  dsimp only
  apply (Cardinal.mk_iUnion_le _).trans
  apply Cardinal.mul_le_of_le (hkappa.trans (le_succ kappa))
  · exact mk_eligiblePair_le (hkappa.trans (le_succ kappa))
      (CausalHammockRows.mk_priorCarrier_le_succ hkappa a prior)
  · apply ciSup_le'
    intro q
    cases he : q.1.2 with
    | infinity => simp
    | vertex v =>
        let H := CoherentNondegenerateHammockTracker.chosenAt Gamma kappa
          (priorCore Gamma a prior).warpAt
          (fun b ↦ Gamma.roof ((priorCore Gamma a prior).frontier b)) q.1.1 v a
        have heq : hammockVertexSet H = ⋃ Q : H, Q.1.vertexSet := by
          ext x
          simp only [hammockVertexSet, Set.mem_iUnion]
          constructor
          · rintro ⟨Q, hQ, hxQ⟩
            exact ⟨⟨Q, hQ⟩, hxQ⟩
          · rintro ⟨Q, hxQ⟩
            exact ⟨Q.1, Q.2, hxQ⟩
        change #(hammockVertexSet H) ≤ succ kappa
        rw [heq]
        apply (Cardinal.mk_iUnion_le _).trans
        apply Cardinal.mul_le_of_le (hkappa.trans (le_succ kappa))
        · exact (CoherentNondegenerateHammockTracker.card_at_le
            Gamma kappa hkappa _ _ _ _ _).trans (le_succ kappa)
        · apply ciSup_le'
          intro Q
          exact (altPath_vertexSet_countable Q.1).le_aleph0.trans
            (hkappa.trans (le_succ kappa))

theorem mk_largeNondegenerateHammockIncrement_le_succ
    (hkappa : aleph0 ≤ kappa)
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) :
    #(largeNondegenerateHammockIncrement Gamma kappa a prior)
      ≤ succ kappa := by
  unfold largeNondegenerateHammockIncrement
  dsimp only
  apply (Cardinal.mk_iUnion_le _).trans
  apply Cardinal.mul_le_of_le (hkappa.trans (le_succ kappa))
  · exact mk_eligiblePair_le (hkappa.trans (le_succ kappa))
      (CausalHammockRows.mk_priorCarrier_le_succ hkappa a prior)
  · apply ciSup_le'
    intro q
    cases he : q.1.2 with
    | infinity => simp
    | vertex v =>
        exact CoherentNondegenerateHammockLargeDiagnostic.chosenAt_vertexSet_card_le
          Gamma kappa hkappa _ _ _ _ _

theorem mk_nativeEndpointHammockIncrement_le_succ
    (hkappa : aleph0 ≤ kappa)
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) :
    #(nativeEndpointHammockIncrement Gamma kappa a prior) ≤ succ kappa :=
  ColouredSafeEndpointTracker.requestedCarriers_card_le
    (priorCore Gamma a prior) (hkappa.trans (le_succ kappa)) a
    (CausalHammockRows.mk_priorCarrier_le_succ hkappa a prior)

theorem mk_coherentHammockIncrement_le_succ
    (hkappa : aleph0 ≤ kappa)
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) :
    #(coherentHammockIncrement Gamma kappa a prior) ≤ succ kappa := by
  exact (Cardinal.mk_union_le _ _).trans
    (Cardinal.add_le_of_le (hkappa.trans (le_succ kappa))
      (mk_coherentOrdinaryHammockIncrement_le_succ hkappa a prior)
      ((Cardinal.mk_union_le _ _).trans
        (Cardinal.add_le_of_le (hkappa.trans (le_succ kappa))
          (mk_coherentNondegenerateHammockIncrement_le_succ hkappa a prior)
          ((Cardinal.mk_union_le _ _).trans
            (Cardinal.add_le_of_le (hkappa.trans (le_succ kappa))
              (mk_largeNondegenerateHammockIncrement_le_succ hkappa a prior)
              (mk_nativeEndpointHammockIncrement_le_succ hkappa a prior))))))

theorem mk_increment_le_succ
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (a : Ladder.Stage (succ kappa))
    (prior : ∀ b : Ladder.Stage (succ kappa),
      b < a → CausalState (succ kappa) V) :
    #(increment Gamma kappa seed a prior) ≤ succ kappa := by
  unfold increment
  apply (Cardinal.mk_union_le _ _).trans
  apply Cardinal.add_le_of_le (hkappa.trans (le_succ kappa))
  · apply (Cardinal.mk_union_le _ _).trans
    apply Cardinal.add_le_of_le (hkappa.trans (le_succ kappa))
    · apply (Cardinal.mk_union_le _ _).trans
      exact Cardinal.add_le_of_le (hkappa.trans (le_succ kappa)) hseed
        ((mk_historyIncrement_le hkappa a prior).trans (le_succ kappa))
    · exact mk_targetIncrement_le_succ hkappa a prior
  · exact (Cardinal.mk_union_le _ _).trans
      (Cardinal.add_le_of_le (hkappa.trans (le_succ kappa))
        (CausalReferenceHammockRows.mk_increment_le_succ
          hkappa hGamma a prior)
        (mk_coherentHammockIncrement_le_succ
          (Gamma := Gamma) hkappa a prior))

def rule (Gamma : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (seed : Set V) (hseed : #seed ≤ succ kappa) :
    CausalRowRule (succ kappa) V where
  nextRow a prior := increment Gamma kappa seed a prior
  nextRow_mk_le a prior := mk_increment_le_succ hkappa hGamma hseed a prior

def rowAt (Gamma : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (seed : Set V) (hseed : #seed ≤ succ kappa)
    (a : Ladder.Stage (succ kappa)) : Set V :=
  ((rule Gamma kappa hkappa hGamma seed hseed).state
    (hkappa.trans (le_succ kappa)) a).row

def closedAt (Gamma : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (seed : Set V) (hseed : #seed ≤ succ kappa)
    (a : Ladder.Stage (succ kappa)) : Set V :=
  ⋃ b : Set.Iic a, rowAt Gamma kappa hkappa hGamma seed hseed b.1

def globalCarrier (Gamma : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (seed : Set V) (hseed : #seed ≤ succ kappa) : Set V :=
  ((rule Gamma kappa hkappa hGamma seed hseed).rowSystem
    (hkappa.trans (le_succ kappa))).carrier

def finalLadder (Gamma : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (seed : Set V) (hseed : #seed ≤ succ kappa) :
    Gamma.KappaLadder (succ kappa) :=
  UnroofedHalfwayRowLadder.deferred Gamma (succ kappa)
    ((rule Gamma kappa hkappa hGamma seed hseed).preferred
      (hkappa.trans (le_succ kappa)))

/-- The coherent `kappa`-hammock tracker evaluated on the actual final
causal ladder. -/
def coherentHammockAt (Gamma : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (seed : Set V) (hseed : #seed ≤ succ kappa)
    (u : V) (e : AltEnd V) (a : Ladder.Stage (succ kappa)) :
    Set (AltPath Gamma.graph) :=
  CoherentHammockTracker.chosenAt Gamma kappa
    (finalLadder Gamma kappa hkappa hGamma seed hseed).warpAt u e a

theorem globalCarrier_mk_le_succ
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa) :
    #(globalCarrier Gamma kappa hkappa hGamma seed hseed) ≤ succ kappa :=
  ((rule Gamma kappa hkappa hGamma seed hseed).rowSystem
    (hkappa.trans (le_succ kappa))).mk_carrier_le
      (hkappa.trans (le_succ kappa))

theorem rowAt_subset_globalCarrier
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (a : Ladder.Stage (succ kappa)) :
    rowAt Gamma kappa hkappa hGamma seed hseed a ⊆
      globalCarrier Gamma kappa hkappa hGamma seed hseed :=
  ((rule Gamma kappa hkappa hGamma seed hseed).rowSystem
    (hkappa.trans (le_succ kappa))).row_subset_carrier a

theorem seed_subset_rowAt
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (a : Ladder.Stage (succ kappa)) :
    seed ⊆ rowAt Gamma kappa hkappa hGamma seed hseed a := by
  change seed ⊆ ((rule Gamma kappa hkappa hGamma seed hseed).state
    (hkappa.trans (le_succ kappa)) a).row
  rw [CausalRowRule.state_row_eq]
  change seed ⊆ increment Gamma kappa seed a _
  exact Set.subset_union_left.trans
    (Set.subset_union_left.trans Set.subset_union_left)

theorem seed_subset_globalCarrier
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa) :
    seed ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed := by
  let zero : Ladder.Stage (succ kappa) :=
    ⟨0, (Cardinal.isRegular_succ hkappa).ord_pos⟩
  exact (seed_subset_rowAt hkappa hGamma hseed zero).trans
    (rowAt_subset_globalCarrier hkappa hGamma hseed zero)

theorem historyIncrement_subset_rowAt
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (a : Ladder.Stage (succ kappa)) :
    historyIncrement Gamma a (fun b _hba ↦
      (rule Gamma kappa hkappa hGamma seed hseed).state
        (hkappa.trans (le_succ kappa)) b) ⊆
      rowAt Gamma kappa hkappa hGamma seed hseed a := by
  change _ ⊆ ((rule Gamma kappa hkappa hGamma seed hseed).state
    (hkappa.trans (le_succ kappa)) a).row
  rw [CausalRowRule.state_row_eq]
  change _ ⊆ increment Gamma kappa seed a _
  exact Set.subset_union_right.trans
    (Set.subset_union_left.trans Set.subset_union_left)

theorem targetIncrement_subset_rowAt
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (a : Ladder.Stage (succ kappa)) :
    targetIncrement Gamma a (fun b _hba ↦
      (rule Gamma kappa hkappa hGamma seed hseed).state
        (hkappa.trans (le_succ kappa)) b) ⊆
      rowAt Gamma kappa hkappa hGamma seed hseed a := by
  change _ ⊆ ((rule Gamma kappa hkappa hGamma seed hseed).state
    (hkappa.trans (le_succ kappa)) a).row
  rw [CausalRowRule.state_row_eq]
  change _ ⊆ increment Gamma kappa seed a _
  exact Set.subset_union_right.trans Set.subset_union_left

/-- Each requested safe stage target path has its entire (hence also its
ambient lifted) carrier in the actual row. -/
theorem safeStageTargetChoice_support_subset_rowAt
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    {alpha a : Ladder.Stage (succ kappa)} (halpha : alpha < a)
    (hU : ((priorCore Gamma a (fun b _hba ↦
      (rule Gamma kappa hkappa hGamma seed hseed).state
        (hkappa.trans (le_succ kappa)) b)).stageWeb alpha).IsUnhindered)
    (z : ActiveStageTarget
      (priorCore Gamma a (fun b _hba ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) b)) alpha
      (priorCarrier a (fun b _hba ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) b))) :
    (safeStageTargetChoice
      (priorCore Gamma a (fun b _hba ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) b)) alpha _ hU z).path.support ⊆
      rowAt Gamma kappa hkappa hGamma seed hseed a := by
  classical
  apply Set.Subset.trans _
    (targetIncrement_subset_rowAt hkappa hGamma hseed a)
  unfold targetIncrement
  dsimp only
  apply Set.subset_iUnion_of_subset ⟨alpha, halpha⟩
  rw [dif_pos hU]
  exact Set.subset_iUnion (fun z ↦
    (safeStageTargetChoice _ alpha _ hU z).path.support) z

/-- Prefix-causality for the actual seeded row recursion. -/
theorem prior_geometry_eq_final
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (a : Ladder.Stage (succ kappa)) :
    let prior := fun b (_hba : b < a) ↦
      (rule Gamma kappa hkappa hGamma seed hseed).state
        (hkappa.trans (le_succ kappa)) b
    (priorCore Gamma a prior).warpAt a =
        (finalLadder Gamma kappa hkappa hGamma seed hseed).warpAt a ∧
      (priorCore Gamma a prior).frontier a =
        (finalLadder Gamma kappa hkappa hGamma seed hseed).frontier a := by
  dsimp only
  let Q := rule Gamma kappa hkappa hGamma seed hseed
  let hsucc : aleph0 ≤ succ kappa := hkappa.trans (le_succ kappa)
  have hpref : ∀ b : Ladder.Stage (succ kappa), b < a →
      CardinalInduction.RegularRows.CausalRegular.preferredOfPrior a
          (fun c _hca ↦ Q.state hsucc c) b = Q.preferred hsucc b := by
    intro b hba
    simp only [CardinalInduction.RegularRows.CausalRegular.preferredOfPrior,
      dif_pos hba, CausalRowRule.preferred]
  have hwarp :=
    UnroofedHalfwayRowLadder.core_warpAt_eq_of_forall_lt
      Gamma
      (CardinalInduction.RegularRows.CausalRegular.preferredOfPrior a
        (fun c _hca ↦ Q.state hsucc c))
      (Q.preferred hsucc) a hpref
  have hfrontier :=
    UnroofedHalfwayRowLadder.core_frontier_eq_of_forall_lt
      Gamma
      (CardinalInduction.RegularRows.CausalRegular.preferredOfPrior a
        (fun c _hca ↦ Q.state hsucc c))
      (Q.preferred hsucc) a hpref
  constructor
  · change
      (UnroofedHalfwayRowLadder.core Gamma (succ kappa)
        (CardinalInduction.RegularRows.CausalRegular.preferredOfPrior a
          (fun c _hca ↦ Q.state hsucc c))).warpAt a = _
    simpa only [finalLadder, Q, hsucc,
      UnroofedHalfwayRowLadder.deferred,
      DWeb.KappaLadder.Deferred.withValidBookkeeping,
      DWeb.KappaLadder.warpAt] using hwarp
  · change
      (UnroofedHalfwayRowLadder.core Gamma (succ kappa)
        (CardinalInduction.RegularRows.CausalRegular.preferredOfPrior a
          (fun c _hca ↦ Q.state hsucc c))).frontier a = _
    simpa only [finalLadder, Q, hsucc,
      UnroofedHalfwayRowLadder.deferred,
      DWeb.KappaLadder.Deferred.withValidBookkeeping,
      DWeb.KappaLadder.frontier, DWeb.KappaLadder.stageWeb,
      DWeb.KappaLadder.warpAt] using hfrontier

/-- More generally, a strict-prior ladder computed at `a` already agrees
with the final causal ladder at every earlier stage `alpha`. -/
theorem prior_geometry_eq_final_of_lt
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    {alpha a : Ladder.Stage (succ kappa)} (halpha : alpha < a) :
    let prior := fun b (_hba : b < a) ↦
      (rule Gamma kappa hkappa hGamma seed hseed).state
        (hkappa.trans (le_succ kappa)) b
    (priorCore Gamma a prior).warpAt alpha =
        (finalLadder Gamma kappa hkappa hGamma seed hseed).warpAt alpha ∧
      (priorCore Gamma a prior).frontier alpha =
        (finalLadder Gamma kappa hkappa hGamma seed hseed).frontier alpha := by
  dsimp only
  let Q := rule Gamma kappa hkappa hGamma seed hseed
  let hsucc : aleph0 ≤ succ kappa := hkappa.trans (le_succ kappa)
  have hpref : ∀ b : Ladder.Stage (succ kappa), b < alpha →
      CardinalInduction.RegularRows.CausalRegular.preferredOfPrior a
          (fun c _hca ↦ Q.state hsucc c) b = Q.preferred hsucc b := by
    intro b hbalpha
    have hba : b < a := hbalpha.trans halpha
    simp only [CardinalInduction.RegularRows.CausalRegular.preferredOfPrior,
      dif_pos hba, CausalRowRule.preferred]
  have hwarp :=
    UnroofedHalfwayRowLadder.core_warpAt_eq_of_forall_lt
      Gamma
      (CardinalInduction.RegularRows.CausalRegular.preferredOfPrior a
        (fun c _hca ↦ Q.state hsucc c))
      (Q.preferred hsucc) alpha hpref
  have hfrontier :=
    UnroofedHalfwayRowLadder.core_frontier_eq_of_forall_lt
      Gamma
      (CardinalInduction.RegularRows.CausalRegular.preferredOfPrior a
        (fun c _hca ↦ Q.state hsucc c))
      (Q.preferred hsucc) alpha hpref
  constructor
  · change
      (UnroofedHalfwayRowLadder.core Gamma (succ kappa)
        (CardinalInduction.RegularRows.CausalRegular.preferredOfPrior a
          (fun c _hca ↦ Q.state hsucc c))).warpAt alpha = _
    simpa only [finalLadder, Q, hsucc,
      UnroofedHalfwayRowLadder.deferred,
      DWeb.KappaLadder.Deferred.withValidBookkeeping,
      DWeb.KappaLadder.warpAt] using hwarp
  · change
      (UnroofedHalfwayRowLadder.core Gamma (succ kappa)
        (CardinalInduction.RegularRows.CausalRegular.preferredOfPrior a
          (fun c _hca ↦ Q.state hsucc c))).frontier alpha = _
    simpa only [finalLadder, Q, hsucc,
      UnroofedHalfwayRowLadder.deferred,
      DWeb.KappaLadder.Deferred.withValidBookkeeping,
      DWeb.KappaLadder.frontier, DWeb.KappaLadder.stageWeb,
      DWeb.KappaLadder.warpAt] using hfrontier

theorem prior_warpAt_eq_final_of_le
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    {b a : Ladder.Stage (succ kappa)} (hba : b ≤ a) :
    (priorCore Gamma a (fun c _hca ↦
      (rule Gamma kappa hkappa hGamma seed hseed).state
        (hkappa.trans (le_succ kappa)) c)).warpAt b =
      (finalLadder Gamma kappa hkappa hGamma seed hseed).warpAt b := by
  rcases hba.lt_or_eq with hba | rfl
  · exact (prior_geometry_eq_final_of_lt
      (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed hba).1
  · exact (prior_geometry_eq_final
      (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed b).1

/-- Prefix causality identifies the tracker used by the row definition
with the tracker on the actual final ladder. -/
theorem coherentHammockAt_eq_prior
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (u : V) (e : AltEnd V) (a : Ladder.Stage (succ kappa)) :
    coherentHammockAt Gamma kappa hkappa hGamma seed hseed u e a =
      CoherentHammockTracker.chosenAt Gamma kappa
        (priorCore Gamma a (fun c _hca ↦
          (rule Gamma kappa hkappa hGamma seed hseed).state
            (hkappa.trans (le_succ kappa)) c)).warpAt u e a := by
  symm
  apply CoherentHammockTracker.at_congr_le Gamma kappa _ _ u e a
  intro b hba
  exact prior_warpAt_eq_final_of_le
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed hba

theorem coherentHammockIncrement_subset_rowAt
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (a : Ladder.Stage (succ kappa)) :
    coherentHammockIncrement Gamma kappa a (fun b _hba ↦
      (rule Gamma kappa hkappa hGamma seed hseed).state
        (hkappa.trans (le_succ kappa)) b) ⊆
      rowAt Gamma kappa hkappa hGamma seed hseed a := by
  change _ ⊆ ((rule Gamma kappa hkappa hGamma seed hseed).state
    (hkappa.trans (le_succ kappa)) a).row
  rw [CausalRowRule.state_row_eq]
  change _ ⊆ increment Gamma kappa seed a _
  exact Set.subset_union_right.trans Set.subset_union_right

/-- Every final coherent choice whose endpoints are eligible in the
actual stage geometry has its complete vertex carrier in the causal
global set. -/
theorem coherentHammockAt_contained
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (a : Ladder.Stage (succ kappa))
    (q : EligiblePair
      (priorCarrier a (fun b _hba ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) b))
      (Gamma.strictRoof
        ((finalLadder Gamma kappa hkappa hGamma seed hseed).frontier a))
      (Gamma.roof
        ((finalLadder Gamma kappa hkappa hGamma seed hseed).frontier a))) :
    HammockContained
      (coherentHammockAt Gamma kappa hkappa hGamma seed hseed
        q.1.1 q.1.2 a)
      (globalCarrier Gamma kappa hkappa hGamma seed hseed) := by
  apply Set.Subset.trans ?_
    ((coherentHammockIncrement_subset_rowAt hkappa hGamma hseed a).trans
      (rowAt_subset_globalCarrier hkappa hGamma hseed a))
  unfold coherentHammockIncrement
  apply Set.Subset.trans ?_ Set.subset_union_left
  unfold coherentOrdinaryHammockIncrement
  dsimp only
  have hfrontier := (prior_geometry_eq_final
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed a).2
  rw [hfrontier]
  apply Set.subset_iUnion_of_subset q
  rw [← coherentHammockAt_eq_prior
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed q.1.1 q.1.2 a]

/-- The actual final tracker is maximal-up-to-`kappa` at each stage and
retains every earlier member which remains safe there. -/
theorem coherentHammockAt_spec
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (u : V) (e : AltEnd V) (a : Ladder.Stage (succ kappa)) :
    HammockMaximalUpTo Gamma
        ((finalLadder Gamma kappa hkappa hGamma seed hseed).warpAt a)
        u e kappa
        (coherentHammockAt Gamma kappa hkappa hGamma seed hseed u e a) ∧
      ∀ b, b < a → ∀ Q ∈
          coherentHammockAt Gamma kappa hkappa hGamma seed hseed u e b,
        IsSafe
          ((finalLadder Gamma kappa hkappa hGamma seed hseed).warpAt a) Q →
        Q ∈ coherentHammockAt Gamma kappa hkappa hGamma seed hseed u e a := by
  let L := finalLadder Gamma kappa hkappa hGamma seed hseed
  have hlegal : DWeb.KappaLadder.Deferred.HalfwayGeometry L := by
    let hsucc : aleph0 ≤ succ kappa := hkappa.trans (le_succ kappa)
    let preferred :=
      (rule Gamma kappa hkappa hGamma seed hseed).preferred hsucc
    have hregular : (succ kappa).IsRegular := Cardinal.isRegular_succ hkappa
    have huncountable : aleph0 < succ kappa :=
      hkappa.trans_lt (lt_succ kappa)
    have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
      intro x y hxy hy
      exact (hGamma hxy).1 hy
    simpa only [L, finalLadder, preferred, hsucc] using
      UnroofedHalfwayRowLadder.deferred_halfwayGeometry
        preferred hregular huncountable hNoEnter
  exact CoherentHammockTracker.at_spec Gamma kappa hkappa L.warpAt
    (CoherentHammockTracker.safeConvex_of_deferred Gamma kappa hlegal)
    u e a

/-- Every vertex of the final causal carrier which lies on an unhindered
earlier frontier receives the source-Theorem-6.1 completion for that exact
earlier stage in a later row.  The witness retains the concrete
strict-prior ladder used by the causal definition, while prefix invariance
identifies its stage web with the final one. -/
theorem exists_later_safeStageTargetChoice
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (alpha : Ladder.Stage (succ kappa))
    (hU : ((finalLadder Gamma kappa hkappa hGamma seed hseed).stageWeb
      alpha).IsUnhindered)
    {z : V}
    (hzCarrier : z ∈ globalCarrier Gamma kappa hkappa hGamma seed hseed)
    (hzFrontier : z ∈
      (finalLadder Gamma kappa hkappa hGamma seed hseed).frontier alpha) :
    ∃ (a : Ladder.Stage (succ kappa)) (halpha : alpha < a)
      (hUprior : ((priorCore Gamma a (fun b _hba ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) b)).stageWeb alpha).IsUnhindered)
      (za : ActiveStageTarget
        (priorCore Gamma a (fun b _hba ↦
          (rule Gamma kappa hkappa hGamma seed hseed).state
            (hkappa.trans (le_succ kappa)) b)) alpha
        (priorCarrier a (fun b _hba ↦
          (rule Gamma kappa hkappa hGamma seed hseed).state
            (hkappa.trans (le_succ kappa)) b))),
      za.1 = z ∧
        (safeStageTargetChoice
          (priorCore Gamma a (fun b _hba ↦
            (rule Gamma kappa hkappa hGamma seed hseed).state
              (hkappa.trans (le_succ kappa)) b)) alpha _ hUprior za).path.support ⊆
          globalCarrier Gamma kappa hkappa hGamma seed hseed := by
  let hsucc : aleph0 ≤ succ kappa := hkappa.trans (le_succ kappa)
  let Q := rule Gamma kappa hkappa hGamma seed hseed
  change z ∈ (Q.rowSystem hsucc).carrier at hzCarrier
  obtain ⟨c, hzc⟩ := CardinalInduction.RegularRows.RowSystem.mem_carrier.mp
    hzCarrier
  let a : Ladder.Stage (succ kappa) :=
    ⟨max alpha.1 c.1 + 1,
      (Cardinal.isSuccLimit_ord hsucc).succ_lt (max_lt alpha.2 c.2)⟩
  have halpha : alpha < a := by
    change alpha.1 < max alpha.1 c.1 + 1
    exact (le_max_left alpha.1 c.1).trans_lt (lt_add_one _)
  have hca : c < a := by
    change c.1 < max alpha.1 c.1 + 1
    exact (le_max_right alpha.1 c.1).trans_lt (lt_add_one _)
  let prior := fun b (_hba : b < a) ↦ Q.state hsucc b
  have hgeom := prior_geometry_eq_final_of_lt
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed halpha
  have hUprior : ((priorCore Gamma a prior).stageWeb alpha).IsUnhindered := by
    unfold DWeb.KappaLadder.stageWeb
    rw [hgeom.1]
    exact hU
  have hzPrior : z ∈ priorCarrier a prior := by
    exact Set.mem_iUnion.2 ⟨⟨c, hca⟩, hzc⟩
  have hzFrontierPrior : z ∈ (priorCore Gamma a prior).frontier alpha := by
    rw [hgeom.2]
    exact hzFrontier
  let za : ActiveStageTarget (priorCore Gamma a prior) alpha
      (priorCarrier a prior) :=
    ⟨z, hzPrior, hzFrontierPrior⟩
  refine ⟨a, halpha, hUprior, za, rfl, ?_⟩
  exact (safeStageTargetChoice_support_subset_rowAt
      (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed halpha
      hUprior za).trans
    (rowAt_subset_globalCarrier hkappa hGamma hseed a)

/-- Successor geometry and the marker born at an earlier stage are already
fixed by the strict-prior preferred stream. -/
theorem prior_successorWarp_marker_eq_final
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    {a b : Ladder.Stage (succ kappa)} (hba : b < a) :
    let prior := fun c (_hca : c < a) ↦
      (rule Gamma kappa hkappa hGamma seed hseed).state
        (hkappa.trans (le_succ kappa)) c
    (priorCore Gamma a prior).successorWarp b =
        (finalLadder Gamma kappa hkappa hGamma seed hseed).successorWarp b ∧
      (priorCore Gamma a prior).marker b =
        (finalLadder Gamma kappa hkappa hGamma seed hseed).marker b := by
  dsimp only
  let Q := rule Gamma kappa hkappa hGamma seed hseed
  let hsucc : aleph0 ≤ succ kappa := hkappa.trans (le_succ kappa)
  let p := CardinalInduction.RegularRows.CausalRegular.preferredOfPrior a
    (fun c _hca ↦ Q.state hsucc c)
  let q := Q.preferred hsucc
  have hpref : ∀ c : Ladder.Stage (succ kappa), c < a → p c = q c := by
    intro c hca
    simp only [p, q,
      CardinalInduction.RegularRows.CausalRegular.preferredOfPrior,
      dif_pos hca, CausalRowRule.preferred]
  have hle (d : Ladder.Stage (succ kappa)) (hdb : d ≤ b) : p d = q d :=
    hpref d (hdb.trans_lt hba)
  constructor
  · exact DWeb.UnroofedMarker.successorWarp_eq_of_forall_le
      Gamma (succ kappa) p q b hle
  · exact DWeb.UnroofedMarker.marker_eq_of_forall_le
      Gamma (succ kappa) p q b hle

/-- The deferred recursive choice made at an earlier stage is also prefix
invariant; it therefore represents the actual final recorded path. -/
theorem priorDeferred_chosen_eq_final
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    {a b : Ladder.Stage (succ kappa)} (hba : b < a) :
    let prior := fun c (_hca : c < a) ↦
      (rule Gamma kappa hkappa hGamma seed hseed).state
        (hkappa.trans (le_succ kappa)) c
    (priorDeferred Gamma a prior).chosen b =
      (finalLadder Gamma kappa hkappa hGamma seed hseed).chosen b := by
  dsimp only
  let P := priorCore Gamma a (fun c _hca ↦
    (rule Gamma kappa hkappa hGamma seed hseed).state
      (hkappa.trans (le_succ kappa)) c)
  let F := UnroofedHalfwayRowLadder.core Gamma (succ kappa)
    ((rule Gamma kappa hkappa hGamma seed hseed).preferred
      (hkappa.trans (le_succ kappa)))
  change (DWeb.KappaLadder.Deferred.chosenBookkeeping P).chosen b =
    (DWeb.KappaLadder.Deferred.chosenBookkeeping F).chosen b
  apply DWeb.KappaLadder.Deferred.chosenBookkeeping_chosen_congr_le P F b
  intro c hcb
  unfold DWeb.KappaLadder.Deferred.selectable
  have hca : c < a := hcb.trans_lt hba
  have hgeom := prior_successorWarp_marker_eq_final
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed hca
  ext r
  change
    (r ∈ Gamma.inessentialPaths (P.successorWarp c) ∧
      P.marker c ≠ some r.initial) ↔
    (r ∈ Gamma.inessentialPaths (F.successorWarp c) ∧
      F.marker c ≠ some r.initial)
  have hsuccGeom : P.successorWarp c = F.successorWarp c := by
    have hPF : P.successorWarp c =
        (finalLadder Gamma kappa hkappa hGamma seed hseed).successorWarp c :=
      hgeom.1
    exact hPF
  have hmarkerGeom : P.marker c = F.marker c := by
    have hPF : P.marker c =
        (finalLadder Gamma kappa hkappa hGamma seed hseed).marker c :=
      hgeom.2
    exact hPF
  rw [hsuccGeom, hmarkerGeom]

/-- Literal final-ladder history below one stage. -/
def finalHistoryBefore
    (Gamma : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (seed : Set V) (hseed : #seed ≤ succ kappa)
    (a : Ladder.Stage (succ kappa)) : Set V :=
  Gamma.vertexSet
      ((DWeb.KappaLadder.Deferred.bookkeeping
        (finalLadder Gamma kappa hkappa hGamma seed hseed)).recordedBefore a) ∪
    (finalLadder Gamma kappa hkappa hGamma seed hseed).markerSetBelow a

theorem historyIncrement_eq_finalHistoryBefore
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (a : Ladder.Stage (succ kappa)) :
    historyIncrement Gamma a (fun b _hba ↦
      (rule Gamma kappa hkappa hGamma seed hseed).state
        (hkappa.trans (le_succ kappa)) b) =
      finalHistoryBefore Gamma kappa hkappa hGamma seed hseed a := by
  have hchosen : ∀ b : Ladder.Stage (succ kappa), b < a →
      (priorDeferred Gamma a (fun c _hca ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) c)).chosen b =
      (finalLadder Gamma kappa hkappa hGamma seed hseed).chosen b := by
    intro b hba
    exact priorDeferred_chosen_eq_final hkappa hGamma hseed hba
  have hmarker : ∀ b : Ladder.Stage (succ kappa), b < a →
      (priorDeferred Gamma a (fun c _hca ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) c)).marker b =
      (finalLadder Gamma kappa hkappa hGamma seed hseed).marker b := by
    intro b hba
    exact (prior_successorWarp_marker_eq_final
      (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed hba).2
  exact UnroofedHalfwayRowLadder.history_eq_of_chosen_marker_eq
    _ _ a hchosen hmarker

/-- Every path selected by the final deferred bookkeeping has its whole
carrier inserted in the next causal row. -/
theorem chosen_support_subset_globalCarrier
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    {a : Ladder.Stage (succ kappa)} {p : Gamma.DPath}
    (hp : (finalLadder Gamma kappa hkappa hGamma seed hseed).chosen a =
      some p) :
    p.support ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed := by
  let hsucc : aleph0 ≤ succ kappa := hkappa.trans (le_succ kappa)
  let b : Ladder.Stage (succ kappa) :=
    ⟨a.1 + 1, (Cardinal.isSuccLimit_ord hsucc).succ_lt a.2⟩
  have hab : a < b := by
    change a.1 < a.1 + 1
    exact lt_add_one a.1
  have hpRecorded : p ∈
      (DWeb.KappaLadder.Deferred.bookkeeping
        (finalLadder Gamma kappa hkappa hGamma seed hseed)).recordedBefore b :=
    ⟨a, hab, hp⟩
  have hhistory :
      finalHistoryBefore Gamma kappa hkappa hGamma seed hseed b ⊆
        globalCarrier Gamma kappa hkappa hGamma seed hseed := by
    rw [← historyIncrement_eq_finalHistoryBefore hkappa hGamma hseed b]
    exact (historyIncrement_subset_rowAt hkappa hGamma hseed b).trans
      (rowAt_subset_globalCarrier hkappa hGamma hseed b)
  intro x hxp
  apply hhistory
  exact Or.inl ⟨p, hpRecorded, hxp⟩

/-- Every marker of the final causal ladder is inserted in the next row. -/
theorem markerSet_subset_globalCarrier
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa) :
    (finalLadder Gamma kappa hkappa hGamma seed hseed).markerSet ⊆
      globalCarrier Gamma kappa hkappa hGamma seed hseed := by
  intro y hy
  obtain ⟨a, hay⟩ := hy
  let hsucc : aleph0 ≤ succ kappa := hkappa.trans (le_succ kappa)
  let b : Ladder.Stage (succ kappa) :=
    ⟨a.1 + 1, (Cardinal.isSuccLimit_ord hsucc).succ_lt a.2⟩
  have hab : a < b := by
    change a.1 < a.1 + 1
    exact lt_add_one a.1
  have hyBelow : y ∈
      (finalLadder Gamma kappa hkappa hGamma seed hseed).markerSetBelow b :=
    ⟨a, hab, hay⟩
  have hhistory :
      finalHistoryBefore Gamma kappa hkappa hGamma seed hseed b ⊆
        globalCarrier Gamma kappa hkappa hGamma seed hseed := by
    rw [← historyIncrement_eq_finalHistoryBefore hkappa hGamma hseed b]
    exact (historyIncrement_subset_rowAt hkappa hGamma hseed b).trans
      (rowAt_subset_globalCarrier hkappa hGamma hseed b)
  exact hhistory (Or.inr hyBelow)

theorem contacted_reference_subset_rowAt
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (a : Ladder.Stage (succ kappa)) :
    meetingVertices Gamma
        ((finalLadder Gamma kappa hkappa hGamma seed hseed).warpAt a)
        (priorCarrier a (fun b _hba ↦
          (rule Gamma kappa hkappa hGamma seed hseed).state
            (hkappa.trans (le_succ kappa)) b)) ⊆
      rowAt Gamma kappa hkappa hGamma seed hseed a := by
  change _ ⊆ ((rule Gamma kappa hkappa hGamma seed hseed).state
    (hkappa.trans (le_succ kappa)) a).row
  rw [CausalRowRule.state_row_eq]
  change _ ⊆ increment Gamma kappa seed a _
  apply Set.Subset.trans ?_ Set.subset_union_right
  apply Set.Subset.trans ?_ Set.subset_union_left
  unfold CausalReferenceHammockRows.increment
  apply Set.Subset.trans ?_ Set.subset_union_right
  unfold CausalReferenceHammockRows.referenceIncrement
  dsimp only
  change meetingVertices Gamma
      ((finalLadder Gamma kappa hkappa hGamma seed hseed).warpAt a) _ ⊆
    meetingVertices Gamma
      ((priorCore Gamma a (fun b _hba ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) b)).warpAt a) _
  rw [(prior_geometry_eq_final (Gamma := Gamma) (kappa := kappa)
    hkappa hGamma hseed a).1]

/-- The actual seeded row contains the maximal-up-to-`kappa` hammock
selected from the full reference warp visible at that stage. -/
theorem selectedHammocks_subset_rowAt
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (a : Ladder.Stage (succ kappa)) :
    allHammockVertices Gamma
        ((finalLadder Gamma kappa hkappa hGamma seed hseed).warpAt a) kappa
        (priorCarrier a (fun b _hba ↦
          (rule Gamma kappa hkappa hGamma seed hseed).state
            (hkappa.trans (le_succ kappa)) b))
        (Gamma.strictRoof
          ((finalLadder Gamma kappa hkappa hGamma seed hseed).frontier a))
        (Gamma.roof
          ((finalLadder Gamma kappa hkappa hGamma seed hseed).frontier a)) ⊆
      rowAt Gamma kappa hkappa hGamma seed hseed a := by
  change _ ⊆ ((rule Gamma kappa hkappa hGamma seed hseed).state
    (hkappa.trans (le_succ kappa)) a).row
  rw [CausalRowRule.state_row_eq]
  change _ ⊆ increment Gamma kappa seed a _
  apply Set.Subset.trans ?_ Set.subset_union_right
  apply Set.Subset.trans ?_ Set.subset_union_left
  unfold CausalReferenceHammockRows.increment
  apply Set.Subset.trans ?_ Set.subset_union_left
  unfold CausalHammockRows.hammockIncrement
  dsimp only
  rw [← (prior_geometry_eq_final (Gamma := Gamma) (kappa := kappa)
    hkappa hGamma hseed a).1,
    ← (prior_geometry_eq_final (Gamma := Gamma) (kappa := kappa)
      hkappa hGamma hseed a).2]
  exact Set.subset_union_left

/-- The same seeded row contains the source's maximal-up-to-`kappa^+`
stage selection. -/
theorem selectedHammocksSucc_subset_rowAt
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (a : Ladder.Stage (succ kappa)) :
    allHammockVertices Gamma
        ((finalLadder Gamma kappa hkappa hGamma seed hseed).warpAt a)
          (succ kappa)
        (priorCarrier a (fun b _hba ↦
          (rule Gamma kappa hkappa hGamma seed hseed).state
            (hkappa.trans (le_succ kappa)) b))
        (Gamma.strictRoof
          ((finalLadder Gamma kappa hkappa hGamma seed hseed).frontier a))
        (Gamma.roof
          ((finalLadder Gamma kappa hkappa hGamma seed hseed).frontier a)) ⊆
      rowAt Gamma kappa hkappa hGamma seed hseed a := by
  change _ ⊆ ((rule Gamma kappa hkappa hGamma seed hseed).state
    (hkappa.trans (le_succ kappa)) a).row
  rw [CausalRowRule.state_row_eq]
  change _ ⊆ increment Gamma kappa seed a _
  apply Set.Subset.trans ?_ Set.subset_union_right
  apply Set.Subset.trans ?_ Set.subset_union_left
  unfold CausalReferenceHammockRows.increment
  apply Set.Subset.trans ?_ Set.subset_union_left
  unfold CausalHammockRows.hammockIncrement
  dsimp only
  rw [← (prior_geometry_eq_final (Gamma := Gamma) (kappa := kappa)
    hkappa hGamma hseed a).1,
    ← (prior_geometry_eq_final (Gamma := Gamma) (kappa := kappa)
      hkappa hGamma hseed a).2]
  exact Set.subset_union_right

/-- At every ordinary stage, the final carrier contains the exact
maximal-up-to-`kappa` hammock selected from that stage's full warp.  This
is deliberately a stage-local statement; it does not identify a
stage-maximal hammock with one maximal for the limit warp. -/
theorem hammockClosedAt
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (a : Ladder.Stage (succ kappa)) :
    HammockClosedUpTo Gamma
      ((finalLadder Gamma kappa hkappa hGamma seed hseed).warpAt a)
      (globalCarrier Gamma kappa hkappa hGamma seed hseed)
      (priorCarrier a (fun b _hba ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) b))
      (Gamma.strictRoof
        ((finalLadder Gamma kappa hkappa hGamma seed hseed).frontier a))
      (Gamma.roof
        ((finalLadder Gamma kappa hkappa hGamma seed hseed).frontier a))
      kappa := by
  intro u e helig
  let q : EligiblePair
      (priorCarrier a (fun b _hba ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) b))
      (Gamma.strictRoof
        ((finalLadder Gamma kappa hkappa hGamma seed hseed).frontier a))
      (Gamma.roof
        ((finalLadder Gamma kappa hkappa hGamma seed hseed).frontier a)) :=
    ⟨(u, e), helig⟩
  refine ⟨chosenHammock Gamma
      ((finalLadder Gamma kappa hkappa hGamma seed hseed).warpAt a)
        kappa q,
    chosenHammock_spec Gamma
      ((finalLadder Gamma kappa hkappa hGamma seed hseed).warpAt a)
        kappa q, ?_⟩
  exact (chosenHammock_contained_all Gamma
      ((finalLadder Gamma kappa hkappa hGamma seed hseed).warpAt a)
        kappa q).mono
    ((selectedHammocks_subset_rowAt hkappa hGamma hseed a).trans
      (rowAt_subset_globalCarrier hkappa hGamma hseed a))

/-- Stage-local hammock closure at the source cardinal `kappa^+`. -/
theorem hammockClosedAt_succ
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (a : Ladder.Stage (succ kappa)) :
    HammockClosedUpTo Gamma
      ((finalLadder Gamma kappa hkappa hGamma seed hseed).warpAt a)
      (globalCarrier Gamma kappa hkappa hGamma seed hseed)
      (priorCarrier a (fun b _hba ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) b))
      (Gamma.strictRoof
        ((finalLadder Gamma kappa hkappa hGamma seed hseed).frontier a))
      (Gamma.roof
        ((finalLadder Gamma kappa hkappa hGamma seed hseed).frontier a))
      (succ kappa) := by
  intro u e helig
  let q : EligiblePair
      (priorCarrier a (fun b _hba ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) b))
      (Gamma.strictRoof
        ((finalLadder Gamma kappa hkappa hGamma seed hseed).frontier a))
      (Gamma.roof
        ((finalLadder Gamma kappa hkappa hGamma seed hseed).frontier a)) :=
    ⟨(u, e), helig⟩
  refine ⟨chosenHammock Gamma
      ((finalLadder Gamma kappa hkappa hGamma seed hseed).warpAt a)
        (succ kappa) q,
    chosenHammock_spec Gamma
      ((finalLadder Gamma kappa hkappa hGamma seed hseed).warpAt a)
        (succ kappa) q, ?_⟩
  exact (chosenHammock_contained_all Gamma
      ((finalLadder Gamma kappa hkappa hGamma seed hseed).warpAt a)
        (succ kappa) q).mono
    ((selectedHammocksSucc_subset_rowAt hkappa hGamma hseed a).trans
      (rowAt_subset_globalCarrier hkappa hGamma hseed a))

theorem closedAt_mono
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa) :
    Monotone (closedAt Gamma kappa hkappa hGamma seed hseed) := by
  intro a b hab x hx
  obtain ⟨c, hxc⟩ := Set.mem_iUnion.1 hx
  exact Set.mem_iUnion.2 ⟨⟨c.1, c.2.trans hab⟩, hxc⟩

theorem iUnion_closedAt_eq_globalCarrier
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa) :
    (⋃ a, closedAt Gamma kappa hkappa hGamma seed hseed a) =
      globalCarrier Gamma kappa hkappa hGamma seed hseed := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, hxa⟩ := Set.mem_iUnion.1 hx
    obtain ⟨b, hxb⟩ := Set.mem_iUnion.1 hxa
    exact rowAt_subset_globalCarrier hkappa hGamma hseed b.1 hxb
  · intro hx
    change x ∈ ⋃ a, rowAt Gamma kappa hkappa hGamma seed hseed a at hx
    obtain ⟨a, hxa⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2
      ⟨⟨a, show a ≤ a from le_rfl⟩, hxa⟩⟩

theorem causalStagePathClosure
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa) :
    CausalStagePathClosure
      (finalLadder Gamma kappa hkappa hGamma seed hseed)
      (closedAt Gamma kappa hkappa hGamma seed hseed) := by
  intro a p hp hmeet
  let hsucc : aleph0 ≤ succ kappa := hkappa.trans (le_succ kappa)
  let preferred :=
    (rule Gamma kappa hkappa hGamma seed hseed).preferred hsucc
  have hregular : (succ kappa).IsRegular := Cardinal.isRegular_succ hkappa
  have huncountable : aleph0 < succ kappa := hkappa.trans_lt (lt_succ kappa)
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (hGamma hxy).1 hy
  have hlegal : DWeb.KappaLadder.Deferred.HalfwayGeometry
      (finalLadder Gamma kappa hkappa hGamma seed hseed) := by
    simpa only [finalLadder, preferred, hsucc] using
      UnroofedHalfwayRowLadder.deferred_halfwayGeometry
        preferred hregular huncountable hNoEnter
  let b : Ladder.Stage (succ kappa) :=
    ⟨a.1 + 1, (Cardinal.isSuccLimit_ord hsucc).succ_lt a.2⟩
  have hab : a < b := by
    change a.1 < a.1 + 1
    exact Order.lt_succ a.1
  obtain ⟨q, hqSucc, hpq⟩ :=
    CardinalInduction.DeferredStageInterval.successorExtensions hlegal a p hp
  have hq : q ∈
      (finalLadder Gamma kappa hkappa hGamma seed hseed).warpAt b := by
    change q ∈ (finalLadder Gamma kappa hkappa hGamma seed hseed).accumulated
      (Ladder.Stage.toExtended b)
    change q ∈ (finalLadder Gamma kappa hkappa hGamma seed hseed).accumulated
      (Ladder.Stage.succExtended a) at hqSucc
    have hstage : Ladder.Stage.toExtended b =
        Ladder.Stage.succExtended a := by apply Subtype.ext; rfl
    rwa [hstage]
  obtain ⟨x, hxp, hxClosed⟩ := hmeet
  obtain ⟨c, hxc⟩ := Set.mem_iUnion.1 hxClosed
  have hcb : c.1 < b := c.2.trans_lt hab
  have hxPrior : x ∈ priorCarrier b (fun d _hdb ↦
      (rule Gamma kappa hkappa hGamma seed hseed).state hsucc d) :=
    Set.mem_iUnion.2 ⟨⟨c.1, hcb⟩, hxc⟩
  have hxq : x ∈ q.support := Gamma.support_mono_of_extends hpq hxp
  have hqMeet : (q.support ∩ priorCarrier b (fun d _hdb ↦
      (rule Gamma kappa hkappa hGamma seed hseed).state hsucc d)).Nonempty :=
    ⟨x, hxq, hxPrior⟩
  have hqRow : q.support ⊆
      rowAt Gamma kappa hkappa hGamma seed hseed b :=
    (support_subset_meetingVertices Gamma
      ((finalLadder Gamma kappa hkappa hGamma seed hseed).warpAt b)
      (priorCarrier b (fun d _hdb ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state hsucc d)) hq hqMeet).trans
      (contacted_reference_subset_rowAt hkappa hGamma hseed b)
  refine ⟨b, hab.le, ?_⟩
  intro y hyp
  exact Set.mem_iUnion.2 ⟨⟨b, show b ≤ b from le_rfl⟩,
    hqRow (Gamma.support_mono_of_extends hpq hyp)⟩

theorem reference_closed
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa) :
    ClosedUnderPaths Gamma
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitWarp
      (globalCarrier Gamma kappa hkappa hGamma seed hseed) := by
  let hsucc : aleph0 ≤ succ kappa := hkappa.trans (le_succ kappa)
  let preferred :=
    (rule Gamma kappa hkappa hGamma seed hseed).preferred hsucc
  have hregular : (succ kappa).IsRegular := Cardinal.isRegular_succ hkappa
  have huncountable : aleph0 < succ kappa := hkappa.trans_lt (lt_succ kappa)
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (hGamma hxy).1 hy
  have hlegal : DWeb.KappaLadder.Deferred.HalfwayGeometry
      (finalLadder Gamma kappa hkappa hGamma seed hseed) := by
    simpa only [finalLadder, preferred, hsucc] using
      UnroofedHalfwayRowLadder.deferred_halfwayGeometry
        preferred hregular huncountable hNoEnter
  rw [← iUnion_closedAt_eq_globalCarrier hkappa hGamma hseed]
  exact closedUnderPaths_limitWarp_iUnion_of_causalStages
    (finalLadder Gamma kappa hkappa hGamma seed hseed) hlegal
    (closedAt Gamma kappa hkappa hGamma seed hseed)
    (closedAt_mono hkappa hGamma hseed)
    (causalStagePathClosure hkappa hGamma hseed)

theorem globalCarrier_subset_limitRoof
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa) :
    globalCarrier Gamma kappa hkappa hGamma seed hseed ⊆
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitRoof := by
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (hGamma hxy).1 hy
  exact DWeb.UnroofedMarker.causalCarrier_subset_limitRoof Gamma
    (rule Gamma kappa hkappa hGamma seed hseed) hNoEnter
    (Cardinal.isRegular_succ hkappa) (hkappa.trans_lt (lt_succ kappa))

#print axioms CausalSection9Rows.mk_historyIncrement_le
#print axioms CausalSection9Rows.mk_targetIncrement_le_succ
#print axioms CausalSection9Rows.mk_increment_le_succ
#print axioms CausalSection9Rows.seed_subset_globalCarrier
#print axioms CausalSection9Rows.safeStageTargetChoice_support_subset_rowAt
#print axioms CausalSection9Rows.exists_later_safeStageTargetChoice
#print axioms CausalSection9Rows.chosen_support_subset_globalCarrier
#print axioms CausalSection9Rows.markerSet_subset_globalCarrier
#print axioms CausalSection9Rows.hammockClosedAt
#print axioms CausalSection9Rows.hammockClosedAt_succ
#print axioms CausalSection9Rows.reference_closed
#print axioms CausalSection9Rows.globalCarrier_subset_limitRoof

end CausalSection9Rows
end Erdos599.Blueprint.LinkageBlueprint
