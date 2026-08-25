/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos76.FiniteBernoulliVariance
import ErdosProblems.Erdos76.FiniteBernoulliBoundedDifferences
import ErdosProblems.Erdos76.FiniteProductBoundedDifferences
import ErdosProblems.Erdos76.FiniteLocalLemma
import ErdosProblems.Erdos76.HypergraphGreedyColoring
import ErdosProblems.Erdos76.PippengerSpencerEdgeColoring
import ErdosProblems.Erdos76.PippengerSpencerParameters
import Mathlib.Tactic

/-!
# One-round invariants for Pippenger--Spencer

This module sits downstream of both the elementary hypergraph bookkeeping
and the finite Bernoulli variance calculation.  It specializes the generic
penalized averaging theorem to the residual-degree loss coefficients of a
uniform hypergraph.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FiniteHypergraph

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ### Finite restrictions used by the outer iteration -/

/-- Restrict simultaneously to a finite active vertex set and a finite
family of original indexed edges whose supports lie in that set. -/
def restrictTo (H : FiniteHypergraph V E) (A : Finset V) (R : Finset E)
    (hR : ∀ e ∈ R, H.support e ⊆ A) : FiniteHypergraph V ↥R where
  vertexSet := A
  support e := H.support e.1
  support_subset_vertexSet e := hR e.1 e.2

@[simp] lemma restrictTo_vertexSet (H : FiniteHypergraph V E)
    (A : Finset V) (R : Finset E) (hR : ∀ e ∈ R, H.support e ⊆ A) :
    (H.restrictTo A R hR).vertexSet = A := rfl

@[simp] lemma restrictTo_support (H : FiniteHypergraph V E)
    (A : Finset V) (R : Finset E) (hR : ∀ e ∈ R, H.support e ⊆ A)
    (e : ↥R) :
    (H.restrictTo A R hR).support e = H.support e.1 := rfl

lemma restrictTo_isUniform {H : FiniteHypergraph V E} {A : Finset V}
    {R : Finset E} {hR : ∀ e ∈ R, H.support e ⊆ A} {k : ℕ}
    (hunif : H.IsUniform k) :
    (H.restrictTo A R hR).IsUniform k := fun e ↦ hunif e.1

/-- Forget the restriction proof on a selected edge family. -/
def liftRestrictedEdges {R : Finset E} (M : Finset ↥R) : Finset E :=
  M.image Subtype.val

@[simp] lemma mem_liftRestrictedEdges {R : Finset E} {M : Finset ↥R} {e : E} :
    e ∈ liftRestrictedEdges M ↔ ∃ he : e ∈ R, (⟨e, he⟩ : ↥R) ∈ M := by
  simp [liftRestrictedEdges]

@[simp] lemma card_liftRestrictedEdges {R : Finset E} (M : Finset ↥R) :
    (liftRestrictedEdges M).card = M.card := by
  exact card_image_of_injective M Subtype.val_injective

lemma isMatching_liftRestrictedEdges
    {H : FiniteHypergraph V E} {A : Finset V} {R : Finset E}
    {hR : ∀ e ∈ R, H.support e ⊆ A} {M : Finset ↥R}
    (hM : (H.restrictTo A R hR).IsMatching M) :
    H.IsMatching (liftRestrictedEdges M) := by
  intro e he f hf hef
  obtain ⟨heR, heM⟩ := mem_liftRestrictedEdges.mp he
  obtain ⟨hfR, hfM⟩ := mem_liftRestrictedEdges.mp hf
  apply hM heM hfM
  intro h
  exact hef (congrArg Subtype.val h)

lemma edgeDegree_restrictTo_le
    (H : FiniteHypergraph V E) (A : Finset V) (R : Finset E)
    (hR : ∀ e ∈ R, H.support e ⊆ A) (v : V) :
    (H.restrictTo A R hR).edgeDegree v ≤ H.edgeDegree v := by
  let F : Finset ↥R := (univ : Finset ↥R).filter fun e ↦
    v ∈ (H.restrictTo A R hR).support e
  let G : Finset E := (univ : Finset E).filter fun e ↦ v ∈ H.support e
  let phi : ↥F → ↥G := fun e ↦ ⟨e.1.1, by
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp e.2).2⟩⟩
  have hphi : Function.Injective phi := by
    intro e f hef
    have hval : e.1.1 = f.1.1 :=
      congrArg (fun z : ↥G ↦ z.1) hef
    exact Subtype.ext (Subtype.ext hval)
  have hc := Fintype.card_le_of_injective phi hphi
  simpa only [edgeDegree, Fintype.card_coe, F, G] using hc

lemma edgePairDegree_restrictTo_le
    (H : FiniteHypergraph V E) (A : Finset V) (R : Finset E)
    (hR : ∀ e ∈ R, H.support e ⊆ A) (u v : V) :
    (H.restrictTo A R hR).edgePairDegree u v ≤ H.edgePairDegree u v := by
  let F : Finset ↥R := (univ : Finset ↥R).filter fun e ↦
    u ∈ (H.restrictTo A R hR).support e ∧
      v ∈ (H.restrictTo A R hR).support e
  let G : Finset E := (univ : Finset E).filter fun e ↦
    u ∈ H.support e ∧ v ∈ H.support e
  let phi : ↥F → ↥G := fun e ↦ ⟨e.1.1, by
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp e.2).2⟩⟩
  have hphi : Function.Injective phi := by
    intro e f hef
    have hval : e.1.1 = f.1.1 :=
      congrArg (fun z : ↥G ↦ z.1) hef
    exact Subtype.ext (Subtype.ext hval)
  have hc := Fintype.card_le_of_injective phi hphi
  simpa only [edgePairDegree, Fintype.card_coe, F, G] using hc

/-- The coefficient family whose Bernoulli sum is the raw off-vertex
conflict load. -/
def offConflictCoefficient (H : FiniteHypergraph V E) :
    (↥H.vertexSet) → E → ℝ :=
  fun v e ↦ (H.offConflictLink v.1 e : ℝ)

/-- The weighted centered Bernoulli sum for the off-conflict coefficients is
exactly raw conflict load minus its expectation. -/
lemma weightedCenteredSum_offConflictCoefficient
    (H : FiniteHypergraph V E) (p : E → ℝ) (S : Finset E)
    (v : ↥H.vertexSet) :
    FiniteNibble.weightedCenteredSum univ p
        (H.offConflictCoefficient v) S =
      (H.sampleConflictLoad v.1 S : ℝ) -
        ∑ e, (H.offConflictLink v.1 e : ℝ) * p e := by
  change (∑ e, (H.offConflictLink v.1 e : ℝ) *
      ((if e ∈ S then 1 else 0) - p e)) =
    (↑(∑ e ∈ S, H.offConflictLink v.1 e) : ℝ) -
      ∑ e, (H.offConflictLink v.1 e : ℝ) * p e
  have hindicator :
      (∑ e, (H.offConflictLink v.1 e : ℝ) *
        (if e ∈ S then 1 else 0)) =
        (↑(∑ e ∈ S, H.offConflictLink v.1 e) : ℝ) := by
    calc
      (∑ e, (H.offConflictLink v.1 e : ℝ) *
          (if e ∈ S then 1 else 0)) =
          ∑ e, if e ∈ S then (H.offConflictLink v.1 e : ℝ) else 0 := by
        apply sum_congr rfl
        intro e _
        by_cases he : e ∈ S <;> simp [he]
      _ = ∑ e ∈ S, (H.offConflictLink v.1 e : ℝ) := by
        rw [← sum_filter]
        simp
      _ = (↑(∑ e ∈ S, H.offConflictLink v.1 e) : ℝ) := by
        push_cast
        rfl
  calc
    (∑ e, (H.offConflictLink v.1 e : ℝ) *
        ((if e ∈ S then 1 else 0) - p e)) =
        (∑ e, (H.offConflictLink v.1 e : ℝ) *
          (if e ∈ S then 1 else 0)) -
          ∑ e, (H.offConflictLink v.1 e : ℝ) * p e := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro e _
      ring
    _ = _ := by rw [hindicator]

/-- With constant sampling probability `tau / D`, the expected raw
off-conflict load is the same factor times the total coefficient. -/
lemma expected_offConflictLoad_const (H : FiniteHypergraph V E)
    (tau : ℝ) (D : ℕ) (v : V) :
    (∑ e, (H.offConflictLink v e : ℝ) * (tau / (D : ℝ))) =
      (tau / (D : ℝ)) * ∑ e, H.offConflictLink v e := by
  push_cast
  rw [mul_sum]
  apply sum_congr rfl
  intro e _
  push_cast
  ring

/-- Sampled edges removed by the isolation alteration. -/
def discardedSample (H : FiniteHypergraph V E) (S : Finset E) : Finset E :=
  S \ H.isolatedSample S

lemma isolatedSample_union_discardedSample (H : FiniteHypergraph V E)
    (S : Finset E) :
    H.isolatedSample S ∪ H.discardedSample S = S := by
  rw [discardedSample, union_sdiff_of_subset (H.isolatedSample_subset S)]

lemma disjoint_isolatedSample_discardedSample (H : FiniteHypergraph V E)
    (S : Finset E) :
    Disjoint (H.isolatedSample S) (H.discardedSample S) := by
  exact Finset.disjoint_sdiff

/-- Every edge discarded by alteration participates in at least one ordered
collision, so the number discarded is at most the ordered collision count. -/
lemma discardedSample_card_le_collisionCount (H : FiniteHypergraph V E)
    (S : Finset E) :
    (H.discardedSample S).card ≤ H.collisionCount S := by
  have hpositive : ∀ f ∈ H.discardedSample S,
      1 ≤ (S.filter fun g ↦ H.Conflicts f g).card := by
    intro f hf
    have hfS : f ∈ S := (mem_sdiff.mp hf).1
    have hfnot : f ∉ H.isolatedSample S := (mem_sdiff.mp hf).2
    simp only [isolatedSample, mem_filter, hfS, true_and] at hfnot
    push_neg at hfnot
    obtain ⟨g, hgS, hfg, hnd⟩ := hfnot
    have hg : g ∈ S.filter fun g ↦ H.Conflicts f g :=
      mem_filter.mpr ⟨hgS, hfg, hnd⟩
    exact card_pos.mpr ⟨g, hg⟩
  calc
    (H.discardedSample S).card = ∑ _f ∈ H.discardedSample S, 1 := by simp
    _ ≤ ∑ f ∈ H.discardedSample S,
        (S.filter fun g ↦ H.Conflicts f g).card := sum_le_sum hpositive
    _ ≤ ∑ f ∈ S, (S.filter fun g ↦ H.Conflicts f g).card := by
      exact sum_le_sum_of_subset_of_nonneg (sdiff_subset)
        (fun _ _ _ ↦ Nat.zero_le _)
    _ = H.collisionCount S := rfl

/-- The off-conflict load splits exactly into its isolated and discarded
parts. -/
lemma sampleConflictLoad_isolated_add_discarded
    (H : FiniteHypergraph V E) (v : V) (S : Finset E) :
    H.sampleConflictLoad v (H.isolatedSample S) +
        H.sampleConflictLoad v (H.discardedSample S) =
      H.sampleConflictLoad v S := by
  simp only [sampleConflictLoad]
  rw [← sum_union (H.disjoint_isolatedSample_discardedSample S),
    H.isolatedSample_union_discardedSample S]

/-- Globally, the off-conflict load lost during alteration is charged to
ordered collisions.  Each discarded edge has at most `k D` conflicts, and
each conflict contributes at most `k` vertex incidences. -/
lemma sum_discardedSample_conflictLoad_le
    {H : FiniteHypergraph V E} {k D : ℕ} (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) (S : Finset E) :
    ∑ v ∈ H.vertexSet, H.sampleConflictLoad v (H.discardedSample S) ≤
      H.collisionCount S * (k * (k * D)) := by
  calc
    ∑ v ∈ H.vertexSet, H.sampleConflictLoad v (H.discardedSample S) =
        ∑ f ∈ H.discardedSample S,
          ∑ v ∈ H.vertexSet, H.offConflictLink v f := by
      simp only [sampleConflictLoad]
      rw [sum_comm]
    _ ≤ ∑ _f ∈ H.discardedSample S, k * (k * D) := by
      apply sum_le_sum
      intro f hf
      calc
        ∑ v ∈ H.vertexSet, H.offConflictLink v f ≤
            k * H.conflictDegree f := H.sum_vertexSet_offConflictLink_le hunif f
        _ ≤ k * (k * D) := Nat.mul_le_mul_left k
          (H.conflictDegree_le_uniform_mul hunif hdeg f)
    _ = (H.discardedSample S).card * (k * (k * D)) := by simp
    _ ≤ H.collisionCount S * (k * (k * D)) :=
      Nat.mul_le_mul_right _ (H.discardedSample_card_le_collisionCount S)

/-- Vertices at which alteration discards at least `r` units of raw
off-conflict load. -/
def collisionHeavyVertices (H : FiniteHypergraph V E) (r : ℕ)
    (S : Finset E) : Finset ↥H.vertexSet :=
  (univ : Finset ↥H.vertexSet).filter fun v ↦
    r ≤ H.sampleConflictLoad v.1 (H.discardedSample S)

lemma mul_card_collisionHeavyVertices_le
    {H : FiniteHypergraph V E} {k D r : ℕ} (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) (S : Finset E) :
    r * (H.collisionHeavyVertices r S).card ≤
      H.collisionCount S * (k * (k * D)) := by
  calc
    r * (H.collisionHeavyVertices r S).card =
        ∑ _v ∈ H.collisionHeavyVertices r S, r := by
      simp [mul_comm]
    _ ≤ ∑ v ∈ H.collisionHeavyVertices r S,
        H.sampleConflictLoad v.1 (H.discardedSample S) := by
      apply sum_le_sum
      intro v hv
      exact (mem_filter.mp hv).2
    _ ≤ ∑ v : ↥H.vertexSet,
        H.sampleConflictLoad v.1 (H.discardedSample S) := by
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _)
        (fun _ _ _ ↦ Nat.zero_le _)
    _ = ∑ v ∈ H.vertexSet,
        H.sampleConflictLoad v (H.discardedSample S) := by
      rw [sum_subtype H.vertexSet (fun _ ↦ Iff.rfl)]
    _ ≤ H.collisionCount S * (k * (k * D)) :=
      H.sum_discardedSample_conflictLoad_le hunif hdeg S

/-- Vertices whose raw off-conflict load deviates from its Bernoulli mean by
at least `t` in squared distance. -/
def offConflictDeviationVertices (H : FiniteHypergraph V E) (p : E → ℝ)
    (t : ℝ) (S : Finset E) : Finset ↥H.vertexSet :=
  (univ : Finset ↥H.vertexSet).filter fun v ↦
    t ^ 2 ≤ FiniteNibble.weightedCenteredSum univ p
      (H.offConflictCoefficient v) S ^ 2

@[simp] lemma card_offConflictDeviationVertices
    (H : FiniteHypergraph V E) (p : E → ℝ) (t : ℝ) (S : Finset E) :
    (H.offConflictDeviationVertices p t S).card =
      FiniteNibble.weightedDeviationCount univ p
        H.offConflictCoefficient t S := rfl

/-- Vertices discarded after a round: either the raw load deviated, or too
much of that load came from sampled edges removed by alteration. -/
def nibbleExceptionalVertices (H : FiniteHypergraph V E) (p : E → ℝ)
    (t : ℝ) (r : ℕ) (S : Finset E) : Finset ↥H.vertexSet :=
  H.offConflictDeviationVertices p t S ∪ H.collisionHeavyVertices r S

/-- Away from the deviation set and the collision-heavy set, the accepted
matching load differs from the raw Bernoulli mean only by the declared
deviation and alteration budgets. -/
lemma isolatedSample_conflictLoad_bounds
    (H : FiniteHypergraph V E) (p : E → ℝ) {t : ℝ} (ht : 0 < t)
    {r : ℕ} (S : Finset E) (v : ↥H.vertexSet)
    (hdev : v ∉ H.offConflictDeviationVertices p t S)
    (hheavy : v ∉ H.collisionHeavyVertices r S) :
    (∑ e, (H.offConflictLink v.1 e : ℝ) * p e) - t - r <
        (H.sampleConflictLoad v.1 (H.isolatedSample S) : ℝ) ∧
      (H.sampleConflictLoad v.1 (H.isolatedSample S) : ℝ) <
        (∑ e, (H.offConflictLink v.1 e : ℝ) * p e) + t := by
  have hsq :
      (FiniteNibble.weightedCenteredSum univ p
        (H.offConflictCoefficient v) S) ^ 2 < t ^ 2 := by
    simpa only [offConflictDeviationVertices, mem_filter, mem_univ, true_and,
      not_le] using hdev
  rw [H.weightedCenteredSum_offConflictCoefficient] at hsq
  have habs :
      |(H.sampleConflictLoad v.1 S : ℝ) -
        ∑ e, (H.offConflictLink v.1 e : ℝ) * p e| < t := by
    rw [abs_lt]
    constructor <;> nlinarith
  have hdiscard : H.sampleConflictLoad v.1 (H.discardedSample S) < r := by
    simpa only [collisionHeavyVertices, mem_filter, mem_univ, true_and,
      not_le] using hheavy
  have hsplit := H.sampleConflictLoad_isolated_add_discarded v.1 S
  have hsplitR :
      (H.sampleConflictLoad v.1 (H.isolatedSample S) : ℝ) +
          (H.sampleConflictLoad v.1 (H.discardedSample S) : ℝ) =
        (H.sampleConflictLoad v.1 S : ℝ) := by
    exact_mod_cast hsplit
  have hdiscardR :
      (H.sampleConflictLoad v.1 (H.discardedSample S) : ℝ) < (r : ℝ) := by
    exact_mod_cast hdiscard
  constructor
  · have hlower := (abs_lt.mp habs).1
    nlinarith
  · have hupper := (abs_lt.mp habs).2
    have hnonneg :
        (0 : ℝ) ≤ H.sampleConflictLoad v.1 (H.discardedSample S) := by
      positivity
    nlinarith

/-- Residual-degree sandwich at every nonexceptional uncovered vertex.  This
is the deterministic one-round invariant used by the outer iteration. -/
lemma residualDegree_bounds_of_not_mem_nibbleExceptionalVertices
    {H : FiniteHypergraph V E} {k : ℕ} (hunif : H.IsUniform k)
    (p : E → ℝ) {t : ℝ} (ht : 0 < t) {r : ℕ}
    (S : Finset E) (v : ↥H.vertexSet)
    (hv : H.UncoveredBy (H.isolatedSample S) v.1)
    (hgood : v ∉ H.nibbleExceptionalVertices p t r S) :
    ((H.edgeDegree v.1 : ℝ) <
        (H.residualDegree (H.isolatedSample S) v.1 : ℝ) +
          (∑ e, (H.offConflictLink v.1 e : ℝ) * p e) + t) ∧
      ((∑ e, (H.offConflictLink v.1 e : ℝ) * p e) - t - r <
        (k : ℝ) * ((H.edgeDegree v.1 : ℝ) -
          H.residualDegree (H.isolatedSample S) v.1)) := by
  have hnotdev : v ∉ H.offConflictDeviationVertices p t S := by
    exact fun hvbad ↦ hgood (mem_union_left _ hvbad)
  have hnotheavy : v ∉ H.collisionHeavyVertices r S := by
    exact fun hvbad ↦ hgood (mem_union_right _ hvbad)
  have hload := H.isolatedSample_conflictLoad_bounds p ht S v hnotdev hnotheavy
  have hlowerNat := H.edgeDegree_le_residualDegree_add_sampleConflictLoad
    (H.isolatedSample S) v.1 hv
  have hlowerR :
      (H.edgeDegree v.1 : ℝ) ≤
        (H.residualDegree (H.isolatedSample S) v.1 : ℝ) +
          H.sampleConflictLoad v.1 (H.isolatedSample S) := by
    exact_mod_cast hlowerNat
  have hdropNat := H.sampleConflictLoad_le_card_mul_degree_sub_residual
    hunif (H.isolatedSample_isMatching S) hv
  have hresle := H.residualDegree_le_edgeDegree (H.isolatedSample S) v.1
  have hdropR :
      (H.sampleConflictLoad v.1 (H.isolatedSample S) : ℝ) ≤
        (k : ℝ) * ((H.edgeDegree v.1 : ℝ) -
          H.residualDegree (H.isolatedSample S) v.1) := by
    calc
      (H.sampleConflictLoad v.1 (H.isolatedSample S) : ℝ) ≤
          (k * (H.edgeDegree v.1 -
            H.residualDegree (H.isolatedSample S) v.1) : ℕ) := by
        exact_mod_cast hdropNat
      _ = (k : ℝ) * ((H.edgeDegree v.1 : ℝ) -
          H.residualDegree (H.isolatedSample S) v.1) := by
        rw [Nat.cast_mul, Nat.cast_sub hresle]
  constructor <;> nlinarith

/-! ### Independent batches of altered samples -/

/-- Edges accepted by at least one colour trial in a batch.  Each individual
trial contributes an isolated sample, hence a matching. -/
def batchAcceptedEdges {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (X : J → Finset E) : Finset E :=
  (univ : Finset J).biUnion fun j ↦ H.isolatedSample (X j)

/-- Edges not accepted by any colour trial in the batch. -/
def batchResidualEdges {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (X : J → Finset E) : Finset E :=
  (univ : Finset E) \ H.batchAcceptedEdges X

/-- Accepted edges of the batch which contain `v`. -/
def batchCoveredAt {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (X : J → Finset E) (v : V) : Finset E :=
  (H.batchAcceptedEdges X).filter fun e ↦ v ∈ H.support e

/-- Degree of `v` in the edge family left after one batch. -/
def batchResidualDegree {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (X : J → Finset E) (v : V) : ℕ :=
  (H.batchResidualEdges X).filter (fun e ↦ v ∈ H.support e) |>.card

@[simp] lemma mem_batchAcceptedEdges {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (X : J → Finset E) (e : E) :
    e ∈ H.batchAcceptedEdges X ↔ ∃ j : J, e ∈ H.isolatedSample (X j) := by
  simp [batchAcceptedEdges]

/-- Choose one witnessing trial for every edge accepted somewhere in a
nonempty batch.  Its value on unaccepted edges is irrelevant. -/
def batchOwner {J : Type*} [Fintype J] [Nonempty J]
    (H : FiniteHypergraph V E) (X : J → Finset E) (e : E) : J :=
  if he : e ∈ H.batchAcceptedEdges X then
    Classical.choose ((H.mem_batchAcceptedEdges X e).mp he)
  else Classical.choice inferInstance

lemma batchOwner_mem_isolatedSample
    {J : Type*} [Fintype J] [Nonempty J]
    (H : FiniteHypergraph V E) (X : J → Finset E) {e : E}
    (he : e ∈ H.batchAcceptedEdges X) :
    e ∈ H.isolatedSample (X (H.batchOwner X e)) := by
  unfold batchOwner
  rw [dif_pos he]
  exact Classical.choose_spec ((H.mem_batchAcceptedEdges X e).mp he)

/-- Accepted edges assigned to a specified batch color. -/
def batchColorClass {J : Type*} [Fintype J] [Nonempty J]
    (H : FiniteHypergraph V E) (X : J → Finset E) (j : J) : Finset E :=
  (H.batchAcceptedEdges X).filter fun e ↦ H.batchOwner X e = j

@[simp] lemma mem_batchColorClass
    {J : Type*} [Fintype J] [Nonempty J]
    (H : FiniteHypergraph V E) (X : J → Finset E) (j : J) (e : E) :
    e ∈ H.batchColorClass X j ↔
      e ∈ H.batchAcceptedEdges X ∧ H.batchOwner X e = j := by
  simp [batchColorClass]

/-- Every assigned batch color class is a matching, since it is a subset of
the isolated sample of its owner trial. -/
lemma batchColorClass_isMatching
    {J : Type*} [Fintype J] [Nonempty J]
    (H : FiniteHypergraph V E) (X : J → Finset E) (j : J) :
    H.IsMatching (H.batchColorClass X j) := by
  intro e he f hf hef
  have he' := (H.mem_batchColorClass X j e).mp he
  have hf' := (H.mem_batchColorClass X j f).mp hf
  have heIso := H.batchOwner_mem_isolatedSample X he'.1
  have hfIso := H.batchOwner_mem_isolatedSample X hf'.1
  rw [he'.2] at heIso
  rw [hf'.2] at hfIso
  exact H.isolatedSample_isMatching (X j) heIso hfIso hef

/-- The assigned color classes partition precisely the accepted edges. -/
lemma biUnion_batchColorClass
    {J : Type*} [Fintype J] [Nonempty J]
    (H : FiniteHypergraph V E) (X : J → Finset E) :
    (univ : Finset J).biUnion (H.batchColorClass X) = H.batchAcceptedEdges X := by
  ext e
  constructor
  · intro he
    obtain ⟨j, hj, hej⟩ := mem_biUnion.mp he
    exact (H.mem_batchColorClass X j e).mp hej |>.1
  · intro he
    apply mem_biUnion.mpr
    exact ⟨H.batchOwner X e, mem_univ _,
      (H.mem_batchColorClass X (H.batchOwner X e) e).mpr ⟨he, rfl⟩⟩

lemma disjoint_batchColorClass
    {J : Type*} [Fintype J] [Nonempty J]
    (H : FiniteHypergraph V E) (X : J → Finset E) {i j : J} (hij : i ≠ j) :
    Disjoint (H.batchColorClass X i) (H.batchColorClass X j) := by
  rw [Finset.disjoint_left]
  intro e hei hej
  have hi := (H.mem_batchColorClass X i e).mp hei |>.2
  have hj := (H.mem_batchColorClass X j e).mp hej |>.2
  exact hij (hi.symm.trans hj)

lemma batchResidualDegree_add_coveredAt
    {J : Type*} [Fintype J] (H : FiniteHypergraph V E)
    (X : J → Finset E) (v : V) :
    H.batchResidualDegree X v + (H.batchCoveredAt X v).card = H.edgeDegree v := by
  let A : Finset E := H.batchAcceptedEdges X
  let R : Finset E := ((univ : Finset E) \ A).filter fun e ↦ v ∈ H.support e
  let C : Finset E := A.filter fun e ↦ v ∈ H.support e
  have hdisj : Disjoint R C := by
    rw [Finset.disjoint_left]
    intro e heR heC
    exact (mem_sdiff.mp (mem_filter.mp heR).1).2 (mem_filter.mp heC).1
  have hunion : R ∪ C = (univ : Finset E).filter fun e ↦ v ∈ H.support e := by
    ext e
    simp only [R, C, mem_union, mem_filter, mem_sdiff, mem_univ, true_and]
    tauto
  change R.card + C.card = H.edgeDegree v
  rw [← card_union_of_disjoint hdisj, hunion]
  rfl

lemma batchResidualDegree_le_edgeDegree
    {J : Type*} [Fintype J] (H : FiniteHypergraph V E)
    (X : J → Finset E) (v : V) :
    H.batchResidualDegree X v ≤ H.edgeDegree v := by
  have hsplit := H.batchResidualDegree_add_coveredAt X v
  omega

/-- A matching contains at most one edge through a fixed vertex. -/
lemma card_filter_isolatedSample_mem_support_le_one
    (H : FiniteHypergraph V E) (S : Finset E) (v : V) :
    ((H.isolatedSample S).filter fun e ↦ v ∈ H.support e).card ≤ 1 := by
  rw [card_le_one]
  intro e he f hf
  have heM := (mem_filter.mp he).1
  have hfM := (mem_filter.mp hf).1
  by_contra hef
  have hd := H.isolatedSample_isMatching S heM hfM hef
  exact (Finset.disjoint_left.mp hd) (mem_filter.mp he).2 (mem_filter.mp hf).2

/-- Replacing one whole colour trial changes a residual vertex degree by at
most one.  This is the crucial Lipschitz-one fact: treating all Bernoulli
choices inside a trial as a single product coordinate avoids a factor `D`
in the concentration exponent. -/
lemma abs_batchResidualDegree_update_sub_le_one
    {J : Type*} [Fintype J] [DecidableEq J]
    (H : FiniteHypergraph V E) (X : J → Finset E)
    (j : J) (T : Finset E) (v : V) :
    |(H.batchResidualDegree (Function.update X j T) v : ℝ) -
      (H.batchResidualDegree X v : ℝ)| ≤ 1 := by
  let A : Finset E := H.batchCoveredAt X v
  let B : Finset E := H.batchCoveredAt (Function.update X j T) v
  let C : Finset E := (H.isolatedSample T).filter fun e ↦ v ∈ H.support e
  let C₀ : Finset E := (H.isolatedSample (X j)).filter fun e ↦ v ∈ H.support e
  have hBA : B ⊆ A ∪ C := by
    intro e heB
    have heAcc := (mem_filter.mp heB).1
    have hev := (mem_filter.mp heB).2
    obtain ⟨i, hei⟩ := (H.mem_batchAcceptedEdges _ e).mp heAcc
    by_cases hij : i = j
    · subst i
      exact mem_union_right _ (mem_filter.mpr ⟨by simpa using hei, hev⟩)
    · apply mem_union_left
      apply mem_filter.mpr
      refine ⟨(H.mem_batchAcceptedEdges X e).mpr ⟨i, ?_⟩, hev⟩
      simpa [Function.update, hij] using hei
  have hAB : A ⊆ B ∪ C₀ := by
    intro e heA
    have heAcc := (mem_filter.mp heA).1
    have hev := (mem_filter.mp heA).2
    obtain ⟨i, hei⟩ := (H.mem_batchAcceptedEdges _ e).mp heAcc
    by_cases hij : i = j
    · subst i
      exact mem_union_right _ (mem_filter.mpr ⟨hei, hev⟩)
    · apply mem_union_left
      apply mem_filter.mpr
      refine ⟨(H.mem_batchAcceptedEdges (Function.update X j T) e).mpr ⟨i, ?_⟩, hev⟩
      simpa [Function.update, hij] using hei
  have hC : C.card ≤ 1 := H.card_filter_isolatedSample_mem_support_le_one T v
  have hC₀ : C₀.card ≤ 1 := H.card_filter_isolatedSample_mem_support_le_one (X j) v
  have hBcard : B.card ≤ A.card + 1 := by
    calc
      B.card ≤ (A ∪ C).card := card_le_card hBA
      _ ≤ A.card + C.card := card_union_le A C
      _ ≤ A.card + 1 := Nat.add_le_add_left hC _
  have hAcard : A.card ≤ B.card + 1 := by
    calc
      A.card ≤ (B ∪ C₀).card := card_le_card hAB
      _ ≤ B.card + C₀.card := card_union_le B C₀
      _ ≤ B.card + 1 := Nat.add_le_add_left hC₀ _
  have hsplitA := H.batchResidualDegree_add_coveredAt X v
  have hsplitB := H.batchResidualDegree_add_coveredAt (Function.update X j T) v
  dsimp [A, B] at hAcard hBcard
  have hforward : H.batchResidualDegree (Function.update X j T) v ≤
      H.batchResidualDegree X v + 1 := by
    omega
  have hbackward : H.batchResidualDegree X v ≤
      H.batchResidualDegree (Function.update X j T) v + 1 := by
    omega
  rw [abs_le]
  constructor
  · have hbackwardR : (H.batchResidualDegree X v : ℝ) ≤
        (H.batchResidualDegree (Function.update X j T) v : ℝ) + 1 := by
      exact_mod_cast hbackward
    linarith

  · have hforwardR :
        (H.batchResidualDegree (Function.update X j T) v : ℝ) ≤
          (H.batchResidualDegree X v : ℝ) + 1 := by
      exact_mod_cast hforward
    linarith

/-- As a function of the independent colour trials, the residual degree at
one vertex has bounded differences one in every whole-trial coordinate. -/
lemma batchResidualDegree_hasBoundedDifferences
    {J : Type*} [Fintype J] [DecidableEq J]
    (H : FiniteHypergraph V E) (v : V) :
    FiniteProduct.HasBoundedDifferences
      (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ))
      (fun _ : J ↦ (1 : ℝ)) := by
  intro j X T
  exact H.abs_batchResidualDegree_update_sub_le_one X j T v

/-- McDiarmid concentration for the residual degree left by a nonempty
finite batch.  Notice that the variance proxy is the number of trials, not
the number of Bernoulli edge coordinates inside the trials. -/
theorem upperTailMass_batchResidualDegree_le
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (H : FiniteHypergraph V E) (v : V)
    (w : J → Finset E → ℝ)
    (hw₀ : ∀ j S, 0 ≤ w j S) (hw : ∀ j, ∑ S, w j S = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    FiniteProduct.upperTailMass w
        (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ))
        (FiniteProduct.expectation w
            (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ)) + t) ≤
      Real.exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) := by
  have hcard : (0 : ℝ) < Fintype.card J := by
    exact_mod_cast Fintype.card_pos
  have hsquares :
      ∑ _j : J, ((1 : ℝ) ^ 2) = (Fintype.card J : ℝ) := by simp
  have htail := FiniteProduct.upperTailMass_le_mcdiarmid w
    (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ))
    (fun _ : J ↦ (1 : ℝ)) hw₀ hw
    (H.batchResidualDegree_hasBoundedDifferences v) ht
    (by simpa [hsquares] using hcard)
  simpa [hsquares] using htail

/-- The residual degree is the sum of the indicators of incident edges
which were accepted in none of the batch trials. -/
lemma batchResidualDegree_eq_sum_never_accepted
    {J : Type*} [Fintype J] [DecidableEq J]
    (H : FiniteHypergraph V E) (X : J → Finset E) (v : V) :
    (H.batchResidualDegree X v : ℝ) =
      ∑ e : E, if v ∈ H.support e ∧
          ∀ j : J, e ∉ H.isolatedSample (X j) then 1 else 0 := by
  unfold batchResidualDegree batchResidualEdges
  rw [show (∑ e : E, if v ∈ H.support e ∧
      ∀ j : J, e ∉ H.isolatedSample (X j) then (1 : ℝ) else 0) =
      (((univ : Finset E).filter (fun e ↦ v ∈ H.support e ∧
        ∀ j : J, e ∉ H.isolatedSample (X j))).card : ℝ) by simp]
  norm_cast
  apply congrArg Finset.card
  ext e
  simp [batchAcceptedEdges, and_comm]

lemma matching_card_le_vertexSet_div
    {H : FiniteHypergraph V E} {k : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k) {M : Finset E} (hM : H.IsMatching M) :
    (M.card : ℝ) ≤ (H.vertexSet.card : ℝ) / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [le_div_iff₀ hkR]
  have hnat := H.card_mul_matching_le_vertexSet hunif hM
  have hreal : (k : ℝ) * (M.card : ℝ) ≤ H.vertexSet.card := by
    exact_mod_cast hnat
  simpa [mul_comm] using hreal

end FiniteHypergraph

namespace FiniteNibble

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Probability mass that a fixed edge survives the alteration in one
Bernoulli colour trial. -/
def trialAcceptanceMass (H : FiniteHypergraph V E) (p : E → ℝ) (e : E) : ℝ :=
  ∑ S : Finset E, bernoulliMass univ p S *
    if e ∈ H.isolatedSample S then 1 else 0

lemma trialAcceptanceMass_nonneg
    (H : FiniteHypergraph V E) {p : E → ℝ}
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1) (e : E) :
    0 ≤ trialAcceptanceMass H p e := by
  unfold trialAcceptanceMass
  exact sum_nonneg fun S _ ↦ mul_nonneg
    (bernoulliMass_nonneg (subset_univ S)
      (fun x _ ↦ hp₀ x) (fun x _ ↦ hp₁ x))
    (by split <;> norm_num)

lemma trialAcceptanceMass_le_one
    (H : FiniteHypergraph V E) {p : E → ℝ}
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1) (e : E) :
    trialAcceptanceMass H p e ≤ 1 := by
  calc
    trialAcceptanceMass H p e ≤ ∑ S : Finset E, bernoulliMass univ p S := by
      unfold trialAcceptanceMass
      apply sum_le_sum
      intro S hS
      have hm := bernoulliMass_nonneg (subset_univ S)
        (fun x _ ↦ hp₀ x) (fun x _ ↦ hp₁ x)
      split
      · simp
      · simp [hm]
    _ = 1 := by simpa using sum_bernoulliMass (univ : Finset E) p

/-- The mass of outcomes in which an edge is not accepted in one altered
trial is the complement of its acceptance mass. -/
lemma sum_bernoulliMass_not_mem_isolatedSample
    (H : FiniteHypergraph V E) {p : E → ℝ}
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1) (e : E) :
    (∑ S : Finset E, bernoulliMass univ p S *
        if e ∉ H.isolatedSample S then 1 else 0) =
      1 - trialAcceptanceMass H p e := by
  have hsum : ∑ S : Finset E, bernoulliMass univ p S = 1 := by
    simpa using sum_bernoulliMass (univ : Finset E) p
  calc
    (∑ S : Finset E, bernoulliMass univ p S *
        if e ∉ H.isolatedSample S then 1 else 0) =
        (∑ S : Finset E, bernoulliMass univ p S) -
          ∑ S : Finset E, bernoulliMass univ p S *
            if e ∈ H.isolatedSample S then 1 else 0 := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro S hS
      by_cases he : e ∈ H.isolatedSample S <;> simp [he]
    _ = 1 - trialAcceptanceMass H p e := by
      rw [hsum]
      rfl

/-- Independence across a homogeneous batch: the mass that a fixed edge is
never accepted is the corresponding one-trial rejection mass to the power
`|J|`. -/
lemma sum_productMass_never_accepted
    {J : Type*} [Fintype J] [DecidableEq J]
    (H : FiniteHypergraph V E) {p : E → ℝ}
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1) (e : E) :
    (∑ X : J → Finset E,
        FiniteProduct.productMass (bernoulliMass univ p) X *
          if ∀ j, e ∉ H.isolatedSample (X j) then 1 else 0) =
      (1 - trialAcceptanceMass H p e) ^ Fintype.card J := by
  have hpoint (X : J → Finset E) :
      FiniteProduct.productMass (bernoulliMass univ p) X *
          (if ∀ j, e ∉ H.isolatedSample (X j) then 1 else 0) =
        ∏ j : J, (bernoulliMass univ p (X j) *
          if e ∉ H.isolatedSample (X j) then 1 else 0) := by
    by_cases hall : ∀ j, e ∉ H.isolatedSample (X j)
    · rw [if_pos hall]
      simp only [FiniteProduct.productMass, mul_one]
      apply prod_congr rfl
      intro j hj
      simp [hall j]
    · rw [if_neg hall, mul_zero]
      push Not at hall
      obtain ⟨j, hj⟩ := hall
      symm
      apply (prod_eq_zero (mem_univ j))
      simp [hj]
  calc
    (∑ X : J → Finset E,
        FiniteProduct.productMass (bernoulliMass univ p) X *
          if ∀ j, e ∉ H.isolatedSample (X j) then 1 else 0) =
        ∑ X : J → Finset E, ∏ j : J,
          (bernoulliMass univ p (X j) *
            if e ∉ H.isolatedSample (X j) then 1 else 0) := by
      apply sum_congr rfl
      intro X hX
      exact hpoint X
    _ = ∏ _j : J, ∑ S : Finset E, bernoulliMass univ p S *
          if e ∉ H.isolatedSample S then 1 else 0 := by
      symm
      simpa using (Finset.prod_univ_sum
        (fun _j : J ↦ (univ : Finset (Finset E)))
        (fun _j : J ↦ fun S : Finset E ↦ bernoulliMass univ p S *
          if e ∉ H.isolatedSample S then 1 else 0))
    _ = ∏ _j : J, (1 - trialAcceptanceMass H p e) := by
      apply prod_congr rfl
      intro j hj
      exact sum_bernoulliMass_not_mem_isolatedSample H hp₀ hp₁ e
    _ = (1 - trialAcceptanceMass H p e) ^ Fintype.card J := by simp

/-- Exact expected residual degree after a homogeneous independent batch:
sum, over the incident edges, of the probability that no trial accepts that
edge. -/
lemma productExpectation_batchResidualDegree
    {J : Type*} [Fintype J] [DecidableEq J]
    (H : FiniteHypergraph V E) {p : E → ℝ}
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1) (v : V) :
    FiniteProduct.productExpectation (bernoulliMass univ p)
        (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ)) =
      ∑ e : E, if v ∈ H.support e then
        (1 - trialAcceptanceMass H p e) ^ Fintype.card J else 0 := by
  unfold FiniteProduct.productExpectation
  calc
    (∑ X : J → Finset E,
        FiniteProduct.productMass (bernoulliMass univ p) X *
          (H.batchResidualDegree X v : ℝ)) =
        ∑ X : J → Finset E, ∑ e : E,
          FiniteProduct.productMass (bernoulliMass univ p) X *
            if v ∈ H.support e ∧
                ∀ j : J, e ∉ H.isolatedSample (X j) then 1 else 0 := by
      apply sum_congr rfl
      intro X hX
      rw [H.batchResidualDegree_eq_sum_never_accepted]
      rw [mul_sum]
    _ = ∑ e : E, ∑ X : J → Finset E,
          FiniteProduct.productMass (bernoulliMass univ p) X *
            if v ∈ H.support e ∧
                ∀ j : J, e ∉ H.isolatedSample (X j) then 1 else 0 := sum_comm
    _ = ∑ e : E, if v ∈ H.support e then
          (1 - trialAcceptanceMass H p e) ^ Fintype.card J else 0 := by
      apply sum_congr rfl
      intro e he
      by_cases hev : v ∈ H.support e
      · rw [if_pos hev]
        simpa [hev] using
          (sum_productMass_never_accepted (J := J) H hp₀ hp₁ e)
      · simp [hev]

/-- A uniform lower bound on the one-trial acceptance mass gives geometric
decay of every vertex degree in expectation. -/
lemma productExpectation_batchResidualDegree_le
    {J : Type*} [Fintype J] [DecidableEq J]
    (H : FiniteHypergraph V E) {p : E → ℝ}
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1)
    {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (haccept : ∀ e, a ≤ trialAcceptanceMass H p e) (v : V) :
    FiniteProduct.productExpectation (bernoulliMass univ p)
        (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ)) ≤
      (H.edgeDegree v : ℝ) * (1 - a) ^ Fintype.card J := by
  rw [productExpectation_batchResidualDegree H hp₀ hp₁ v]
  calc
    (∑ e : E, if v ∈ H.support e then
        (1 - trialAcceptanceMass H p e) ^ Fintype.card J else 0) ≤
        ∑ e : E, if v ∈ H.support e then
          (1 - a) ^ Fintype.card J else 0 := by
      apply sum_le_sum
      intro e he
      by_cases hev : v ∈ H.support e
      · simp only [hev, if_true]
        exact pow_le_pow_left₀
          (sub_nonneg.mpr (trialAcceptanceMass_le_one H hp₀ hp₁ e))
          (sub_le_sub_left (haccept e) 1) _
      · simp [hev]
    _ = (H.edgeDegree v : ℝ) * (1 - a) ^ Fintype.card J := by
      rw [← sum_filter]
      simp only [sum_const, card_filter, nsmul_eq_mul]
      congr 1
      norm_cast
      simp [FiniteHypergraph.edgeDegree]

/-- Local union bound for one altered Bernoulli trial.  An edge is lost only
if it and at least one conflicting edge were both sampled. -/
lemma trialAcceptanceMass_ge
    (H : FiniteHypergraph V E) (p : E → ℝ)
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1) (e : E) :
    p e - (∑ f, if H.Conflicts e f then p e * p f else 0) ≤
      trialAcceptanceMass H p e := by
  let A : Finset E → ℝ := fun S ↦ if e ∈ S then 1 else 0
  let C : Finset E → ℝ := fun S ↦
    ∑ f, if e ∈ S ∧ f ∈ S ∧ H.Conflicts e f then 1 else 0
  let I : Finset E → ℝ := fun S ↦
    if e ∈ H.isolatedSample S then 1 else 0
  have hpoint : ∀ S : Finset E, A S - C S ≤ I S := by
    intro S
    by_cases heS : e ∈ S
    · by_cases heI : e ∈ H.isolatedSample S
      · have hC₀ : 0 ≤ C S := by
          dsimp [C]
          exact sum_nonneg fun f _ ↦ by split <;> norm_num
        simp only [A, I, heS, heI, if_true]
        linarith
      · have hnot : ¬∀ f ∈ S, e ≠ f → Disjoint (H.support e) (H.support f) := by
          intro hall
          exact heI (mem_filter.mpr ⟨heS, hall⟩)
        push Not at hnot
        obtain ⟨f, hfS, hef, hnd⟩ := hnot
        have hconf : H.Conflicts e f := ⟨hef, hnd⟩
        have hone : (1 : ℝ) ≤ C S := by
          calc
            (1 : ℝ) =
                (if e ∈ S ∧ f ∈ S ∧ H.Conflicts e f then 1 else 0) := by
                  simp [heS, hfS, hconf]
            _ ≤ ∑ x : E,
                if e ∈ S ∧ x ∈ S ∧ H.Conflicts e x then 1 else 0 := by
              refine single_le_sum
                (s := (univ : Finset E))
                (f := fun x ↦
                  if e ∈ S ∧ x ∈ S ∧ H.Conflicts e x then
                    (1 : ℝ) else 0) ?_ (mem_univ f)
              intro x hx
              split <;> norm_num
            _ = C S := by simp only [C]
        simp only [A, I, heS, heI, if_true, if_false]
        linarith
    · have heI : e ∉ H.isolatedSample S := fun h ↦
        heS (H.isolatedSample_subset S h)
      have hCzero : C S = 0 := by simp [C, heS]
      simp [A, I, heS, heI, hCzero]
  have hmass₀ : ∀ S : Finset E, 0 ≤ bernoulliMass univ p S := fun S ↦
    bernoulliMass_nonneg (subset_univ S) (fun x _ ↦ hp₀ x) (fun x _ ↦ hp₁ x)
  have hfirst : ∑ S : Finset E, bernoulliMass univ p S * A S = p e := by
    simp only [A, mul_ite, mul_one, mul_zero, ← sum_filter]
    simpa using sum_bernoulliMass_filter_mem
      (U := (univ : Finset E)) (p := p) (e := e) (mem_univ e)
  have hsecond : ∑ S : Finset E, bernoulliMass univ p S * C S =
      ∑ f, if H.Conflicts e f then p e * p f else 0 := by
    calc
      ∑ S : Finset E, bernoulliMass univ p S * C S =
          ∑ S : Finset E, ∑ f : E,
            if e ∈ S ∧ f ∈ S ∧ H.Conflicts e f then
              bernoulliMass univ p S else 0 := by
        apply sum_congr rfl
        intro S hS
        simp only [C, mul_sum, mul_ite, mul_one, mul_zero]
      _ = ∑ f : E, ∑ S : Finset E,
            if e ∈ S ∧ f ∈ S ∧ H.Conflicts e f then
              bernoulliMass univ p S else 0 := sum_comm
      _ = ∑ f, if H.Conflicts e f then p e * p f else 0 := by
        apply sum_congr rfl
        intro f hf
        by_cases hconf : H.Conflicts e f
        · simp only [hconf, and_true, if_true, ← sum_filter]
          simpa using sum_bernoulliMass_filter_mem_mem
            (U := (univ : Finset E)) (p := p) (e := e) (f := f)
            (mem_univ e) (mem_univ f) hconf.1
        · simp [hconf]
  calc
    p e - (∑ f, if H.Conflicts e f then p e * p f else 0) =
        ∑ S : Finset E, bernoulliMass univ p S * (A S - C S) := by
      simp only [mul_sub, sum_sub_distrib, hfirst, hsecond]
    _ ≤ ∑ S : Finset E, bernoulliMass univ p S * I S := by
      exact sum_le_sum fun S hS ↦
        mul_le_mul_of_nonneg_left (hpoint S) (hmass₀ S)
    _ = trialAcceptanceMass H p e := rfl

/-- Constant-probability consequence of the local union bound. -/
lemma trialAcceptanceMass_const_ge
    {H : FiniteHypergraph V E} {k D : ℕ} (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (e : E) :
    p - ((k * D : ℕ) : ℝ) * p ^ 2 ≤
      trialAcceptanceMass H (fun _ ↦ p) e := by
  have hlocal := trialAcceptanceMass_ge H (fun _ : E ↦ p)
    (fun _ ↦ hp₀) (fun _ ↦ hp₁) e
  have hconflict :
      (∑ f : E, if H.Conflicts e f then p * p else 0) =
        (H.conflictDegree e : ℝ) * p ^ 2 := by
    calc
      (∑ f : E, if H.Conflicts e f then p * p else 0) =
          ∑ f with H.Conflicts e f, p ^ 2 := by
        rw [sum_filter]
        apply sum_congr rfl
        intro f hf
        by_cases hconf : H.Conflicts e f <;> simp [hconf, pow_two]
      _ = (H.conflictDegree e : ℝ) * p ^ 2 := by
        simp [FiniteHypergraph.conflictDegree]
  rw [hconflict] at hlocal
  have hdegree : (H.conflictDegree e : ℝ) ≤ (k * D : ℕ) := by
    exact_mod_cast H.conflictDegree_le_uniform_mul hunif hdeg e
  have hmul : (H.conflictDegree e : ℝ) * p ^ 2 ≤
      ((k * D : ℕ) : ℝ) * p ^ 2 :=
    mul_le_mul_of_nonneg_right hdegree (sq_nonneg p)
  exact (sub_le_sub_left hmul p).trans hlocal

/-- Explicit geometric expectation bound obtained from the elementary
one-trial union bound `p - kD p²`. -/
lemma productExpectation_batchResidualDegree_const_le
    {J : Type*} [Fintype J] [DecidableEq J]
    {H : FiniteHypergraph V E} {k D : ℕ}
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (ha₀ : 0 ≤ p - ((k * D : ℕ) : ℝ) * p ^ 2)
    (ha₁ : p - ((k * D : ℕ) : ℝ) * p ^ 2 ≤ 1) (v : V) :
    FiniteProduct.productExpectation (bernoulliMass univ (fun _ : E ↦ p))
        (fun X : J → Finset E ↦ (H.batchResidualDegree X v : ℝ)) ≤
      (H.edgeDegree v : ℝ) *
        (1 - (p - ((k * D : ℕ) : ℝ) * p ^ 2)) ^ Fintype.card J := by
  exact productExpectation_batchResidualDegree_le H
    (fun _ ↦ hp₀) (fun _ ↦ hp₁) ha₀ ha₁
    (fun e ↦ trialAcceptanceMass_const_ge hunif hdeg hp₀ hp₁ e) v

/-- The ordered-collision expectation for constant sampling is bounded by
`|E| · kD · p²`. -/
lemma sum_conflictProbability_const_le
    {H : FiniteHypergraph V E} {k D : ℕ} (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) {p : ℝ} (hp : 0 ≤ p) :
    (∑ e, ∑ f, if H.Conflicts e f then p * p else 0) ≤
      (Fintype.card E : ℝ) * (k * D : ℕ) * p ^ 2 := by
  have hinner (e : E) :
      (∑ f, if H.Conflicts e f then p * p else 0) =
        (H.conflictDegree e : ℝ) * p ^ 2 := by
    calc
      (∑ f, if H.Conflicts e f then p * p else 0) =
          ∑ f with H.Conflicts e f, p ^ 2 := by
        rw [sum_filter]
        apply sum_congr rfl
        intro f _
        by_cases hef : H.Conflicts e f <;> simp [hef, pow_two]
      _ = (H.conflictDegree e : ℝ) * p ^ 2 := by
        simp [FiniteHypergraph.conflictDegree]
  calc
    (∑ e, ∑ f, if H.Conflicts e f then p * p else 0) =
        ∑ e, (H.conflictDegree e : ℝ) * p ^ 2 := by
      apply sum_congr rfl
      intro e _
      exact hinner e
    _ ≤ ∑ _e : E, ((k * D : ℕ) : ℝ) * p ^ 2 := by
      apply sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast H.conflictDegree_le_uniform_mul hunif hdeg e)
        (sq_nonneg p)
    _ = (Fintype.card E : ℝ) * (k * D : ℕ) * p ^ 2 := by
      simp only [sum_const, card_univ, nsmul_eq_mul]
      push_cast
      ring

/-- The aggregate variance numerator for the off-conflict coefficient
family is bounded explicitly by the maximum degree and pair-degree. -/
lemma sum_offConflictCoefficient_sq_mul_le
    {H : FiniteHypergraph V E} {k D C : ℕ} (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    (∑ v : ↥H.vertexSet, ∑ e,
        (H.offConflictCoefficient v e) ^ 2 * p * (1 - p)) ≤
      (H.vertexSet.card : ℝ) *
        (((k * C) * (D * (k * D)) : ℕ) : ℝ) * p * (1 - p) := by
  have hfactor : 0 ≤ p * (1 - p) :=
    mul_nonneg hp₀ (sub_nonneg.mpr hp₁)
  have hpoint (v : ↥H.vertexSet) :
      (∑ e, (H.offConflictCoefficient v e) ^ 2 * p * (1 - p)) ≤
        (((k * C) * (D * (k * D)) : ℕ) : ℝ) * p * (1 - p) := by
    have hsq := H.sum_offConflictLink_sq_le hunif hdeg hpair v.2
    have hsq' :
        ∑ e, (H.offConflictLink v.1 e) ^ 2 ≤
          (k * C) * (D * (k * D)) := by
      exact hsq.trans (Nat.mul_le_mul_left (k * C)
        (Nat.mul_le_mul_right (k * D) (hdeg v.1 v.2)))
    have hsqR :
        (∑ e, ((H.offConflictLink v.1 e : ℝ) ^ 2)) ≤
          (((k * C) * (D * (k * D)) : ℕ) : ℝ) := by
      exact_mod_cast hsq'
    calc
      (∑ e, (H.offConflictCoefficient v e) ^ 2 * p * (1 - p)) =
          (∑ e, (H.offConflictLink v.1 e : ℝ) ^ 2) *
            (p * (1 - p)) := by
        rw [sum_mul]
        apply sum_congr rfl
        intro e _
        simp only [FiniteHypergraph.offConflictCoefficient]
        ring
      _ ≤ (((k * C) * (D * (k * D)) : ℕ) : ℝ) *
          (p * (1 - p)) := mul_le_mul_of_nonneg_right hsqR hfactor
      _ = (((k * C) * (D * (k * D)) : ℕ) : ℝ) * p * (1 - p) := by ring
  calc
    (∑ v : ↥H.vertexSet, ∑ e,
        (H.offConflictCoefficient v e) ^ 2 * p * (1 - p)) ≤
        ∑ _v : ↥H.vertexSet,
          (((k * C) * (D * (k * D)) : ℕ) : ℝ) * p * (1 - p) :=
      sum_le_sum fun v _ ↦ hpoint v
    _ = (H.vertexSet.card : ℝ) *
        (((k * C) * (D * (k * D)) : ℕ) : ℝ) * p * (1 - p) := by
      simp only [sum_const, card_univ, nsmul_eq_mul, Fintype.card_coe]
      ring

/-- One Bernoulli nibble round, simultaneously optimizing the size of the
isolated matching and the number of vertices whose raw off-conflict load has
large squared deviation.  The unsimplified variance term is intentional:
subsequent applications may use either a uniform maximum-degree bound or a
sharper inhomogeneous estimate. -/
theorem exists_penalized_offConflict_nibble
    (H : FiniteHypergraph V E) {tau : ℝ} {D : ℕ} {t lambda : ℝ}
    (hD : 0 < D) (htau₀ : 0 ≤ tau) (htau₁ : tau ≤ 1)
    (ht : 0 < t) (hlambda : 0 ≤ lambda) :
    ∃ S : Finset E, H.IsMatching (H.isolatedSample S) ∧
      ((tau / (D : ℝ)) * (Fintype.card E : ℝ) -
        (∑ e, ∑ f, if H.Conflicts e f then
          (tau / (D : ℝ)) ^ 2 else 0)) -
        lambda * ((t ^ 2)⁻¹ *
          ∑ v : ↥H.vertexSet, ∑ e,
            (H.offConflictCoefficient v e) ^ 2 *
              (tau / (D : ℝ)) * (1 - tau / (D : ℝ))) ≤
      ((H.isolatedSample S).card : ℝ) -
        lambda * (weightedDeviationCount univ
          (fun _ : E ↦ tau / (D : ℝ)) H.offConflictCoefficient t S : ℝ) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hp₀ : ∀ _e : E, 0 ≤ tau / (D : ℝ) := fun _ ↦
    div_nonneg htau₀ hDR.le
  have hp₁ : ∀ _e : E, tau / (D : ℝ) ≤ 1 := by
    intro e
    calc
      tau / (D : ℝ) ≤ tau := by
        apply div_le_self htau₀
        exact_mod_cast hD
      _ ≤ 1 := htau₁
  obtain ⟨S, hM, hbound⟩ :=
    exists_isolatedSample_sub_weightedDeviationPenalty
      H (p := fun _ : E ↦ tau / (D : ℝ))
      (a := H.offConflictCoefficient) hp₀ hp₁ ht hlambda
  refine ⟨S, hM, ?_⟩
  simpa [pow_two, mul_comm] using hbound

/-- Penalized one-round extraction including both weighted load deviations
and ordered collisions. -/
theorem exists_isolatedSample_sub_deviation_collisionPenalty
    (H : FiniteHypergraph V E) {p : E → ℝ} {t q lambda : ℝ}
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1)
    (ht : 0 < t) (hq : 0 ≤ q) (hlambda : 0 ≤ lambda) :
    ∃ S : Finset E, H.IsMatching (H.isolatedSample S) ∧
      ((∑ e, p e) -
          (∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0)) -
        lambda *
          ((t ^ 2)⁻¹ * ∑ v : ↥H.vertexSet, ∑ e,
              (H.offConflictCoefficient v e) ^ 2 * p e * (1 - p e) +
            q * ∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0) ≤
      ((H.isolatedSample S).card : ℝ) - lambda *
        ((weightedDeviationCount univ p H.offConflictCoefficient t S : ℝ) +
          q * (H.collisionCount S : ℝ)) := by
  let mass : Finset E → ℝ := fun S ↦ bernoulliMass univ p S
  let reward : Finset E → ℝ := fun S ↦ ((H.isolatedSample S).card : ℝ)
  let penalty : Finset E → ℝ := fun S ↦
    (weightedDeviationCount univ p H.offConflictCoefficient t S : ℝ) +
      q * H.collisionScore S
  let rewardLower : ℝ :=
    (∑ e, p e) -
      (∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0)
  let penaltyUpper : ℝ :=
    (t ^ 2)⁻¹ * ∑ v : ↥H.vertexSet, ∑ e,
        (H.offConflictCoefficient v e) ^ 2 * p e * (1 - p e) +
      q * ∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0
  have hmass : ∀ S, 0 ≤ mass S := fun S ↦
    bernoulliMass_nonneg (subset_univ S) (fun e _ ↦ hp₀ e) (fun e _ ↦ hp₁ e)
  have hsum : ∑ S, mass S = 1 := by
    simpa [mass] using sum_bernoulliMass (univ : Finset E) p
  have hreward : rewardLower ≤ ∑ S, mass S * reward S := by
    simpa [mass, reward, rewardLower] using
      (sum_bernoulliMass_mul_isolatedSample_card_ge H p hp₀ hp₁)
  have hpenalty : ∑ S, mass S * penalty S ≤ penaltyUpper := by
    calc
      ∑ S, mass S * penalty S =
          (∑ S, mass S *
            (weightedDeviationCount univ p H.offConflictCoefficient t S : ℝ)) +
            q * (∑ S, mass S * H.collisionScore S) := by
        simp only [mass, penalty, mul_add, sum_add_distrib]
        congr 1
        rw [mul_sum]
        apply sum_congr rfl
        intro S _
        ring
      _ ≤ ((t ^ 2)⁻¹ * ∑ v : ↥H.vertexSet, ∑ e,
              (H.offConflictCoefficient v e) ^ 2 * p e * (1 - p e)) +
            q * (∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0) := by
        apply add_le_add
        · simpa [mass] using
            (sum_bernoulliMass_mul_weightedDeviationCount_le
              (U := (univ : Finset E)) (a := H.offConflictCoefficient)
              (fun e _ ↦ hp₀ e) (fun e _ ↦ hp₁ e) ht)
        · exact mul_le_mul_of_nonneg_left
            (le_of_eq (sum_bernoulliMass_mul_collisionScore H p)) hq
      _ = penaltyUpper := rfl
  obtain ⟨S, hS⟩ := exists_output_sub_penalty_ge mass reward penalty
    hmass hsum hreward hpenalty hlambda
  refine ⟨S, H.isolatedSample_isMatching S, ?_⟩
  simpa [reward, penalty, rewardLower, penaltyUpper] using hS

/-- Choosing the penalty multiplier `R/(2B)` turns the combined penalized
estimate into simultaneous progress and regularity: at least half the
expected alteration reward, and penalty at most the universal matching
upper bound divided by the multiplier. -/
theorem exists_isolatedSample_reward_and_penalty
    (H : FiniteHypergraph V E) {k : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k) {p : E → ℝ} {t q : ℝ}
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1)
    (ht : 0 < t) (hq : 0 ≤ q)
    (hR : 0 < (∑ e, p e) -
      (∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0))
    (hB : 0 <
      (t ^ 2)⁻¹ * ∑ v : ↥H.vertexSet, ∑ e,
          (H.offConflictCoefficient v e) ^ 2 * p e * (1 - p e) +
        q * ∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0) :
    ∃ S : Finset E, H.IsMatching (H.isolatedSample S) ∧
      (((∑ e, p e) -
          (∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0)) / 2 ≤
        ((H.isolatedSample S).card : ℝ)) ∧
      ((weightedDeviationCount univ p H.offConflictCoefficient t S : ℝ) +
          q * (H.collisionCount S : ℝ) ≤
        ((H.vertexSet.card : ℝ) / (k : ℝ)) /
          (((∑ e, p e) -
            (∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0)) /
            (2 * ((t ^ 2)⁻¹ * ∑ v : ↥H.vertexSet, ∑ e,
              (H.offConflictCoefficient v e) ^ 2 * p e * (1 - p e) +
              q * ∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0)))) := by
  let R : ℝ := (∑ e, p e) -
    (∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0)
  let B : ℝ := (t ^ 2)⁻¹ * ∑ v : ↥H.vertexSet, ∑ e,
      (H.offConflictCoefficient v e) ^ 2 * p e * (1 - p e) +
    q * ∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0
  let lambda : ℝ := R / (2 * B)
  have hR' : 0 < R := hR
  have hB' : 0 < B := hB
  have hlambda : 0 < lambda := div_pos hR' (mul_pos (by norm_num) hB')
  obtain ⟨S, hM, hmain⟩ :=
    exists_isolatedSample_sub_deviation_collisionPenalty H hp₀ hp₁ ht hq
      hlambda.le
  let Y : ℝ :=
    (weightedDeviationCount univ p H.offConflictCoefficient t S : ℝ) +
      q * (H.collisionCount S : ℝ)
  have hY : 0 ≤ Y := add_nonneg (Nat.cast_nonneg _)
    (mul_nonneg hq (Nat.cast_nonneg _))
  have hlambdaB : lambda * B = R / 2 := by
    dsimp [lambda]
    field_simp
  have hmain' : R - lambda * B ≤
      ((H.isolatedSample S).card : ℝ) - lambda * Y := by
    exact hmain
  have hreward : R / 2 ≤ ((H.isolatedSample S).card : ℝ) := by
    rw [hlambdaB] at hmain'
    nlinarith [mul_nonneg hlambda.le hY]
  have hupper := H.matching_card_le_vertexSet_div hk hunif hM
  have hscaled : lambda * Y ≤ (H.vertexSet.card : ℝ) / (k : ℝ) := by
    rw [hlambdaB] at hmain'
    nlinarith
  have hpenalty : Y ≤ ((H.vertexSet.card : ℝ) / (k : ℝ)) / lambda := by
    apply (le_div_iff₀ hlambda).mpr
    simpa [mul_comm] using hscaled
  refine ⟨S, hM, ?_, ?_⟩
  · exact hreward
  · simpa [R, B, lambda, Y] using hpenalty

/-- A robust version of `exists_isolatedSample_reward_and_penalty`: the
reward and penalty budget may be replaced by any explicit lower and upper
bounds.  This avoids having to prove that the exact variance expression is
strictly positive in later constant-parameter applications. -/
theorem exists_isolatedSample_reward_and_penalty_of_bounds
    (H : FiniteHypergraph V E) {k : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k) {p : E → ℝ} {t q L B : ℝ}
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1)
    (ht : 0 < t) (hq : 0 ≤ q) (hL : 0 < L) (hB : 0 < B)
    (hreward : L ≤ ( ∑ e, p e) -
      (∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0))
    (hbudget :
      (t ^ 2)⁻¹ * ∑ v : ↥H.vertexSet, ∑ e,
          (H.offConflictCoefficient v e) ^ 2 * p e * (1 - p e) +
        q * (∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0) ≤ B) :
    ∃ S : Finset E, H.IsMatching (H.isolatedSample S) ∧
      L / 2 ≤ ((H.isolatedSample S).card : ℝ) ∧
      ((weightedDeviationCount univ p H.offConflictCoefficient t S : ℝ) +
          q * (H.collisionCount S : ℝ) ≤
        ((H.vertexSet.card : ℝ) / (k : ℝ)) / (L / (2 * B))) := by
  let lambda : ℝ := L / (2 * B)
  have hlambda : 0 < lambda := div_pos hL (mul_pos (by norm_num) hB)
  obtain ⟨S, hM, hmain⟩ :=
    exists_isolatedSample_sub_deviation_collisionPenalty H hp₀ hp₁ ht hq
      hlambda.le
  let Y : ℝ :=
    (weightedDeviationCount univ p H.offConflictCoefficient t S : ℝ) +
      q * (H.collisionCount S : ℝ)
  let R : ℝ := (∑ e, p e) -
    (∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0)
  let B₀ : ℝ := (t ^ 2)⁻¹ * ∑ v : ↥H.vertexSet, ∑ e,
      (H.offConflictCoefficient v e) ^ 2 * p e * (1 - p e) +
    q * ∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0
  have hY : 0 ≤ Y := add_nonneg (Nat.cast_nonneg _)
    (mul_nonneg hq (Nat.cast_nonneg _))
  have hmain' : R - lambda * B₀ ≤
      ((H.isolatedSample S).card : ℝ) - lambda * Y := by
    exact hmain
  have hscaledMain : L - lambda * B ≤
      ((H.isolatedSample S).card : ℝ) - lambda * Y := by
    exact (sub_le_sub hreward
      (mul_le_mul_of_nonneg_left hbudget hlambda.le)).trans hmain'
  have hlambdaB : lambda * B = L / 2 := by
    dsimp [lambda]
    field_simp
  have hsize : L / 2 ≤ ((H.isolatedSample S).card : ℝ) := by
    rw [hlambdaB] at hscaledMain
    nlinarith [mul_nonneg hlambda.le hY]
  have hmatchingUpper := H.matching_card_le_vertexSet_div hk hunif hM
  have hscaled : lambda * Y ≤ (H.vertexSet.card : ℝ) / (k : ℝ) := by
    rw [hlambdaB] at hscaledMain
    nlinarith
  have hpenalty : Y ≤ ((H.vertexSet.card : ℝ) / (k : ℝ)) / lambda := by
    apply (le_div_iff₀ hlambda).mpr
    simpa [mul_comm] using hscaled
  refine ⟨S, hM, hsize, ?_⟩
  simpa [lambda, Y] using hpenalty

/-- Fully explicit constant-probability form of the simultaneous progress
and regularity round.  The reward loses the standard ordered-collision
term `|E| kD p²`; the penalty budget uses only the maximum degree and
maximum pair-degree. -/
theorem exists_isolatedSample_explicit_progress_and_penalty
    (H : FiniteHypergraph V E) {k D C : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    {p t q : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (ht : 0 < t) (hq : 0 ≤ q)
    (hL : 0 < (Fintype.card E : ℝ) * p -
      (Fintype.card E : ℝ) * (k * D : ℕ) * p ^ 2)
    (hB : 0 <
      (t ^ 2)⁻¹ * ((H.vertexSet.card : ℝ) *
        (((k * C) * (D * (k * D)) : ℕ) : ℝ) * p * (1 - p)) +
      q * ((Fintype.card E : ℝ) * (k * D : ℕ) * p ^ 2)) :
    ∃ S : Finset E, H.IsMatching (H.isolatedSample S) ∧
      (((Fintype.card E : ℝ) * p -
          (Fintype.card E : ℝ) * (k * D : ℕ) * p ^ 2) / 2 ≤
        ((H.isolatedSample S).card : ℝ)) ∧
      ((weightedDeviationCount univ (fun _ : E ↦ p)
            H.offConflictCoefficient t S : ℝ) +
          q * (H.collisionCount S : ℝ) ≤
        ((H.vertexSet.card : ℝ) / (k : ℝ)) /
          (((Fintype.card E : ℝ) * p -
              (Fintype.card E : ℝ) * (k * D : ℕ) * p ^ 2) /
            (2 * ((t ^ 2)⁻¹ * ((H.vertexSet.card : ℝ) *
                (((k * C) * (D * (k * D)) : ℕ) : ℝ) * p * (1 - p)) +
              q * ((Fintype.card E : ℝ) * (k * D : ℕ) * p ^ 2))))) := by
  let L : ℝ := (Fintype.card E : ℝ) * p -
    (Fintype.card E : ℝ) * (k * D : ℕ) * p ^ 2
  let B : ℝ :=
    (t ^ 2)⁻¹ * ((H.vertexSet.card : ℝ) *
      (((k * C) * (D * (k * D)) : ℕ) : ℝ) * p * (1 - p)) +
    q * ((Fintype.card E : ℝ) * (k * D : ℕ) * p ^ 2)
  have hcollision := sum_conflictProbability_const_le hunif hdeg hp₀
  have hreward : L ≤ (∑ _e : E, p) -
      (∑ e, ∑ f, if H.Conflicts e f then p * p else 0) := by
    have hsum : (∑ _e : E, p) = (Fintype.card E : ℝ) * p := by
      simp only [sum_const, card_univ, nsmul_eq_mul]
    rw [hsum]
    exact sub_le_sub_left hcollision _
  have hvar := sum_offConflictCoefficient_sq_mul_le hunif hdeg hpair hp₀ hp₁
  have hinv : 0 ≤ (t ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg t)
  have hbudget :
      (t ^ 2)⁻¹ * ∑ v : ↥H.vertexSet, ∑ e,
          (H.offConflictCoefficient v e) ^ 2 * p * (1 - p) +
        q * (∑ e, ∑ f, if H.Conflicts e f then p * p else 0) ≤ B := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hvar hinv)
      (mul_le_mul_of_nonneg_left hcollision hq)
  obtain ⟨S, hM, hsize, hpenalty⟩ :=
    exists_isolatedSample_reward_and_penalty_of_bounds H hk hunif
      (p := fun _ : E ↦ p) (fun _ ↦ hp₀) (fun _ ↦ hp₁)
      ht hq hL hB hreward hbudget
  refine ⟨S, hM, ?_, ?_⟩
  · simpa [L] using hsize
  · simpa [L, B] using hpenalty

/-- A single sample simultaneously realizes the aggregate weighted variance
budget and the expected ordered-collision budget.  This is the form used
when exceptional vertices are sacrificed instead of invoking a local lemma. -/
theorem exists_offConflict_deviation_add_collision_le
    (H : FiniteHypergraph V E) {p : E → ℝ} {t q : ℝ}
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1)
    (ht : 0 < t) (hq : 0 ≤ q) :
    ∃ S : Finset E,
      (weightedDeviationCount univ p H.offConflictCoefficient t S : ℝ) +
          q * (H.collisionCount S : ℝ) ≤
        (t ^ 2)⁻¹ * ∑ v : ↥H.vertexSet, ∑ e,
            (H.offConflictCoefficient v e) ^ 2 * p e * (1 - p e) +
          q * ∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0 := by
  let mass : Finset E → ℝ := fun S ↦ bernoulliMass univ p S
  let penalty : Finset E → ℝ := fun S ↦
    (weightedDeviationCount univ p H.offConflictCoefficient t S : ℝ) +
      q * H.collisionScore S
  let budget : ℝ :=
    (t ^ 2)⁻¹ * ∑ v : ↥H.vertexSet, ∑ e,
        (H.offConflictCoefficient v e) ^ 2 * p e * (1 - p e) +
      q * ∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0
  have hmass : ∀ S, 0 ≤ mass S := fun S ↦
    bernoulliMass_nonneg (subset_univ S) (fun e _ ↦ hp₀ e) (fun e _ ↦ hp₁ e)
  have hsum : ∑ S, mass S = 1 := by
    simpa [mass] using sum_bernoulliMass (univ : Finset E) p
  have hpenalty : ∑ S, mass S * penalty S ≤ budget := by
    calc
      ∑ S, mass S * penalty S =
          (∑ S, mass S *
            (weightedDeviationCount univ p H.offConflictCoefficient t S : ℝ)) +
            q * (∑ S, mass S * H.collisionScore S) := by
        simp only [mass, penalty, mul_add, sum_add_distrib]
        congr 1
        rw [mul_sum]
        apply sum_congr rfl
        intro S _
        ring
      _ ≤ ((t ^ 2)⁻¹ * ∑ v : ↥H.vertexSet, ∑ e,
              (H.offConflictCoefficient v e) ^ 2 * p e * (1 - p e)) +
            q * (∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0) := by
        apply add_le_add
        · simpa [mass] using
            (sum_bernoulliMass_mul_weightedDeviationCount_le
              (U := (univ : Finset E)) (a := H.offConflictCoefficient)
              (fun e _ ↦ hp₀ e) (fun e _ ↦ hp₁ e) ht)
        · exact mul_le_mul_of_nonneg_left
            (le_of_eq (sum_bernoulliMass_mul_collisionScore H p)) hq
      _ = budget := rfl
  obtain ⟨S, hS⟩ := exists_output_sub_penalty_ge mass
    (fun _ ↦ (0 : ℝ)) penalty hmass hsum (rewardLower := 0)
    (penaltyUpper := budget) (lambda := 1) (by simp) hpenalty (by norm_num)
  refine ⟨S, ?_⟩
  have : penalty S ≤ budget := by
    simpa using hS
  simpa [penalty, budget] using this

/-- Aggregate exceptional-vertex form of one nibble round.  The collision
penalty is chosen so that the deterministic alteration charge exactly pays
for all collision-heavy vertices. -/
theorem exists_nibble_exceptionalVertices_le
    (H : FiniteHypergraph V E) {p : E → ℝ} {t : ℝ} {r k D : ℕ}
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1)
    (ht : 0 < t) (hr : 0 < r) :
    ∃ S : Finset E, H.IsMatching (H.isolatedSample S) ∧
      ((H.nibbleExceptionalVertices p t r S).card : ℝ) ≤
        (t ^ 2)⁻¹ * ∑ v : ↥H.vertexSet, ∑ e,
            (H.offConflictCoefficient v e) ^ 2 * p e * (1 - p e) +
          ((k * (k * D) : ℕ) : ℝ) / (r : ℝ) *
            (∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0) := by
  let q : ℝ := ((k * (k * D) : ℕ) : ℝ) / (r : ℝ)
  have hq : 0 ≤ q := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨S, hbudget⟩ :=
    exists_offConflict_deviation_add_collision_le H hp₀ hp₁ ht hq
  refine ⟨S, H.isolatedSample_isMatching S, ?_⟩
  have hheavyNat := H.mul_card_collisionHeavyVertices_le hunif hdeg S (r := r)
  have hheavyCast :
      (r : ℝ) * (H.collisionHeavyVertices r S).card ≤
        (H.collisionCount S : ℝ) * ((k * (k * D) : ℕ) : ℝ) := by
    exact_mod_cast hheavyNat
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hheavy : ((H.collisionHeavyVertices r S).card : ℝ) ≤
      q * (H.collisionCount S : ℝ) := by
    calc
      ((H.collisionHeavyVertices r S).card : ℝ) =
          (r : ℝ)⁻¹ * ((r : ℝ) * (H.collisionHeavyVertices r S).card) := by
        rw [← mul_assoc, inv_mul_cancel₀ hrR.ne', one_mul]
      _ ≤ (r : ℝ)⁻¹ *
          ((H.collisionCount S : ℝ) * ((k * (k * D) : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hheavyCast (inv_nonneg.mpr hrR.le)
      _ = q * (H.collisionCount S : ℝ) := by
        dsimp [q]
        rw [div_eq_mul_inv]
        ring
  calc
    ((H.nibbleExceptionalVertices p t r S).card : ℝ) ≤
        ((H.offConflictDeviationVertices p t S).card : ℝ) +
          ((H.collisionHeavyVertices r S).card : ℝ) := by
      exact_mod_cast card_union_le (H.offConflictDeviationVertices p t S)
        (H.collisionHeavyVertices r S)
    _ ≤ (weightedDeviationCount univ p H.offConflictCoefficient t S : ℝ) +
          q * (H.collisionCount S : ℝ) := by
      rw [H.card_offConflictDeviationVertices]
      exact add_le_add (le_refl _) hheavy
    _ ≤ (t ^ 2)⁻¹ * ∑ v : ↥H.vertexSet, ∑ e,
            (H.offConflictCoefficient v e) ^ 2 * p e * (1 - p e) +
          q * (∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0) := hbudget
    _ = _ := rfl

/-- Constant-rate corollary with all expectation terms replaced by explicit
degree and codegree bounds. -/
theorem exists_nibble_exceptionalVertices_le_explicit
    (H : FiniteHypergraph V E) {p t : ℝ} {r k D C : ℕ}
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (ht : 0 < t) (hr : 0 < r) :
    ∃ S : Finset E, H.IsMatching (H.isolatedSample S) ∧
      ((H.nibbleExceptionalVertices (fun _ ↦ p) t r S).card : ℝ) ≤
        (t ^ 2)⁻¹ * ((H.vertexSet.card : ℝ) *
          (((k * C) * (D * (k * D)) : ℕ) : ℝ) * p * (1 - p)) +
        (((k * (k * D) : ℕ) : ℝ) / (r : ℝ)) *
          ((Fintype.card E : ℝ) * (k * D : ℕ) * p ^ 2) := by
  obtain ⟨S, hM, hraw⟩ := exists_nibble_exceptionalVertices_le H hunif hdeg
    (fun _ ↦ hp₀) (fun _ ↦ hp₁) ht hr
  refine ⟨S, hM, hraw.trans ?_⟩
  have hvar := sum_offConflictCoefficient_sq_mul_le hunif hdeg hpair hp₀ hp₁
  have hcollision := sum_conflictProbability_const_le hunif hdeg hp₀
  have hinv : 0 ≤ (t ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg t)
  have hq : 0 ≤ (((k * (k * D) : ℕ) : ℝ) / (r : ℝ)) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  exact add_le_add
    (mul_le_mul_of_nonneg_left hvar hinv)
    (mul_le_mul_of_nonneg_left hcollision hq)

/-- Explicit one-round invariant in the form needed for an outer nibble:
the same altered sample makes definite matching progress and leaves only a
controlled set of vertices without the residual-degree estimate. -/
theorem exists_nibble_explicit_progress_and_exceptional
    (H : FiniteHypergraph V E) {k D C r : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    {p t : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (ht : 0 < t) (hr : 0 < r)
    (hL : 0 < (Fintype.card E : ℝ) * p -
      (Fintype.card E : ℝ) * (k * D : ℕ) * p ^ 2)
    (hB : 0 <
      (t ^ 2)⁻¹ * ((H.vertexSet.card : ℝ) *
        (((k * C) * (D * (k * D)) : ℕ) : ℝ) * p * (1 - p)) +
      (((k * (k * D) : ℕ) : ℝ) / (r : ℝ)) *
        ((Fintype.card E : ℝ) * (k * D : ℕ) * p ^ 2)) :
    ∃ S : Finset E, H.IsMatching (H.isolatedSample S) ∧
      (((Fintype.card E : ℝ) * p -
          (Fintype.card E : ℝ) * (k * D : ℕ) * p ^ 2) / 2 ≤
        ((H.isolatedSample S).card : ℝ)) ∧
      ((H.nibbleExceptionalVertices (fun _ : E ↦ p) t r S).card : ℝ) ≤
        ((H.vertexSet.card : ℝ) / (k : ℝ)) /
          (((Fintype.card E : ℝ) * p -
              (Fintype.card E : ℝ) * (k * D : ℕ) * p ^ 2) /
            (2 * ((t ^ 2)⁻¹ * ((H.vertexSet.card : ℝ) *
                (((k * C) * (D * (k * D)) : ℕ) : ℝ) * p * (1 - p)) +
              (((k * (k * D) : ℕ) : ℝ) / (r : ℝ)) *
                ((Fintype.card E : ℝ) * (k * D : ℕ) * p ^ 2)))) := by
  let q : ℝ := ((k * (k * D) : ℕ) : ℝ) / (r : ℝ)
  have hq : 0 ≤ q := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨S, hM, hsize, hpenalty⟩ :=
    exists_isolatedSample_explicit_progress_and_penalty H hk hunif hdeg hpair
      hp₀ hp₁ ht hq hL hB
  refine ⟨S, hM, hsize, ?_⟩
  have hheavyNat := H.mul_card_collisionHeavyVertices_le hunif hdeg S (r := r)
  have hheavyCast :
      (r : ℝ) * (H.collisionHeavyVertices r S).card ≤
        (H.collisionCount S : ℝ) * ((k * (k * D) : ℕ) : ℝ) := by
    exact_mod_cast hheavyNat
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hheavy : ((H.collisionHeavyVertices r S).card : ℝ) ≤
      q * (H.collisionCount S : ℝ) := by
    calc
      ((H.collisionHeavyVertices r S).card : ℝ) =
          (r : ℝ)⁻¹ * ((r : ℝ) * (H.collisionHeavyVertices r S).card) := by
        rw [← mul_assoc, inv_mul_cancel₀ hrR.ne', one_mul]
      _ ≤ (r : ℝ)⁻¹ *
          ((H.collisionCount S : ℝ) * ((k * (k * D) : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hheavyCast (inv_nonneg.mpr hrR.le)
      _ = q * (H.collisionCount S : ℝ) := by
        dsimp [q]
        rw [div_eq_mul_inv]
        ring
  have hexceptional :
      ((H.nibbleExceptionalVertices (fun _ : E ↦ p) t r S).card : ℝ) ≤
        (weightedDeviationCount univ (fun _ : E ↦ p)
            H.offConflictCoefficient t S : ℝ) +
          q * (H.collisionCount S : ℝ) := by
    calc
      ((H.nibbleExceptionalVertices (fun _ : E ↦ p) t r S).card : ℝ) ≤
          ((H.offConflictDeviationVertices (fun _ : E ↦ p) t S).card : ℝ) +
            ((H.collisionHeavyVertices r S).card : ℝ) := by
        exact_mod_cast card_union_le
          (H.offConflictDeviationVertices (fun _ : E ↦ p) t S)
          (H.collisionHeavyVertices r S)
      _ ≤ (weightedDeviationCount univ (fun _ : E ↦ p)
              H.offConflictCoefficient t S : ℝ) +
            q * (H.collisionCount S : ℝ) := by
        rw [H.card_offConflictDeviationVertices]
        exact add_le_add (le_refl _) hheavy
  exact hexceptional.trans (by simpa [q] using hpenalty)

end FiniteNibble

end

end Erdos76
