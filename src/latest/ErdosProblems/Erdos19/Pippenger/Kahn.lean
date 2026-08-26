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
import ErdosProblems.Erdos19.Pippenger.WeightedHypergraph
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# The weighted nibble for finite uniform hypergraphs

This file develops the finite probabilistic theorem used to round the averaged
fractional triangle packing.  The elementary incidence identities are kept
separate from the probabilistic nibble.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FiniteHypergraph

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Double-counting incidences: the sum of the vertex loads is the sum of the
edge weights multiplied by the sizes of their supports. -/
lemma sum_vertexLoad_eq_sum_card_mul (H : FiniteHypergraph V E) (w : E → ℝ) :
    ∑ v ∈ H.vertexSet, H.vertexLoad w v =
      ∑ e, ((H.support e).card : ℝ) * w e := by
  classical
  simp only [vertexLoad, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  rw [← sum_filter]
  have hfilter : H.vertexSet.filter (fun v ↦ v ∈ H.support e) = H.support e := by
    ext v
    simp only [mem_filter]
    constructor
    · exact fun h ↦ h.2
    · intro hv
      exact ⟨H.support_subset_vertexSet e hv, hv⟩
  rw [hfilter]
  simp

/-- A fractional matching in a `k`-uniform hypergraph has total weight at most
`|V| / k`.  The multiplication form avoids division and also covers `k = 0`. -/
lemma card_mul_totalWeight_le_vertexSet_card {H : FiniteHypergraph V E} {w : E → ℝ}
    {k : ℕ} (hunif : H.IsUniform k) (hw : H.IsFractionalMatching w) :
    (k : ℝ) * H.totalWeight w ≤ H.vertexSet.card := by
  calc
    (k : ℝ) * H.totalWeight w = ∑ e, ((H.support e).card : ℝ) * w e := by
      simp only [totalWeight]
      rw [mul_sum]
      apply sum_congr rfl
      intro e _
      rw [hunif e]
    _ = ∑ v ∈ H.vertexSet, H.vertexLoad w v :=
      (sum_vertexLoad_eq_sum_card_mul H w).symm
    _ ≤ ∑ _v ∈ H.vertexSet, (1 : ℝ) := by
      exact sum_le_sum fun v hv ↦ hw.vertexLoad_le_one hv
    _ = H.vertexSet.card := by simp

/-- In a positive-uniform hypergraph, every indexed edge is supported inside
the declared vertex set and hence the vertex set is nonempty when `E` is. -/
lemma support_nonempty_of_uniform {H : FiniteHypergraph V E} {k : ℕ}
    (hk : 0 < k) (hunif : H.IsUniform k) (e : E) : (H.support e).Nonempty := by
  rw [nonempty_iff_ne_empty]
  intro hempty
  have := hunif e
  simp [hempty] at this
  omega

/-- For rank at least two, the codegree hypothesis bounds every individual
edge weight: choose two distinct vertices in its support. -/
lemma weight_lt_of_pairCodegreeLT {H : FiniteHypergraph V E} {w : E → ℝ}
    {k : ℕ} {delta : ℝ} (hk : 2 ≤ k) (hunif : H.IsUniform k)
    (hw : H.IsFractionalMatching w) (hcodeg : H.PairCodegreeLT w delta) (e : E) :
    w e < delta := by
  have hcard : 2 ≤ (H.support e).card := by simpa [hunif e] using hk
  obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp (by omega : 1 < (H.support e).card)
  have he_le : w e ≤ H.pairLoad w x y := by
    rw [pairLoad]
    exact single_le_sum (fun f _ ↦ hw.nonneg f) (mem_filter.mpr ⟨mem_univ e, hx, hy⟩)
  exact he_le.trans_lt (hcodeg x y hxy)

/-- If the permitted additive error is at least `1/k` of the vertex set, the
empty matching already proves the desired conclusion. -/
lemma exists_matching_of_inv_nat_le_error {H : FiniteHypergraph V E} {w : E → ℝ}
    {k : ℕ} {zeta : ℝ} (hk : 0 < k) (hunif : H.IsUniform k)
    (hw : H.IsFractionalMatching w) (hzeta : (k : ℝ)⁻¹ ≤ zeta) :
    ∃ M : Finset E, H.IsMatching M ∧
      H.totalWeight w ≤ (M.card : ℝ) + zeta * H.vertexSet.card := by
  refine ⟨∅, H.empty_isMatching, ?_⟩
  simp only [card_empty, Nat.cast_zero, zero_add]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hbound := card_mul_totalWeight_le_vertexSet_card hunif hw
  calc
    H.totalWeight w = (k : ℝ)⁻¹ * ((k : ℝ) * H.totalWeight w) := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hkR), one_mul]
    _ ≤ (k : ℝ)⁻¹ * H.vertexSet.card :=
      mul_le_mul_of_nonneg_left hbound (le_of_lt (inv_pos.mpr hkR))
    _ ≤ zeta * H.vertexSet.card := by
      exact mul_le_mul_of_nonneg_right hzeta (Nat.cast_nonneg _)

/-! ## Removing parallel indexed edges

Kahn's theorem is conventionally stated for a family of distinct finite
supports.  The construction used for Erdős 76 naturally produces parallel
indexed copies, so we collect their weights before applying the nibble.
-/

/-- The finite set of distinct supports occurring in an indexed hypergraph. -/
def supportSet (H : FiniteHypergraph V E) : Finset (Finset V) :=
  univ.image H.support

/-- Distinct supports, regarded as the edge-index type of the simple quotient. -/
abbrev SupportIndex (H : FiniteHypergraph V E) := ↑H.supportSet

/-- The support-indexed hypergraph obtained by identifying parallel edges. -/
def collectParallel (H : FiniteHypergraph V E) :
    FiniteHypergraph V H.SupportIndex where
  vertexSet := H.vertexSet
  support s := s.1
  support_subset_vertexSet s := by
    obtain ⟨e, _, he⟩ := mem_image.mp s.2
    simpa [← he] using H.support_subset_vertexSet e

/-- The weight of a collected support is the sum of all weights in its fiber. -/
def collectedWeight (H : FiniteHypergraph V E) (w : E → ℝ) (s : H.SupportIndex) : ℝ :=
  ∑ e with H.support e = s.1, w e

@[simp] lemma collectParallel_vertexSet (H : FiniteHypergraph V E) :
    H.collectParallel.vertexSet = H.vertexSet := rfl

@[simp] lemma collectParallel_support (H : FiniteHypergraph V E) (s : H.SupportIndex) :
    H.collectParallel.support s = s.1 := rfl

/-- Collecting parallel edges preserves total weight. -/
lemma totalWeight_collectedWeight (H : FiniteHypergraph V E) (w : E → ℝ) :
    H.collectParallel.totalWeight (H.collectedWeight w) = H.totalWeight w := by
  rw [totalWeight, totalWeight]
  change (∑ s : H.SupportIndex, ∑ e with H.support e = s.1, w e) = ∑ e, w e
  rw [← sum_subtype H.supportSet (fun _ ↦ Iff.rfl)
    (fun s ↦ ∑ e with H.support e = s, w e)]
  exact sum_fiberwise_of_maps_to (fun e _ ↦ mem_image_of_mem H.support (mem_univ e)) w

/-- Uniformity is unchanged by collecting parallel indexed edges. -/
lemma isUniform_collectParallel {H : FiniteHypergraph V E} {k : ℕ}
    (hunif : H.IsUniform k) : H.collectParallel.IsUniform k := by
  intro s
  obtain ⟨e, _, he⟩ := mem_image.mp s.2
  simpa [collectParallel, ← he] using hunif e

/-- Nonnegativity is preserved when parallel weights are collected. -/
lemma collectedWeight_nonneg {H : FiniteHypergraph V E} {w : E → ℝ}
    (hw : ∀ e, 0 ≤ w e) (s : H.SupportIndex) : 0 ≤ H.collectedWeight w s := by
  exact sum_nonneg fun e _ ↦ hw e

/-- Collecting parallel edges preserves every vertex load. -/
lemma vertexLoad_collectedWeight (H : FiniteHypergraph V E) (w : E → ℝ) (v : V) :
    H.collectParallel.vertexLoad (H.collectedWeight w) v = H.vertexLoad w v := by
  rw [vertexLoad, vertexLoad]
  change (∑ s : H.SupportIndex with v ∈ s.1,
      ∑ e with H.support e = s.1, w e) = ∑ e with v ∈ H.support e, w e
  rw [sum_filter]
  rw [← sum_subtype H.supportSet (fun _ ↦ Iff.rfl)
    (fun s ↦ if v ∈ s then ∑ e with H.support e = s, w e else 0)]
  rw [← sum_filter]
  simpa [supportSet] using
    (sum_fiberwise_eq_sum_filter (univ : Finset E)
      (H.supportSet.filter fun s ↦ v ∈ s) H.support w)

/-- Collecting parallel edges preserves every pair load. -/
lemma pairLoad_collectedWeight (H : FiniteHypergraph V E) (w : E → ℝ) (x y : V) :
    H.collectParallel.pairLoad (H.collectedWeight w) x y = H.pairLoad w x y := by
  rw [pairLoad, pairLoad]
  change (∑ s : H.SupportIndex with x ∈ s.1 ∧ y ∈ s.1,
      ∑ e with H.support e = s.1, w e) =
    ∑ e with x ∈ H.support e ∧ y ∈ H.support e, w e
  rw [sum_filter]
  rw [← sum_subtype H.supportSet (fun _ ↦ Iff.rfl)
    (fun s ↦ if x ∈ s ∧ y ∈ s then ∑ e with H.support e = s, w e else 0)]
  rw [← sum_filter]
  simpa [supportSet] using
    (sum_fiberwise_eq_sum_filter (univ : Finset E)
      (H.supportSet.filter fun s ↦ x ∈ s ∧ y ∈ s) H.support w)

/-- Feasibility of a fractional matching is unchanged by collection. -/
lemma isFractionalMatching_collectParallel {H : FiniteHypergraph V E} {w : E → ℝ}
    (hw : H.IsFractionalMatching w) :
    H.collectParallel.IsFractionalMatching (H.collectedWeight w) := by
  constructor
  · exact H.collectedWeight_nonneg hw.1
  · intro v hv
    rw [vertexLoad_collectedWeight]
    exact hw.2 v hv

/-- The fractional pair-codegree bound is unchanged by collection. -/
lemma pairCodegreeLT_collectParallel {H : FiniteHypergraph V E} {w : E → ℝ} {δ : ℝ}
    (hcodeg : H.PairCodegreeLT w δ) :
    H.collectParallel.PairCodegreeLT (H.collectedWeight w) δ := by
  intro x y hxy
  rw [pairLoad_collectedWeight]
  exact hcodeg x y hxy

/-- A canonical representative of a collected support. -/
def supportRepresentative (H : FiniteHypergraph V E) (s : H.SupportIndex) : E :=
  Classical.choose (mem_image.mp s.2)

@[simp] lemma support_supportRepresentative (H : FiniteHypergraph V E)
    (s : H.SupportIndex) : H.support (H.supportRepresentative s) = s.1 := by
  exact (Classical.choose_spec (mem_image.mp s.2)).2

lemma supportRepresentative_injective (H : FiniteHypergraph V E) :
    Function.Injective H.supportRepresentative := by
  intro s t hst
  apply Subtype.ext
  rw [← support_supportRepresentative H s, ← support_supportRepresentative H t, hst]

/-- Lift a family of distinct supports back to representative indexed edges. -/
def liftCollected (H : FiniteHypergraph V E) (M : Finset H.SupportIndex) : Finset E :=
  M.image H.supportRepresentative

@[simp] lemma card_liftCollected (H : FiniteHypergraph V E) (M : Finset H.SupportIndex) :
    (H.liftCollected M).card = M.card := by
  rw [liftCollected, card_image_iff]
  exact (H.supportRepresentative_injective).injOn

/-- A matching of collected supports lifts to an indexed matching. -/
lemma isMatching_liftCollected {H : FiniteHypergraph V E} {M : Finset H.SupportIndex}
    (hM : H.collectParallel.IsMatching M) : H.IsMatching (H.liftCollected M) := by
  rw [IsMatching] at hM ⊢
  intro e he f hf hef
  change e ∈ H.liftCollected M at he
  change f ∈ H.liftCollected M at hf
  obtain ⟨s, hs, rfl⟩ := mem_image.mp he
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hf
  have hst : s ≠ t := by
    intro h
    subst t
    exact hef rfl
  simpa using hM hs ht hst

/-- Any rounding statement proved after collecting parallel edges transfers
back to the original indexed hypergraph with exactly the same cardinality. -/
lemma lift_collected_rounding {H : FiniteHypergraph V E} {w : E → ℝ} {zeta : ℝ}
    (hround : ∃ M : Finset H.SupportIndex, H.collectParallel.IsMatching M ∧
      H.collectParallel.totalWeight (H.collectedWeight w) ≤
        (M.card : ℝ) + zeta * H.collectParallel.vertexSet.card) :
    ∃ M : Finset E, H.IsMatching M ∧
      H.totalWeight w ≤ (M.card : ℝ) + zeta * H.vertexSet.card := by
  obtain ⟨M, hM, hbound⟩ := hround
  refine ⟨H.liftCollected M, H.isMatching_liftCollected hM, ?_⟩
  rw [← H.totalWeight_collectedWeight w]
  simpa using hbound

/-! ## The rank-one case -/

/-- A distinct-support, one-uniform hypergraph has all of its edges as a
matching. -/
lemma univ_isMatching_of_uniform_one {H : FiniteHypergraph V E}
    (hunif : H.IsUniform 1) (hinj : Function.Injective H.support) :
    H.IsMatching univ := by
  rw [IsMatching]
  intro e _ f _ hef
  obtain ⟨x, hx⟩ := card_eq_one.mp (hunif e)
  obtain ⟨y, hy⟩ := card_eq_one.mp (hunif f)
  have hxy : x ≠ y := by
    intro h
    apply hef
    apply hinj
    simpa [hx, hy, h]
  simp [hx, hy, hxy]

/-- Every individual edge of a positive-uniform fractional matching has weight
at most one. -/
lemma weight_le_one_of_uniform_pos {H : FiniteHypergraph V E} {w : E → ℝ} {k : ℕ}
    (hk : 0 < k) (hunif : H.IsUniform k) (hw : H.IsFractionalMatching w) (e : E) :
    w e ≤ 1 := by
  obtain ⟨v, hv⟩ := H.support_nonempty_of_uniform hk hunif e
  calc
    w e ≤ H.vertexLoad w v := by
      rw [vertexLoad]
      exact single_le_sum (fun f _ ↦ hw.nonneg f) (mem_filter.mpr ⟨mem_univ e, hv⟩)
    _ ≤ 1 := hw.vertexLoad_le_one (H.support_subset_vertexSet e hv)

/-- For an injectively support-indexed one-uniform hypergraph, the total
fractional weight is at most the number of edges. -/
lemma totalWeight_le_card_of_uniform_one_injective {H : FiniteHypergraph V E} {w : E → ℝ}
    (hunif : H.IsUniform 1) (hinj : Function.Injective H.support)
    (hw : H.IsFractionalMatching w) : H.totalWeight w ≤ Fintype.card E := by
  rw [totalWeight]
  calc
    ∑ e, w e ≤ ∑ _e : E, (1 : ℝ) :=
      sum_le_sum fun e _ ↦ H.weight_le_one_of_uniform_pos (by omega) hunif hw e
    _ = Fintype.card E := by simp

lemma support_collectParallel_injective (H : FiniteHypergraph V E) :
    Function.Injective H.collectParallel.support := by
  intro s t hst
  exact Subtype.ext hst

/-- Kahn's conclusion is exact in rank one: collect parallel singleton edges
and take every distinct support. -/
lemma exists_matching_uniform_one {H : FiniteHypergraph V E} {w : E → ℝ} {zeta : ℝ}
    (hzeta : 0 ≤ zeta) (hunif : H.IsUniform 1) (hw : H.IsFractionalMatching w) :
    ∃ M : Finset E, H.IsMatching M ∧
      H.totalWeight w ≤ (M.card : ℝ) + zeta * H.vertexSet.card := by
  apply H.lift_collected_rounding
  refine ⟨univ,
    univ_isMatching_of_uniform_one (H := H.collectParallel)
      (H.isUniform_collectParallel hunif) H.support_collectParallel_injective, ?_⟩
  calc
    H.collectParallel.totalWeight (H.collectedWeight w) ≤
        Fintype.card H.SupportIndex :=
      H.collectParallel.totalWeight_le_card_of_uniform_one_injective
        (H.isUniform_collectParallel hunif) H.support_collectParallel_injective
        (H.isFractionalMatching_collectParallel hw)
    _ ≤ (univ.card : ℝ) + zeta * H.collectParallel.vertexSet.card := by
      simp only [card_univ]
      exact le_add_of_nonneg_right (mul_nonneg hzeta (Nat.cast_nonneg _))

/-! ## One alteration round -/

/-- Two distinct indexed hyperedges conflict when their supports intersect. -/
def Conflicts (H : FiniteHypergraph V E) (e f : E) : Prop :=
  e ≠ f ∧ ¬Disjoint (H.support e) (H.support f)

lemma Conflicts.symm {H : FiniteHypergraph V E} {e f : E}
    (h : H.Conflicts e f) : H.Conflicts f e := by
  exact ⟨h.1.symm, fun hd ↦ h.2 hd.symm⟩

/-- Keep precisely those sampled edges which have no sampled conflict. -/
def isolatedSample (H : FiniteHypergraph V E) (S : Finset E) : Finset E :=
  S.filter fun e ↦ ∀ f ∈ S, e ≠ f → Disjoint (H.support e) (H.support f)

/-- Number of ordered conflicting pairs in a sample. -/
def collisionCount (H : FiniteHypergraph V E) (S : Finset E) : ℕ :=
  ∑ e ∈ S, (S.filter fun f ↦ H.Conflicts e f).card

/-- Real-valued ordered collision count, convenient inside expectations. -/
def collisionScore (H : FiniteHypergraph V E) (S : Finset E) : ℝ :=
  ∑ e ∈ S, ∑ f ∈ S, if H.Conflicts e f then 1 else 0

@[simp] lemma collisionScore_eq_collisionCount (H : FiniteHypergraph V E) (S : Finset E) :
    H.collisionScore S = H.collisionCount S := by
  simp [collisionScore, collisionCount, sum_boole, Nat.cast_sum]

lemma isolatedSample_subset (H : FiniteHypergraph V E) (S : Finset E) :
    H.isolatedSample S ⊆ S := by
  exact filter_subset _ _

lemma isolatedSample_isMatching (H : FiniteHypergraph V E) (S : Finset E) :
    H.IsMatching (H.isolatedSample S) := by
  rw [IsMatching]
  intro e he f hf hef
  change e ∈ H.isolatedSample S at he
  change f ∈ H.isolatedSample S at hf
  exact (mem_filter.mp he).2 f (mem_filter.mp hf).1 hef

/-- Since the selected supports are disjoint, distinct selected edges
conflicting with a fixed edge must use distinct vertices of that edge. -/
lemma card_filter_conflicts_le_support_card (H : FiniteHypergraph V E)
    {M : Finset E} (hM : H.IsMatching M) (e : E) :
    (M.filter fun f ↦ H.Conflicts e f).card ≤ (H.support e).card := by
  let F : Finset E := M.filter fun f ↦ H.Conflicts e f
  have hex : ∀ f : {x // x ∈ F},
      ∃ v, v ∈ H.support e ∧ v ∈ H.support f.1 := by
    intro f
    have hconf : H.Conflicts e f.1 := (mem_filter.mp f.2).2
    exact not_disjoint_iff.mp hconf.2
  let phi : {x // x ∈ F} → {v // v ∈ H.support e} := fun f ↦
    ⟨Classical.choose (hex f), (Classical.choose_spec (hex f)).1⟩
  have hphi_support : ∀ f : {x // x ∈ F},
      (phi f).1 ∈ H.support f.1 := fun f ↦ (Classical.choose_spec (hex f)).2
  have hphi : Function.Injective phi := by
    intro f g hfg
    apply Subtype.ext
    by_contra hne
    have hfM : f.1 ∈ M := (mem_filter.mp f.2).1
    have hgM : g.1 ∈ M := (mem_filter.mp g.2).1
    have hd : Disjoint (H.support f.1) (H.support g.1) := hM hfM hgM hne
    have hwf : (phi f).1 ∈ H.support f.1 := hphi_support f
    have hwg : (phi f).1 ∈ H.support g.1 := by
      rw [show (phi f).1 = (phi g).1 from congrArg Subtype.val hfg]
      exact hphi_support g
    exact (Finset.disjoint_left.mp hd) hwf hwg
  have hc : F.card ≤ (H.support e).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective phi hphi
  exact hc

/-- Deleting every edge involved in a collision loses at most the number of
ordered conflicting pairs. -/
lemma card_sub_collisionCount_le_isolatedSample (H : FiniteHypergraph V E) (S : Finset E) :
    (S.card : ℝ) - (H.collisionCount S : ℝ) ≤ ((H.isolatedSample S).card : ℝ) := by
  have hbad : (S \ H.isolatedSample S).card ≤ H.collisionCount S := by
    calc
      (S \ H.isolatedSample S).card = ∑ _e ∈ S \ H.isolatedSample S, 1 := by simp
      _ ≤ ∑ e ∈ S \ H.isolatedSample S,
          (S.filter fun f ↦ H.Conflicts e f).card := by
        apply sum_le_sum
        intro e he
        have heS : e ∈ S := (mem_sdiff.mp he).1
        have hnot : ¬∀ f ∈ S, e ≠ f → Disjoint (H.support e) (H.support f) := by
          intro hall
          exact (mem_sdiff.mp he).2 (mem_filter.mpr ⟨heS, hall⟩)
        push_neg at hnot
        obtain ⟨f, hfS, hef, hconflict⟩ := hnot
        exact card_pos.mpr ⟨f, mem_filter.mpr ⟨hfS, hef, hconflict⟩⟩
      _ ≤ ∑ e ∈ S, (S.filter fun f ↦ H.Conflicts e f).card := by
        exact sum_le_sum_of_subset (sdiff_subset)
      _ = H.collisionCount S := rfl
  have hsplit : (S \ H.isolatedSample S).card + (H.isolatedSample S).card = S.card :=
    card_sdiff_add_card_eq_card (H.isolatedSample_subset S)
  have hbadR : ((S \ H.isolatedSample S).card : ℝ) ≤ H.collisionCount S := by
    exact_mod_cast hbad
  have hsplitR : ((S \ H.isolatedSample S).card : ℝ) +
      (H.isolatedSample S).card = S.card := by
    exact_mod_cast hsplit
  calc
    (S.card : ℝ) - H.collisionCount S =
        ((S \ H.isolatedSample S).card : ℝ) +
          (H.isolatedSample S).card - H.collisionCount S := by rw [hsplitR]
    _ = (((S \ H.isolatedSample S).card : ℝ) - H.collisionCount S) +
          (H.isolatedSample S).card := by ring
    _ ≤ 0 + (H.isolatedSample S).card :=
      add_le_add (sub_nonpos.mpr hbadR) (le_refl _)
    _ = (H.isolatedSample S).card := zero_add _

end FiniteHypergraph

/-! ## Finite Bernoulli sampling

The nibble is developed over the explicit finite sample space `U.powerset`.
This keeps all expectations as finite sums and avoids measure-theoretic
side-conditions in the combinatorial part of the proof.
-/

namespace FiniteNibble

variable {E : Type*} [DecidableEq E]

private lemma ite_and_and_zero (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R]
    (a : ℝ) :
    (if P ∧ Q ∧ R then a else 0) =
      if P then (if Q then (if R then a else 0) else 0) else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp_all

private lemma sum_univ_ite_mem [Fintype E] (S : Finset E) (g : E → ℝ) :
    ∑ e, (if e ∈ S then g e else 0) = ∑ e ∈ S, g e := by
  rw [← sum_filter]
  simp

/-- Product Bernoulli mass of a subset `S` of a finite ground set `U`. -/
def bernoulliMass (U : Finset E) (p : E → ℝ) (S : Finset E) : ℝ :=
  (∏ e ∈ S, p e) * ∏ e ∈ U \ S, (1 - p e)

/-- The explicit Bernoulli masses on the powerset sum to one.  This identity is
purely algebraic and does not require the parameters to lie in `[0,1]`. -/
lemma sum_bernoulliMass (U : Finset E) (p : E → ℝ) :
    ∑ S ∈ U.powerset, bernoulliMass U p S = 1 := by
  simp only [bernoulliMass]
  rw [← prod_add]
  simp

lemma bernoulliMass_nonneg {U S : Finset E} {p : E → ℝ}
    (hS : S ⊆ U) (hp₀ : ∀ e ∈ U, 0 ≤ p e) (hp₁ : ∀ e ∈ U, p e ≤ 1) :
    0 ≤ bernoulliMass U p S := by
  apply mul_nonneg
  · exact prod_nonneg fun e he ↦ hp₀ e (hS he)
  · exact prod_nonneg fun e he ↦ sub_nonneg.mpr (hp₁ e (mem_sdiff.mp he).1)

lemma bernoulliMass_insert {U T : Finset E} {p : E → ℝ} {e : E}
    (heU : e ∈ U) (hT : T ⊆ U.erase e) :
    bernoulliMass U p (insert e T) = p e * bernoulliMass (U.erase e) p T := by
  have heT : e ∉ T := by
    intro he
    exact (mem_erase.mp (hT he)).1 rfl
  have hdiff : U \ insert e T = U.erase e \ T := by
    ext x
    simp only [mem_sdiff, mem_insert, mem_erase]
    tauto
  simp only [bernoulliMass, prod_insert heT, hdiff]
  ring

/-- First Bernoulli moment: the total mass of subsets containing `e` is `p e`. -/
lemma sum_bernoulliMass_filter_mem {U : Finset E} {p : E → ℝ} {e : E} (heU : e ∈ U) :
    ∑ S ∈ U.powerset with e ∈ S, bernoulliMass U p S = p e := by
  have hsets : U.powerset.filter (fun S ↦ e ∈ S) =
      (U.erase e).powerset.image (insert e) := by
    ext S
    simp only [mem_filter, mem_powerset, mem_image]
    constructor
    · rintro ⟨hSU, heS⟩
      refine ⟨S.erase e, ?_, ?_⟩
      · intro x hx
        obtain ⟨hxe, hxS⟩ := mem_erase.mp hx
        exact mem_erase.mpr ⟨hxe, hSU hxS⟩
      · simpa using insert_erase heS
    · rintro ⟨T, hT, rfl⟩
      exact ⟨insert_subset heU (hT.trans (erase_subset _ _)), mem_insert_self _ _⟩
  rw [hsets, sum_image]
  · calc
      ∑ T ∈ (U.erase e).powerset, bernoulliMass U p (insert e T) =
          ∑ T ∈ (U.erase e).powerset, p e * bernoulliMass (U.erase e) p T := by
        apply sum_congr rfl
        intro T hT
        exact bernoulliMass_insert heU (mem_powerset.mp hT)
      _ = p e * ∑ T ∈ (U.erase e).powerset, bernoulliMass (U.erase e) p T := by
        rw [mul_sum]
      _ = p e := by rw [sum_bernoulliMass, mul_one]
  · intro A hA B hB hAB
    have heA : e ∉ A := by
      intro heA
      exact (mem_erase.mp ((mem_powerset.mp hA) heA)).1 rfl
    have heB : e ∉ B := by
      intro heB
      exact (mem_erase.mp ((mem_powerset.mp hB) heB)).1 rfl
    simpa [heA, heB] using congrArg (fun S : Finset E ↦ S.erase e) hAB

/-- Second Bernoulli moment for two distinct coordinates. -/
lemma sum_bernoulliMass_filter_mem_mem {U : Finset E} {p : E → ℝ} {e f : E}
    (heU : e ∈ U) (hfU : f ∈ U) (hef : e ≠ f) :
    ∑ S ∈ U.powerset with e ∈ S ∧ f ∈ S, bernoulliMass U p S = p e * p f := by
  have hsets : U.powerset.filter (fun S ↦ e ∈ S ∧ f ∈ S) =
      ((U.erase e).powerset.filter fun T ↦ f ∈ T).image (insert e) := by
    ext S
    simp only [mem_filter, mem_powerset, mem_image]
    constructor
    · rintro ⟨hSU, heS, hfS⟩
      refine ⟨S.erase e, ?_, ?_⟩
      · refine ⟨?_, mem_erase.mpr ⟨hef.symm, hfS⟩⟩
        intro x hx
        obtain ⟨hxe, hxS⟩ := mem_erase.mp hx
        exact mem_erase.mpr ⟨hxe, hSU hxS⟩
      · simpa using insert_erase heS
    · rintro ⟨T, ⟨hT, hfT⟩, rfl⟩
      exact ⟨insert_subset heU (hT.trans (erase_subset _ _)), mem_insert_self _ _,
        mem_insert_of_mem hfT⟩
  rw [hsets, sum_image]
  · calc
      ∑ T ∈ (U.erase e).powerset with f ∈ T, bernoulliMass U p (insert e T) =
          ∑ T ∈ (U.erase e).powerset with f ∈ T,
            p e * bernoulliMass (U.erase e) p T := by
        apply sum_congr rfl
        intro T hT
        exact bernoulliMass_insert heU (mem_powerset.mp (mem_filter.mp hT).1)
      _ = p e * ∑ T ∈ (U.erase e).powerset with f ∈ T,
          bernoulliMass (U.erase e) p T := by rw [mul_sum]
      _ = p e * p f := by
        rw [sum_bernoulliMass_filter_mem (mem_erase.mpr ⟨hef.symm, hfU⟩)]
  · intro A hA B hB hAB
    have heA : e ∉ A := by
      intro heA
      exact (mem_erase.mp ((mem_powerset.mp (mem_filter.mp hA).1) heA)).1 rfl
    have heB : e ∉ B := by
      intro heB
      exact (mem_erase.mp ((mem_powerset.mp (mem_filter.mp hB).1) heB)).1 rfl
    simpa [heA, heB] using congrArg (fun S : Finset E ↦ S.erase e) hAB

/-- Expected cardinality of the explicit Bernoulli sample. -/
lemma sum_bernoulliMass_mul_card (U : Finset E) (p : E → ℝ) :
    ∑ S ∈ U.powerset, bernoulliMass U p S * (S.card : ℝ) = ∑ e ∈ U, p e := by
  calc
    ∑ S ∈ U.powerset, bernoulliMass U p S * (S.card : ℝ) =
        ∑ S ∈ U.powerset, ∑ e ∈ U, if e ∈ S then bernoulliMass U p S else 0 := by
      apply sum_congr rfl
      intro S hS
      rw [← sum_filter]
      have hfilter : U.filter (fun e ↦ e ∈ S) = S := by
        ext e
        simp only [mem_filter]
        constructor
        · exact fun h ↦ h.2
        · intro heS
          exact ⟨(mem_powerset.mp hS) heS, heS⟩
      rw [hfilter]
      simp [mul_comm]
    _ = ∑ e ∈ U, ∑ S ∈ U.powerset,
          if e ∈ S then bernoulliMass U p S else 0 := by rw [sum_comm]
    _ = ∑ e ∈ U, p e := by
      apply sum_congr rfl
      intro e heU
      rw [← sum_filter, sum_bernoulliMass_filter_mem heU]

/-- Finite probabilistic method: some outcome is at least its expectation under
any nonnegative mass function of total mass one. -/
lemma exists_output_ge_average {Omega : Type*} [Fintype Omega]
    (mass output : Omega → ℝ) (hmass : ∀ omega, 0 ≤ mass omega)
    (hsum : ∑ omega, mass omega = 1) :
    ∃ omega, (∑ x, mass x * output x) ≤ output omega := by
  have hne : (univ : Finset Omega).Nonempty := by
    by_contra h
    have hempty : (univ : Finset Omega) = ∅ := not_nonempty_iff_eq_empty.mp h
    simpa [hempty] using hsum
  obtain ⟨omega, _, homega⟩ := exists_max_image univ output hne
  refine ⟨omega, ?_⟩
  calc
    ∑ x, mass x * output x ≤ ∑ x, mass x * output omega := by
      exact sum_le_sum fun x hx ↦ mul_le_mul_of_nonneg_left (homega x hx) (hmass x)
    _ = (∑ x, mass x) * output omega := by rw [sum_mul]
    _ = output omega := by rw [hsum, one_mul]

section Hypergraph

variable {V : Type*} [DecidableEq V] [Fintype E]

/-- Expected number of ordered conflicts in an independent Bernoulli sample. -/
lemma sum_bernoulliMass_mul_collisionScore (H : FiniteHypergraph V E) (p : E → ℝ) :
    ∑ S ∈ (univ : Finset E).powerset,
        bernoulliMass univ p S * H.collisionScore S =
      ∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0 := by
  calc
    ∑ S ∈ (univ : Finset E).powerset,
        bernoulliMass univ p S * H.collisionScore S =
      ∑ S ∈ (univ : Finset E).powerset, ∑ e, ∑ f,
        if e ∈ S ∧ f ∈ S ∧ H.Conflicts e f then bernoulliMass univ p S else 0 := by
      apply sum_congr rfl
      intro S hS
      simp only [FiniteHypergraph.collisionScore, mul_sum, mul_ite, mul_one, mul_zero]
      symm
      simp only [ite_and]
      simp_rw [Finset.sum_ite_irrel]
      simp only [sum_const_zero]
      simp only [← sum_filter]
      simp
    _ = ∑ e, ∑ S ∈ (univ : Finset E).powerset, ∑ f,
        if e ∈ S ∧ f ∈ S ∧ H.Conflicts e f then bernoulliMass univ p S else 0 := by
      rw [sum_comm]
    _ = ∑ e, ∑ f, ∑ S ∈ (univ : Finset E).powerset,
        if e ∈ S ∧ f ∈ S ∧ H.Conflicts e f then bernoulliMass univ p S else 0 := by
      apply sum_congr rfl
      intro e _
      rw [sum_comm]
    _ = ∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0 := by
      apply sum_congr rfl
      intro e _
      apply sum_congr rfl
      intro f _
      by_cases hconf : H.Conflicts e f
      · simp only [hconf, and_true, if_true]
        rw [← sum_filter]
        exact sum_bernoulliMass_filter_mem_mem (U := (univ : Finset E)) (p := p)
          (e := e) (f := f) (mem_univ e) (mem_univ f) hconf.1
      · simp [hconf]

/-- Expectation form of the one-round alteration estimate.  Keeping this
inequality before the final averaging step lets later arguments penalize bad
residual-degree events and choose a sample which is simultaneously large and
regular. -/
lemma sum_bernoulliMass_mul_isolatedSample_card_ge
    (H : FiniteHypergraph V E) (p : E → ℝ)
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1) :
    (∑ e, p e) -
        (∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0) ≤
      ∑ S ∈ (univ : Finset E).powerset,
        bernoulliMass univ p S * ((H.isolatedSample S).card : ℝ) := by
  have hcardMean :
      ∑ S ∈ (univ : Finset E).powerset,
          bernoulliMass univ p S * (S.card : ℝ) = ∑ e, p e := by
    simpa using sum_bernoulliMass_mul_card (univ : Finset E) p
  have hcollisionMean :
      ∑ S ∈ (univ : Finset E).powerset,
          bernoulliMass univ p S * H.collisionScore S =
        ∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0 := by
    simpa using sum_bernoulliMass_mul_collisionScore H p
  calc
    (∑ e, p e) -
        (∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0) =
      ∑ S ∈ (univ : Finset E).powerset,
        bernoulliMass univ p S * ((S.card : ℝ) - H.collisionScore S) := by
      simp only [mul_sub, sum_sub_distrib]
      rw [hcardMean, hcollisionMean]
    _ ≤ ∑ S ∈ (univ : Finset E).powerset,
        bernoulliMass univ p S * ((H.isolatedSample S).card : ℝ) := by
      apply sum_le_sum
      intro S hS
      apply mul_le_mul_of_nonneg_left
      · simpa using H.card_sub_collisionCount_le_isolatedSample S
      · exact bernoulliMass_nonneg (mem_powerset.mp hS)
          (fun e _ ↦ hp₀ e) (fun e _ ↦ hp₁ e)

/-- One independent-sampling/alteration round.  The loss is the exact expected
number of ordered conflicting pairs. -/
lemma exists_matching_one_round (H : FiniteHypergraph V E) (p : E → ℝ)
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1) :
    ∃ M : Finset E, H.IsMatching M ∧
      (∑ e, p e) - (∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0) ≤
        (M.card : ℝ) := by
  let mass : Finset E → ℝ := fun S ↦ bernoulliMass univ p S
  let output : Finset E → ℝ := fun S ↦ (S.card : ℝ) - H.collisionScore S
  have hmass₀ : ∀ S, 0 ≤ mass S := by
    intro S
    exact bernoulliMass_nonneg (subset_univ S) (fun e _ ↦ hp₀ e) (fun e _ ↦ hp₁ e)
  have hmassSum : ∑ S, mass S = 1 := by
    simpa [mass] using sum_bernoulliMass (univ : Finset E) p
  have hcardMean : ∑ T, bernoulliMass univ p T * (T.card : ℝ) = ∑ e, p e := by
    simpa using sum_bernoulliMass_mul_card (univ : Finset E) p
  have hcollisionMean : ∑ T, bernoulliMass univ p T * H.collisionScore T =
      ∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0 := by
    simpa using sum_bernoulliMass_mul_collisionScore H p
  obtain ⟨S, hS⟩ := exists_output_ge_average mass output hmass₀ hmassSum
  refine ⟨H.isolatedSample S, H.isolatedSample_isMatching S, ?_⟩
  calc
    (∑ e, p e) - (∑ e, ∑ f, if H.Conflicts e f then p e * p f else 0) =
        ∑ T, mass T * output T := by
      simp only [mass, output, mul_sub, sum_sub_distrib]
      rw [hcardMean, hcollisionMean]
    _ ≤ output S := hS
    _ = (S.card : ℝ) - H.collisionCount S := by
      simp [output]
    _ ≤ (H.isolatedSample S).card := H.card_sub_collisionCount_le_isolatedSample S

end Hypergraph

end FiniteNibble

namespace FiniteHypergraph

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

private lemma conflict_product_le_incidence_sum (H : FiniteHypergraph V E) (w : E → ℝ)
    (hw₀ : ∀ e, 0 ≤ w e) (e f : E) :
    (if H.Conflicts e f then w e * w f else 0) ≤
      ∑ v ∈ H.vertexSet,
        if v ∈ H.support e ∧ v ∈ H.support f then w e * w f else 0 := by
  by_cases hconf : H.Conflicts e f
  · rw [if_pos hconf]
    obtain ⟨_, hnd⟩ := hconf
    obtain ⟨v, hve, hvf⟩ := not_disjoint_iff.mp hnd
    have hsingle :
        (if v ∈ H.support e ∧ v ∈ H.support f then w e * w f else 0) ≤
          ∑ x ∈ H.vertexSet,
            if x ∈ H.support e ∧ x ∈ H.support f then w e * w f else 0 := by
      refine single_le_sum (s := H.vertexSet)
        (f := fun x ↦ if x ∈ H.support e ∧ x ∈ H.support f then w e * w f else 0) ?_ ?_
      · intro x hx
        by_cases hmem : x ∈ H.support e ∧ x ∈ H.support f
        · simp [hmem, mul_nonneg (hw₀ e) (hw₀ f)]
        · simp [hmem]
      · exact H.support_subset_vertexSet e hve
    simpa [hve, hvf] using hsingle
  · simp only [hconf, if_false]
    exact sum_nonneg fun v _ ↦ by
      split <;> simp_all [mul_nonneg (hw₀ e) (hw₀ f)]

private lemma sum_incidence_products_eq_sum_vertexLoad_sq
    (H : FiniteHypergraph V E) (w : E → ℝ) :
    (∑ e, ∑ f, ∑ v ∈ H.vertexSet,
        if v ∈ H.support e ∧ v ∈ H.support f then w e * w f else 0) =
      ∑ v ∈ H.vertexSet, (H.vertexLoad w v) ^ 2 := by
  calc
    (∑ e, ∑ f, ∑ v ∈ H.vertexSet,
        if v ∈ H.support e ∧ v ∈ H.support f then w e * w f else 0) =
      ∑ e, ∑ v ∈ H.vertexSet, ∑ f,
        if v ∈ H.support e ∧ v ∈ H.support f then w e * w f else 0 := by
      apply sum_congr rfl
      intro e _
      rw [sum_comm]
    _ = ∑ v ∈ H.vertexSet, ∑ e, ∑ f,
        if v ∈ H.support e ∧ v ∈ H.support f then w e * w f else 0 := by
      rw [sum_comm]
    _ = ∑ v ∈ H.vertexSet, (H.vertexLoad w v) ^ 2 := by
      apply sum_congr rfl
      intro v _
      rw [vertexLoad, pow_two]
      simp only [sum_filter]
      rw [sum_mul]
      apply sum_congr rfl
      intro e _
      rw [mul_sum]
      apply sum_congr rfl
      intro f _
      by_cases he : v ∈ H.support e <;> by_cases hf : v ∈ H.support f <;>
        simp [he, hf]

/-- The weighted conflict quadratic form is controlled by the vertex loads.
This is the basic loss estimate in one nibble round. -/
lemma conflictWeight_le_sum_vertexLoad_sq (H : FiniteHypergraph V E) (w : E → ℝ)
    (hw₀ : ∀ e, 0 ≤ w e) :
    (∑ e, ∑ f, if H.Conflicts e f then w e * w f else 0) ≤
      ∑ v ∈ H.vertexSet, (H.vertexLoad w v) ^ 2 := by
  calc
    (∑ e, ∑ f, if H.Conflicts e f then w e * w f else 0) ≤
      ∑ e, ∑ f, ∑ v ∈ H.vertexSet,
        if v ∈ H.support e ∧ v ∈ H.support f then w e * w f else 0 := by
      apply sum_le_sum
      intro e _
      apply sum_le_sum
      intro f _
      exact H.conflict_product_le_incidence_sum w hw₀ e f
    _ = ∑ v ∈ H.vertexSet, (H.vertexLoad w v) ^ 2 :=
      H.sum_incidence_products_eq_sum_vertexLoad_sq w

lemma sum_vertexLoad_sq_le_card_mul_totalWeight {H : FiniteHypergraph V E} {w : E → ℝ}
    {k : ℕ} (hunif : H.IsUniform k) (hw : H.IsFractionalMatching w) :
    (∑ v ∈ H.vertexSet, (H.vertexLoad w v) ^ 2) ≤ (k : ℝ) * H.totalWeight w := by
  calc
    (∑ v ∈ H.vertexSet, (H.vertexLoad w v) ^ 2) ≤
        ∑ v ∈ H.vertexSet, H.vertexLoad w v := by
      apply sum_le_sum
      intro v hv
      have hload₀ : 0 ≤ H.vertexLoad w v := by
        exact sum_nonneg fun e _ ↦ hw.nonneg e
      simpa [pow_two] using
        mul_le_mul_of_nonneg_left (hw.vertexLoad_le_one hv) hload₀
    _ = ∑ e, ((H.support e).card : ℝ) * w e :=
      H.sum_vertexLoad_eq_sum_card_mul w
    _ = (k : ℝ) * H.totalWeight w := by
      rw [totalWeight, mul_sum]
      apply sum_congr rfl
      intro e _
      rw [hunif e]

lemma conflictWeight_le_card_mul_totalWeight {H : FiniteHypergraph V E} {w : E → ℝ}
    {k : ℕ} (hunif : H.IsUniform k) (hw : H.IsFractionalMatching w) :
    (∑ e, ∑ f, if H.Conflicts e f then w e * w f else 0) ≤
      (k : ℝ) * H.totalWeight w :=
  (H.conflictWeight_le_sum_vertexLoad_sq w hw.1).trans
    (H.sum_vertexLoad_sq_le_card_mul_totalWeight hunif hw)

/-- A scaled one-round nibble extracts the expected first-order fraction of a
fractional matching, with the standard quadratic collision loss. -/
lemma exists_matching_one_round_scaled {H : FiniteHypergraph V E} {w : E → ℝ}
    {k : ℕ} {tau : ℝ} (hk : 0 < k) (htau₀ : 0 ≤ tau) (htau₁ : tau ≤ 1)
    (hunif : H.IsUniform k) (hw : H.IsFractionalMatching w) :
    ∃ M : Finset E, H.IsMatching M ∧
      tau * (1 - (k : ℝ) * tau) * H.totalWeight w ≤ (M.card : ℝ) := by
  have hp₀ : ∀ e, 0 ≤ tau * w e := fun e ↦ mul_nonneg htau₀ (hw.nonneg e)
  have hp₁ : ∀ e, tau * w e ≤ 1 := by
    intro e
    have hwe := H.weight_le_one_of_uniform_pos hk hunif hw e
    have := mul_le_mul htau₁ hwe (hw.nonneg e) (by exact zero_le_one)
    simpa using this
  obtain ⟨M, hM, hround⟩ := FiniteNibble.exists_matching_one_round H
    (fun e ↦ tau * w e) hp₀ hp₁
  refine ⟨M, hM, ?_⟩
  have hsum : (∑ e, tau * w e) = tau * H.totalWeight w := by
    rw [totalWeight, mul_sum]
  have hscale :
      (∑ e, ∑ f, if H.Conflicts e f then (tau * w e) * (tau * w f) else 0) =
        tau ^ 2 * (∑ e, ∑ f, if H.Conflicts e f then w e * w f else 0) := by
    calc
      (∑ e, ∑ f, if H.Conflicts e f then (tau * w e) * (tau * w f) else 0) =
          ∑ e, ∑ f, tau ^ 2 *
            (if H.Conflicts e f then w e * w f else 0) := by
        apply sum_congr rfl
        intro e _
        apply sum_congr rfl
        intro f _
        by_cases hconf : H.Conflicts e f <;> simp [hconf, pow_two] <;> ring
      _ = tau ^ 2 * (∑ e, ∑ f, if H.Conflicts e f then w e * w f else 0) := by
        symm
        rw [mul_sum]
        apply sum_congr rfl
        intro e _
        rw [mul_sum]
  have hconf :
      (∑ e, ∑ f, if H.Conflicts e f then (tau * w e) * (tau * w f) else 0) ≤
        tau ^ 2 * ((k : ℝ) * H.totalWeight w) := by
    rw [hscale]
    exact mul_le_mul_of_nonneg_left
      (H.conflictWeight_le_card_mul_totalWeight hunif hw) (sq_nonneg tau)
  calc
    tau * (1 - (k : ℝ) * tau) * H.totalWeight w =
        tau * H.totalWeight w - tau ^ 2 * ((k : ℝ) * H.totalWeight w) := by ring
    _ ≤ tau * H.totalWeight w -
        (∑ e, ∑ f, if H.Conflicts e f then (tau * w e) * (tau * w f) else 0) :=
      sub_le_sub_left hconf _
    _ = (∑ e, tau * w e) -
        (∑ e, ∑ f, if H.Conflicts e f then (tau * w e) * (tau * w f) else 0) := by
      rw [hsum]
    _ ≤ (M.card : ℝ) := hround

/-! ## Unweighted degree parameters

These are the integer parameters in the Pippenger--Spencer form of the
nibble.  They deliberately count indexed edges, so parallel copies created
by discretizing a real fractional matching are retained.
-/

/-- Number of indexed hyperedges containing a vertex. -/
def edgeDegree (H : FiniteHypergraph V E) (v : V) : ℕ :=
  ((Finset.univ : Finset E).filter fun e ↦ v ∈ H.support e).card

/-- Number of indexed hyperedges containing both specified vertices. -/
def edgePairDegree (H : FiniteHypergraph V E) (u v : V) : ℕ :=
  ((Finset.univ : Finset E).filter fun e ↦ u ∈ H.support e ∧ v ∈ H.support e).card

/-- Number of indexed edges which conflict with a fixed indexed edge. -/
def conflictDegree (H : FiniteHypergraph V E) (e : E) : ℕ :=
  ((Finset.univ : Finset E).filter fun f ↦ H.Conflicts e f).card

/-- Number of edges through `v` which conflict with `f`.  In a nibble this is
the coefficient with which sampling `f` contributes to the loss of the
residual degree at `v`. -/
def conflictLink (H : FiniteHypergraph V E) (v : V) (f : E) : ℕ :=
  ((Finset.univ : Finset E).filter fun e ↦ v ∈ H.support e ∧ H.Conflicts e f).card

/-- The residual-degree loss coefficient with the edges through `v` removed.
Those incident edges are handled separately by the event that `v` itself is
covered. -/
def offConflictLink (H : FiniteHypergraph V E) (v : V) (f : E) : ℕ :=
  if v ∈ H.support f then 0 else H.conflictLink v f

lemma conflictDegree_le_card_mul {H : FiniteHypergraph V E} {D : ℕ}
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) (e : E) :
    H.conflictDegree e ≤ (H.support e).card * D := by
  let A : V → Finset E := fun v ↦
    (Finset.univ : Finset E).filter fun f ↦ v ∈ H.support f
  have hsub :
      ((Finset.univ : Finset E).filter fun f ↦ H.Conflicts e f) ⊆
        (H.support e).biUnion A := by
    intro f hf
    have hconf : H.Conflicts e f := (mem_filter.mp hf).2
    obtain ⟨_, hnd⟩ := hconf
    obtain ⟨v, hve, hvf⟩ := not_disjoint_iff.mp hnd
    exact mem_biUnion.mpr ⟨v, hve, by simp [A, hvf]⟩
  calc
    H.conflictDegree e ≤ ((H.support e).biUnion A).card := card_le_card hsub
    _ ≤ ∑ v ∈ H.support e, (A v).card := card_biUnion_le
    _ ≤ ∑ _v ∈ H.support e, D := by
      exact sum_le_sum fun v hv ↦ hdeg v (H.support_subset_vertexSet e hv)
    _ = (H.support e).card * D := by simp

lemma conflictDegree_le_uniform_mul {H : FiniteHypergraph V E} {D k : ℕ}
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) (e : E) :
    H.conflictDegree e ≤ k * D := by
  simpa [hunif e] using H.conflictDegree_le_card_mul hdeg e

lemma conflictLink_le_sum_pairDegree (H : FiniteHypergraph V E) (v : V) (f : E)
    (hvf : v ∉ H.support f) :
    H.conflictLink v f ≤ ∑ u ∈ H.support f, H.edgePairDegree v u := by
  let A : V → Finset E := fun u ↦
    (Finset.univ : Finset E).filter fun e ↦ v ∈ H.support e ∧ u ∈ H.support e
  have hsub :
      ((Finset.univ : Finset E).filter fun e ↦
          v ∈ H.support e ∧ H.Conflicts e f) ⊆
        (H.support f).biUnion A := by
    intro e he
    have he' := (mem_filter.mp he).2
    obtain ⟨_, hnd⟩ := he'.2
    obtain ⟨u, hue, huf⟩ := not_disjoint_iff.mp hnd
    exact mem_biUnion.mpr ⟨u, huf, by simp [A, he'.1, hue]⟩
  calc
    H.conflictLink v f ≤ ((H.support f).biUnion A).card := card_le_card hsub
    _ ≤ ∑ u ∈ H.support f, (A u).card := card_biUnion_le
    _ = ∑ u ∈ H.support f, H.edgePairDegree v u := by
      apply sum_congr rfl
      intro u hu
      simp [A, edgePairDegree]

/-- Off its sampled edge, every residual-degree loss coefficient is at most
`k C` when all distinct pair-degrees are at most `C`. -/
lemma conflictLink_le_uniform_mul {H : FiniteHypergraph V E} {C k : ℕ}
    (hunif : H.IsUniform k)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    {v : V} {f : E} (hvV : v ∈ H.vertexSet) (hvf : v ∉ H.support f) :
    H.conflictLink v f ≤ k * C := by
  calc
    H.conflictLink v f ≤ ∑ u ∈ H.support f, H.edgePairDegree v u :=
      H.conflictLink_le_sum_pairDegree v f hvf
    _ ≤ ∑ _u ∈ H.support f, C := by
      apply sum_le_sum
      intro u hu
      apply hpair v
      · exact hvV
      · exact H.support_subset_vertexSet f hu
      · exact fun hvu ↦ hvf (hvu ▸ hu)
    _ = k * C := by simp [hunif f]

lemma offConflictLink_le_uniform_mul {H : FiniteHypergraph V E} {C k : ℕ}
    (hunif : H.IsUniform k)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    {v : V} (hvV : v ∈ H.vertexSet) (f : E) :
    H.offConflictLink v f ≤ k * C := by
  by_cases hvf : v ∈ H.support f
  · simp [offConflictLink, hvf]
  · simpa [offConflictLink, hvf] using
      H.conflictLink_le_uniform_mul hunif hpair hvV hvf

lemma sum_conflictLink_eq (H : FiniteHypergraph V E) (v : V) :
    ∑ f, H.conflictLink v f =
      ∑ e with v ∈ H.support e, H.conflictDegree e := by
  simp only [conflictLink, conflictDegree, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  by_cases hve : v ∈ H.support e
  · simp [hve]
  · simp [hve]

/-- Summing a conflict link over all vertices counts every conflicting edge
once for each vertex in its support. -/
lemma sum_vertexSet_conflictLink_eq {H : FiniteHypergraph V E} {k : ℕ}
    (hunif : H.IsUniform k) (f : E) :
    ∑ v ∈ H.vertexSet, H.conflictLink v f = k * H.conflictDegree f := by
  simp only [conflictLink, conflictDegree, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  calc
    (∑ e, ∑ v ∈ H.vertexSet,
        if v ∈ H.support e ∧ H.Conflicts e f then 1 else 0) =
        ∑ e, if H.Conflicts e f then k else 0 := by
      apply sum_congr rfl
      intro e _
      by_cases hef : H.Conflicts e f
      · simp only [hef, and_true, if_true]
        rw [← sum_filter]
        have hfilter : H.vertexSet.filter (fun v ↦ v ∈ H.support e) =
            H.support e := by
          ext v
          simp only [mem_filter]
          exact and_iff_right_of_imp (fun hv ↦ H.support_subset_vertexSet e hv)
        rw [hfilter]
        simp [hunif e]
      · simp [hef]
    _ = k * ∑ e, if H.Conflicts f e then 1 else 0 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro e _
      by_cases hef : H.Conflicts e f
      · have hfe := hef.symm
        simp [hef, hfe]
      · have hfe : ¬H.Conflicts f e := fun h ↦ hef h.symm
        simp [hef, hfe]

/-- The total off-conflict coefficient of one sampled edge over the declared
vertex set is at most `k` times its conflict degree. -/
lemma sum_vertexSet_offConflictLink_le {H : FiniteHypergraph V E} {k : ℕ}
    (hunif : H.IsUniform k) (f : E) :
    ∑ v ∈ H.vertexSet, H.offConflictLink v f ≤ k * H.conflictDegree f := by
  calc
    ∑ v ∈ H.vertexSet, H.offConflictLink v f ≤
        ∑ v ∈ H.vertexSet, H.conflictLink v f := by
      apply sum_le_sum
      intro v hv
      simp only [offConflictLink]
      split <;> simp
    _ = k * H.conflictDegree f := H.sum_vertexSet_conflictLink_eq hunif f

lemma sum_offConflictLink_le {H : FiniteHypergraph V E} {D k : ℕ}
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) (v : V) :
    ∑ f, H.offConflictLink v f ≤ H.edgeDegree v * (k * D) := by
  calc
    ∑ f, H.offConflictLink v f ≤ ∑ f, H.conflictLink v f := by
      apply sum_le_sum
      intro f _
      simp only [offConflictLink]
      split <;> simp
    _ = ∑ e with v ∈ H.support e, H.conflictDegree e := H.sum_conflictLink_eq v
    _ ≤ ∑ e with v ∈ H.support e, k * D := by
      apply sum_le_sum
      intro e he
      exact H.conflictDegree_le_uniform_mul hunif hdeg e
    _ = H.edgeDegree v * (k * D) := by
      rw [sum_const, nsmul_eq_mul]
      rfl

/-- Double-counting the off-vertex conflict coefficients.  The right-hand
side counts, for each edge through `v`, all conflicting edges which avoid
`v`. -/
lemma sum_offConflictLink_eq (H : FiniteHypergraph V E) (v : V) :
    ∑ f, H.offConflictLink v f =
      ∑ e with v ∈ H.support e,
        ((Finset.univ : Finset E).filter fun f ↦
          v ∉ H.support f ∧ H.Conflicts e f).card := by
  simp only [offConflictLink, conflictLink, card_eq_sum_ones, sum_filter]
  calc
    (∑ f, if v ∈ H.support f then 0 else
        ∑ e, if v ∈ H.support e ∧ H.Conflicts e f then 1 else 0) =
        ∑ f, ∑ e, if v ∉ H.support f ∧ v ∈ H.support e ∧ H.Conflicts e f
          then 1 else 0 := by
      apply sum_congr rfl
      intro f _
      by_cases hvf : v ∈ H.support f <;> simp [hvf]
    _ = ∑ e, ∑ f, if v ∉ H.support f ∧ v ∈ H.support e ∧ H.Conflicts e f
          then 1 else 0 := sum_comm
    _ = ∑ e, if v ∈ H.support e then
        ∑ f, if v ∉ H.support f ∧ H.Conflicts e f then 1 else 0 else 0 := by
      apply sum_congr rfl
      intro e _
      by_cases hve : v ∈ H.support e <;> simp [hve]

/-- Every edge through `v` has many off-`v` conflicts when all vertex
degrees are large and all pair-degrees are small.  The proof chooses a
second vertex of the edge and partitions the edges through it according to
whether they also contain `v`. -/
lemma minDegree_sub_pairDegree_le_offConflictNeighborhood
    {H : FiniteHypergraph V E} {k D C : ℕ} (hk : 2 ≤ k)
    (hunif : H.IsUniform k)
    (hmin : ∀ u ∈ H.vertexSet, D ≤ H.edgeDegree u)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    {v : V} {e : E} (hve : v ∈ H.support e) :
    D ≤ C + ((Finset.univ : Finset E).filter fun f ↦
      v ∉ H.support f ∧ H.Conflicts e f).card := by
  have hcard : 1 < (H.support e).card := by
    rw [hunif e]
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp hcard
  obtain ⟨u, hue, huv⟩ : ∃ u ∈ H.support e, u ≠ v := by
    by_cases hxv : x = v
    · refine ⟨y, hy, ?_⟩
      intro hyv
      exact hxy (hxv.trans hyv.symm)
    · exact ⟨x, hx, hxv⟩
  let A : Finset E := (Finset.univ : Finset E).filter fun f ↦ u ∈ H.support f
  let B : Finset E := A.filter fun f ↦ v ∈ H.support f
  let Q : Finset E := A.filter fun f ↦ v ∉ H.support f
  let N : Finset E := (Finset.univ : Finset E).filter fun f ↦
    v ∉ H.support f ∧ H.Conflicts e f
  have hpartition : B.card + Q.card = A.card := by
    simpa only [B, Q] using A.card_filter_add_card_filter_not
      (fun f ↦ v ∈ H.support f)
  have hA : A.card = H.edgeDegree u := by
    rfl
  have hB : B.card = H.edgePairDegree u v := by
    apply congrArg card
    ext f
    simp [B, A, edgePairDegree, and_comm]
  have hQN : Q ⊆ N := by
    intro f hfQ
    have hfQ' := mem_filter.mp hfQ
    have huf : u ∈ H.support f := (mem_filter.mp hfQ'.1).2
    have hvf : v ∉ H.support f := hfQ'.2
    apply mem_filter.mpr
    refine ⟨mem_univ f, hvf, ?_⟩
    refine ⟨?_, ?_⟩
    · intro hef
      subst f
      exact hvf hve
    · exact not_disjoint_iff.mpr ⟨u, hue, huf⟩
  have hQcard : Q.card ≤ N.card := card_le_card hQN
  have hdeg : D ≤ H.edgeDegree u :=
    hmin u (H.support_subset_vertexSet e hue)
  have hcodeg : H.edgePairDegree u v ≤ C :=
    hpair u (H.support_subset_vertexSet e hue) v
      (H.support_subset_vertexSet e hve) huv
  change D ≤ C + N.card
  omega

/-- Summed form of the preceding pointwise lower bound. -/
lemma edgeDegree_mul_sub_le_sum_offConflictLink
    {H : FiniteHypergraph V E} {k D C : ℕ} (hk : 2 ≤ k)
    (hunif : H.IsUniform k)
    (hmin : ∀ u ∈ H.vertexSet, D ≤ H.edgeDegree u)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    (v : V) :
    H.edgeDegree v * (D - C) ≤ ∑ f, H.offConflictLink v f := by
  rw [H.sum_offConflictLink_eq v]
  calc
    H.edgeDegree v * (D - C) =
        ∑ _e with v ∈ H.support _e, (D - C) := by
      rw [sum_const, nsmul_eq_mul]
      rfl
    _ ≤ ∑ e with v ∈ H.support e,
        ((Finset.univ : Finset E).filter fun f ↦
          v ∉ H.support f ∧ H.Conflicts e f).card := by
      apply sum_le_sum
      intro e he
      have hpoint := H.minDegree_sub_pairDegree_le_offConflictNeighborhood
        hk hunif hmin hpair (v := v) (e := e) (mem_filter.mp he).2
      omega

/-- Square-sum bound for the coefficients governing one residual vertex
degree.  After multiplying by the Bernoulli probability `tau / D`, this is
the variance estimate `O(k² C tau d(v))`. -/
lemma sum_offConflictLink_sq_le {H : FiniteHypergraph V E} {C D k : ℕ}
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    {v : V} (hvV : v ∈ H.vertexSet) :
    ∑ f, (H.offConflictLink v f) ^ 2 ≤
      (k * C) * (H.edgeDegree v * (k * D)) := by
  calc
    ∑ f, (H.offConflictLink v f) ^ 2 ≤
        ∑ f, (k * C) * H.offConflictLink v f := by
      apply sum_le_sum
      intro f _
      rw [pow_two]
      exact Nat.mul_le_mul_right _ (H.offConflictLink_le_uniform_mul hunif hpair hvV f)
    _ = (k * C) * ∑ f, H.offConflictLink v f := by rw [mul_sum]
    _ ≤ (k * C) * (H.edgeDegree v * (k * D)) :=
      Nat.mul_le_mul_left _ (H.sum_offConflictLink_le hunif hdeg v)

/-! ## Deterministic residual-degree bookkeeping -/

/-- Indexed edges left after deleting all edges which meet a chosen matching.
The definition is useful for any selected family; matching is only needed when
iterating the construction. -/
def residualEdges (H : FiniteHypergraph V E) (M : Finset E) : Finset E :=
  (Finset.univ : Finset E).filter fun e ↦
    ∀ f ∈ M, Disjoint (H.support e) (H.support f)

/-- Degree of `v` in the family residual after `M`. -/
def residualDegree (H : FiniteHypergraph V E) (M : Finset E) (v : V) : ℕ :=
  (H.residualEdges M |>.filter fun e ↦ v ∈ H.support e).card

/-- `v` is not covered by any edge of the selected family. -/
def UncoveredBy (H : FiniteHypergraph V E) (M : Finset E) (v : V) : Prop :=
  ∀ f ∈ M, v ∉ H.support f

/-- Total off-vertex conflict coefficient contributed by a sample. -/
def sampleConflictLoad (H : FiniteHypergraph V E) (v : V) (S : Finset E) : ℕ :=
  ∑ f ∈ S, H.offConflictLink v f

lemma sum_conflictLink_on_eq (H : FiniteHypergraph V E) (v : V) (M : Finset E) :
    ∑ f ∈ M, H.conflictLink v f =
      ∑ e with v ∈ H.support e, (M.filter fun f ↦ H.Conflicts e f).card := by
  simp only [conflictLink, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  by_cases hve : v ∈ H.support e
  · simp [hve]
  · simp [hve]

lemma residualDegree_le_edgeDegree (H : FiniteHypergraph V E) (M : Finset E) (v : V) :
    H.residualDegree M v ≤ H.edgeDegree v := by
  apply card_le_card
  intro e he
  simp only [residualDegree, mem_filter, residualEdges] at he ⊢
  exact ⟨mem_univ e, he.2⟩

/-- Every edge through an uncovered vertex which is deleted from the residual
family is witnessed by a selected edge, and hence charged to one of the
off-vertex conflict coefficients. -/
lemma edgeDegree_le_residualDegree_add_sampleConflictLoad
    (H : FiniteHypergraph V E) (M : Finset E) (v : V)
    (hv : H.UncoveredBy M v) :
    H.edgeDegree v ≤ H.residualDegree M v + H.sampleConflictLoad v M := by
  let I : Finset E := (Finset.univ : Finset E).filter fun e ↦ v ∈ H.support e
  let R : Finset E := I.filter fun e ↦
    ∀ f ∈ M, Disjoint (H.support e) (H.support f)
  let L : E → Finset E := fun f ↦
    (Finset.univ : Finset E).filter fun e ↦ v ∈ H.support e ∧ H.Conflicts e f
  have hsub : I ⊆ R ∪ M.biUnion L := by
    intro e heI
    by_cases heR : ∀ f ∈ M, Disjoint (H.support e) (H.support f)
    · exact mem_union_left _ (mem_filter.mpr ⟨heI, heR⟩)
    · push Not at heR
      obtain ⟨f, hfM, hnd⟩ := heR
      have hef : e ≠ f := by
        intro hef
        subst f
        exact hv e hfM (mem_filter.mp heI).2
      apply mem_union_right
      exact mem_biUnion.mpr ⟨f, hfM, by
        simp only [L, mem_filter, mem_univ, true_and]
        exact ⟨(mem_filter.mp heI).2, hef, hnd⟩⟩
  calc
    H.edgeDegree v = I.card := by rfl
    _ ≤ (R ∪ M.biUnion L).card := card_le_card hsub
    _ ≤ R.card + (M.biUnion L).card := Finset.card_union_le R (M.biUnion L)
    _ ≤ R.card + ∑ f ∈ M, (L f).card :=
      Nat.add_le_add_left card_biUnion_le _
    _ = H.residualDegree M v + H.sampleConflictLoad v M := by
      have hR : R = (H.residualEdges M).filter (fun e ↦ v ∈ H.support e) := by
        ext e
        simp [R, I, residualEdges, and_comm]
      rw [hR]
      simp only [residualDegree, sampleConflictLoad]
      congr 1
      apply sum_congr rfl
      intro f hfM
      have hvf : v ∉ H.support f := hv f hfM
      simp [L, offConflictLink, conflictLink, hvf]

lemma sampleConflictLoad_mono (H : FiniteHypergraph V E) (v : V)
    {S T : Finset E} (hST : S ⊆ T) :
    H.sampleConflictLoad v S ≤ H.sampleConflictLoad v T := by
  exact sum_le_sum_of_subset_of_nonneg hST (fun _ _ _ ↦ Nat.zero_le _)

/-- For an uncovered vertex, each deleted incident edge is charged by at most
`k` selected matching edges.  Thus accepted conflict load forces a genuine
drop in residual degree. -/
lemma sampleConflictLoad_le_card_mul_degree_sub_residual
    {H : FiniteHypergraph V E} {k : ℕ} (hunif : H.IsUniform k)
    {M : Finset E} (hM : H.IsMatching M) {v : V} (hv : H.UncoveredBy M v) :
    H.sampleConflictLoad v M ≤
      k * (H.edgeDegree v - H.residualDegree M v) := by
  let I : Finset E := (Finset.univ : Finset E).filter fun e ↦ v ∈ H.support e
  let R : Finset E := I.filter fun e ↦
    ∀ f ∈ M, Disjoint (H.support e) (H.support f)
  have hRI : R ⊆ I := filter_subset _ _
  have hoff : H.sampleConflictLoad v M = ∑ f ∈ M, H.conflictLink v f := by
    apply sum_congr rfl
    intro f hfM
    simp [offConflictLink, hv f hfM]
  have hzero : ∀ e ∈ R, (M.filter fun f ↦ H.Conflicts e f).card = 0 := by
    intro e heR
    apply card_eq_zero.mpr
    ext f
    constructor
    · intro hf
      have hf' : f ∈ M ∧ H.Conflicts e f := mem_filter.mp hf
      exact False.elim (hf'.2.2 ((mem_filter.mp heR).2 f hf'.1))
    · simp
  have hpoint : ∀ e ∈ I,
      (M.filter fun f ↦ H.Conflicts e f).card ≤ if e ∈ R then 0 else k := by
    intro e heI
    by_cases heR : e ∈ R
    · simp [heR, hzero e heR]
    · simp only [heR, if_false]
      simpa [hunif e] using H.card_filter_conflicts_le_support_card hM e
  have hRcard : R.card = H.residualDegree M v := by
    have hR : R = (H.residualEdges M).filter (fun e ↦ v ∈ H.support e) := by
      ext e
      simp [R, I, residualEdges, and_comm]
    simp [hR, residualDegree]
  calc
    H.sampleConflictLoad v M =
        ∑ e with v ∈ H.support e, (M.filter fun f ↦ H.Conflicts e f).card := by
      rw [hoff, H.sum_conflictLink_on_eq]
    _ = ∑ e ∈ I, (M.filter fun f ↦ H.Conflicts e f).card := by rfl
    _ ≤ ∑ e ∈ I, if e ∈ R then 0 else k :=
      sum_le_sum hpoint
    _ = (I \ R).card * k := by
      have hrewrite :
          (∑ e ∈ I, if e ∈ R then 0 else k) =
            ∑ e ∈ I, if e ∉ R then k else 0 := by
        apply sum_congr rfl
        intro e heI
        by_cases heR : e ∈ R <;> simp [heR]
      rw [hrewrite, ← sum_filter, filter_notMem_eq_sdiff]
      simp
    _ = k * (H.edgeDegree v - H.residualDegree M v) := by
      rw [card_sdiff_of_subset hRI, hRcard]
      change (H.edgeDegree v - H.residualDegree M v) * k =
        k * (H.edgeDegree v - H.residualDegree M v)
      exact Nat.mul_comm _ _

/-- The isolated part of a Bernoulli sample has no larger conflict load than
the raw sample itself. -/
lemma edgeDegree_le_residual_isolated_add_sampleConflictLoad
    (H : FiniteHypergraph V E) (v : V) (S : Finset E)
    (hv : H.UncoveredBy (H.isolatedSample S) v) :
    H.edgeDegree v ≤
      H.residualDegree (H.isolatedSample S) v + H.sampleConflictLoad v S := by
  exact (H.edgeDegree_le_residualDegree_add_sampleConflictLoad
    (H.isolatedSample S) v hv).trans (Nat.add_le_add_left
      (H.sampleConflictLoad_mono v (H.isolatedSample_subset S)) _)

@[simp] lemma vertexLoad_const_eq_edgeDegree_div (H : FiniteHypergraph V E)
    (D : ℕ) (v : V) :
    H.vertexLoad (fun _ ↦ ((D : ℝ)⁻¹)) v = (H.edgeDegree v : ℝ) / (D : ℝ) := by
  simp [vertexLoad, edgeDegree, div_eq_mul_inv]

@[simp] lemma totalWeight_const_inv (H : FiniteHypergraph V E) (D : ℕ) :
    H.totalWeight (fun _ ↦ ((D : ℝ)⁻¹)) =
      (Fintype.card E : ℝ) / (D : ℝ) := by
  simp [totalWeight, div_eq_mul_inv]

/-- The reciprocal of a maximum degree is an unweighted fractional matching.
This is the bridge from integer degree hypotheses to the weighted one-round
alteration estimate. -/
lemma isFractionalMatching_const_inv {H : FiniteHypergraph V E} {D : ℕ}
    (hD : 0 < D) (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) :
    H.IsFractionalMatching (fun _ ↦ ((D : ℝ)⁻¹)) := by
  constructor
  · intro e
    positivity
  · intro v hv
    rw [H.vertexLoad_const_eq_edgeDegree_div]
    exact (div_le_one (by exact_mod_cast hD)).2 (by exact_mod_cast hdeg v hv)

/-- One unweighted alteration round under a maximum-degree bound.  The
codegree assumption is not yet needed at this first-order stage; it enters
when controlling the residual degrees through subsequent rounds. -/
lemma exists_matching_degree_round {H : FiniteHypergraph V E} {D k : ℕ}
    {tau : ℝ} (hD : 0 < D) (hk : 0 < k) (htau₀ : 0 ≤ tau) (htau₁ : tau ≤ 1)
    (hunif : H.IsUniform k) (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) :
    ∃ M : Finset E, H.IsMatching M ∧
      tau * (1 - (k : ℝ) * tau) *
          ((Fintype.card E : ℝ) / (D : ℝ)) ≤ (M.card : ℝ) := by
  simpa using H.exists_matching_one_round_scaled hk htau₀ htau₁ hunif
    (H.isFractionalMatching_const_inv hD hdeg)

/-- A matching in a `k`-uniform hypergraph covers exactly `k` vertices per
edge, and all covered vertices lie in the declared vertex set. -/
lemma card_mul_matching_le_vertexSet {H : FiniteHypergraph V E} {k : ℕ}
    (hunif : H.IsUniform k) {M : Finset E} (hM : H.IsMatching M) :
    k * M.card ≤ H.vertexSet.card := by
  have hsub : M.biUnion H.support ⊆ H.vertexSet := by
    intro v hv
    obtain ⟨e, heM, hve⟩ := mem_biUnion.mp hv
    exact H.support_subset_vertexSet e hve
  calc
    k * M.card = ∑ _e ∈ M, k := by simp [Nat.mul_comm]
    _ = ∑ e ∈ M, (H.support e).card := by
      apply sum_congr rfl
      intro e he
      exact (hunif e).symm
    _ = (M.biUnion H.support).card := (card_biUnion hM).symm
    _ ≤ H.vertexSet.card := card_le_card hsub

end FiniteHypergraph

/-! ## The unweighted and weighted multiplicative nibble statements

The maximum-degree form below is the precise unweighted theorem used by the
integer-copy reduction.  The lower threshold on `D` is essential: this is an
asymptotic theorem with the uniformity fixed.
-/

/-- Maximum-degree Pippenger--Spencer matching theorem, in the finite form
suited to discretizing a real fractional matching into parallel copies. -/
def PippengerSpencerMatching : Prop :=
  ∀ k : ℕ, 0 < k → ∀ epsilon : ℝ, 0 < epsilon →
    ∃ eta : ℝ, 0 < eta ∧ ∃ D₀ : ℕ,
      ∀ (V E : Type) [DecidableEq V] [Fintype E] [DecidableEq E],
        ∀ (H : FiniteHypergraph V E) (D : ℕ),
          D₀ ≤ D → H.IsUniform k →
          (∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) →
          (∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
            (H.edgePairDegree u v : ℝ) < eta * (D : ℝ)) →
          ∃ M : Finset E, H.IsMatching M ∧
            (1 - epsilon) * (Fintype.card E : ℝ) / (D : ℝ) ≤ (M.card : ℝ)

/-! ## Reduction to the multiplicative nibble theorem

The probabilistic heart is most naturally stated with a relative loss.  The
additive form used by Erdős 76 is an immediate consequence of incidence
double-counting.
-/

/-- Standard multiplicative cardinality form of Kahn's weighted nibble. -/
def KahnMultiplicativeMatching : Prop :=
  ∀ k : ℕ, 0 < k → ∀ rho : ℝ, 0 < rho → ∃ delta : ℝ, 0 < delta ∧
    ∀ (V E : Type) [DecidableEq V] [Fintype E] [DecidableEq E],
      ∀ (H : FiniteHypergraph V E) (w : E → ℝ),
        H.IsUniform k → H.IsFractionalMatching w → H.PairCodegreeLT w delta →
          ∃ M : Finset E, H.IsMatching M ∧
            (1 - rho) * H.totalWeight w ≤ (M.card : ℝ)

/-- The standard multiplicative theorem implies the repository's additive
`KahnWeightedMatching` interface. -/
theorem kahnWeightedMatching_of_multiplicative
    (hKahn : KahnMultiplicativeMatching) : KahnWeightedMatching := by
  intro k hk zeta hzeta
  let rho : ℝ := min (1 / 2) ((k : ℝ) * zeta)
  have hrho : 0 < rho := by
    apply lt_min
    · positivity
    · exact mul_pos (by exact_mod_cast hk) hzeta
  obtain ⟨delta, hdelta, hround⟩ := hKahn k hk rho hrho
  refine ⟨delta, hdelta, ?_⟩
  intro V E _ _ _ H w hunif hw hcodeg
  obtain ⟨M, hM, hsize⟩ := hround V E H w hunif hw hcodeg
  refine ⟨M, hM, ?_⟩
  have htotal₀ : 0 ≤ H.totalWeight w := H.totalWeight_nonneg hw
  have hrho_le : rho ≤ (k : ℝ) * zeta := min_le_right _ _
  have hloss : rho * H.totalWeight w ≤ zeta * H.vertexSet.card := by
    calc
      rho * H.totalWeight w ≤ ((k : ℝ) * zeta) * H.totalWeight w :=
        mul_le_mul_of_nonneg_right hrho_le htotal₀
      _ = zeta * ((k : ℝ) * H.totalWeight w) := by ring
      _ ≤ zeta * H.vertexSet.card :=
        mul_le_mul_of_nonneg_left (H.card_mul_totalWeight_le_vertexSet_card hunif hw) hzeta.le
  calc
    H.totalWeight w = (1 - rho) * H.totalWeight w + rho * H.totalWeight w := by ring
    _ ≤ (M.card : ℝ) + rho * H.totalWeight w :=
      add_le_add hsize (le_refl (rho * H.totalWeight w))
    _ ≤ (M.card : ℝ) + zeta * H.vertexSet.card :=
      add_le_add (le_refl (M.card : ℝ)) hloss

end


end Erdos76
