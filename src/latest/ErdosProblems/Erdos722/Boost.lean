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
import ErdosProblems.Erdos722.LocalDecoder
import ErdosProblems.Erdos722.Probability
import ErdosProblems.Erdos722.Typicality
import ErdosProblems.Erdos722.Counting
import Mathlib

/-!
# Local-decoder regularity boost

This file develops the exact finite linear-algebraic part of Keevash's
regularity boost.  Starting from the nearly constant weight on all available
`q`-cliques, averaged copies of the checked local decoder correct every edge
degree exactly.  The later probabilistic rounding only has to concentrate
independent Bernoulli coordinates around these exact means.
-/

namespace Erdos722.Boost

open Finset

noncomputable section

/-- `q`-sets all of whose `r`-subsets belong to `G`. -/
def cliqueFamily (n q r : ℕ) (G : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  (Typicality.uniformEdges n q).filter fun Q ↦ Q.powersetCard r ⊆ G

/-- Available `(q+r)`-sets through an edge, on which every local decoder is
supported entirely inside `G`. -/
def decoderAmbients (n q r : ℕ) (G : Finset (Finset (Fin n)))
    (e : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  (Typicality.uniformEdges n (q + r)).filter fun Z ↦
    e ⊆ Z ∧ Z.powersetCard r ⊆ G

/-- Exact number of `q`-sets through a fixed `r`-edge in the complete host.
Using the exact count `choose (n-r) (q-r)` removes a harmless lower-order
normalization error from the paper's `choose n (q-r)` convention. -/
def extensionScale (n q r : ℕ) : ℕ := Nat.choose (n - r) (q - r)

/-- Complete-host `r`-edges omitted from `G`. -/
def complementEdges (n r : ℕ) (G : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  Typicality.uniformEdges n r \ G

/-- Complete-host number of `(q+r)`-sets through an `r`-edge. -/
def ambientScale (n q r : ℕ) : ℕ := Nat.choose (n - r) q

/-- The initial normalized weight: `1/(2 choose(n,q-r))` on every
available clique and zero elsewhere. -/
def baseWeight (n q r : ℕ) (G : Finset (Finset (Fin n)))
    (Q : Finset (Fin n)) : ℝ :=
  if Q ∈ cliqueFamily n q r G then
    1 / (2 * extensionScale n q r : ℕ)
  else 0

/-- Weighted degree of an edge in a real vector on `q`-sets. -/
def weightedDegree (n q : ℕ) (w : Finset (Fin n) → ℝ)
    (e : Finset (Fin n)) : ℝ :=
  ∑ Q ∈ Typicality.uniformEdges n q, if e ⊆ Q then w Q else 0

/-- Defect of the base weight from the desired normalized degree `1/2`. -/
def degreeDefect (n q r : ℕ) (G : Finset (Finset (Fin n)))
    (e : Finset (Fin n)) : ℝ :=
  1 / 2 - weightedDegree n q (baseWeight n q r G) e

/-- Number of available `q`-cliques through one edge. -/
def availableDegree (n q r : ℕ) (G : Finset (Finset (Fin n)))
    (e : Finset (Fin n)) : ℕ :=
  ((cliqueFamily n q r G).filter (e ⊆ ·)).card

/-- One averaged local-decoder summand.  The explicit support guard is
important: `LocalDecoder.decoderWeight` is an algebraic formula on every
set, whereas the decoder vector is supported only on the `q`-subsets of
its ambient `(q+r)`-set. -/
def averagedDecoderTerm (n q r : ℕ) (G : Finset (Finset (Fin n)))
    (e Z Q : Finset (Fin n)) : ℝ :=
  if Q ∈ Z.powersetCard q then
    degreeDefect n q r G e /
        (decoderAmbients n q r G e).card *
      LocalDecoder.decoderWeight q r Z e Q
  else 0

/-- Sum of all averaged decoder corrections. -/
def correctionWeight (n q r : ℕ) (G : Finset (Finset (Fin n)))
    (Q : Finset (Fin n)) : ℝ :=
  ∑ e ∈ G, ∑ Z ∈ decoderAmbients n q r G e,
    averagedDecoderTerm n q r G e Z Q

/-- Corrected normalized weight. -/
def correctedWeight (n q r : ℕ) (G : Finset (Finset (Fin n)))
    (Q : Finset (Fin n)) : ℝ :=
  baseWeight n q r G Q + correctionWeight n q r G Q

@[simp] theorem mem_cliqueFamily {G : Finset (Finset (Fin n))}
    {Q : Finset (Fin n)} :
    Q ∈ cliqueFamily n q r G ↔ Q.card = q ∧ Q.powersetCard r ⊆ G := by
  simp [cliqueFamily, Typicality.uniformEdges]

@[simp] theorem mem_decoderAmbients {G : Finset (Finset (Fin n))}
    {e Z : Finset (Fin n)} :
    Z ∈ decoderAmbients n q r G e ↔
      Z.card = q + r ∧ e ⊆ Z ∧ Z.powersetCard r ⊆ G := by
  simp [decoderAmbients, Typicality.uniformEdges]

private lemma filtered_uniform_subset_eq
    {Z e' : Finset (Fin n)} :
    (Typicality.uniformEdges n q).filter (fun Q ↦ e' ⊆ Q ∧ Q ⊆ Z) =
      (Z.powersetCard q).filter (e' ⊆ ·) := by
  ext Q
  simp only [Finset.mem_filter, Typicality.mem_uniformEdges,
    Finset.mem_powersetCard]
  aesop

private lemma weightedDegree_add (n q : ℕ)
    (w₁ w₂ : Finset (Fin n) → ℝ) (e : Finset (Fin n)) :
    weightedDegree n q (fun Q ↦ w₁ Q + w₂ Q) e =
      weightedDegree n q w₁ e + weightedDegree n q w₂ e := by
  unfold weightedDegree
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Q hQ
  by_cases heQ : e ⊆ Q <;> simp [heQ]

/-- The complete-host incident family has the exact normalizing cardinality.
-/
theorem card_incident_uniformEdges
    {n q r : ℕ} (hrq : r ≤ q) {e : Finset (Fin n)}
    (hecard : e.card = r) :
    ((Typicality.uniformEdges n q).filter (e ⊆ ·)).card =
      extensionScale n q r := by
  rw [Typicality.uniformEdges,
    Finset.card_filter_powersetCard_subset e Finset.univ q
      (Finset.subset_univ e) (by omega),
    hecard]
  simp [extensionScale]

/-- The base weighted degree is the available-clique count divided by
twice the complete-host incident count. -/
theorem weightedDegree_baseWeight
    {n q r : ℕ} {G : Finset (Finset (Fin n))}
    {e : Finset (Fin n)} :
    weightedDegree n q (baseWeight n q r G) e =
      (availableDegree n q r G e : ℝ) /
        (2 * extensionScale n q r : ℕ) := by
  classical
  rw [weightedDegree]
  have hsub : cliqueFamily n q r G ⊆ Typicality.uniformEdges n q := by
    intro Q hQ
    exact Typicality.mem_uniformEdges.mpr (mem_cliqueFamily.mp hQ).1
  calc
    (∑ Q ∈ Typicality.uniformEdges n q,
        if e ⊆ Q then baseWeight n q r G Q else 0) =
        ∑ Q ∈ cliqueFamily n q r G,
          if e ⊆ Q then baseWeight n q r G Q else 0 := by
      symm
      apply Finset.sum_subset hsub
      intro Q hQ hQnot
      have hQnotClique : Q ∉ cliqueFamily n q r G := by
        exact hQnot
      simp [baseWeight, hQnotClique]
    _ = ∑ Q ∈ cliqueFamily n q r G,
          if e ⊆ Q then (1 : ℝ) / (2 * extensionScale n q r : ℕ)
            else 0 := by
      apply Finset.sum_congr rfl
      intro Q hQ
      by_cases heQ : e ⊆ Q
      · simp [heQ, baseWeight, hQ]
      · simp [heQ]
    _ = ∑ Q ∈ (cliqueFamily n q r G).filter (e ⊆ ·),
          (1 : ℝ) / (2 * extensionScale n q r : ℕ) := by
      rw [Finset.sum_filter]
    _ = (availableDegree n q r G e : ℝ) /
          (2 * extensionScale n q r : ℕ) := by
      simp [availableDegree, div_eq_mul_inv]

/-- Exact nonnegative defect formula when the normalizing incident count is
positive. -/
theorem degreeDefect_eq
    {n q r : ℕ} (hrq : r ≤ q) {G : Finset (Finset (Fin n))}
    {e : Finset (Fin n)} (hecard : e.card = r)
    (hscale : 0 < extensionScale n q r) :
    degreeDefect n q r G e =
      ((extensionScale n q r - availableDegree n q r G e : ℕ) : ℝ) /
        (2 * extensionScale n q r : ℕ) := by
  have havail : availableDegree n q r G e ≤ extensionScale n q r := by
    unfold availableDegree
    rw [← card_incident_uniformEdges hrq hecard]
    apply Finset.card_le_card
    intro Q hQ
    have hm := Finset.mem_filter.mp hQ
    exact Finset.mem_filter.mpr
      ⟨Typicality.mem_uniformEdges.mpr (mem_cliqueFamily.mp hm.1).1, hm.2⟩
  rw [degreeDefect, weightedDegree_baseWeight]
  push_cast
  rw [Nat.cast_sub havail]
  have hscaleR : (extensionScale n q r : ℝ) ≠ 0 := by exact_mod_cast hscale.ne'
  field_simp

theorem degreeDefect_nonneg
    {n q r : ℕ} (hrq : r ≤ q) {G : Finset (Finset (Fin n))}
    {e : Finset (Fin n)} (hecard : e.card = r)
    (hscale : 0 < extensionScale n q r) :
    0 ≤ degreeDefect n q r G e := by
  rw [degreeDefect_eq hrq hecard hscale]
  positivity

/-! ## Counting the cliques lost to a sparse complement -/

lemma complementEdges_uniform
    {n r : ℕ} {G : Finset (Finset (Fin n))} :
    ∀ f ∈ complementEdges n r G, f.card = r := by
  intro f hf
  exact Typicality.mem_uniformEdges.mp (Finset.mem_sdiff.mp hf).1

private lemma incident_clique_eq_sdiff_spoiled
    {n q r : ℕ} {G : Finset (Finset (Fin n))}
    {e : Finset (Fin n)} :
    (cliqueFamily n q r G).filter (e ⊆ ·) =
      ((Typicality.uniformEdges n q).filter (e ⊆ ·)) \
        Counting.spoiledExtensions n q (complementEdges n r G) e := by
  classical
  ext Q
  constructor
  · intro hQ
    have hm := Finset.mem_filter.mp hQ
    have hc := mem_cliqueFamily.mp hm.1
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_filter.mpr
      ⟨Typicality.mem_uniformEdges.mpr hc.1, hm.2⟩, ?_⟩
    intro hspoiled
    obtain ⟨hQu, heQ, f, hfcomp, hfQ⟩ :=
      Finset.mem_filter.mp hspoiled
    have hfr : f ∈ Q.powersetCard r :=
      Finset.mem_powersetCard.mpr
        ⟨hfQ, Typicality.mem_uniformEdges.mp
          (Finset.mem_sdiff.mp hfcomp).1⟩
    exact (Finset.mem_sdiff.mp hfcomp).2 (hc.2 hfr)
  · intro hQ
    have hm := Finset.mem_sdiff.mp hQ
    have hU := Finset.mem_filter.mp hm.1
    apply Finset.mem_filter.mpr
    refine ⟨mem_cliqueFamily.mpr
      ⟨Typicality.mem_uniformEdges.mp hU.1, ?_⟩, hU.2⟩
    intro f hf
    by_contra hfG
    have hfcomp : f ∈ complementEdges n r G :=
      Finset.mem_sdiff.mpr ⟨Typicality.mem_uniformEdges.mpr
        (Finset.mem_powersetCard.mp hf).2, hfG⟩
    exact hm.2 (Finset.mem_filter.mpr ⟨hU.1, hU.2,
      f, hfcomp, (Finset.mem_powersetCard.mp hf).1⟩)

theorem availableDegree_eq_sub_spoiled
    {n q r : ℕ} (hrq : r ≤ q) {G : Finset (Finset (Fin n))}
    {e : Finset (Fin n)} (hecard : e.card = r) :
    availableDegree n q r G e = extensionScale n q r -
      (Counting.spoiledExtensions n q (complementEdges n r G) e).card := by
  classical
  unfold availableDegree
  rw [incident_clique_eq_sdiff_spoiled]
  rw [Finset.card_sdiff_of_subset]
  · rw [card_incident_uniformEdges hrq hecard]
  · intro Q hQ
    have hm := Finset.mem_filter.mp hQ
    exact Finset.mem_filter.mpr ⟨hm.1, hm.2.1⟩

/-- Explicit defect bound supplied by the sparse-extension estimate. -/
theorem abs_degreeDefect_le_sparse
    {n q r D : ℕ} (hr : 0 < r) (hqr : r < q)
    {G : Finset (Finset (Fin n))}
    (hdegree : Counting.LowerDegreeLE n r D (complementEdges n r G))
    {e : Finset (Fin n)} (he : e ∈ G) (hecard : e.card = r)
    (hscale : 0 < extensionScale n q r) :
    |degreeDefect n q r G e| ≤
      (((q - r) * n ^ (q - r - 1) * (2 ^ q * D) : ℕ) : ℝ) /
        (2 * extensionScale n q r : ℕ) := by
  have heNot : e ∉ complementEdges n r G := by
    intro hec
    exact (Finset.mem_sdiff.mp hec).2 he
  have hspoiled := Counting.card_spoiledExtensions_le hr hqr
    complementEdges_uniform hdegree hecard heNot
  rw [degreeDefect_eq hqr.le hecard hscale,
    availableDegree_eq_sub_spoiled hqr.le hecard]
  have hspLe :
      (Counting.spoiledExtensions n q (complementEdges n r G) e).card ≤
        extensionScale n q r := by
    rw [← card_incident_uniformEdges hqr.le hecard]
    apply Finset.card_le_card
    intro Q hQ
    have hm := Finset.mem_filter.mp hQ
    exact Finset.mem_filter.mpr ⟨hm.1, hm.2.1⟩
  rw [Nat.sub_sub_self hspLe]
  rw [abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hspoiled) (by positivity)

private lemma decoderAmbients_eq_sdiff_spoiled
    {n q r : ℕ} {G : Finset (Finset (Fin n))}
    {e : Finset (Fin n)} :
    decoderAmbients n q r G e =
      ((Typicality.uniformEdges n (q + r)).filter (e ⊆ ·)) \
        Counting.spoiledExtensions n (q + r)
          (complementEdges n r G) e := by
  classical
  ext Z
  constructor
  · intro hZ
    have hz := mem_decoderAmbients.mp hZ
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_filter.mpr
      ⟨Typicality.mem_uniformEdges.mpr hz.1, hz.2.1⟩, ?_⟩
    intro hspoiled
    obtain ⟨hZu, heZ, f, hfcomp, hfZ⟩ :=
      Finset.mem_filter.mp hspoiled
    have hfr : f ∈ Z.powersetCard r :=
      Finset.mem_powersetCard.mpr
        ⟨hfZ, Typicality.mem_uniformEdges.mp
          (Finset.mem_sdiff.mp hfcomp).1⟩
    exact (Finset.mem_sdiff.mp hfcomp).2 (hz.2.2 hfr)
  · intro hZ
    have hm := Finset.mem_sdiff.mp hZ
    have hU := Finset.mem_filter.mp hm.1
    apply mem_decoderAmbients.mpr
    refine ⟨Typicality.mem_uniformEdges.mp hU.1, hU.2, ?_⟩
    intro f hf
    by_contra hfG
    have hfcomp : f ∈ complementEdges n r G :=
      Finset.mem_sdiff.mpr ⟨Typicality.mem_uniformEdges.mpr
        (Finset.mem_powersetCard.mp hf).2, hfG⟩
    exact hm.2 (Finset.mem_filter.mpr ⟨hU.1, hU.2,
      f, hfcomp, (Finset.mem_powersetCard.mp hf).1⟩)

theorem card_decoderAmbients_eq_sub_spoiled
    {n q r : ℕ} {G : Finset (Finset (Fin n))}
    {e : Finset (Fin n)} (hecard : e.card = r) :
    (decoderAmbients n q r G e).card = ambientScale n q r -
      (Counting.spoiledExtensions n (q + r)
        (complementEdges n r G) e).card := by
  classical
  rw [decoderAmbients_eq_sdiff_spoiled, Finset.card_sdiff_of_subset]
  · rw [card_incident_uniformEdges (by omega : r ≤ q + r) hecard]
    simp [extensionScale, ambientScale]
  · intro Z hZ
    have hm := Finset.mem_filter.mp hZ
    exact Finset.mem_filter.mpr ⟨hm.1, hm.2.1⟩

theorem decoderAmbients_nonempty_of_sparse
    {n q r D : ℕ} (hr : 0 < r) (hqr : r < q)
    {G : Finset (Finset (Fin n))}
    (hdegree : Counting.LowerDegreeLE n r D (complementEdges n r G))
    {e : Finset (Fin n)} (he : e ∈ G) (hecard : e.card = r)
    (hlarge : q * n ^ (q - 1) * (2 ^ (q + r) * D) <
      ambientScale n q r) :
    (decoderAmbients n q r G e).Nonempty := by
  have heNot : e ∉ complementEdges n r G := by
    intro hec
    exact (Finset.mem_sdiff.mp hec).2 he
  have hspoiled := Counting.card_spoiledExtensions_le hr
    (by omega : r < q + r) complementEdges_uniform hdegree hecard heNot
  have hless :
      (Counting.spoiledExtensions n (q + r)
        (complementEdges n r G) e).card < ambientScale n q r := by
    calc
      _ ≤ ((q + r - r) * n ^ (q + r - r - 1) *
          (2 ^ (q + r) * D)) := hspoiled
      _ = q * n ^ (q - 1) * (2 ^ (q + r) * D) := by
        simp [Nat.add_sub_cancel]
      _ < ambientScale n q r := hlarge
  apply Finset.card_pos.mp
  rw [card_decoderAmbients_eq_sub_spoiled hecard]
  omega

/-- Pairs `(e,Z)` which contribute to the correction of a fixed clique. -/
def correctionPairs (n q r : ℕ) (G : Finset (Finset (Fin n)))
    (Q : Finset (Fin n)) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  (G ×ˢ Typicality.uniformEdges n (q + r)).filter fun p ↦
    p.2 ∈ decoderAmbients n q r G p.1 ∧ Q ∈ p.2.powersetCard q

/-- All pairs `(e,Z)` with `Q ⊆ Z` and `e` an `r`-subset of `Z`. -/
def ambientEdgePairs (n q r : ℕ) (Q : Finset (Fin n)) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  ((Typicality.uniformEdges n (q + r)).filter (Q ⊆ ·)).biUnion
    fun Z ↦ (Z.powersetCard r).image fun e ↦ (e, Z)

theorem correctionPairs_subset_ambientEdgePairs
    {n q r : ℕ} {G : Finset (Finset (Fin n))}
    (huniform : ∀ e ∈ G, e.card = r) (Q : Finset (Fin n)) :
    correctionPairs n q r G Q ⊆ ambientEdgePairs n q r Q := by
  intro p hp
  have hm := Finset.mem_filter.mp hp
  have hpG := Finset.mem_product.mp hm.1
  have hZ := mem_decoderAmbients.mp hm.2.1
  have hQZ := Finset.mem_powersetCard.mp hm.2.2
  apply Finset.mem_biUnion.mpr
  refine ⟨p.2, Finset.mem_filter.mpr
    ⟨Typicality.mem_uniformEdges.mpr hZ.1, hQZ.1⟩, ?_⟩
  exact Finset.mem_image.mpr ⟨p.1,
    Finset.mem_powersetCard.mpr ⟨hZ.2.1, huniform p.1 hpG.1⟩, rfl⟩

theorem card_ambientEdgePairs_le
    {n q r : ℕ} {Q : Finset (Fin n)} (hQcard : Q.card = q) :
    (ambientEdgePairs n q r Q).card ≤ n ^ r * 2 ^ (q + r) := by
  classical
  let Zs := (Typicality.uniformEdges n (q + r)).filter (Q ⊆ ·)
  calc
    (ambientEdgePairs n q r Q).card ≤
        ∑ Z ∈ Zs, ((Z.powersetCard r).image fun e ↦ (e, Z)).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _Z ∈ Zs, 2 ^ (q + r) := by
      apply Finset.sum_le_sum
      intro Z hZ
      calc
        ((Z.powersetCard r).image fun e ↦ (e, Z)).card ≤
            (Z.powersetCard r).card := Finset.card_image_le
        _ = Nat.choose (q + r) r := by
          rw [Finset.card_powersetCard]
          exact congrArg (fun t ↦ Nat.choose t r)
            (Typicality.mem_uniformEdges.mp (Finset.mem_filter.mp hZ).1)
        _ ≤ 2 ^ (q + r) := Nat.choose_le_two_pow _ _
    _ = Zs.card * 2 ^ (q + r) := by simp
    _ ≤ n ^ r * 2 ^ (q + r) := by
      apply Nat.mul_le_mul_right
      have hZcard : Zs.card = Nat.choose (n - q) r := by
        dsimp [Zs]
        rw [Typicality.uniformEdges,
          Finset.card_filter_powersetCard_subset Q Finset.univ (q + r)
            (Finset.subset_univ Q) (by omega), hQcard]
        simp
      rw [hZcard]
      exact (Nat.choose_le_pow (n - q) r).trans
        (Nat.pow_le_pow_left (Nat.sub_le n q) r)

theorem card_correctionPairs_le
    {n q r : ℕ} {G : Finset (Finset (Fin n))}
    (huniform : ∀ e ∈ G, e.card = r)
    {Q : Finset (Fin n)} (hQcard : Q.card = q) :
    (correctionPairs n q r G Q).card ≤ n ^ r * 2 ^ (q + r) :=
  (Finset.card_le_card (correctionPairs_subset_ambientEdgePairs huniform Q)).trans
    (card_ambientEdgePairs_le hQcard)

/-- One ambient decoder has normalized boundary one at its root edge and
zero at every other `r`-edge. -/
theorem sum_averagedDecoderTerm
    {n q r : ℕ} (hrq : r ≤ q)
    {G : Finset (Finset (Fin n))} {e e' Z : Finset (Fin n)}
    (hecard : e.card = r) (he'card : e'.card = r)
    (hZ : Z ∈ decoderAmbients n q r G e) :
    (∑ Q ∈ Typicality.uniformEdges n q,
        if e' ⊆ Q then averagedDecoderTerm n q r G e Z Q else 0) =
      degreeDefect n q r G e /
          (decoderAmbients n q r G e).card *
        (if e = e' then 1 else 0) := by
  classical
  have he'Z_or : e' ⊆ Z ∨ ¬ e' ⊆ Z := em _
  rcases he'Z_or with he'Z | he'Z
  · rw [show (∑ Q ∈ Typicality.uniformEdges n q,
          if e' ⊆ Q then averagedDecoderTerm n q r G e Z Q else 0) =
        ∑ Q ∈ (Typicality.uniformEdges n q).filter
            (fun Q ↦ e' ⊆ Q ∧ Q ⊆ Z),
          degreeDefect n q r G e /
              (decoderAmbients n q r G e).card *
            LocalDecoder.decoderWeight q r Z e Q by
        calc
          _ = ∑ Q ∈ Typicality.uniformEdges n q,
              if e' ⊆ Q ∧ Q ⊆ Z then
                degreeDefect n q r G e /
                    (decoderAmbients n q r G e).card *
                  LocalDecoder.decoderWeight q r Z e Q
              else 0 := by
            apply Finset.sum_congr rfl
            intro Q hQ
            have hQcard : Q.card = q := Typicality.mem_uniformEdges.mp hQ
            by_cases he'Q : e' ⊆ Q <;> by_cases hQZ : Q ⊆ Z <;>
              simp [averagedDecoderTerm, he'Q, hQZ,
                Finset.mem_powersetCard.mpr, hQcard]
          _ = _ := by rw [Finset.sum_filter]]
    rw [filtered_uniform_subset_eq]
    rw [← Finset.mul_sum]
    rw [LocalDecoder.sum_decoderWeight hrq
      (mem_decoderAmbients.mp hZ).1 hecard he'card
      (mem_decoderAmbients.mp hZ).2.1 he'Z]
  · have hne : e ≠ e' := by
      intro h
      exact he'Z (h ▸ (mem_decoderAmbients.mp hZ).2.1)
    rw [if_neg hne]
    simp only [mul_zero]
    apply Finset.sum_eq_zero
    intro Q hQ
    by_cases he'Q : e' ⊆ Q
    · rw [if_pos he'Q]
      have hQnot : Q ∉ Z.powersetCard q := fun hQZ ↦
        he'Z (he'Q.trans (Finset.mem_powersetCard.mp hQZ).1)
      simp [averagedDecoderTerm, hQnot]
    · simp [he'Q]

/-- The total decoder correction has boundary equal to the base-degree
defect.  This is the exact finite identity at the heart of regularity
boosting. -/
theorem weightedDegree_correctionWeight
    {n q r : ℕ} (hrq : r ≤ q)
    {G : Finset (Finset (Fin n))}
    (huniform : ∀ e ∈ G, e.card = r)
    (hnonempty : ∀ e ∈ G, (decoderAmbients n q r G e).Nonempty)
    {e' : Finset (Fin n)} (he' : e' ∈ G) :
    weightedDegree n q (correctionWeight n q r G) e' =
      degreeDefect n q r G e' := by
  classical
  rw [weightedDegree]
  simp only [correctionWeight]
  rw [show (∑ Q ∈ Typicality.uniformEdges n q,
      if e' ⊆ Q then
        ∑ e ∈ G, ∑ Z ∈ decoderAmbients n q r G e,
          averagedDecoderTerm n q r G e Z Q
      else 0) =
      ∑ e ∈ G, ∑ Z ∈ decoderAmbients n q r G e,
        ∑ Q ∈ Typicality.uniformEdges n q,
          if e' ⊆ Q then averagedDecoderTerm n q r G e Z Q else 0 by
    calc
      _ = ∑ Q ∈ Typicality.uniformEdges n q,
          ∑ e ∈ G, ∑ Z ∈ decoderAmbients n q r G e,
            if e' ⊆ Q then averagedDecoderTerm n q r G e Z Q else 0 := by
        apply Finset.sum_congr rfl
        intro Q hQ
        by_cases he'Q : e' ⊆ Q <;> simp [he'Q]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro e he
        rw [Finset.sum_comm]]
  calc
    (∑ e ∈ G, ∑ Z ∈ decoderAmbients n q r G e,
        ∑ Q ∈ Typicality.uniformEdges n q,
          if e' ⊆ Q then averagedDecoderTerm n q r G e Z Q else 0) =
        ∑ e ∈ G, ∑ _Z ∈ decoderAmbients n q r G e,
          degreeDefect n q r G e /
              (decoderAmbients n q r G e).card *
            (if e = e' then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro Z hZ
      exact sum_averagedDecoderTerm hrq (huniform e he)
        (huniform e' he') hZ
    _ = degreeDefect n q r G e' := by
      have hcard : 0 < (decoderAmbients n q r G e').card :=
        Finset.card_pos.mpr (hnonempty e' he')
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_eq_single e']
      · simp only [Finset.sum_const, nsmul_eq_mul, if_true]
        field_simp
      · intro e he hne
        simp [hne]
      · exact fun hnot ↦ (hnot he').elim

/-- Consequently the corrected normalized degree is exactly `1/2` on
every host edge. -/
theorem weightedDegree_correctedWeight
    {n q r : ℕ} (hrq : r ≤ q)
    {G : Finset (Finset (Fin n))}
    (huniform : ∀ e ∈ G, e.card = r)
    (hnonempty : ∀ e ∈ G, (decoderAmbients n q r G e).Nonempty)
    {e : Finset (Fin n)} (he : e ∈ G) :
    weightedDegree n q (correctedWeight n q r G) e = 1 / 2 := by
  change weightedDegree n q
      (fun Q ↦ baseWeight n q r G Q + correctionWeight n q r G Q) e = 1 / 2
  rw [weightedDegree_add]
  rw [weightedDegree_correctionWeight hrq huniform hnonempty he]
  simp [degreeDefect]

/-- Uniform absolute-value bound for a normalized local decoder. -/
def decoderBound (q r : ℕ) : ℝ :=
  (((2 * q) ^ r * Nat.factorial r : ℕ) : ℝ) / q.descFactorial r

/-- Total reciprocal ambient multiplicity through a fixed clique.  This is
the quantity in which all correction terms affecting that clique are
collected. -/
def correctionMass (n q r : ℕ) (G : Finset (Finset (Fin n)))
    (Q : Finset (Fin n)) : ℝ :=
  ∑ e ∈ G, ∑ Z ∈ decoderAmbients n q r G e,
    if Q ∈ Z.powersetCard q then
      (1 : ℝ) / (decoderAmbients n q r G e).card
    else 0

theorem correctionMass_eq_sum_pairs
    (n q r : ℕ) (G : Finset (Finset (Fin n)))
    (Q : Finset (Fin n)) :
    correctionMass n q r G Q =
      ∑ p ∈ correctionPairs n q r G Q,
        (1 : ℝ) / (decoderAmbients n q r G p.1).card := by
  classical
  rw [correctionMass]
  calc
    (∑ e ∈ G, ∑ Z ∈ decoderAmbients n q r G e,
        if Q ∈ Z.powersetCard q then
          (1 : ℝ) / (decoderAmbients n q r G e).card else 0) =
        ∑ e ∈ G, ∑ Z ∈ Typicality.uniformEdges n (q + r),
          if Z ∈ decoderAmbients n q r G e ∧ Q ∈ Z.powersetCard q then
            (1 : ℝ) / (decoderAmbients n q r G e).card else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      symm
      calc
        (∑ Z ∈ Typicality.uniformEdges n (q + r),
            if Z ∈ decoderAmbients n q r G e ∧
                Q ∈ Z.powersetCard q then
              (1 : ℝ) / (decoderAmbients n q r G e).card else 0) =
            ∑ Z ∈ decoderAmbients n q r G e,
              if Z ∈ decoderAmbients n q r G e ∧
                  Q ∈ Z.powersetCard q then
                (1 : ℝ) / (decoderAmbients n q r G e).card else 0 := by
          symm
          apply Finset.sum_subset
          · intro Z hZ
            exact Typicality.mem_uniformEdges.mpr
              (mem_decoderAmbients.mp hZ).1
          · intro Z hZ hZnot
            simp [hZnot]
        _ = ∑ Z ∈ decoderAmbients n q r G e,
              if Q ∈ Z.powersetCard q then
                (1 : ℝ) / (decoderAmbients n q r G e).card else 0 := by
          apply Finset.sum_congr rfl
          intro Z hZ
          simp [hZ]
    _ = ∑ p ∈ G ×ˢ Typicality.uniformEdges n (q + r),
          if p.2 ∈ decoderAmbients n q r G p.1 ∧
              Q ∈ p.2.powersetCard q then
            (1 : ℝ) / (decoderAmbients n q r G p.1).card else 0 := by
      rw [Finset.sum_product]
    _ = ∑ p ∈ correctionPairs n q r G Q,
          (1 : ℝ) / (decoderAmbients n q r G p.1).card := by
      rw [correctionPairs, ← Finset.sum_filter]

/-- Once every decoder root has at least `A` available ambients, the total
correction mass through a `q`-clique is at most the explicit pair count
divided by `A`. -/
theorem correctionMass_le_of_ambient_lower
    {n q r A : ℕ} {G : Finset (Finset (Fin n))}
    (huniform : ∀ e ∈ G, e.card = r)
    (hA : 0 < A)
    (hambient : ∀ e ∈ G, A ≤ (decoderAmbients n q r G e).card)
    {Q : Finset (Fin n)} (hQcard : Q.card = q) :
    correctionMass n q r G Q ≤
      ((n ^ r * 2 ^ (q + r) : ℕ) : ℝ) / A := by
  rw [correctionMass_eq_sum_pairs]
  calc
    (∑ p ∈ correctionPairs n q r G Q,
        (1 : ℝ) / (decoderAmbients n q r G p.1).card) ≤
        ∑ _p ∈ correctionPairs n q r G Q, (1 : ℝ) / A := by
      apply Finset.sum_le_sum
      intro p hp
      have hpG : p.1 ∈ G :=
        (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
      exact one_div_le_one_div_of_le (by exact_mod_cast hA)
        (by exact_mod_cast hambient p.1 hpG)
    _ = ((correctionPairs n q r G Q).card : ℝ) / A := by
      simp [div_eq_mul_inv]
    _ ≤ ((n ^ r * 2 ^ (q + r) : ℕ) : ℝ) / A := by
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast card_correctionPairs_le huniform hQcard)
        (by positivity)

/-- Absolute correction bound after collecting the decoder terms by their
root and ambient. -/
theorem abs_correctionWeight_le
    {n q r : ℕ} (hq : 0 < q) (hrq : r ≤ q)
    {G : Finset (Finset (Fin n))} {defect : ℝ}
    (huniform : ∀ e ∈ G, e.card = r)
    (hdefect : ∀ e ∈ G, |degreeDefect n q r G e| ≤ defect)
    {Q : Finset (Fin n)} :
    |correctionWeight n q r G Q| ≤
      defect * decoderBound q r * correctionMass n q r G Q := by
  classical
  rw [correctionWeight]
  calc
    |∑ e ∈ G, ∑ Z ∈ decoderAmbients n q r G e,
        averagedDecoderTerm n q r G e Z Q| ≤
        ∑ e ∈ G, |∑ Z ∈ decoderAmbients n q r G e,
          averagedDecoderTerm n q r G e Z Q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ G, ∑ Z ∈ decoderAmbients n q r G e,
          |averagedDecoderTerm n q r G e Z Q| := by
      apply Finset.sum_le_sum
      intro e he
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ G, ∑ Z ∈ decoderAmbients n q r G e,
        if Q ∈ Z.powersetCard q then
          defect * decoderBound q r /
            (decoderAmbients n q r G e).card
        else 0 := by
      apply Finset.sum_le_sum
      intro e he
      apply Finset.sum_le_sum
      intro Z hZ
      by_cases hQZ : Q ∈ Z.powersetCard q
      · rw [if_pos hQZ]
        have hden : (0 : ℝ) ≤ (decoderAmbients n q r G e).card := by positivity
        have hdecoder := LocalDecoder.abs_decoderWeight_le
          (Z := Z) (Q := Q) hq hrq (huniform e he)
        rw [averagedDecoderTerm, if_pos hQZ, abs_mul, abs_div,
          abs_of_nonneg hden]
        have hdefectNonneg : 0 ≤ defect :=
          (abs_nonneg (degreeDefect n q r G e)).trans (hdefect e he)
        calc
          |degreeDefect n q r G e| /
                (decoderAmbients n q r G e).card *
              |LocalDecoder.decoderWeight q r Z e Q| ≤
              defect /
                (decoderAmbients n q r G e).card * decoderBound q r := by
            exact mul_le_mul
              (div_le_div_of_nonneg_right (hdefect e he) hden)
              hdecoder (abs_nonneg _) (by positivity)
          _ = defect * decoderBound q r /
                (decoderAmbients n q r G e).card := by ring
      · simp [averagedDecoderTerm, hQZ]
    _ = defect * decoderBound q r * correctionMass n q r G Q := by
      rw [correctionMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Z hZ
      by_cases hQZ : Q ∈ Z.powersetCard q <;>
        simp [hQZ, div_eq_mul_inv]

/-- Once the absolute correction is at most half of the base weight, all
scaled corrected weights lie in `[0,1]`. -/
theorem correctedWeight_probability_bounds
    {n q r : ℕ} (hscale : 0 < extensionScale n q r)
    {G : Finset (Finset (Fin n))} {error : ℝ}
    (hcorr : ∀ Q ∈ cliqueFamily n q r G,
      |correctionWeight n q r G Q| ≤ error)
    (hsmall : (extensionScale n q r : ℝ) * error ≤ 1 / 2) :
    ∀ Q ∈ cliqueFamily n q r G,
      (0 : ℝ) ≤ extensionScale n q r * correctedWeight n q r G Q ∧
        extensionScale n q r * correctedWeight n q r G Q ≤ 1 := by
  intro Q hQ
  have hscaleR : (0 : ℝ) < extensionScale n q r := by exact_mod_cast hscale
  have hbase :
      (extensionScale n q r : ℝ) * baseWeight n q r G Q = 1 / 2 := by
    rw [baseWeight, if_pos hQ]
    push_cast
    field_simp
  have habs := hcorr Q hQ
  have hlower : -error ≤ correctionWeight n q r G Q :=
    (neg_le_of_abs_le habs)
  have hupper : correctionWeight n q r G Q ≤ error := le_of_abs_le habs
  rw [correctedWeight, mul_add, hbase]
  constructor
  · have := mul_le_mul_of_nonneg_left hlower hscaleR.le
    nlinarith
  · have := mul_le_mul_of_nonneg_left hupper hscaleR.le
    nlinarith

/-- Decoder corrections never create weight on a clique using a forbidden
edge. -/
theorem correctedWeight_eq_zero_of_not_mem
    {n q r : ℕ} {G : Finset (Finset (Fin n))}
    {Q : Finset (Fin n)} (hQ : Q ∉ cliqueFamily n q r G) :
    correctedWeight n q r G Q = 0 := by
  classical
  rw [correctedWeight]
  have hbase : baseWeight n q r G Q = 0 := by simp [baseWeight, hQ]
  rw [hbase, zero_add, correctionWeight]
  apply Finset.sum_eq_zero
  intro e he
  apply Finset.sum_eq_zero
  intro Z hZ
  by_cases hQZ : Q ∈ Z.powersetCard q
  · apply (hQ ?_).elim
    apply mem_cliqueFamily.mpr
    refine ⟨(Finset.mem_powersetCard.mp hQZ).2, ?_⟩
    intro f hf
    exact (mem_decoderAmbients.mp hZ).2.2
      (Finset.mem_powersetCard.mpr
        ⟨(Finset.mem_powersetCard.mp hf).1.trans
            (Finset.mem_powersetCard.mp hQZ).1,
          (Finset.mem_powersetCard.mp hf).2⟩)
  · simp [averagedDecoderTerm, hQZ]

/-! ## Independent rounding of exact fractional degrees -/

/-- Available cliques incident with one host edge, as a finite coordinate
subtype of the Bernoulli experiment. -/
abbrev IncidentClique (n q r : ℕ) (G : Finset (Finset (Fin n)))
    (e : Finset (Fin n)) :=
  {Q : Finset (Fin n) // Q ∈ cliqueFamily n q r G ∧ e ⊆ Q}

def incidentCoordinate
    (n q r : ℕ) (G : Finset (Finset (Fin n))) (e : Finset (Fin n))
    (Q : IncidentClique n q r G e) :
    {Q // Q ∈ cliqueFamily n q r G} :=
  ⟨Q.1, Q.2.1⟩

/-- The actual clique family selected by a Bernoulli outcome. -/
def roundedFamily (n q r : ℕ) (G : Finset (Finset (Fin n)))
    (ω : {Q // Q ∈ cliqueFamily n q r G} → Bool) :
    Finset (Finset (Fin n)) :=
  (cliqueFamily n q r G).filter fun Q ↦
    if hQ : Q ∈ cliqueFamily n q r G then ω ⟨Q, hQ⟩ = true else False

theorem roundedFamily_subset
    (n q r : ℕ) (G : Finset (Finset (Fin n)))
    (ω : {Q // Q ∈ cliqueFamily n q r G} → Bool) :
    roundedFamily n q r G ω ⊆ cliqueFamily n q r G :=
  Finset.filter_subset _ _

private lemma incident_coordinate_injective
    (n q r : ℕ) (G : Finset (Finset (Fin n))) (e : Finset (Fin n)) :
    Function.Injective
      (fun Q : IncidentClique n q r G e ↦
        incidentCoordinate n q r G e Q) := by
  intro Q Q' h
  apply Subtype.ext
  exact congrArg
    (fun x : {Q // Q ∈ cliqueFamily n q r G} ↦
      (x : Finset (Fin n))) h

private lemma rounded_indicator_iIndep
    (n q r : ℕ) (G : Finset (Finset (Fin n))) (e : Finset (Fin n))
    (p : {Q // Q ∈ cliqueFamily n q r G} → Set.Icc (0 : ℝ) 1) :
    ProbabilityTheory.iIndepFun
      (fun Q : IncidentClique n q r G e ↦
        Probability.coordinateIndicator
          (incidentCoordinate n q r G e Q))
      (Probability.varyingBernoulliProductMeasure p) := by
  exact ProbabilityTheory.iIndepFun.precomp
    (incident_coordinate_injective n q r G e)
    (Probability.coordinateIndicator_iIndep_varying p)

/-- The selected incidence count is the corresponding finite Bernoulli
sum. -/
theorem card_filter_roundedFamily
    (n q r : ℕ) (G : Finset (Finset (Fin n)))
    (e : Finset (Fin n))
    (ω : {Q // Q ∈ cliqueFamily n q r G} → Bool) :
    (((roundedFamily n q r G ω).filter fun Q ↦ e ⊆ Q).card : ℝ) =
      Probability.finiteRandomSum
        (fun Q : IncidentClique n q r G e ↦
          Probability.coordinateIndicator
            (incidentCoordinate n q r G e Q)) ω := by
  classical
  let f : Finset (Fin n) → ℝ := fun Q ↦
    if hQ : Q ∈ cliqueFamily n q r G then
      if e ⊆ Q then Probability.coordinateIndicator ⟨Q, hQ⟩ ω else 0
    else 0
  have hsum :
      Probability.finiteRandomSum
        (fun Q : IncidentClique n q r G e ↦
          Probability.coordinateIndicator
            (incidentCoordinate n q r G e Q)) ω =
        ∑ Q ∈ (cliqueFamily n q r G).filter (e ⊆ ·), f Q := by
    rw [Probability.finiteRandomSum]
    calc
      (∑ Q : IncidentClique n q r G e,
          Probability.coordinateIndicator
            (incidentCoordinate n q r G e Q) ω) =
          ∑ Q : IncidentClique n q r G e, f Q.1 := by
        apply Finset.sum_congr rfl
        intro Q hQ
        rw [show f Q.1 =
            Probability.coordinateIndicator ⟨Q.1, Q.2.1⟩ ω by
          rw [show f Q.1 = if hQ' : Q.1 ∈ cliqueFamily n q r G then
              if e ⊆ Q.1 then
                Probability.coordinateIndicator ⟨Q.1, hQ'⟩ ω else 0
            else 0 by rfl,
            dif_pos Q.2.1, if_pos Q.2.2]]
        rfl
      _ = ∑ Q ∈ (cliqueFamily n q r G).filter (e ⊆ ·), f Q :=
        (Finset.sum_subtype
          ((cliqueFamily n q r G).filter (e ⊆ ·))
          (fun Q ↦ by simp) f).symm
  rw [hsum]
  have hfilter :
      (roundedFamily n q r G ω).filter (e ⊆ ·) =
        ((cliqueFamily n q r G).filter (e ⊆ ·)).filter fun Q ↦
          if hQ : Q ∈ cliqueFamily n q r G then ω ⟨Q, hQ⟩ = true
          else False := by
    ext Q
    simp only [roundedFamily, Finset.mem_filter]
    aesop
  rw [hfilter, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro Q hQ
  have hQclique : Q ∈ cliqueFamily n q r G :=
    (Finset.mem_filter.mp hQ).1
  have heQ : e ⊆ Q := (Finset.mem_filter.mp hQ).2
  rw [show f Q = Probability.coordinateIndicator ⟨Q, hQclique⟩ ω by
    rw [show f Q = if hQ' : Q ∈ cliqueFamily n q r G then
        if e ⊆ Q then Probability.coordinateIndicator ⟨Q, hQ'⟩ ω else 0
      else 0 by rfl,
      dif_pos hQclique, if_pos heQ]]
  cases hωQ : ω ⟨Q, hQclique⟩ <;>
    simp only [Probability.coordinateIndicator, hωQ, if_false, if_true,
      dif_pos hQclique, heQ, and_self, Bool.false_eq_true,
      Nat.cast_zero, Nat.cast_one]

/-- Failure of the requested additive degree error at one host edge. -/
def roundingBad (n q r : ℕ) (G : Finset (Finset (Fin n)))
    (p : {Q // Q ∈ cliqueFamily n q r G} → Set.Icc (0 : ℝ) 1)
    (e : Finset (Fin n)) (error : ℝ) :
    Set ({Q // Q ∈ cliqueFamily n q r G} → Bool) :=
  let X := fun Q : IncidentClique n q r G e ↦
    Probability.coordinateIndicator
      (incidentCoordinate n q r G e Q)
  {ω | error ≤ ∑ Q, (X Q ω - p (incidentCoordinate n q r G e Q))} ∪
    {ω | ∑ Q, (X Q ω - p (incidentCoordinate n q r G e Q)) ≤ -error}

/-- Hoeffding bound for the two-sided rounding error at one edge. -/
theorem measureReal_roundingBad_le
    (n q r : ℕ) (G : Finset (Finset (Fin n)))
    (p : {Q // Q ∈ cliqueFamily n q r G} → Set.Icc (0 : ℝ) 1)
    (e : Finset (Fin n)) {error : ℝ} (herror : 0 ≤ error) :
    (Probability.varyingBernoulliProductMeasure p).real
        (roundingBad n q r G p e error) ≤
      2 * Real.exp
        (-error ^ 2 /
          (2 * ∑ _Q : IncidentClique n q r G e,
            (Probability.hoeffdingUnitVariance : ℝ))) := by
  let X := fun Q : IncidentClique n q r G e ↦
    Probability.coordinateIndicator
      (incidentCoordinate n q r G e Q)
  have hmeas : ∀ Q, Measurable (X Q) := fun Q ↦
    Probability.coordinateIndicator_measurable _
  have hindep : ProbabilityTheory.iIndepFun X
      (Probability.varyingBernoulliProductMeasure p) :=
    rounded_indicator_iIndep n q r G e p
  have hbound : ∀ Q, ∀ᵐ ω ∂Probability.varyingBernoulliProductMeasure p,
      X Q ω ∈ Set.Icc (0 : ℝ) 1 := fun Q ↦
    Probability.coordinateIndicator_mem_Icc_varying p _
  have hmean (Q : IncidentClique n q r G e) :
      ∫ ω, X Q ω ∂Probability.varyingBernoulliProductMeasure p =
        p (incidentCoordinate n q r G e Q) := by
    exact Probability.integral_coordinateIndicator_varying p _
  apply (MeasureTheory.measureReal_union_le _ _).trans
  have hu := Probability.measure_centered_sum_ge_le X hmeas hindep hbound herror
  have hl := Probability.measure_centered_sum_le_neg_le X hmeas hindep hbound herror
  simp_rw [hmean] at hu hl
  exact calc
    _ ≤ Real.exp
          (-error ^ 2 /
            (2 * ∑ _Q : IncidentClique n q r G e,
              (Probability.hoeffdingUnitVariance : ℝ))) +
        Real.exp
          (-error ^ 2 /
            (2 * ∑ _Q : IncidentClique n q r G e,
              (Probability.hoeffdingUnitVariance : ℝ))) :=
      add_le_add hu hl
    _ = _ := by ring

/-- If the finite union-bound sum is below one, some Bernoulli outcome
rounds all prescribed exact means simultaneously. -/
theorem exists_roundedFamily
    (n q r : ℕ) (G : Finset (Finset (Fin n)))
    (p : {Q // Q ∈ cliqueFamily n q r G} → Set.Icc (0 : ℝ) 1)
    (target error : ℝ) (herror : 0 ≤ error)
    (hmean : ∀ e ∈ G, ∑ Q : IncidentClique n q r G e,
      (p (incidentCoordinate n q r G e Q) : ℝ) = target)
    (htail :
      ∑ e ∈ G, 2 * Real.exp
        (-error ^ 2 /
          (2 * ∑ _Q : IncidentClique n q r G e,
            (Probability.hoeffdingUnitVariance : ℝ))) < 1) :
    ∃ H : Finset (Finset (Fin n)), H ⊆ cliqueFamily n q r G ∧
      ∀ e ∈ G,
        |((H.filter fun Q ↦ e ⊆ Q).card : ℝ) - target| < error := by
  let P := Probability.varyingBernoulliProductMeasure p
  let bad : Set ({Q // Q ∈ cliqueFamily n q r G} → Bool) :=
    ⋃ e : {e // e ∈ G}, roundingBad n q r G p e.1 error
  have hbad : P.real bad < 1 := by
    calc
      P.real bad ≤ ∑ e : {e // e ∈ G},
          P.real (roundingBad n q r G p e.1 error) := by
        exact MeasureTheory.measureReal_iUnion_fintype_le _
      _ ≤ ∑ e : {e // e ∈ G},
          2 * Real.exp
            (-error ^ 2 /
              (2 * ∑ _Q : IncidentClique n q r G e.1,
                (Probability.hoeffdingUnitVariance : ℝ))) := by
        apply Finset.sum_le_sum
        intro e he
        exact measureReal_roundingBad_le n q r G p e.1 herror
      _ = ∑ e ∈ G, 2 * Real.exp
            (-error ^ 2 /
              (2 * ∑ _Q : IncidentClique n q r G e,
                (Probability.hoeffdingUnitVariance : ℝ))) := by
        exact (Finset.sum_subtype G (fun _ ↦ Iff.rfl)
          (fun e ↦ 2 * Real.exp
            (-error ^ 2 /
              (2 * ∑ _Q : IncidentClique n q r G e,
                (Probability.hoeffdingUnitVariance : ℝ))))).symm
      _ < 1 := htail
  have hproper : bad ≠ Set.univ := by
    intro hbaduniv
    have : P.real bad = 1 := by simp [hbaduniv, P]
    linarith
  obtain ⟨ω, hω⟩ : ∃ ω, ω ∉ bad := by
    by_contra hall
    apply hproper
    rw [Set.eq_univ_iff_forall]
    intro ω
    by_contra hnot
    exact hall ⟨ω, hnot⟩
  refine ⟨roundedFamily n q r G ω, roundedFamily_subset n q r G ω, ?_⟩
  intro e he
  have hnotBad : ω ∉ roundingBad n q r G p e error := by
    intro hmem
    apply hω
    simp only [bad, Set.mem_iUnion]
    exact ⟨⟨e, he⟩, hmem⟩
  let X := fun Q : IncidentClique n q r G e ↦
    Probability.coordinateIndicator
      (incidentCoordinate n q r G e Q)
  rw [roundingBad, Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq,
    not_or] at hnotBad
  have hcenter :
      ∑ Q : IncidentClique n q r G e,
          (X Q ω - p (incidentCoordinate n q r G e Q)) =
        (((roundedFamily n q r G ω).filter fun Q ↦ e ⊆ Q).card : ℝ) -
          target := by
    rw [Finset.sum_sub_distrib, hmean e he]
    have hc := card_filter_roundedFamily n q r G e ω
    rw [Probability.finiteRandomSum] at hc
    exact congrArg (fun x : ℝ ↦ x - target) (by simpa [X] using hc.symm)
  rw [hcenter] at hnotBad
  rw [abs_lt]
  constructor <;> linarith

/-! ## Specialization to the corrected local-decoder weight -/

/-- Summing a weight supported on available cliques over the incident
subtype is the same as the ambient weighted-degree sum. -/
theorem sum_incident_eq_weightedDegree
    (n q r : ℕ) (G : Finset (Finset (Fin n)))
    (w : Finset (Fin n) → ℝ)
    (hsupport : ∀ Q, Q ∉ cliqueFamily n q r G → w Q = 0)
    (e : Finset (Fin n)) :
    (∑ Q : IncidentClique n q r G e, w Q.1) = weightedDegree n q w e := by
  classical
  rw [weightedDegree, ← Finset.sum_filter]
  let f : Finset (Fin n) → ℝ := fun Q ↦ if e ⊆ Q then w Q else 0
  have hleft : (∑ Q : IncidentClique n q r G e, w Q.1) =
      ∑ Q ∈ (cliqueFamily n q r G).filter (e ⊆ ·), f Q := by
    calc
      _ = ∑ Q : IncidentClique n q r G e, f Q.1 := by
        apply Finset.sum_congr rfl
        intro Q hQ
        simp [f, Q.2.2]
      _ = _ := (Finset.sum_subtype
        ((cliqueFamily n q r G).filter (e ⊆ ·))
        (fun Q ↦ by simp) f).symm
  rw [hleft]
  have hrhs :
      (∑ Q ∈ (Typicality.uniformEdges n q).filter (e ⊆ ·), w Q) =
        ∑ Q ∈ (Typicality.uniformEdges n q).filter (e ⊆ ·), f Q := by
    apply Finset.sum_congr rfl
    intro Q hQ
    simp [f, (Finset.mem_filter.mp hQ).2]
  rw [hrhs]
  apply Finset.sum_subset
  · intro Q hQ
    have hQdata := Finset.mem_filter.mp hQ
    apply Finset.mem_filter.mpr
    exact ⟨Typicality.mem_uniformEdges.mpr (mem_cliqueFamily.mp hQdata.1).1,
      hQdata.2⟩
  · intro Q hQuniform hQnot
    have hQnotClique : Q ∉ cliqueFamily n q r G := by
      intro hQclique
      exact hQnot (Finset.mem_filter.mpr ⟨hQclique,
        (Finset.mem_filter.mp hQuniform).2⟩)
    simp [f, hsupport Q hQnotClique]

/-- Turn a pointwise `[0,1]` proof for the scaled corrected weights into
the heterogeneous Bernoulli parameter vector. -/
def correctedProbability
    (n q r : ℕ) (G : Finset (Finset (Fin n)))
    (hprob : ∀ Q ∈ cliqueFamily n q r G,
      (0 : ℝ) ≤ extensionScale n q r * correctedWeight n q r G Q ∧
        extensionScale n q r * correctedWeight n q r G Q ≤ 1) :
    {Q // Q ∈ cliqueFamily n q r G} → Set.Icc (0 : ℝ) 1 :=
  fun Q ↦ ⟨extensionScale n q r * correctedWeight n q r G Q,
    hprob Q.1 Q.2⟩

/-- Every incident Bernoulli sum produced by the corrected weight has the
exact target mean `choose(n,q-r)/2`. -/
theorem sum_correctedProbability
    {n q r : ℕ} (hrq : r ≤ q)
    {G : Finset (Finset (Fin n))}
    (huniform : ∀ e ∈ G, e.card = r)
    (hnonempty : ∀ e ∈ G, (decoderAmbients n q r G e).Nonempty)
    (hprob : ∀ Q ∈ cliqueFamily n q r G,
      (0 : ℝ) ≤ extensionScale n q r * correctedWeight n q r G Q ∧
        extensionScale n q r * correctedWeight n q r G Q ≤ 1)
    {e : Finset (Fin n)} (he : e ∈ G) :
    (∑ Q : IncidentClique n q r G e,
        ((correctedProbability n q r G hprob
          (incidentCoordinate n q r G e Q) : Set.Icc (0 : ℝ) 1) : ℝ)) =
      (extensionScale n q r : ℝ) / 2 := by
  change (∑ Q : IncidentClique n q r G e,
      (extensionScale n q r : ℝ) * correctedWeight n q r G Q.1) = _
  rw [← Finset.mul_sum]
  rw [sum_incident_eq_weightedDegree n q r G
    (correctedWeight n q r G)
    (fun Q hQ ↦ correctedWeight_eq_zero_of_not_mem hQ) e]
  rw [weightedDegree_correctedWeight hrq huniform hnonempty he]
  ring

/-- The exact corrected fractional vector plus the finite union-bound
inequality yields an actual regular clique family. -/
theorem exists_rounded_corrected
    {n q r : ℕ} (hrq : r ≤ q)
    {G : Finset (Finset (Fin n))}
    (huniform : ∀ e ∈ G, e.card = r)
    (hnonempty : ∀ e ∈ G, (decoderAmbients n q r G e).Nonempty)
    (hprob : ∀ Q ∈ cliqueFamily n q r G,
      (0 : ℝ) ≤ extensionScale n q r * correctedWeight n q r G Q ∧
        extensionScale n q r * correctedWeight n q r G Q ≤ 1)
    (error : ℝ) (herror : 0 ≤ error)
    (htail :
      ∑ e ∈ G, 2 * Real.exp
        (-error ^ 2 /
          (2 * ∑ _Q : IncidentClique n q r G e,
            (Probability.hoeffdingUnitVariance : ℝ))) < 1) :
    ∃ H : Finset (Finset (Fin n)), H ⊆ cliqueFamily n q r G ∧
      ∀ e ∈ G,
        |((H.filter fun Q ↦ e ⊆ Q).card : ℝ) -
            (extensionScale n q r : ℝ) / 2| < error := by
  apply exists_roundedFamily n q r G
    (correctedProbability n q r G hprob)
    ((extensionScale n q r : ℝ) / 2) error herror
  · intro e he
    exact sum_correctedProbability hrq huniform hnonempty hprob he
  · exact htail

/-! ## A finite quantitative boost interface -/

/-- The number of available cliques through an edge is at most the exact
complete-host extension count.  This is the denominator used in all later
tail estimates. -/
theorem fintypeCard_incidentClique_le
    {n q r : ℕ} (hrq : r ≤ q) {G : Finset (Finset (Fin n))}
    {e : Finset (Fin n)} (hecard : e.card = r) :
    Fintype.card (IncidentClique n q r G e) ≤ extensionScale n q r := by
  classical
  rw [← card_incident_uniformEdges hrq hecard]
  let equivFilter : IncidentClique n q r G e ≃
      ↑((cliqueFamily n q r G).filter (e ⊆ ·)) :=
    { toFun := fun Q ↦ ⟨Q.1, Finset.mem_filter.mpr ⟨Q.2.1, Q.2.2⟩⟩
      invFun := fun Q ↦
        ⟨Q.1, (Finset.mem_filter.mp Q.2).1, (Finset.mem_filter.mp Q.2).2⟩
      left_inv := by
        intro Q
        apply Subtype.ext
        rfl
      right_inv := by
        intro Q
        apply Subtype.ext
        rfl }
  rw [Fintype.card_congr equivFilter, Fintype.card_coe]
  apply Finset.card_le_card
  intro Q hQ
  have hm := Finset.mem_filter.mp hQ
  exact Finset.mem_filter.mpr
    ⟨Typicality.mem_uniformEdges.mpr (mem_cliqueFamily.mp hm.1).1, hm.2⟩

/-- All analytic and enumerative estimates in the boost enter through four
explicit finite inequalities.  Under those inequalities, the checked local
decoder and Bernoulli rounding produce the desired regular clique family.
This theorem contains no asymptotic or probabilistic black box. -/
theorem exists_boost_of_finite_bounds
    {n q r : ℕ} (hq : 0 < q) (hrq : r ≤ q)
    {G : Finset (Finset (Fin n))}
    (huniform : ∀ e ∈ G, e.card = r)
    (hscale : 0 < extensionScale n q r)
    (hnonempty : ∀ e ∈ G, (decoderAmbients n q r G e).Nonempty)
    (defect mass error : ℝ)
    (hdefect0 : 0 ≤ defect)
    (hdefect : ∀ e ∈ G, |degreeDefect n q r G e| ≤ defect)
    (hmass : ∀ Q ∈ cliqueFamily n q r G,
      correctionMass n q r G Q ≤ mass)
    (hquant : (extensionScale n q r : ℝ) *
      (defect * decoderBound q r * mass) ≤ 1 / 2)
    (herror : 0 ≤ error)
    (htail :
      ∑ e ∈ G, 2 * Real.exp
        (-error ^ 2 /
          (2 * ∑ _Q : IncidentClique n q r G e,
            (Probability.hoeffdingUnitVariance : ℝ))) < 1) :
    ∃ H : Finset (Finset (Fin n)), H ⊆ cliqueFamily n q r G ∧
      ∀ e ∈ G,
        |((H.filter fun Q ↦ e ⊆ Q).card : ℝ) -
            (extensionScale n q r : ℝ) / 2| < error := by
  have hcorr : ∀ Q ∈ cliqueFamily n q r G,
      |correctionWeight n q r G Q| ≤
        defect * decoderBound q r * mass := by
    intro Q hQ
    have hdecoder0 : 0 ≤ decoderBound q r := by
      unfold decoderBound
      exact div_nonneg (by positivity) (by positivity)
    exact (abs_correctionWeight_le hq hrq huniform hdefect).trans
      (mul_le_mul_of_nonneg_left (hmass Q hQ) (by
        exact mul_nonneg hdefect0 hdecoder0))
  have hprob := correctedWeight_probability_bounds hscale hcorr hquant
  exact exists_rounded_corrected hrq huniform hnonempty hprob error herror htail

/-- Explicit upper bound for every edge defect when the omitted host has
maximum lower degree `D`. -/
def sparseDefectBound (n q r D : ℕ) : ℝ :=
  (((q - r) * n ^ (q - r - 1) * (2 ^ q * D) : ℕ) : ℝ) /
    (2 * extensionScale n q r : ℕ)

/-- Explicit upper bound for correction mass when every root has at least
`A` decoder ambients. -/
def sparseMassBound (n q r A : ℕ) : ℝ :=
  ((n ^ r * 2 ^ (q + r) : ℕ) : ℝ) / A

/-- Fully concrete finite boost theorem.  Its only remaining hypotheses are
the displayed natural/real inequalities; all clique counts, decoder
identities, support assertions, and the Bernoulli rounding are proved above.
-/
theorem exists_boost_of_sparse_finite
    {n q r D A : ℕ} (hr : 0 < r) (hqr : r < q)
    {G : Finset (Finset (Fin n))}
    (hGsub : G ⊆ Typicality.uniformEdges n r)
    (hdegree : Counting.LowerDegreeLE n r D (complementEdges n r G))
    (hscale : 0 < extensionScale n q r)
    (hA : 0 < A)
    (hambient : ∀ e ∈ G, A ≤ (decoderAmbients n q r G e).card)
    (hquant : (extensionScale n q r : ℝ) *
      (sparseDefectBound n q r D * decoderBound q r *
        sparseMassBound n q r A) ≤ 1 / 2)
    (error : ℝ) (herror : 0 ≤ error)
    (htail :
      ∑ e ∈ G, 2 * Real.exp
        (-error ^ 2 /
          (2 * ∑ _Q : IncidentClique n q r G e,
            (Probability.hoeffdingUnitVariance : ℝ))) < 1) :
    ∃ H : Finset (Finset (Fin n)), H ⊆ cliqueFamily n q r G ∧
      ∀ e ∈ G,
        |((H.filter fun Q ↦ e ⊆ Q).card : ℝ) -
            (extensionScale n q r : ℝ) / 2| < error := by
  have huniform : ∀ e ∈ G, e.card = r := by
    intro e he
    exact Typicality.mem_uniformEdges.mp (hGsub he)
  have hnonempty : ∀ e ∈ G,
      (decoderAmbients n q r G e).Nonempty := by
    intro e he
    apply Finset.card_pos.mp
    exact hA.trans_le (hambient e he)
  apply exists_boost_of_finite_bounds (by omega) hqr.le huniform hscale
    hnonempty (sparseDefectBound n q r D) (sparseMassBound n q r A)
    error (by unfold sparseDefectBound; positivity)
  · intro e he
    exact abs_degreeDefect_le_sparse hr hqr hdegree he (huniform e he) hscale
  · intro Q hQ
    exact correctionMass_le_of_ambient_lower huniform hA hambient
      (mem_cliqueFamily.mp hQ).1
  · exact hquant
  · exact herror
  · exact htail

end

end Erdos722.Boost
