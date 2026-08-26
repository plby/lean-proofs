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
import ErdosProblems.Erdos76.InducedTransport
import ErdosProblems.Erdos76.RoundingAssembly
import ErdosProblems.Erdos76.TriangleHypergraph
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

/-!
# Averaging local fractional triangle packings

This file contains the finite double-counting step in the proof of Erdős
Problem 76.  A fractional packing on every `m`-vertex induced colouring is
averaged over the `m`-subsets of an `n`-vertex colouring.  The normalization
is the number `choose (n - 2) (m - 2)` of `m`-sets through a fixed graph edge.

The two binomial quotients which occur in the argument are proved here as
exact real identities, rather than being hidden inside an asymptotic estimate.
-/

open Filter Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The family of all `m`-element subsets of a finite type. -/
def fixedCardSubsets (m : ℕ) : Finset (Finset A) :=
  (Finset.univ : Finset A).powersetCard m

/-- The `m`-element subsets containing a prescribed finite set. -/
def fixedCardSubsetsContaining (m : ℕ) (s : Finset A) : Finset (Finset A) :=
  (fixedCardSubsets m).filter (s ⊆ ·)

@[simp] lemma mem_fixedCardSubsets {m : ℕ} {s : Finset A} :
    s ∈ fixedCardSubsets m ↔ s.card = m := by
  simp [fixedCardSubsets]

@[simp] lemma mem_fixedCardSubsetsContaining {m : ℕ} {s t : Finset A} :
    t ∈ fixedCardSubsetsContaining m s ↔ t.card = m ∧ s ⊆ t := by
  simp [fixedCardSubsetsContaining, and_comm]

@[simp] lemma card_fixedCardSubsets (m : ℕ) :
    (fixedCardSubsets (A := A) m).card = (Fintype.card A).choose m := by
  simp [fixedCardSubsets, card_powersetCard]

/-- Exact count of the `m`-subsets which contain `s`. -/
lemma card_fixedCardSubsetsContaining (m : ℕ) (s : Finset A) (hsm : s.card ≤ m) :
    (fixedCardSubsetsContaining m s).card =
      (Fintype.card A - s.card).choose (m - s.card) := by
  simpa [fixedCardSubsetsContaining, fixedCardSubsets] using
    card_filter_powersetCard_subset s (Finset.univ : Finset A) m
      (subset_univ s) hsm

lemma card_fixedCardSubsetsContaining_pair {m : ℕ} {e : Finset A}
    (he : e.card = 2) (hm : 2 ≤ m) :
    (fixedCardSubsetsContaining m e).card =
      (Fintype.card A - 2).choose (m - 2) := by
  simpa [he] using card_fixedCardSubsetsContaining (A := A) m e (by omega)

lemma card_fixedCardSubsetsContaining_triple {m : ℕ} {t : Finset A}
    (ht : t.card = 3) (hm : 3 ≤ m) :
    (fixedCardSubsetsContaining m t).card =
      (Fintype.card A - 3).choose (m - 3) := by
  simpa [ht] using card_fixedCardSubsetsContaining (A := A) m t (by omega)

lemma choose_sub_two_pos {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    0 < (n - 2).choose (m - 2) := by
  exact Nat.choose_pos (Nat.sub_le_sub_right hmn 2)

lemma choose_sub_two_ne_zero {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    (n - 2).choose (m - 2) ≠ 0 :=
  (choose_sub_two_pos hm hmn).ne'

/-- Double-count pairs `(S,e)` with `|S| = m` and `e ⊆ S`, `|e| = 2`. -/
lemma choose_mul_choose_two {m n : ℕ} (hm : 2 ≤ m) :
    n.choose m * m.choose 2 = n.choose 2 * (n - 2).choose (m - 2) := by
  simpa using (Nat.choose_mul (n := n) (k := m) (s := 2) hm)

/-- Exact quotient used for the total weight after averaging. -/
lemma cast_choose_div_choose_sub_two {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    (n.choose m : ℝ) / ((n - 2).choose (m - 2) : ℝ) =
      (n : ℝ) * (n - 1 : ℕ) / ((m : ℝ) * (m - 1 : ℕ)) := by
  have hD : ((n - 2).choose (m - 2) : ℝ) ≠ 0 := by
    exact_mod_cast choose_sub_two_ne_zero hm hmn
  have hM : (m.choose 2 : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hm
  calc
    (n.choose m : ℝ) / ((n - 2).choose (m - 2) : ℝ) =
        (n.choose 2 : ℝ) / (m.choose 2 : ℝ) := by
          field_simp
          have hcast :
              (n.choose m : ℝ) * (m.choose 2 : ℝ) =
                (n.choose 2 : ℝ) * ((n - 2).choose (m - 2) : ℝ) := by
            exact_mod_cast choose_mul_choose_two (n := n) hm
          simpa [mul_comm] using hcast
    _ = (n : ℝ) * (n - 1 : ℕ) / ((m : ℝ) * (m - 1 : ℕ)) := by
      rw [Nat.cast_choose_two, Nat.cast_choose_two]
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 1 ≤ m)]
      field_simp
      <;> ring

/-- Double-count a fixed triple inside the `m`-sets through a fixed pair. -/
lemma choose_sub_two_mul_sub_two {m n : ℕ} (hm : 3 ≤ m) :
    (n - 2).choose (m - 2) * (m - 2) =
      (n - 2) * (n - 3).choose (m - 3) := by
  have h := Nat.choose_mul (n := n - 2) (k := m - 2) (s := 1) (by omega)
  simpa [Nat.choose_one_right, Nat.sub_sub] using h

/-- Exact quotient controlling every averaged triangle weight and hence every
weighted pair-codegree in the triangle hypergraph. -/
lemma cast_choose_sub_three_div_choose_sub_two {m n : ℕ}
    (hm : 3 ≤ m) (hmn : m ≤ n) :
    ((n - 3).choose (m - 3) : ℝ) / ((n - 2).choose (m - 2) : ℝ) =
      ((m - 2 : ℕ) : ℝ) / ((n - 2 : ℕ) : ℝ) := by
  have hD : ((n - 2).choose (m - 2) : ℝ) ≠ 0 := by
    exact_mod_cast choose_sub_two_ne_zero (by omega) hmn
  have hN : ((n - 2 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show n - 2 ≠ 0 by omega)
  field_simp
  have hcast :
      ((n - 2 : ℕ) : ℝ) * ((n - 3).choose (m - 3) : ℝ) =
        ((n - 2).choose (m - 2) : ℝ) * ((m - 2 : ℕ) : ℝ) := by
    exact_mod_cast (choose_sub_two_mul_sub_two (n := n) hm).symm
  simpa [mul_comm] using hcast

private lemma real_averaging_factor_lower {c x y : ℝ}
    (hc : 0 ≤ c) (hx : 1 < x) (hy : 1 ≤ y) :
    c * y * (y - 1) ≤
      y * (y - 1) / (x * (x - 1)) * (c * x ^ 2) := by
  have hxsub : 0 < x - 1 := sub_pos.mpr hx
  have hxratio : 1 ≤ x / (x - 1) :=
    (one_le_div hxsub).2 (by linarith)
  have hcy : 0 ≤ c * y * (y - 1) := by positivity
  calc
    c * y * (y - 1) = c * y * (y - 1) * 1 := by ring
    _ ≤ c * y * (y - 1) * (x / (x - 1)) :=
      mul_le_mul_of_nonneg_left hxratio hcy
    _ = y * (y - 1) / (x * (x - 1)) * (c * x ^ 2) := by
      field_simp

section GenericAveraging

variable (G : SimpleGraph A) (m : ℕ)

/-- The local weights to be averaged.  The hypotheses are stated using the
triangle hypergraph's two-element-finset vertices, so no conversion between
`Sym2` and pairs is exposed by the averaging argument.

The upper bounds by indicator functions encode both support inside `S` and
the fam fractional matching inequalities. -/
def IsLocalAveragingFamily
    (fam : Finset A → MonoTriangle G → ℝ) : Prop :=
  (∀ S ∈ fixedCardSubsets m, ∀ t, 0 ≤ fam S t) ∧
    (∀ S ∈ fixedCardSubsets m, ∀ t,
      fam S t ≤ if t.1 ⊆ S then 1 else 0) ∧
    ∀ S ∈ fixedCardSubsets m, ∀ e ∈ (monochromaticTriangleHypergraph G).vertexSet,
      (monochromaticTriangleHypergraph G).vertexLoad (fam S) e ≤
        if e ⊆ S then 1 else 0

/-- Average a fam weight family over all `m`-sets, normalized by the number
of `m`-sets containing a fixed pair. -/
def averagedMonoWeight
    (fam : Finset A → MonoTriangle G → ℝ) (t : MonoTriangle G) : ℝ :=
  (∑ S ∈ fixedCardSubsets m, fam S t) /
    ((Fintype.card A - 2).choose (m - 2) : ℝ)

lemma averagedMonoWeight_nonneg
    {fam : Finset A → MonoTriangle G → ℝ}
    (hlocal : IsLocalAveragingFamily G m fam)
    (hm : 2 ≤ m) (hmA : m ≤ Fintype.card A) (t : MonoTriangle G) :
    0 ≤ averagedMonoWeight G m fam t := by
  apply div_nonneg
  · exact sum_nonneg fun S hS ↦ hlocal.1 S hS t
  · exact_mod_cast (choose_sub_two_pos hm hmA).le

private lemma vertexLoad_averagedMonoWeight
    (fam : Finset A → MonoTriangle G → ℝ) (e : Finset A) :
    (monochromaticTriangleHypergraph G).vertexLoad
        (averagedMonoWeight G m fam) e =
      (∑ S ∈ fixedCardSubsets m,
          (monochromaticTriangleHypergraph G).vertexLoad (fam S) e) /
        ((Fintype.card A - 2).choose (m - 2) : ℝ) := by
  simp only [FiniteHypergraph.vertexLoad, averagedMonoWeight, sum_div]
  rw [sum_comm]

private lemma sum_pair_subset_indicator {e : Finset A} (he : e.card = 2) (hm : 2 ≤ m) :
    (∑ S ∈ fixedCardSubsets m, if e ⊆ S then (1 : ℝ) else 0) =
      ((Fintype.card A - 2).choose (m - 2) : ℝ) := by
  rw [← card_fixedCardSubsetsContaining_pair (A := A) he hm]
  simp [fixedCardSubsetsContaining]

lemma averagedMonoWeight_isFractionalMatching
    {fam : Finset A → MonoTriangle G → ℝ}
    (hlocal : IsLocalAveragingFamily G m fam)
    (hm : 2 ≤ m) (hmA : m ≤ Fintype.card A) :
    (monochromaticTriangleHypergraph G).IsFractionalMatching
      (averagedMonoWeight G m fam) := by
  constructor
  · exact averagedMonoWeight_nonneg G m hlocal hm hmA
  · intro e he
    rw [vertexLoad_averagedMonoWeight]
    have hD : 0 < (((Fintype.card A - 2).choose (m - 2) : ℕ) : ℝ) := by
      exact_mod_cast choose_sub_two_pos hm hmA
    apply (div_le_iff₀ hD).2
    calc
      ∑ S ∈ fixedCardSubsets m,
          (monochromaticTriangleHypergraph G).vertexLoad (fam S) e
          ≤ ∑ S ∈ fixedCardSubsets m, if e ⊆ S then (1 : ℝ) else 0 := by
            exact sum_le_sum fun S hS ↦ hlocal.2.2 S hS e he
      _ = ((Fintype.card A - 2).choose (m - 2) : ℝ) := by
        apply sum_pair_subset_indicator (A := A) (m := m)
        · exact (mem_powersetCard.mp he).2
        · exact hm
      _ = 1 * ((Fintype.card A - 2).choose (m - 2) : ℝ) := by ring

private lemma totalWeight_averagedMonoWeight
    (fam : Finset A → MonoTriangle G → ℝ) :
    (monochromaticTriangleHypergraph G).totalWeight
        (averagedMonoWeight G m fam) =
      (∑ S ∈ fixedCardSubsets m,
          (monochromaticTriangleHypergraph G).totalWeight (fam S)) /
        ((Fintype.card A - 2).choose (m - 2) : ℝ) := by
  simp only [FiniteHypergraph.totalWeight, averagedMonoWeight, sum_div]
  rw [sum_comm]

/-- Exact total-weight lower bound furnished by fam averaging. -/
lemma averagedMonoWeight_totalWeight_lower
    {fam : Finset A → MonoTriangle G → ℝ}
    {q : ℝ} (hm : 2 ≤ m) (hmA : m ≤ Fintype.card A)
    (hsize : ∀ S ∈ fixedCardSubsets m,
      q ≤ (monochromaticTriangleHypergraph G).totalWeight (fam S)) :
    ((Fintype.card A).choose m : ℝ) /
          ((Fintype.card A - 2).choose (m - 2) : ℝ) * q ≤
      (monochromaticTriangleHypergraph G).totalWeight
        (averagedMonoWeight G m fam) := by
  rw [totalWeight_averagedMonoWeight]
  rw [div_mul_eq_mul_div]
  have hD : 0 ≤ (((Fintype.card A - 2).choose (m - 2) : ℕ) : ℝ) := by positivity
  apply div_le_div_of_nonneg_right _ hD
  calc
    ((Fintype.card A).choose m : ℝ) * q =
        ∑ _S ∈ fixedCardSubsets (A := A) m, q := by
          rw [sum_const, nsmul_eq_mul, card_fixedCardSubsets]
    _ ≤ ∑ S ∈ fixedCardSubsets m,
        (monochromaticTriangleHypergraph G).totalWeight (fam S) := by
          exact sum_le_sum fun S hS ↦ hsize S hS

private lemma sum_triple_subset_indicator (t : MonoTriangle G) (hm : 3 ≤ m) :
    (∑ S ∈ fixedCardSubsets m, if t.1 ⊆ S then (1 : ℝ) else 0) =
      ((Fintype.card A - 3).choose (m - 3) : ℝ) := by
  rw [← card_fixedCardSubsetsContaining_triple (A := A) (m := m)
    (t := t.1) (by rcases mem_monochromaticTriangles.mp t.2 with h | h <;> exact h.card_eq) hm]
  simp [fixedCardSubsetsContaining]

/-- Every averaged triangle has weight at most the proportion of `m`-sets
through that triangle among the `m`-sets through one of its edges. -/
lemma averagedMonoWeight_le_choose_ratio
    {fam : Finset A → MonoTriangle G → ℝ}
    (hlocal : IsLocalAveragingFamily G m fam)
    (hm : 3 ≤ m) (hmA : m ≤ Fintype.card A) (t : MonoTriangle G) :
    averagedMonoWeight G m fam t ≤
      ((Fintype.card A - 3).choose (m - 3) : ℝ) /
        ((Fintype.card A - 2).choose (m - 2) : ℝ) := by
  unfold averagedMonoWeight
  have hD : 0 ≤ (((Fintype.card A - 2).choose (m - 2) : ℕ) : ℝ) := by positivity
  apply div_le_div_of_nonneg_right _ hD
  calc
    ∑ S ∈ fixedCardSubsets m, fam S t ≤
        ∑ S ∈ fixedCardSubsets m, if t.1 ⊆ S then (1 : ℝ) else 0 := by
          exact sum_le_sum fun S hS ↦ hlocal.2.1 S hS t
    _ = ((Fintype.card A - 3).choose (m - 3) : ℝ) :=
      sum_triple_subset_indicator G m t hm

/-- Two distinct two-element subsets of a three-element set determine that
set.  This is the elementary linearity property of the triangle hypergraph. -/
lemma union_eq_of_two_pairs {e f t : Finset A}
    (hecard : e.card = 2) (hfcard : f.card = 2) (hef : e ≠ f)
    (het : e ⊆ t) (hft : f ⊆ t) (htcard : t.card = 3) :
    e ∪ f = t := by
  have hsub : e ∪ f ⊆ t := union_subset het hft
  apply eq_of_subset_of_card_le hsub
  rw [htcard]
  by_contra hcard
  have hcard' : (e ∪ f).card ≤ 2 := by omega
  have heq : e = e ∪ f :=
    eq_of_subset_of_card_le subset_union_left (by omega)
  have hfeq : f = e ∪ f :=
    eq_of_subset_of_card_le subset_union_right (by omega)
  exact hef (heq.trans hfeq.symm)

lemma two_pairs_determine_triangle {e f s t : Finset A}
    (hef : e ≠ f)
    (hes : e ∈ triangleEdgeSet s) (hfs : f ∈ triangleEdgeSet s)
    (het : e ∈ triangleEdgeSet t) (hft : f ∈ triangleEdgeSet t)
    (hscard : s.card = 3) (htcard : t.card = 3) : s = t := by
  have hes' := mem_powersetCard.mp hes
  have hfs' := mem_powersetCard.mp hfs
  have het' := mem_powersetCard.mp het
  have hft' := mem_powersetCard.mp hft
  exact (union_eq_of_two_pairs hes'.2 hfs'.2 hef hes'.1 hfs'.1 hscard).symm.trans
    (union_eq_of_two_pairs het'.2 hft'.2 hef het'.1 hft'.1 htcard)

private lemma card_triangles_through_two_pairs_le_one
    {G : SimpleGraph A} {e f : Finset A} (hef : e ≠ f) :
    ((Finset.univ : Finset (MonoTriangle G)).filter fun t ↦
      e ∈ (monochromaticTriangleHypergraph G).support t ∧
        f ∈ (monochromaticTriangleHypergraph G).support t).card ≤ 1 := by
  rw [card_le_one]
  intro s hs t ht
  simp only [mem_filter, mem_univ, true_and] at hs ht
  apply Subtype.ext
  apply two_pairs_determine_triangle hef hs.1 hs.2 ht.1 ht.2
  · rcases mem_monochromaticTriangles.mp s.2 with h | h <;> exact h.card_eq
  · rcases mem_monochromaticTriangles.mp t.2 with h | h <;> exact h.card_eq

/-- In the triangle hypergraph, a pointwise bound on nonnegative hyperedge
weights is also a bound on every distinct-vertex weighted codegree. -/
lemma monochromaticTriangleHypergraph_pairLoad_le
    {G : SimpleGraph A} {w : MonoTriangle G → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hw : ∀ t, w t ≤ r) {e f : Finset A} (hef : e ≠ f) :
    (monochromaticTriangleHypergraph G).pairLoad w e f ≤ r := by
  let U := (Finset.univ : Finset (MonoTriangle G)).filter fun t ↦
    e ∈ (monochromaticTriangleHypergraph G).support t ∧
      f ∈ (monochromaticTriangleHypergraph G).support t
  have hU : U.card ≤ 1 := card_triangles_through_two_pairs_le_one hef
  rw [FiniteHypergraph.pairLoad]
  change (∑ t ∈ U, w t) ≤ r
  rcases U.eq_empty_or_nonempty with hUempty | hUne
  · simp [hUempty, hr]
  · have hUcard : U.card = 1 := Nat.le_antisymm hU hUne.card_pos
    obtain ⟨t, hUt⟩ := card_eq_one.mp hUcard
    rw [hUt]
    simpa using hw t

/-- Pointwise bound in its simpler rational form. -/
lemma averagedMonoWeight_le_ratio
    {fam : Finset A → MonoTriangle G → ℝ}
    (hlocal : IsLocalAveragingFamily G m fam)
    (hm : 3 ≤ m) (hmA : m ≤ Fintype.card A) (t : MonoTriangle G) :
    averagedMonoWeight G m fam t ≤
      ((m - 2 : ℕ) : ℝ) / ((Fintype.card A - 2 : ℕ) : ℝ) := by
  rw [← cast_choose_sub_three_div_choose_sub_two hm hmA]
  exact averagedMonoWeight_le_choose_ratio G m hlocal hm hmA t

lemma averagedMonoWeight_pairLoad_le_ratio
    {fam : Finset A → MonoTriangle G → ℝ}
    (hlocal : IsLocalAveragingFamily G m fam)
    (hm : 3 ≤ m) (hmA : m ≤ Fintype.card A)
    {e f : Finset A} (hef : e ≠ f) :
    (monochromaticTriangleHypergraph G).pairLoad
        (averagedMonoWeight G m fam) e f ≤
      ((m - 2 : ℕ) : ℝ) / ((Fintype.card A - 2 : ℕ) : ℝ) := by
  apply monochromaticTriangleHypergraph_pairLoad_le
  · positivity
  · exact averagedMonoWeight_le_ratio G m hlocal hm hmA
  · exact hef

lemma averagedMonoWeight_pairCodegreeLT
    {fam : Finset A → MonoTriangle G → ℝ}
    (hlocal : IsLocalAveragingFamily G m fam)
    (hm : 3 ≤ m) (hmA : m ≤ Fintype.card A) {delta : ℝ}
    (hdelta : ((m - 2 : ℕ) : ℝ) /
      ((Fintype.card A - 2 : ℕ) : ℝ) < delta) :
    (monochromaticTriangleHypergraph G).PairCodegreeLT
      (averagedMonoWeight G m fam) delta := by
  intro e f hef
  exact (averagedMonoWeight_pairLoad_le_ratio G m hlocal hm hmA hef).trans_lt hdelta

end GenericAveraging

section ColourWeights

variable (G : SimpleGraph A)

/-- A feasible fractional triangle weight is at most one on every triangle. -/
lemma IsFractionalPacking.weight_le_one
    {w : Finset A → ℝ} (hw : IsFractionalPacking G w)
    {t : Finset A} (ht : G.IsNClique 3 t) : w t ≤ 1 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp ht.card_eq
  let e : Sym2 A := s(a, b)
  have he : e ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ht.isClique (by simp) (by simp) hab
  have htri : {a, b, c} ∈
      (G.cliqueFinset 3).filter (fun u ↦ e ∈ u.sym2) := by
    rw [mem_filter]
    constructor
    · exact SimpleGraph.mem_cliqueFinset_iff.mpr ht
    · simp [e]
  calc
    w {a, b, c} ≤ fractionalEdgeLoad G w e := by
      unfold fractionalEdgeLoad
      apply single_le_sum
      · intro u hu
        exact hw.nonneg_on (mem_filter.mp hu).1
      · exact htri
    _ ≤ 1 := hw.edgeLoad_le_one he

/-- Combine red and blue fractional weights into a weight on the subtype of
monochromatic triangles. -/
def monoColorWeight (wR wB : Finset A → ℝ) (t : MonoTriangle G) : ℝ :=
  if G.IsNClique 3 t.1 then wR t.1 else wB t.1

private lemma monoTriangle_blue_of_not_red (t : MonoTriangle G)
    (hred : ¬ G.IsNClique 3 t.1) : Gᶜ.IsNClique 3 t.1 := by
  rcases mem_monochromaticTriangles.mp t.2 with ht | ht
  · exact (hred ht).elim
  · exact ht

lemma monoColorWeight_nonneg {wR wB : Finset A → ℝ}
    (hwR : IsFractionalPacking G wR) (hwB : IsFractionalPacking Gᶜ wB)
    (t : MonoTriangle G) : 0 ≤ monoColorWeight G wR wB t := by
  unfold monoColorWeight
  split_ifs with hred
  · apply hwR.1
    simpa only [SimpleGraph.mem_cliqueFinset_iff]
  · apply hwB.1
    simpa only [SimpleGraph.mem_cliqueFinset_iff] using
      monoTriangle_blue_of_not_red G t hred

lemma monoColorWeight_le_one {wR wB : Finset A → ℝ}
    (hwR : IsFractionalPacking G wR) (hwB : IsFractionalPacking Gᶜ wB)
    (t : MonoTriangle G) : monoColorWeight G wR wB t ≤ 1 := by
  unfold monoColorWeight
  split_ifs with hred
  · exact hwR.weight_le_one G hred
  · exact hwB.weight_le_one Gᶜ (monoTriangle_blue_of_not_red G t hred)

private lemma not_red_of_blue {t : Finset A} (hblue : Gᶜ.IsNClique 3 t) :
    ¬ G.IsNClique 3 t := by
  intro hred
  have hle := red_blue_triangle_inter_card_le_one hred hblue
  have hcard : (t ∩ t).card = 3 := by simpa using hred.card_eq
  omega

/-- The combined subtype sum is exactly the sum of the two colour-specific
fractional sizes. -/
lemma totalWeight_monoColorWeight {wR wB : Finset A → ℝ} :
    (monochromaticTriangleHypergraph G).totalWeight (monoColorWeight G wR wB) =
      fractionalSize G wR + fractionalSize Gᶜ wB := by
  let M := monochromaticTriangles G
  let R := M.filter (G.IsNClique 3)
  let B := M.filter (fun t ↦ ¬ G.IsNClique 3 t)
  have hR : R = G.cliqueFinset 3 := by
    ext t
    simp only [R, M, mem_filter, mem_monochromaticTriangles,
      SimpleGraph.mem_cliqueFinset_iff]
    tauto
  have hB : B = Gᶜ.cliqueFinset 3 := by
    ext t
    simp only [B, M, mem_filter, mem_monochromaticTriangles,
      SimpleGraph.mem_cliqueFinset_iff]
    constructor
    · rintro ⟨hred | hblue, hnred⟩
      · exact (hnred hred).elim
      · exact hblue
    · intro hblue
      exact ⟨Or.inr hblue, not_red_of_blue G hblue⟩
  have hsR : (∑ t ∈ R, wR t) = fractionalSize G wR := by
    unfold fractionalSize
    rw [hR]
  have hsB : (∑ t ∈ B, wB t) = fractionalSize Gᶜ wB := by
    unfold fractionalSize
    rw [hB]
    apply sum_congr
    · ext t
      simp only [SimpleGraph.mem_cliqueFinset_iff]
    · intro t ht
      rfl
  unfold FiniteHypergraph.totalWeight
  calc
    ∑ t : MonoTriangle G, monoColorWeight G wR wB t =
        ∑ t ∈ M,
          if G.IsNClique 3 t then wR t else wB t := by
            symm
            simpa only [M, monoColorWeight] using
              (Finset.sum_subtype (monochromaticTriangles G)
                (fun _ ↦ Iff.rfl)
                (fun t ↦ if G.IsNClique 3 t then wR t else wB t))
    _ = (∑ t ∈ R, if G.IsNClique 3 t then wR t else wB t) +
          ∑ t ∈ B, if G.IsNClique 3 t then wR t else wB t := by
      exact (sum_filter_add_sum_filter_not M (G.IsNClique 3)
        (fun t ↦ if G.IsNClique 3 t then wR t else wB t)).symm
    _ = (∑ t ∈ R, wR t) + ∑ t ∈ B, wB t := by
      apply congrArg₂ (· + ·)
      · apply sum_congr rfl
        intro t ht
        rw [if_pos (mem_filter.mp ht).2]
      · apply sum_congr rfl
        intro t ht
        rw [if_neg (mem_filter.mp ht).2]
    _ = fractionalSize G wR + fractionalSize Gᶜ wB := by rw [hsR, hsB]

private lemma red_of_pair_mem
    {a b : A} (hab : a ≠ b) (hG : G.Adj a b) (t : MonoTriangle G)
    (ht : {a, b} ∈ (monochromaticTriangleHypergraph G).support t) :
    G.IsNClique 3 t.1 := by
  have habt : a ∈ t.1 ∧ b ∈ t.1 := by
    have hs := (mem_powersetCard.mp ht).1
    simpa only [insert_subset_iff, singleton_subset_iff] using hs
  rcases mem_monochromaticTriangles.mp t.2 with hred | hblue
  · exact hred
  · have hb := hblue.isClique habt.1 habt.2 hab
    exact (((SimpleGraph.compl_adj G a b).mp hb).2 hG).elim

private lemma blue_of_pair_mem
    {a b : A} (hab : a ≠ b) (hG : ¬ G.Adj a b) (t : MonoTriangle G)
    (ht : {a, b} ∈ (monochromaticTriangleHypergraph G).support t) :
    Gᶜ.IsNClique 3 t.1 := by
  have habt : a ∈ t.1 ∧ b ∈ t.1 := by
    have hs := (mem_powersetCard.mp ht).1
    simpa only [insert_subset_iff, singleton_subset_iff] using hs
  rcases mem_monochromaticTriangles.mp t.2 with hred | hblue
  · exact (hG (hred.isClique habt.1 habt.2 hab)).elim
  · exact hblue

private lemma vertexLoad_monoColorWeight_of_adj {wR wB : Finset A → ℝ}
    {a b : A} (hab : a ≠ b) (hG : G.Adj a b) :
    (monochromaticTriangleHypergraph G).vertexLoad
        (monoColorWeight G wR wB) {a, b} =
      fractionalEdgeLoad G wR s(a, b) := by
  letI : DecidableRel G.Adj := Classical.decRel _
  unfold FiniteHypergraph.vertexLoad fractionalEdgeLoad
  apply Finset.sum_bij (fun t _ ↦ t.1)
  · intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht
    rw [mem_filter]
    have hred := red_of_pair_mem G hab hG t ht
    refine ⟨SimpleGraph.mem_cliqueFinset_iff.mpr hred, ?_⟩
    have hs := (mem_powersetCard.mp ht).1
    exact Finset.mk_mem_sym2_iff.mpr <| by
      simpa only [insert_subset_iff, singleton_subset_iff] using hs
  · intro t₁ ht₁ t₂ ht₂ h
    exact Subtype.ext h
  · intro t ht
    rw [mem_filter] at ht
    refine ⟨⟨t, mem_monochromaticTriangles.mpr (Or.inl
      (SimpleGraph.mem_cliqueFinset_iff.mp ht.1))⟩, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    have hs : a ∈ t ∧ b ∈ t := by simpa using ht.2
    exact mem_powersetCard.mpr ⟨by
      simpa only [insert_subset_iff, singleton_subset_iff] using hs, by simp [hab]⟩
  · intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht
    rw [monoColorWeight, if_pos (red_of_pair_mem G hab hG t ht)]

private lemma vertexLoad_monoColorWeight_of_not_adj {wR wB : Finset A → ℝ}
    {a b : A} (hab : a ≠ b) (hG : ¬ G.Adj a b) :
    (monochromaticTriangleHypergraph G).vertexLoad
        (monoColorWeight G wR wB) {a, b} =
      fractionalEdgeLoad Gᶜ wB s(a, b) := by
  letI : DecidableRel Gᶜ.Adj := Classical.decRel _
  unfold FiniteHypergraph.vertexLoad fractionalEdgeLoad
  apply Finset.sum_bij (fun t _ ↦ t.1)
  · intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht
    rw [mem_filter]
    have hblue := blue_of_pair_mem G hab hG t ht
    refine ⟨SimpleGraph.mem_cliqueFinset_iff.mpr hblue, ?_⟩
    have hs := (mem_powersetCard.mp ht).1
    exact Finset.mk_mem_sym2_iff.mpr <| by
      simpa only [insert_subset_iff, singleton_subset_iff] using hs
  · intro t₁ ht₁ t₂ ht₂ h
    exact Subtype.ext h
  · intro t ht
    rw [mem_filter] at ht
    refine ⟨⟨t, mem_monochromaticTriangles.mpr (Or.inr
      (SimpleGraph.mem_cliqueFinset_iff.mp ht.1))⟩, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    have hs : a ∈ t ∧ b ∈ t := by simpa using ht.2
    exact mem_powersetCard.mpr ⟨by
      simpa only [insert_subset_iff, singleton_subset_iff] using hs, by simp [hab]⟩
  · intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht
    have hblue := blue_of_pair_mem G hab hG t ht
    rw [monoColorWeight, if_neg (not_red_of_blue G hblue)]

/-- Combining two feasible colour-specific fractional packings gives a
fractional matching of the monochromatic-triangle hypergraph. -/
lemma monoColorWeight_isFractionalMatching {wR wB : Finset A → ℝ}
    (hwR : IsFractionalPacking G wR) (hwB : IsFractionalPacking Gᶜ wB) :
    (monochromaticTriangleHypergraph G).IsFractionalMatching
      (monoColorWeight G wR wB) := by
  letI : DecidableRel G.Adj := Classical.decRel _
  letI : DecidableRel Gᶜ.Adj := Classical.decRel _
  constructor
  · exact monoColorWeight_nonneg G hwR hwB
  · intro e he
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp (mem_powersetCard.mp he).2
    by_cases hG : G.Adj a b
    · rw [vertexLoad_monoColorWeight_of_adj G hab hG]
      apply hwR.2
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact hG
    · rw [vertexLoad_monoColorWeight_of_not_adj G hab hG]
      apply hwB.2
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.compl_adj]
      exact ⟨hab, hG⟩

end ColourWeights

section GruslysLetzterAveraging

variable (G : SimpleGraph A) (m : ℕ)

/-- The Gruslys--Letzter packings on all `m`-vertex induced colourings,
extended by zero, form a local averaging family. -/
theorem exists_localAveragingFamily_of_gruslysLetzter
    (hGL : GruslysLetzterFractional) (hm : 26 ≤ m) :
    ∃ fam : Finset A → MonoTriangle G → ℝ,
      IsLocalAveragingFamily G m fam ∧
        ∀ S ∈ fixedCardSubsets m,
          ((((m - 1) ^ 2 / 4 : ℕ) : ℝ) / 3) ≤
            (monochromaticTriangleHypergraph G).totalWeight (fam S) := by
  let Valid := {S : Finset A // S ∈ fixedCardSubsets (A := A) m}
  have hex : ∀ S : Valid, ∃ wR wB : Finset A → ℝ,
      IsFractionalPacking G wR ∧ IsFractionalPacking Gᶜ wB ∧
        (∀ t, ¬t ⊆ S.1 → wR t = 0 ∧ wB t = 0) ∧
        (((((m - 1) ^ 2 / 4 : ℕ) : ℝ)) ≤
          fractionalCoveredSize G wR + fractionalCoveredSize Gᶜ wB) := by
    intro S
    have hcard : Fintype.card S.1 = m := by
      rw [Fintype.card_coe]
      exact mem_fixedCardSubsets.mp S.2
    obtain ⟨uR, uB, huR, huB, hsize⟩ :=
      GruslysLetzterFractional.on_fintype hGL hcard hm
        (G.induce (S.1 : Set A))
    obtain ⟨heR, heB, heSize⟩ := extendInduced_pair huR huB
    refine ⟨extendInducedWeight S.1 uR, extendInducedWeight S.1 uB,
      heR, heB, ?_, ?_⟩
    · intro t ht
      exact ⟨extendInducedWeight_eq_zero ht, extendInducedWeight_eq_zero ht⟩
    · exact hsize.trans_eq heSize.symm
  choose wR wB hw using hex
  let fam : Finset A → MonoTriangle G → ℝ := fun S t ↦
    if hS : S ∈ fixedCardSubsets (A := A) m then
      monoColorWeight G (wR ⟨S, hS⟩) (wB ⟨S, hS⟩) t
    else 0
  refine ⟨fam, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro S hS t
      simp only [fam, dif_pos hS]
      exact monoColorWeight_nonneg G (hw ⟨S, hS⟩).1
        (hw ⟨S, hS⟩).2.1 t
    · intro S hS t
      simp only [fam, dif_pos hS]
      by_cases ht : t.1 ⊆ S
      · rw [if_pos ht]
        exact monoColorWeight_le_one G (hw ⟨S, hS⟩).1
          (hw ⟨S, hS⟩).2.1 t
      · rw [if_neg ht]
        obtain ⟨hzR, hzB⟩ := (hw ⟨S, hS⟩).2.2.1 t.1 ht
        simp only [monoColorWeight]
        split_ifs
        · rw [hzR]
        · rw [hzB]
    · intro S hS e he
      simp only [fam, dif_pos hS]
      by_cases heS : e ⊆ S
      · rw [if_pos heS]
        exact (monoColorWeight_isFractionalMatching G
          (hw ⟨S, hS⟩).1 (hw ⟨S, hS⟩).2.1).2 e he
      · rw [if_neg heS]
        unfold FiniteHypergraph.vertexLoad
        apply le_of_eq
        apply sum_eq_zero
        intro t ht
        simp only [mem_filter, mem_univ, true_and] at ht
        have het : e ⊆ t.1 := (mem_powersetCard.mp ht).1
        have htS : ¬t.1 ⊆ S := fun h ↦ heS (het.trans h)
        obtain ⟨hzR, hzB⟩ := (hw ⟨S, hS⟩).2.2.1 t.1 htS
        simp only [monoColorWeight]
        split_ifs <;> assumption
  · intro S hS
    simp only [fam, dif_pos hS]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    calc
      ((((m - 1) ^ 2 / 4 : ℕ) : ℝ)) ≤
          fractionalCoveredSize G (wR ⟨S, hS⟩) +
            fractionalCoveredSize Gᶜ (wB ⟨S, hS⟩) :=
        (hw ⟨S, hS⟩).2.2.2
      _ = (monochromaticTriangleHypergraph G).totalWeight
          (monoColorWeight G (wR ⟨S, hS⟩) (wB ⟨S, hS⟩)) * 3 := by
        rw [totalWeight_monoColorWeight]
        simp only [fractionalCoveredSize]
        ring

/-- Exact fixed-`m` output of local subset averaging: feasibility, total
weight, and the distinct-pair codegree estimate needed by Kahn's theorem. -/
theorem exists_averagedMonoWeight_of_gruslysLetzter
    (hGL : GruslysLetzterFractional)
    (hm : 26 ≤ m) (hmA : m ≤ Fintype.card A) :
    ∃ w : MonoTriangle G → ℝ,
      (monochromaticTriangleHypergraph G).IsFractionalMatching w ∧
      ((Fintype.card A).choose m : ℝ) /
          ((Fintype.card A - 2).choose (m - 2) : ℝ) *
            ((((m - 1) ^ 2 / 4 : ℕ) : ℝ) / 3) ≤
        (monochromaticTriangleHypergraph G).totalWeight w ∧
      ∀ e f : Finset A, e ≠ f →
        (monochromaticTriangleHypergraph G).pairLoad w e f ≤
          ((m - 2 : ℕ) : ℝ) / ((Fintype.card A - 2 : ℕ) : ℝ) := by
  obtain ⟨fam, hlocal, hsize⟩ :=
    exists_localAveragingFamily_of_gruslysLetzter G m hGL hm
  refine ⟨averagedMonoWeight G m fam,
    averagedMonoWeight_isFractionalMatching G m hlocal (by omega) hmA,
    averagedMonoWeight_totalWeight_lower G m (by omega) hmA hsize, ?_⟩
  intro e f hef
  exact averagedMonoWeight_pairLoad_le_ratio G m hlocal (by omega) hmA hef

/-- The smoothed fractional conclusion furnished by local subset averaging.
This has the same fields as the problem-specific interface in
`RoundingAssembly`, but is kept here to avoid making the purely fractional
argument depend on the rounding implementation. -/
def SmoothedFractionalMonochromaticTrianglesByAveraging : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    ∀ G : SimpleGraph (Fin n),
      ∃ w : MonoTriangle G → ℝ,
        (monochromaticTriangleHypergraph G).IsFractionalMatching w ∧
        (monochromaticTriangleHypergraph G).PairCodegreeLT w δ ∧
        (1 / 12 - ε) * (n : ℝ) ^ 2 ≤
          (monochromaticTriangleHypergraph G).totalWeight w

/-- The all-orders Gruslys--Letzter fractional theorem implies the smoothed
weighted-hypergraph input required for one Kahn nibble. -/
theorem smoothedFractionalMonochromaticTrianglesByAveraging
    (hGL : GruslysLetzterFractional) :
    SmoothedFractionalMonochromaticTrianglesByAveraging := by
  intro ε hε δ hδ
  by_cases hlargeε : (1 / 12 : ℝ) ≤ ε
  · apply Filter.Eventually.of_forall
    intro n G
    let w : MonoTriangle G → ℝ := fun _ ↦ 0
    refine ⟨w, FiniteHypergraph.isFractionalMatching_zero _, ?_, ?_⟩
    · intro e f hef
      simpa only [w, FiniteHypergraph.pairLoad_zero] using hδ
    · calc
        (1 / 12 - ε) * (n : ℝ) ^ 2 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hlargeε) (sq_nonneg _)
        _ = (monochromaticTriangleHypergraph G).totalWeight w := by
          simp only [w, FiniteHypergraph.totalWeight_zero]
  · have hsmallε : ε < (1 / 12 : ℝ) := lt_of_not_ge hlargeε
    obtain ⟨m, hm26, hmq⟩ := (eventually_fractional_threshold ε hε).exists
    obtain ⟨N, hN⟩ := exists_nat_gt
      (max (1 / (6 * ε)) (2 + (m : ℝ) / δ))
    filter_upwards [eventually_ge_atTop (max m N)] with n hn
    intro G
    have hmn : m ≤ n := (le_max_left m N).trans hn
    have hNn : N ≤ n := (le_max_right m N).trans hn
    have hnreal : max (1 / (6 * ε)) (2 + (m : ℝ) / δ) < (n : ℝ) :=
      hN.trans_le (by exact_mod_cast hNn)
    have hnlinear : 1 / (6 * ε) < (n : ℝ) :=
      (le_max_left _ _).trans_lt hnreal
    have hncodeg : 2 + (m : ℝ) / δ < (n : ℝ) :=
      (le_max_right _ _).trans_lt hnreal
    obtain ⟨w, hw, hweight, hcodeg⟩ :=
      exists_averagedMonoWeight_of_gruslysLetzter G m hGL hm26 (by simpa using hmn)
    simp only [Fintype.card_fin] at hweight hcodeg
    refine ⟨w, hw, ?_, ?_⟩
    · intro e f hef
      apply (hcodeg e f hef).trans_lt
      have hn2 : 2 < n := by omega
      have hden : (0 : ℝ) < ((n - 2 : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_pos_of_lt hn2
      rw [div_lt_iff₀ hden]
      have hquot : (m : ℝ) / δ < (n : ℝ) - 2 := by linarith
      have hmprod : (m : ℝ) < ((n : ℝ) - 2) * δ :=
        (div_lt_iff₀ hδ).1 hquot
      rw [Nat.cast_sub hn2.le]
      calc
        ((m - 2 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m 2
        _ < ((n : ℝ) - 2) * δ := hmprod
        _ = δ * ((n : ℝ) - 2) := by ring
    · let q : ℝ := ((((m - 1) ^ 2 / 4 : ℕ) : ℝ) / 3)
      let c : ℝ := 1 / 12 - ε / 2
      have hc : 0 ≤ c := by dsimp only [c]; linarith
      have hm1 : 1 ≤ m := by omega
      have hn1 : 1 ≤ n := hm1.trans hmn
      have hmq' : c * (m : ℝ) ^ 2 ≤ q := by
        simpa only [c, q] using hmq
      have hratio := cast_choose_div_choose_sub_two
        (m := m) (n := n) (by omega) hmn
      have hweight' :
          (n : ℝ) * ((n - 1 : ℕ) : ℝ) /
                ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) * q ≤
            (monochromaticTriangleHypergraph G).totalWeight w := by
        rw [← hratio]
        exact hweight
      have hfactor : 0 ≤
          (n : ℝ) * ((n - 1 : ℕ) : ℝ) /
            ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) := by positivity
      have hscaled := mul_le_mul_of_nonneg_left hmq' hfactor
      have hbase : c * (n : ℝ) * ((n : ℝ) - 1) ≤
          (n : ℝ) * ((n - 1 : ℕ) : ℝ) /
              ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) * (c * (m : ℝ) ^ 2) := by
        simpa only [Nat.cast_sub hn1, Nat.cast_sub hm1, Nat.cast_one] using
          (real_averaging_factor_lower hc
            (by exact_mod_cast hm26.trans' (by omega : 1 < 26))
            (by exact_mod_cast hn1))
      have hsixε : 0 < 6 * ε := mul_pos (by norm_num) hε
      have hone : (1 : ℝ) < 6 * ε * (n : ℝ) := by
        have := (div_lt_iff₀ hsixε).1 hnlinear
        nlinarith
      have hmul := mul_le_mul_of_nonneg_right hone.le (Nat.cast_nonneg n)
      have hlinear : (n : ℝ) / 12 ≤ ε / 2 * (n : ℝ) ^ 2 := by
        nlinarith
      have htarget : (1 / 12 - ε) * (n : ℝ) ^ 2 ≤
          c * (n : ℝ) * ((n : ℝ) - 1) := by
        dsimp only [c]
        nlinarith
      exact htarget.trans (hbase.trans (hscaled.trans hweight'))

/-- Public wrapper in the exact interface consumed by `RoundingAssembly`. -/
theorem GruslysLetzterFractional.smoothedFractionalMonochromaticTriangles
    (hGL : GruslysLetzterFractional) :
    SmoothedFractionalMonochromaticTriangles := by
  simpa only [SmoothedFractionalMonochromaticTriangles,
    SmoothedFractionalMonochromaticTrianglesByAveraging] using
      smoothedFractionalMonochromaticTrianglesByAveraging hGL

end GruslysLetzterAveraging

end

end Erdos76
