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
import ErdosProblems.Erdos622.External.Erdos76.FiniteBernoulliBoundedDifferences
import ErdosProblems.Erdos622.External.Erdos88.Foundations
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Concentration estimates for Erdős Problem 622

This file specializes the already proved finite-product McDiarmid inequality
to the uniform powerset.  It provides the two estimates used repeatedly in
the proof of the DKM theorem: Hoeffding concentration for subset sizes and
Azuma--Hoeffding concentration for induced edge counts.  All statements are
finite cardinality inequalities, so no measure-theoretic sample space is
hidden in the formalization.
-/

open Filter Finset Real
open scoped BigOperators Topology

namespace Erdos622.Concentration

noncomputable section

attribute [local instance] Classical.propDecidable

variable {E : Type*} [DecidableEq E]

private def halfProbability (_ : E) : ℝ := 1 / 2

/-- At parameter `1/2`, every member of a finite powerset has the same mass. -/
lemma bernoulliMass_half {U S : Finset E} (hS : S ⊆ U) :
    Erdos76.FiniteNibble.bernoulliMass U halfProbability S =
      1 / (2 : ℝ) ^ U.card := by
  rw [Erdos76.FiniteNibble.bernoulliMass]
  simp only [halfProbability, one_div]
  rw [prod_const, prod_const]
  norm_num
  have hcard : S.card + (U \ S).card = U.card := by
    have := card_sdiff_add_card_eq_card hS
    omega
  rw [← pow_add, hcard, one_div]
  exact inv_pow (2 : ℝ) U.card

/-- The Bernoulli expectation at parameter `1/2` is the ordinary uniform
average over the powerset. -/
lemma bernoulliExpectation_half (U : Finset E) (F : Finset E → ℝ) :
    Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F =
      (∑ S ∈ U.powerset, F S) / (2 : ℝ) ^ U.card := by
  rw [Erdos76.FiniteNibble.bernoulliExpectation]
  calc
    ∑ S ∈ U.powerset,
          Erdos76.FiniteNibble.bernoulliMass U halfProbability S * F S =
        ∑ S ∈ U.powerset, (1 / (2 : ℝ) ^ U.card) * F S := by
      apply sum_congr rfl
      intro S hS
      rw [bernoulliMass_half (mem_powerset.mp hS)]
    _ = (∑ S ∈ U.powerset, F S) / (2 : ℝ) ^ U.card := by
      rw [sum_div]
      apply sum_congr rfl
      intro S _
      ring

/-- The cardinality form of the upper-tail McDiarmid inequality on a uniform
powerset. -/
theorem countEvent_upperTail_le
    {U : Finset E} {F : Finset E → ℝ} {c : E → ℝ} {t : ℝ}
    (hbd : Erdos76.FiniteNibble.HasBoundedDifferences U F c) (ht : 0 ≤ t) :
    ((U.powerset.filter fun S ↦
        Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F + t ≤ F S).card : ℝ) ≤
      (2 : ℝ) ^ U.card *
        exp (-2 * t ^ 2 / (∑ e ∈ U, c e ^ 2)) := by
  have htail := Erdos76.FiniteNibble.bernoulliUpperTailMass_le_exp
    (U := U) (p := halfProbability) (F := F) (c := c) (t := t)
    (by intro; norm_num [halfProbability])
    (by intro; norm_num [halfProbability]) hbd ht
  have hmass :
      Erdos76.FiniteNibble.bernoulliUpperTailMass U halfProbability F
          (Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F + t) =
        ((U.powerset.filter fun S ↦
          Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F + t ≤ F S).card : ℝ) /
          (2 : ℝ) ^ U.card := by
    rw [Erdos76.FiniteNibble.bernoulliUpperTailMass]
    calc
      ∑ S ∈ U.powerset with
            Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F + t ≤ F S,
          Erdos76.FiniteNibble.bernoulliMass U halfProbability S =
          ∑ S ∈ U.powerset with
            Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F + t ≤ F S,
              1 / (2 : ℝ) ^ U.card := by
        apply sum_congr rfl
        intro S hS
        rw [bernoulliMass_half (mem_powerset.mp (mem_filter.mp hS).1)]
      _ = _ := by
        simp only [sum_const, nsmul_eq_mul]
        ring
  rw [hmass] at htail
  have hpow : 0 < (2 : ℝ) ^ U.card := by positivity
  calc
    ((U.powerset.filter fun S ↦
        Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F + t ≤ F S).card : ℝ) ≤
        exp (-2 * t ^ 2 / (∑ e ∈ U, c e ^ 2)) * (2 : ℝ) ^ U.card :=
      (div_le_iff₀ hpow).mp htail
    _ = _ := by ring

/-- The cardinality form of the lower-tail McDiarmid inequality on a uniform
powerset. -/
theorem countEvent_lowerTail_le
    {U : Finset E} {F : Finset E → ℝ} {c : E → ℝ} {t : ℝ}
    (hbd : Erdos76.FiniteNibble.HasBoundedDifferences U F c) (ht : 0 ≤ t) :
    ((U.powerset.filter fun S ↦ F S ≤
        Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F - t).card : ℝ) ≤
      (2 : ℝ) ^ U.card *
        exp (-2 * t ^ 2 / (∑ e ∈ U, c e ^ 2)) := by
  have htail := Erdos76.FiniteNibble.bernoulliLowerTailMass_le_exp
    (U := U) (p := halfProbability) (F := F) (c := c) (t := t)
    (by intro; norm_num [halfProbability])
    (by intro; norm_num [halfProbability]) hbd ht
  have hmass :
      Erdos76.FiniteNibble.bernoulliLowerTailMass U halfProbability F
          (Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F - t) =
        ((U.powerset.filter fun S ↦ F S ≤
          Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F - t).card : ℝ) /
          (2 : ℝ) ^ U.card := by
    rw [Erdos76.FiniteNibble.bernoulliLowerTailMass]
    calc
      ∑ S ∈ U.powerset with
            F S ≤ Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F - t,
          Erdos76.FiniteNibble.bernoulliMass U halfProbability S =
          ∑ S ∈ U.powerset with
            F S ≤ Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F - t,
              1 / (2 : ℝ) ^ U.card := by
        apply sum_congr rfl
        intro S hS
        rw [bernoulliMass_half (mem_powerset.mp (mem_filter.mp hS).1)]
      _ = _ := by
        simp only [sum_const, nsmul_eq_mul]
        ring
  rw [hmass] at htail
  have hpow : 0 < (2 : ℝ) ^ U.card := by positivity
  calc
    ((U.powerset.filter fun S ↦ F S ≤
        Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F - t).card : ℝ) ≤
        exp (-2 * t ^ 2 / (∑ e ∈ U, c e ^ 2)) * (2 : ℝ) ^ U.card :=
      (div_le_iff₀ hpow).mp htail
    _ = _ := by ring

/-- Exact mean of the cardinality of a uniform random subset. -/
lemma bernoulliExpectation_half_card (U : Finset E) :
    Erdos76.FiniteNibble.bernoulliExpectation U halfProbability
        (fun S ↦ (S.card : ℝ)) = (U.card : ℝ) / 2 := by
  rw [Erdos76.FiniteNibble.bernoulliExpectation,
    Erdos76.FiniteNibble.sum_bernoulliMass_mul_card]
  simp [halfProbability]
  ring

/-- Changing one membership bit changes subset cardinality by exactly one at
most. -/
lemma card_hasBoundedDifferences (U : Finset E) :
    Erdos76.FiniteNibble.HasBoundedDifferences U
      (fun S ↦ (S.card : ℝ)) (fun _ ↦ 1) := by
  intro e he T hT
  have heT : e ∉ T := by
    intro heT
    exact (mem_erase.mp (hT heT)).1 rfl
  simp [card_insert_of_notMem heT]

/-- One-sided uniform Hoeffding bound for subset cardinality. -/
theorem subsetCard_upperTail (U : Finset E) {t : ℝ} (ht : 0 ≤ t) :
    ((U.powerset.filter fun S ↦ (U.card : ℝ) / 2 + t ≤ S.card).card : ℝ) ≤
      (2 : ℝ) ^ U.card * exp (-2 * t ^ 2 / U.card) := by
  simpa [bernoulliExpectation_half_card] using
    countEvent_upperTail_le (card_hasBoundedDifferences U) ht

/-- One-sided lower Hoeffding bound for subset cardinality. -/
theorem subsetCard_lowerTail (U : Finset E) {t : ℝ} (ht : 0 ≤ t) :
    ((U.powerset.filter fun S ↦ (S.card : ℝ) ≤ (U.card : ℝ) / 2 - t).card : ℝ) ≤
      (2 : ℝ) ^ U.card * exp (-2 * t ^ 2 / U.card) := by
  simpa [bernoulliExpectation_half_card] using
    countEvent_lowerTail_le (card_hasBoundedDifferences U) ht

/-- The standard two-sided Hoeffding bound, in exact finite counting form. -/
theorem subsetCard_twoSided (U : Finset E) {t : ℝ} (ht : 0 ≤ t) :
    ((U.powerset.filter fun S ↦
        t ≤ |(S.card : ℝ) - (U.card : ℝ) / 2|).card : ℝ) ≤
      2 * (2 : ℝ) ^ U.card * exp (-2 * t ^ 2 / U.card) := by
  let A := U.powerset.filter fun S ↦ (U.card : ℝ) / 2 + t ≤ S.card
  let B := U.powerset.filter fun S ↦ (S.card : ℝ) ≤ (U.card : ℝ) / 2 - t
  have hsub : U.powerset.filter (fun S ↦
      t ≤ |(S.card : ℝ) - (U.card : ℝ) / 2|) ⊆ A ∪ B := by
    intro S hS
    simp only [mem_filter, mem_powerset, mem_union, A, B] at hS ⊢
    rcases (le_abs.mp hS.2) with h | h
    · exact Or.inl ⟨hS.1, by linarith⟩
    · exact Or.inr ⟨hS.1, by linarith⟩
  have hcard : (U.powerset.filter fun S ↦
      t ≤ |(S.card : ℝ) - (U.card : ℝ) / 2|).card ≤ A.card + B.card :=
    (card_le_card hsub).trans (card_union_le A B)
  have hA := subsetCard_upperTail U ht
  have hB := subsetCard_lowerTail U ht
  have hcardR : ((U.powerset.filter fun S ↦
      t ≤ |(S.card : ℝ) - (U.card : ℝ) / 2|).card : ℝ) ≤
      (A.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hcard
  dsimp [A, B] at hcardR
  linarith

section InducedEdges

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The induced-edge statistic, expressed as a real-valued function on the
uniform powerset. -/
def inducedEdgeCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : ℝ :=
  ((G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S).card : ℝ)

@[simp] lemma inducedEdgeCount_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    inducedEdgeCount G S = (Erdos88.inducedEdges G S : ℝ) := by
  rw [inducedEdgeCount, Erdos88.inducedEdges_eq_card_filter]

private lemma edge_survival_mass (G : SimpleGraph V) [DecidableRel G.Adj]
    {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    ∑ S ∈ (univ : Finset V).powerset with e.toFinset ⊆ S,
        Erdos76.FiniteNibble.bernoulliMass univ halfProbability S = 1 / 4 := by
  induction e using Sym2.inductionOn with
  | _ v w =>
      have hadj : G.Adj v w := by
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      have h := Erdos76.FiniteNibble.sum_bernoulliMass_filter_mem_mem
        (U := (univ : Finset V)) (p := halfProbability)
        (e := v) (f := w) (mem_univ v) (mem_univ w) hadj.ne
      calc
        ∑ S ∈ (univ : Finset V).powerset with s(v, w).toFinset ⊆ S,
            Erdos76.FiniteNibble.bernoulliMass univ halfProbability S =
            ∑ S ∈ (univ : Finset V).powerset with v ∈ S ∧ w ∈ S,
              Erdos76.FiniteNibble.bernoulliMass univ halfProbability S := by
          congr 2
          ext S
          rw [Sym2.toFinset_mk_eq]
          constructor
          · intro hs
            exact ⟨
              hs (mem_insert_self v {w}),
              hs (mem_insert_of_mem (mem_singleton_self w))⟩
          · rintro ⟨hv, hw⟩
            intro x hx
            simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hv
            · exact hw
        _ = 1 / 4 := by
          rw [h]
          norm_num [halfProbability]

/-- Every graph edge survives uniform vertex sampling with probability
exactly `1/4`. -/
lemma bernoulliExpectation_half_inducedEdgeCount
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Erdos76.FiniteNibble.bernoulliExpectation (univ : Finset V)
        halfProbability (inducedEdgeCount G) =
      (G.edgeFinset.card : ℝ) / 4 := by
  rw [Erdos76.FiniteNibble.bernoulliExpectation]
  have hcount (S : Finset V) :
      inducedEdgeCount G S =
        ∑ e ∈ G.edgeFinset, if e.toFinset ⊆ S then (1 : ℝ) else 0 := by
    rw [inducedEdgeCount]
    simp [← sum_filter]
  calc
    ∑ S ∈ (univ : Finset V).powerset,
          Erdos76.FiniteNibble.bernoulliMass univ halfProbability S * inducedEdgeCount G S =
        ∑ S ∈ (univ : Finset V).powerset, ∑ e ∈ G.edgeFinset,
          if e.toFinset ⊆ S then
            Erdos76.FiniteNibble.bernoulliMass univ halfProbability S else 0 := by
      apply sum_congr rfl
      intro S _
      rw [hcount, mul_sum]
      apply sum_congr rfl
      intro e _
      by_cases he : e.toFinset ⊆ S <;> simp [he]
    _ = ∑ e ∈ G.edgeFinset, ∑ S ∈ (univ : Finset V).powerset,
          if e.toFinset ⊆ S then
            Erdos76.FiniteNibble.bernoulliMass univ halfProbability S else 0 := by
      rw [sum_comm]
    _ = ∑ _e ∈ G.edgeFinset, (1 / 4 : ℝ) := by
      apply sum_congr rfl
      intro e he
      rw [← sum_filter]
      exact edge_survival_mass G he
    _ = (G.edgeFinset.card : ℝ) / 4 := by simp; ring

/-- Toggling a vertex changes the induced-edge count by at most its degree. -/
lemma inducedEdgeCount_hasBoundedDifferences
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Erdos76.FiniteNibble.HasBoundedDifferences (univ : Finset V)
      (inducedEdgeCount G) (fun v ↦ G.degree v) := by
  intro v _ T hT
  have hvT : v ∉ T := by
    intro hvT
    exact (mem_erase.mp (hT hvT)).1 rfl
  let A := G.edgeFinset.filter fun e ↦ e.toFinset ⊆ insert v T
  let B := G.edgeFinset.filter fun e ↦ e.toFinset ⊆ T
  let I := G.incidenceFinset v
  have hBA : B ⊆ A := by
    intro e he
    simp only [B, A, mem_filter] at he ⊢
    exact ⟨he.1, he.2.trans (subset_insert v T)⟩
  have hAI : A ⊆ B ∪ I := by
    intro e he
    simp only [A, B, I, mem_filter, mem_union]
    by_cases heT : e.toFinset ⊆ T
    · exact Or.inl ⟨(mem_filter.mp he).1, heT⟩
    · right
      rw [SimpleGraph.incidenceFinset_eq_filter]
      refine mem_filter.mpr ⟨(mem_filter.mp he).1, ?_⟩
      rw [← Sym2.mem_toFinset]
      by_contra hve
      apply heT
      intro x hxe
      have hx := (mem_filter.mp he).2 hxe
      rcases mem_insert.mp hx with hxv | hxT
      · exact (hve (hxv ▸ hxe)).elim
      · exact hxT
  have hcardBA : B.card ≤ A.card := card_le_card hBA
  have hcardAI : A.card ≤ B.card + I.card :=
    (card_le_card hAI).trans (card_union_le B I)
  have hI : I.card = G.degree v := by
    dsimp [I]
    exact G.card_incidenceFinset_eq_degree v
  change |(A.card : ℝ) - (B.card : ℝ)| ≤ (G.degree v : ℝ)
  have hnonneg : 0 ≤ (A.card : ℝ) - (B.card : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hcardBA)
  rw [abs_of_nonneg hnonneg]
  exact_mod_cast (by omega : A.card - B.card ≤ G.degree v)

/-- Two-sided Azuma--Hoeffding concentration for the number of induced
edges, with the natural squared-degree variance proxy. -/
theorem inducedEdgeCount_twoSided
    (G : SimpleGraph V) [DecidableRel G.Adj] {t : ℝ} (ht : 0 ≤ t) :
    ((((univ : Finset V).powerset.filter fun S ↦
        t ≤ |inducedEdgeCount G S - (G.edgeFinset.card : ℝ) / 4|).card : ℝ)) ≤
      2 * (2 : ℝ) ^ Fintype.card V *
        exp (-2 * t ^ 2 / (∑ v : V, (G.degree v : ℝ) ^ 2)) := by
  let U : Finset V := univ
  let F : Finset V → ℝ := inducedEdgeCount G
  let c : V → ℝ := fun v ↦ G.degree v
  let A := U.powerset.filter fun S ↦
    Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F + t ≤ F S
  let B := U.powerset.filter fun S ↦
    F S ≤ Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F - t
  have hsub : U.powerset.filter (fun S ↦
      t ≤ |F S - Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F|) ⊆
      A ∪ B := by
    intro S hS
    simp only [mem_filter, mem_powerset, mem_union, A, B] at hS ⊢
    rcases le_abs.mp hS.2 with h | h
    · exact Or.inl ⟨hS.1, by linarith⟩
    · exact Or.inr ⟨hS.1, by linarith⟩
  have hcard : (U.powerset.filter fun S ↦
      t ≤ |F S - Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F|).card ≤
      A.card + B.card := (card_le_card hsub).trans (card_union_le A B)
  have hA := countEvent_upperTail_le
    (inducedEdgeCount_hasBoundedDifferences G) ht
  have hB := countEvent_lowerTail_le
    (inducedEdgeCount_hasBoundedDifferences G) ht
  have hcardR : ((U.powerset.filter fun S ↦
      t ≤ |F S - Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F|).card : ℝ) ≤
      (A.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hcard
  dsimp [U, F, c, A, B] at hcardR hA hB ⊢
  rw [bernoulliExpectation_half_inducedEdgeCount] at hcardR hA hB
  linarith

/-- The squared-degree proxy is bounded by `2 Δ e`, the estimate used in
the DKM induced-edge concentration argument. -/
lemma sum_degree_sq_le_maxDegree_mul_edges
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v : V, (G.degree v : ℝ) ^ 2 ≤
      2 * G.maxDegree * G.edgeFinset.card := by
  calc
    ∑ v : V, (G.degree v : ℝ) ^ 2 ≤
        ∑ v : V, (G.maxDegree : ℝ) * G.degree v := by
      apply sum_le_sum
      intro v _
      have hd := G.degree_le_maxDegree v
      have hdR : (G.degree v : ℝ) ≤ G.maxDegree := by exact_mod_cast hd
      nlinarith [sq_nonneg (G.degree v : ℝ)]
    _ = (G.maxDegree : ℝ) * (∑ v : V, G.degree v) := by
      rw [Nat.cast_sum, mul_sum]
    _ = 2 * G.maxDegree * G.edgeFinset.card := by
      rw [G.sum_degrees_eq_twice_card_edges]
      norm_num
      ring

/-- Sequence form of induced-edge concentration.  If the explicit
Azuma exponent tends to minus infinity, then the proportion of subsets
outside the corresponding moving window tends to zero. -/
def inducedEdgeBadProportion {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℝ) : ℝ :=
  (((univ : Finset (Fin n)).powerset.filter fun S ↦
      t ≤ |inducedEdgeCount G S - (G.edgeFinset.card : ℝ) / 4|).card : ℝ) /
    (2 : ℝ) ^ n

theorem inducedEdgeCount_badProportion_tendsto_zero
    (G : ∀ n : ℕ, SimpleGraph (Fin n)) (t : ℕ → ℝ)
    (ht : ∀ᶠ n : ℕ in atTop, 0 ≤ t n)
    (hdecay : Tendsto (fun n : ℕ ↦
      -2 * (t n) ^ 2 /
        (∑ v : Fin n, ((G n).degree v : ℝ) ^ 2)) atTop atBot) :
    Tendsto (fun n : ℕ ↦ inducedEdgeBadProportion (G n) (t n))
      atTop (nhds 0) := by
  classical
  have hmajor : Tendsto (fun n : ℕ ↦
      2 * exp (-2 * (t n) ^ 2 /
        (∑ v : Fin n, ((G n).degree v : ℝ) ^ 2))) atTop (nhds 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hdecay).const_mul 2
  apply squeeze_zero' (g := fun n : ℕ ↦
    2 * exp (-2 * (t n) ^ 2 /
      (∑ v : Fin n, ((G n).degree v : ℝ) ^ 2)))
  · exact Eventually.of_forall fun n ↦ by
      unfold inducedEdgeBadProportion
      positivity
  · filter_upwards [ht] with n htn
    have hb := inducedEdgeCount_twoSided (G n) htn
    have hpow : 0 < (2 : ℝ) ^ n := by positivity
    unfold inducedEdgeBadProportion
    rw [div_le_iff₀ hpow]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hb
  · exact hmajor

/-- Fully quantified eventual form of induced-edge concentration. -/
theorem eventually_inducedEdgeCount_badProportion_lt
    (G : ∀ n : ℕ, SimpleGraph (Fin n)) (t : ℕ → ℝ)
    (ht : ∀ᶠ n : ℕ in atTop, 0 ≤ t n)
    (hdecay : Tendsto (fun n : ℕ ↦
      -2 * (t n) ^ 2 /
        (∑ v : Fin n, ((G n).degree v : ℝ) ^ 2)) atTop atBot)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      inducedEdgeBadProportion (G n) (t n) < ε := by
  have h := inducedEdgeCount_badProportion_tendsto_zero G t ht hdecay
  rcases Metric.tendsto_atTop.1 h ε hε with ⟨N, hN⟩
  exact eventually_atTop.2 ⟨N, fun n hn ↦ by
    have hnonneg : 0 ≤ inducedEdgeBadProportion (G n) (t n) := by
      unfold inducedEdgeBadProportion
      positivity
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hN n hn⟩

end InducedEdges

/-- An `O(n)` union bound multiplied by any fixed exponentially decaying
Hoeffding tail tends to zero. -/
theorem tendsto_linear_mul_exp_neg (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * exp (-c * n)) atTop (nhds 0) := by
  have hscale : Tendsto (fun n : ℕ ↦ c * (n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
  have hcne : c ≠ 0 := ne_of_gt hc
  convert h.const_mul (1 / c) using 1
  · ext n
    simp only [Function.comp_apply, pow_one]
    field_simp
  · simp

/-- Explicit eventual form of the preceding exponential-union estimate. -/
theorem eventually_linear_mul_exp_neg_lt
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) * exp (-c * n) < ε := by
  have h := tendsto_linear_mul_exp_neg c hc
  rcases Metric.tendsto_atTop.1 h ε hε with ⟨N, hN⟩
  exact eventually_atTop.2 ⟨N, fun n hn ↦ by
    simpa [Real.dist_eq] using hN n hn⟩

end

end Erdos622.Concentration
