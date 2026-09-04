/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos63.ExpanderDefs
import ErdosProblems.Erdos63.BipartiteHalf

/-!
# Extracting a sublinear expander

This file formalizes the Komlós--Szemerédi density-maximization argument used
in the proof of Erdős Problem 63.  The formulation uses the base-two logarithm;
this is equivalent, up to the absolute constant in the numerator, to the
natural-logarithm formulation in Liu--Montgomery.
-/

open Finset Set SimpleGraph
open scoped BigOperators SimpleGraph

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable section

universe u

variable {V : Type u}

/-! ## Numerical profiles -/

/-- Average degree, with value zero on the empty graph. -/
def averageDegree [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  (2 * G.edgeFinset.card : ℝ) / Fintype.card V

/-- The number of edges of `G` having both endpoints in `S`.  Keeping this as
an ambient finite-set count makes comparisons between differently induced
graphs painless. -/
noncomputable def ksInducedEdges [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (S : Finset V) : ℕ := by
  classical
  exact (G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S).card

lemma ksInducedEdges_eq_card_edgeFinset_induce [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    ksInducedEdges G S = (G.induce (↑S : Set V)).edgeFinset.card := by
  classical
  simpa [ksInducedEdges] using G.card_filter_edgeFinset_toFinset_subset S

@[simp] lemma ksInducedEdges_empty [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ksInducedEdges G ∅ = 0 := by
  classical
  simp [ksInducedEdges]

@[simp] lemma ksInducedEdges_univ [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ksInducedEdges G Finset.univ = G.edgeFinset.card := by
  classical
  simp [ksInducedEdges]

/-- Average degree of the graph induced by an ambient finite vertex set. -/
def ksInducedAverageDegree [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (S : Finset V) : ℝ :=
  (2 * ksInducedEdges G S : ℝ) / S.card

@[simp] lemma ksInducedAverageDegree_empty [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ksInducedAverageDegree G ∅ = 0 := by
  simp [ksInducedAverageDegree]

@[simp] lemma ksInducedAverageDegree_univ [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ksInducedAverageDegree G Finset.univ = averageDegree G := by
  simp [ksInducedAverageDegree, averageDegree]

lemma ksInducedAverageDegree_nonneg [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    0 ≤ ksInducedAverageDegree G S := by
  exact div_nonneg (by positivity) (by positivity)

/-- The auxiliary potential from the density-maximization proof.  Below the
expansion threshold it is kept equal to one. -/
def ksGamma (t x : ℝ) : ℝ :=
  if x < t then 1 else (Real.logb 2 (2 * x / t))⁻¹

/-- A convenient Komlós--Szemerédi expansion profile. -/
def ksRate (t x : ℝ) : ℝ :=
  if x < t then 0 else
    Real.logb 2 (3 / 2) / (128 * (Real.logb 2 (4 * x / t)) ^ 2)

/-- `G` expands every vertex set between the threshold and half its order. -/
def IsKSExpander [Fintype V] (G : SimpleGraph V) (t : ℝ) : Prop :=
  ∀ S : Finset V,
    t ≤ S.card → 2 * S.card ≤ Fintype.card V →
      ksRate t S.card * S.card ≤ (externalNeighborhood G S).card

lemma ksGamma_mem_Icc {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    ksGamma t x ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hxt : x < t
  · simp [ksGamma, hxt]
  · have htx : t ≤ x := le_of_not_gt hxt
    have harg : (2 : ℝ) ≤ 2 * x / t := by
      rw [le_div_iff₀ ht]
      nlinarith
    have hlog : (1 : ℝ) ≤ Real.logb 2 (2 * x / t) := by
      rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      exact Real.logb_le_logb_of_le (by norm_num) (by positivity) harg
    simp only [ksGamma, hxt, if_false]
    exact ⟨inv_nonneg.2 (zero_le_one.trans hlog), inv_le_one_of_one_le₀ hlog⟩

lemma ksGamma_nonneg {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    0 ≤ ksGamma t x :=
  (ksGamma_mem_Icc ht hx).1

lemma ksGamma_le_one {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    ksGamma t x ≤ 1 :=
  (ksGamma_mem_Icc ht hx).2

lemma ksGamma_anti {t x y : ℝ} (ht : 0 < t) (hx : 0 < x) (hxy : x ≤ y) :
    ksGamma t y ≤ ksGamma t x := by
  have hy : 0 < y := hx.trans_le hxy
  by_cases hxt : x < t
  · exact (ksGamma_le_one ht hy).trans_eq (by simp [ksGamma, hxt])
  · have htx : t ≤ x := le_of_not_gt hxt
    have hyt : ¬y < t := not_lt_of_ge (htx.trans hxy)
    have hargx : 1 < 2 * x / t := by
      rw [lt_div_iff₀ ht]
      nlinarith
    have hargy : 1 < 2 * y / t := by
      rw [lt_div_iff₀ ht]
      nlinarith
    have hlogxy : Real.logb 2 (2 * x / t) ≤ Real.logb 2 (2 * y / t) := by
      apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxy (by norm_num)) ht.le
    have hlogx : 0 < Real.logb 2 (2 * x / t) :=
      Real.logb_pos (by norm_num) hargx
    have hlogy : 0 < Real.logb 2 (2 * y / t) :=
      Real.logb_pos (by norm_num) hargy
    simp only [ksGamma, hxt, hyt, if_false]
    exact (inv_le_inv₀ hlogy hlogx).2 hlogxy

lemma ksRate_nonneg {t x : ℝ} (ht : 0 < t) (hx : 0 ≤ x) :
    0 ≤ ksRate t x := by
  by_cases hxt : x < t
  · simp [ksRate, hxt]
  · have htx : t ≤ x := le_of_not_gt hxt
    have hnum : 0 ≤ Real.logb 2 (3 / 2) := by
      exact (Real.logb_nonneg_iff (by norm_num : (1 : ℝ) < 2) (by norm_num)).2 (by norm_num)
    simp only [ksRate, hxt, if_false]
    positivity

lemma ksRate_le_one_third {t x : ℝ} (ht : 0 < t) (htx : t ≤ x) :
    ksRate t x ≤ (1 : ℝ) / 3 := by
  have hxt : ¬x < t := not_lt_of_ge htx
  have hlog : (2 : ℝ) ≤ Real.logb 2 (4 * x / t) := by
    have hfour : Real.logb 2 (4 : ℝ) = 2 := by
      calc
        Real.logb 2 (4 : ℝ) = Real.logb 2 ((2 : ℝ) ^ 2) := by norm_num
        _ = 2 * Real.logb 2 (2 : ℝ) := Real.logb_pow 2 2 2
        _ = 2 := by rw [Real.logb_self_eq_one (by norm_num)]; norm_num
    calc
      (2 : ℝ) = Real.logb 2 (4 : ℝ) := hfour.symm
      _ ≤ Real.logb 2 (4 * x / t) := by
        apply Real.logb_le_logb_of_le (by norm_num) (by norm_num)
        rw [le_div_iff₀ ht]
        nlinarith
  have hnum : Real.logb 2 (3 / 2) ≤ 1 := by
    rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
  have hsq : (4 : ℝ) ≤ (Real.logb 2 (4 * x / t)) ^ 2 := by
    nlinarith [sq_nonneg (Real.logb 2 (4 * x / t) - 2)]
  have hden : 0 < 128 * (Real.logb 2 (4 * x / t)) ^ 2 := by nlinarith
  simp only [ksRate, hxt, if_false]
  rw [div_le_iff₀ hden]
  nlinarith

lemma ksRate_le_one {t x : ℝ} (ht : 0 < t) (htx : t ≤ x) :
    ksRate t x ≤ 1 := by
  exact (ksRate_le_one_third ht htx).trans (by norm_num)

lemma ksRate_anti {t x y : ℝ} (ht : 0 < t) (htx : t ≤ x) (hxy : x ≤ y) :
    ksRate t y ≤ ksRate t x := by
  have hty : t ≤ y := htx.trans hxy
  have hxt : ¬ x < t := not_lt_of_ge htx
  have hyt : ¬ y < t := not_lt_of_ge hty
  have hxpos : 0 < x := ht.trans_le htx
  have hypos : 0 < y := hxpos.trans_le hxy
  have hargx : 1 < 4 * x / t := by
    rw [lt_div_iff₀ ht]
    nlinarith
  have hargy : 1 < 4 * y / t := by
    rw [lt_div_iff₀ ht]
    nlinarith
  have hlogx : 0 < Real.logb 2 (4 * x / t) :=
    Real.logb_pos (by norm_num) hargx
  have hlogy : 0 < Real.logb 2 (4 * y / t) :=
    Real.logb_pos (by norm_num) hargy
  have hlogxy : Real.logb 2 (4 * x / t) ≤ Real.logb 2 (4 * y / t) := by
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    rw [div_le_div_iff_of_pos_right ht]
    nlinarith
  have hsq : (Real.logb 2 (4 * x / t)) ^ 2 ≤
      (Real.logb 2 (4 * y / t)) ^ 2 :=
    (sq_le_sq₀ hlogx.le hlogy.le).2 hlogxy
  have hdenpos : 0 < 128 * (Real.logb 2 (4 * x / t)) ^ 2 := by positivity
  have hdenle : 128 * (Real.logb 2 (4 * x / t)) ^ 2 ≤
      128 * (Real.logb 2 (4 * y / t)) ^ 2 := by nlinarith
  have hnum : 0 ≤ Real.logb 2 (3 / 2) :=
    (Real.logb_nonneg_iff (by norm_num : (1 : ℝ) < 2) (by norm_num)).2 (by norm_num)
  simp only [ksRate, hxt, hyt, if_false]
  exact div_le_div_of_nonneg_left hnum hdenpos hdenle

lemma ksRate_double {t x : ℝ} (ht : 0 < t) (htx : t ≤ x) :
    ksRate t x ≤ 4 * ksRate t (2 * x) := by
  have hxpos : 0 < x := ht.trans_le htx
  have hxt : ¬ x < t := not_lt_of_ge htx
  have h2xt : ¬ 2 * x < t := not_lt_of_ge (by nlinarith)
  let A : ℝ := Real.logb 2 (4 * x / t)
  let B : ℝ := Real.logb 2 (4 * (2 * x) / t)
  have hA : 0 < A := by
    dsimp [A]
    apply Real.logb_pos (by norm_num)
    rw [lt_div_iff₀ ht]
    nlinarith
  have hB : 0 < B := by
    dsimp [B]
    apply Real.logb_pos (by norm_num)
    rw [lt_div_iff₀ ht]
    nlinarith
  have hu : (1 : ℝ) ≤ x / t := by
    rw [le_div_iff₀ ht]
    simpa using htx
  have hu_sq : x / t ≤ (x / t) ^ 2 := by
    nlinarith [sq_nonneg (x / t - 1)]
  have hargSq : 4 * (2 * x) / t ≤ (4 * x / t) ^ 2 := by
    calc
      4 * (2 * x) / t = 8 * (x / t) := by ring
      _ ≤ 16 * (x / t) ^ 2 := by nlinarith [hu_sq, sq_nonneg (x / t)]
      _ = (4 * x / t) ^ 2 := by ring
  have hBA : B ≤ 2 * A := by
    dsimp [A, B]
    calc
      Real.logb 2 (4 * (2 * x) / t)
          ≤ Real.logb 2 ((4 * x / t) ^ 2) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) hargSq
      _ = 2 * Real.logb 2 (4 * x / t) := by
        simpa using Real.logb_pow (2 : ℝ) (4 * x / t) 2
  have hsq : B ^ 2 ≤ (2 * A) ^ 2 :=
    (sq_le_sq₀ hB.le (by positivity)).2 hBA
  have hdenle : 32 * B ^ 2 ≤ 128 * A ^ 2 := by nlinarith
  have hdenpos : 0 < 32 * B ^ 2 := by positivity
  have hnum : 0 ≤ Real.logb 2 (3 / 2) :=
    (Real.logb_nonneg_iff (by norm_num : (1 : ℝ) < 2) (by norm_num)).2 (by norm_num)
  simp only [ksRate, hxt, h2xt, if_false]
  simpa [A, B] using
    (calc
      Real.logb 2 (3 / 2) / (128 * A ^ 2)
          ≤ Real.logb 2 (3 / 2) / (32 * B ^ 2) :=
        div_le_div_of_nonneg_left hnum hdenpos hdenle
      _ = 4 * (Real.logb 2 (3 / 2) / (128 * B ^ 2)) := by ring)

lemma ksGamma_gap {t x : ℝ} (ht : 0 < t) (htx : t ≤ x) :
    64 * ksRate t x ≤
      (ksGamma t x - ksGamma t (3 * x / 2)) / 2 := by
  have hxpos : 0 < x := ht.trans_le htx
  have hxt : ¬ x < t := not_lt_of_ge htx
  have h3xt : ¬ 3 * x / 2 < t := not_lt_of_ge (by nlinarith)
  let A : ℝ := Real.logb 2 (2 * x / t)
  let B : ℝ := Real.logb 2 (2 * (3 * x / 2) / t)
  let C : ℝ := Real.logb 2 (4 * x / t)
  let L : ℝ := Real.logb 2 (3 / 2)
  have hA : 0 < A := by
    dsimp [A]
    apply Real.logb_pos (by norm_num)
    rw [lt_div_iff₀ ht]
    nlinarith
  have hB : 0 < B := by
    dsimp [B]
    apply Real.logb_pos (by norm_num)
    rw [lt_div_iff₀ ht]
    nlinarith
  have hC : 0 < C := by
    dsimp [C]
    apply Real.logb_pos (by norm_num)
    rw [lt_div_iff₀ ht]
    nlinarith
  have hL : 0 ≤ L := by
    dsimp [L]
    exact (Real.logb_nonneg_iff (by norm_num : (1 : ℝ) < 2) (by norm_num)).2
      (by norm_num)
  have hargEq : 2 * (3 * x / 2) / t = (2 * x / t) * (3 / 2) := by ring
  have hBAeq : B = A + L := by
    dsimp [A, B, L]
    calc
      Real.logb 2 (2 * (3 * x / 2) / t)
          = Real.logb 2 ((2 * x / t) * (3 / 2)) :=
        congrArg (Real.logb 2) hargEq
      _ = Real.logb 2 (2 * x / t) + Real.logb 2 (3 / 2) :=
        Real.logb_mul (by positivity) (by norm_num)
  have hAC : A ≤ C := by
    dsimp [A, C]
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    rw [div_le_div_iff_of_pos_right ht]
    nlinarith
  have hBC : B ≤ C := by
    dsimp [B, C]
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    rw [div_le_div_iff_of_pos_right ht]
    nlinarith
  have hAB : A * B ≤ C ^ 2 := by
    calc
      A * B ≤ C * B := mul_le_mul_of_nonneg_right hAC hB.le
      _ ≤ C * C := mul_le_mul_of_nonneg_left hBC hC.le
      _ = C ^ 2 := by ring
  have hdiffBA : B - A = L := by linarith [hBAeq]
  have hdiff : (A⁻¹ - B⁻¹) / 2 = L / (2 * A * B) := by
    calc
      (A⁻¹ - B⁻¹) / 2 = ((B - A) / (A * B)) / 2 := by
        rw [inv_sub_inv hA.ne' hB.ne']
      _ = (L / (A * B)) / 2 := by rw [hdiffBA]
      _ = L / (2 * A * B) := by ring
  have hdenpos : 0 < 2 * A * B := by positivity
  have hdenle : 2 * A * B ≤ 2 * C ^ 2 := by nlinarith
  simp only [ksRate, hxt, if_false, ksGamma, h3xt]
  change 64 * (L / (128 * C ^ 2)) ≤ (A⁻¹ - B⁻¹) / 2
  calc
    64 * (L / (128 * C ^ 2)) = L / (2 * C ^ 2) := by ring
    _ ≤ L / (2 * A * B) :=
      div_le_div_of_nonneg_left hL hdenpos hdenle
    _ = (A⁻¹ - B⁻¹) / 2 := hdiff.symm

@[simp] lemma averageDegree_empty [Fintype V] :
    averageDegree (G := (⊥ : SimpleGraph V)) = 0 := by
  simp [averageDegree]

lemma averageDegree_nonneg [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : 0 ≤ averageDegree G := by
  exact div_nonneg (by positivity) (by positivity)

lemma averageDegree_eq_sum_degrees [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    averageDegree G = (∑ v : V, G.degree v : ℝ) / Fintype.card V := by
  rw [averageDegree]
  congr 1
  norm_cast
  exact G.sum_degrees_eq_twice_card_edges.symm

lemma avgDegreeAtLeast_iff [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d : ℕ} (hV : 0 < Fintype.card V) :
    AvgDegreeAtLeast G d ↔ (d : ℝ) ≤ averageDegree G := by
  have hVR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hV
  constructor
  · intro h
    rw [averageDegree_eq_sum_degrees]
    apply (le_div_iff₀ hVR).2
    rw [AvgDegreeAtLeast] at h
    exact_mod_cast h
  · intro h
    rw [averageDegree_eq_sum_degrees] at h
    have h' := (le_div_iff₀ hVR).1 h
    rw [AvgDegreeAtLeast]
    exact_mod_cast h'

/-! ## The maximizing induced subgraph -/

/-- Potential score of the subgraph induced on `S`. -/
def ksInducedScore [Fintype V] (t : ℝ) (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (S : Finset V) : ℝ :=
  ksInducedAverageDegree G S * (1 + ksGamma t S.card)

/-- A potential-maximizing induced subgraph exists. -/
lemma exists_ksInducedScore_maximizer [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (t : ℝ) :
    ∃ S : Finset V, ∀ T : Finset V,
      ksInducedScore t G T ≤ ksInducedScore t G S := by
  classical
  obtain ⟨S, -, hS⟩ :=
    Finset.exists_max_image (Finset.univ.powerset : Finset (Finset V))
      (ksInducedScore t G) ⟨∅, by simp⟩
  refine ⟨S, fun T ↦ hS T ?_⟩
  simp

lemma ksInducedAverageDegree_le_of_score_maximal [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : ℝ} (ht : 0 < t) {S : Finset V}
    (hS : S.Nonempty)
    (hmax : ∀ T : Finset V,
      ksInducedScore t G T ≤ ksInducedScore t G S) :
    ∀ T : Finset V, T ⊆ S →
      ksInducedAverageDegree G T ≤ ksInducedAverageDegree G S := by
  intro T hTS
  by_cases hT : T.Nonempty
  · have hcard : (T.card : ℝ) ≤ S.card := by
      exact_mod_cast Finset.card_le_card hTS
    have hTcard : 0 < (T.card : ℝ) := by exact_mod_cast hT.card_pos
    have hgamma := ksGamma_anti ht hTcard hcard
    have hnonT : 0 ≤ 1 + ksGamma t T.card := by
      have := ksGamma_nonneg ht hTcard
      linarith
    have hnonS : 0 ≤ ksInducedAverageDegree G S :=
      ksInducedAverageDegree_nonneg G S
    by_contra hle
    have havglt : ksInducedAverageDegree G S <
        ksInducedAverageDegree G T := lt_of_not_ge hle
    have hscorelt : ksInducedScore t G S < ksInducedScore t G T := by
      rw [ksInducedScore, ksInducedScore]
      calc
        ksInducedAverageDegree G S * (1 + ksGamma t S.card)
            ≤ ksInducedAverageDegree G S * (1 + ksGamma t T.card) := by
              gcongr
        _ < ksInducedAverageDegree G T * (1 + ksGamma t T.card) := by
              exact mul_lt_mul_of_pos_right havglt (by
                have := ksGamma_nonneg ht hTcard
                linarith)
    exact (not_lt_of_ge (hmax T)) hscorelt
  · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    simp [hTempty, ksInducedAverageDegree_nonneg G S]

lemma ks_maximizer_nonempty_and_retains_average [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : ℝ} (ht : 0 < t) {S : Finset V}
    (hGpos : 0 < averageDegree G)
    (hmax : ∀ T : Finset V,
      ksInducedScore t G T ≤ ksInducedScore t G S) :
    S.Nonempty ∧ averageDegree G / 2 ≤ ksInducedAverageDegree G S := by
  have hscore_univ : 0 < ksInducedScore t G Finset.univ := by
    rw [ksInducedScore, ksInducedAverageDegree_univ]
    have hcard : 0 < (Fintype.card V : ℝ) := by
      by_cases hzero : Fintype.card V = 0
      · simp [averageDegree, hzero] at hGpos
      · exact_mod_cast Nat.pos_of_ne_zero hzero
    have hgamma : 0 ≤ ksGamma t ((Finset.univ : Finset V).card : ℝ) := by
      simpa using ksGamma_nonneg ht hcard
    exact mul_pos hGpos (by linarith)
  have hSne : S.Nonempty := by
    by_contra hS
    have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hle : ksInducedScore t G Finset.univ ≤ 0 := by
      simpa [ksInducedScore, hSempty] using hmax Finset.univ
    exact (not_le_of_gt hscore_univ) hle
  refine ⟨hSne, ?_⟩
  have hScard : 0 < (S.card : ℝ) := by exact_mod_cast hSne.card_pos
  have hg0 := ksGamma_nonneg ht hScard
  have hg1 := ksGamma_le_one ht hScard
  have hnon := ksInducedAverageDegree_nonneg G S
  have hleft : averageDegree G ≤
      ksInducedScore t G Finset.univ := by
    rw [ksInducedScore, ksInducedAverageDegree_univ]
    have hGnon : 0 ≤ averageDegree G := hGpos.le
    have hVcard : 0 < (Fintype.card V : ℝ) := by
      have hVnat : 0 < Fintype.card V := by
        by_contra h
        have hzero : Fintype.card V = 0 := Nat.eq_zero_of_not_pos h
        simp [averageDegree, hzero] at hGpos
      exact_mod_cast hVnat
    have hgV : 0 ≤ ksGamma t ((Finset.univ : Finset V).card : ℝ) := by
      simpa using ksGamma_nonneg ht hVcard
    nlinarith [mul_nonneg hGnon hgV]
  have hright : ksInducedScore t G S ≤
      2 * ksInducedAverageDegree G S := by
    rw [ksInducedScore]
    calc
      ksInducedAverageDegree G S * (1 + ksGamma t S.card) ≤
          ksInducedAverageDegree G S * 2 :=
        mul_le_mul_of_nonneg_left (by linarith) hnon
      _ = 2 * ksInducedAverageDegree G S := by ring
  have := hleft.trans ((hmax Finset.univ).trans hright)
  linarith

/-! ## Transport between an induced graph and the ambient graph -/

/-- Forget the subtype proof in a finite vertex set. -/
noncomputable def ksFinsetImage {S : Finset V}
    (A : Finset (↑S : Set V)) : Finset V := by
  classical
  exact A.image Subtype.val

@[simp] lemma card_ksFinsetImage {S : Finset V}
    (A : Finset (↑S : Set V)) : (ksFinsetImage A).card = A.card := by
  classical
  exact Finset.card_image_of_injective A Subtype.val_injective

lemma ksFinsetImage_subset {S : Finset V}
    (A : Finset (↑S : Set V)) : ksFinsetImage A ⊆ S := by
  classical
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact y.2

/-- Inducing first on `S` and then on `A` is isomorphic to inducing on the
ambient image of `A`. -/
private noncomputable def ksInduceImageIso [Fintype V]
    (G : SimpleGraph V) (S : Finset V) (A : Finset (↑S : Set V)) :
    G.induce (↑(ksFinsetImage A) : Set V) ≃g
      (G.induce (↑S : Set V)).induce (↑A : Set (↑S : Set V)) := by
  classical
  let f : (G.induce (↑S : Set V)).induce (↑A : Set (↑S : Set V)) ≃g
      G.induce (↑(ksFinsetImage A) : Set V) :=
    { toFun := fun x ↦
        ⟨x.1.1, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩
      invFun := fun x ↦
        ⟨Classical.choose (Finset.mem_image.mp x.2),
          (Classical.choose_spec (Finset.mem_image.mp x.2)).1⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        exact (Classical.choose_spec (Finset.mem_image.mp
          (Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩))).2
      right_inv := by
        intro x
        apply Subtype.ext
        exact (Classical.choose_spec (Finset.mem_image.mp x.2)).2
      map_rel_iff' := Iff.rfl }
  exact f.symm

lemma ksInducedAverageDegree_image [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (A : Finset (↑S : Set V)) :
    ksInducedAverageDegree G (ksFinsetImage A) =
      ksInducedAverageDegree (G.induce (↑S : Set V)) A := by
  classical
  rw [ksInducedAverageDegree, ksInducedAverageDegree,
    ksInducedEdges_eq_card_edgeFinset_induce,
    ksInducedEdges_eq_card_edgeFinset_induce, card_ksFinsetImage,
    (ksInduceImageIso G S A).card_edgeFinset_eq]

lemma ksInducedAverageDegree_le_in_maximizer [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : ℝ} (ht : 0 < t) {S : Finset V} (hS : S.Nonempty)
    (hmax : ∀ T : Finset V,
      ksInducedScore t G T ≤ ksInducedScore t G S) :
    ∀ A : Finset (↑S : Set V),
      ksInducedAverageDegree (G.induce (↑S : Set V)) A ≤
        ksInducedAverageDegree G S := by
  intro A
  rw [← ksInducedAverageDegree_image G S A]
  exact ksInducedAverageDegree_le_of_score_maximal G ht hS hmax _
    (ksFinsetImage_subset A)

/-! ## Minimum degree of the maximizer -/

private noncomputable def ksInduceEraseIso [Fintype V]
    (G : SimpleGraph V) (S : Finset V) (v : V) (hv : v ∈ S) :
    G.induce (↑(S.erase v) : Set V) ≃g
      (G.induce (↑S : Set V)).induce
        ({⟨v, hv⟩}ᶜ : Set (↑S : Set V)) where
  toFun x := by
    refine ⟨⟨x, Finset.mem_of_mem_erase x.2⟩, ?_⟩
    have hxv : x.1 ≠ v := (Finset.mem_erase.mp x.2).1
    simpa using hxv
  invFun x := by
    refine ⟨x.1.1, Finset.mem_erase.mpr ⟨?_, x.1.2⟩⟩
    have hxv : x.1 ≠ (⟨v, hv⟩ : (↑S : Set V)) := by
      intro hEq
      apply x.2
      simpa using hEq
    intro h
    exact hxv (Subtype.ext h)
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext <| Subtype.ext rfl
  map_rel_iff' := Iff.rfl

private theorem ks_card_edgeFinset_induce_erase_add_degree [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) (hv : v ∈ S) :
    (G.induce (↑(S.erase v) : Set V)).edgeFinset.card +
        (G.induce (↑S : Set V)).degree ⟨v, hv⟩ =
      (G.induce (↑S : Set V)).edgeFinset.card := by
  classical
  let K : SimpleGraph (↑S : Set V) := G.induce (↑S : Set V)
  let x : (↑S : Set V) := ⟨v, hv⟩
  have hdeg : K.degree x ≤ K.edgeFinset.card := K.degree_le_card_edgeFinset x
  have hcard :
      (G.induce (↑(S.erase v) : Set V)).edgeFinset.card =
        K.edgeFinset.card - K.degree x := by
    calc
      (G.induce (↑(S.erase v) : Set V)).edgeFinset.card =
          (K.induce ({x}ᶜ : Set (↑S : Set V))).edgeFinset.card :=
        (ksInduceEraseIso G S v hv).card_edgeFinset_eq
      _ = (K.deleteIncidenceSet x).edgeFinset.card :=
        K.card_edgeFinset_induce_compl_singleton x
      _ = K.edgeFinset.card - K.degree x :=
        K.card_edgeFinset_deleteIncidenceSet x
  change (G.induce (↑(S.erase v) : Set V)).edgeFinset.card + K.degree x =
    K.edgeFinset.card
  rw [hcard, Nat.sub_add_cancel hdeg]

lemma ksInducedAverageDegree_erase_gt [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} (hS : S.Nonempty) {v : V} (hv : v ∈ S)
    (hpos : 0 < ksInducedAverageDegree G S)
    (hdegree : ((G.induce (↑S : Set V)).degree ⟨v, hv⟩ : ℝ) <
      ksInducedAverageDegree G S / 2) :
    ksInducedAverageDegree G S < ksInducedAverageDegree G (S.erase v) := by
  classical
  let n := S.card
  let m := (G.induce (↑S : Set V)).edgeFinset.card
  let q := (G.induce (↑S : Set V)).degree ⟨v, hv⟩
  have hn : 0 < n := hS.card_pos
  have hn2 : 2 ≤ n := by
    by_contra hn2
    have hn1 : n = 1 := by omega
    have hm : m = 0 := by
      have hbound := (G.induce (↑S : Set V)).card_edgeFinset_le_card_choose_two
      change m ≤ (Fintype.card (↑S : Set V)).choose 2 at hbound
      have hcard : Fintype.card (↑S : Set V) = 1 := by
        simpa [n] using hn1
      rw [hcard] at hbound
      simpa [m] using hbound
    rw [ksInducedAverageDegree,
      ksInducedEdges_eq_card_edgeFinset_induce] at hpos
    change 0 < 2 * (m : ℝ) / (n : ℝ) at hpos
    simp [hm] at hpos
  have hqle : q ≤ m :=
    (G.induce (↑S : Set V)).degree_le_card_edgeFinset ⟨v, hv⟩
  have hedge := ks_card_edgeFinset_induce_erase_add_degree G S v hv
  have herase_edges :
      (G.induce (↑(S.erase v) : Set V)).edgeFinset.card = m - q := by
    change (G.induce (↑(S.erase v) : Set V)).edgeFinset.card + q = m at hedge
    omega
  rw [ksInducedAverageDegree,
    ksInducedEdges_eq_card_edgeFinset_induce,
    ksInducedAverageDegree,
    ksInducedEdges_eq_card_edgeFinset_induce]
  rw [herase_edges, Finset.card_erase_of_mem hv]
  change 2 * (m : ℝ) / n <
    2 * ((m - q : ℕ) : ℝ) / ((n - 1 : ℕ) : ℝ)
  rw [Nat.cast_sub hqle, Nat.cast_sub (by omega : 1 ≤ n)]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn1R : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have havgeq : ksInducedAverageDegree G S / 2 = (m : ℝ) / n := by
    rw [ksInducedAverageDegree,
      ksInducedEdges_eq_card_edgeFinset_induce]
    change 2 * (m : ℝ) / (n : ℝ) / 2 = (m : ℝ) / n
    ring
  rw [havgeq] at hdegree
  have hdegree' : (q : ℝ) * n < m := (lt_div_iff₀ hnR).mp hdegree
  norm_num only [Nat.cast_one] at ⊢
  rw [div_lt_div_iff₀ hnR hn1R]
  push_cast at hdegree' ⊢
  calc
    2 * (m : ℝ) * ((n : ℝ) - 1) =
        2 * m * n - 2 * m := by ring
    _ < 2 * m * n - 2 * (n * q) := by nlinarith [hdegree']
    _ = 2 * ((m : ℝ) - q) * n := by ring

lemma ks_minDegree_of_score_maximal [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : ℝ} (ht : 0 < t) {S : Finset V} (hS : S.Nonempty)
    (hpos : 0 < ksInducedAverageDegree G S)
    (hmax : ∀ T : Finset V,
      ksInducedScore t G T ≤ ksInducedScore t G S) :
    ∀ v : (↑S : Set V),
      ksInducedAverageDegree G S / 2 ≤
        (G.induce (↑S : Set V)).degree v := by
  intro v
  by_contra hdegree
  have hlt : ((G.induce (↑S : Set V)).degree v : ℝ) <
      ksInducedAverageDegree G S / 2 := lt_of_not_ge hdegree
  have hraise := ksInducedAverageDegree_erase_gt G hS v.2 hpos hlt
  have hle := ksInducedAverageDegree_le_of_score_maximal G ht hS hmax
    (S.erase v.1) (Finset.erase_subset _ _)
  exact (not_lt_of_ge hle) hraise

/-! ## The separator inequality -/

/-- Ambient edges whose two endpoints lie in `A`. -/
noncomputable def ksEdgesInside [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (A : Finset V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter fun e ↦ e.toFinset ⊆ A

@[simp] lemma card_ksEdgesInside [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Finset V) :
    (ksEdgesInside G A).card = ksInducedEdges G A := by
  rfl

lemma ks_edgeFinset_subset_inside_union_compl [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    G.edgeFinset ⊆
      ksEdgesInside G (A ∪ externalNeighborhood G A) ∪
        ksEdgesInside G ((Finset.univ : Finset V) \ A) := by
  classical
  intro e he
  cases e using Sym2.inductionOn with
  | _ a b =>
      have hab : G.Adj a b := by
        simpa only [SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] using he
      by_cases ha : a ∈ A
      · have hbX : b ∈ A ∪ externalNeighborhood G A := by
          by_cases hb : b ∈ A
          · exact Finset.mem_union_left _ hb
          · exact Finset.mem_union_right _ <|
              (mem_externalNeighborhood G A b).2 ⟨hb, a, ha, hab⟩
        have haX : a ∈ A ∪ externalNeighborhood G A :=
          Finset.mem_union_left _ ha
        apply Finset.mem_union_left
        refine Finset.mem_filter.2 ⟨he, ?_⟩
        rw [Sym2.toFinset_mk_eq]
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact haX
        · exact hbX
      · by_cases hb : b ∈ A
        · have haX : a ∈ A ∪ externalNeighborhood G A := by
            exact Finset.mem_union_right _ <|
              (mem_externalNeighborhood G A a).2 ⟨ha, b, hb, hab.symm⟩
          have hbX : b ∈ A ∪ externalNeighborhood G A :=
            Finset.mem_union_left _ hb
          apply Finset.mem_union_left
          refine Finset.mem_filter.2 ⟨he, ?_⟩
          rw [Sym2.toFinset_mk_eq]
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact haX
          · exact hbX
        · apply Finset.mem_union_right
          refine Finset.mem_filter.2 ⟨he, ?_⟩
          rw [Sym2.toFinset_mk_eq]
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · simp [ha]
          · simp [hb]

lemma ks_card_edgeFinset_le_inside_union_compl [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    G.edgeFinset.card ≤
      ksInducedEdges G (A ∪ externalNeighborhood G A) +
        ksInducedEdges G ((Finset.univ : Finset V) \ A) := by
  classical
  calc
    G.edgeFinset.card ≤
        (ksEdgesInside G (A ∪ externalNeighborhood G A) ∪
          ksEdgesInside G ((Finset.univ : Finset V) \ A)).card :=
      Finset.card_le_card (ks_edgeFinset_subset_inside_union_compl G A)
    _ ≤ (ksEdgesInside G (A ∪ externalNeighborhood G A)).card +
          (ksEdgesInside G ((Finset.univ : Finset V) \ A)).card :=
      Finset.card_union_le _ _
    _ = _ := by
      rw [card_ksEdgesInside, card_ksEdgesInside]

/-- If every induced subgraph of `G` has average degree at most `d`, then the
union of a set with its external neighborhood spans enough edges to account
for half of `d` times the size of the set. -/
lemma ks_separator_density [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d : ℝ} (hd : 0 ≤ d)
    (hbase : d ≤ averageDegree G)
    (hmax : ∀ T : Finset V, ksInducedAverageDegree G T ≤ d)
    (A : Finset V) :
    d * A.card ≤
      2 * (ksInducedEdges G (A ∪ externalNeighborhood G A) : ℝ) := by
  classical
  let C : Finset V := (Finset.univ : Finset V) \ A
  let X : Finset V := A ∪ externalNeighborhood G A
  have hcover := ks_card_edgeFinset_le_inside_union_compl G A
  change G.edgeFinset.card ≤ ksInducedEdges G X + ksInducedEdges G C at hcover
  have hCavg := hmax C
  have hCedges : 2 * (ksInducedEdges G C : ℝ) ≤ d * C.card := by
    by_cases hC : C = ∅
    · simp [hC]
    · have hCcard : (0 : ℝ) < C.card := by
        exact_mod_cast (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hC))
      rw [ksInducedAverageDegree] at hCavg
      norm_num at hCavg ⊢
      exact (div_le_iff₀ hCcard).mp hCavg
  have htotal : d * Fintype.card V ≤
      2 * (G.edgeFinset.card : ℝ) := by
    by_cases hV : Fintype.card V = 0
    · simp [hV]
    · have hVR : (0 : ℝ) < Fintype.card V := by exact_mod_cast Nat.pos_of_ne_zero hV
      rw [averageDegree] at hbase
      norm_num at hbase ⊢
      exact (le_div_iff₀ hVR).mp hbase
  have hCcard : A.card + C.card = Fintype.card V := by
    dsimp [C]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ A)]
    simp only [Finset.card_univ]
    exact Nat.add_sub_of_le (Finset.card_le_card (Finset.subset_univ A))
  have hCcardR : (A.card : ℝ) + C.card = Fintype.card V := by
    exact_mod_cast hCcard
  have hcoverR : 2 * (G.edgeFinset.card : ℝ) ≤
      2 * (ksInducedEdges G X : ℝ) +
        2 * (ksInducedEdges G C : ℝ) := by
    have hcoverNat := Nat.mul_le_mul_left 2 hcover
    rw [Nat.mul_add] at hcoverNat
    exact_mod_cast hcoverNat
  have hdcard : d * A.card + d * C.card = d * Fintype.card V := by
    rw [← mul_add, hCcardR]
  nlinarith

/-! ## Potential loss at a sparse scale -/

lemma ks_score_forces_density_loss {t x n a d : ℝ}
    (ht : 0 < t) (htx : t ≤ x) (hxn : 3 * x ≤ 2 * n)
    (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hscore : a * (1 + ksGamma t x) ≤
      d * (1 + ksGamma t n)) :
    a ≤ d * (1 - 64 * ksRate t x) := by
  have hx : 0 < x := ht.trans_le htx
  have hx15 : 0 < 3 * x / 2 := by positivity
  have h15n : 3 * x / 2 ≤ n := by linarith
  have hgn : ksGamma t n ≤ ksGamma t (3 * x / 2) :=
    ksGamma_anti ht hx15 h15n
  have hg0 := ksGamma_nonneg ht hx
  have hg1 := ksGamma_le_one ht hx
  have hr0 := ksRate_nonneg ht (le_of_lt hx)
  have hgap := ksGamma_gap ht htx
  have hscore' : a * (1 + ksGamma t x) ≤
      d * (1 + ksGamma t (3 * x / 2)) := by
    exact hscore.trans (mul_le_mul_of_nonneg_left (by linarith) hd)
  have hprod : 64 * ksRate t x * ksGamma t x ≤ 64 * ksRate t x := by
    exact mul_le_of_le_one_right (by positivity) hg1
  have hcoef : 1 + ksGamma t (3 * x / 2) ≤
      (1 - 64 * ksRate t x) * (1 + ksGamma t x) := by
    nlinarith [hgap, hprod]
  by_contra h
  have halt : d * (1 - 64 * ksRate t x) < a := lt_of_not_ge h
  have hmul : d * (1 - 64 * ksRate t x) * (1 + ksGamma t x) <
      a * (1 + ksGamma t x) :=
    mul_lt_mul_of_pos_right halt (by linarith)
  have hright : d * (1 + ksGamma t (3 * x / 2)) ≤
      d * ((1 - 64 * ksRate t x) * (1 + ksGamma t x)) :=
    mul_le_mul_of_nonneg_left hcoef hd
  have := hscore'.trans hright
  nlinarith

lemma ks_induced_density_loss_of_maximal [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : ℝ} (ht : 0 < t) {S : Finset V}
    (hmax : ∀ T : Finset V,
      ksInducedScore t G T ≤ ksInducedScore t G S)
    (T : Finset V) (htT : t ≤ T.card)
    (hTS : (3 : ℝ) * T.card ≤ 2 * S.card) :
    ksInducedAverageDegree G T ≤
      ksInducedAverageDegree G S * (1 - 64 * ksRate t T.card) := by
  apply ks_score_forces_density_loss ht htT hTS
  · exact ksInducedAverageDegree_nonneg G T
  · exact ksInducedAverageDegree_nonneg G S
  · exact hmax T

/-! ## Expansion of the maximizer -/

lemma ks_expands_of_score_maximal [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : ℝ} (ht : 0 < t) {S : Finset V} (hS : S.Nonempty)
    (hpos : 0 < ksInducedAverageDegree G S)
    (hmax : ∀ T : Finset V,
      ksInducedScore t G T ≤ ksInducedScore t G S) :
    IsKSExpander (G.induce (↑S : Set V)) t := by
  classical
  let : DecidableEq (↑S : Set V) := Classical.decEq _
  let H : SimpleGraph (↑S : Set V) := G.induce (↑S : Set V)
  have hhered : ∀ T : Finset (↑S : Set V),
      ksInducedAverageDegree H T ≤ ksInducedAverageDegree G S :=
    ksInducedAverageDegree_le_in_maximizer G ht hS hmax
  intro A htA hAS
  let B : Finset (↑S : Set V) := externalNeighborhood H A
  let X : Finset (↑S : Set V) := A ∪ B
  have hAB : Disjoint A B := (externalNeighborhood_disjoint H A).symm
  have hXcardNat : X.card = A.card + B.card := by
    dsimp [X]
    exact Finset.card_union_of_disjoint hAB
  have hXcard : (X.card : ℝ) = A.card + B.card := by exact_mod_cast hXcardNat
  have hAX : A ⊆ X := Finset.subset_union_left
  have htX : t ≤ (X.card : ℝ) :=
    htA.trans (by exact_mod_cast Finset.card_le_card hAX)
  have hApos : 0 < (A.card : ℝ) := ht.trans_le htA
  have hXpos : 0 < (X.card : ℝ) := hApos.trans_le <| by
    exact_mod_cast Finset.card_le_card hAX
  have hbase : ksInducedAverageDegree G S ≤ averageDegree H := by
    rw [averageDegree, ksInducedAverageDegree,
      ksInducedEdges_eq_card_edgeFinset_induce]
    simp [H, Fintype.card_coe]
  have hsep : ksInducedAverageDegree G S * A.card ≤
      2 * (ksInducedEdges H X : ℝ) := by
    simpa [X] using ks_separator_density H hpos.le hbase hhered A
  have hsepAvg : ksInducedAverageDegree G S * A.card ≤
      ksInducedAverageDegree H X * X.card := by
    have heq : ksInducedAverageDegree H X * (X.card : ℝ) =
        2 * (ksInducedEdges H X : ℝ) := by
      rw [ksInducedAverageDegree]
      push_cast
      exact div_mul_cancel₀ _ hXpos.ne'
    rw [heq]
    exact hsep
  by_cases hlarge : (4 : ℝ) * A.card ≤ 3 * X.card
  · have hB : ksRate t A.card * A.card ≤ B.card := by
      have hr := ksRate_le_one_third ht htA
      calc
        ksRate t A.card * A.card ≤ (1 / 3 : ℝ) * A.card :=
          mul_le_mul_of_nonneg_right hr (by positivity)
        _ ≤ B.card := by
          rw [hXcard] at hlarge
          linarith
    simpa [B] using hB
  · have hXsmall : (3 : ℝ) * X.card ≤ 2 * S.card := by
      have hAlarge : (2 : ℝ) * A.card ≤ S.card := by
        have hAlargeNat : 2 * A.card ≤ S.card := by
          simpa [H, Fintype.card_coe] using hAS
        exact_mod_cast hAlargeNat
      have hxlt : (3 : ℝ) * X.card < 4 * A.card := lt_of_not_ge hlarge
      linarith
    have hlossAmbient :=
      ks_induced_density_loss_of_maximal G ht hmax (ksFinsetImage X)
        (by simpa using htX) (by simpa using hXsmall)
    have hloss : ksInducedAverageDegree H X ≤
        ksInducedAverageDegree G S * (1 - 64 * ksRate t X.card) := by
      rw [← ksInducedAverageDegree_image G S X]
      simpa using hlossAmbient
    have hXle2A : (X.card : ℝ) ≤ 2 * A.card := by
      have hxlt : (3 : ℝ) * X.card < 4 * A.card := lt_of_not_ge hlarge
      nlinarith
    have hranti : ksRate t (2 * A.card) ≤ ksRate t X.card :=
      ksRate_anti ht htX hXle2A
    have hrdouble := ksRate_double ht htA
    have hrA : ksRate t A.card ≤ 4 * ksRate t X.card :=
      hrdouble.trans (mul_le_mul_of_nonneg_left hranti (by norm_num))
    have hrX0 := ksRate_nonneg ht (by positivity : (0 : ℝ) ≤ X.card)
    have hAXR : (A.card : ℝ) ≤ X.card := by
      exact_mod_cast Finset.card_le_card hAX
    have hcombined : ksInducedAverageDegree G S * A.card ≤
        ksInducedAverageDegree G S *
          (1 - 64 * ksRate t X.card) * X.card :=
      hsepAvg.trans <| mul_le_mul_of_nonneg_right hloss (by positivity)
    have hB : ksRate t A.card * A.card ≤ B.card := by
      let rX : ℝ := ksRate t X.card
      have hcancel : (A.card : ℝ) ≤ (1 - 64 * rX) * X.card := by
        apply le_of_mul_le_mul_left _ hpos
        simpa [rX, mul_assoc] using hcombined
      have hmass : 64 * rX * X.card ≤ B.card := by
        rw [hXcard] at hcancel
        nlinarith
      calc
        ksRate t A.card * A.card ≤ (4 * rX) * A.card :=
          mul_le_mul_of_nonneg_right (by simpa [rX] using hrA) (by positivity)
        _ ≤ (4 * rX) * X.card :=
          mul_le_mul_of_nonneg_left hAXR (by simpa [rX] using hrX0)
        _ ≤ 64 * rX * X.card := by
          have : 0 ≤ rX * X.card := mul_nonneg (by simpa [rX] using hrX0) (by positivity)
          nlinarith
        _ ≤ B.card := hmass
    simpa [B] using hB

/-- Finite Komlós--Szemerédi extraction in the base-two normalization used
inside this proof.  The output is induced, retains half the average degree,
and has minimum degree at least half of its own average degree. -/
theorem exists_komlos_szemeredi_expander [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : ℝ} (ht : 0 < t) (hGpos : 0 < averageDegree G) :
    ∃ S : Finset V, S.Nonempty ∧
      IsKSExpander (G.induce (↑S : Set V)) t ∧
      averageDegree G / 2 ≤ ksInducedAverageDegree G S ∧
      ∀ v : (↑S : Set V),
        ksInducedAverageDegree G S / 2 ≤
          (G.induce (↑S : Set V)).degree v := by
  classical
  obtain ⟨S, hmax⟩ := exists_ksInducedScore_maximizer G t
  obtain ⟨hS, hretain⟩ :=
    ks_maximizer_nonempty_and_retains_average G ht hGpos hmax
  have hpos : 0 < ksInducedAverageDegree G S :=
    lt_of_lt_of_le (half_pos hGpos) hretain
  refine ⟨S, hS, ks_expands_of_score_maximal G ht hS hpos hmax,
    hretain, ?_⟩
  exact ks_minDegree_of_score_maximal G ht hS hpos hmax

/-! ## Conversion to the Liu--Montgomery normalization -/

/-- The base-two profile proved above dominates the Liu--Montgomery profile
with the explicit universal constant `1 / 1024`. -/
lemma expansionEpsilon_le_ksRate {k : ℝ} (hk : 0 < k) {x : ℕ}
    (hx : k / 2 ≤ (x : ℝ)) :
    expansionEpsilon (1 / 1024) k x ≤ ksRate (k / 2) x := by
  have hk2 : 0 < k / 2 := by positivity
  have hxpos : 0 < (x : ℝ) := hk2.trans_le hx
  have hbranch : k / 5 ≤ (x : ℝ) := by nlinarith
  have hksbranch : ¬ (x : ℝ) < k / 2 := not_lt_of_ge hx
  let A : ℝ := Real.log (8 * (x : ℝ) / k)
  let B : ℝ := Real.log (15 * (x : ℝ) / k)
  let q : ℝ := Real.log 2
  let L : ℝ := Real.log (3 / 2)
  have hargA : (1 : ℝ) < 8 * (x : ℝ) / k := by
    rw [lt_div_iff₀ hk]
    nlinarith
  have hargB : (1 : ℝ) < 15 * (x : ℝ) / k := by
    rw [lt_div_iff₀ hk]
    nlinarith
  have hA : 0 < A := by exact Real.log_pos hargA
  have hB : 0 < B := by exact Real.log_pos hargB
  have hAB : A ≤ B := by
    dsimp [A, B]
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff_of_pos_right hk]
    nlinarith
  have hABsq : A ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ hA.le hB.le).2 hAB
  have hq : (1 : ℝ) / 2 ≤ q := by
    dsimp [q]
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hL : (1 : ℝ) / 3 ≤ L := by
    dsimp [L]
    have h := Real.one_sub_inv_le_log_of_pos
      (by norm_num : (0 : ℝ) < 3 / 2)
    norm_num at h ⊢
    exact h
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hcoeff : (1 : ℝ) / 1024 ≤ L * q / 128 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 128)]
    nlinarith [mul_le_mul hL hq (by norm_num : (0 : ℝ) ≤ 1 / 2) hLpos.le]
  rw [expansionEpsilon_of_le hbranch]
  simp only [ksRate, hksbranch, if_false]
  have harg : 4 * (x : ℝ) / (k / 2) = 8 * (x : ℝ) / k := by
    field_simp [hk.ne']
    ring
  rw [harg]
  have hrate : Real.logb 2 (3 / 2) /
        (128 * Real.logb 2 (8 * (x : ℝ) / k) ^ 2) =
      L * q / (128 * A ^ 2) := by
    dsimp [A, q, L]
    rw [← Real.log_div_log, ← Real.log_div_log]
    field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1), hA.ne']
  rw [hrate]
  change (1 : ℝ) / 1024 / B ^ 2 ≤ L * q / (128 * A ^ 2)
  calc
    (1 : ℝ) / 1024 / B ^ 2 ≤ (1 : ℝ) / 1024 / A ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hA) hABsq
    _ ≤ (L * q / 128) / A ^ 2 :=
      div_le_div_of_nonneg_right hcoeff (sq_nonneg A)
    _ = L * q / (128 * A ^ 2) := by ring

lemma IsKSExpander.isLMExpander [Fintype V] {G : SimpleGraph V}
    {k : ℝ} (hk : 0 < k)
    (h : IsKSExpander G (k / 2)) :
    IsLMExpander G (1 / 1024) k := by
  intro S hlower hupper
  have hupperR : (2 : ℝ) * S.card ≤ Fintype.card V := by linarith
  have hupper' : 2 * S.card ≤ Fintype.card V := by exact_mod_cast hupperR
  have hks := h S hlower hupper'
  exact (mul_le_mul_of_nonneg_right (expansionEpsilon_le_ksRate hk hlower)
    (Nat.cast_nonneg _)).trans hks

/-- Extraction stated directly with the Liu--Montgomery expansion predicate. -/
theorem exists_liu_montgomery_expander [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℝ} (hk : 0 < k) (hGpos : 0 < averageDegree G) :
    ∃ S : Finset V, S.Nonempty ∧
      IsLMExpander (G.induce (↑S : Set V)) (1 / 1024) k ∧
      averageDegree G / 2 ≤ ksInducedAverageDegree G S ∧
      ∀ v : (↑S : Set V),
        ksInducedAverageDegree G S / 2 ≤
          (G.induce (↑S : Set V)).degree v := by
  obtain ⟨S, hS, hexp, hretain, hmin⟩ :=
    exists_komlos_szemeredi_expander G (half_pos hk) hGpos
  exact ⟨S, hS, hexp.isLMExpander hk, hretain, hmin⟩

/-- Liu--Montgomery Corollary 2.5 in the finite, explicit-constant form used
downstream.  Average degree at least `8*d` yields a bipartite
`(1/1024,k)`-expander whose minimum degree is at least `d`. -/
theorem exists_bipartite_liu_montgomery_expander [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : 0 < d) {k : ℝ} (hk : 0 < k)
    (havg : AvgDegreeAtLeast G (8 * d)) :
    ∃ (H : SimpleGraph V) (S : Finset V),
      H ≤ G ∧ H.IsBipartite ∧ S.Nonempty ∧
      IsLMExpander (H.induce (↑S : Set V)) (1 / 1024) k ∧
      (2 * d : ℝ) ≤ ksInducedAverageDegree H S ∧
      ∀ v : (↑S : Set V),
        (d : ℝ) ≤ (H.induce (↑S : Set V)).degree v := by
  classical
  obtain ⟨H, hHG, hbip, hhalf⟩ := exists_bipartite_subgraph_half G
  have hcard : 0 < Fintype.card V := Fintype.card_pos
  let q : ℕ := d * Fintype.card V
  have hGedges : 8 * q ≤ 2 * G.edgeFinset.card := by
    rw [AvgDegreeAtLeast, G.sum_degrees_eq_twice_card_edges] at havg
    simpa only [q, Nat.mul_assoc] using havg
  have hhalf' : 2 * G.edgeFinset.card ≤ 4 * H.edgeFinset.card := by
    calc
      2 * G.edgeFinset.card ≤ 2 * (2 * H.edgeFinset.card) :=
        Nat.mul_le_mul_left 2 hhalf
      _ = 4 * H.edgeFinset.card := by ring
  have hHedges : 4 * q ≤ 2 * H.edgeFinset.card := by omega
  have hHreal : ((4 * d : ℕ) : ℝ) ≤ averageDegree H :=
    (avgDegreeAtLeast_iff H hcard).mp <| by
      rw [AvgDegreeAtLeast, H.sum_degrees_eq_twice_card_edges]
      simpa only [q, Nat.mul_assoc] using hHedges
  have hHpos : 0 < averageDegree H :=
    lt_of_lt_of_le (by positivity) hHreal
  obtain ⟨S, hS, hexp, hretain, hmin⟩ :=
    exists_liu_montgomery_expander H hk hHpos
  have hSaverage : (2 * d : ℝ) ≤ ksInducedAverageDegree H S := by
    push_cast at hHreal ⊢
    nlinarith
  refine ⟨H, S, hHG, hbip, hS, hexp, hSaverage, ?_⟩
  · intro v
    have hv := hmin v
    nlinarith

end

end Erdos63
