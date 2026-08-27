import Arxiv.Arxiv2411_18291.TypicalityFailureLower
import Arxiv.Arxiv2411_18291.TypicalityCounterexampleNumerics

/-!
# The printed definition of high probability is too strong

For every `n ≥ 1000000`, use ordinary graphs, one tested neighborhood,
and edge probability `1/100`. The event that vertex zero is isolated while
the edge {1,2} is present violates typicality and has probability greater
than `exp(-n/10)`. These parameters meet every hypothesis of Lemma 5.3.
-/

open MeasureTheory Finset

noncomputable section

namespace Arxiv2411_18291.PrintedWhpCounterexample

def edgeProbability : unitInterval := ⟨1 / 100, by norm_num⟩

theorem failure_probability_gt (n : ℕ) (hn : 1000000 ≤ n) :
    Real.exp (-(n : ℝ) / 10) <
      (BernoulliSubset.probability (Block (Fin n) 2) edgeProbability).real
        {ω | ¬IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) 1} := by
  let v : Fin n := ⟨0, by omega⟩
  let a : Fin n := ⟨1, by omega⟩
  let b : Fin n := ⟨2, by omega⟩
  have hab : a ≠ b := by
    intro he
    have hh := congrArg Fin.val he
    norm_num [a, b] at hh
  let e : Block (Fin n) 2 := ⟨{a, b}, by simp [hab]⟩
  have hve : v ∉ e.val := by norm_num [e, v, a, b]
  have hfailure := typicality_failure_probability_lower edgeProbability v e hve
    (typicality_counterexample_scales n hn).2.2 (by norm_num : 1 ≤ 1)
  have hbound : (1 / 100 : ℝ) * (99 / 100 : ℝ) ^ (n - 1) ≤
      (BernoulliSubset.probability (Block (Fin n) 2) edgeProbability).real
        {ω | ¬IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) 1} := by
    simpa only [edgeProbability, Fintype.card_fin,
      show (1 - (1 / 100 : ℝ)) = 99 / 100 by norm_num] using hfailure
  exact (isolated_vertex_probability_gt_exp n (by omega)).trans_le hbound

theorem success_probability_lt (n : ℕ) (hn : 1000000 ≤ n) :
    (BernoulliSubset.probability (Block (Fin n) 2) edgeProbability).real
        {ω | IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) 1} <
      1 - Real.exp (-(n : ℝ) / 10) := by
  have hm : MeasurableSet {ω : BernoulliSubset.Sample (Block (Fin n) 2) |
      IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) 1} :=
    (Set.toFinite _).measurableSet
  have he := measureReal_compl (μ := BernoulliSubset.probability (Block (Fin n) 2)
    edgeProbability) hm
  simp only [probReal_univ, Set.compl_ofPred] at he
  have hf := failure_probability_gt n hn
  rw [he] at hf
  linarith only [hf]

/-- All source hypotheses hold, but even the opposite strict probability bound holds. -/
theorem printed_typicality_whp_counterexample (n : ℕ) (hn : 1000000 ≤ n) :
    2 ^ (9 * 2 * 1) < n ∧ (n : ℝ) ^ (-(1 / (2 * 1 : ℝ))) < edgeProbability ∧
      (BernoulliSubset.probability (Block (Fin n) 2) edgeProbability).real
          {ω | IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) 1} <
        1 - Real.exp (-(n : ℝ) / 10) := by
  obtain ⟨hsize, hp, _⟩ := typicality_counterexample_scales n hn
  exact ⟨hsize, by simpa only [edgeProbability, mul_one] using hp,
    success_probability_lt n hn⟩

end Arxiv2411_18291.PrintedWhpCounterexample
