import Arxiv.Arxiv2411_18291.BernoulliPatterns
import Arxiv.Arxiv2411_18291.IsolatedVertexTypicality
import Arxiv.Arxiv2411_18291.RandomHypergraph

/-! # A lower bound for failure of random-graph typicality -/

open MeasureTheory Finset

noncomputable section

namespace Arxiv2411_18291

theorem typicality_failure_probability_lower {V : Type*} [Fintype V] [DecidableEq V]
    (p : unitInterval) (v : V) (e : Block V 2) (hve : v ∉ e.val)
    {c : ℝ} (hc : c < 1) {h : ℕ} (hh : 1 ≤ h) :
    (p : ℝ) * (1 - p) ^ (Fintype.card V - 1) ≤
      (BernoulliSubset.probability (Block V 2) p).real
        {ω | ¬IsTypical (sampleGraph ω) c h} := by
  let E : Set (BernoulliSubset.Sample (Block V 2)) :=
    {ω | (∀ f ∈ ({e} : Finset (Block V 2)), ω f) ∧ ∀ f ∈ pairStar v, ¬ω f}
  have hdis : Disjoint ({e} : Finset (Block V 2)) (pairStar v) := by
    apply disjoint_left.mpr
    intro f hf hs
    have hfe : f = e := mem_singleton.mp hf
    subst f
    exact hve ((mem_pairStar v e).mp hs)
  have hprob : (BernoulliSubset.probability (Block V 2) p).real E =
      (p : ℝ) * (1 - p) ^ (Fintype.card V - 1) := by
    simpa only [E, card_singleton, pow_one, card_pairStar] using
      BernoulliSubset.probabilityReal_present_absent p {e} (pairStar v) hdis
  have hsub : E ⊆ {ω | ¬IsTypical (sampleGraph ω) c h} := by
    intro ω hω
    apply not_typical_of_isolated_vertex (sampleGraph ω)
      ⟨e, (mem_sampleGraph ω e).mpr (hω.1 e (mem_singleton_self e))⟩ v _ hc hh
    intro f hf hv
    exact hω.2 f ((mem_pairStar v f).mpr hv) ((mem_sampleGraph ω f).mp hf)
  rw [← hprob]
  exact measureReal_mono hsub

end Arxiv2411_18291
