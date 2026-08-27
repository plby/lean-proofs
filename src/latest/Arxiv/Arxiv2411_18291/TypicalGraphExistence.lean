import Arxiv.Arxiv2411_18291.RandomTypicality
import Arxiv.Arxiv2411_18291.TypicalityDensity

/-!
# Existence of typical graphs from an explicit probability bound

The failure bound includes both the edge count and every common-neighborhood
test. The resulting existence theorem has only numerical hypotheses; it does
not assume a random-typicality or graph-existence lemma.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

/-- The sum of the edge-count and common-neighborhood failure bounds.
Here `r` is the face size and the hypergraph has uniformity `r + 1`. -/
def typicalFailureBound (n r h : ℕ) (p c : ℝ) : ℝ :=
  2 * Real.exp (-(p * n.choose (r + 1) * c ^ 2 / (2 * (1 + 2 * c)))) +
    ((∑ a ∈ range (h + 1), (n.choose r).choose a : ℕ) : ℝ) *
      (2 * Real.exp (-(((n - h * r : ℕ) : ℝ) * p ^ h * c ^ 2 / (2 * (1 + 2 * c)))))

variable {V : Type*} [Fintype V] [DecidableEq V] {r h : ℕ}

/-- Simultaneous density and typicality control for a random graph. -/
theorem typical_failure_probability (p : unitInterval) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hn : r + 1 ≤ Fintype.card V)
    (hsize : (h * r : ℝ) ≤ c * Fintype.card V) (hsmall : c * h * 2 ^ h ≤ 1 / 2) :
    (BernoulliSubset.probability (Block V (r + 1)) p).real
      {ω | ¬ (|density (sampleGraph ω) - (p : ℝ)| ≤ c * p ∧
        IsTypical (sampleGraph ω) ((4 + 2 * h * 2 ^ h) * c) h)} ≤
      typicalFailureBound (Fintype.card V) r h p c := by
  let E := {ω : BernoulliSubset.Sample (Block V (r + 1)) |
    |((sampleGraph ω).card : ℝ) - (p : ℝ) * (Fintype.card V).choose (r + 1)| >
      c * ((p : ℝ) * (Fintype.card V).choose (r + 1))}
  let B := {ω : BernoulliSubset.Sample (Block V (r + 1)) |
    ¬ IsTypicalAt (sampleGraph ω) (p : ℝ) (2 * c) h}
  have hsub : {ω | ¬ (|density (sampleGraph ω) - (p : ℝ)| ≤ c * p ∧
      IsTypical (sampleGraph ω) ((4 + 2 * h * 2 ^ h) * c) h)} ⊆ E ∪ B := by
    intro ω hω
    by_cases hE : ω ∈ E
    · exact Or.inl hE
    · right
      change ¬ IsTypicalAt (sampleGraph ω) (p : ℝ) (2 * c) h
      intro hT
      have he : |((sampleGraph ω).card : ℝ) - (p : ℝ) * (Fintype.card V).choose (r + 1)| ≤
          c * ((p : ℝ) * (Fintype.card V).choose (r + 1)) := le_of_not_gt hE
      have hd := density_error_of_card_error (sampleGraph ω) hn he
      exact hω ⟨hd, hT.to_isTypical p.property.1 hc hc1 hd hsmall⟩
  calc
    _ ≤ (BernoulliSubset.probability (Block V (r + 1)) p).real (E ∪ B) := measureReal_mono hsub
    _ ≤ (BernoulliSubset.probability (Block V (r + 1)) p).real E +
        (BernoulliSubset.probability (Block V (r + 1)) p).real B := measureReal_union_le E B
    _ ≤ _ := add_le_add (sampleGraph_card_concentration p hc)
      (typicalAt_failure_probability p hc hsize)

/-- A finite existence criterion with explicit numerical assumptions. -/
theorem exists_typicalGraph (p : unitInterval) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hn : r + 1 ≤ Fintype.card V)
    (hsize : (h * r : ℝ) ≤ c * Fintype.card V) (hsmall : c * h * 2 ^ h ≤ 1 / 2)
    (hfailure : typicalFailureBound (Fintype.card V) r h p c < 1) :
    ∃ G : Hypergraph V (r + 1), |density G - (p : ℝ)| ≤ c * p ∧
      IsTypical G ((4 + 2 * h * 2 ^ h) * c) h := by
  have hb := typical_failure_probability p hc hc1 hn hsize hsmall
  by_contra hnone
  have hbad : {ω : BernoulliSubset.Sample (Block V (r + 1)) |
      ¬ (|density (sampleGraph ω) - (p : ℝ)| ≤ c * p ∧
        IsTypical (sampleGraph ω) ((4 + 2 * h * 2 ^ h) * c) h)} = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro ω hω
    exact hnone ⟨sampleGraph ω, hω⟩
  rw [hbad, probReal_univ] at hb
  exact (not_lt_of_ge hb) hfailure

end Arxiv2411_18291
