import Arxiv.Arxiv2411_18291.RandomHypergraph

/-!
# Simultaneous common-neighborhood estimates

This module keeps an explicit failure probability instead of using the paper's
`whp` shorthand. It also accounts for the faces excluded from their own common
neighborhood, before centering the count at `n * p ^ |A|`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

theorem abs_sub_reference_le {x n b p c : ℝ}
    (hb : 0 ≤ b) (hp : 0 ≤ p) (hc : 0 ≤ c) (hsmall : b ≤ c * n)
    (hx : |x - (n - b) * p| ≤ c * ((n - b) * p)) :
    |x - n * p| ≤ (2 * c) * (n * p) := by
  have ht := abs_sub_le x ((n - b) * p) (n * p)
  have he : |(n - b) * p - n * p| = b * p := by
    rw [show (n - b) * p - n * p = -(b * p) by ring, abs_neg,
      abs_of_nonneg (mul_nonneg hb hp)]
  rw [he] at ht
  have hbp := mul_le_mul_of_nonneg_right hsmall hp
  have hcbp := mul_nonneg hc (mul_nonneg hb hp)
  nlinarith

variable {V : Type*} [Fintype V] [DecidableEq V] {r h : ℕ}

/-- All families of at most `h` faces, grouped by cardinality. -/
def faceFamilies (V : Type*) [Fintype V] [DecidableEq V] (r h : ℕ) :
    Finset (Finset (Block V r)) :=
  (range (h + 1)).biUnion fun a => (univ : Finset (Block V r)).powersetCard a

@[simp] theorem mem_faceFamilies (A : Finset (Block V r)) :
    A ∈ faceFamilies V r h ↔ A.card ≤ h := by
  simp only [faceFamilies, mem_biUnion, mem_range, mem_powersetCard, subset_univ, true_and]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact Nat.le_of_lt_succ ha
  · intro hA
    exact ⟨A.card, Nat.lt_succ_of_le hA, rfl⟩

theorem card_faceFamilies :
    (faceFamilies V r h).card =
      ∑ a ∈ range (h + 1), ((Fintype.card V).choose r).choose a := by
  rw [faceFamilies, card_biUnion]
  · simp [Fintype.card_finset_len]
  · intro a _ b _ hab
    apply disjoint_left.mpr
    intro A ha hb
    exact hab ((mem_powersetCard.mp ha).2.symm.trans (mem_powersetCard.mp hb).2)

/-- Move from the exact expectation to `n * p ^ |A|`. -/
theorem commonNeighbors_reference_concentration (p : unitInterval) {c : ℝ} (hc : 0 ≤ c)
    (A : Finset (Block V r))
    (hsmall : ((faceVertices A).card : ℝ) ≤ c * Fintype.card V) :
    let μ := ((Fintype.card V - (faceVertices A).card : ℕ) : ℝ) * (p : ℝ) ^ A.card
    (BernoulliSubset.probability (Block V (r + 1)) p).real
      {ω | |((commonNeighbors (sampleGraph ω) A).card : ℝ) -
        Fintype.card V * (p : ℝ) ^ A.card| > (2 * c) *
          (Fintype.card V * (p : ℝ) ^ A.card)} ≤
      2 * Real.exp (-(μ * c ^ 2 / (2 * (1 + 2 * c)))) := by
  dsimp only
  apply le_trans (measureReal_mono (show
    {ω | |((commonNeighbors (sampleGraph ω) A).card : ℝ) -
      Fintype.card V * (p : ℝ) ^ A.card| > (2 * c) *
        (Fintype.card V * (p : ℝ) ^ A.card)} ⊆
    {ω | |((commonNeighbors (sampleGraph ω) A).card : ℝ) -
      ((Fintype.card V - (faceVertices A).card : ℕ) : ℝ) * (p : ℝ) ^ A.card| >
        c * (((Fintype.card V - (faceVertices A).card : ℕ) : ℝ) * (p : ℝ) ^ A.card)} from ?_))
    (commonNeighbors_concentration p A hc)
  intro ω hω
  change c * (((Fintype.card V - (faceVertices A).card : ℕ) : ℝ) * (p : ℝ) ^ A.card) <
    |((commonNeighbors (sampleGraph ω) A).card : ℝ) -
      ((Fintype.card V - (faceVertices A).card : ℕ) : ℝ) * (p : ℝ) ^ A.card|
  by_contra hn
  have hx := le_of_not_gt hn
  rw [Nat.cast_sub (card_le_univ (faceVertices A))] at hx
  have hb := abs_sub_reference_le (Nat.cast_nonneg _) (pow_nonneg p.property.1 _)
    hc hsmall hx
  exact (not_lt_of_ge hb) hω

/-- A uniform lower bound for the means of all tested families of faces. -/
theorem commonMean_lower (p : unitInterval) (A : Finset (Block V r)) (hA : A.card ≤ h) :
    ((Fintype.card V - h * r : ℕ) : ℝ) * (p : ℝ) ^ h ≤
      ((Fintype.card V - (faceVertices A).card : ℕ) : ℝ) * (p : ℝ) ^ A.card := by
  have hb : (faceVertices A).card ≤ h * r :=
    (card_faceVertices_le A).trans (Nat.mul_le_mul_right r hA)
  apply mul_le_mul
  · exact_mod_cast Nat.sub_le_sub_left hb (Fintype.card V)
  · exact pow_le_pow_of_le_one p.property.1 p.property.2 hA
  · exact pow_nonneg p.property.1 _
  · positivity

/-- An explicit union bound over every tested common neighborhood. -/
theorem typicalAt_failure_probability (p : unitInterval) {c : ℝ} (hc : 0 ≤ c)
    (hsmall : (h * r : ℝ) ≤ c * Fintype.card V) :
    let m := ((Fintype.card V - h * r : ℕ) : ℝ) * (p : ℝ) ^ h
    (BernoulliSubset.probability (Block V (r + 1)) p).real
      {ω | ¬ IsTypicalAt (sampleGraph ω) (p : ℝ) (2 * c) h} ≤
      ((∑ a ∈ range (h + 1), ((Fintype.card V).choose r).choose a : ℕ) : ℝ) *
        (2 * Real.exp (-(m * c ^ 2 / (2 * (1 + 2 * c))))) := by
  dsimp only
  let B (A : Finset (Block V r)) :=
    {ω : BernoulliSubset.Sample (Block V (r + 1)) |
      |((commonNeighbors (sampleGraph ω) A).card : ℝ) - Fintype.card V * (p : ℝ) ^ A.card| >
        (2 * c) * (Fintype.card V * (p : ℝ) ^ A.card)}
  have hevent : {ω | ¬ IsTypicalAt (sampleGraph ω) (p : ℝ) (2 * c) h} =
      ⋃ A ∈ faceFamilies V r h, B A := by
    ext ω
    simp only [IsTypicalAt, Set.mem_ofPred_eq, not_forall, not_le, exists_prop,
      Set.mem_iUnion, mem_faceFamilies, B]
  have hbound (A : Finset (Block V r)) (hA : A ∈ faceFamilies V r h) :
      (BernoulliSubset.probability (Block V (r + 1)) p).real (B A) ≤
        2 * Real.exp (-(((Fintype.card V - h * r : ℕ) : ℝ) * (p : ℝ) ^ h * c ^ 2 /
          (2 * (1 + 2 * c)))) := by
    have hAc := mem_faceFamilies A |>.mp hA
    have hb : (faceVertices A).card ≤ h * r :=
      (card_faceVertices_le A).trans (Nat.mul_le_mul_right r hAc)
    have hs : ((faceVertices A).card : ℝ) ≤ c * Fintype.card V := by
      exact (by exact_mod_cast hb : ((faceVertices A).card : ℝ) ≤ (h * r : ℝ)).trans hsmall
    refine (commonNeighbors_reference_concentration p hc A hs).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (commonMean_lower p A hAc) (sq_nonneg c)) (by positivity)
  rw [hevent]
  calc
    _ ≤ ∑ A ∈ faceFamilies V r h, (BernoulliSubset.probability (Block V (r + 1)) p).real (B A) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _ ∈ faceFamilies V r h,
        2 * Real.exp (-(((Fintype.card V - h * r : ℕ) : ℝ) * (p : ℝ) ^ h * c ^ 2 /
          (2 * (1 + 2 * c)))) := sum_le_sum hbound
    _ = _ := by rw [sum_const, nsmul_eq_mul, card_faceFamilies]

end Arxiv2411_18291
