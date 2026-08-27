import Arxiv.Arxiv2411_18291.LinearTypicalityDensity

/-! # Typicality with separate errors for density and neighborhoods

The density estimate has many more independent trials than a common
neighborhood. Giving it a smaller error preserves almost the entire final
error allowance for neighborhood concentration.
-/

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {r h : ℕ}

omit [DecidableEq V] in
theorem sampleGraph_card_concentration_sharp (p : unitInterval) {c : ℝ} (hc : 0 ≤ c) :
    let μ := (p : ℝ) * (Fintype.card V).choose r
    (BernoulliSubset.probability (Block V r) p).real
      {ω | |((sampleGraph ω).card : ℝ) - μ| > c * μ} ≤
        2 * Real.exp (-(μ * c ^ 2 / (2 + c))) := by
  have hdis : Pairwise fun e f : Block V r => Disjoint ({e} : Finset (Block V r)) {f} := by
    intro e f hef
    simpa only [disjoint_singleton] using hef
  simpa [← sampleGraph_card_eq_sum, Fintype.card_finset_len, mul_comm] using
    BernoulliSubset.count_concentration_sharp p univ (fun e : Block V r => {e}) hdis hc

theorem commonNeighbors_concentration_sharp (p : unitInterval) (A : Finset (Block V r))
    {c : ℝ} (hc : 0 ≤ c) :
    let μ := ((Fintype.card V - (faceVertices A).card : ℕ) : ℝ) * (p : ℝ) ^ A.card
    (BernoulliSubset.probability (Block V (r + 1)) p).real
      {ω | |((commonNeighbors (sampleGraph ω) A).card : ℝ) - μ| > c * μ} ≤
        2 * Real.exp (-(μ * c ^ 2 / (2 + c))) := by
  simpa only [← commonNeighbors_card_eq_sum, card_extensionEdges, sum_const,
    card_univ, nsmul_eq_mul, card_outsideFaces] using
    BernoulliSubset.count_concentration_sharp p univ (extensionEdges A)
      (extensionEdges_disjoint A) hc

theorem abs_sub_reference_le_of_bias {x n b p c β : ℝ}
    (hb : 0 ≤ b) (hp : 0 ≤ p) (hc : 0 ≤ c) (hsmall : b ≤ β * n)
    (hx : |x - (n - b) * p| ≤ c * ((n - b) * p)) :
    |x - n * p| ≤ (c + β) * (n * p) := by
  have ht := abs_sub_le x ((n - b) * p) (n * p)
  have he : |(n - b) * p - n * p| = b * p := by
    rw [show (n - b) * p - n * p = -(b * p) by ring, abs_neg,
      abs_of_nonneg (mul_nonneg hb hp)]
  rw [he] at ht
  have hbp := mul_le_mul_of_nonneg_right hsmall hp
  have hcbp := mul_nonneg hc (mul_nonneg hb hp)
  nlinarith only [ht, hx, hbp, hcbp]

theorem commonNeighbors_reference_concentration_sharp (p : unitInterval)
    {c β : ℝ} (hc : 0 ≤ c) (A : Finset (Block V r))
    (hsmall : ((faceVertices A).card : ℝ) ≤ β * Fintype.card V) :
    let μ := ((Fintype.card V - (faceVertices A).card : ℕ) : ℝ) * (p : ℝ) ^ A.card
    (BernoulliSubset.probability (Block V (r + 1)) p).real
      {ω | |((commonNeighbors (sampleGraph ω) A).card : ℝ) -
        Fintype.card V * (p : ℝ) ^ A.card| > (c + β) *
          (Fintype.card V * (p : ℝ) ^ A.card)} ≤
      2 * Real.exp (-(μ * c ^ 2 / (2 + c))) := by
  dsimp only
  apply le_trans (measureReal_mono (show
    {ω | |((commonNeighbors (sampleGraph ω) A).card : ℝ) -
      Fintype.card V * (p : ℝ) ^ A.card| > (c + β) *
        (Fintype.card V * (p : ℝ) ^ A.card)} ⊆
    {ω | |((commonNeighbors (sampleGraph ω) A).card : ℝ) -
      ((Fintype.card V - (faceVertices A).card : ℕ) : ℝ) * (p : ℝ) ^ A.card| >
        c * (((Fintype.card V - (faceVertices A).card : ℕ) : ℝ) * (p : ℝ) ^ A.card)} from ?_))
    (commonNeighbors_concentration_sharp p A hc)
  intro ω hω
  change c * (((Fintype.card V - (faceVertices A).card : ℕ) : ℝ) * (p : ℝ) ^ A.card) <
    |((commonNeighbors (sampleGraph ω) A).card : ℝ) -
      ((Fintype.card V - (faceVertices A).card : ℕ) : ℝ) * (p : ℝ) ^ A.card|
  by_contra hn
  have hx := le_of_not_gt hn
  rw [Nat.cast_sub (card_le_univ (faceVertices A))] at hx
  exact (not_lt_of_ge (abs_sub_reference_le_of_bias (Nat.cast_nonneg _)
    (pow_nonneg p.property.1 _) hc hsmall hx)) hω

theorem typicalAt_failure_probability_sharp (p : unitInterval) {c β : ℝ} (hc : 0 ≤ c)
    (hsmall : (h * r : ℝ) ≤ β * Fintype.card V) :
    let m := ((Fintype.card V - h * r : ℕ) : ℝ) * (p : ℝ) ^ h
    (BernoulliSubset.probability (Block V (r + 1)) p).real
      {ω | ¬ IsTypicalAt (sampleGraph ω) (p : ℝ) (c + β) h} ≤
      ((∑ a ∈ range (h + 1), ((Fintype.card V).choose r).choose a : ℕ) : ℝ) *
        (2 * Real.exp (-(m * c ^ 2 / (2 + c)))) := by
  dsimp only
  let B (A : Finset (Block V r)) :=
    {ω : BernoulliSubset.Sample (Block V (r + 1)) |
      |((commonNeighbors (sampleGraph ω) A).card : ℝ) - Fintype.card V * (p : ℝ) ^ A.card| >
        (c + β) * (Fintype.card V * (p : ℝ) ^ A.card)}
  have hevent : {ω | ¬ IsTypicalAt (sampleGraph ω) (p : ℝ) (c + β) h} =
      ⋃ A ∈ faceFamilies V r h, B A := by
    ext ω
    simp only [IsTypicalAt, Set.mem_ofPred_eq, not_forall, not_le, exists_prop,
      Set.mem_iUnion, mem_faceFamilies, B]
  have hbound (A : Finset (Block V r)) (hA : A ∈ faceFamilies V r h) :
      (BernoulliSubset.probability (Block V (r + 1)) p).real (B A) ≤
        2 * Real.exp (-(((Fintype.card V - h * r : ℕ) : ℝ) * (p : ℝ) ^ h * c ^ 2 /
          (2 + c))) := by
    have hAc := mem_faceFamilies A |>.mp hA
    have hb : (faceVertices A).card ≤ h * r :=
      (card_faceVertices_le A).trans (Nat.mul_le_mul_right r hAc)
    have hs : ((faceVertices A).card : ℝ) ≤ β * Fintype.card V :=
      (show ((faceVertices A).card : ℝ) ≤ (h * r : ℝ) by exact_mod_cast hb).trans hsmall
    refine (commonNeighbors_reference_concentration_sharp p hc A hs).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (commonMean_lower p A hAc) (sq_nonneg c)) (by positivity)
  rw [hevent]
  calc
    _ ≤ ∑ A ∈ faceFamilies V r h,
        (BernoulliSubset.probability (Block V (r + 1)) p).real (B A) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _ ∈ faceFamilies V r h,
        2 * Real.exp (-(((Fintype.card V - h * r : ℕ) : ℝ) * (p : ℝ) ^ h * c ^ 2 /
          (2 + c))) := sum_le_sum hbound
    _ = _ := by rw [sum_const, nsmul_eq_mul, card_faceFamilies]

def separateTypicalityFailureBound (n r h : ℕ) (p δ : ℝ) : ℝ :=
  2 * Real.exp (-(p * n.choose (r + 1) * (δ / (512 * h)) ^ 2 /
    (2 + δ / (512 * h)))) +
      ((∑ a ∈ range (h + 1), (n.choose r).choose a : ℕ) : ℝ) *
        (2 * Real.exp (-(((n - h * r : ℕ) : ℝ) * p ^ h * ((63 / 64 : ℝ) * δ) ^ 2 /
          (2 + (63 / 64 : ℝ) * δ))))

theorem typical_failure_probability_separate (p : unitInterval) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hh : 1 ≤ h) (hn : r + 1 ≤ Fintype.card V)
    (hroot : (h * r : ℝ) ≤ (δ / 128) * Fintype.card V) :
    (BernoulliSubset.probability (Block V (r + 1)) p).real
      {ω | ¬ (|density (sampleGraph ω) - (p : ℝ)| ≤ δ * p ∧
        IsTypical (sampleGraph ω) δ h)} ≤
      separateTypicalityFailureBound (Fintype.card V) r h p δ := by
  let c := δ / (512 * h : ℝ)
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hhpos : (0 : ℝ) < h := by linarith only [hhR]
  have hden : 0 < 512 * (h : ℝ) := by positivity
  have hc : 0 ≤ c := div_nonneg hδ hden.le
  have hcδ : c ≤ δ := by
    apply (div_le_iff₀ hden).mpr
    have hm := mul_le_mul_of_nonneg_left hhR hδ
    nlinarith only [hδ, hm]
  have hch : c * h = δ / 512 := by dsimp only [c]; field_simp
  have hsmall : c * h ≤ 1 / 2 := by rw [hch]; linarith only [hδ1]
  have hbudget : (127 / 128 : ℝ) * δ + 2 * c * h ≤ δ * (1 - 2 * c * h) := by
    rw [mul_assoc 2 c _, hch]
    nlinarith only [hδ, hδ1]
  let E := {ω : BernoulliSubset.Sample (Block V (r + 1)) |
    |((sampleGraph ω).card : ℝ) - (p : ℝ) * (Fintype.card V).choose (r + 1)| >
      c * ((p : ℝ) * (Fintype.card V).choose (r + 1))}
  let B := {ω : BernoulliSubset.Sample (Block V (r + 1)) |
    ¬ IsTypicalAt (sampleGraph ω) (p : ℝ) ((127 / 128 : ℝ) * δ) h}
  have hsub : {ω | ¬ (|density (sampleGraph ω) - (p : ℝ)| ≤ δ * p ∧
      IsTypical (sampleGraph ω) δ h)} ⊆ E ∪ B := by
    intro ω hω
    by_cases hE : ω ∈ E
    · exact Or.inl hE
    · right
      change ¬ IsTypicalAt (sampleGraph ω) (p : ℝ) ((127 / 128 : ℝ) * δ) h
      intro hT
      have he : |((sampleGraph ω).card : ℝ) -
          (p : ℝ) * (Fintype.card V).choose (r + 1)| ≤
            c * ((p : ℝ) * (Fintype.card V).choose (r + 1)) := le_of_not_gt hE
      have hd := density_error_of_card_error (sampleGraph ω) hn he
      exact hω ⟨hd.trans (mul_le_mul_of_nonneg_right hcδ p.property.1),
        hT.to_isTypical_of_error_budget p.property.1 hc hδ hd hsmall hbudget⟩
  have hB := typicalAt_failure_probability_sharp p
    (by positivity : (0 : ℝ) ≤ (63 / 64 : ℝ) * δ) hroot
  rw [show (63 / 64 : ℝ) * δ + δ / 128 = (127 / 128 : ℝ) * δ by ring] at hB
  calc
    _ ≤ (BernoulliSubset.probability (Block V (r + 1)) p).real (E ∪ B) := measureReal_mono hsub
    _ ≤ (BernoulliSubset.probability (Block V (r + 1)) p).real E +
        (BernoulliSubset.probability (Block V (r + 1)) p).real B := measureReal_union_le E B
    _ ≤ _ := add_le_add (sampleGraph_card_concentration_sharp p hc) hB

end Arxiv2411_18291
