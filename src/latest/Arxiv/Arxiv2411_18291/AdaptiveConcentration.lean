import Arxiv.Arxiv2411_18291.ExponentialProcess

/-!
# Concentration from a bound on the sum of conditional means

Part 2 of `lem:pseudobin` in arXiv:2411.18291, stated for an arbitrary
filtration to which the variables are adapted. Applying exponential
compensation to the absolute values gives a bound stronger than the printed
one. Independence is not needed.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ} {n : ℕ} {C c μ : ℝ}

/-- Upper-tail concentration for bounded nonnegative adapted variables.
The conditional-mean bound is allowed to hold only almost surely. -/
theorem adaptive_nonnegative_upper_tail_ge (hC : 0 < C) (hc : 0 < c)
    (hX : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (X i))
    (hXC : ∀ i < n, ∀ᵐ ω ∂P, 0 ≤ X i ω ∧ X i ω ≤ C)
    (hμ : ∀ᵐ ω ∂P, (∑ i ∈ range n, P[X i | ℱ i] ω) ≤ μ) :
    P.real {ω | (1 + c) * μ ≤ ∑ i ∈ range n, X i ω} ≤
      Real.exp (-(μ * c ^ 2 / ((2 + c) * C))) := by
  let t := c / ((1 + c) * C)
  let g := 2 * t / (2 - t * C)
  obtain ⟨ht, hg, htC, hpar⟩ := adaptive_chernoff_parameters hC hc
  change 0 < t at ht
  change 0 ≤ g at hg
  change t * C < 2 at htC
  change -t * (1 + c) + g = -(c ^ 2 / ((2 + c) * C)) at hpar
  let M := compensatedExp ℱ P X t g n
  let δ := Real.exp (t * ((1 + c) * μ) - g * μ)
  have hδ : 0 < δ := Real.exp_pos _
  have hi : Integrable M P := compensatedExp_integrable hX hXC ht.le hg
  have hE : (∫ ω, M ω ∂P) ≤ 1 := integral_compensatedExp_le ht.le htC n hX hXC
  have hsub : {ω | (1 + c) * μ ≤ ∑ i ∈ range n, X i ω} ≤ᵐ[P]
      {ω | δ ≤ M ω} := by
    filter_upwards [hμ] with ω hω
    intro hx
    change (1 + c) * μ ≤ ∑ i ∈ range n, X i ω at hx
    change δ ≤ M ω
    dsimp only [δ, M, compensatedExp]
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum]
    apply Real.exp_le_exp.mpr
    exact sub_le_sub (mul_le_mul_of_nonneg_left hx ht.le)
      (mul_le_mul_of_nonneg_left hω hg)
  have hprob : P.real {ω | (1 + c) * μ ≤ ∑ i ∈ range n, X i ω} ≤
      P.real {ω | δ ≤ M ω} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have hmark : δ * P.real {ω | δ ≤ M ω} ≤ 1 :=
    (mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun _ => (Real.exp_pos _).le) hi δ).trans hE
  calc
    _ ≤ P.real {ω | δ ≤ M ω} := hprob
    _ ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by rw [mul_comm]; exact hmark)
    _ = _ := by
      dsimp only [δ]
      rw [one_div, ← Real.exp_neg]
      congr 1
      calc
        -(t * ((1 + c) * μ) - g * μ) = μ * (-t * (1 + c) + g) := by ring
        _ = _ := by rw [hpar]; ring

/-- The strict-event form of the nonnegative upper-tail bound. -/
theorem adaptive_nonnegative_upper_tail (hC : 0 < C) (hc : 0 < c)
    (hX : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (X i))
    (hXC : ∀ i < n, ∀ᵐ ω ∂P, 0 ≤ X i ω ∧ X i ω ≤ C)
    (hμ : ∀ᵐ ω ∂P, (∑ i ∈ range n, P[X i | ℱ i] ω) ≤ μ) :
    P.real {ω | (1 + c) * μ < ∑ i ∈ range n, X i ω} ≤
      Real.exp (-(μ * c ^ 2 / ((2 + c) * C))) := by
  have hsub : {ω | (1 + c) * μ < ∑ i ∈ range n, X i ω} ⊆
      {ω | (1 + c) * μ ≤ ∑ i ∈ range n, X i ω} := by
    intro ω h
    change (1 + c) * μ < ∑ i ∈ range n, X i ω at h
    change (1 + c) * μ ≤ ∑ i ∈ range n, X i ω
    exact h.le
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (adaptive_nonnegative_upper_tail_ge hC hc hX hXC hμ)

/-- A stronger form of part 2: the absolute value of a signed sum is bounded
using conditional expectations of the absolute values of its summands. -/
theorem adaptive_signed_upper_tail (hC : 0 < C) (hc : 0 < c)
    (hX : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (X i))
    (hXC : ∀ i < n, ∀ᵐ ω ∂P, |X i ω| ≤ C)
    (hμ : ∀ᵐ ω ∂P, (∑ i ∈ range n, P[fun ω => |X i ω| | ℱ i] ω) ≤ μ) :
    P.real {ω | |∑ i ∈ range n, X i ω| > (1 + c) * μ} ≤
      Real.exp (-(μ * c ^ 2 / ((2 + c) * C))) := by
  have hY : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (fun ω => |X i ω|) :=
    fun i hi => continuous_abs.comp_stronglyMeasurable (hX i hi)
  have hYC : ∀ i < n, ∀ᵐ ω ∂P, 0 ≤ |X i ω| ∧ |X i ω| ≤ C := by
    intro i hi
    filter_upwards [hXC i hi] with ω hω
    exact ⟨abs_nonneg _, hω⟩
  apply le_trans (measureReal_mono (show
    {ω | |∑ i ∈ range n, X i ω| > (1 + c) * μ} ⊆
      {ω | (1 + c) * μ < ∑ i ∈ range n, |X i ω|} from ?_))
    (adaptive_nonnegative_upper_tail hC hc hY hYC hμ)
  intro ω hω
  exact hω.trans_le (Finset.abs_sum_le_sum_abs (fun i => X i ω) (range n))

/-- Part 2 of the paper's concentration lemma, with its stated constants.
Nonnegative `c` and positive `C` make the exponent well-defined. -/
theorem pseudobin_part_two (hC : 0 < C) (hc : 0 ≤ c)
    (hX : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (X i))
    (hXC : ∀ i < n, ∀ᵐ ω ∂P, |X i ω| ≤ C)
    (hμ : ∀ᵐ ω ∂P, (∑ i ∈ range n, P[fun ω => |X i ω| | ℱ i] ω) ≤ μ) :
    P.real {ω | |∑ i ∈ range n, X i ω| > (1 + c) * μ} ≤
      2 * Real.exp (-(μ * c ^ 2 / (2 * (1 + 2 * c) * C))) := by
  obtain rfl | hcpos := hc.eq_or_lt
  · simpa using (measureReal_le_one (μ := P) (s :=
      {ω | |∑ i ∈ range n, X i ω| > (1 + (0 : ℝ)) * μ})).trans (by norm_num : (1 : ℝ) ≤ 2)
  have hμ0 : 0 ≤ μ := by
    have hpos : ∀ i, 0 ≤ᵐ[P] P[fun ω => |X i ω| | ℱ i] :=
      fun _ => condExp_nonneg (ae_of_all _ fun _ => abs_nonneg _)
    have hall : ∀ᵐ ω ∂P, ∀ i, 0 ≤ P[fun ω => |X i ω| | ℱ i] ω := ae_all_iff.mpr hpos
    obtain ⟨ω, hω, hωμ⟩ := (hall.and hμ).exists
    exact (sum_nonneg fun i _ => hω i).trans hωμ
  have hden : 0 < (2 + c) * C := by positivity
  have hcompare : -(μ * c ^ 2 / ((2 + c) * C)) ≤
      -(μ * c ^ 2 / (2 * (1 + 2 * c) * C)) := by
    apply neg_le_neg
    exact div_le_div_of_nonneg_left (by positivity) hden (by nlinarith)
  calc
    _ ≤ Real.exp (-(μ * c ^ 2 / ((2 + c) * C))) :=
      adaptive_signed_upper_tail hC hcpos hX hXC hμ
    _ ≤ Real.exp (-(μ * c ^ 2 / (2 * (1 + 2 * c) * C))) := Real.exp_le_exp.mpr hcompare
    _ ≤ _ := by nlinarith [Real.exp_pos (-(μ * c ^ 2 / (2 * (1 + 2 * c) * C)))]

/-- The sigma-algebra before time `i` is generated by the variables with
indices strictly smaller than `i`, exactly as in the paper's conditioning. -/
def pastFiltration (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) : Filtration ℕ mΩ where
  seq i := ⨆ j < i, MeasurableSpace.comap (X j) inferInstance
  mono' _ _ hij := iSup₂_le fun j hj => le_iSup₂_of_le j (lt_of_lt_of_le hj hij) le_rfl
  le' _ := iSup₂_le fun j _ => (hX j).comap_le

omit [IsProbabilityMeasure P] in
theorem measurable_pastFiltration (hX : ∀ i, Measurable (X i)) (i : ℕ) :
    StronglyMeasurable[pastFiltration X hX (i + 1)] (X i) := by
  apply Measurable.stronglyMeasurable
  exact measurable_iff_comap_le.mpr (le_iSup₂_of_le i (Nat.lt_succ_self i) le_rfl)

/-- The direct natural-history formulation of part 2 of `lem:pseudobin`. -/
theorem pseudobin_part_two_natural (hC : 0 < C) (hc : 0 ≤ c)
    (hX : ∀ i, Measurable (X i))
    (hXC : ∀ i < n, ∀ᵐ ω ∂P, |X i ω| ≤ C)
    (hμ : ∀ᵐ ω ∂P,
      (∑ i ∈ range n, P[fun ω => |X i ω| | pastFiltration X hX i] ω) ≤ μ) :
    P.real {ω | |∑ i ∈ range n, X i ω| > (1 + c) * μ} ≤
      2 * Real.exp (-(μ * c ^ 2 / (2 * (1 + 2 * c) * C))) :=
  pseudobin_part_two hC hc (fun i _ => measurable_pastFiltration hX i) hXC hμ

end Arxiv2411_18291
