import Arxiv.Arxiv2411_18291.IndependentConcentration
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.InfinitePi

/-!
# Independent random subsets and counts

The sample space records whether each potential element is present. Products
of indicators on disjoint finite sets are independent, so the corrected
concentration lemma applies to counts of disjoint configurations.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators ENNReal

noncomputable section

namespace Arxiv2411_18291.BernoulliSubset

variable {ι κ : Type*}

abbrev Sample (ι : Type*) := ι → Prop

def coin (p : unitInterval) : Measure Prop := bernoulliMeasure True False p

instance (p : unitInterval) : IsProbabilityMeasure (coin p) := by
  unfold coin
  infer_instance

def probability (ι : Type*) (p : unitInterval) : Measure (Sample ι) :=
  Measure.infinitePi (fun _ => coin p)

instance (p : unitInterval) : IsProbabilityMeasure (probability ι p) := by
  unfold probability
  infer_instance

def allPresent (s : Finset ι) : Set (Sample ι) := {ω | ∀ i ∈ s, ω i}

theorem allPresent_eq_iInter (s : Finset ι) :
    allPresent s = ⋂ i ∈ s, (fun ω : Sample ι => ω i) ⁻¹' {True} := by
  ext ω
  simp [allPresent]

theorem allPresent_measurable (s : Finset ι) : MeasurableSet (allPresent s) := by
  rw [allPresent_eq_iInter]
  exact MeasurableSet.biInter s.countable_toSet
    (fun i _ => (measurable_pi_apply i) (.singleton True))

theorem coordinate_law (p : unitInterval) (i : ι) :
    (probability ι p).map (fun ω => ω i) = coin p :=
  Measure.infinitePi_map_eval (fun _ => coin p) i

theorem probability_coordinate (p : unitInterval) (i : ι) :
    probability ι p ((fun ω => ω i) ⁻¹' {True}) = unitInterval.toNNReal p := by
  rw [← Measure.map_apply (measurable_pi_apply i) (.singleton True), coordinate_law]
  simp [coin]

theorem probability_allPresent (p : unitInterval) (s : Finset ι) :
    probability ι p (allPresent s) = (unitInterval.toNNReal p : ℝ≥0∞) ^ s.card := by
  have hInd : iIndepFun (fun i (ω : Sample ι) => ω i) (probability ι p) :=
    iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  rw [allPresent_eq_iInter,
    hInd.measure_inter_preimage_eq_mul s (fun _ _ => MeasurableSet.singleton True)]
  simp only [probability_coordinate, prod_const]

theorem probabilityReal_allPresent (p : unitInterval) (s : Finset ι) :
    (probability ι p).real (allPresent s) = (p : ℝ) ^ s.card := by
  simp [measureReal_def, probability_allPresent]

def present (s : Finset ι) : Sample ι → ℝ := (allPresent s).indicator (fun _ => 1)

theorem present_measurable (s : Finset ι) : Measurable (present s) :=
  measurable_const.indicator (allPresent_measurable s)

theorem present_bounds (s : Finset ι) (ω : Sample ι) :
    0 ≤ present s ω ∧ present s ω ≤ 1 := by
  classical
  simp only [present, Set.indicator]
  split_ifs <;> norm_num

theorem present_integrable (p : unitInterval) (s : Finset ι) :
    Integrable (present s) (probability ι p) :=
  (integrable_const 1).indicator (allPresent_measurable s)

theorem present_mean (p : unitInterval) (s : Finset ι) :
    (∫ ω, present s ω ∂probability ι p) = (p : ℝ) ^ s.card := by
  change (∫ ω, (allPresent s).indicator (1 : Sample ι → ℝ) ω ∂probability ι p) = _
  rw [integral_indicator_one (allPresent_measurable s), probabilityReal_allPresent]

open Classical in
theorem sum_present_eq_card_filter (s : Finset κ) (f : κ → Finset ι) (ω : Sample ι) :
    (∑ j ∈ s, present (f j) ω) = ((s.filter fun j => ω ∈ allPresent (f j)).card : ℝ) := by
  classical
  simp [present, Set.indicator]

theorem allPresent_biUnion [DecidableEq ι] (s : Finset κ) (f : κ → Finset ι) :
    allPresent (s.biUnion f) = ⋂ j ∈ s, allPresent (f j) := by
  ext ω
  simp only [allPresent, Set.mem_ofPred_eq, mem_biUnion, Set.mem_iInter]
  constructor
  · intro h j hj i hi
    exact h i ⟨j, hj, hi⟩
  · intro h i ⟨j, hj, hi⟩
    exact h j hj i hi

/-- Disjoint sets of coordinates give mutually independent occurrence events. -/
theorem allPresent_independent (p : unitInterval)
    (f : κ → Finset ι) (hdis : Pairwise fun i j => Disjoint (f i) (f j)) :
    iIndepSet (fun j => allPresent (f j)) (probability ι p) := by
  classical
  rw [iIndepSet_iff_meas_biInter (fun j => allPresent_measurable (f j))]
  intro s
  rw [← allPresent_biUnion, probability_allPresent,
    card_biUnion (fun i _ j _ hij => hdis hij)]
  simp_rw [probability_allPresent]
  exact Finset.prod_pow_eq_pow_sum _ _ _ |>.symm

theorem present_independent (p : unitInterval)
    (f : κ → Finset ι) (hdis : Pairwise fun i j => Disjoint (f i) (f j)) :
    iIndepFun (fun j => present (f j)) (probability ι p) :=
  (allPresent_independent p f hdis).iIndepFun_indicator

/-- The expected number of occurring configurations, without disjointness. -/
theorem count_mean (p : unitInterval) (s : Finset κ) (f : κ → Finset ι) :
    (∫ ω, ∑ j ∈ s, present (f j) ω ∂probability ι p) =
      ∑ j ∈ s, (p : ℝ) ^ (f j).card := by
  rw [integral_finsetSum s (fun j _ => present_integrable p (f j))]
  simp_rw [present_mean]

/-- The summands are indicators, so the corrected concentration lemma's
nonnegativity assumption is discharged by `present_bounds`. -/
theorem count_concentration (p : unitInterval) (s : Finset κ)
    (f : κ → Finset ι) (hdis : Pairwise fun i j => Disjoint (f i) (f j))
    {c : ℝ} (hc : 0 ≤ c) :
    let μ := ∑ j ∈ s, (p : ℝ) ^ (f j).card
    (probability ι p).real {ω | |(∑ j ∈ s, present (f j) ω) - μ| > c * μ} ≤
      2 * Real.exp (-(μ * c ^ 2 / (2 * (1 + 2 * c)))) := by
  dsimp only
  simpa only [mul_one] using pseudobin_part_one_nonneg s (by norm_num : (0 : ℝ) < 1) hc
    (fun j => present_measurable (f j)) (present_independent p f hdis)
    (fun j _ => ae_of_all _ fun ω => present_bounds (f j) ω) (count_mean p s f)

/-- Retain the stronger independent upper-tail constant in the two-sided bound. -/
theorem count_concentration_sharp (p : unitInterval) (s : Finset κ)
    (f : κ → Finset ι) (hdis : Pairwise fun i j => Disjoint (f i) (f j))
    {c : ℝ} (hc : 0 ≤ c) :
    let μ := ∑ j ∈ s, (p : ℝ) ^ (f j).card
    (probability ι p).real {ω | |(∑ j ∈ s, present (f j) ω) - μ| > c * μ} ≤
      2 * Real.exp (-(μ * c ^ 2 / (2 + c))) := by
  dsimp only
  obtain rfl | hcpos := hc.eq_or_lt
  · simpa using (measureReal_le_one (μ := probability ι p) (s :=
      {ω | |(∑ j ∈ s, present (f j) ω) - ∑ j ∈ s, (p : ℝ) ^ (f j).card| >
        (0 : ℝ) * ∑ j ∈ s, (p : ℝ) ^ (f j).card})).trans (by norm_num : (1 : ℝ) ≤ 2)
  let μ := ∑ j ∈ s, (p : ℝ) ^ (f j).card
  have hμ : 0 ≤ μ := sum_nonneg fun j _ => pow_nonneg p.property.1 _
  have hsub : {ω | |(∑ j ∈ s, present (f j) ω) - μ| > c * μ} ⊆
      {ω | (1 + c) * μ < ∑ j ∈ s, present (f j) ω} ∪
      {ω | (∑ j ∈ s, present (f j) ω) < (1 - c) * μ} := by
    intro ω hω
    change c * μ < |(∑ j ∈ s, present (f j) ω) - μ| at hω
    rcases lt_abs.mp hω with hω | hω
    · left
      change (1 + c) * μ < ∑ j ∈ s, present (f j) ω
      linarith only [hω]
    · right
      change (∑ j ∈ s, present (f j) ω) < (1 - c) * μ
      linarith only [hω]
  have hu := independent_nonnegative_upper_tail s (by norm_num : (0 : ℝ) < 1) hcpos
    (fun j => present_measurable (f j)) (present_independent p f hdis)
    (fun j _ => ae_of_all _ fun ω => present_bounds (f j) ω) (count_mean p s f)
  have hl := independent_nonnegative_lower_tail s (by norm_num : (0 : ℝ) < 1) hcpos.le
    (fun j => present_measurable (f j)) (present_independent p f hdis)
    (fun j _ => ae_of_all _ fun ω => present_bounds (f j) ω) (count_mean p s f)
  simp only [mul_one] at hu hl
  have ht : Real.exp (-(μ * c ^ 2 / 2)) ≤ Real.exp (-(μ * c ^ 2 / (2 + c))) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith only [hcpos])
  calc
    _ ≤ (probability ι p).real
        ({ω | (1 + c) * μ < ∑ j ∈ s, present (f j) ω} ∪
          {ω | (∑ j ∈ s, present (f j) ω) < (1 - c) * μ}) := measureReal_mono hsub
    _ ≤ _ := (measureReal_union_le _ _).trans (by linarith only [hu, hl, ht])

end Arxiv2411_18291.BernoulliSubset
