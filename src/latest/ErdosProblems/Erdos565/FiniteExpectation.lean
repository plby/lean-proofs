import ErdosProblems.Erdos565.FiniteAnalysis
import Mathlib.Tactic

/-!
# Finite conditional expectations

The probabilistic part of the proof of Erdős problem 565 only uses finite
sample spaces.  This file records the required calculus directly as weighted
`Finset` sums, without introducing a measure space.

The weights are allowed to be unnormalised.  Conditioning on `given` divides
by the mass of `outcomes ∩ given`; hypotheses asserting that this mass is
positive are therefore kept explicit.  This is convenient for the binomial
random-subset distribution, where positivity is witnessed by one admissible
sample.
-/

open scoped BigOperators

namespace Erdos565
namespace FiniteExpectation

variable {Ω ι : Type*} [DecidableEq Ω]

/-- The part of an event lying in the declared finite sample space. -/
def conditioningSet (outcomes given : Finset Ω) : Finset Ω :=
  outcomes ∩ given

/-- The (not necessarily normalised) weight of an event. -/
def conditioningMass (outcomes given : Finset Ω) (weight : Ω → ℝ) : ℝ :=
  ∑ ω ∈ conditioningSet outcomes given, weight ω

/-- An unnormalised finite expectation. -/
def expectation (outcomes : Finset Ω) (weight : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ ω ∈ outcomes, weight ω * f ω

/-- Conditional expectation with respect to an unnormalised finite weight. -/
noncomputable def conditionalExpectation (outcomes given : Finset Ω) (weight : Ω → ℝ)
    (f : Ω → ℝ) : ℝ :=
  expectation (conditioningSet outcomes given) weight f /
    conditioningMass outcomes given weight

/-- Conditional probability, expressed as the expectation of an indicator. -/
noncomputable def conditionalProbability (outcomes given event : Finset Ω)
    (weight : Ω → ℝ) : ℝ :=
  conditionalExpectation outcomes given weight fun ω ↦ if ω ∈ event then 1 else 0

@[simp] theorem mem_conditioningSet {outcomes given : Finset Ω} {ω : Ω} :
    ω ∈ conditioningSet outcomes given ↔ ω ∈ outcomes ∧ ω ∈ given := by
  simp [conditioningSet]

theorem conditioningSet_subset_left (outcomes given : Finset Ω) :
    conditioningSet outcomes given ⊆ outcomes := by
  exact Finset.inter_subset_left

theorem conditioningSet_subset_right (outcomes given : Finset Ω) :
    conditioningSet outcomes given ⊆ given := by
  exact Finset.inter_subset_right

/-! ## Positivity of conditioning -/

theorem conditioningMass_nonneg (outcomes given : Finset Ω) (weight : Ω → ℝ)
    (hweight : ∀ ω ∈ outcomes, 0 ≤ weight ω) :
    0 ≤ conditioningMass outcomes given weight := by
  unfold conditioningMass
  exact Finset.sum_nonneg fun ω hω ↦
    hweight ω (conditioningSet_subset_left outcomes given hω)

/-- One positively weighted admissible outcome makes the conditioning mass
strictly positive. -/
theorem conditioningMass_pos_of_mem {outcomes given : Finset Ω} {weight : Ω → ℝ}
    (hweight : ∀ ω ∈ outcomes, 0 ≤ weight ω) {ω : Ω}
    (hωout : ω ∈ outcomes) (hωgiven : ω ∈ given) (hωpos : 0 < weight ω) :
    0 < conditioningMass outcomes given weight := by
  unfold conditioningMass
  have hω : ω ∈ conditioningSet outcomes given := by
    exact mem_conditioningSet.mpr ⟨hωout, hωgiven⟩
  have hle : weight ω ≤ ∑ x ∈ conditioningSet outcomes given, weight x := by
    apply Finset.single_le_sum
    · intro x hx
      exact hweight x (conditioningSet_subset_left outcomes given hx)
    · exact hω
  exact hωpos.trans_le hle

theorem conditioningMass_pos_of_nonempty {outcomes given : Finset Ω}
    {weight : Ω → ℝ} (hweight : ∀ ω ∈ outcomes, 0 < weight ω)
    (hne : (conditioningSet outcomes given).Nonempty) :
    0 < conditioningMass outcomes given weight := by
  obtain ⟨ω, hω⟩ := hne
  exact conditioningMass_pos_of_mem
    (fun x hx ↦ (hweight x hx).le)
    (conditioningSet_subset_left outcomes given hω)
    (conditioningSet_subset_right outcomes given hω)
    (hweight ω (conditioningSet_subset_left outcomes given hω))

theorem conditioningMass_ne_zero_of_pos {outcomes given : Finset Ω}
    {weight : Ω → ℝ} (h : 0 < conditioningMass outcomes given weight) :
    conditioningMass outcomes given weight ≠ 0 :=
  h.ne'

/-! ## Linearity -/

@[simp] theorem expectation_zero (outcomes : Finset Ω) (weight : Ω → ℝ) :
    expectation outcomes weight (fun _ ↦ 0) = 0 := by
  simp [expectation]

theorem expectation_add (outcomes : Finset Ω) (weight f g : Ω → ℝ) :
    expectation outcomes weight (fun ω ↦ f ω + g ω) =
      expectation outcomes weight f + expectation outcomes weight g := by
  simp only [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_sub (outcomes : Finset Ω) (weight f g : Ω → ℝ) :
    expectation outcomes weight (fun ω ↦ f ω - g ω) =
      expectation outcomes weight f - expectation outcomes weight g := by
  simp only [expectation, mul_sub, Finset.sum_sub_distrib]

theorem expectation_const_mul (outcomes : Finset Ω) (weight f : Ω → ℝ) (c : ℝ) :
    expectation outcomes weight (fun ω ↦ c * f ω) =
      c * expectation outcomes weight f := by
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  ring

@[simp] theorem conditionalExpectation_zero (outcomes given : Finset Ω)
    (weight : Ω → ℝ) :
    conditionalExpectation outcomes given weight (fun _ ↦ 0) = 0 := by
  simp [conditionalExpectation]

theorem conditionalExpectation_add (outcomes given : Finset Ω)
    (weight f g : Ω → ℝ) :
    conditionalExpectation outcomes given weight (fun ω ↦ f ω + g ω) =
      conditionalExpectation outcomes given weight f +
        conditionalExpectation outcomes given weight g := by
  unfold conditionalExpectation
  rw [expectation_add]
  ring

theorem conditionalExpectation_sub (outcomes given : Finset Ω)
    (weight f g : Ω → ℝ) :
    conditionalExpectation outcomes given weight (fun ω ↦ f ω - g ω) =
      conditionalExpectation outcomes given weight f -
        conditionalExpectation outcomes given weight g := by
  unfold conditionalExpectation
  rw [expectation_sub]
  ring

theorem conditionalExpectation_const_mul (outcomes given : Finset Ω)
    (weight f : Ω → ℝ) (c : ℝ) :
    conditionalExpectation outcomes given weight (fun ω ↦ c * f ω) =
      c * conditionalExpectation outcomes given weight f := by
  unfold conditionalExpectation
  rw [expectation_const_mul]
  ring

theorem conditionalExpectation_mul_const (outcomes given : Finset Ω)
    (weight f : Ω → ℝ) (c : ℝ) :
    conditionalExpectation outcomes given weight (fun ω ↦ f ω * c) =
      conditionalExpectation outcomes given weight f * c := by
  simpa [mul_comm] using conditionalExpectation_const_mul outcomes given weight f c

theorem conditionalExpectation_sum [DecidableEq ι] (outcomes given : Finset Ω)
    (weight : Ω → ℝ) (indices : Finset ι) (f : ι → Ω → ℝ) :
    conditionalExpectation outcomes given weight (fun ω ↦ ∑ i ∈ indices, f i ω) =
      ∑ i ∈ indices, conditionalExpectation outcomes given weight (f i) := by
  classical
  unfold conditionalExpectation expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_div]

/-! ## Indicators and unbiased reweighting -/

theorem expectation_indicator (outcomes event : Finset Ω) (weight : Ω → ℝ) :
    expectation outcomes weight (fun ω ↦ if ω ∈ event then 1 else 0) =
      conditioningMass outcomes event weight := by
  classical
  unfold expectation conditioningMass conditioningSet
  simp [Finset.sum_filter]

theorem conditionalExpectation_indicator (outcomes given event : Finset Ω)
    (weight : Ω → ℝ) :
    conditionalExpectation outcomes given weight
        (fun ω ↦ if ω ∈ event then 1 else 0) =
      conditioningMass outcomes (given ∩ event) weight /
        conditioningMass outcomes given weight := by
  classical
  unfold conditionalExpectation
  rw [expectation_indicator]
  congr 1
  unfold conditioningMass conditioningSet
  congr 1
  ext ω
  simp [and_left_comm, and_assoc]

theorem conditionalProbability_eq_mass_div (outcomes given event : Finset Ω)
    (weight : Ω → ℝ) :
    conditionalProbability outcomes given event weight =
      conditioningMass outcomes (given ∩ event) weight /
        conditioningMass outcomes given weight := by
  exact conditionalExpectation_indicator outcomes given event weight

/-- Dividing an event indicator by its conditional probability produces an
unbiased random variable. -/
theorem conditionalExpectation_unbiased_indicator
    (outcomes given event : Finset Ω) (weight : Ω → ℝ) (c : ℝ)
    (_hmass : conditioningMass outcomes given weight ≠ 0)
    (hprob : conditionalProbability outcomes given event weight ≠ 0) :
    conditionalExpectation outcomes given weight
        (fun ω ↦ c * (if ω ∈ event then 1 else 0) /
          conditionalProbability outcomes given event weight) = c := by
  rw [show (fun ω ↦ c * (if ω ∈ event then 1 else 0) /
      conditionalProbability outcomes given event weight) =
      (fun ω ↦ (c / conditionalProbability outcomes given event weight) *
        (if ω ∈ event then 1 else 0)) by
        funext ω
        ring]
  rw [conditionalExpectation_const_mul]
  change (c / conditionalProbability outcomes given event weight) *
      conditionalProbability outcomes given event weight = c
  exact div_mul_cancel₀ c hprob

/-- A finite sum of inverse-probability-weighted indicators is unbiased
term-by-term.  This is the form used for random restricted edge weights. -/
theorem conditionalExpectation_unbiased_sum [DecidableEq ι]
    (outcomes given : Finset Ω) (weight : Ω → ℝ) (indices : Finset ι)
    (event : ι → Finset Ω) (coefficient : ι → ℝ)
    (hmass : conditioningMass outcomes given weight ≠ 0)
    (hprob : ∀ i ∈ indices,
      conditionalProbability outcomes given (event i) weight ≠ 0) :
    conditionalExpectation outcomes given weight
        (fun ω ↦ ∑ i ∈ indices,
          coefficient i * (if ω ∈ event i then 1 else 0) /
            conditionalProbability outcomes given (event i) weight) =
      ∑ i ∈ indices, coefficient i := by
  rw [conditionalExpectation_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact conditionalExpectation_unbiased_indicator outcomes given (event i)
    weight (coefficient i) hmass (hprob i hi)

/-! ## Order and Jensen -/

/-- A pointwise inequality on the conditioning event transfers to conditional
expectations. -/
theorem conditionalExpectation_mono (outcomes given : Finset Ω)
    (weight f g : Ω → ℝ)
    (hweight : ∀ ω ∈ outcomes, 0 ≤ weight ω)
    (hmass : 0 < conditioningMass outcomes given weight)
    (hfg : ∀ ω ∈ conditioningSet outcomes given, f ω ≤ g ω) :
    conditionalExpectation outcomes given weight f ≤
      conditionalExpectation outcomes given weight g := by
  unfold conditionalExpectation expectation
  apply (div_le_div_iff_of_pos_right hmass).2
  apply Finset.sum_le_sum
  intro ω hω
  exact mul_le_mul_of_nonneg_left (hfg ω hω)
    (hweight ω (conditioningSet_subset_left outcomes given hω))

theorem conditionalExpectation_nonneg (outcomes given : Finset Ω)
    (weight f : Ω → ℝ)
    (hweight : ∀ ω ∈ outcomes, 0 ≤ weight ω)
    (hmass : 0 < conditioningMass outcomes given weight)
    (hf : ∀ ω ∈ conditioningSet outcomes given, 0 ≤ f ω) :
    0 ≤ conditionalExpectation outcomes given weight f := by
  simpa using conditionalExpectation_mono outcomes given weight (fun _ ↦ 0) f
    hweight hmass (fun ω hω ↦ hf ω hω)

/-- Jensen's inequality for the square function, proved from finite weighted
Cauchy--Schwarz. -/
theorem sq_conditionalExpectation_le (outcomes given : Finset Ω)
    (weight f : Ω → ℝ)
    (hweight : ∀ ω ∈ outcomes, 0 ≤ weight ω)
    (hmass : 0 < conditioningMass outcomes given weight) :
    conditionalExpectation outcomes given weight f ^ 2 ≤
      conditionalExpectation outcomes given weight (fun ω ↦ f ω ^ 2) := by
  let s := conditioningSet outcomes given
  let Z := conditioningMass outcomes given weight
  let S := ∑ ω ∈ s, weight ω * f ω ^ 2
  have hw : ∀ ω ∈ s, 0 ≤ weight ω := fun ω hω ↦
    hweight ω (conditioningSet_subset_left outcomes given hω)
  have hcauchy : (∑ ω ∈ s, weight ω * f ω) ^ 2 ≤ Z * S := by
    simpa [Z, S, conditioningMass] using
      FiniteAnalysis.weighted_sum_sq_le s weight f hw
  have hZsq : 0 < Z ^ 2 := sq_pos_of_pos hmass
  unfold conditionalExpectation expectation
  change ((∑ ω ∈ s, weight ω * f ω) / Z) ^ 2 ≤ S / Z
  rw [div_pow]
  apply (div_le_iff₀ hZsq).2
  have hrewrite : S / Z * Z ^ 2 = Z * S := by
    field_simp [hmass.ne']
  rw [hrewrite]
  exact hcauchy

/-! ## Interchanging expectation and degree sums -/

/-- Conditional expectation commutes with the finite cross-degree sum which
appears when expanding a quadratic Janson energy. -/
theorem conditionalExpectation_crossDegree_sum [DecidableEq ι]
    (outcomes given : Finset Ω) (weight : Ω → ℝ) (sets : Finset ι)
    (kernel fixedDegree : ι → ℝ) (randomDegree : Ω → ι → ℝ) :
    conditionalExpectation outcomes given weight
        (fun ω ↦ ∑ L ∈ sets,
          kernel L * fixedDegree L * randomDegree ω L) =
      ∑ L ∈ sets, kernel L * fixedDegree L *
        conditionalExpectation outcomes given weight
          (fun ω ↦ randomDegree ω L) := by
  rw [conditionalExpectation_sum]
  apply Finset.sum_congr rfl
  intro L hL
  rw [conditionalExpectation_const_mul]

/-- Substitute unbiased expected degrees in the preceding identity. -/
theorem conditionalExpectation_crossDegree_sum_of_unbiased [DecidableEq ι]
    (outcomes given : Finset Ω) (weight : Ω → ℝ) (sets : Finset ι)
    (kernel fixedDegree baseDegree : ι → ℝ) (randomDegree : Ω → ι → ℝ)
    (scale : ℝ)
    (hunbiased : ∀ L ∈ sets,
      conditionalExpectation outcomes given weight
        (fun ω ↦ randomDegree ω L) = scale * baseDegree L) :
    conditionalExpectation outcomes given weight
        (fun ω ↦ ∑ L ∈ sets,
          kernel L * fixedDegree L * randomDegree ω L) =
      scale * ∑ L ∈ sets, kernel L * fixedDegree L * baseDegree L := by
  rw [conditionalExpectation_crossDegree_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro L hL
  rw [hunbiased L hL]
  ring

end FiniteExpectation
end Erdos565
