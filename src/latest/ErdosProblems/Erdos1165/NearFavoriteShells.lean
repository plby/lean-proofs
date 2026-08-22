/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.Screening
import ErdosProblems.Erdos1165.UrnScreening
import Mathlib.Probability.Moments.Basic

/-!
# Finite near-favorite shell screening for Erdős Problem 1165

This module formalizes the finite shell-partition and occupancy-growth engine
in the proof of Hao--Li--Okada--Zheng, Proposition 4.8.  It makes no assertion
about planar random walk.  In particular, balancedness of the external local
time and the conditional binomial domination at an interface remain explicit
inputs.

The main deterministic statement is `totalOverflow_subset_globalBad`.  Given
geometrically compatible shell thresholds, excess total occupancy can only
happen through excess occupancy in the first shell or through a failed
adjacent-shell comparison.  The measure version
`measureReal_totalOverflow_le` combines this inclusion with a sharp finite
union bound.

For the probabilistic input, `binomial_upper_tail_two_pow` proves the elementary
Chernoff bound

`Bin(n,r)[a,∞) ≤ (1+r)^n / 2^a`,

and `adjacent_pair_upper_tail_two_pow` combines it with the adjacent mass-ratio
normalization from `UrnScreening`.  Thus the random-walk development only has
to identify its conditional interface law (or stochastic domination) and
verify the mass-ratio estimate.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory unitInterval

namespace Erdos1165.NearFavoriteShells

/-! ## Finite shell partitions -/

section Partition

variable {Site : Type*}

/-- Candidates whose shell label lies among `0, ..., shellCount - 1`. -/
def boundedCandidates (candidates : Finset Site) (label : Site → ℕ)
    (shellCount : ℕ) : Finset Site :=
  candidates.filter fun x ↦ label x < shellCount

/-- The candidates in one shell. -/
def shellCandidates (candidates : Finset Site) (label : Site → ℕ)
    (j : ℕ) : Finset Site :=
  Screening.shell candidates label j

/-- Occupancy of one shell. -/
def shellOccupancy (candidates : Finset Site) (label : Site → ℕ)
    (j : ℕ) : ℕ :=
  (shellCandidates candidates label j).card

@[simp] lemma mem_boundedCandidates {candidates : Finset Site} {label : Site → ℕ}
    {shellCount : ℕ} {x : Site} :
    x ∈ boundedCandidates candidates label shellCount ↔
      x ∈ candidates ∧ label x < shellCount := by
  simp [boundedCandidates]

@[simp] lemma mem_shellCandidates {candidates : Finset Site} {label : Site → ℕ}
    {j : ℕ} {x : Site} :
    x ∈ shellCandidates candidates label j ↔ x ∈ candidates ∧ label x = j := by
  simp [shellCandidates]

/-- Restricting the candidate set to the displayed shell range does not alter
any shell in that range. -/
lemma shellCandidates_boundedCandidates_eq (candidates : Finset Site)
    (label : Site → ℕ) {shellCount j : ℕ} (hj : j < shellCount) :
    shellCandidates (boundedCandidates candidates label shellCount) label j =
      shellCandidates candidates label j := by
  ext x
  constructor
  · intro hx
    have h := mem_shellCandidates.mp hx
    exact mem_shellCandidates.mpr ⟨(mem_boundedCandidates.mp h.1).1, h.2⟩
  · intro hx
    have h := mem_shellCandidates.mp hx
    apply mem_shellCandidates.mpr
    exact ⟨mem_boundedCandidates.mpr ⟨h.1, h.2 ▸ hj⟩, h.2⟩

/-- The displayed shell occupancies add up exactly to the number of candidates
whose labels lie in the displayed range. -/
theorem sum_shellOccupancy_eq_card_boundedCandidates
    (candidates : Finset Site) (label : Site → ℕ) (shellCount : ℕ) :
    ∑ j ∈ Finset.range shellCount, shellOccupancy candidates label j =
      (boundedCandidates candidates label shellCount).card := by
  classical
  calc
    ∑ j ∈ Finset.range shellCount, shellOccupancy candidates label j =
        ∑ j ∈ Finset.range shellCount,
          shellOccupancy (boundedCandidates candidates label shellCount) label j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [shellOccupancy]
      rw [shellCandidates_boundedCandidates_eq candidates label (Finset.mem_range.mp hj)]
    _ = (boundedCandidates candidates label shellCount).card := by
      exact Screening.sum_card_shell_eq
        (boundedCandidates candidates label shellCount) label
        (Finset.range shellCount) (by
          intro x hx
          exact Finset.mem_range.mpr (mem_boundedCandidates.mp hx).2)

/-- Event-level bridge from the abstract occupancy formulation below to an
actual finite set partitioned by shell labels. -/
lemma mem_total_shell_sum_iff_card_boundedCandidates
    {Ω : Type*} (candidates : Ω → Finset Site) (label : Ω → Site → ℕ)
    (threshold : ℕ → ℕ) (shellCount : ℕ) (ω : Ω) :
    (∑ j ∈ Finset.range shellCount, threshold j <
        ∑ j ∈ Finset.range shellCount,
          shellOccupancy (candidates ω) (label ω) j) ↔
      ∑ j ∈ Finset.range shellCount, threshold j <
        (boundedCandidates (candidates ω) (label ω) shellCount).card := by
  rw [sum_shellOccupancy_eq_card_boundedCandidates]

end Partition

/-! ## Adjacent-binomial upper tails -/

section BinomialTail

/-- The moment-generating identity at the elementary parameter `log 2`,
written without logarithms. -/
lemma integral_two_pow_binomial (n : ℕ) (r : I) :
    ∫ k : ℕ, (2 : ℝ) ^ k ∂Bin(n, r) = (1 + (r : ℝ)) ^ n := by
  rw [ProbabilityTheory.integral_binomial]
  simp only [smul_eq_mul]
  rw [← Nat.range_succ_eq_Iic]
  rw [show (1 + (r : ℝ)) = (r : ℝ) * 2 + (1 - (r : ℝ)) by ring]
  rw [add_pow]
  apply Finset.sum_congr
  · simp
  · intro k hk
    simp only [Finset.mem_range] at hk
    ring

/-- A completely explicit finite Chernoff bound for a binomial upper tail.
It is often stronger and easier to compose than an unspecified `exp (-c n)`
bound. -/
theorem binomial_upper_tail_two_pow (n a : ℕ) (r : I) :
    Bin(n, r).real (Set.Ici a) ≤ (1 + (r : ℝ)) ^ n / (2 : ℝ) ^ a := by
  have hint : Integrable (fun k : ℕ ↦ (2 : ℝ) ^ k) Bin(n, r) :=
    ProbabilityTheory.integrable_binomial _
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := Bin(n, r)) (f := fun k : ℕ ↦ (2 : ℝ) ^ k)
    (ae_of_all _ fun _ ↦ by positivity) hint ((2 : ℝ) ^ a)
  have hevent : {k : ℕ | (2 : ℝ) ^ a ≤ (2 : ℝ) ^ k} = Set.Ici a := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_Ici]
    exact pow_le_pow_iff_right₀ (by norm_num)
  rw [hevent, integral_two_pow_binomial] at hmarkov
  exact (le_div_iff₀' (by positivity : (0 : ℝ) < (2 : ℝ) ^ a)).mpr hmarkov

/-- The mass-ratio form of the preceding tail estimate.  If adjacent shell
masses satisfy `p ≤ C q`, then the conditional upper-shell parameter is at
most `C/(1+C)`. -/
theorem adjacent_pair_upper_tail_two_pow (n a : ℕ) {p q C : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p + q)
    (hC : 0 ≤ C) (hpqC : p ≤ C * q) :
    Bin(n, UrnScreening.pairParameter p q hp hq hpq).real (Set.Ici a) ≤
      (1 + C / (1 + C)) ^ n / (2 : ℝ) ^ a := by
  refine (binomial_upper_tail_two_pow n a
    (UrnScreening.pairParameter p q hp hq hpq)).trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply pow_le_pow_left₀
  · have := (UrnScreening.pairParameter p q hp hq hpq).2.1
    positivity
  · gcongr
    exact UrnScreening.pairParameter_le hp hq hpq hC hpqC

/-- Integer cut corresponding to `upper > G * lower` when the two occupancies
sum to `total`. -/
def growthCut (G total : ℕ) : ℕ := G * total / (G + 1) + 1

/-- An excessive upper-to-lower occupancy ratio forces the upper occupancy
into the tail starting at `growthCut`. -/
lemma growthCut_le_of_ratio {G total upper : ℕ} (hupper : upper ≤ total)
    (hratio : G * (total - upper) < upper) :
    growthCut G total ≤ upper := by
  unfold growthCut
  rw [Nat.add_one_le_iff]
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < G + 1)).2
  calc
    G * total = G * (total - upper) + G * upper := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hupper]
    _ < upper + G * upper := Nat.add_lt_add_right hratio (G * upper)
    _ = upper * (G + 1) := by
      simp [Nat.mul_add, Nat.mul_comm, Nat.add_comm]

/-- The explicit binomial cost of violating the adjacent occupancy comparison
`upper ≤ G * lower`, conditional on a fixed total occupancy. -/
theorem adjacent_pair_growth_tail (total G : ℕ) {p q C : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p + q)
    (hC : 0 ≤ C) (hpqC : p ≤ C * q) :
    Bin(total, UrnScreening.pairParameter p q hp hq hpq).real
        {upper | upper ≤ total ∧ G * (total - upper) < upper} ≤
      (1 + C / (1 + C)) ^ total / (2 : ℝ) ^ growthCut G total := by
  calc
    Bin(total, UrnScreening.pairParameter p q hp hq hpq).real
        {upper | upper ≤ total ∧ G * (total - upper) < upper} ≤
        Bin(total, UrnScreening.pairParameter p q hp hq hpq).real
          (Set.Ici (growthCut G total)) := by
      apply measureReal_mono
      intro upper hupper
      exact growthCut_le_of_ratio hupper.1 hupper.2
      finiteness
    _ ≤ (1 + C / (1 + C)) ^ total / (2 : ℝ) ^ growthCut G total :=
      adjacent_pair_upper_tail_two_pow total (growthCut G total) hp hq hpq hC hpqC

end BinomialTail

/-! ## Geometric threshold propagation -/

section Propagation

variable {Ω : Type*}

/-- A shell exceeds its prescribed threshold. -/
def shellOverflow (occupancy : Ω → ℕ → ℕ) (threshold : ℕ → ℕ)
    (j : ℕ) : Set Ω :=
  {ω | threshold j < occupancy ω j}

/-- The adjacent occupancy comparison fails. -/
def interfaceGrowthFailure (occupancy : Ω → ℕ → ℕ) (G j : ℕ) : Set Ω :=
  {ω | G * occupancy ω j < occupancy ω (j + 1)}

/-- A failed adjacent-shell comparison while the balancing event is present.
This is the part controlled by conditional urn domination. -/
def balancedGrowthFailure (balanced : ℕ → Set Ω)
    (occupancy : Ω → ℕ → ℕ) (G j : ℕ) : Set Ω :=
  balanced j ∩ interfaceGrowthFailure occupancy G j

/-- At an interface, either the balancedness input is unavailable or the
adjacent occupancy comparison fails. -/
def interfaceBad (balanced : ℕ → Set Ω) (occupancy : Ω → ℕ → ℕ)
    (G j : ℕ) : Set Ω :=
  (balanced j)ᶜ ∪ interfaceGrowthFailure occupancy G j

/-- Split an interface failure into the failure of balancedness and the urn
growth failure on the balanced event. -/
lemma interfaceBad_eq_balance_union_growth
    (balanced : ℕ → Set Ω) (occupancy : Ω → ℕ → ℕ) (G j : ℕ) :
    interfaceBad balanced occupancy G j =
      (balanced j)ᶜ ∪ balancedGrowthFailure balanced occupancy G j := by
  ext ω
  simp only [interfaceBad, balancedGrowthFailure, Set.mem_union, Set.mem_compl_iff,
    Set.mem_inter_iff]
  tauto

/-- Some displayed interface is bad. -/
def someInterfaceBad (balanced : ℕ → Set Ω) (occupancy : Ω → ℕ → ℕ)
    (G shellCount : ℕ) : Set Ω :=
  ⋃ j ∈ Finset.range (shellCount - 1), interfaceBad balanced occupancy G j

/-- The complete finite failure event: either the first shell is too large or
one of the displayed interfaces is bad. -/
def globalBad (balanced : ℕ → Set Ω) (occupancy : Ω → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount : ℕ) : Set Ω :=
  shellOverflow occupancy threshold 0 ∪
    someInterfaceBad balanced occupancy G shellCount

/-- The event that the total displayed occupancy exceeds the sum of the
displayed thresholds. -/
def totalOverflow (occupancy : Ω → ℕ → ℕ) (threshold : ℕ → ℕ)
    (shellCount : ℕ) : Set Ω :=
  {ω | ∑ j ∈ Finset.range shellCount, threshold j <
    ∑ j ∈ Finset.range shellCount, occupancy ω j}

lemma mem_someInterfaceBad_iff
    {balanced : ℕ → Set Ω} {occupancy : Ω → ℕ → ℕ}
    {G shellCount : ℕ} {ω : Ω} :
    ω ∈ someInterfaceBad balanced occupancy G shellCount ↔
      ∃ j < shellCount - 1, ω ∈ interfaceBad balanced occupancy G j := by
  simp [someInterfaceBad]

/-- Outside `globalBad`, every displayed shell satisfies its threshold. -/
theorem occupancy_le_threshold_of_notMem_globalBad
    (balanced : ℕ → Set Ω) (occupancy : Ω → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount : ℕ)
    (hstep : ∀ j, j + 1 < shellCount → G * threshold j ≤ threshold (j + 1))
    {ω : Ω} (hgood : ω ∉ globalBad balanced occupancy threshold G shellCount) :
    ∀ j < shellCount, occupancy ω j ≤ threshold j := by
  intro j hj
  induction j with
  | zero =>
      by_contra hnot
      apply hgood
      exact Or.inl (Nat.lt_of_not_ge hnot)
  | succ j ih =>
      have hjlt : j < shellCount := by omega
      have hprev : occupancy ω j ≤ threshold j := ih hjlt
      have hinterface : ω ∉ interfaceBad balanced occupancy G j := by
        intro hbad
        apply hgood
        apply Or.inr
        rw [mem_someInterfaceBad_iff]
        exact ⟨j, by omega, hbad⟩
      have hgrow : occupancy ω (j + 1) ≤ G * occupancy ω j := by
        by_contra hnot
        apply hinterface
        exact Or.inr (Nat.lt_of_not_ge hnot)
      exact hgrow.trans <| (Nat.mul_le_mul_left G hprev).trans (hstep j hj)

/-- The deterministic heart of Proposition 4.8: excess total occupancy is
contained in the finite union of the initial-shell and interface failures. -/
theorem totalOverflow_subset_globalBad
    (balanced : ℕ → Set Ω) (occupancy : Ω → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount : ℕ)
    (hstep : ∀ j, j + 1 < shellCount → G * threshold j ≤ threshold (j + 1)) :
    totalOverflow occupancy threshold shellCount ⊆
      globalBad balanced occupancy threshold G shellCount := by
  intro ω hoverflow
  by_contra hgood
  have hpoint := occupancy_le_threshold_of_notMem_globalBad
    balanced occupancy threshold G shellCount hstep hgood
  have hsum :
      (∑ j ∈ Finset.range shellCount, occupancy ω j) ≤
        ∑ j ∈ Finset.range shellCount, threshold j := by
    exact Finset.sum_le_sum fun j hj ↦ hpoint j (Finset.mem_range.mp hj)
  exact (Nat.not_lt_of_ge hsum) hoverflow

/-- Finite measure bound corresponding to the deterministic shell engine.
No measurability hypotheses are needed for this subadditive estimate. -/
theorem measureReal_totalOverflow_le [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (balanced : ℕ → Set Ω) (occupancy : Ω → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount : ℕ)
    (hstep : ∀ j, j + 1 < shellCount → G * threshold j ≤ threshold (j + 1)) :
    μ.real (totalOverflow occupancy threshold shellCount) ≤
      μ.real (shellOverflow occupancy threshold 0) +
        ∑ j ∈ Finset.range (shellCount - 1),
          μ.real (interfaceBad balanced occupancy G j) := by
  calc
    μ.real (totalOverflow occupancy threshold shellCount) ≤
        μ.real (globalBad balanced occupancy threshold G shellCount) :=
      measureReal_mono (totalOverflow_subset_globalBad
        balanced occupancy threshold G shellCount hstep)
    _ ≤ μ.real (shellOverflow occupancy threshold 0) +
        μ.real (someInterfaceBad balanced occupancy G shellCount) :=
      measureReal_union_le _ _
    _ ≤ μ.real (shellOverflow occupancy threshold 0) +
        ∑ j ∈ Finset.range (shellCount - 1),
          μ.real (interfaceBad balanced occupancy G j) := by
      gcongr
      exact measureReal_biUnion_finset_le (Finset.range (shellCount - 1))
        (interfaceBad balanced occupancy G)

/-- One interface costs at most the balancedness failure plus the conditional
urn-growth failure. -/
theorem measureReal_interfaceBad_le [MeasurableSpace Ω] (μ : Measure Ω)
    (balanced : ℕ → Set Ω) (occupancy : Ω → ℕ → ℕ) (G j : ℕ) :
    μ.real (interfaceBad balanced occupancy G j) ≤
      μ.real (balanced j)ᶜ +
        μ.real (balancedGrowthFailure balanced occupancy G j) := by
  rw [interfaceBad_eq_balance_union_growth]
  exact measureReal_union_le _ _

/-- Budget form of the shell estimate.  These are precisely the finite inputs
produced in HLOZ by the first-shell comparison, balancedness, and conditional
adjacent-binomial domination. -/
theorem measureReal_totalOverflow_le_budget [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (balanced : ℕ → Set Ω) (occupancy : Ω → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount : ℕ)
    (hstep : ∀ j, j + 1 < shellCount → G * threshold j ≤ threshold (j + 1))
    {baseCost : ℝ} {interfaceCost : ℕ → ℝ}
    (hbase : μ.real (shellOverflow occupancy threshold 0) ≤ baseCost)
    (hinterface : ∀ j < shellCount - 1,
      μ.real (interfaceBad balanced occupancy G j) ≤ interfaceCost j) :
    μ.real (totalOverflow occupancy threshold shellCount) ≤
      baseCost + ∑ j ∈ Finset.range (shellCount - 1), interfaceCost j := by
  refine (measureReal_totalOverflow_le μ balanced occupancy threshold G shellCount hstep).trans ?_
  exact add_le_add hbase <|
    Finset.sum_le_sum fun j hj ↦ hinterface j (Finset.mem_range.mp hj)

/-- The finite Proposition 4.8 recurrence with balancedness and conditional
growth costs separated. -/
theorem measureReal_totalOverflow_le_balanced [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (balanced : ℕ → Set Ω) (occupancy : Ω → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount : ℕ)
    (hstep : ∀ j, j + 1 < shellCount → G * threshold j ≤ threshold (j + 1))
    {baseCost : ℝ} {balanceCost growthCost : ℕ → ℝ}
    (hbase : μ.real (shellOverflow occupancy threshold 0) ≤ baseCost)
    (hbalance : ∀ j < shellCount - 1, μ.real (balanced j)ᶜ ≤ balanceCost j)
    (hgrowth : ∀ j < shellCount - 1,
      μ.real (balancedGrowthFailure balanced occupancy G j) ≤ growthCost j) :
    μ.real (totalOverflow occupancy threshold shellCount) ≤
      baseCost + ∑ j ∈ Finset.range (shellCount - 1),
        (balanceCost j + growthCost j) := by
  apply measureReal_totalOverflow_le_budget μ balanced occupancy threshold G shellCount
    hstep hbase
  intro j hj
  exact (measureReal_interfaceBad_le μ balanced occupancy G j).trans <|
    add_le_add (hbalance j hj) (hgrowth j hj)

/-- Strong finite generic form of the shell screen under explicit inputs.

For every interface, `hdom` is the only conditional-law hypothesis: on the
balanced event, its growth-failure probability is dominated by the indicated
two-urn binomial law with fixed conditioned total `pairTotal j`.  The remaining
hypotheses are positivity, the adjacent mass comparison `p j ≤ C j * q j`,
and the balancedness/first-shell costs.  The conclusion displays the complete
finite Chernoff and union-bound cost, without an unspecified asymptotic
constant. -/
theorem measureReal_totalOverflow_le_of_pair_domination
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (balanced : ℕ → Set Ω) (occupancy : Ω → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount : ℕ)
    (pairTotal : ℕ → ℕ) (p q C : ℕ → ℝ)
    (hstep : ∀ j, j + 1 < shellCount → G * threshold j ≤ threshold (j + 1))
    (hp : ∀ j < shellCount - 1, 0 ≤ p j)
    (hq : ∀ j < shellCount - 1, 0 ≤ q j)
    (hpq : ∀ j < shellCount - 1, 0 < p j + q j)
    (hC : ∀ j < shellCount - 1, 0 ≤ C j)
    (hratio : ∀ j < shellCount - 1, p j ≤ C j * q j)
    {baseCost : ℝ} {balanceCost : ℕ → ℝ}
    (hbase : μ.real (shellOverflow occupancy threshold 0) ≤ baseCost)
    (hbalance : ∀ j < shellCount - 1, μ.real (balanced j)ᶜ ≤ balanceCost j)
    (hdom : ∀ (j : ℕ) (hj : j < shellCount - 1),
      μ.real (balancedGrowthFailure balanced occupancy G j) ≤
        Bin(pairTotal j, UrnScreening.pairParameter (p j) (q j)
          (hp j hj) (hq j hj) (hpq j hj)).real
          {upper | upper ≤ pairTotal j ∧
            G * (pairTotal j - upper) < upper}) :
    μ.real (totalOverflow occupancy threshold shellCount) ≤
      baseCost + ∑ j ∈ Finset.range (shellCount - 1),
        (balanceCost j +
          (1 + C j / (1 + C j)) ^ pairTotal j /
            (2 : ℝ) ^ growthCut G (pairTotal j)) := by
  apply measureReal_totalOverflow_le_balanced μ balanced occupancy threshold G shellCount
    hstep hbase hbalance
  intro j hj
  refine (hdom j hj).trans ?_
  exact adjacent_pair_growth_tail (pairTotal j) G
    (hp j hj) (hq j hj) (hpq j hj) (hC j hj) (hratio j hj)

/-- Constant-cost specialization, useful after obtaining uniform estimates at
all adjacent interfaces. -/
theorem measureReal_totalOverflow_le_uniform [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (balanced : ℕ → Set Ω) (occupancy : Ω → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount : ℕ)
    (hstep : ∀ j, j + 1 < shellCount → G * threshold j ≤ threshold (j + 1))
    {baseCost interfaceCost : ℝ}
    (hbase : μ.real (shellOverflow occupancy threshold 0) ≤ baseCost)
    (hinterface : ∀ j < shellCount - 1,
      μ.real (interfaceBad balanced occupancy G j) ≤ interfaceCost) :
    μ.real (totalOverflow occupancy threshold shellCount) ≤
      baseCost + ((shellCount - 1 : ℕ) : ℝ) * interfaceCost := by
  simpa using measureReal_totalOverflow_le_budget μ balanced occupancy threshold G shellCount
    hstep hbase hinterface

end Propagation

end Erdos1165.NearFavoriteShells
