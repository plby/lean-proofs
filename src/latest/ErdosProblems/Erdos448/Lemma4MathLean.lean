import ErdosProblems.Erdos448.Basic

namespace Erdos448Lemma4Scratch

open Filter
open scoped Topology BigOperators

/-!
This scratch file isolates the finite/divisor-mass part of Erdős--Tenenbaum
Lemma 4 after specializing `σ = θ = 2` and `ε = 1/5`.

The only unproved analytic input is stated as an ordinary theorem hypothesis:
an eventual first-moment estimate for the fraction of rejected divisors.  The
rest of the argument, including the exact `1/20 -> 1/4` Markov calculation,
is proved below.
-/

/-- `Ω(d,u)`: prime factors of `d` below the real cutoff `u`, counted with
multiplicity.  Using `primeFactorsList` makes this a genuinely finite count. -/
noncomputable def omegaBelowReal (d : ℕ) (u : ℝ) : ℕ := by
  classical
  exact (d.primeFactorsList.filter fun p ↦ (p : ℝ) < u).length

/-- The logarithmic grid used in the proof of Erdős--Tenenbaum Lemma 4:
`u_k = exp (e^k log 2 log ξ)` after specializing `σ = 2`. -/
noncomputable def etGridCutoff (ξ : ℝ) (k : ℕ) : ℝ :=
  Real.exp (Real.exp (k : ℝ) * Real.log 2 * Real.log ξ)

/-- Deviation of `Ω(d,u)` from the normal-order center in Lemma 4. -/
noncomputable def etDeviation (d : ℕ) (u : ℝ) : ℝ :=
  |(omegaBelowReal d u : ℝ) -
    (1 / 2 : ℝ) * Real.log (Real.log u / Real.log 2)|

/-- The exact specialized selected-divisor predicate from the statement of
Erdős--Tenenbaum Lemma 4. -/
def etGoodDivisor (ξ : ℝ) (d : ℕ) : Prop :=
  ∀ u : ℝ,
    Real.exp (Real.log ξ * Real.log 2) < u →
    u < d →
    etDeviation d u <
      (1 / 5 : ℝ) * Real.log (Real.log u / Real.log 2)

/-- The finite grid predicate actually estimated before the interpolation
step in the proof of Lemma 4.  Only `k < d` is inspected.  The grid tolerance
is `0.98 ε = 49/250` for `ε = 1/5`.

For the large values of `ξ` used in the paper, every grid point below `d`
has index `< d`; retaining the implication `u_k < d` makes the predicate
correct without baking that elementary growth fact into the definition. -/
def etGridGoodDivisor (ξ : ℝ) (d : ℕ) : Prop :=
  ∀ k < d,
    etGridCutoff ξ k < d →
    etDeviation d (etGridCutoff ξ k) <
      (49 / 250 : ℝ) *
        Real.log (Real.log (etGridCutoff ξ k) / Real.log 2)

/-- Divisors retained by an arbitrary selection predicate. -/
noncomputable def selectedDivisors (P : ℕ → Prop) (n : ℕ) : Finset ℕ :=
  by
    classical
    exact n.divisors.filter P

/-- Divisors rejected by an arbitrary selection predicate. -/
noncomputable def rejectedDivisors (P : ℕ → Prop) (n : ℕ) : Finset ℕ :=
  by
    classical
    exact n.divisors.filter fun d ↦ ¬ P d

noncomputable def selectedDivisorMass (P : ℕ → Prop) (n : ℕ) : ℕ :=
  (selectedDivisors P n).card

noncomputable def rejectedDivisorMass (P : ℕ → Prop) (n : ℕ) : ℕ :=
  (rejectedDivisors P n).card

theorem selectedDivisors_subset_divisors (P : ℕ → Prop) (n : ℕ) :
    selectedDivisors P n ⊆ n.divisors := by
  classical
  exact Finset.filter_subset _ _

theorem selected_mass_add_rejected_mass (P : ℕ → Prop) (n : ℕ) :
    selectedDivisorMass P n + rejectedDivisorMass P n =
      n.divisors.card := by
  classical
  simpa [selectedDivisorMass, rejectedDivisorMass, selectedDivisors,
    rejectedDivisors] using
    (Finset.card_filter_add_card_filter_not (s := n.divisors) P)

/-- Rejected divisor mass divided by the full divisor mass.  The value at
`n = 0` is set to zero; `0` belongs to every good set below anyway. -/
noncomputable def rejectedFraction (P : ℕ → Prop) (n : ℕ) : ℝ :=
  if n = 0 then 0
  else (rejectedDivisorMass P n : ℝ) / n.divisors.card

theorem rejectedFraction_nonneg (P : ℕ → Prop) (n : ℕ) :
    0 ≤ rejectedFraction P n := by
  simp only [rejectedFraction]
  split_ifs
  · exact le_rfl
  · positivity

/-- The four-fifths good set required by the finite Cauchy--Schwarz step. -/
def fourFifthsGoodSet (P : ℕ → Prop) : Set ℕ :=
  {n : ℕ | 4 * n.divisors.card ≤ 5 * selectedDivisorMass P n}

theorem selected_mass_four_fifths {P : ℕ → Prop} {n : ℕ}
    (hn : n ∈ fourFifthsGoodSet P) :
    4 * n.divisors.card ≤ 5 * selectedDivisorMass P n :=
  hn

/-- The output of Lemma 4 plugs directly into the finite dyadic
Cauchy--Schwarz inequality already proved in the main development. -/
theorem finite_dyadic_reduction_on_fourFifthsGoodSet
    (P : ℕ → Prop) {n : ℕ} (hn0 : n ≠ 0)
    (hn : n ∈ fourFifthsGoodSet P) :
    (4 / 5 : ℝ) * (n.divisors.card : ℝ) / Erdos448.tauPlus n ≤
      1 + 2 *
        (Erdos448.selectedDyadicUnorderedPairCount
          (selectedDivisors P n) : ℝ) /
        (selectedDivisors P n).card := by
  apply Erdos448.four_fifths_tau_div_tauPlus_le_closePairs
    hn0 (selectedDivisors_subset_divisors P n)
  simpa [selectedDivisorMass] using selected_mass_four_fifths hn

/-- Failing the selected-mass inequality forces rejected fraction above
`1/5`.  This is the deterministic core of Lemma 4. -/
theorem compl_fourFifthsGoodSet_subset_superlevel (P : ℕ → Prop) :
    (fourFifthsGoodSet P)ᶜ ⊆
      {n : ℕ | (1 / 5 : ℝ) < rejectedFraction P n} := by
  intro n hn
  have hnot : ¬ 4 * n.divisors.card ≤ 5 * selectedDivisorMass P n := hn
  have hn0 : n ≠ 0 := by
    intro hnzero
    subst n
    simp [selectedDivisorMass, selectedDivisors] at hnot
  have htau : 0 < n.divisors.card :=
    Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn0⟩
  have hpartition := selected_mass_add_rejected_mass P n
  have hrejectedNat : n.divisors.card < 5 * rejectedDivisorMass P n := by
    omega
  have hrejectedReal : (n.divisors.card : ℝ) <
      5 * rejectedDivisorMass P n := by
    exact_mod_cast hrejectedNat
  change (1 / 5 : ℝ) < rejectedFraction P n
  simp only [rejectedFraction, if_neg hn0]
  apply (lt_div_iff₀ (by exact_mod_cast htau : (0 : ℝ) < n.divisors.card)).2
  linarith

/-- Minimal analytic hypothesis for the four-fifths form of Lemma 4.
The estimate `1/20` for the mean rejected fraction, followed by Markov at
threshold `1/5`, gives exceptional upper density at most `1/4`. -/
theorem fourFifthsGoodSet_compl_upperDensity_le_one_fourth
    (P : ℕ → Prop)
    (hmean : ∀ᶠ x : ℕ in atTop,
      (∑ n ∈ Finset.range x, rejectedFraction P n) ≤
        (1 / 20 : ℝ) * x) :
    ((fourFifthsGoodSet P)ᶜ : Set ℕ).upperDensity ≤ 1 / 4 := by
  calc
    ((fourFifthsGoodSet P)ᶜ : Set ℕ).upperDensity ≤
        ({n : ℕ | (1 / 5 : ℝ) < rejectedFraction P n} : Set ℕ).upperDensity :=
      Erdos448.upperDensity_mono
        (compl_fourFifthsGoodSet_subset_superlevel P)
    _ ≤ (1 / 20 : ℝ) / (1 / 5 : ℝ) :=
      Erdos448.upperDensity_superlevel_le
        (rejectedFraction P) (rejectedFraction_nonneg P)
        (by norm_num) hmean
    _ = 1 / 4 := by norm_num

/-- Lemma 4 specialized to the finite grid predicate, conditional only on
the first-moment estimate supplied by the multiplicative mean-value proof. -/
theorem exists_grid_good_set
    (ξ : ℝ)
    (hmean : ∀ᶠ x : ℕ in atTop,
      (∑ n ∈ Finset.range x,
        rejectedFraction (etGridGoodDivisor ξ) n) ≤
          (1 / 20 : ℝ) * x) :
    ∃ G : Set ℕ,
      Gᶜ.upperDensity ≤ 1 / 4 ∧
      ∀ n ∈ G,
        4 * n.divisors.card ≤
          5 * selectedDivisorMass (etGridGoodDivisor ξ) n := by
  refine ⟨fourFifthsGoodSet (etGridGoodDivisor ξ), ?_, ?_⟩
  · exact fourFifthsGoodSet_compl_upperDensity_le_one_fourth _ hmean
  · exact fun n hn ↦ selected_mass_four_fifths hn

/-- The exact full-interval selector follows from the same minimal mean
hypothesis.  This is the form directly consumed by Proposition 1. -/
theorem exists_et_good_set
    (ξ : ℝ)
    (hmean : ∀ᶠ x : ℕ in atTop,
      (∑ n ∈ Finset.range x,
        rejectedFraction (etGoodDivisor ξ) n) ≤
          (1 / 20 : ℝ) * x) :
    ∃ G : Set ℕ,
      Gᶜ.upperDensity ≤ 1 / 4 ∧
      ∀ n ∈ G,
        4 * n.divisors.card ≤
          5 * selectedDivisorMass (etGoodDivisor ξ) n := by
  refine ⟨fourFifthsGoodSet (etGoodDivisor ξ), ?_, ?_⟩
  · exact fourFifthsGoodSet_compl_upperDensity_le_one_fourth _ hmean
  · exact fun n hn ↦ selected_mass_four_fifths hn

end Erdos448Lemma4Scratch
