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

import ErdosProblems.Erdos1165.Basic
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Finite screening lemmas for Erdős Problem 1165

This file isolates the finite combinatorics in the three screening rounds of
Hao--Li--Okada--Zheng.  It deliberately makes no claim about the law of planar
random walk.  The inputs which must eventually come from that law are visible
as inequalities between measures or urn masses.

The three rounds represented here are:

1. a union bound over a finite family of candidate sites (the balancing
   screen);
2. partition into local-time deficit shells, followed by deterministic
   propagation of adjacent-shell occupancy bounds;
3. a near-window mass-ratio estimate and a union bound over the surviving
   candidates.

Thus every declaration below is either a finite-set identity, an elementary
ordered-semiring calculation, or finite subadditivity of a measure.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.Screening

/-! ## Shell partitions and occupancies -/

section Shells

variable {Site Shell : Type*} [DecidableEq Shell]

/-- The candidates with shell label `i`.  In the HLOZ application, `label x`
is the strip containing the local-time deficit `m - xi(x,T_m^k)`. -/
def shell (candidates : Finset Site) (label : Site → Shell) (i : Shell) : Finset Site :=
  candidates.filter fun x ↦ label x = i

@[simp] lemma mem_shell {candidates : Finset Site} {label : Site → Shell}
    {i : Shell} {x : Site} :
    x ∈ shell candidates label i ↔ x ∈ candidates ∧ label x = i := by
  simp [shell]

/-- Distinct fibers of the shell-label map are disjoint. -/
lemma shell_disjoint {candidates : Finset Site} {label : Site → Shell}
    {i j : Shell} (hij : i ≠ j) :
    Disjoint (shell candidates label i) (shell candidates label j) := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  exact hij ((mem_shell.mp hxi).2.symm.trans (mem_shell.mp hxj).2)

/-- Every candidate occurs in the shell carrying its label. -/
lemma mem_shell_self (candidates : Finset Site) (label : Site → Shell)
    {x : Site} (hx : x ∈ candidates) :
    x ∈ shell candidates label (label x) := by
  simp [shell, hx]

/-- A finite list of shell labels covers the candidates exactly when every
candidate has a label in that list. -/
lemma biUnion_shell_eq (candidates : Finset Site) (label : Site → Shell)
    [DecidableEq Site] (indices : Finset Shell)
    (hcover : ∀ x ∈ candidates, label x ∈ indices) :
    indices.biUnion (shell candidates label) = candidates := by
  ext x
  simp only [Finset.mem_biUnion, mem_shell]
  constructor
  · rintro ⟨i, hi, hx, -⟩
    exact hx
  · intro hx
    exact ⟨label x, hcover x hx, hx, rfl⟩

/-- Shell occupancies sum to the number of candidates. -/
lemma sum_card_shell_eq (candidates : Finset Site) (label : Site → Shell)
    [DecidableEq Site] (indices : Finset Shell)
    (hcover : ∀ x ∈ candidates, label x ∈ indices) :
    ∑ i ∈ indices, (shell candidates label i).card = candidates.card := by
  rw [← Finset.card_biUnion]
  · exact congrArg Finset.card (biUnion_shell_eq candidates label indices hcover)
  · intro i hi j hj hij
    exact shell_disjoint hij

/-- The standard deficit-strip label.  Deficit `d` is assigned to the strip
of width `width` whose zero-based index is `d / width`.  We keep this function
total; the analytic application separately proves `0 < width`. -/
def deficitShellIndex (width deficit : ℕ) : ℕ := deficit / width

/-- Candidates grouped into deterministic deficit strips. -/
def deficitShells (candidates : Finset Site) (deficit : Site → ℕ)
    (width index : ℕ) : Finset Site :=
  shell candidates (fun x ↦ deficitShellIndex width (deficit x)) index

@[simp] lemma mem_deficitShells {candidates : Finset Site} {deficit : Site → ℕ}
    {width index : ℕ} {x : Site} :
    x ∈ deficitShells candidates deficit width index ↔
      x ∈ candidates ∧ deficit x / width = index := by
  simp [deficitShells, deficitShellIndex]

end Shells

/-! ## A reusable finite union bound (screening round one) -/

section UnionBound

variable {Ω Candidate : Type*} [MeasurableSpace Ω]

/-- The event that at least one member of a finite candidate family is bad. -/
def someCandidateBad (candidates : Finset Candidate) (bad : Candidate → Set Ω) : Set Ω :=
  {ω | ∃ x ∈ candidates, ω ∈ bad x}

omit [MeasurableSpace Ω] in
lemma someCandidateBad_eq_iUnion (candidates : Finset Candidate)
    (bad : Candidate → Set Ω) :
    someCandidateBad candidates bad = ⋃ x ∈ candidates, bad x := by
  ext ω
  simp [someCandidateBad]

/-- Finite subadditivity, stated in the form used to discard all imbalanced
candidate sites at once. -/
theorem measure_someCandidateBad_le_sum (μ : Measure Ω)
    (candidates : Finset Candidate) (bad : Candidate → Set Ω) :
    μ (someCandidateBad candidates bad) ≤ ∑ x ∈ candidates, μ (bad x) := by
  rw [someCandidateBad_eq_iUnion]
  exact measure_biUnion_finset_le candidates bad

/-- If each of at most `J` candidates fails with cost at most `q`, their
union has cost at most `J*q`.  This is the finite union bound used in both the
balancing screen and the final near-window screen. -/
theorem measure_someCandidateBad_le_card_mul (μ : Measure Ω)
    (candidates : Finset Candidate) (bad : Candidate → Set Ω) (q : ℝ≥0∞)
    (hbad : ∀ x ∈ candidates, μ (bad x) ≤ q) :
    μ (someCandidateBad candidates bad) ≤ (candidates.card : ℝ≥0∞) * q := by
  refine (measure_someCandidateBad_le_sum μ candidates bad).trans ?_
  calc
    ∑ x ∈ candidates, μ (bad x) ≤ ∑ _x ∈ candidates, q :=
      Finset.sum_le_sum fun x hx ↦ hbad x hx
    _ = (candidates.card : ℝ≥0∞) * q := by simp

/-- Version with an externally verified cardinality bound. -/
theorem measure_someCandidateBad_le_budget (μ : Measure Ω)
    (candidates : Finset Candidate) (bad : Candidate → Set Ω)
    (J : ℕ) (q : ℝ≥0∞) (hcard : candidates.card ≤ J)
    (hbad : ∀ x ∈ candidates, μ (bad x) ≤ q) :
    μ (someCandidateBad candidates bad) ≤ (J : ℝ≥0∞) * q := by
  refine (measure_someCandidateBad_le_card_mul μ candidates bad q hbad).trans ?_
  have hcard' : (candidates.card : ℝ≥0∞) ≤ (J : ℝ≥0∞) := by
    exact_mod_cast hcard
  simpa [mul_comm] using mul_le_mul_right hcard' q

end UnionBound

/-! ## Adjacent-shell occupancy growth (screening round two) -/

section Growth

/-- A one-step adjacent-shell growth bound propagates geometrically. -/
theorem occupancy_le_geometric {occupancy : ℕ → ℕ} {C : ℕ}
    (hgrow : ∀ j, occupancy (j + 1) ≤ C * occupancy j) (j : ℕ) :
    occupancy j ≤ C ^ j * occupancy 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc
        occupancy (j + 1) ≤ C * occupancy j := hgrow j
        _ ≤ C * (C ^ j * occupancy 0) := Nat.mul_le_mul_left C ih
        _ = C ^ (j + 1) * occupancy 0 := by simp [pow_succ, mul_assoc, mul_comm]

/-- Summing the shellwise geometric bounds controls total occupancy. -/
theorem sum_occupancy_le_geometric {occupancy : ℕ → ℕ} {C N : ℕ}
    (hgrow : ∀ j, occupancy (j + 1) ≤ C * occupancy j) :
    ∑ j ∈ Finset.range (N + 1), occupancy j ≤
      occupancy 0 * ∑ j ∈ Finset.range (N + 1), C ^ j := by
  calc
    ∑ j ∈ Finset.range (N + 1), occupancy j ≤
        ∑ j ∈ Finset.range (N + 1), C ^ j * occupancy 0 :=
      Finset.sum_le_sum fun j _ ↦ occupancy_le_geometric hgrow j
    _ = occupancy 0 * ∑ j ∈ Finset.range (N + 1), C ^ j := by
      simp [Finset.mul_sum, mul_comm]

/-- A cruder but often more convenient growth bound: there are `N+1`
shells and each is at most the last geometric scale. -/
theorem sum_occupancy_le_shellCount_mul {occupancy : ℕ → ℕ} {C N : ℕ}
    (hC : 1 ≤ C) (hgrow : ∀ j, occupancy (j + 1) ≤ C * occupancy j) :
    ∑ j ∈ Finset.range (N + 1), occupancy j ≤
      (N + 1) * (C ^ N * occupancy 0) := by
  calc
    ∑ j ∈ Finset.range (N + 1), occupancy j ≤
        ∑ _j ∈ Finset.range (N + 1), C ^ N * occupancy 0 := by
      apply Finset.sum_le_sum
      intro j hj
      have hjN : j ≤ N := by simpa using (Finset.mem_range.mp hj)
      exact (occupancy_le_geometric hgrow j).trans
        (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hC hjN))
    _ = (N + 1) * (C ^ N * occupancy 0) := by simp

end Growth

section GrowthEvents

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Failure of the adjacent-shell growth comparison at one interface. -/
def growthFailure (occupancy : Ω → ℕ → ℕ) (C j : ℕ) : Set Ω :=
  {ω | C * occupancy ω j < occupancy ω (j + 1)}

/-- Failure at one of the first `N` shell interfaces. -/
def someGrowthFailure (occupancy : Ω → ℕ → ℕ) (C N : ℕ) : Set Ω :=
  {ω | ∃ j < N, ω ∈ growthFailure occupancy C j}

omit [MeasurableSpace Ω] in
lemma someGrowthFailure_eq_iUnion (occupancy : Ω → ℕ → ℕ) (C N : ℕ) :
    someGrowthFailure occupancy C N =
      ⋃ j ∈ Finset.range N, growthFailure occupancy C j := by
  ext ω
  simp [someGrowthFailure]

/-- Union bound for all adjacent-shell comparisons. -/
theorem measure_someGrowthFailure_le_sum (μ : Measure Ω)
    (occupancy : Ω → ℕ → ℕ) (C N : ℕ) :
    μ (someGrowthFailure occupancy C N) ≤
      ∑ j ∈ Finset.range N, μ (growthFailure occupancy C j) := by
  rw [someGrowthFailure_eq_iUnion]
  exact measure_biUnion_finset_le (Finset.range N) (growthFailure occupancy C)

/-- Uniform adjacent-shell failure costs give the expected `N*q` bound. -/
theorem measure_someGrowthFailure_le_mul (μ : Measure Ω)
    (occupancy : Ω → ℕ → ℕ) (C N : ℕ) (q : ℝ≥0∞)
    (hfail : ∀ j < N, μ (growthFailure occupancy C j) ≤ q) :
    μ (someGrowthFailure occupancy C N) ≤ (N : ℝ≥0∞) * q := by
  refine (measure_someGrowthFailure_le_sum μ occupancy C N).trans ?_
  calc
    ∑ j ∈ Finset.range N, μ (growthFailure occupancy C j) ≤
        ∑ _j ∈ Finset.range N, q :=
      Finset.sum_le_sum fun j hj ↦ hfail j (Finset.mem_range.mp hj)
    _ = (N : ℝ≥0∞) * q := by simp

omit [MeasurableSpace Ω] in
/-- Outside the failure union, every one of the first `N` growth comparisons
holds. -/
theorem growth_le_of_notMem_someGrowthFailure
    (occupancy : Ω → ℕ → ℕ) (C N : ℕ) {ω : Ω}
    (hgood : ω ∉ someGrowthFailure occupancy C N) {j : ℕ} (hj : j < N) :
    occupancy ω (j + 1) ≤ C * occupancy ω j := by
  by_contra hnot
  apply hgood
  exact ⟨j, hj, Nat.lt_of_not_ge hnot⟩

end GrowthEvents

/-! ## Urn mass ratios and the near-window screen (round three) -/

section Ratios

/-- If upper-window mass is at most `rho` times lower-window mass, its
conditional proportion inside the union of the two windows is at most `rho`.
This deliberately weak form is exactly what the final candidate union bound
needs. -/
theorem upper_ratio_le_rho {upper lower rho : ℝ}
    (hupper : 0 ≤ upper) (hlower : 0 < lower) (hrho : 0 ≤ rho)
    (hmass : upper ≤ rho * lower) :
    upper / (upper + lower) ≤ rho := by
  rw [div_le_iff₀ (add_pos_of_nonneg_of_pos hupper hlower)]
  nlinarith

/-- The sharp adjacent-urn normalization used in the exponential screen. -/
theorem upper_ratio_le_normalized {upper lower C : ℝ}
    (hupper : 0 ≤ upper) (hlower : 0 < lower) (hC : 0 ≤ C)
    (hmass : upper ≤ C * lower) :
    upper / (upper + lower) ≤ C / (C + 1) := by
  apply (div_le_div_iff₀ (add_pos_of_nonneg_of_pos hupper hlower) (by linarith)).2
  nlinarith

/-- All `h` balls choosing the upper urn costs at most the `h`-th power of
the normalized adjacent-mass ratio. -/
theorem all_upper_cost {upper lower C : ℝ} {h : ℕ}
    (hupper : 0 ≤ upper) (hlower : 0 < lower) (hC : 0 ≤ C)
    (hmass : upper ≤ C * lower) :
    (upper / (upper + lower)) ^ h ≤ (C / (C + 1)) ^ h := by
  exact pow_le_pow_left₀ (div_nonneg hupper (add_nonneg hupper hlower.le))
    (upper_ratio_le_normalized hupper hlower hC hmass) h

/-- The elementary binomial coefficient bound underlying the two-window urn
screen: choosing `j` exceptional balls among `ell` costs at most `ell^j`. -/
theorem choose_mul_pow_le {ell j : ℕ} {q : ℝ}
    (hq : 0 ≤ q) :
    (ell.choose j : ℝ) * q ^ j ≤ (ell * q) ^ j := by
  have hchoose : (ell.choose j : ℝ) ≤ ell ^ j := by
    exact_mod_cast Nat.choose_le_pow ell j
  calc
    (ell.choose j : ℝ) * q ^ j ≤ (ell : ℝ) ^ j * q ^ j :=
      mul_le_mul_of_nonneg_right hchoose (pow_nonneg hq j)
    _ = (ell * q) ^ j := by rw [mul_pow]

/-- Replacing the actual candidate count `ell` by a verified budget `J`. -/
theorem choose_mul_pow_le_budget {ell J j : ℕ} {q : ℝ}
    (hq : 0 ≤ q) (hell : ell ≤ J) :
    (ell.choose j : ℝ) * q ^ j ≤ (J * q) ^ j := by
  refine (choose_mul_pow_le hq).trans ?_
  exact pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hq)
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hell) hq) j

/-- A ratio of the form `upper ≤ C*(g/f)*lower` yields the near-window
conditional probability bound used by HLOZ.  The positivity assumptions are
kept explicit because in the random-walk application they come from the
local/moderate-deviation estimate. -/
theorem nearWindow_ratio {upper lower C g f : ℝ}
    (hupper : 0 ≤ upper) (hlower : 0 < lower) (hC : 0 ≤ C)
    (hg : 0 ≤ g) (hf : 0 < f)
    (hmass : upper ≤ (C * (g / f)) * lower) :
    upper / (upper + lower) ≤ C * (g / f) := by
  apply upper_ratio_le_rho hupper hlower
  · exact mul_nonneg hC (div_nonneg hg hf.le)
  · exact hmass

end Ratios

section NearWindow

variable {Ω Candidate : Type*} [MeasurableSpace Ω]

/-- The finite probabilistic conclusion of the near-window screen.  Once
conditioning on the external data has produced a fixed candidate set and a
per-candidate upper-window bound, no independence is needed: finite
subadditivity gives the result. -/
theorem nearWindow_union_bound (μ : Measure Ω)
    (candidates : Finset Candidate) (near : Candidate → Set Ω)
    (J : ℕ) (q : ℝ≥0∞) (hcard : candidates.card ≤ J)
    (hnear : ∀ x ∈ candidates, μ (near x) ≤ q) :
    μ {ω | ∃ x ∈ candidates, ω ∈ near x} ≤ (J : ℝ≥0∞) * q := by
  exact measure_someCandidateBad_le_budget μ candidates near J q hcard hnear

end NearWindow

/-! ## Composition of the three finite screens -/

section ThreeRounds

variable {Ω BalanceCandidate NearCandidate : Type*} [MeasurableSpace Ω]

/-- The union of the failures of the balancing, adjacent-shell-growth, and
near-window screening rounds. -/
def threeRoundFailure
    (balanceCandidates : Finset BalanceCandidate) (balanceBad : BalanceCandidate → Set Ω)
    (occupancy : Ω → ℕ → ℕ) (C N : ℕ)
    (nearCandidates : Finset NearCandidate) (near : NearCandidate → Set Ω) : Set Ω :=
  someCandidateBad balanceCandidates balanceBad ∪
    (someGrowthFailure occupancy C N ∪
      someCandidateBad nearCandidates near)

/-- The checked finite endgame for all three screens.  Each hypothesis is an
explicit numerical input: a candidate-count budget and a one-candidate cost
for rounds one and three, and a one-interface cost for round two. -/
theorem measure_threeRoundFailure_le
    (μ : Measure Ω)
    (balanceCandidates : Finset BalanceCandidate) (balanceBad : BalanceCandidate → Set Ω)
    (balanceBudget : ℕ) (balanceCost : ℝ≥0∞)
    (hbalanceCard : balanceCandidates.card ≤ balanceBudget)
    (hbalance : ∀ x ∈ balanceCandidates, μ (balanceBad x) ≤ balanceCost)
    (occupancy : Ω → ℕ → ℕ) (C N : ℕ) (growthCost : ℝ≥0∞)
    (hgrowth : ∀ j < N, μ (growthFailure occupancy C j) ≤ growthCost)
    (nearCandidates : Finset NearCandidate) (near : NearCandidate → Set Ω)
    (nearBudget : ℕ) (nearCost : ℝ≥0∞)
    (hnearCard : nearCandidates.card ≤ nearBudget)
    (hnear : ∀ x ∈ nearCandidates, μ (near x) ≤ nearCost) :
    μ (threeRoundFailure balanceCandidates balanceBad occupancy C N nearCandidates near) ≤
      (balanceBudget : ℝ≥0∞) * balanceCost +
        (N : ℝ≥0∞) * growthCost + (nearBudget : ℝ≥0∞) * nearCost := by
  unfold threeRoundFailure
  calc
    μ (someCandidateBad balanceCandidates balanceBad ∪
        (someGrowthFailure occupancy C N ∪ someCandidateBad nearCandidates near)) ≤
        μ (someCandidateBad balanceCandidates balanceBad) +
          μ (someGrowthFailure occupancy C N ∪ someCandidateBad nearCandidates near) :=
      measure_union_le _ _
    _ ≤ μ (someCandidateBad balanceCandidates balanceBad) +
        (μ (someGrowthFailure occupancy C N) + μ (someCandidateBad nearCandidates near)) :=
      add_le_add (le_refl _) (measure_union_le _ _)
    _ ≤ (balanceBudget : ℝ≥0∞) * balanceCost +
        ((N : ℝ≥0∞) * growthCost + (nearBudget : ℝ≥0∞) * nearCost) :=
      add_le_add
        (measure_someCandidateBad_le_budget μ balanceCandidates balanceBad
          balanceBudget balanceCost hbalanceCard hbalance)
        (add_le_add
          (measure_someGrowthFailure_le_mul μ occupancy C N growthCost hgrowth)
          (measure_someCandidateBad_le_budget μ nearCandidates near
            nearBudget nearCost hnearCard hnear))
    _ = (balanceBudget : ℝ≥0∞) * balanceCost +
        (N : ℝ≥0∞) * growthCost + (nearBudget : ℝ≥0∞) * nearCost := by
      rw [add_assoc]

omit [MeasurableSpace Ω] in
/-- Pointwise complement of the combined bad event exposes every checked
consequence required downstream. -/
theorem notMem_threeRoundFailure_iff
    (balanceCandidates : Finset BalanceCandidate) (balanceBad : BalanceCandidate → Set Ω)
    (occupancy : Ω → ℕ → ℕ) (C N : ℕ)
    (nearCandidates : Finset NearCandidate) (near : NearCandidate → Set Ω) {ω : Ω} :
    ω ∉ threeRoundFailure balanceCandidates balanceBad occupancy C N nearCandidates near ↔
      (∀ x ∈ balanceCandidates, ω ∉ balanceBad x) ∧
      (∀ j < N, occupancy ω (j + 1) ≤ C * occupancy ω j) ∧
      (∀ x ∈ nearCandidates, ω ∉ near x) := by
  simp [threeRoundFailure, someCandidateBad, someGrowthFailure, growthFailure, not_lt]

end ThreeRounds

end Erdos1165.Screening
