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

import ErdosProblems.Erdos1165.ThickPoint
import ErdosProblems.Erdos1165.Markov
import ErdosProblems.Erdos1165.NegativeBinomial
import ErdosProblems.Erdos1165.Annulus

/-!
# Excursion-count transition kernels in the HLOZ appendix

Hao--Li--Okada--Zheng compare the nested-annulus excursion counts with the
upcrossing counts of a one-dimensional Markov jump process.  For an internal
level, each of `a` incoming upcrossings produces an independent geometric
number of outgoing upcrossings, with success probability `1 / 2`.  At the
last level the success probability is

`3 * log n / (1 + 3 * log n)`.

This file supplies the exact part of that assertion.

* `OffspringPattern a b` is the finite weak-composition space recording how
  `b` outgoing upcrossings are split between `a` incoming upcrossings.
* `sum_offspringPattern_weight` proves by an exact finite sum that the total
  mass is the negative-binomial mass from `NegativeBinomial.lean`.
* `transitionLaw` and `hlozTransitionKernel` package the absorbing Markov
  transition as genuine probability mass functions.
* `stopped_finiteExcursionPair_conditional` applies the finite-dimensional
  strong Markov theorem to the *actual* nested-disc statistic.  It proves that
  conditioning on an arbitrary stopped-past event leaves the fresh finite
  planar kernel.

The last item deliberately does not identify the fresh planar kernel with the
one-dimensional negative-binomial kernel.  HLOZ obtain only a multiplicative
comparison: the probability that the planar walk moves between two successive
disc boundaries must be uniformly compared with `1 / 2` (and with the terminal
parameter).  This is the quantitative annular Harnack/potential-kernel input
behind HLOZ (2.5), (A.2), and the comparison following Remark A.5.  Neither
that scale-uniform estimate nor its accumulated `1 + O(n^-3)` error follows
from the exact finite optional-stopping identities in `Annulus.lean`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.ExcursionTransition

noncomputable section

/-! ## Geometric offspring and the finite negative-binomial sum -/

/-- Mass of `q` failures before one success for geometric success parameter
`p`. -/
def geometricOffspringMass (p : ℝ) (q : ℕ) : ℝ :=
  p * (1 - p) ^ q

/-- A weak composition of `b` offspring among `a` parent excursions. -/
abbrev OffspringPattern (a b : ℕ) := Sym (Fin a) b

/-- The number of offspring assigned to the parent indexed by `k`. -/
def offspringMultiplicity {a b : ℕ} (g : OffspringPattern a b) (k : Fin a) : ℕ :=
  g.toMultiset.count k

theorem sum_offspringMultiplicity {a b : ℕ} (g : OffspringPattern a b) :
    ∑ k : Fin a, offspringMultiplicity g k = b := by
  simp [offspringMultiplicity]

@[simp] theorem card_offspringPattern (a b : ℕ) :
    Fintype.card (OffspringPattern a b) = (a + b - 1).choose b := by
  simpa using (Sym.card_sym_eq_choose (α := Fin a) b)

/-- Every weak composition with total `b` has the same product geometric
mass. -/
theorem prod_geometricOffspringMass {a b : ℕ} (p : ℝ)
    (g : OffspringPattern a b) :
    ∏ k : Fin a, geometricOffspringMass p (offspringMultiplicity g k) =
      p ^ a * (1 - p) ^ b := by
  simp only [geometricOffspringMass, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_pow_eq_pow_sum, sum_offspringMultiplicity]

/-- Exact finite conditional-law calculation: summing the independent
geometric product weights over all offspring vectors of total `b` gives the
negative-binomial transition mass. -/
theorem sum_offspringPattern_weight {a : ℕ} (ha : 0 < a) (b : ℕ) (p : ℝ) :
    ∑ g : OffspringPattern a b,
        ∏ k : Fin a, geometricOffspringMass p (offspringMultiplicity g k) =
      NegativeBinomial.mass p a b := by
  simp_rw [prod_geometricOffspringMass]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, card_offspringPattern,
    NegativeBinomial.mass_eq_hloz_formula p ha]
  ring

/-! ## The absorbing negative-binomial Markov kernel -/

/-- The transition mass with success parameter `p`.  State zero is
absorbing; from a positive state this is the negative-binomial law. -/
def transitionMass (p : ℝ) (a b : ℕ) : ℝ :=
  if a = 0 then if b = 0 then 1 else 0 else NegativeBinomial.mass p a b

@[simp] theorem transitionMass_zero_left (p : ℝ) (b : ℕ) :
    transitionMass p 0 b = if b = 0 then 1 else 0 := by
  simp [transitionMass]

@[simp] theorem transitionMass_zero_zero (p : ℝ) : transitionMass p 0 0 = 1 := by
  simp

theorem transitionMass_of_pos (p : ℝ) {a : ℕ} (ha : 0 < a) (b : ℕ) :
    transitionMass p a b = NegativeBinomial.mass p a b := by
  simp [transitionMass, ha.ne']

theorem transitionMass_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (a b : ℕ) : 0 ≤ transitionMass p a b := by
  by_cases ha : a = 0
  · subst a
    rw [transitionMass_zero_left]
    split_ifs <;> norm_num
  · rw [transitionMass, if_neg ha]
    exact NegativeBinomial.mass_nonneg hp0 hp1 a b

theorem hasSum_transitionMass {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (a : ℕ) :
    HasSum (transitionMass p a) 1 := by
  by_cases ha : a = 0
  · subst a
    exact (hasSum_ite_eq 0 (1 : ℝ)).congr fun b ↦ by simp [transitionMass]
  · have h := NegativeBinomial.hasSum_mass hp0 hp1 (Nat.pos_of_ne_zero ha)
    exact HasSum.congr_fun h fun b ↦
      transitionMass_of_pos p (Nat.pos_of_ne_zero ha) b

/-- The transition kernel as a probability mass function on `ℕ`. -/
noncomputable def transitionLaw (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (a : ℕ) : PMF ℕ :=
  if ha : a = 0 then PMF.pure 0
  else NegativeBinomial.law p hp0 hp1 a (Nat.pos_of_ne_zero ha)

@[simp] theorem transitionLaw_apply (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (a b : ℕ) :
    transitionLaw p hp0 hp1 a b = ENNReal.ofReal (transitionMass p a b) := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      simp [transitionLaw]
    · simp [transitionLaw, hb]
  · simp [transitionLaw, transitionMass, ha, NegativeBinomial.law_apply]

@[simp] theorem transitionLaw_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    transitionLaw p hp0 hp1 0 = PMF.pure 0 := by
  simp [transitionLaw]

/-! ## The exact HLOZ level-dependent kernel -/

/-- The terminal geometric success parameter in HLOZ Remark A.5. -/
def terminalSuccess (n : ℕ) : ℝ :=
  3 * Real.log n / (1 + 3 * Real.log n)

theorem terminalSuccess_pos {n : ℕ} (hn : 2 ≤ n) : 0 < terminalSuccess n := by
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
  unfold terminalSuccess
  positivity

theorem terminalSuccess_le_one {n : ℕ} (hn : 2 ≤ n) : terminalSuccess n ≤ 1 := by
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
  unfold terminalSuccess
  apply (div_le_one (by positivity)).2
  linarith

/-- At levels below `n` the auxiliary jump process is symmetric.  At level
`n` it has the terminal success parameter.  The index type ensures these are
the only two cases. -/
def levelSuccess (n : ℕ) (level : Fin (n + 1)) : ℝ :=
  if (level : ℕ) < n then 1 / 2 else terminalSuccess n

theorem levelSuccess_pos {n : ℕ} (hn : 2 ≤ n) (level : Fin (n + 1)) :
    0 < levelSuccess n level := by
  by_cases hlevel : (level : ℕ) < n
  · norm_num [levelSuccess, hlevel]
  · simp [levelSuccess, hlevel, terminalSuccess_pos hn]

theorem levelSuccess_le_one {n : ℕ} (hn : 2 ≤ n) (level : Fin (n + 1)) :
    levelSuccess n level ≤ 1 := by
  by_cases hlevel : (level : ℕ) < n
  · norm_num [levelSuccess, hlevel]
  · simp [levelSuccess, hlevel, terminalSuccess_le_one hn]

/-- The exact upcrossing-count transition kernel in HLOZ Remark A.5. -/
noncomputable def hlozTransitionKernel (n : ℕ) (hn : 2 ≤ n)
    (level : Fin (n + 1)) : ℕ → PMF ℕ :=
  transitionLaw (levelSuccess n level) (levelSuccess_pos hn level)
    (levelSuccess_le_one hn level)

@[simp] theorem hlozTransitionKernel_apply (n : ℕ) (hn : 2 ≤ n)
    (level : Fin (n + 1)) (a b : ℕ) :
    hlozTransitionKernel n hn level a b =
      ENNReal.ofReal (transitionMass (levelSuccess n level) a b) := by
  simp [hlozTransitionKernel]

/-- Internal HLOZ transitions have the critical negative-binomial formula
`choose (a+b-1,b) / 2^(a+b)`. -/
theorem internal_transitionMass_formula {n : ℕ} (_hn : 2 ≤ n)
    {level : Fin (n + 1)} (hlevel : (level : ℕ) < n)
    {a : ℕ} (ha : 0 < a) (b : ℕ) :
    transitionMass (levelSuccess n level) a b =
      ((a + b - 1).choose b : ℝ) / (2 : ℝ) ^ (a + b) := by
  rw [transitionMass_of_pos _ ha,
    NegativeBinomial.mass_eq_hloz_formula (levelSuccess n level) ha]
  simp only [levelSuccess, if_pos hlevel]
  norm_num [div_pow]
  ring

/-- The terminal HLOZ transition is the corresponding negative-binomial
mass with parameter `3 log n / (1 + 3 log n)`. -/
theorem terminal_transitionMass_formula {n : ℕ} (_hn : 2 ≤ n)
    {level : Fin (n + 1)} (hlevel : (level : ℕ) = n)
    {a : ℕ} (ha : 0 < a) (b : ℕ) :
    transitionMass (levelSuccess n level) a b =
      ((a + b - 1).choose b : ℝ) * terminalSuccess n ^ a *
        (1 - terminalSuccess n) ^ b := by
  rw [transitionMass_of_pos _ ha,
    NegativeBinomial.mass_eq_hloz_formula (levelSuccess n level) ha]
  have hnotlt : ¬(level : ℕ) < n := by omega
  simp only [levelSuccess, if_neg hnotlt]

/-! ## The actual finite nested-disc statistic -/

/-- Extend a finite increment block arbitrarily beyond its length.  Only the
first `horizon` increments are read by `finiteWalkPath`. -/
def extendBlock {horizon : ℕ} (u : Fin horizon → Direction) : StepPath :=
  fun j ↦ if hj : j < horizon then u ⟨j, hj⟩ else 0

/-- The walk started from `start`, driven by a finite block, and frozen after
the supplied horizon. -/
def finiteWalkPath {horizon : ℕ} (start : Point)
    (u : Fin horizon → Direction) : WalkPath :=
  fun t ↦ if _ht : t ≤ horizon then start + trajectory (extendBlock u) t
    else start + trajectory (extendBlock u) horizon

@[simp] theorem finiteWalkPath_zero {horizon : ℕ} (start : Point)
    (u : Fin horizon → Direction) : finiteWalkPath start u 0 = start := by
  simp [finiteWalkPath]

/-- The adjacent pair `(N_{n,k}, N_{n,k+1})` of actual nested-disc excursion
counts in a finite fresh block. -/
noncomputable def finiteExcursionPair (n horizon : ℕ) (start center : Point)
    (level : Fin (n + 1)) (u : Fin horizon → Direction) : ℕ × ℕ := by
  classical
  let profile := ThickPoint.excursionProfile (finiteWalkPath start u) n horizon center
  exact (profile level.castSucc, profile level.succ)

/-- Fresh finite-block event specifying both adjacent excursion counts. -/
def freshPairEvent (n horizon : ℕ) (start center : Point)
    (level : Fin (n + 1)) (a b : ℕ) : Set (Fin horizon → Direction) :=
  {u | finiteExcursionPair n horizon start center level u = (a, b)}

/-- Fresh finite-block event specifying only the incoming excursion count. -/
def freshParentEvent (n horizon : ℕ) (start center : Point)
    (level : Fin (n + 1)) (a : ℕ) : Set (Fin horizon → Direction) :=
  {u | (finiteExcursionPair n horizon start center level u).1 = a}

/-- Joint mass of the actual adjacent excursion counts in a finite fresh
planar block. -/
def finitePlanarJointMass (n horizon : ℕ) (start center : Point)
    (level : Fin (n + 1)) (a b : ℕ) : ℝ≥0∞ :=
  fairBlock horizon (freshPairEvent n horizon start center level a b)

/-- Marginal mass of the incoming actual excursion count. -/
def finitePlanarParentMass (n horizon : ℕ) (start center : Point)
    (level : Fin (n + 1)) (a : ℕ) : ℝ≥0∞ :=
  fairBlock horizon (freshParentEvent n horizon start center level a)

/-- The exact finite planar conditional kernel.  It is intentionally kept
separate from `hlozTransitionKernel`: proving their scale-uniform
multiplicative comparison is the missing Harnack step. -/
def finitePlanarConditionalMass (n horizon : ℕ) (start center : Point)
    (level : Fin (n + 1)) (a b : ℕ) : ℝ≥0∞ :=
  finitePlanarJointMass n horizon start center level a b /
    finitePlanarParentMass n horizon start center level a

theorem freshPairEvent_subset_parentEvent (n horizon : ℕ) (start center : Point)
    (level : Fin (n + 1)) (a b : ℕ) :
    freshPairEvent n horizon start center level a b ⊆
      freshParentEvent n horizon start center level a := by
  intro u hu
  exact congrArg Prod.fst hu

/-! ## Strong Markov factorization for the finite planar kernel -/

/-- Exact factorization of the actual adjacent-count event after a finite
stopping time. -/
theorem stopped_finiteExcursionPair_factorization
    {τ : StepPath → ℕ} {A : Set StepPath}
    (hτ : IsFiniteStoppingTime τ) (hA : IsMeasurableAtStopping τ A)
    (n horizon : ℕ) (start center : Point) (level : Fin (n + 1)) (a b : ℕ) :
    fairSteps
        (A ∩ postStoppingBlock τ horizon ⁻¹'
          freshPairEvent n horizon start center level a b) =
      fairSteps A * finitePlanarJointMass n horizon start center level a b := by
  exact strongMarkov_stoppedEvent_set hτ hA horizon
    (freshPairEvent n horizon start center level a b)

/-- Exact factorization of the incoming-count event after a finite stopping
time. -/
theorem stopped_finiteExcursionParent_factorization
    {τ : StepPath → ℕ} {A : Set StepPath}
    (hτ : IsFiniteStoppingTime τ) (hA : IsMeasurableAtStopping τ A)
    (n horizon : ℕ) (start center : Point) (level : Fin (n + 1)) (a : ℕ) :
    fairSteps
        (A ∩ postStoppingBlock τ horizon ⁻¹'
          freshParentEvent n horizon start center level a) =
      fairSteps A * finitePlanarParentMass n horizon start center level a := by
  exact strongMarkov_stoppedEvent_set hτ hA horizon
    (freshParentEvent n horizon start center level a)

/-- Conditional-law form of finite strong Markov: after conditioning on a
positive stopped-past event, the quotient of the joint adjacent-count mass by
the incoming-count mass is exactly the fresh finite planar kernel. -/
theorem stopped_finiteExcursionPair_conditional
    {τ : StepPath → ℕ} {A : Set StepPath}
    (hτ : IsFiniteStoppingTime τ) (hA : IsMeasurableAtStopping τ A)
    (hApos : fairSteps A ≠ 0)
    (n horizon : ℕ) (start center : Point) (level : Fin (n + 1)) (a b : ℕ) :
    fairSteps
          (A ∩ postStoppingBlock τ horizon ⁻¹'
            freshPairEvent n horizon start center level a b) /
        fairSteps
          (A ∩ postStoppingBlock τ horizon ⁻¹'
            freshParentEvent n horizon start center level a) =
      finitePlanarConditionalMass n horizon start center level a b := by
  rw [stopped_finiteExcursionPair_factorization hτ hA,
    stopped_finiteExcursionParent_factorization hτ hA]
  exact ENNReal.mul_div_mul_left _ _ hApos (measure_ne_top fairSteps A)

end

end Erdos1165.ExcursionTransition
