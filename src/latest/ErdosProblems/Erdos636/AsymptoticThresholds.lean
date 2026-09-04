/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos636.RoundedParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Eventual numerical estimates for Erdős Problem 636

The structural and augmentation arguments use only finitely many constants,
chosen before the ambient order.  This file packages the corresponding
Archimedean bookkeeping.  In particular it gives reusable threshold lemmas
for floors on the square-root scale and for a polynomial times an
exponentially decaying factor.

No graph-theoretic input occurs here.
-/

open Filter
open scoped Topology

namespace Erdos636.AsymptoticThresholds

noncomputable section

/-! ## General threshold combinators -/

/-- Turn an eventual assertion about natural numbers into a literal natural
threshold. -/
lemma exists_nat_threshold {P : ℕ → Prop} (hP : ∀ᶠ n : ℕ in atTop, P n) :
    ∃ N : ℕ, ∀ n ≥ N, P n :=
  eventually_atTop.mp hP

/-- Two eventual natural-number assertions can be made simultaneous by one
threshold. -/
lemma exists_nat_threshold_and {P Q : ℕ → Prop}
    (hP : ∃ NP : ℕ, ∀ n ≥ NP, P n)
    (hQ : ∃ NQ : ℕ, ∀ n ≥ NQ, Q n) :
    ∃ N : ℕ, ∀ n ≥ N, P n ∧ Q n := by
  obtain ⟨NP, hP⟩ := hP
  obtain ⟨NQ, hQ⟩ := hQ
  refine ⟨max NP NQ, fun n hn ↦ ⟨?_, ?_⟩⟩
  · exact hP n ((le_max_left _ _).trans hn)
  · exact hQ n ((le_max_right _ _).trans hn)

/-- Positive real powers of natural numbers eventually exceed every fixed
real constant. -/
lemma exists_nat_rpow_ge (p B : ℝ) (hp : 0 < p) :
    ∃ N : ℕ, ∀ n ≥ N, B ≤ (n : ℝ) ^ p := by
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ p) atTop atTop :=
    (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (ht.eventually (eventually_ge_atTop B))

/-- A fixed positive multiple of `sqrt n` eventually exceeds every fixed
real constant. -/
theorem exists_const_le_mul_sqrt (a B : ℝ) (ha : 0 < a) :
    ∃ N : ℕ, ∀ n ≥ N, B ≤ a * Real.sqrt n := by
  obtain ⟨N, hN⟩ := exists_nat_rpow_ge (1 / 2 : ℝ) (B / a) (by norm_num)
  refine ⟨N, ?_⟩
  intro n hn
  have h := hN n hn
  have hsqrt : (n : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]
  rw [hsqrt] at h
  have hscaled := mul_le_mul_of_nonneg_left h ha.le
  rw [mul_div_cancel₀ B ha.ne'] at hscaled
  simpa [mul_comm] using hscaled

/-- For positive `a`, the floor of `a * sqrt n` eventually retains half of
its unrounded value. -/
theorem exists_half_mul_sqrt_le_floor (a : ℝ) (ha : 0 < a) :
    ∃ N : ℕ, ∀ n ≥ N,
      a / 2 * Real.sqrt n ≤ (⌊a * Real.sqrt n⌋₊ : ℝ) := by
  obtain ⟨N, hN⟩ := exists_const_le_mul_sqrt a 2 ha
  refine ⟨N, ?_⟩
  intro n hn
  have hlarge := hN n hn
  have hfloor := Nat.lt_floor_add_one (a * Real.sqrt n)
  linarith

/-- A convenient scaled form of `exists_half_mul_sqrt_le_floor`. -/
theorem exists_eighth_mul_sqrt_le_quarter_floor (a : ℝ) (ha : 0 < a) :
    ∃ N : ℕ, ∀ n ≥ N,
      a / 8 * Real.sqrt n ≤ (⌊a * Real.sqrt n / 4⌋₊ : ℝ) := by
  have ha4 : 0 < a / 4 := by positivity
  obtain ⟨N, hN⟩ := exists_half_mul_sqrt_le_floor (a / 4) ha4
  refine ⟨N, ?_⟩
  intro n hn
  convert hN n hn using 1 <;> ring_nf

/-- The corresponding floor never exceeds its unrounded square-root scale. -/
lemma floor_mul_sqrt_le (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (⌊a * Real.sqrt n⌋₊ : ℝ) ≤ a * Real.sqrt n := by
  exact Nat.floor_le (mul_nonneg ha (Real.sqrt_nonneg _))

/-- In particular, the quarter-scale floor has twice its cardinality at
most the half-scale, with room to spare. -/
lemma twice_quarter_floor_le (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (2 : ℝ) * (⌊a * Real.sqrt n / 4⌋₊ : ℝ) ≤
      a * Real.sqrt n := by
  have h := Nat.floor_le (show 0 ≤ a * Real.sqrt n / 4 by positivity)
  nlinarith

/-- Once a nonnegative real quantity is at least two, flooring loses at
most half of it. -/
lemma half_le_natFloor {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have hfloor := Nat.lt_floor_add_one x
  linarith

/-- A division-and-floor form convenient for deterministic thinning and
stride selection. -/
lemma half_div_le_natFloor_div {x L : ℝ} (hL : 0 < L)
    (hx : 2 * L ≤ x) :
    x / (2 * L) ≤ (⌊x / L⌋₊ : ℝ) := by
  calc
    x / (2 * L) = (x / L) / 2 := by ring
    _ ≤ (⌊x / L⌋₊ : ℝ) := half_le_natFloor (by
      rwa [le_div_iff₀ hL])

/-- If at least half of a `theta`-fraction survives two deletion steps,
then retaining one item per stride `L` keeps a `theta/(4L)`-fraction. -/
lemma strideSurvivor_lower
    {theta : ℝ} {base survivors kept L : ℕ}
    (htheta : 0 ≤ theta) (hL : 0 < L)
    (hsurvivors : theta * base ≤ 2 * survivors)
    (hlarge : 2 * L ≤ survivors)
    (hkept : ⌊(survivors : ℝ) / L⌋₊ ≤ kept) :
    theta / (4 * L) * base ≤ (kept : ℝ) := by
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hlargeReal : (2 : ℝ) * (L : ℝ) ≤ (survivors : ℝ) := by
    exact_mod_cast hlarge
  have hhalf := half_div_le_natFloor_div hLreal hlargeReal
  have hfloor : ((⌊(survivors : ℝ) / L⌋₊ : ℕ) : ℝ) ≤ kept := by
    exact_mod_cast hkept
  calc
    theta / (4 * L) * base ≤ (survivors : ℝ) / (2 * L) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * L)).2
      calc
        theta / (4 * L) * base * (2 * L) = theta * base / 2 := by
          field_simp
          ring
        _ ≤ survivors := by nlinarith [hsurvivors]
    _ ≤ (⌊(survivors : ℝ) / L⌋₊ : ℝ) := hhalf
    _ ≤ kept := hfloor

/-- Combine a square-root lower bound for a Turán-thinned base family with
the stride-survivor lemma. -/
lemma sqrt_le_strideSurvivor
    {theta c : ℝ} {nD base survivors kept L : ℕ}
    (htheta : 0 ≤ theta) (hc : 0 ≤ c) (hL : 0 < L)
    (hbase : c * Real.sqrt nD ≤ (base : ℝ))
    (hsurvivors : theta * base ≤ 2 * survivors)
    (hlarge : 2 * L ≤ survivors)
    (hkept : ⌊(survivors : ℝ) / L⌋₊ ≤ kept) :
    theta * c / (4 * L) * Real.sqrt nD ≤ (kept : ℝ) := by
  calc
    theta * c / (4 * L) * Real.sqrt nD =
        theta / (4 * L) * (c * Real.sqrt nD) := by ring
    _ ≤ theta / (4 * L) * base := by gcongr
    _ ≤ kept := strideSurvivor_lower htheta hL hsurvivors hlarge hkept

/-- The elementary scale translation `sqrt n ≤ n` for positive natural
orders. -/
lemma sqrt_nat_le_nat {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt n ≤ n := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith

/-- A polynomial times `exp (-b n)` tends to zero, uniformly after a
literal natural threshold.  The coefficient is allowed to be any fixed
nonnegative real number. -/
theorem exists_polynomial_mul_exp_neg_lt
    (A b : ℝ) (p : ℕ) (hA : 0 ≤ A) (hb : 0 < b) (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n ≥ N,
      A * (n : ℝ) ^ p * Real.exp (-b * n) < epsilon := by
  have htReal : Tendsto
      (fun x : ℝ ↦ A * (x ^ (p : ℝ) * Real.exp (-b * x)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
          (p : ℝ) b hb) :
        Tendsto (fun x : ℝ ↦ A * (x ^ (p : ℝ) * Real.exp (-b * x)))
          atTop (𝓝 (A * 0)))
  have htNatRpow : Tendsto
      (fun n : ℕ ↦ A * ((n : ℝ) ^ (p : ℝ) * Real.exp (-b * n)))
      atTop (𝓝 0) := by
    change Tendsto
      ((fun x : ℝ ↦ A * (x ^ (p : ℝ) * Real.exp (-b * x))) ∘
        (fun n : ℕ ↦ (n : ℝ))) atTop (𝓝 0)
    exact htReal.comp tendsto_natCast_atTop_atTop
  have heventRpow : ∀ᶠ n : ℕ in atTop,
      A * ((n : ℝ) ^ (p : ℝ) * Real.exp (-b * n)) < epsilon :=
    htNatRpow.eventually (Iio_mem_nhds hepsilon)
  apply eventually_atTop.mp
  filter_upwards [heventRpow] with n hn
  simpa only [Real.rpow_natCast, mul_assoc] using hn

/-- The special `epsilon = 1` form used for union bounds. -/
theorem exists_polynomial_mul_exp_neg_lt_one
    (A b : ℝ) (p : ℕ) (hA : 0 ≤ A) (hb : 0 < b) :
    ∃ N : ℕ, ∀ n ≥ N,
      A * (n : ℝ) ^ p * Real.exp (-b * n) < 1 :=
  exists_polynomial_mul_exp_neg_lt A b p hA hb 1 zero_lt_one

/-! ## Fixed-ambient structural scales -/

/-- The structural switching density is a fixed small fraction of the rich
subgraph density. -/
def structuralDensity (cR : ℝ) : ℝ := cR / 100

def structuralSwitchingSize (cR : ℝ) (n : ℕ) : ℕ :=
  ⌊structuralDensity cR * n⌋₊

def structuralCandidateSize (cR : ℝ) (n : ℕ) : ℕ :=
  ⌊cR / 4 * n⌋₊

/-- Size of the preliminary vertex reservoir sorted by its sampled degree. -/
def structuralSortingSize (cR : ℝ) (n : ℕ) : ℕ :=
  ⌊cR / 2 * n⌋₊

def structuralGapSize (cGap : ℝ) (n : ℕ) : ℕ :=
  ⌊cGap * Real.sqrt n⌋₊

def structuralEdgeBudget (QE : ℝ) (n : ℕ) : ℕ :=
  ⌈QE * n * Real.sqrt n⌉₊

def structuralDegreeBudget (QD : ℝ) (n : ℕ) : ℕ :=
  ⌈QD * Real.sqrt n⌉₊

def structuralExceptionalSize (m : ℕ) : ℕ :=
  ⌈(m : ℝ) ^ (1 / 5 : ℝ)⌉₊

def structuralTestCount (m : ℕ) : ℕ :=
  (65 * m ^ 64) ^ 2

/-- The persistence union bound used by the fixed-slice structural
selection.  Its polynomial factor has degree at most `130`, whereas the
failure probability decays exponentially in the outer parameter `ell`. -/
theorem exists_structuralUnionBudget
    {cR QE q : ℝ} (hcR : 0 < cR) (hQE : 0 < QE) (hq : 0 < q) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m ell : ℕ,
      m ≤ n → structuralDensity cR * n ≤ (ell : ℝ) →
      ((structuralEdgeBudget QE n + 1 : ℕ) : ℝ) *
          structuralTestCount m *
          (2 * Real.exp (-q * ell)) < 1 := by
  let b : ℝ := q * structuralDensity cR
  let A : ℝ := 2 * (QE + 2) * 65 ^ 2
  have hcS : 0 < structuralDensity cR := by
    simp only [structuralDensity]
    positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨Nexp, hNexp⟩ :=
    exists_polynomial_mul_exp_neg_lt_one A b 130 hA hb
  refine ⟨max 1 Nexp, ?_⟩
  intro n hn m ell hmn hell
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hNexp' : Nexp ≤ n := (le_max_right _ _).trans hn
  have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnreal1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hmreal : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hsqrt : Real.sqrt n ≤ (n : ℝ) := sqrt_nat_le_nat hn1
  have hedgeCeil : (structuralEdgeBudget QE n : ℝ) <
      QE * n * Real.sqrt n + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  have hedge : ((structuralEdgeBudget QE n + 1 : ℕ) : ℝ) ≤
      (QE + 2) * (n : ℝ) ^ 2 := by
    push_cast
    have hmain : QE * (n : ℝ) * Real.sqrt n ≤ QE * n * n := by
      gcongr
    have hone : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    nlinarith
  have htests : (structuralTestCount m : ℝ) ≤
      (65 : ℝ) ^ 2 * (n : ℝ) ^ 128 := by
    dsimp only [structuralTestCount]
    push_cast
    calc
      ((65 : ℝ) * (m : ℝ) ^ 64) ^ 2 =
          (65 : ℝ) ^ 2 * (m : ℝ) ^ 128 := by ring
      _ ≤ (65 : ℝ) ^ 2 * (n : ℝ) ^ 128 := by gcongr
  have hdecay : Real.exp (-q * (ell : ℝ)) ≤
      Real.exp (-b * n) := by
    apply Real.exp_le_exp.mpr
    dsimp only [b]
    nlinarith
  have hnonnegDecay : 0 ≤ Real.exp (-q * (ell : ℝ)) :=
    (Real.exp_pos _).le
  have hpoly :
      ((structuralEdgeBudget QE n + 1 : ℕ) : ℝ) *
          structuralTestCount m * 2 ≤ A * (n : ℝ) ^ 130 := by
    calc
      ((structuralEdgeBudget QE n + 1 : ℕ) : ℝ) *
          structuralTestCount m * 2
          ≤ ((QE + 2) * (n : ℝ) ^ 2) *
              ((65 : ℝ) ^ 2 * (n : ℝ) ^ 128) * 2 := by gcongr
      _ = A * (n : ℝ) ^ 130 := by
        dsimp [A]
        ring
  calc
    ((structuralEdgeBudget QE n + 1 : ℕ) : ℝ) *
          structuralTestCount m *
          (2 * Real.exp (-q * ell)) =
        (((structuralEdgeBudget QE n + 1 : ℕ) : ℝ) *
          structuralTestCount m * 2) * Real.exp (-q * ell) := by ring
    _ ≤ (A * (n : ℝ) ^ 130) * Real.exp (-q * ell) := by gcongr
    _ ≤ A * (n : ℝ) ^ 130 * Real.exp (-b * n) := by gcongr
    _ < 1 := hNexp n hNexp'

/-- The degree-fibre and degree-gap budgets leave room between the bottom
and top switching blocks in the sorted reservoir. -/
theorem exists_structuralMiddleRoom
    {cR QD cGap : ℝ}
    (hcR : 0 < cR) (hQD : 0 < QD) (hcGap : 0 < cGap)
    (hconstants : 4 * QD * cGap < cR / 8) :
    ∃ N : ℕ, ∀ n ≥ N,
      (structuralDegreeBudget QD n + 1) *
          (structuralGapSize cGap n + 1) <
        structuralSortingSize cR n -
          2 * structuralSwitchingSize cR n := by
  let B : ℝ := QD + 2 * cGap + 2
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨N, hN⟩ := exists_const_le_mul_sqrt 1
    (max (32 * B / cR) (100 / cR)) zero_lt_one
  refine ⟨max 1 N, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hN' : N ≤ n := (le_max_right _ _).trans hn
  have hlarge := hN n hN'
  simp only [one_mul] at hlarge
  have hBroot : 32 * B / cR ≤ Real.sqrt n :=
    (le_max_left _ _).trans hlarge
  have h100root : 100 / cR ≤ Real.sqrt n :=
    (le_max_right _ _).trans hlarge
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hsqrtPos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnreal
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt n := by
    calc
      (1 : ℝ) = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hn1)
  have hsqrtSq : (Real.sqrt n) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hnreal.le
  have hsortLarge : 2 ≤ cR / 2 * (n : ℝ) := by
    have hsqrtn : Real.sqrt n ≤ (n : ℝ) := sqrt_nat_le_nat hn1
    have h100n : 100 / cR ≤ (n : ℝ) := h100root.trans hsqrtn
    rw [div_le_iff₀ hcR] at h100n
    nlinarith
  have hsortLower : cR / 4 * n ≤
      (structuralSortingSize cR n : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (cR / 2 * (n : ℝ))
    dsimp only [structuralSortingSize]
    linarith
  have hnWUpper : (structuralSwitchingSize cR n : ℝ) ≤
      cR / 100 * n := by
    rw [structuralSwitchingSize]
    exact Nat.floor_le
      (mul_nonneg (div_nonneg hcR.le (by norm_num)) (Nat.cast_nonneg n))
  have hdegree : (structuralDegreeBudget QD n : ℝ) <
      QD * Real.sqrt n + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  have hgap : (structuralGapSize cGap n : ℝ) ≤
      cGap * Real.sqrt n := by
    exact Nat.floor_le (by positivity)
  have herror : B * Real.sqrt n ≤ cR / 32 * n := by
    have hcoef : B ≤ cR / 32 * Real.sqrt n := by
      have hscaled := mul_le_mul_of_nonneg_left hBroot (show 0 ≤ cR / 32 by positivity)
      have hcancel : cR / 32 * (32 * B / cR) = B := by field_simp
      rw [hcancel] at hscaled
      exact hscaled
    have hscaled := mul_le_mul_of_nonneg_right hcoef hsqrtPos.le
    calc
      B * Real.sqrt n ≤ cR / 32 * Real.sqrt n * Real.sqrt n := hscaled
      _ = cR / 32 * (Real.sqrt n) ^ 2 := by ring
      _ = cR / 32 * n := by rw [hsqrtSq]
  have hleading : QD * cGap * n < cR / 32 * n := by
    have hcoeff : QD * cGap < cR / 32 := by nlinarith
    exact mul_lt_mul_of_pos_right hcoeff hnreal
  have hproduct :
      ((structuralDegreeBudget QD n + 1 : ℕ) : ℝ) *
          (structuralGapSize cGap n + 1) < cR / 16 * n := by
    push_cast
    calc
      ((structuralDegreeBudget QD n : ℝ) + 1) *
          ((structuralGapSize cGap n : ℝ) + 1)
          < (QD * Real.sqrt n + 2) *
              ((structuralGapSize cGap n : ℝ) + 1) := by
            have hright : 0 < cGap * Real.sqrt n + 1 := by positivity
            exact mul_lt_mul_of_pos_right
              (by linarith : (structuralDegreeBudget QD n : ℝ) + 1 <
                QD * Real.sqrt n + 2)
              (by positivity)
      _ ≤ (QD * Real.sqrt n + 2) *
              (cGap * Real.sqrt n + 1) := by
            exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = QD * cGap * (Real.sqrt n) ^ 2 +
          (QD + 2 * cGap) * Real.sqrt n + 2 := by
            ring
      _ = QD * cGap * n +
          (QD + 2 * cGap) * Real.sqrt n + 2 := by rw [hsqrtSq]
      _ ≤ QD * cGap * n + B * Real.sqrt n := by
            dsimp [B]
            nlinarith
      _ < cR / 16 * n := by linarith
  have hsumReal :
      (((structuralDegreeBudget QD n + 1) *
          (structuralGapSize cGap n + 1) +
          2 * structuralSwitchingSize cR n : ℕ) : ℝ) <
        structuralSortingSize cR n := by
    push_cast
    calc
      ((structuralDegreeBudget QD n : ℝ) + 1) *
            ((structuralGapSize cGap n : ℝ) + 1) +
          2 * structuralSwitchingSize cR n
          < cR / 16 * n + 2 * (cR / 100 * n) := by
            nlinarith
      _ ≤ cR / 4 * n := by
            have : 0 ≤ cR * n := by positivity
            nlinarith
      _ ≤ structuralSortingSize cR n := hsortLower
  have hsumNat :
      (structuralDegreeBudget QD n + 1) *
          (structuralGapSize cGap n + 1) +
          2 * structuralSwitchingSize cR n <
        structuralSortingSize cR n := by exact_mod_cast hsumReal
  omega

/-- The exceptional vertices, collision-degree pruning, and reserved
two-copy parameter together occupy at most half of the rich vertex set. -/
theorem exists_structuralPruningBudget
    {cR QE QD : ℝ}
    (hcR : 0 < cR) (hQE : 0 < QE) (hQD : 0 < QD)
    (hconstants : 32 * QE ≤ cR * QD) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m ell : ℕ,
      cR * n ≤ (m : ℝ) → m ≤ n →
      (ell : ℝ) ≤ 2 * structuralDensity cR * n →
      structuralExceptionalSize m +
          (2 * structuralEdgeBudget QE n) /
            (structuralDegreeBudget QD n + 1) +
          2 * ell ≤ m / 2 := by
  obtain ⟨Mpow, hMpow⟩ := exists_nat_rpow_ge (4 / 5 : ℝ) 32 (by norm_num)
  let M : ℕ := max 32 Mpow
  obtain ⟨Nscale, hNscale⟩ := exists_nat_rpow_ge 1 (M / cR) (by norm_num)
  obtain ⟨Nedge, hNedge⟩ := exists_const_le_mul_sqrt QE 1 hQE
  let N := max 1 (max Nscale Nedge)
  refine ⟨N, ?_⟩
  intro n hn m ell hmLower _hmUpper hellUpper
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have htail : max Nscale Nedge ≤ n := (le_max_right _ _).trans hn
  have hNscale' : Nscale ≤ n := (le_max_left _ _).trans htail
  have hNedge' : Nedge ≤ n := (le_max_right _ _).trans htail
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hsqrtPos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnreal
  have hsqrtSq : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hnreal.le
  have hMraw := hNscale n hNscale'
  rw [Real.rpow_one] at hMraw
  have hMscaled := mul_le_mul_of_nonneg_left hMraw hcR.le
  rw [mul_div_cancel₀ (M : ℝ) hcR.ne'] at hMscaled
  have hMleReal : (M : ℝ) ≤ m := hMscaled.trans hmLower
  have hMle : M ≤ m := by exact_mod_cast hMleReal
  have hm32 : 32 ≤ m := (le_max_left _ _).trans hMle
  have hMpowm : Mpow ≤ m := (le_max_right _ _).trans hMle
  have hmreal : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 32) hm32)
  have hpow08 := hMpow m hMpowm
  have hpow02nonneg : 0 ≤ (m : ℝ) ^ (1 / 5 : ℝ) :=
    Real.rpow_nonneg hmreal.le _
  have hpowProduct :
      (m : ℝ) ^ (1 / 5 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ) = m := by
    rw [← Real.rpow_add hmreal]
    norm_num
  have hpow02 : (m : ℝ) ^ (1 / 5 : ℝ) ≤ (m : ℝ) / 32 := by
    have hscaled := mul_le_mul_of_nonneg_left hpow08 hpow02nonneg
    rw [hpowProduct] at hscaled
    linarith
  have hexceptional : (structuralExceptionalSize m : ℝ) ≤ (m : ℝ) / 16 := by
    have hceil : (structuralExceptionalSize m : ℝ) <
        (m : ℝ) ^ (1 / 5 : ℝ) + 1 := by
      exact Nat.ceil_lt_add_one (Real.rpow_nonneg hmreal.le _)
    have hm32real : (32 : ℝ) ≤ m := by exact_mod_cast hm32
    exact (hceil.trans_le (by linarith)).le
  let collisionLoss : ℕ :=
    (2 * structuralEdgeBudget QE n) /
      (structuralDegreeBudget QD n + 1)
  have hmain := hNedge n hNedge'
  have hmainN : 1 ≤ QE * (n : ℝ) * Real.sqrt n := by
    have hnreal1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hmono : QE * Real.sqrt n ≤ (n : ℝ) * (QE * Real.sqrt n) := by
      have := mul_le_mul_of_nonneg_right hnreal1
        (show 0 ≤ QE * Real.sqrt n by positivity)
      simpa only [one_mul] using this
    calc
      1 ≤ QE * Real.sqrt n := hmain
      _ ≤ (n : ℝ) * (QE * Real.sqrt n) := hmono
      _ = QE * (n : ℝ) * Real.sqrt n := by ring
  have hedge : (structuralEdgeBudget QE n : ℝ) <
      QE * n * Real.sqrt n + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  have hedgeTwice : (2 : ℝ) * structuralEdgeBudget QE n ≤
      4 * QE * n * Real.sqrt n := by
    nlinarith
  have hdegreeLower : QD * Real.sqrt n ≤
      (structuralDegreeBudget QD n : ℝ) + 1 := by
    have hceil : QD * Real.sqrt n ≤
        (structuralDegreeBudget QD n : ℝ) := Nat.le_ceil _
    exact hceil.trans (by push_cast; linarith)
  have hcollisionMulNat :
      collisionLoss * (structuralDegreeBudget QD n + 1) ≤
        2 * structuralEdgeBudget QE n := by
    exact Nat.div_mul_le_self _ _
  have hcollisionMul : (collisionLoss : ℝ) * (QD * Real.sqrt n) ≤
      4 * QE * n * Real.sqrt n := by
    calc
      (collisionLoss : ℝ) * (QD * Real.sqrt n) ≤
          collisionLoss * (structuralDegreeBudget QD n + 1) := by
            gcongr
      _ ≤ (2 * structuralEdgeBudget QE n : ℕ) := by exact_mod_cast hcollisionMulNat
      _ ≤ 4 * QE * n * Real.sqrt n := by
            push_cast
            exact hedgeTwice
  have hcoeff : 4 * QE ≤ cR * QD / 8 := by nlinarith
  have htargetMul : 4 * QE * n * Real.sqrt n ≤
      (cR / 8 * n) * (QD * Real.sqrt n) := by
    have hscaled := mul_le_mul_of_nonneg_right hcoeff
      (show 0 ≤ (n : ℝ) * Real.sqrt n by positivity)
    calc
      4 * QE * n * Real.sqrt n = (4 * QE) * (n * Real.sqrt n) := by ring
      _ ≤ (cR * QD / 8) * (n * Real.sqrt n) := hscaled
      _ = (cR / 8 * n) * (QD * Real.sqrt n) := by ring
  have hdenpos : 0 < QD * Real.sqrt n := mul_pos hQD hsqrtPos
  have hcollision : (collisionLoss : ℝ) ≤ (m : ℝ) / 8 := by
    have hcancel : (collisionLoss : ℝ) ≤ cR / 8 * n :=
      le_of_mul_le_mul_right (hcollisionMul.trans htargetMul) hdenpos
    linarith
  have hell : ((2 * ell : ℕ) : ℝ) ≤ (m : ℝ) / 16 := by
    push_cast
    have hraw : (2 : ℝ) * ell ≤ 4 * structuralDensity cR * n := by
      nlinarith
    have hsmall : 4 * structuralDensity cR * n ≤ cR / 16 * n := by
      simp only [structuralDensity]
      have : 0 ≤ cR * n := by positivity
      nlinarith
    linarith
  have hsumReal :
      (((structuralExceptionalSize m + collisionLoss + 2 * ell) * 2 : ℕ) : ℝ) ≤
        (m : ℝ) := by
    have hsumQuarter :
        (structuralExceptionalSize m : ℝ) + collisionLoss +
            ((2 * ell : ℕ) : ℝ) ≤ (m : ℝ) / 4 := by
      linarith
    push_cast at hsumQuarter ⊢
    nlinarith
  rw [Nat.le_div_iff_mul_le (by omega : 0 < (2 : ℕ))]
  exact_mod_cast hsumReal

/-- The deterministic exceptional-pair charge and the anti-concentration
collision expectation fit strictly below the chosen `n sqrt n` edge budget.
The fixed coefficient `A` is instantiated by the variance point-mass
constant in the graph-facing structural theorem. -/
theorem exists_structuralCollisionBudget
    {A QE : ℝ} (hA : 0 ≤ A) (hQE : 0 < QE) (hAQE : 2 * A < QE) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℕ, 1 ≤ m → m ≤ n →
      (m : ℝ) * structuralExceptionalSize m +
          m.choose 2 * (A / Real.sqrt m) <
        (structuralEdgeBudget QE n : ℝ) := by
  obtain ⟨Npow, hNpow⟩ := exists_nat_rpow_ge (3 / 10 : ℝ)
    (4 / QE) (by norm_num)
  obtain ⟨Nsqrt, hNsqrt⟩ := exists_const_le_mul_sqrt QE 4 hQE
  let N := max 1 (max Npow Nsqrt)
  refine ⟨N, ?_⟩
  intro n hn m hm1 hmn
  have hn1 : 1 ≤ n := hm1.trans hmn
  have htail : max Npow Nsqrt ≤ n := (le_max_right _ _).trans hn
  have hNpow' : Npow ≤ n := (le_max_left _ _).trans htail
  have hNsqrt' : Nsqrt ≤ n := (le_max_right _ _).trans htail
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hmreal : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm1)
  have hmnreal : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hsqrtNPos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnreal
  have hsqrtMPos : 0 < Real.sqrt m := Real.sqrt_pos.2 hmreal
  have hsqrtMSq : (Real.sqrt m) ^ 2 = (m : ℝ) := Real.sq_sqrt hmreal.le
  have hpow03 := hNpow n hNpow'
  have hpow02nonneg : 0 ≤ (n : ℝ) ^ (1 / 5 : ℝ) :=
    Real.rpow_nonneg hnreal.le _
  have hpowProduct :
      (n : ℝ) ^ (1 / 5 : ℝ) * (n : ℝ) ^ (3 / 10 : ℝ) =
        Real.sqrt n := by
    rw [← Real.rpow_add hnreal]
    norm_num
    rw [← Real.sqrt_eq_rpow]
  have hpow02 : (n : ℝ) ^ (1 / 5 : ℝ) ≤ QE / 4 * Real.sqrt n := by
    have hscaled := mul_le_mul_of_nonneg_left hpow03 hpow02nonneg
    rw [hpowProduct] at hscaled
    have hQE4 : 0 < QE / 4 := by positivity
    have hrescaled := mul_le_mul_of_nonneg_left hscaled hQE4.le
    have hcancel : QE / 4 *
        ((n : ℝ) ^ (1 / 5 : ℝ) * (4 / QE)) =
          (n : ℝ) ^ (1 / 5 : ℝ) := by
      field_simp
    rw [hcancel] at hrescaled
    exact hrescaled
  have hsqrtLarge := hNsqrt n hNsqrt'
  have hone : (1 : ℝ) ≤ QE / 4 * Real.sqrt n := by
    nlinarith
  have hmPow : (m : ℝ) ^ (1 / 5 : ℝ) ≤
      (n : ℝ) ^ (1 / 5 : ℝ) :=
    Real.rpow_le_rpow hmreal.le hmnreal (by norm_num)
  have hexceptional : (structuralExceptionalSize m : ℝ) ≤
      QE / 2 * Real.sqrt n := by
    have hceil : (structuralExceptionalSize m : ℝ) <
        (m : ℝ) ^ (1 / 5 : ℝ) + 1 :=
      Nat.ceil_lt_add_one (Real.rpow_nonneg hmreal.le _)
    exact (hceil.trans_le (by linarith)).le
  have hfirst : (m : ℝ) * structuralExceptionalSize m ≤
      QE / 2 * n * Real.sqrt n := by
    calc
      (m : ℝ) * structuralExceptionalSize m ≤
          (n : ℝ) * (QE / 2 * Real.sqrt n) := by gcongr
      _ = QE / 2 * n * Real.sqrt n := by ring
  have hchoose : ((m.choose 2 : ℕ) : ℝ) ≤ (m : ℝ) ^ 2 := by
    exact_mod_cast Nat.choose_le_pow m 2
  have hcollision : ((m.choose 2 : ℕ) : ℝ) *
      (A / Real.sqrt m) ≤ A * n * Real.sqrt n := by
    have hdivnonneg : 0 ≤ A / Real.sqrt m := div_nonneg hA hsqrtMPos.le
    calc
      ((m.choose 2 : ℕ) : ℝ) * (A / Real.sqrt m) ≤
          (m : ℝ) ^ 2 * (A / Real.sqrt m) := by gcongr
      _ = A * m * Real.sqrt m := by
        field_simp
        nlinarith [hsqrtMSq]
      _ ≤ A * n * Real.sqrt n := by
        have hsqrtMono : Real.sqrt m ≤ Real.sqrt n := Real.sqrt_le_sqrt hmnreal
        gcongr
  have hcollisionHalf : ((m.choose 2 : ℕ) : ℝ) *
      (A / Real.sqrt m) < QE / 2 * n * Real.sqrt n := by
    exact hcollision.trans_lt (by
      have hcoeff : A < QE / 2 := by linarith
      have hscale : 0 < (n : ℝ) * Real.sqrt n := mul_pos hnreal hsqrtNPos
      nlinarith)
  have hraw : (m : ℝ) * structuralExceptionalSize m +
      m.choose 2 * (A / Real.sqrt m) < QE * n * Real.sqrt n := by
    linarith
  exact hraw.trans_le (Nat.le_ceil _)

/-- The fixed-ambient capacity, slice balance, and endpoint score estimates
which do not involve the probabilistic loss terms. -/
structure FixedAmbientBounds (cR cGap : ℝ) (n m ell : ℕ) : Prop where
  switching_pos : 0 < structuralSwitchingSize cR n
  two_parameter_le : 2 * ell ≤ m
  capacity :
    2 * structuralSwitchingSize cR n + 2 * ell +
      structuralCandidateSize cR n ≤ m
  selected_balance : structuralDensity cR * m ≤ 2 * ell
  unselected_balance : structuralDensity cR * m ≤ (m - 2 * ell : ℕ)
  score_lower :
    cR * cGap / 1600 * n * Real.sqrt n ≤
      (1 / 8 : ℝ) * structuralSwitchingSize cR n *
        (structuralGapSize cGap n + 1)

/-- Pointwise capacity and slice balance for the fixed ambient scale. -/
lemma fixedAmbient_capacity_balance
    {cR : ℝ} {n m ell : ℕ}
    (hcR : 0 < cR) (hcR1 : cR ≤ 1)
    (hmLower : cR * n ≤ (m : ℝ)) (hmUpper : m ≤ n)
    (hellLower : structuralDensity cR * n ≤ (ell : ℝ))
    (hellUpper : (ell : ℝ) ≤ 2 * structuralDensity cR * n) :
    2 * ell ≤ m ∧
      2 * structuralSwitchingSize cR n + 2 * ell +
        structuralCandidateSize cR n ≤ m ∧
      structuralDensity cR * m ≤ 2 * ell ∧
      structuralDensity cR * m ≤ (m - 2 * ell : ℕ) := by
  have hcS : 0 < structuralDensity cR := by
    simp only [structuralDensity]
    positivity
  have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmreal : (m : ℝ) ≤ n := by exact_mod_cast hmUpper
  have hnW : (structuralSwitchingSize cR n : ℝ) ≤
      structuralDensity cR * n := by
    exact Nat.floor_le (by positivity)
  have hsA : (structuralCandidateSize cR n : ℝ) ≤ cR / 4 * n := by
    exact Nat.floor_le (by positivity)
  have htwoReal : ((2 * ell : ℕ) : ℝ) ≤ m := by
    push_cast
    calc
      2 * (ell : ℝ) ≤ 4 * structuralDensity cR * n := by nlinarith
      _ ≤ cR * n := by
        simp only [structuralDensity]
        nlinarith
      _ ≤ m := hmLower
  have htwo : 2 * ell ≤ m := by exact_mod_cast htwoReal
  have hcapacityReal :
      ((2 * structuralSwitchingSize cR n + 2 * ell +
          structuralCandidateSize cR n : ℕ) : ℝ) ≤ m := by
    push_cast
    calc
      2 * (structuralSwitchingSize cR n : ℝ) + 2 * ell +
          structuralCandidateSize cR n
          ≤ 2 * (structuralDensity cR * n) +
              4 * structuralDensity cR * n + cR / 4 * n := by
            nlinarith
      _ ≤ cR * n := by
        simp only [structuralDensity]
        nlinarith
      _ ≤ m := hmLower
  have hselected : structuralDensity cR * m ≤ 2 * (ell : ℝ) := by
    calc
      structuralDensity cR * (m : ℝ) ≤ structuralDensity cR * n := by
        gcongr
      _ ≤ (ell : ℝ) := hellLower
      _ ≤ 2 * ell := by linarith
  have hunselectedSum :
      structuralDensity cR * m + 2 * ell ≤ (m : ℝ) := by
    calc
      structuralDensity cR * (m : ℝ) + 2 * ell
          ≤ structuralDensity cR * n +
              4 * structuralDensity cR * n := by
            have : structuralDensity cR * (m : ℝ) ≤
                structuralDensity cR * n := by gcongr
            nlinarith
      _ ≤ cR * n := by
        simp only [structuralDensity]
        nlinarith
      _ ≤ m := hmLower
  have hunselected : structuralDensity cR * m ≤
      ((m - 2 * ell : ℕ) : ℝ) := by
    rw [Nat.cast_sub htwo]
    push_cast
    linarith
  exact ⟨htwo, by exact_mod_cast hcapacityReal,
    hselected, hunselected⟩

/-- One threshold makes the fixed-ambient capacity and score estimates
uniform in the rich order `m` and outer parameter `ell`. -/
theorem exists_fixedAmbientBounds
    {cR cGap : ℝ} (hcR : 0 < cR) (hcR1 : cR ≤ 1)
    (hcGap : 0 < cGap) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m ell : ℕ,
      cR * n ≤ (m : ℝ) → m ≤ n →
      structuralDensity cR * n ≤ (ell : ℝ) →
      (ell : ℝ) ≤ 2 * structuralDensity cR * n →
      FixedAmbientBounds cR cGap n m ell := by
  obtain ⟨N, hN⟩ := exists_nat_rpow_ge 1
    (2 / structuralDensity cR) (by norm_num)
  refine ⟨N, ?_⟩
  intro n hn m ell hmLower hmUpper hellLower hellUpper
  have hcS : 0 < structuralDensity cR := by
    simp only [structuralDensity]
    positivity
  have hlargeRaw := hN n hn
  rw [Real.rpow_one] at hlargeRaw
  have hlargeScaled := mul_le_mul_of_nonneg_left hlargeRaw hcS.le
  rw [mul_div_cancel₀ 2 hcS.ne'] at hlargeScaled
  have hnWhalf : structuralDensity cR / 2 * n ≤
      (structuralSwitchingSize cR n : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (structuralDensity cR * (n : ℝ))
    dsimp only [structuralSwitchingSize]
    linarith
  have hnWpos : 0 < structuralSwitchingSize cR n := by
    have hpositive : (0 : ℝ) < structuralDensity cR / 2 * n := by
      have hnreal : (0 : ℝ) < n := by nlinarith
      positivity
    exact_mod_cast hpositive.trans_le hnWhalf
  have hgap : cGap * Real.sqrt n ≤
      (structuralGapSize cGap n : ℝ) + 1 := by
    simpa only [structuralGapSize] using
      (Nat.lt_floor_add_one (cGap * Real.sqrt n)).le
  have hscore :
      cR * cGap / 1600 * n * Real.sqrt n ≤
        (1 / 8 : ℝ) * structuralSwitchingSize cR n *
          (structuralGapSize cGap n + 1) := by
    change cR * cGap / 1600 * n * Real.sqrt n ≤
      (1 / 8 : ℝ) * (structuralSwitchingSize cR n : ℝ) *
        ((structuralGapSize cGap n : ℝ) + 1)
    have hnWnonneg : (0 : ℝ) ≤ structuralSwitchingSize cR n := by positivity
    have hgapnonneg : 0 ≤ cGap * Real.sqrt n := by positivity
    calc
      cR * cGap / 1600 * n * Real.sqrt n =
          (1 / 8 : ℝ) * (structuralDensity cR / 2 * n) *
            (cGap * Real.sqrt n) := by
              simp only [structuralDensity]
              ring
      _ ≤ (1 / 8 : ℝ) * structuralSwitchingSize cR n *
            (cGap * Real.sqrt n) := by gcongr
      _ ≤ (1 / 8 : ℝ) * structuralSwitchingSize cR n *
            (structuralGapSize cGap n + 1) := by gcongr
  obtain ⟨htwo, hcapacity, hselected, hunselected⟩ :=
    fixedAmbient_capacity_balance hcR hcR1 hmLower hmUpper
      hellLower hellUpper
  exact {
    switching_pos := hnWpos
    two_parameter_le := htwo
    capacity := hcapacity
    selected_balance := hselected
    unselected_balance := hunselected
    score_lower := hscore }

/-! ## Balanced-augmentation scales -/

/-- The first matching extracted in the partial exposure. -/
def partialMatchingSize (a₀ : ℝ) (nD : ℕ) : ℕ :=
  ⌊a₀ * Real.sqrt nD / 4⌋₊

/-- The explicit two-sided linear-statistic failure probability used in the
outer partial exposure. -/
def balancedLinearFailure (nD K : ℕ) (t : ℝ) : ℝ :=
  2 * Real.exp (-t ^ 2 / (2 * (2 * nD) * (4 * K) ^ 2))

/-- A uniform augmentation size valid for every structural arity
`1 ≤ k ≤ K`. -/
def uniformAugmentationSize (delta : ℝ) (K nD : ℕ) : ℕ :=
  ⌊delta * Real.sqrt nD / K⌋₊

/-- The matching remaining after the auxiliary-graph Turán thinning. -/
def thinnedMatchingSize (gamma R : ℝ) (nZ : ℕ) : ℕ :=
  ⌊gamma * nZ / R⌋₊

@[simp] lemma partialMatchingSize_eq (a₀ : ℝ) (nD : ℕ) :
    partialMatchingSize a₀ nD = ⌊a₀ * Real.sqrt nD / 4⌋₊ := rfl

/-- Choose the two free constants in the partial-exposure union bound.
The parameter `A` is an arbitrary positive upper bound imposed by the
graph-theoretic part of the argument.  Thus the returned `a₀` can be made
simultaneously small enough for every preceding deterministic estimate.

The concrete choice `Q = 1` is already sufficient: `a₀` is chosen below
both `A` and `1 / (16 * (C + 1))`. -/
theorem exists_partialExposureConstants
    {K : ℕ} {A C : ℝ}
    (hK : 0 < K) (hA : 0 < A) (hC : 0 ≤ C) :
    ∃ a₀ Q : ℝ,
      0 < a₀ ∧ a₀ ≤ A ∧ 0 < Q ∧
        a₀ * Real.exp (-(Q ^ 2 / (64 * (K : ℝ) ^ 2))) +
            a₀ ^ 2 * C / 16 ≤ 3 / 16 := by
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have hCplus : 0 < C + 1 := by linarith
  have hden : 0 < 16 * (C + 1) := mul_pos (by norm_num) hCplus
  let cap : ℝ := 1 / (16 * (C + 1))
  have hcap : 0 < cap := by
    dsimp [cap]
    positivity
  let a₀ : ℝ := min A cap
  have ha₀ : 0 < a₀ := by
    dsimp [a₀]
    exact lt_min hA hcap
  have haA : a₀ ≤ A := by
    dsimp [a₀]
    exact min_le_left _ _
  have haCap : a₀ ≤ cap := by
    dsimp [a₀]
    exact min_le_right _ _
  have hcapSixteenth : cap ≤ 1 / 16 := by
    dsimp [cap]
    apply (div_le_iff₀ hden).2
    nlinarith
  have haSixteenth : a₀ ≤ 1 / 16 := haCap.trans hcapSixteenth
  have hfracC : C / (16 * (C + 1)) ≤ 1 / 16 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hcapC : cap * C ≤ 1 / 16 := by
    simpa [cap, div_eq_mul_inv, mul_comm] using hfracC
  have haC : a₀ * C ≤ 1 / 16 :=
    (mul_le_mul_of_nonneg_right haCap hC).trans hcapC
  have ha₀nonneg : 0 ≤ a₀ := ha₀.le
  have haCnonneg : 0 ≤ a₀ * C := mul_nonneg ha₀nonneg hC
  have hsquareC : a₀ ^ 2 * C ≤ 1 / 256 := by
    calc
      a₀ ^ 2 * C = a₀ * (a₀ * C) := by ring
      _ ≤ (1 / 16 : ℝ) * (1 / 16) :=
        mul_le_mul haSixteenth haC haCnonneg (by norm_num)
      _ = 1 / 256 := by norm_num
  have hcollision : a₀ ^ 2 * C / 16 ≤ 1 / 16 := by
    nlinarith
  have hfracNonneg :
      0 ≤ (1 : ℝ) ^ 2 / (64 * (K : ℝ) ^ 2) := by positivity
  have hexp :
      Real.exp (-((1 : ℝ) ^ 2 / (64 * (K : ℝ) ^ 2))) ≤ 1 := by
    calc
      Real.exp (-((1 : ℝ) ^ 2 / (64 * (K : ℝ) ^ 2)))
          ≤ Real.exp 0 := Real.exp_le_exp.mpr (neg_nonpos.mpr hfracNonneg)
      _ = 1 := Real.exp_zero
  have hfirst :
      a₀ * Real.exp (-((1 : ℝ) ^ 2 / (64 * (K : ℝ) ^ 2))) ≤ 1 / 16 := by
    calc
      a₀ * Real.exp (-((1 : ℝ) ^ 2 / (64 * (K : ℝ) ^ 2)))
          ≤ a₀ * 1 := mul_le_mul_of_nonneg_left hexp ha₀nonneg
      _ = a₀ := mul_one _
      _ ≤ 1 / 16 := haSixteenth
  refine ⟨a₀, 1, ha₀, haA, by norm_num, ?_⟩
  norm_num only [one_pow]
  linarith

/-- Eventual four-term union budget for the graph-specific partial
exposure.  `C` is the fixed anti-concentration point-mass constant.  The
displayed smallness condition is precisely the remaining constant choice:
the diversity term tends to zero, while the two degree terms and collision
term have the stated limiting upper bounds. -/
theorem exists_partialExposureBudget
    {K : ℕ} {a₀ theta Q C : ℝ}
    (hK : 0 < K) (ha₀ : 0 < a₀) (htheta : 0 < theta)
    (hQ : 0 < Q) (hC : 0 ≤ C)
    (hsmall :
      a₀ * Real.exp (-(Q ^ 2 / (64 * (K : ℝ) ^ 2))) +
          a₀ ^ 2 * C / 16 ≤ 3 / 16) :
    ∃ N : ℕ, ∀ nD ≥ N, ∀ m : ℕ, 2 * nD ≤ m →
      let s₀ := partialMatchingSize a₀ nD
      let pDiv := balancedLinearFailure nD K (theta * nD)
      let pDegree := balancedLinearFailure nD K (Q * Real.sqrt nD)
      let pCollision := C / Real.sqrt m
      (s₀.choose 2 : ℝ) * pDiv +
          s₀ * pDegree / Real.sqrt nD +
          s₀ * pDegree / Real.sqrt nD +
          (s₀.choose 2 : ℝ) * pCollision / Real.sqrt nD ≤ 1 / 4 := by
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  let b : ℝ := theta ^ 2 / (64 * (K : ℝ) ^ 2)
  have hb : 0 < b := by dsimp [b]; positivity
  let Adiv : ℝ := a₀ ^ 2 / 8
  have hAdiv : 0 ≤ Adiv := by dsimp [Adiv]; positivity
  obtain ⟨Ndiv, hNdiv⟩ :=
    exists_polynomial_mul_exp_neg_lt Adiv b 1 hAdiv hb (1 / 16) (by norm_num)
  refine ⟨max 1 Ndiv, ?_⟩
  intro nD hnD m hm
  dsimp only
  have hnD1 : 1 ≤ nD := (le_max_left _ _).trans hnD
  have hNdiv' : Ndiv ≤ nD := (le_max_right _ _).trans hnD
  have hnDreal : (0 : ℝ) < nD := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hnD1)
  have hm1 : 1 ≤ m := by omega
  have hmreal : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm1)
  have hsqrtDPos : 0 < Real.sqrt nD := Real.sqrt_pos.2 hnDreal
  have hsqrtMPos : 0 < Real.sqrt m := Real.sqrt_pos.2 hmreal
  have hsqrtDSq : (Real.sqrt nD) ^ 2 = (nD : ℝ) :=
    Real.sq_sqrt hnDreal.le
  have hs₀ : (partialMatchingSize a₀ nD : ℝ) ≤
      a₀ / 4 * Real.sqrt nD := by
    rw [partialMatchingSize]
    have hfloor := Nat.floor_le
      (show 0 ≤ a₀ * Real.sqrt nD / 4 by positivity)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hfloor
  have hs₀nonneg : (0 : ℝ) ≤ partialMatchingSize a₀ nD := by positivity
  have hs₀sq : (partialMatchingSize a₀ nD : ℝ) ^ 2 ≤
      a₀ ^ 2 / 16 * nD := by
    have hsquare := mul_self_le_mul_self hs₀nonneg hs₀
    calc
      (partialMatchingSize a₀ nD : ℝ) ^ 2 =
          (partialMatchingSize a₀ nD : ℝ) *
            partialMatchingSize a₀ nD := by ring
      _ ≤ (a₀ / 4 * Real.sqrt nD) *
            (a₀ / 4 * Real.sqrt nD) := hsquare
      _ = a₀ ^ 2 / 16 * (Real.sqrt nD) ^ 2 := by ring
      _ = a₀ ^ 2 / 16 * nD := by rw [hsqrtDSq]
  have hchoose : ((partialMatchingSize a₀ nD).choose 2 : ℝ) ≤
      (partialMatchingSize a₀ nD : ℝ) ^ 2 := by
    exact_mod_cast Nat.choose_le_pow (partialMatchingSize a₀ nD) 2
  have hpDiv : balancedLinearFailure nD K (theta * nD) =
      2 * Real.exp (-b * nD) := by
    simp only [balancedLinearFailure]
    congr 2
    congr 1
    dsimp [b]
    field_simp
    ring
  have hpDegree : balancedLinearFailure nD K (Q * Real.sqrt nD) =
      2 * Real.exp (-(Q ^ 2 / (64 * (K : ℝ) ^ 2))) := by
    simp only [balancedLinearFailure]
    congr 2
    congr 1
    rw [show (Q * Real.sqrt nD) ^ 2 = Q ^ 2 * nD by
      rw [mul_pow, hsqrtDSq]]
    field_simp
    ring
  have hdivTerm : ((partialMatchingSize a₀ nD).choose 2 : ℝ) *
      balancedLinearFailure nD K (theta * nD) ≤ 1 / 16 := by
    rw [hpDiv]
    have hdecay : 0 ≤ Real.exp (-b * nD) := (Real.exp_pos _).le
    calc
      ((partialMatchingSize a₀ nD).choose 2 : ℝ) *
          (2 * Real.exp (-b * nD)) ≤
          (a₀ ^ 2 / 16 * nD) * (2 * Real.exp (-b * nD)) := by
            exact mul_le_mul_of_nonneg_right (hchoose.trans hs₀sq)
              (mul_nonneg (by norm_num) hdecay)
      _ = Adiv * (nD : ℝ) ^ 1 * Real.exp (-b * nD) := by
            dsimp [Adiv]
            ring
      _ ≤ 1 / 16 := (hNdiv nD hNdiv').le
  have hdegreeTerms :
      (partialMatchingSize a₀ nD : ℝ) *
            balancedLinearFailure nD K (Q * Real.sqrt nD) /
            Real.sqrt nD +
          (partialMatchingSize a₀ nD : ℝ) *
            balancedLinearFailure nD K (Q * Real.sqrt nD) /
            Real.sqrt nD ≤
        a₀ * Real.exp (-(Q ^ 2 / (64 * (K : ℝ) ^ 2))) := by
    rw [hpDegree]
    have hExp : 0 ≤ Real.exp (-(Q ^ 2 / (64 * (K : ℝ) ^ 2))) :=
      (Real.exp_pos _).le
    have hterm :
        (partialMatchingSize a₀ nD : ℝ) *
              (2 * Real.exp (-(Q ^ 2 / (64 * (K : ℝ) ^ 2)))) /
              Real.sqrt nD ≤
            (a₀ / 4 * Real.sqrt nD) *
              (2 * Real.exp (-(Q ^ 2 / (64 * (K : ℝ) ^ 2)))) /
              Real.sqrt nD := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hs₀ (mul_nonneg (by norm_num) hExp))
        hsqrtDPos.le
    calc
      (partialMatchingSize a₀ nD : ℝ) *
              (2 * Real.exp (-(Q ^ 2 / (64 * (K : ℝ) ^ 2)))) /
              Real.sqrt nD +
            (partialMatchingSize a₀ nD : ℝ) *
              (2 * Real.exp (-(Q ^ 2 / (64 * (K : ℝ) ^ 2)))) /
              Real.sqrt nD ≤
          (a₀ / 4 * Real.sqrt nD) *
              (2 * Real.exp (-(Q ^ 2 / (64 * (K : ℝ) ^ 2)))) /
              Real.sqrt nD +
            (a₀ / 4 * Real.sqrt nD) *
              (2 * Real.exp (-(Q ^ 2 / (64 * (K : ℝ) ^ 2)))) /
              Real.sqrt nD := add_le_add hterm hterm
      _ = a₀ * Real.exp (-(Q ^ 2 / (64 * (K : ℝ) ^ 2))) := by
        field_simp
        ring
  have hsqrtMono : Real.sqrt nD ≤ Real.sqrt m := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast (show nD ≤ m by omega)
  have hden : (nD : ℝ) ≤ Real.sqrt m * Real.sqrt nD := by
    calc
      (nD : ℝ) = Real.sqrt nD * Real.sqrt nD := by
        rw [← pow_two, hsqrtDSq]
      _ ≤ Real.sqrt m * Real.sqrt nD := by gcongr
  have hcollisionTerm :
      ((partialMatchingSize a₀ nD).choose 2 : ℝ) *
          (C / Real.sqrt m) / Real.sqrt nD ≤ a₀ ^ 2 * C / 16 := by
    have hdenPos : 0 < Real.sqrt m * Real.sqrt nD :=
      mul_pos hsqrtMPos hsqrtDPos
    calc
      ((partialMatchingSize a₀ nD).choose 2 : ℝ) *
          (C / Real.sqrt m) / Real.sqrt nD =
          (((partialMatchingSize a₀ nD).choose 2 : ℝ) * C) /
            (Real.sqrt m * Real.sqrt nD) := by field_simp
      _ ≤ ((a₀ ^ 2 / 16 * nD) * C) /
            (Real.sqrt m * Real.sqrt nD) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hchoose.trans hs₀sq) hC) hdenPos.le
      _ ≤ a₀ ^ 2 * C / 16 := by
        rw [div_le_iff₀ hdenPos]
        have hscaled := mul_le_mul_of_nonneg_left hden
          (show 0 ≤ a₀ ^ 2 * C / 16 by positivity)
        nlinarith
  linarith

@[simp] lemma uniformAugmentationSize_eq (delta : ℝ) (K nD : ℕ) :
    uniformAugmentationSize delta K nD =
      ⌊delta * Real.sqrt nD / K⌋₊ := rfl

@[simp] lemma thinnedMatchingSize_eq (gamma R : ℝ) (nZ : ℕ) :
    thinnedMatchingSize gamma R nZ = ⌊gamma * nZ / R⌋₊ := rfl

/-- The coarse eventual estimates common to both exposure stages. -/
structure BalancedBounds (K nD : ℕ) (a₀ a₁ Q₁ delta : ℝ) : Prop where
  order_pos : 1 ≤ nD
  sqrt_le_order : Real.sqrt nD ≤ nD
  partial_lower :
    a₀ / 8 * Real.sqrt nD ≤ (partialMatchingSize a₀ nD : ℝ)
  partial_upper :
    (2 : ℝ) * partialMatchingSize a₀ nD ≤ a₀ * Real.sqrt nD
  diversity_union_budget :
    ((partialMatchingSize a₀ nD : ℝ) ^ 2) * 2 *
        Real.exp (-(a₁ ^ 2 / (4 * K ^ 2)) * nD) < 1 / 32
  variance_slack :
    a₁ * nD - 2 * Q₁ ^ 2 ≥ a₁ * nD / 2
  augmentation_two : 2 ≤ uniformAugmentationSize delta K nD
  augmentation_lower :
    delta / (2 * K) * Real.sqrt nD ≤
      (uniformAugmentationSize delta K nD : ℝ)
  augmentation_upper :
    (uniformAugmentationSize delta K nD : ℝ) ≤ delta * Real.sqrt nD

/-- All square-root rounding, variance slack, and exponential diversity
budgets needed in the balanced augmentation hold after one threshold. -/
theorem exists_balancedBounds
    {K : ℕ} {a₀ a₁ Q₁ delta : ℝ}
    (hK : 0 < K) (ha₀ : 0 < a₀) (ha₁ : 0 < a₁)
    (hdelta : 0 < delta) :
    ∃ N : ℕ, ∀ nD ≥ N, BalancedBounds K nD a₀ a₁ Q₁ delta := by
  let b : ℝ := a₁ ^ 2 / (4 * (K : ℝ) ^ 2)
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨Npartial, hpartial⟩ :=
    exists_eighth_mul_sqrt_le_quarter_floor a₀ ha₀
  obtain ⟨Naug, haug⟩ :=
    exists_half_mul_sqrt_le_floor (delta / K) (by positivity)
  obtain ⟨Ntwo, htwo⟩ := exists_const_le_mul_sqrt (delta / K) 4 (by positivity)
  obtain ⟨Nvar, hvar⟩ := exists_nat_rpow_ge 1
    (4 * Q₁ ^ 2 / a₁) (by norm_num)
  let A : ℝ := a₀ ^ 2 / 8
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨Nexp, hexp⟩ :=
    exists_polynomial_mul_exp_neg_lt A b 1 hA hb (1 / 32) (by norm_num)
  let N := max 1 (max Npartial (max Naug (max Ntwo (max Nvar Nexp))))
  refine ⟨N, ?_⟩
  intro nD hnD
  have hn1 : 1 ≤ nD := (le_max_left _ _).trans hnD
  have htail : max Npartial (max Naug (max Ntwo (max Nvar Nexp))) ≤ nD :=
    (le_max_right _ _).trans hnD
  have hNpartial : Npartial ≤ nD := (le_max_left _ _).trans htail
  have htail2 : max Naug (max Ntwo (max Nvar Nexp)) ≤ nD :=
    (le_max_right _ _).trans htail
  have hNaug : Naug ≤ nD := (le_max_left _ _).trans htail2
  have htail3 : max Ntwo (max Nvar Nexp) ≤ nD :=
    (le_max_right _ _).trans htail2
  have hNtwo : Ntwo ≤ nD := (le_max_left _ _).trans htail3
  have htail4 : max Nvar Nexp ≤ nD := (le_max_right _ _).trans htail3
  have hNvar : Nvar ≤ nD := (le_max_left _ _).trans htail4
  have hNexp : Nexp ≤ nD := (le_max_right _ _).trans htail4
  have hnreal : (0 : ℝ) < nD := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hpartialUpper :
      (2 : ℝ) * partialMatchingSize a₀ nD ≤ a₀ * Real.sqrt nD :=
    twice_quarter_floor_le a₀ ha₀.le nD
  have hpartialSq :
      ((partialMatchingSize a₀ nD : ℝ) ^ 2) * 2 ≤ A * nD := by
    have hsqrtSq : (Real.sqrt nD) ^ 2 = (nD : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg nD)
    have hpartialQuarter : (partialMatchingSize a₀ nD : ℝ) ≤
        a₀ * Real.sqrt nD / 4 := by
      exact Nat.floor_le (by positivity)
    have hpartialNonneg : (0 : ℝ) ≤ partialMatchingSize a₀ nD := by
      positivity
    have hsquare := mul_self_le_mul_self
      hpartialNonneg hpartialQuarter
    calc
      ((partialMatchingSize a₀ nD : ℝ) ^ 2) * 2 =
          2 * ((partialMatchingSize a₀ nD : ℝ) *
            partialMatchingSize a₀ nD) := by ring
      _ ≤ 2 * ((a₀ * Real.sqrt nD / 4) *
            (a₀ * Real.sqrt nD / 4)) := by gcongr
      _ = a₀ ^ 2 / 8 * (Real.sqrt nD) ^ 2 := by ring
      _ = A * nD := by rw [hsqrtSq]
  have hexp' := hexp nD hNexp
  have hdecay : 0 ≤ Real.exp (-b * nD) := (Real.exp_pos _).le
  have hunion :
      ((partialMatchingSize a₀ nD : ℝ) ^ 2) * 2 *
          Real.exp (-b * nD) < 1 / 32 := by
    exact (mul_le_mul_of_nonneg_right hpartialSq hdecay).trans_lt (by
      simpa [A] using hexp')
  have hvarLarge := hvar nD hNvar
  have hvariance : a₁ * nD - 2 * Q₁ ^ 2 ≥ a₁ * nD / 2 := by
    rw [Real.rpow_one] at hvarLarge
    have hscaled := mul_le_mul_of_nonneg_left hvarLarge ha₁.le
    rw [mul_div_cancel₀ (4 * Q₁ ^ 2) ha₁.ne'] at hscaled
    nlinarith
  have haugLowerRaw := haug nD hNaug
  have haugLower : delta / (2 * K) * Real.sqrt nD ≤
      (uniformAugmentationSize delta K nD : ℝ) := by
    have harg : delta / (K : ℝ) * Real.sqrt nD =
        delta * Real.sqrt nD / K := by ring
    calc
      delta / (2 * K) * Real.sqrt nD =
          delta / K / 2 * Real.sqrt nD := by ring
      _ ≤ (⌊delta / K * Real.sqrt nD⌋₊ : ℝ) := haugLowerRaw
      _ = (uniformAugmentationSize delta K nD : ℝ) := by
        simp only [uniformAugmentationSize, harg]
  have haugRaw := htwo nD hNtwo
  have haugTwo : 2 ≤ uniformAugmentationSize delta K nD := by
    rw [uniformAugmentationSize, Nat.le_floor_iff' (by omega : (2 : ℕ) ≠ 0)]
    have : (4 : ℝ) ≤ delta * Real.sqrt nD / K := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using haugRaw
    linarith
  have haugUpper : (uniformAugmentationSize delta K nD : ℝ) ≤
      delta * Real.sqrt nD := by
    calc
      (uniformAugmentationSize delta K nD : ℝ)
          ≤ delta * Real.sqrt nD / K := by
            exact Nat.floor_le (by positivity)
      _ ≤ delta * Real.sqrt nD := by
        exact div_le_self (mul_nonneg hdelta.le (Real.sqrt_nonneg _))
          (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hK.ne'))
  exact {
    order_pos := hn1
    sqrt_le_order := sqrt_nat_le_nat hn1
    partial_lower := hpartial nD hNpartial
    partial_upper := hpartialUpper
    diversity_union_budget := by simpa [b] using hunion
    variance_slack := hvariance
    augmentation_two := haugTwo
    augmentation_lower := haugLower
    augmentation_upper := haugUpper }

/-- The eventual lower bound for the matching which survives Turán
thinning.  The input augmentation size is the uniform `K`-valid floor
defined above. -/
theorem exists_thinnedMatchingBounds
    {K : ℕ} {delta gamma R : ℝ}
    (hK : 0 < K) (hdelta : 0 < delta)
    (hgamma : 0 < gamma) (hR : 0 < R) :
    ∃ N : ℕ, ∀ nD ≥ N,
      2 ≤ thinnedMatchingSize gamma R
        (uniformAugmentationSize delta K nD) ∧
      gamma * delta / (4 * K * R) * Real.sqrt nD ≤
        (thinnedMatchingSize gamma R
          (uniformAugmentationSize delta K nD) : ℝ) := by
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  let a : ℝ := gamma * delta / (2 * K * R)
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨Naug, haug⟩ :=
    exists_half_mul_sqrt_le_floor (delta / K) (by positivity)
  obtain ⟨Nlarge, hlarge⟩ := exists_const_le_mul_sqrt a 4 ha
  refine ⟨max Naug Nlarge, ?_⟩
  intro nD hnD
  have hNaug : Naug ≤ nD := (le_max_left _ _).trans hnD
  have hNlarge : Nlarge ≤ nD := (le_max_right _ _).trans hnD
  have hnZ : delta / (2 * K) * Real.sqrt nD ≤
      (uniformAugmentationSize delta K nD : ℝ) := by
    have hraw := haug nD hNaug
    have harg : delta / (K : ℝ) * Real.sqrt nD =
        delta * Real.sqrt nD / K := by ring
    calc
      delta / (2 * K) * Real.sqrt nD =
          delta / K / 2 * Real.sqrt nD := by ring
      _ ≤ (⌊delta / K * Real.sqrt nD⌋₊ : ℝ) := hraw
      _ = (uniformAugmentationSize delta K nD : ℝ) := by
        simp only [uniformAugmentationSize, harg]
  have hrawLarge := hlarge nD hNlarge
  have hthinArg : 4 ≤ gamma *
      (uniformAugmentationSize delta K nD : ℝ) / R := by
    have hscaled := mul_le_mul_of_nonneg_left hnZ
      (show 0 ≤ gamma / R by positivity)
    calc
      4 ≤ a * Real.sqrt nD := hrawLarge
      _ = gamma / R *
          (delta / (2 * K) * Real.sqrt nD) := by
            dsimp [a]
            ring
      _ ≤ gamma / R * uniformAugmentationSize delta K nD := hscaled
      _ = gamma * uniformAugmentationSize delta K nD / R := by ring
  have htwo : 2 ≤ thinnedMatchingSize gamma R
      (uniformAugmentationSize delta K nD) := by
    rw [thinnedMatchingSize, Nat.le_floor_iff' (by omega : (2 : ℕ) ≠ 0)]
    linarith
  have hfloorHalf := half_le_natFloor (show
      2 ≤ gamma * (uniformAugmentationSize delta K nD : ℝ) / R by
        linarith [hthinArg])
  have hlower : gamma * delta / (4 * K * R) * Real.sqrt nD ≤
      (thinnedMatchingSize gamma R
        (uniformAugmentationSize delta K nD) : ℝ) := by
    have hscaled := mul_le_mul_of_nonneg_left hnZ
      (show 0 ≤ gamma / R by positivity)
    calc
      gamma * delta / (4 * K * R) * Real.sqrt nD =
          (gamma / R *
            (delta / (2 * K) * Real.sqrt nD)) / 2 := by ring
      _ ≤ (gamma * uniformAugmentationSize delta K nD / R) / 2 := by
            apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
            simpa only [div_mul_eq_mul_div] using hscaled
      _ ≤ (⌊gamma * uniformAugmentationSize delta K nD / R⌋₊ : ℝ) :=
        hfloorHalf
      _ = (thinnedMatchingSize gamma R
          (uniformAugmentationSize delta K nD) : ℝ) := rfl
  exact ⟨htwo, hlower⟩

end

end Erdos636.AsymptoticThresholds
