/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 764.
https://www.erdosproblems.com/forum/thread/764

Informal authors:
- Robert Vaughan

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos764.md
-/
/-
This is a Lean formalization of the negative answer to Erdős Problem 764.

The problem asks whether an indicator can have a three-fold additive
convolution whose summatory function is `c * N + O(1)` for some `c > 0`.
Vaughan proved a stronger theorem in:

R. C. Vaughan, "On the addition of sequences of integers",
Journal of Number Theory 4 (1972), 1--16.

The proof below is the bounded-error specialization described in
`tex/764.tex`.  It uses the differentiated generating-function identity,
Fourier orthogonality on a circle, and a short geometric kernel.
-/

import Mathlib

namespace Erdos764

open scoped BigOperators Classical
open Finset Nat Asymptotics Filter

noncomputable def indicator (A : Set ℕ) (n : ℕ) : ℕ :=
  if n ∈ A then 1 else 0

def addConv (f g : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, f p.1 * g p.2

noncomputable def tripleConv (A : Set ℕ) (n : ℕ) : ℕ :=
  addConv (addConv (indicator A) (indicator A)) (indicator A) n

noncomputable def summatory (A : Set ℕ) (N : ℕ) : ℕ :=
  ∑ n ∈ range (N + 1), tripleConv A n

noncomputable def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  #((range (N + 1)).filter (fun n ↦ n ∈ A))

noncomputable def tripleReps (A : Set ℕ) (n : ℕ) :
    Finset (Σ _p : ℕ × ℕ, ℕ × ℕ) :=
  (Finset.HasAntidiagonal.antidiagonal n).sigma fun p ↦
    (Finset.HasAntidiagonal.antidiagonal p.1).filter fun q ↦
      q.1 ∈ A ∧ q.2 ∈ A ∧ p.2 ∈ A

lemma tripleConv_eq_card_tripleReps (A : Set ℕ) (n : ℕ) :
    tripleConv A n = #(tripleReps A n) := by
  simp only [tripleConv, addConv, indicator, tripleReps, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hp₂ : p.2 ∈ A
  · simp only [hp₂, if_true, mul_one]
    rw [Finset.card_eq_sum_ones]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hq₁ : q.1 ∈ A <;> by_cases hq₂ : q.2 ∈ A <;> simp [hq₁, hq₂]
  · simp [hp₂]

noncomputable def summatoryReps (A : Set ℕ) (N : ℕ) :
    Finset (Σ _n : ℕ, Σ _p : ℕ × ℕ, ℕ × ℕ) :=
  (range (N + 1)).sigma (tripleReps A)

lemma summatory_eq_card_summatoryReps (A : Set ℕ) (N : ℕ) :
    summatory A N = #(summatoryReps A N) := by
  simp only [summatory, summatoryReps, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro n hn
  exact tripleConv_eq_card_tripleReps A n

noncomputable def membersUpTo (A : Set ℕ) (N : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (fun n ↦ n ∈ A)

noncomputable def boundedTriples (A : Set ℕ) (N : ℕ) :
    Finset ((ℕ × ℕ) × ℕ) :=
  ((membersUpTo A N).product (membersUpTo A N)).product (membersUpTo A N)

def forgetSums : (Σ _n : ℕ, Σ _p : ℕ × ℕ, ℕ × ℕ) → ((ℕ × ℕ) × ℕ)
  | ⟨_, ⟨p, q⟩⟩ => ((q.1, q.2), p.2)

lemma forgetSums_mapsTo (A : Set ℕ) (N : ℕ) :
    Set.MapsTo forgetSums (summatoryReps A N : Set _)
      (boundedTriples A N : Set _) := by
  intro x hx
  rcases x with ⟨n, ⟨p, q⟩⟩
  simp only [summatoryReps, Finset.mem_coe, Finset.mem_sigma] at hx
  rcases hx with ⟨hn, hx⟩
  simp only [tripleReps, Finset.mem_sigma] at hx
  rcases hx with ⟨hpn, hq⟩
  simp only [Finset.mem_filter] at hq
  rcases hq with ⟨hqp, hqA⟩
  have hnN : n ≤ N := by simpa using hn
  have hp_eq : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hpn
  have hq_eq : q.1 + q.2 = p.1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hqp
  change ((q.1, q.2), p.2) ∈ boundedTriples A N
  change ((q.1, q.2), p.2) ∈
    ((membersUpTo A N).product (membersUpTo A N)).product (membersUpTo A N)
  rcases hqA with ⟨hq₁A, hq₂A, hp₂A⟩
  apply Finset.mem_product.mpr
  constructor
  · apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (show q.1 < N + 1 by omega), hq₁A⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (show q.2 < N + 1 by omega), hq₂A⟩
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (show p.2 < N + 1 by omega), hp₂A⟩

lemma forgetSums_injOn (A : Set ℕ) (N : ℕ) :
    Set.InjOn forgetSums (summatoryReps A N : Set _) := by
  intro x hx y hy hxy
  rcases x with ⟨n, ⟨p, q⟩⟩
  rcases y with ⟨n', ⟨p', q'⟩⟩
  simp only [summatoryReps, Finset.mem_coe, Finset.mem_sigma] at hx hy
  rcases hx with ⟨_, hx⟩
  rcases hy with ⟨_, hy⟩
  simp only [tripleReps, Finset.mem_sigma] at hx hy
  rcases hx with ⟨hpn, hq⟩
  rcases hy with ⟨hpn', hq'⟩
  have hqmem := (Finset.mem_filter.mp hq).1
  have hqmem' := (Finset.mem_filter.mp hq').1
  have hp_eq : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hpn
  have hp_eq' : p'.1 + p'.2 = n' := Finset.HasAntidiagonal.mem_antidiagonal.mp hpn'
  have hq_eq : q.1 + q.2 = p.1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hqmem
  have hq_eq' : q'.1 + q'.2 = p'.1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hqmem'
  simp only [forgetSums, Prod.mk.injEq] at hxy
  rcases hxy with ⟨⟨hq₁, hq₂⟩, hp₂⟩
  have hq_eq_pair : q = q' := Prod.ext hq₁ hq₂
  subst q'
  have hp₁ : p.1 = p'.1 := by omega
  have hp_eq_pair : p = p' := Prod.ext hp₁ hp₂
  subst p'
  have hn : n = n' := by omega
  cases hn
  rfl

lemma card_summatoryReps_le_card_boundedTriples (A : Set ℕ) (N : ℕ) :
    #(summatoryReps A N) ≤ #(boundedTriples A N) :=
  Finset.card_le_card_of_injOn forgetSums (forgetSums_mapsTo A N) (forgetSums_injOn A N)

lemma card_boundedTriples (A : Set ℕ) (N : ℕ) :
    #(boundedTriples A N) = countingFunction A N ^ 3 := by
  simp [boundedTriples, membersUpTo, countingFunction, Finset.card_product, pow_succ]

lemma summatory_le_countingFunction_cube (A : Set ℕ) (N : ℕ) :
    summatory A N ≤ countingFunction A N ^ 3 := by
  rw [summatory_eq_card_summatoryReps, ← card_boundedTriples]
  exact card_summatoryReps_le_card_boundedTriples A N

noncomputable def remainder (A : Set ℕ) (c : ℝ) (N : ℕ) : ℝ :=
  (summatory A N : ℝ) - c * N

lemma isBigO_one_iff_uniform_remainder_bound (A : Set ℕ) (c : ℝ) :
    ((remainder A c) =O[Filter.atTop] (fun _ : ℕ ↦ (1 : ℝ))) ↔
      ∃ C : ℝ, ∀ N : ℕ, |remainder A c N| ≤ C := by
  rw [isBigO_one_nat_atTop_iff]
  simp only [Real.norm_eq_abs]

lemma uniform_remainder_bound_of_isBigO_one (A : Set ℕ) (c : ℝ)
    (h : (remainder A c) =O[Filter.atTop] (fun _ : ℕ ↦ (1 : ℝ))) :
    ∃ C : ℝ, ∀ N : ℕ, |remainder A c N| ≤ C :=
  (isBigO_one_iff_uniform_remainder_bound A c).mp h

open scoped Topology BigOperators
open Filter Set Finset

noncomputable section

noncomputable def indicatorC (A : Set ℕ) (n : ℕ) : ℂ := A.indicator (fun _ ↦ 1) n

def F (A : Set ℕ) (z : ℂ) : ℂ := ∑' n : ℕ, indicatorC A n * z ^ n

def E (P : ℕ → ℂ) (z : ℂ) : ℂ := ∑' n : ℕ, P n * z ^ n

def Fderiv (A : Set ℕ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (n : ℂ) * indicatorC A n * z ^ (n - 1)

def Ederiv (P : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (n : ℂ) * P n * z ^ (n - 1)

lemma norm_indicator_le_one (A : Set ℕ) (n : ℕ) : ‖indicatorC A n‖ ≤ 1 := by
  classical
  by_cases hn : n ∈ A <;> simp [indicatorC, hn]

lemma summable_indicator_mul_pow (A : Set ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ ↦ indicatorC A n * z ^ n) := by
  apply (summable_geometric_of_lt_one (norm_nonneg z) hz).of_norm_bounded
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg z) n) (norm_indicator_le_one A n)

lemma summable_norm_indicator_mul_pow (A : Set ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ ↦ ‖indicatorC A n * z ^ n‖) := by
  apply (summable_geometric_of_lt_one (norm_nonneg z) hz).of_nonneg_of_le
  · intro n; positivity
  · intro n
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg z) n) (norm_indicator_le_one A n)

lemma summable_bounded_mul_pow {P : ℕ → ℂ} {C : ℝ} (hC : ∀ n, ‖P n‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ < 1) : Summable (fun n : ℕ ↦ P n * z ^ n) := by
  apply ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left C).of_norm_bounded
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hC n) (pow_nonneg (norm_nonneg z) n)

lemma summable_norm_bounded_mul_pow {P : ℕ → ℂ} {C : ℝ} (hC : ∀ n, ‖P n‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ < 1) : Summable (fun n : ℕ ↦ ‖P n * z ^ n‖) := by
  apply ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left C).of_nonneg_of_le
  · intro n; positivity
  · intro n
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hC n) (pow_nonneg (norm_nonneg z) n)

lemma summable_nat_mul_pow_pred {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ ↦ (n : ℝ) * r ^ (n - 1)) := by
  rw [← summable_nat_add_iff 1]
  have h1 : Summable (fun n : ℕ ↦ (n : ℝ) * r ^ n) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (by simpa [abs_of_nonneg hr0]))
  have h2 : Summable (fun n : ℕ ↦ r ^ n) := summable_geometric_of_lt_one hr0 hr1
  simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using h1.add h2

lemma summable_indicator_deriv (A : Set ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ ↦ (n : ℂ) * indicatorC A n * z ^ (n - 1)) := by
  apply (summable_nat_mul_pow_pred (norm_nonneg z) hz).of_norm_bounded
  intro n
  rw [norm_mul, norm_mul, norm_natCast, norm_pow]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (Nat.cast_nonneg n) (norm_indicator_le_one A n))
    (pow_nonneg (norm_nonneg z) (n - 1))

/-- Termwise differentiation of a power series whose coefficients have a common norm bound. -/
lemma hasDerivAt_E {P : ℕ → ℂ} {C : ℝ} (hC : ∀ n, ‖P n‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (E P) (∑' n : ℕ, (n : ℂ) * P n * z ^ (n - 1)) z := by
  let R : ℝ := (‖z‖ + 1) / 2
  have hC0 : 0 ≤ C := (norm_nonneg (P 0)).trans (hC 0)
  have hR0 : 0 < R := by dsimp [R]; positivity
  have hzR : ‖z‖ < R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hu : Summable (fun n : ℕ ↦ C * ((n : ℝ) * R ^ (n - 1))) :=
    (summable_nat_mul_pow_pred hR0.le hR1).mul_left C
  have hd : ∀ n : ℕ, ∀ y ∈ Metric.ball (0 : ℂ) R,
      HasDerivAt (fun w : ℂ ↦ P n * w ^ n) (P n * ((n : ℂ) * y ^ (n - 1))) y := by
    intro n y _
    exact (hasDerivAt_pow n y).const_mul (P n)
  have hb : ∀ n : ℕ, ∀ y ∈ Metric.ball (0 : ℂ) R,
      ‖P n * ((n : ℂ) * y ^ (n - 1))‖ ≤ C * ((n : ℝ) * R ^ (n - 1)) := by
    intro n y hy
    rw [norm_mul, norm_mul, norm_natCast, norm_pow]
    have hyr' : ‖y‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hy
    have hyr : ‖y‖ ≤ R := hyr'.le
    calc
      ‖P n‖ * ((n : ℝ) * ‖y‖ ^ (n - 1)) ≤ C * ((n : ℝ) * R ^ (n - 1)) := by
        gcongr
        exact hC n
      _ = C * ((n : ℝ) * R ^ (n - 1)) := rfl
  have H := hasDerivAt_tsum_of_isPreconnected
    (u := fun n : ℕ ↦ C * ((n : ℝ) * R ^ (n - 1)))
    (t := Metric.ball (0 : ℂ) R) hu Metric.isOpen_ball (convex_ball (0 : ℂ) R).isPreconnected
    hd hb
    (y₀ := (0 : ℂ)) (by simpa [Metric.mem_ball] using hR0)
    (summable_bounded_mul_pow hC (by norm_num : ‖(0 : ℂ)‖ < 1))
    (by simpa [Metric.mem_ball, dist_zero_right] using hzR)
  change HasDerivAt (fun w : ℂ ↦ ∑' n : ℕ, P n * w ^ n)
    (∑' n : ℕ, (n : ℂ) * P n * z ^ (n - 1)) z
  apply H.congr_deriv
  apply tsum_congr
  intro n
  ring

/-- Termwise differentiation of the indicatorC generating function in the open unit disk. -/
lemma hasDerivAt_F (A : Set ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (F A) (∑' n : ℕ, (n : ℂ) * indicatorC A n * z ^ (n - 1)) z := by
  exact hasDerivAt_E (P := indicatorC A) (C := 1) (norm_indicator_le_one A) hz

lemma hasDerivAt_F' (A : Set ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (F A) (Fderiv A z) z := hasDerivAt_F A hz

lemma hasDerivAt_E' {P : ℕ → ℂ} {C : ℝ} (hC : ∀ n, ‖P n‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ < 1) : HasDerivAt (E P) (Ederiv P z) z :=
  hasDerivAt_E hC hz

def convC (f g : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2

lemma tsum_mul_tsum_eq_E_conv {f g : ℕ → ℂ} {z : ℂ}
    (hf : Summable (fun n : ℕ ↦ ‖f n * z ^ n‖))
    (hg : Summable (fun n : ℕ ↦ ‖g n * z ^ n‖)) :
    (∑' n : ℕ, f n * z ^ n) * (∑' n : ℕ, g n * z ^ n) = E (convC f g) z := by
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
  apply tsum_congr
  intro n
  rw [convC, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro kl hkl
  have hs : kl.1 + kl.2 = n := mem_antidiagonal.mp hkl
  rw [← hs, pow_add]
  ring

lemma summable_norm_conv_mul_pow {f g : ℕ → ℂ} {z : ℂ}
    (hf : Summable (fun n : ℕ ↦ ‖f n * z ^ n‖))
    (hg : Summable (fun n : ℕ ↦ ‖g n * z ^ n‖)) :
    Summable (fun n : ℕ ↦ ‖convC f g n * z ^ n‖) := by
  apply (summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg).congr
  intro n
  congr 1
  rw [convC, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro kl hkl
  have hs : kl.1 + kl.2 = n := mem_antidiagonal.mp hkl
  rw [← hs, pow_add]
  ring

def tripleCoeff (A : Set ℕ) : ℕ → ℂ := convC (convC (indicatorC A) (indicatorC A)) (indicatorC A)

lemma F_cube_eq_E_tripleCoeff (A : Set ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    F A z ^ 3 = E (tripleCoeff A) z := by
  have hI := summable_norm_indicator_mul_pow A hz
  have hII := summable_norm_conv_mul_pow hI hI
  rw [pow_succ, pow_two, F, tripleCoeff]
  rw [tsum_mul_tsum_eq_E_conv hI hI]
  exact tsum_mul_tsum_eq_E_conv hII hI

def summatoryC (q : ℕ → ℂ) (N : ℕ) : ℂ := ∑ n ∈ range (N + 1), q n

lemma summable_norm_tripleCoeff_mul_pow (A : Set ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ ↦ ‖tripleCoeff A n * z ^ n‖) := by
  exact summable_norm_conv_mul_pow
    (summable_norm_conv_mul_pow (summable_norm_indicator_mul_pow A hz)
      (summable_norm_indicator_mul_pow A hz))
    (summable_norm_indicator_mul_pow A hz)

lemma cube_div_one_sub_eq_E_summatory (A : Set ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    F A z ^ 3 / (1 - z) = E (summatoryC (tripleCoeff A)) z := by
  have hq := summable_norm_tripleCoeff_mul_pow A hz
  have hgeom : Summable (fun n : ℕ ↦ ‖z ^ n‖) := by
    simpa using (summable_geometric_of_norm_lt_one hz).norm
  rw [div_eq_mul_inv, ← tsum_geometric_of_norm_lt_one hz, F_cube_eq_E_tripleCoeff A hz, E]
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hq hgeom]
  apply tsum_congr
  intro n
  rw [summatoryC, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (by simpa using hk)
  calc
    tripleCoeff A k * z ^ k * z ^ (n - k) =
        tripleCoeff A k * (z ^ k * z ^ (n - k)) := by ring
    _ = tripleCoeff A k * z ^ n := by rw [← pow_add, Nat.add_sub_of_le hkn]

lemma summable_linear_mul_pow (c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ ↦ c * (n : ℂ) * z ^ n) := by
  simpa [mul_assoc, pow_one] using
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℂ) 1 hz).mul_left c

/-- The exact generating-function identity obtained from a bounded summatoryC error. -/
lemma bounded_error_generating_identity (A : Set ℕ) (P : ℕ → ℂ) (c : ℂ)
    {C : ℝ} (hC : ∀ n, ‖P n‖ ≤ C)
    (hP : ∀ N, summatoryC (tripleCoeff A) N = P N + c * N)
    {z : ℂ} (hz : ‖z‖ < 1) :
    F A z ^ 3 / (1 - z) = c * (z / (1 - z) ^ 2) + E P z := by
  rw [cube_div_one_sub_eq_E_summatory A hz, E]
  calc
    ∑' n : ℕ, summatoryC (tripleCoeff A) n * z ^ n =
        ∑' n : ℕ, (P n * z ^ n + (c * (n : ℂ) * z ^ n)) := by
          apply tsum_congr
          intro n
          rw [hP]
          push_cast
          ring
    _ = (∑' n : ℕ, P n * z ^ n) + ∑' n : ℕ, c * (n : ℂ) * z ^ n := by
          rw [Summable.tsum_add (summable_bounded_mul_pow hC hz) (summable_linear_mul_pow c hz)]
    _ = c * (z / (1 - z) ^ 2) + ∑' n : ℕ, P n * z ^ n := by
          have hc : (∑' n : ℕ, c * (n : ℂ) * z ^ n) =
              c * ∑' n : ℕ, (n : ℂ) * z ^ n := by
            rw [← tsum_mul_left]
            congr 1
            funext n
            ring
          rw [hc, tsum_coe_mul_geometric_of_norm_lt_one hz]
          ring

lemma F_cube_eq_main_add_error (A : Set ℕ) (P : ℕ → ℂ) (c : ℂ)
    {C : ℝ} (hC : ∀ n, ‖P n‖ ≤ C)
    (hP : ∀ N, summatoryC (tripleCoeff A) N = P N + c * N)
    {z : ℂ} (hz : ‖z‖ < 1) :
    F A z ^ 3 = c * z / (1 - z) + (1 - z) * E P z := by
  have hz1 : 1 - z ≠ 0 := by
    intro h
    have : z = 1 := (sub_eq_zero.mp h).symm
    simpa [this] using hz
  have h := bounded_error_generating_identity A P c hC hP hz
  field_simp [hz1] at h ⊢
  linear_combination h

/-- Differentiating the bounded-error generating identity inside the open unit disk. -/
lemma differentiated_bounded_error_identity (A : Set ℕ) (P : ℕ → ℂ) (c : ℂ)
    {C : ℝ} (hC : ∀ n, ‖P n‖ ≤ C)
    (hP : ∀ N, summatoryC (tripleCoeff A) N = P N + c * N)
    {z : ℂ} (hz : ‖z‖ < 1) :
    3 * F A z ^ 2 * Fderiv A z =
      c / (1 - z) ^ 2 - E P z + (1 - z) * Ederiv P z := by
  have hz1 : 1 - z ≠ 0 := by
    intro h
    have hzone : z = 1 := (sub_eq_zero.mp h).symm
    simp [hzone] at hz
  have hleft := (hasDerivAt_F' A hz).pow 3
  have honeSub := (hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)
  have hmain := (honeSub.inv hz1).const_mul c
  have herr := honeSub.mul (hasDerivAt_E' hC hz)
  have hright := hmain.sub_const c |>.add herr
  have hopen : IsOpen {w : ℂ | ‖w‖ < 1} := isOpen_lt continuous_norm continuous_const
  have heq : (fun w : ℂ ↦ F A w ^ 3) =ᶠ[𝓝 z]
      (fun w : ℂ ↦ c * ((((fun _ : ℂ ↦ 1) - (fun x : ℂ ↦ x) : ℂ → ℂ)) w)⁻¹ - c +
        (((fun _ : ℂ ↦ 1) - (fun x : ℂ ↦ x) : ℂ → ℂ) w) * E P w) := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    have hw1 : 1 - w ≠ 0 := by
      intro h
      have hwone : w = 1 := (sub_eq_zero.mp h).symm
      simp [hwone] at hw
    rw [F_cube_eq_main_add_error A P c hC hP hw]
    simp only [Pi.sub_apply, Function.id_def]
    field_simp [hw1]
    ring
  have hsame := hright.congr_of_eventuallyEq heq
  have hderiv := hleft.unique hsame
  dsimp [Fderiv, Ederiv] at hderiv ⊢
  simp only [Pi.sub_apply, Function.id_def, zero_sub] at hderiv
  field_simp [hz1] at hderiv ⊢
  linear_combination hderiv

lemma norm_E_le (P : ℕ → ℂ) {C : ℝ} (hC : ∀ n, ‖P n‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ < 1) : ‖E P z‖ ≤ C / (1 - ‖z‖) := by
  have hC0 : 0 ≤ C := (norm_nonneg (P 0)).trans (hC 0)
  have hs := summable_norm_bounded_mul_pow hC hz
  have hg : Summable (fun n : ℕ ↦ C * ‖z‖ ^ n) :=
    (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left C
  calc
    ‖E P z‖ ≤ ∑' n : ℕ, ‖P n * z ^ n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, C * ‖z‖ ^ n := by
      apply hs.tsum_le_tsum
      · intro n
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_right (hC n) (pow_nonneg (norm_nonneg z) n)
      · exact hg
    _ = C / (1 - ‖z‖) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (norm_nonneg z) hz]
      simp [div_eq_mul_inv]

lemma norm_Ederiv_le_tsum (P : ℕ → ℂ) {C : ℝ} (hC : ∀ n, ‖P n‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖Ederiv P z‖ ≤ ∑' n : ℕ, C * ((n : ℝ) * ‖z‖ ^ (n - 1)) := by
  have hC0 : 0 ≤ C := (norm_nonneg (P 0)).trans (hC 0)
  have hs : Summable (fun n : ℕ ↦ ‖(n : ℂ) * P n * z ^ (n - 1)‖) := by
    apply (summable_nat_mul_pow_pred (norm_nonneg z) hz).mul_left C |>.of_nonneg_of_le
    · intro n; positivity
    · intro n
      rw [norm_mul, norm_mul, norm_natCast, norm_pow]
      calc
        (n : ℝ) * ‖P n‖ * ‖z‖ ^ (n - 1) ≤
            (n : ℝ) * C * ‖z‖ ^ (n - 1) := by
              gcongr
              exact hC n
        _ = C * ((n : ℝ) * ‖z‖ ^ (n - 1)) := by ring
  have hg : Summable (fun n : ℕ ↦ C * ((n : ℝ) * ‖z‖ ^ (n - 1))) :=
    (summable_nat_mul_pow_pred (norm_nonneg z) hz).mul_left C
  calc
    ‖Ederiv P z‖ ≤ ∑' n : ℕ, ‖(n : ℂ) * P n * z ^ (n - 1)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, C * ((n : ℝ) * ‖z‖ ^ (n - 1)) := by
      apply hs.tsum_le_tsum
      · intro n
        rw [norm_mul, norm_mul, norm_natCast, norm_pow]
        calc
          (n : ℝ) * ‖P n‖ * ‖z‖ ^ (n - 1) ≤
              (n : ℝ) * C * ‖z‖ ^ (n - 1) := by
                gcongr
                exact hC n
          _ = C * ((n : ℝ) * ‖z‖ ^ (n - 1)) := by ring
      · exact hg

end

/-- The radius used in the Erdős--Fuchs argument. -/
noncomputable def radius (X : ℝ) : ℝ := 1 - X⁻¹

lemma radius_nonneg {X : ℝ} (hX : 1 ≤ X) : 0 ≤ radius X := by
  rw [radius]
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  rw [sub_nonneg, inv_le_one₀ hX0]
  exact hX

lemma radius_pos {X : ℝ} (hX : 1 < X) : 0 < radius X := by
  rw [radius, sub_pos]
  exact (inv_lt_one₀ (lt_trans zero_lt_one hX)).2 hX

lemma radius_lt_one {X : ℝ} (hX : 0 < X) : radius X < 1 := by
  rw [radius, sub_lt_self_iff]
  exact inv_pos.mpr hX

lemma one_sub_radius_sq {X : ℝ} (hX : X ≠ 0) :
    1 - (radius X) ^ 2 = (2 - X⁻¹) / X := by
  rw [radius]
  field_simp
  ring

lemma one_div_X_le_one_sub_radius_sq {X : ℝ} (hX : 1 ≤ X) :
    X⁻¹ ≤ 1 - (radius X) ^ 2 := by
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  rw [one_sub_radius_sq (ne_of_gt hX0), div_eq_mul_inv]
  have hInv : X⁻¹ ≤ 1 := (inv_le_one₀ hX0).2 hX
  nlinarith [inv_pos.mpr hX0]

lemma one_sub_radius_sq_le_two_div_X {X : ℝ} (hX : 0 < X) :
    1 - (radius X) ^ 2 ≤ 2 / X := by
  rw [one_sub_radius_sq (ne_of_gt hX)]
  apply (div_le_div_iff_of_pos_right hX).2
  nlinarith [inv_pos.mpr hX]

lemma one_sub_radius_sq_pos {X : ℝ} (hX : 1 < X) :
    0 < 1 - (radius X) ^ 2 := by
  have hr0 := radius_pos hX
  have hr1 := radius_lt_one (lt_trans zero_lt_one hX)
  nlinarith

lemma half_X_le_inv_one_sub_radius_sq {X : ℝ} (hX : 1 < X) :
    X / 2 ≤ (1 - (radius X) ^ 2)⁻¹ := by
  have hd := one_sub_radius_sq_pos hX
  have hu := one_sub_radius_sq_le_two_div_X (lt_trans zero_lt_one hX)
  have htwo : 0 < 2 / X := div_pos (by norm_num) (lt_trans zero_lt_one hX)
  have hi := (inv_le_inv₀ htwo hd).2 hu
  have heq : (2 / X)⁻¹ = X / 2 := by rw [inv_div]
  rwa [heq] at hi

lemma inv_one_sub_radius_sq_le_X {X : ℝ} (hX : 1 < X) :
    (1 - (radius X) ^ 2)⁻¹ ≤ X := by
  have hd := one_sub_radius_sq_pos hX
  have hl := one_div_X_le_one_sub_radius_sq (le_of_lt hX)
  have hX0 : 0 < X := lt_trans zero_lt_one hX
  have hi := (inv_le_inv₀ hd (inv_pos.mpr hX0)).2 hl
  simpa using hi

lemma radius_sq_ge_quarter {X : ℝ} (hX : 2 ≤ X) :
    (1 / 4 : ℝ) ≤ (radius X) ^ 2 := by
  have hX0 : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hinv : X⁻¹ ≤ (1 / 2 : ℝ) := by
    have := (inv_le_inv₀ hX0 (by norm_num : (0 : ℝ) < 2)).2 hX
    norm_num at this ⊢
    exact this
  have hr : (1 / 2 : ℝ) ≤ radius X := by rw [radius]; linarith
  nlinarith [sq_nonneg (radius X - 1 / 2)]

/-- A Bernoulli lower bound for a radial weight.  The budget `2n ≤ X` leaves a
uniform factor `1/2`. -/
lemma radius_pow_ge_half {X : ℝ} (hX : 1 ≤ X) {n : ℕ}
    (hbudget : 2 * (n : ℝ) ≤ X) : (1 / 2 : ℝ) ≤ radius X ^ n := by
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hinv0 : 0 ≤ X⁻¹ := le_of_lt (inv_pos.mpr hX0)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hratio : (n : ℝ) * X⁻¹ ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_right hbudget hinv0
    have hcancel : X * X⁻¹ = 1 := by field_simp
    nlinarith
  have hinv1 : X⁻¹ ≤ 1 := (inv_le_one₀ hX0).2 hX
  have hBernoulli := one_add_mul_le_pow (a := -X⁻¹) (by linarith) n
  have hrw : 1 + -X⁻¹ = radius X := by simp only [radius, sub_eq_add_neg]
  rw [hrw] at hBernoulli
  push_cast at hBernoulli
  nlinarith

/-- The form used for the powers of `x = r²`. -/
lemma radius_sq_pow_ge_half {X : ℝ} (hX : 1 ≤ X) {n : ℕ}
    (hbudget : 4 * (n : ℝ) ≤ X) : (1 / 2 : ℝ) ≤ (radius X ^ 2) ^ n := by
  rw [← pow_mul]
  apply radius_pow_ge_half hX
  push_cast
  nlinarith

/-- With `X=t^9` and `m=t^3`, the radial budget is automatic once `t≥2`. -/
lemma ninth_cube_radial_budget {t : ℝ} (ht : 2 ≤ t) :
    4 * t ^ 3 ≤ t ^ 9 := by
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have ht6 : 4 ≤ t ^ 6 := by
    calc
      4 ≤ 2 ^ 6 := by norm_num
      _ ≤ t ^ 6 := pow_le_pow_left₀ (by norm_num) ht 6
  calc
    4 * t ^ 3 ≤ t ^ 6 * t ^ 3 := mul_le_mul_of_nonneg_right ht6 (pow_nonneg ht0 3)
    _ = t ^ 9 := by ring

/-- The square-root factors in the third upper estimate collapse at the same
perfect-power specialization. -/
lemma sqrt_ninth_mul_sqrt_cube {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt (t ^ 9) * Real.sqrt (t ^ 3) = t ^ 6 := by
  rw [← Real.sqrt_mul (pow_nonneg ht 9)]
  have hprod : t ^ 9 * t ^ 3 = (t ^ 6) ^ 2 := by ring
  rw [hprod, Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg ht 6)]

/-- The generating-function identity and a bounded error force an upper cubic bound. -/
lemma cube_upper_of_gf
    {X c C F E : ℝ} (hX : 1 < X) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hE : |E| ≤ C * (1 - (radius X) ^ 2)⁻¹)
    (hgf : F ^ 3 = c * (radius X) ^ 2 * (1 - (radius X) ^ 2)⁻¹
      + (1 - (radius X) ^ 2) * E) :
    F ^ 3 ≤ (c + C) * X := by
  have hd : 0 ≤ 1 - (radius X) ^ 2 :=
    le_of_lt (one_sub_radius_sq_pos hX)
  have hEinv := inv_one_sub_radius_sq_le_X hX
  have herr : (1 - (radius X) ^ 2) * E ≤ C := by
    have hEle : E ≤ C * (1 - (radius X) ^ 2)⁻¹ :=
      le_trans (le_abs_self E) hE
    calc
      (1 - (radius X) ^ 2) * E
          ≤ (1 - (radius X) ^ 2) * (C * (1 - (radius X) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left hEle hd
      _ = C := by
        field_simp [ne_of_gt (one_sub_radius_sq_pos hX)]
  have hr2 : (radius X) ^ 2 ≤ 1 := by
    have hr0 := radius_nonneg (le_of_lt hX)
    have hr1 := radius_lt_one (lt_trans zero_lt_one hX)
    nlinarith
  have hmain : c * (radius X) ^ 2 * (1 - (radius X) ^ 2)⁻¹ ≤ c * X := by
    have hcr : c * (radius X) ^ 2 ≤ c := by nlinarith
    have hinv0 : 0 ≤ (1 - (radius X) ^ 2)⁻¹ := inv_nonneg.mpr hd
    have hfirst := mul_le_mul_of_nonneg_right hcr hinv0
    have hsecond := mul_le_mul_of_nonneg_left hEinv hc
    nlinarith
  rw [hgf]
  nlinarith

/-- A lower cubic bound. Constants are deliberately coarse to make later arithmetic robust. -/
lemma cube_lower_of_gf
    {X c C F E : ℝ} (hX : 2 ≤ X) (hc : 0 < c) (hC : 0 ≤ C)
    (hlarge : 16 * C ≤ c * X)
    (hE : |E| ≤ C * (1 - (radius X) ^ 2)⁻¹)
    (hgf : F ^ 3 = c * (radius X) ^ 2 * (1 - (radius X) ^ 2)⁻¹
      + (1 - (radius X) ^ 2) * E) :
    c * X / 16 ≤ F ^ 3 := by
  have hX1 : 1 < X := lt_of_lt_of_le (by norm_num) hX
  have hd : 0 ≤ 1 - (radius X) ^ 2 := le_of_lt (one_sub_radius_sq_pos hX1)
  have herr : -C ≤ (1 - (radius X) ^ 2) * E := by
    have hneg : -(C * (1 - (radius X) ^ 2)⁻¹) ≤ E := by
      have := neg_abs_le E
      linarith
    calc
      -C = (1 - (radius X) ^ 2) * (-(C * (1 - (radius X) ^ 2)⁻¹)) := by
        field_simp [ne_of_gt (one_sub_radius_sq_pos hX1)]
      _ ≤ (1 - (radius X) ^ 2) * E := mul_le_mul_of_nonneg_left hneg hd
  have hr2 := radius_sq_ge_quarter hX
  have hinv := half_X_le_inv_one_sub_radius_sq hX1
  have hmain : c * X / 8 ≤
      c * (radius X) ^ 2 * (1 - (radius X) ^ 2)⁻¹ := by
    calc
      c * X / 8 = c * (1 / 4) * (X / 2) := by ring
      _ ≤ c * (radius X) ^ 2 * (1 - (radius X) ^ 2)⁻¹ := by gcongr
  rw [hgf]
  nlinarith

/-- The differentiated identity makes the derivative large before dividing by `3 F²`. -/
lemma differentiated_numerator_lower
    {X c C F F' E E' : ℝ} (hX : 1 < X) (hc : 0 < c) (hC : 0 ≤ C)
    (hlarge : 16 * C ≤ c * X)
    (hE : |E| ≤ C * (1 - (radius X) ^ 2)⁻¹)
    (hE' : |E'| ≤ C * (1 - (radius X) ^ 2)⁻¹ ^ 2)
    (hdiff : 3 * F ^ 2 * F' = c * (1 - (radius X) ^ 2)⁻¹ ^ 2
      - E + (1 - (radius X) ^ 2) * E') :
    c * X ^ 2 / 8 ≤ 3 * F ^ 2 * F' := by
  have hd : 0 ≤ 1 - (radius X) ^ 2 := le_of_lt (one_sub_radius_sq_pos hX)
  have hinv0 : 0 ≤ (1 - (radius X) ^ 2)⁻¹ := inv_nonneg.mpr hd
  have hinv := half_X_le_inv_one_sub_radius_sq hX
  have hmain : c * X ^ 2 / 4 ≤ c * (1 - (radius X) ^ 2)⁻¹ ^ 2 := by
    have hX0 : 0 ≤ X := le_of_lt (lt_trans zero_lt_one hX)
    nlinarith [sq_nonneg ((1 - (radius X) ^ 2)⁻¹ - X / 2)]
  have hElower : -(C * (1 - (radius X) ^ 2)⁻¹) ≤ -E := by
    have := le_trans (le_abs_self E) hE
    linarith
  have hE'lower : -(C * (1 - (radius X) ^ 2)⁻¹) ≤
      (1 - (radius X) ^ 2) * E' := by
    have hlow : -(C * (1 - (radius X) ^ 2)⁻¹ ^ 2) ≤ E' := by
      have := neg_abs_le E'
      linarith
    calc
      -(C * (1 - (radius X) ^ 2)⁻¹)
          = (1 - (radius X) ^ 2) * (-(C * (1 - (radius X) ^ 2)⁻¹ ^ 2)) := by
              field_simp
      _ ≤ (1 - (radius X) ^ 2) * E' := mul_le_mul_of_nonneg_left hlow hd
  have hInvX := inv_one_sub_radius_sq_le_X hX
  have herror : 2 * C * (1 - (radius X) ^ 2)⁻¹ ≤ c * X ^ 2 / 8 := by
    have hXpos : 0 < X := lt_trans zero_lt_one hX
    calc
      2 * C * (1 - (radius X) ^ 2)⁻¹ ≤ 2 * C * X := by gcongr
      _ ≤ c * X ^ 2 / 8 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).2
        nlinarith
  rw [hdiff]
  nlinarith

/-- Perfect ninth powers remove every real cube-root from the formal proof. -/
lemma ninth_power_cube_upper
    {t K F : ℝ} (ht : 0 ≤ t) (hK : 0 ≤ K) (hF : 0 ≤ F)
    (h : F ^ 3 ≤ K ^ 3 * t ^ 9) : F ≤ K * t ^ 3 := by
  have hkt : 0 ≤ K * t ^ 3 := mul_nonneg hK (pow_nonneg ht 3)
  have hc : (K * t ^ 3) ^ 3 = K ^ 3 * t ^ 9 := by ring
  rw [← hc] at h
  exact (pow_le_pow_iff_left₀ hF hkt (by norm_num)).mp h

/-- Division of the differentiated lower bound by an explicit upper bound for `F²`. -/
lemma derivative_lower_of_square_upper
    {t c K F F' : ℝ} (ht : 0 < t) (hc : 0 < c) (hK : 0 < K)
    (hF : 0 ≤ F) (hFupper : F ≤ K * t ^ 3)
    (hdiff : c * t ^ 18 / 8 ≤ 3 * F ^ 2 * F') :
    c * t ^ 12 / (24 * K ^ 2) ≤ F' := by
  have hF2 : F ^ 2 ≤ K ^ 2 * t ^ 6 := by nlinarith
  have hden : 0 < 24 * K ^ 2 := by positivity
  have hF'nonneg : 0 ≤ F' := by
    by_contra hneg
    have : F' < 0 := lt_of_not_ge hneg
    have hleft : 0 < c * t ^ 18 / 8 := by positivity
    have hright : 3 * F ^ 2 * F' ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) (sq_nonneg F)) (le_of_lt this)
    linarith
  calc
    c * t ^ 12 / (24 * K ^ 2)
        = (c * t ^ 18 / 8) / (3 * K ^ 2 * t ^ 6) := by field_simp; ring
    _ ≤ (3 * F ^ 2 * F') / (3 * K ^ 2 * t ^ 6) := by
      gcongr
    _ ≤ F' := by
      rw [div_le_iff₀ (by positivity : 0 < 3 * K ^ 2 * t ^ 6)]
      nlinarith

/-- The final exponent gap: `t^16` eventually beats any constant times `t^15`. -/
lemma power_sixteen_not_le_power_fifteen
    {a b t : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (ht : b / a < t)
    (ht0 : 0 ≤ t) : ¬ a * t ^ 16 ≤ b * t ^ 15 := by
  intro h
  by_cases hz : t = 0
  · subst t
    have hba : 0 ≤ b / a := div_nonneg hb (le_of_lt ha)
    linarith
  have htp : 0 < t := lt_of_le_of_ne ht0 (Ne.symm hz)
  have hpow : 0 < t ^ 15 := pow_pos htp 15
  have hab : b < a * t := by
    rw [div_lt_iff₀ ha] at ht
    nlinarith
  have : b * t ^ 15 < a * t ^ 16 := by
    calc
      b * t ^ 15 < (a * t) * t ^ 15 := mul_lt_mul_of_pos_right hab hpow
      _ = a * t ^ 16 := by ring
  linarith

/-- A version allowing the three upper-bound terms occurring in the proof. -/
lemma three_term_upper_contradiction
    {a b₁ b₂ b₃ t : ℝ} (ha : 0 < a)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃)
    (ht1 : 1 ≤ t) (htlarge : (b₁ + b₂ + b₃) / a < t)
    (hlower : a * t ^ 16 ≤ b₁ * t ^ 15 + b₂ * t ^ 11 + b₃ * t ^ 15) : False := by
  have ht0 : 0 ≤ t := le_trans zero_le_one ht1
  have h11 : t ^ 11 ≤ t ^ 15 := by
    exact pow_le_pow_right₀ ht1 (by norm_num)
  have hu : b₁ * t ^ 15 + b₂ * t ^ 11 + b₃ * t ^ 15 ≤
      (b₁ + b₂ + b₃) * t ^ 15 := by
    nlinarith [mul_le_mul_of_nonneg_left h11 hb₂]
  exact power_sixteen_not_le_power_fifteen ha (by positivity) htlarge ht0 (hlower.trans hu)

/-! ### Bridges between the natural counting model and complex generating functions -/

lemma indicatorC_eq_natCast (A : Set ℕ) (n : ℕ) :
    indicatorC A n = (indicator A n : ℂ) := by
  classical
  by_cases hn : n ∈ A <;> simp [indicatorC, indicator, hn]

lemma indicatorC_eq_natCast_fun (A : Set ℕ) :
    indicatorC A = fun n ↦ (indicator A n : ℂ) := by
  funext n
  exact indicatorC_eq_natCast A n

lemma convC_natCast (f g : ℕ → ℕ) (n : ℕ) :
    convC (fun k ↦ (f k : ℂ)) (fun k ↦ (g k : ℂ)) n =
      (addConv f g n : ℂ) := by
  simp only [convC, addConv, Nat.cast_sum, Nat.cast_mul]

lemma tripleCoeff_eq_natCast_tripleConv (A : Set ℕ) (n : ℕ) :
    tripleCoeff A n = (tripleConv A n : ℂ) := by
  rw [tripleCoeff, tripleConv, indicatorC_eq_natCast_fun]
  have hinner :
      convC (fun k ↦ (indicator A k : ℂ)) (fun k ↦ (indicator A k : ℂ)) =
        fun k ↦ (addConv (indicator A) (indicator A) k : ℂ) := by
    funext k
    exact convC_natCast (indicator A) (indicator A) k
  rw [hinner]
  exact convC_natCast (addConv (indicator A) (indicator A)) (indicator A) n

lemma summatoryC_tripleCoeff_eq_natCast_summatory (A : Set ℕ) (N : ℕ) :
    summatoryC (tripleCoeff A) N = (summatory A N : ℂ) := by
  simp only [summatoryC, summatory, tripleCoeff_eq_natCast_tripleConv, Nat.cast_sum]

noncomputable def remainderC (A : Set ℕ) (c : ℝ) (N : ℕ) : ℂ :=
  remainder A c N

lemma norm_remainderC (A : Set ℕ) (c : ℝ) (N : ℕ) :
    ‖remainderC A c N‖ = |remainder A c N| := by
  simp [remainderC]

lemma summatoryC_eq_remainderC_add_main (A : Set ℕ) (c : ℝ) (N : ℕ) :
    summatoryC (tripleCoeff A) N =
      remainderC A c N + (c : ℂ) * (N : ℂ) := by
  rw [summatoryC_tripleCoeff_eq_natCast_summatory]
  simp only [remainderC, remainder, Nat.cast_ofNat, Nat.cast_sum]
  push_cast
  ring

lemma F_cube_eq_main_add_error_of_uniform_remainder_bound
    (A : Set ℕ) (c C : ℝ) (hC : ∀ N, |remainder A c N| ≤ C)
    {z : ℂ} (hz : ‖z‖ < 1) :
    F A z ^ 3 =
      (c : ℂ) * z / (1 - z) + (1 - z) * E (remainderC A c) z := by
  apply F_cube_eq_main_add_error A (remainderC A c) (c : ℂ)
    (C := C) ?_ (summatoryC_eq_remainderC_add_main A c) hz
  intro n
  rw [norm_remainderC]
  exact hC n

lemma differentiated_identity_of_uniform_remainder_bound
    (A : Set ℕ) (c C : ℝ) (hC : ∀ N, |remainder A c N| ≤ C)
    {z : ℂ} (hz : ‖z‖ < 1) :
    3 * F A z ^ 2 * Fderiv A z =
      (c : ℂ) / (1 - z) ^ 2 - E (remainderC A c) z +
        (1 - z) * Ederiv (remainderC A c) z := by
  apply differentiated_bounded_error_identity A (remainderC A c) (c : ℂ)
    (C := C) ?_ (summatoryC_eq_remainderC_add_main A c) hz
  intro n
  rw [norm_remainderC]
  exact hC n

lemma F_cube_eq_main_add_error_of_isBigO
    (A : Set ℕ) (c : ℝ)
    (hO : remainder A c =O[Filter.atTop] (fun _ : ℕ ↦ (1 : ℝ)))
    {z : ℂ} (hz : ‖z‖ < 1) :
    ∃ C : ℝ, F A z ^ 3 =
      (c : ℂ) * z / (1 - z) + (1 - z) * E (remainderC A c) z := by
  obtain ⟨C, hC⟩ := uniform_remainder_bound_of_isBigO_one A c hO
  exact ⟨C, F_cube_eq_main_add_error_of_uniform_remainder_bound A c C hC hz⟩

lemma differentiated_identity_of_isBigO
    (A : Set ℕ) (c : ℝ)
    (hO : remainder A c =O[Filter.atTop] (fun _ : ℕ ↦ (1 : ℝ)))
    {z : ℂ} (hz : ‖z‖ < 1) :
    ∃ C : ℝ, 3 * F A z ^ 2 * Fderiv A z =
      (c : ℂ) / (1 - z) ^ 2 - E (remainderC A c) z +
        (1 - z) * Ederiv (remainderC A c) z := by
  obtain ⟨C, hC⟩ := uniform_remainder_bound_of_isBigO_one A c hO
  exact ⟨C, differentiated_identity_of_uniform_remainder_bound A c C hC hz⟩

lemma summatory_lower_of_remainder_bound (A : Set ℕ) (c C : ℝ)
    (hrem : ∀ N : ℕ, |remainder A c N| ≤ C) (N : ℕ) :
    c * N - C ≤ (summatory A N : ℝ) := by
  have h := (abs_le.mp (hrem N)).1
  simp only [remainder] at h
  linarith

lemma exists_scale (c : ℝ) (hc : 0 < c) :
    ∃ K : ℕ, 0 < K ∧ 1 < c * K := by
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / c)
  have hdiv : 0 < 1 / c := one_div_pos.mpr hc
  have hKr : 0 < (K : ℝ) := lt_trans hdiv hK
  have hmul : 1 < (K : ℝ) * c := (div_lt_iff₀ hc).mp hK
  exact ⟨K, by exact_mod_cast hKr, by simpa [mul_comm] using hmul⟩

lemma countingFunction_ge_of_cube_lt_main (A : Set ℕ) (c C : ℝ)
    (hrem : ∀ N : ℕ, |remainder A c N| ≤ C) (t N : ℕ)
    (hmain : (t : ℝ) ^ 3 < c * N - C) :
    t ≤ countingFunction A N := by
  by_contra h
  have hcount : countingFunction A N < t := Nat.lt_of_not_ge h
  have hcubes : countingFunction A N ^ 3 < t ^ 3 :=
    Nat.pow_lt_pow_left hcount (by norm_num)
  have hsNat := summatory_le_countingFunction_cube A N
  have hsReal : (summatory A N : ℝ) ≤ (countingFunction A N : ℝ) ^ 3 := by
    exact_mod_cast hsNat
  have hcubeReal : (countingFunction A N : ℝ) ^ 3 < (t : ℝ) ^ 3 := by
    exact_mod_cast hcubes
  have hlower := summatory_lower_of_remainder_bound A c C hrem N
  linarith

lemma scaled_cube_div_four (K t : ℕ) :
    (4 * K * t) ^ 3 / 4 = 16 * K ^ 3 * t ^ 3 := by
  have hpoly : (4 * K * t) ^ 3 = 4 * (16 * K ^ 3 * t ^ 3) := by ring
  rw [hpoly]
  simpa [mul_comm] using Nat.mul_div_left (16 * K ^ 3 * t ^ 3) 4

lemma exists_eventual_countingFunction_scaled_lower (A : Set ℕ) (c C : ℝ)
    (hc : 0 < c) (hrem : ∀ N : ℕ, |remainder A c N| ≤ C) :
    ∃ K : ℕ, 0 < K ∧
      ∀ᶠ t : ℕ in atTop,
        t ≤ countingFunction A ((4 * K * t) ^ 3 / 4) := by
  obtain ⟨K, hKpos, hK⟩ := exists_scale c hc
  refine ⟨K, hKpos, ?_⟩
  obtain ⟨T, hT⟩ := exists_nat_gt C
  filter_upwards [eventually_ge_atTop (max 1 T)] with t ht
  have ht1 : 1 ≤ t := le_trans (le_max_left 1 T) ht
  have hTt : T ≤ t := le_trans (le_max_right 1 T) ht
  have hCt : C < (t : ℝ) := lt_of_lt_of_le hT (by exact_mod_cast hTt)
  have htCubeNat : t ≤ t ^ 3 := Nat.le_pow (by norm_num)
  have htCube : (t : ℝ) ≤ (t : ℝ) ^ 3 := by exact_mod_cast htCubeNat
  have hCcube : C < (t : ℝ) ^ 3 := lt_of_lt_of_le hCt htCube
  have hKpowNat : K ≤ K ^ 3 := Nat.le_pow (by norm_num)
  have hKpow : (K : ℝ) ≤ (K ^ 3 : ℕ) := by exact_mod_cast hKpowNat
  have hcoeff : 16 < c * (16 * K ^ 3 : ℕ) := by
    calc
      (16 : ℝ) = 16 * 1 := by ring
      _ < 16 * (c * K) := mul_lt_mul_of_pos_left hK (by norm_num)
      _ ≤ 16 * (c * (K ^ 3 : ℕ)) := by
        gcongr
      _ = c * (16 * K ^ 3 : ℕ) := by push_cast; ring
  rw [scaled_cube_div_four]
  apply countingFunction_ge_of_cube_lt_main A c C hrem
  have htCubePos : 0 < (t : ℝ) ^ 3 := by positivity
  have hprod := mul_lt_mul_of_pos_right hcoeff htCubePos
  push_cast at hprod ⊢
  nlinarith

noncomputable def positiveCountingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  #((Finset.Icc 1 N).filter (fun n ↦ n ∈ A))

lemma positiveCountingFunction_eq_card_erase (A : Set ℕ) (N : ℕ) :
    positiveCountingFunction A N = #((membersUpTo A N).erase 0) := by
  unfold positiveCountingFunction
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_erase, membersUpTo,
    Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, hN⟩, hA⟩
    exact ⟨by omega, by omega, hA⟩
  · rintro ⟨hn0, hnN, hA⟩
    exact ⟨⟨by omega, by omega⟩, hA⟩

lemma pred_countingFunction_le_positiveCountingFunction (A : Set ℕ) (N : ℕ) :
    countingFunction A N - 1 ≤ positiveCountingFunction A N := by
  rw [positiveCountingFunction_eq_card_erase]
  exact pred_card_le_card_erase

lemma exists_eventual_positiveCountingFunction_scaled_lower (A : Set ℕ) (c C : ℝ)
    (hc : 0 < c) (hrem : ∀ N : ℕ, |remainder A c N| ≤ C) :
    ∃ K : ℕ, 0 < K ∧
      ∀ᶠ t : ℕ in atTop,
        t - 1 ≤ positiveCountingFunction A ((4 * K * t) ^ 3 / 4) := by
  obtain ⟨K, hK, hcount⟩ :=
    exists_eventual_countingFunction_scaled_lower A c C hc hrem
  refine ⟨K, hK, ?_⟩
  filter_upwards [hcount] with t ht
  exact le_trans (Nat.sub_le_sub_right ht 1)
    (pred_countingFunction_le_positiveCountingFunction A _)

/-! ### Finite Fourier lower-bound support

The following lemmas isolate the exact zero-frequency selection used by the
Erdős--Fuchs argument.  They use finite real polynomials, so every circle
integral below is an integral of a continuous function and every coefficient
rearrangement is finite. -/

open Complex MeasureTheory Set Polynomial
open scoped Real Polynomial ComplexConjugate

private lemma circleIntegrable_normSq_eval (p : ℂ[X]) :
    CircleIntegrable (fun z : ℂ ↦ ‖p.eval z‖ ^ 2) 0 1 := by
  apply ContinuousOn.circleIntegrable'
  fun_prop

private lemma circleIntegrable_cross (p q : ℂ[X]) :
    CircleIntegrable (fun z : ℂ ↦ (p.eval z * conj (q.eval z)).re) 0 1 := by
  apply ContinuousOn.circleIntegrable'
  fun_prop

private lemma sum_support_union_eq_sum_support (p : ℂ[X]) (s : Finset ℕ)
    (hps : p.support ⊆ s) :
    ∑ i ∈ s, ‖p.coeff i‖ ^ 2 = ∑ i ∈ p.support, ‖p.coeff i‖ ^ 2 := by
  rw [Finset.sum_subset hps]
  intro i hi his
  rw [Polynomial.notMem_support_iff.mp his]
  simp

lemma circleAverage_re_eval_mul_conj_eval (p q : ℂ[X]) :
    Real.circleAverage (fun z : ℂ ↦ (p.eval z * conj (q.eval z)).re) 0 1 =
      ∑ i ∈ p.support ∪ q.support, (p.coeff i * conj (q.coeff i)).re := by
  let s := p.support ∪ q.support
  have hp : p.support ⊆ s := Finset.subset_union_left
  have hq : q.support ⊆ s := Finset.subset_union_right
  have hpq : (p + q).support ⊆ s := Polynomial.support_add
  have P := (p + q).sum_sq_norm_coeff_eq_circleAverage
  have Pp := p.sum_sq_norm_coeff_eq_circleAverage
  have Pq := q.sum_sq_norm_coeff_eq_circleAverage
  rw [← sum_support_union_eq_sum_support (p + q) s hpq] at P
  rw [← sum_support_union_eq_sum_support p s hp] at Pp
  rw [← sum_support_union_eq_sum_support q s hq] at Pq
  have hpoint (z : ℂ) :
      ‖(p + q).eval z‖ ^ 2 =
        ‖p.eval z‖ ^ 2 + ‖q.eval z‖ ^ 2 +
          2 * (p.eval z * conj (q.eval z)).re := by
    simp only [Polynomial.eval_add]
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, add_re, add_im, mul_re, conj_re, conj_im]
    ring
  have hcoeff (i : ℕ) :
      ‖(p + q).coeff i‖ ^ 2 =
        ‖p.coeff i‖ ^ 2 + ‖q.coeff i‖ ^ 2 +
          2 * (p.coeff i * conj (q.coeff i)).re := by
    rw [Polynomial.coeff_add]
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, add_re, add_im, mul_re, conj_re, conj_im]
    ring
  rw [Finset.sum_congr rfl (fun i hi ↦ hcoeff i), Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum] at P
  simp_rw [hpoint] at P
  have hCA :
      Real.circleAverage (fun z : ℂ ↦
          ‖p.eval z‖ ^ 2 + ‖q.eval z‖ ^ 2 + 2 * (p.eval z * conj (q.eval z)).re) 0 1 =
        Real.circleAverage (fun z : ℂ ↦ ‖p.eval z‖ ^ 2) 0 1 +
        Real.circleAverage (fun z : ℂ ↦ ‖q.eval z‖ ^ 2) 0 1 +
        2 * Real.circleAverage (fun z : ℂ ↦ (p.eval z * conj (q.eval z)).re) 0 1 := by
    change Real.circleAverage
        (((fun z : ℂ ↦ ‖p.eval z‖ ^ 2) + (fun z : ℂ ↦ ‖q.eval z‖ ^ 2)) +
          (2 : ℝ) • (fun z : ℂ ↦ (p.eval z * conj (q.eval z)).re)) 0 1 = _
    rw [Real.circleAverage_add
      ((circleIntegrable_normSq_eval p).add (circleIntegrable_normSq_eval q))
      (circleIntegrable_cross p q).const_smul,
      Real.circleAverage_add (circleIntegrable_normSq_eval p)
        (circleIntegrable_normSq_eval q),
      Real.circleAverage_smul]
    rfl
  rw [hCA] at P
  rw [Pp, Pq] at P
  linarith

lemma sum_re_coeff_mul_conj_coeff_le_circleAverage
    (p q : ℂ[X]) (s : Finset ℕ)
    (h0 : ∀ i : ℕ, 0 ≤ (p.coeff i * conj (q.coeff i)).re) :
    ∑ i ∈ s, (p.coeff i * conj (q.coeff i)).re ≤
      Real.circleAverage (fun z : ℂ ↦ (p.eval z * conj (q.eval z)).re) 0 1 := by
  let u := p.support ∪ q.support
  let f : ℕ → ℝ := fun i ↦ (p.coeff i * conj (q.coeff i)).re
  have hsu : s ⊆ s ∪ u := Finset.subset_union_left
  have hle : ∑ i ∈ s, f i ≤ ∑ i ∈ s ∪ u, f i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsu (fun i hi his ↦ h0 i)
  have heu : ∑ i ∈ s ∪ u, f i = ∑ i ∈ u, f i := by
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro i hi hiu
    simp only [u, Finset.mem_union, not_or] at hiu
    simp [f, Polynomial.notMem_support_iff.mp hiu.1]
  rw [heu] at hle
  rw [circleAverage_re_eval_mul_conj_eval p q]
  exact hle

lemma sum_re_coeff_mul_re_coeff_le_circleAverage_of_nonneg
    (p q : ℂ[X]) (s : Finset ℕ)
    (hpim : ∀ i : ℕ, (p.coeff i).im = 0)
    (hqim : ∀ i : ℕ, (q.coeff i).im = 0)
    (hp0 : ∀ i : ℕ, 0 ≤ (p.coeff i).re)
    (hq0 : ∀ i : ℕ, 0 ≤ (q.coeff i).re) :
    ∑ i ∈ s, (p.coeff i).re * (q.coeff i).re ≤
      Real.circleAverage (fun z : ℂ ↦ (p.eval z * conj (q.eval z)).re) 0 1 := by
  have hterm (i : ℕ) :
      (p.coeff i * conj (q.coeff i)).re =
        (p.coeff i).re * (q.coeff i).re := by
    simp [Complex.mul_re, hpim i, hqim i]
  simpa only [hterm] using
    sum_re_coeff_mul_conj_coeff_le_circleAverage p q s
      (fun i ↦ by rw [hterm i]; exact mul_nonneg (hp0 i) (hq0 i))

lemma sum_coeff_mul_coeff_le_circleAverage_of_nonneg
    (p q : ℝ[X]) (s : Finset ℕ)
    (hp0 : ∀ i : ℕ, 0 ≤ p.coeff i)
    (hq0 : ∀ i : ℕ, 0 ≤ q.coeff i) :
    ∑ i ∈ s, p.coeff i * q.coeff i ≤
      Real.circleAverage (fun z : ℂ ↦
        ((p.map Complex.ofRealHom).eval z *
          conj ((q.map Complex.ofRealHom).eval z)).re) 0 1 := by
  simpa using sum_re_coeff_mul_re_coeff_le_circleAverage_of_nonneg
    (p.map Complex.ofRealHom) (q.map Complex.ofRealHom) s
    (fun i ↦ by simp) (fun i ↦ by simp)
    (fun i ↦ by simpa using hp0 i) (fun i ↦ by simpa using hq0 i)

section MonomialSums

variable {I J : Type*} [DecidableEq I] [DecidableEq J]

noncomputable def monomialSum (s : Finset I) (e : I → ℕ) (w : I → ℝ) : ℝ[X] :=
  ∑ i ∈ s, monomial (e i) (w i)

@[simp]
lemma coeff_monomialSum (s : Finset I) (e : I → ℕ) (w : I → ℝ) (n : ℕ) :
    (monomialSum s e w).coeff n = ∑ i ∈ s with e i = n, w i := by
  classical
  rw [Finset.sum_filter]
  induction s using Finset.induction_on with
  | empty => simp [monomialSum]
  | @insert a s ha ih =>
      simp [monomialSum, ha, Polynomial.coeff_add, Polynomial.coeff_monomial]

lemma diagonal_coeff_sum_monomialSum
    (s : Finset I) (t : Finset J)
    (e : I → ℕ) (d : J → ℕ) (w : I → ℝ) (v : J → ℝ) :
    ∑ n ∈ s.image e ∪ t.image d,
        (monomialSum s e w).coeff n * (monomialSum t d v).coeff n =
      ∑ i ∈ s, ∑ j ∈ t with e i = d j, w i * v j := by
  classical
  let u := s.image e ∪ t.image d
  let fi : ℕ → I → ℝ := fun n i ↦ if e i = n then w i else 0
  let gj : ℕ → J → ℝ := fun n j ↦ if d j = n then v j else 0
  have he (n : ℕ) : (monomialSum s e w).coeff n = ∑ i ∈ s, fi n i := by
    rw [coeff_monomialSum, Finset.sum_filter]
  have hd (n : ℕ) : (monomialSum t d v).coeff n = ∑ j ∈ t, gj n j := by
    rw [coeff_monomialSum, Finset.sum_filter]
  have hpair (i : I) (hi : i ∈ s) (j : J) (hj : j ∈ t) :
      ∑ n ∈ u, fi n i * gj n j = if e i = d j then w i * v j else 0 := by
    by_cases hij : e i = d j
    · rw [if_pos hij]
      have hei : e i ∈ u :=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      rw [Finset.sum_eq_single (e i)]
      · simp [fi, gj, hij]
      · intro n hn hne
        simp [fi, hne.symm]
      · exact fun h ↦ (h hei).elim
    · rw [if_neg hij]
      apply Finset.sum_eq_zero
      intro n hn
      by_cases hin : e i = n
      · have hjn : d j ≠ n := fun h ↦ hij (hin.trans h.symm)
        simp [fi, gj, hin, hjn]
      · simp [fi, hin]
  change ∑ n ∈ u, _ = _
  simp_rw [he, hd, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hpair i hi j hj]

lemma sum_selectedPairs_le_circleAverage_monomialSum
    (s : Finset I) (t : Finset J) (sel : Finset (I × J))
    (e : I → ℕ) (d : J → ℕ) (w : I → ℝ) (v : J → ℝ)
    (hsel : sel ⊆ s.product t)
    (hmatch : ∀ x ∈ sel, e x.1 = d x.2)
    (hw0 : ∀ i ∈ s, 0 ≤ w i)
    (hv0 : ∀ j ∈ t, 0 ≤ v j) :
    ∑ x ∈ sel, w x.1 * v x.2 ≤
      Real.circleAverage (fun z : ℂ ↦
        (((monomialSum s e w).map Complex.ofRealHom).eval z *
          conj (((monomialSum t d v).map Complex.ofRealHom).eval z)).re) 0 1 := by
  classical
  let P := monomialSum s e w
  let Q := monomialSum t d v
  have hP0 (n : ℕ) : 0 ≤ P.coeff n := by
    rw [show P = monomialSum s e w from rfl, coeff_monomialSum]
    exact Finset.sum_nonneg fun i hi ↦ hw0 i (Finset.mem_filter.mp hi).1
  have hQ0 (n : ℕ) : 0 ≤ Q.coeff n := by
    rw [show Q = monomialSum t d v from rfl, coeff_monomialSum]
    exact Finset.sum_nonneg fun j hj ↦ hv0 j (Finset.mem_filter.mp hj).1
  have hdiag := sum_coeff_mul_coeff_le_circleAverage_of_nonneg P Q
    (s.image e ∪ t.image d) hP0 hQ0
  have hdiagEq :
      ∑ n ∈ s.image e ∪ t.image d, P.coeff n * Q.coeff n =
        ∑ i ∈ s, ∑ j ∈ t with e i = d j, w i * v j := by
    exact diagonal_coeff_sum_monomialSum s t e d w v
  have hallEq :
      ∑ x ∈ (s.product t).filter (fun x ↦ e x.1 = d x.2), w x.1 * v x.2 =
        ∑ i ∈ s, ∑ j ∈ t with e i = d j, w i * v j := by
    rw [Finset.sum_filter]
    change (s.product t).sum (fun x ↦ if e x.1 = d x.2 then w x.1 * v x.2 else 0) = _
    calc
      _ = ∑ i ∈ s, ∑ j ∈ t,
          if e i = d j then w i * v j else 0 :=
        Finset.sum_product s t (fun x ↦
          if e x.1 = d x.2 then w x.1 * v x.2 else 0)
      _ = _ := by simp_rw [Finset.sum_filter]
  have hsub : sel ⊆ (s.product t).filter (fun x ↦ e x.1 = d x.2) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hsel hx, hmatch x hx⟩
  have hselected :
      ∑ x ∈ sel, w x.1 * v x.2 ≤
        ∑ x ∈ (s.product t).filter (fun x ↦ e x.1 = d x.2), w x.1 * v x.2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro x hx hnx
    exact mul_nonneg (hw0 x.1 (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1)
      (hv0 x.2 (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).2)
  rw [hallEq, ← hdiagEq] at hselected
  exact hselected.trans hdiag

lemma sum_selectedGraph_le_circleAverage_monomialSum
    (s : Finset I) (t : Finset J) (sel : Finset I) (pairWith : I → J)
    (e : I → ℕ) (d : J → ℕ) (w : I → ℝ) (v : J → ℝ)
    (hsel : sel ⊆ s)
    (hpairWith : ∀ i ∈ sel, pairWith i ∈ t)
    (hmatch : ∀ i ∈ sel, e i = d (pairWith i))
    (hw0 : ∀ i ∈ s, 0 ≤ w i)
    (hv0 : ∀ j ∈ t, 0 ≤ v j) :
    ∑ i ∈ sel, w i * v (pairWith i) ≤
      Real.circleAverage (fun z : ℂ ↦
        (((monomialSum s e w).map Complex.ofRealHom).eval z *
          conj (((monomialSum t d v).map Complex.ofRealHom).eval z)).re) 0 1 := by
  classical
  let graphMap : I → I × J := fun i ↦ (i, pairWith i)
  let pairs := sel.image graphMap
  have hpairSub : pairs ⊆ s.product t := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_product.mpr ⟨hsel hi, hpairWith i hi⟩
  have hpairMatch : ∀ x ∈ pairs, e x.1 = d x.2 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hmatch i hi
  have h := sum_selectedPairs_le_circleAverage_monomialSum
    s t pairs e d w v hpairSub hpairMatch hw0 hv0
  have hinj : Set.InjOn graphMap ↑sel := by
    intro i hi j hj hij
    exact congrArg Prod.fst hij
  rw [Finset.sum_image hinj] at h
  exact h

lemma erdosFuchs_selected_b_eq_d
    (aFull dFull jFull bFull ellFull : Finset ℕ)
    (aSel dSel jSel : Finset ℕ)
    (wa wd wj wb wl : ℕ → ℝ)
    (haSub : aSel ⊆ aFull) (hdSub : dSel ⊆ dFull) (hjSub : jSel ⊆ jFull)
    (hdB : dSel ⊆ bFull)
    (hell : ∀ a ∈ aSel, ∀ j ∈ jSel, a - 1 + j ∈ ellFull)
    (haPos : ∀ a ∈ aSel, 1 ≤ a)
    (hdPos : ∀ d ∈ dSel, 1 ≤ d)
    (hwa : ∀ a ∈ aFull, 0 ≤ wa a)
    (hwd : ∀ d ∈ dFull, 0 ≤ wd d)
    (hwj : ∀ j ∈ jFull, 0 ≤ wj j)
    (hwb : ∀ b ∈ bFull, 0 ≤ wb b)
    (hwl : ∀ l ∈ ellFull, 0 ≤ wl l) :
    ∑ x ∈ (aSel.product dSel).product jSel,
        (3 * wa x.1.1 * wd x.1.2 * wj x.2) *
          (wb x.1.2 * wl (x.1.1 - 1 + x.2)) ≤
      Real.circleAverage (fun z : ℂ ↦
        (((monomialSum ((aFull.product dFull).product jFull)
              (fun x ↦ x.1.1 + (x.1.2 - 1) + x.2)
              (fun x ↦ 3 * wa x.1.1 * wd x.1.2 * wj x.2)).map
            Complex.ofRealHom).eval z *
          conj (((monomialSum (bFull.product ellFull)
              (fun x ↦ x.1 + x.2)
              (fun x ↦ wb x.1 * wl x.2)).map Complex.ofRealHom).eval z)).re) 0 1 := by
  classical
  let s := (aFull.product dFull).product jFull
  let t := bFull.product ellFull
  let sel := (aSel.product dSel).product jSel
  let pairWith : ((ℕ × ℕ) × ℕ) → ℕ × ℕ :=
    fun x ↦ (x.1.2, x.1.1 - 1 + x.2)
  let ep : ((ℕ × ℕ) × ℕ) → ℕ :=
    fun x ↦ x.1.1 + (x.1.2 - 1) + x.2
  let eq : (ℕ × ℕ) → ℕ := fun x ↦ x.1 + x.2
  let wp : ((ℕ × ℕ) × ℕ) → ℝ :=
    fun x ↦ 3 * wa x.1.1 * wd x.1.2 * wj x.2
  let wq : (ℕ × ℕ) → ℝ := fun x ↦ wb x.1 * wl x.2
  have hsel : sel ⊆ s := by
    intro x hx
    rcases Finset.mem_product.mp hx with ⟨had, hj⟩
    rcases Finset.mem_product.mp had with ⟨ha, hd⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨haSub ha, hdSub hd⟩, hjSub hj⟩
  have hpairWith : ∀ x ∈ sel, pairWith x ∈ t := by
    intro x hx
    rcases Finset.mem_product.mp hx with ⟨had, hj⟩
    rcases Finset.mem_product.mp had with ⟨ha, hd⟩
    exact Finset.mem_product.mpr ⟨hdB hd, hell x.1.1 ha x.2 hj⟩
  have hmatch : ∀ x ∈ sel, ep x = eq (pairWith x) := by
    intro x hx
    rcases Finset.mem_product.mp hx with ⟨had, hj⟩
    rcases Finset.mem_product.mp had with ⟨ha, hd⟩
    dsimp [ep, eq, pairWith]
    have ha' := haPos x.1.1 ha
    have hd' := hdPos x.1.2 hd
    omega
  have hwp : ∀ x ∈ s, 0 ≤ wp x := by
    intro x hx
    rcases Finset.mem_product.mp hx with ⟨had, hj⟩
    rcases Finset.mem_product.mp had with ⟨ha, hd⟩
    dsimp [wp]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hwa x.1.1 ha))
      (hwd x.1.2 hd)) (hwj x.2 hj)
  have hwq : ∀ x ∈ t, 0 ≤ wq x := by
    intro x hx
    rcases Finset.mem_product.mp hx with ⟨hb, hl⟩
    exact mul_nonneg (hwb x.1 hb) (hwl x.2 hl)
  simpa [s, t, sel, pairWith, ep, eq, wp, wq] using
    sum_selectedGraph_le_circleAverage_monomialSum
      s t sel pairWith ep eq wp wq hsel hpairWith hmatch hwp hwq

end MonomialSums

namespace Hardy

open Complex MeasureTheory Set Filter
open scoped Real Topology Polynomial ComplexConjugate

noncomputable section

def hardySum (u : ℕ → ℂ) (z : ℂ) : ℂ := ∑' n, u n * z ^ n

def partialPoly (u : ℕ → ℂ) (N : ℕ) : ℂ[X] :=
  ∑ n ∈ Finset.range N, Polynomial.monomial n (u n)

lemma eval_partialPoly (u : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    (partialPoly u N).eval z = ∑ n ∈ Finset.range N, u n * z ^ n := by
  simp [partialPoly, Polynomial.eval_finsetSum, mul_comm]

lemma coeff_partialPoly (u : ℕ → ℂ) (N n : ℕ) :
    (partialPoly u N).coeff n = if n < N then u n else 0 := by
  classical
  simp [partialPoly, Polynomial.coeff_monomial, eq_comm]

lemma support_partialPoly_subset (u : ℕ → ℂ) (N : ℕ) :
    (partialPoly u N).support ⊆ Finset.range N := by
  intro n hn
  simp only [Polynomial.mem_support_iff] at hn
  by_contra h
  have hN : ¬ n < N := by simpa using h
  exact hn (by simp [coeff_partialPoly, hN])

lemma sum_range_sq_norm_eq_support (u : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖u n‖ ^ 2 =
      ∑ n ∈ (partialPoly u N).support, ‖(partialPoly u N).coeff n‖ ^ 2 := by
  classical
  rw [Finset.sum_subset (support_partialPoly_subset u N)]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_range] at hn
    simp [coeff_partialPoly, hn]
  · intro n hnR hnS
    have hz : (partialPoly u N).coeff n = 0 := Polynomial.notMem_support_iff.mp hnS
    rw [hz]
    simp

lemma finite_norm_parseval (u : ℕ → ℂ) (N : ℕ) :
    Real.circleAverage
        (fun z ↦ ‖∑ n ∈ Finset.range N, u n * z ^ n‖ ^ 2) 0 1 =
      ∑ n ∈ Finset.range N, ‖u n‖ ^ 2 := by
  simp_rw [← eval_partialPoly]
  rw [← (partialPoly u N).sum_sq_norm_coeff_eq_circleAverage]
  exact (sum_range_sq_norm_eq_support u N).symm

lemma two_mul_re_mul_conj (a b : ℂ) :
    2 * (a * conj b).re = ‖a + b‖ ^ 2 - ‖a‖ ^ 2 - ‖b‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_add]
  ring

lemma finite_inner_parseval (u v : ℕ → ℂ) (N : ℕ) :
    Real.circleAverage
        (fun z ↦ ((∑ n ∈ Finset.range N, u n * z ^ n) *
          conj (∑ n ∈ Finset.range N, v n * z ^ n)).re) 0 1 =
      ∑ n ∈ Finset.range N, (u n * conj (v n)).re := by
  let U : ℂ → ℂ := fun z ↦ ∑ n ∈ Finset.range N, u n * z ^ n
  let V : ℂ → ℂ := fun z ↦ ∑ n ∈ Finset.range N, v n * z ^ n
  have hU : Continuous U := by
    dsimp [U]
    fun_prop
  have hV : Continuous V := by
    dsimp [V]
    fun_prop
  have hiU : CircleIntegrable (fun z ↦ ‖U z‖ ^ 2) 0 1 := by
    apply ContinuousOn.circleIntegrable'
    exact (hU.norm.pow 2).continuousOn
  have hiV : CircleIntegrable (fun z ↦ ‖V z‖ ^ 2) 0 1 := by
    apply ContinuousOn.circleIntegrable'
    exact (hV.norm.pow 2).continuousOn
  have hiUV : CircleIntegrable (fun z ↦ ‖U z + V z‖ ^ 2) 0 1 := by
    apply ContinuousOn.circleIntegrable'
    exact ((hU.add hV).norm.pow 2).continuousOn
  have hiCross : CircleIntegrable (fun z ↦ (U z * conj (V z)).re) 0 1 := by
    apply ContinuousOn.circleIntegrable'
    fun_prop
  have hpoint : (fun z ↦ 2 * (U z * conj (V z)).re) =
      fun z ↦ ‖U z + V z‖ ^ 2 - ‖U z‖ ^ 2 - ‖V z‖ ^ 2 := by
    funext z
    exact two_mul_re_mul_conj (U z) (V z)
  have havg : 2 * Real.circleAverage (fun z ↦ (U z * conj (V z)).re) 0 1 =
      Real.circleAverage (fun z ↦ ‖U z + V z‖ ^ 2) 0 1 -
        Real.circleAverage (fun z ↦ ‖U z‖ ^ 2) 0 1 -
          Real.circleAverage (fun z ↦ ‖V z‖ ^ 2) 0 1 := by
    have hsmul := Real.circleAverage_fun_smul (a := (2 : ℝ))
      (f := fun z ↦ (U z * conj (V z)).re) (c := (0 : ℂ)) (R := (1 : ℝ))
    rw [show 2 * Real.circleAverage (fun z ↦ (U z * conj (V z)).re) 0 1 =
        Real.circleAverage (fun z ↦ 2 * (U z * conj (V z)).re) 0 1 by
      simpa only [smul_eq_mul] using hsmul.symm]
    rw [hpoint]
    change Real.circleAverage
        ((fun z ↦ ‖U z + V z‖ ^ 2) - (fun z ↦ ‖U z‖ ^ 2) - (fun z ↦ ‖V z‖ ^ 2)) 0 1 = _
    rw [Real.circleAverage_sub (hiUV.sub hiU) hiV,
      Real.circleAverage_sub hiUV hiU]
  have hUeq : Real.circleAverage (fun z ↦ ‖U z‖ ^ 2) 0 1 =
      ∑ n ∈ Finset.range N, ‖u n‖ ^ 2 := by
    simpa [U] using finite_norm_parseval u N
  have hVeq : Real.circleAverage (fun z ↦ ‖V z‖ ^ 2) 0 1 =
      ∑ n ∈ Finset.range N, ‖v n‖ ^ 2 := by
    simpa [V] using finite_norm_parseval v N
  have hUVeq : Real.circleAverage (fun z ↦ ‖U z + V z‖ ^ 2) 0 1 =
      ∑ n ∈ Finset.range N, ‖u n + v n‖ ^ 2 := by
    simpa only [U, V, Finset.sum_add_distrib, add_mul] using
      finite_norm_parseval (fun n ↦ u n + v n) N
  rw [hUeq, hVeq, hUVeq] at havg
  have hcoeff : (∑ n ∈ Finset.range N, ‖u n + v n‖ ^ 2) -
      (∑ n ∈ Finset.range N, ‖u n‖ ^ 2) -
        (∑ n ∈ Finset.range N, ‖v n‖ ^ 2) =
      2 * ∑ n ∈ Finset.range N, (u n * conj (v n)).re := by
    calc
      _ = ∑ n ∈ Finset.range N,
          (‖u n + v n‖ ^ 2 - ‖u n‖ ^ 2 - ‖v n‖ ^ 2) := by
            rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      _ = ∑ n ∈ Finset.range N, 2 * (u n * conj (v n)).re := by
            apply Finset.sum_congr rfl
            intro n hn
            exact (two_mul_re_mul_conj (u n) (v n)).symm
      _ = _ := by rw [Finset.mul_sum]
  rw [hcoeff] at havg
  exact mul_left_cancel₀ two_ne_zero havg

lemma uniform_partial_hardySum {u : ℕ → ℂ} (hu : Summable (fun n ↦ ‖u n‖)) :
    TendstoUniformlyOn
      (fun N z ↦ ∑ n ∈ Finset.range N, u n * z ^ n) (hardySum u) atTop
      (Metric.sphere (0 : ℂ) 1) := by
  apply tendstoUniformlyOn_tsum_nat hu
  intro n z hz
  rw [norm_mul, norm_pow]
  have hznorm : ‖z‖ = 1 := by simpa [Metric.mem_sphere] using hz
  simp [hznorm]

lemma continuousOn_hardySum {u : ℕ → ℂ} (hu : Summable (fun n ↦ ‖u n‖)) :
    ContinuousOn (hardySum u) (Metric.closedBall (0 : ℂ) 1) := by
  refine continuousOn_tsum (u := fun n ↦ ‖u n‖) ?_ hu ?_
  · intro n
    fun_prop
  · intro n z hz
    rw [norm_mul, norm_pow]
    have hznorm : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hz
    calc
      ‖u n‖ * ‖z‖ ^ n ≤ ‖u n‖ * 1 ^ n := by gcongr
      _ = ‖u n‖ := by simp

lemma tendsto_circleAverage_of_uniform {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ}
    (hf : ∀ N, ContinuousOn (f N) (Metric.sphere (0 : ℂ) 1))
    (h : TendstoUniformlyOn f g atTop (Metric.sphere (0 : ℂ) 1)) :
    Tendsto (fun N ↦ Real.circleAverage (f N) 0 1) atTop
      (𝓝 (Real.circleAverage g 0 1)) := by
  unfold Real.circleAverage
  apply tendsto_const_nhds.smul
    (TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
      (Filter.Eventually.of_forall fun N ↦
        (hf N).comp (continuous_circleMap 0 1).continuousOn
          (fun x hx ↦ by simpa only [abs_one] using circleMap_mem_sphere' 0 1 x)) ?_)
  have hc := h.comp (circleMap 0 1)
  exact hc.mono (by
    intro x hx
    simpa only [Set.mem_preimage, abs_one] using circleMap_mem_sphere' 0 1 x)

lemma norm_partial_hardySum_le_tsum {u : ℕ → ℂ} (hu : Summable (fun n ↦ ‖u n‖))
    (N : ℕ) {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) 1) :
    ‖∑ n ∈ Finset.range N, u n * z ^ n‖ ≤ ∑' n, ‖u n‖ := by
  have hznorm : ‖z‖ = 1 := by simpa [Metric.mem_sphere] using hz
  calc
    ‖∑ n ∈ Finset.range N, u n * z ^ n‖ ≤
        ∑ n ∈ Finset.range N, ‖u n * z ^ n‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.range N, ‖u n‖ := by simp [norm_mul, norm_pow, hznorm]
    _ ≤ ∑' n, ‖u n‖ := hu.sum_le_tsum (Finset.range N) (fun n hn ↦ norm_nonneg _)

lemma norm_hardySum_le_tsum {u : ℕ → ℂ} (hu : Summable (fun n ↦ ‖u n‖))
    {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) 1) :
    ‖hardySum u z‖ ≤ ∑' n, ‖u n‖ := by
  have hznorm : ‖z‖ = 1 := by simpa [Metric.mem_sphere] using hz
  have hs : Summable (fun n ↦ ‖u n * z ^ n‖) := by
    simpa [norm_mul, norm_pow, hznorm] using hu
  calc
    ‖hardySum u z‖ ≤ ∑' n, ‖u n * z ^ n‖ := norm_tsum_le_tsum_norm hs
    _ = ∑' n, ‖u n‖ := by congr 1; funext n; simp [norm_mul, norm_pow, hznorm]

lemma uniform_partial_inner {u v : ℕ → ℂ}
    (hu : Summable (fun n ↦ ‖u n‖)) (hv : Summable (fun n ↦ ‖v n‖)) :
    TendstoUniformlyOn
      (fun N z ↦ ((∑ n ∈ Finset.range N, u n * z ^ n) *
        conj (∑ n ∈ Finset.range N, v n * z ^ n)).re)
      (fun z ↦ (hardySum u z * conj (hardySum v z)).re) atTop
      (Metric.sphere (0 : ℂ) 1) := by
  let U : ℕ → ℂ → ℂ := fun N z ↦ ∑ n ∈ Finset.range N, u n * z ^ n
  let V : ℕ → ℂ → ℂ := fun N z ↦ ∑ n ∈ Finset.range N, v n * z ^ n
  have hU : TendstoUniformlyOn U (hardySum u) atTop (Metric.sphere (0 : ℂ) 1) := by
    simpa only [U] using uniform_partial_hardySum hu
  have hV : TendstoUniformlyOn V (hardySum v) atTop (Metric.sphere (0 : ℂ) 1) := by
    simpa only [V] using uniform_partial_hardySum hv
  have hVc : TendstoUniformlyOn (fun N z ↦ conj (V N z))
      (fun z ↦ conj (hardySum v z)) atTop (Metric.sphere (0 : ℂ) 1) := by
    exact Complex.isometry_conj.uniformContinuous.comp_tendstoUniformlyOn hV
  have hpair : TendstoUniformlyOn (fun N z ↦ (U N z, conj (V N z)))
      (fun z ↦ (hardySum u z, conj (hardySum v z))) atTop
      (Metric.sphere (0 : ℂ) 1) := by
    rw [Metric.tendstoUniformlyOn_iff] at hU hVc ⊢
    intro ε hε
    filter_upwards [hU ε hε, hVc ε hε] with N hUN hVN
    intro z hz
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨hUN z hz, hVN z hz⟩
  let Bu : ℝ := ∑' n, ‖u n‖
  let Bv : ℝ := ∑' n, ‖v n‖
  let s : Set (ℂ × ℂ) := Metric.closedBall 0 Bu ×ˢ Metric.closedBall 0 Bv
  have hs : Bornology.IsBounded s := by
    exact Metric.isBounded_closedBall.prod Metric.isBounded_closedBall
  have hpartial : ∀ N z, z ∈ Metric.sphere (0 : ℂ) 1 →
      (U N z, conj (V N z)) ∈ s := by
    intro N z hz
    constructor
    · simpa [s, Bu, Metric.mem_closedBall] using norm_partial_hardySum_le_tsum hu N hz
    · simpa [s, Bv, Metric.mem_closedBall, Complex.norm_conj] using
        norm_partial_hardySum_le_tsum hv N hz
  have hlimit : ∀ z, z ∈ Metric.sphere (0 : ℂ) 1 →
      (hardySum u z, conj (hardySum v z)) ∈ s := by
    intro z hz
    constructor
    · simpa [s, Bu, Metric.mem_closedBall] using norm_hardySum_le_tsum hu hz
    · simpa [s, Bv, Metric.mem_closedBall, Complex.norm_conj] using
        norm_hardySum_le_tsum hv hz
  have hmul := hs.uniformContinuousOn_smul.comp_tendstoUniformlyOn_eventually
    (Filter.Eventually.of_forall hpartial) hlimit hpair
  have hre := Complex.uniformContinuous_re.comp_tendstoUniformlyOn hmul
  simpa only [U, V, Function.uncurry_apply_pair, smul_eq_mul, Function.comp_def] using hre

lemma summable_re_mul_conj {u v : ℕ → ℂ}
    (hu : Summable (fun n ↦ ‖u n‖)) (hv : Summable (fun n ↦ ‖v n‖)) :
    Summable (fun n ↦ (u n * conj (v n)).re) := by
  let Bv : ℝ := ∑' n, ‖v n‖
  have hBv_nonneg : 0 ≤ Bv := tsum_nonneg fun n ↦ norm_nonneg _
  have hv_le : ∀ n, ‖v n‖ ≤ Bv := by
    intro n
    have h := hv.sum_le_tsum {n} (fun i hi ↦ norm_nonneg (v i))
    simpa [Bv] using h
  apply (hu.mul_left Bv).of_norm_bounded
  intro n
  calc
    ‖(u n * conj (v n)).re‖ ≤ ‖u n * conj (v n)‖ := Complex.abs_re_le_norm _
    _ = ‖u n‖ * ‖v n‖ := by simp [norm_mul]
    _ ≤ ‖u n‖ * Bv := mul_le_mul_of_nonneg_left (hv_le n) (norm_nonneg (u n))
    _ = Bv * ‖u n‖ := mul_comm _ _

theorem infinite_inner_parseval {u v : ℕ → ℂ}
    (hu : Summable (fun n ↦ ‖u n‖)) (hv : Summable (fun n ↦ ‖v n‖)) :
    Real.circleAverage (fun z ↦ (hardySum u z * conj (hardySum v z)).re) 0 1 =
      ∑' n, (u n * conj (v n)).re := by
  let f : ℕ → ℂ → ℝ := fun N z ↦
    ((∑ n ∈ Finset.range N, u n * z ^ n) *
      conj (∑ n ∈ Finset.range N, v n * z ^ n)).re
  have hf_cont : ∀ N, ContinuousOn (f N) (Metric.sphere (0 : ℂ) 1) := by
    intro N
    apply Continuous.continuousOn
    dsimp [f]
    fun_prop
  have hleft : Tendsto (fun N ↦ Real.circleAverage (f N) 0 1) atTop
      (𝓝 (Real.circleAverage (fun z ↦ (hardySum u z * conj (hardySum v z)).re) 0 1)) :=
    tendsto_circleAverage_of_uniform hf_cont (by
      simpa only [f] using uniform_partial_inner hu hv)
  have hright : Tendsto (fun N ↦ ∑ n ∈ Finset.range N, (u n * conj (v n)).re) atTop
      (𝓝 (∑' n, (u n * conj (v n)).re)) :=
    (summable_re_mul_conj hu hv).hasSum.tendsto_sum_nat
  have hright' : Tendsto (fun N ↦ Real.circleAverage (f N) 0 1) atTop
      (𝓝 (∑' n, (u n * conj (v n)).re)) := by
    apply hright.congr'
    exact Filter.Eventually.of_forall fun N ↦ by
      symm
      simpa only [f] using finite_inner_parseval u v N
  exact tendsto_nhds_unique hleft hright'

theorem infinite_norm_parseval {u : ℕ → ℂ} (hu : Summable (fun n ↦ ‖u n‖)) :
    Real.circleAverage (fun z ↦ ‖hardySum u z‖ ^ 2) 0 1 = ∑' n, ‖u n‖ ^ 2 := by
  have hreal (x : ℝ) : (((x : ℂ) ^ 2).re) = x ^ 2 := by
    simp only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  simpa only [Complex.mul_conj', hreal] using infinite_inner_parseval hu hu

end

end Hardy

/-! ### Exact Fourier estimates for the upper bound -/

namespace Upper

open Complex Filter MeasureTheory Polynomial Real Set
open scoped ComplexConjugate

noncomputable def radialPolynomial (r : ℂ) (p : ℂ[X]) : ℂ[X] :=
  p.comp (C r * X)

lemma radialPolynomial_coeff (r : ℂ) (p : ℂ[X]) (n : ℕ) :
    (radialPolynomial r p).coeff n = p.coeff n * r ^ n := by
  simp [radialPolynomial]

lemma radialPolynomial_eval (r z : ℂ) (p : ℂ[X]) :
    (radialPolynomial r p).eval z = p.eval (r * z) := by
  simp [radialPolynomial, eval_comp]

lemma radialPolynomial_parseval (r : ℂ) (p : ℂ[X]) :
    ∑ n ∈ (radialPolynomial r p).support, ‖p.coeff n * r ^ n‖ ^ 2 =
      circleAverage (fun z ↦ ‖p.eval (r * z)‖ ^ 2) 0 1 := by
  simpa [radialPolynomial_coeff, radialPolynomial_eval] using
    (radialPolynomial r p).sum_sq_norm_coeff_eq_circleAverage

lemma radialDerivative_parseval (r : ℂ) (p : ℂ[X]) :
    ∑ n ∈ (radialPolynomial r p.derivative).support,
        ‖((n + 1 : ℕ) : ℂ) * p.coeff (n + 1) * r ^ n‖ ^ 2 =
      circleAverage (fun z ↦ ‖p.derivative.eval (r * z)‖ ^ 2) 0 1 := by
  simpa [coeff_derivative, mul_comm] using radialPolynomial_parseval r p.derivative

noncomputable def dirichletPolynomial (m : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.range m, X ^ j

lemma dirichletPolynomial_coeff (m n : ℕ) :
    (dirichletPolynomial m).coeff n = if n < m then 1 else 0 := by
  simp [dirichletPolynomial, finsetSum_coeff, coeff_X_pow]

lemma dirichletPolynomial_support (m : ℕ) :
    (dirichletPolynomial m).support = Finset.range m := by
  ext n
  simp [mem_support_iff, dirichletPolynomial_coeff]

lemma dirichletPolynomial_circleAverage_sq (m : ℕ) :
    circleAverage (fun z ↦ ‖(dirichletPolynomial m).eval z‖ ^ 2) 0 1 = m := by
  rw [← (dirichletPolynomial m).sum_sq_norm_coeff_eq_circleAverage,
    dirichletPolynomial_support]
  simp only [dirichletPolynomial_coeff]
  calc
    ∑ n ∈ Finset.range m, ‖if n < m then (1 : ℂ) else 0‖ ^ 2 =
        ∑ _n ∈ Finset.range m, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [if_pos (Finset.mem_range.mp hn)]
      norm_num
    _ = m := by simp

lemma one_sub_X_mul_dirichletPolynomial (m : ℕ) :
    (1 - X) * dirichletPolynomial m = 1 - X ^ m := by
  simpa [dirichletPolynomial] using (mul_neg_geom_sum (X : ℂ[X]) m)

lemma eval_one_sub_mul_dirichletPolynomial (m : ℕ) (z : ℂ) :
    (1 - z) * (dirichletPolynomial m).eval z = 1 - z ^ m := by
  simpa using congrArg (eval z) (one_sub_X_mul_dirichletPolynomial m)

lemma circleAverage_poissonKernel_real (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    circleAverage (poissonKernel 0 (r : ℂ)) 0 1 = 1 := by
  have hf : InnerProductSpace.HarmonicOnNhd (fun _ : ℂ ↦ (1 : ℝ))
      (Metric.closedBall 0 1) := by
    exact InnerProductSpace.harmonicOnNhd_const 1
  have hw : (r : ℂ) ∈ Metric.ball 0 1 := by
    simpa [Metric.mem_ball, Complex.norm_real, abs_of_nonneg hr0] using hr1
  have h := InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul hf hw
  have hfun : poissonKernel 0 (r : ℂ) • (fun _ : ℂ ↦ (1 : ℝ)) =
      poissonKernel 0 (r : ℂ) := by
    ext z
    simp
  rw [hfun] at h
  exact h

lemma circleAverage_mul_reciprocal_norm_sq (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    circleAverage (fun z : ℂ ↦
      (1 - r ^ 2) * ‖(z - (r : ℂ))⁻¹‖ ^ 2) 0 1 = 1 := by
  calc
    circleAverage (fun z : ℂ ↦
        (1 - r ^ 2) * ‖(z - (r : ℂ))⁻¹‖ ^ 2) 0 1 =
        circleAverage (poissonKernel 0 (r : ℂ)) 0 1 := by
      apply circleAverage_congr_sphere
      intro z hz
      have hznorm : ‖z‖ = 1 := by
        simpa [Metric.mem_sphere] using hz
      rw [poissonKernel_def]
      simp [hznorm, Complex.norm_real, abs_of_nonneg hr0, norm_inv,
        div_eq_mul_inv, inv_pow]
    _ = 1 := circleAverage_poissonKernel_real r hr0 hr1

lemma circleAverage_reciprocal_norm_sq (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    circleAverage (fun z : ℂ ↦ ‖(z - (r : ℂ))⁻¹‖ ^ 2) 0 1 =
      (1 - r ^ 2)⁻¹ := by
  have ha : 0 < 1 - r ^ 2 := by nlinarith [sq_nonneg r]
  have h := circleAverage_mul_reciprocal_norm_sq r hr0 hr1
  change circleAverage (fun z : ℂ ↦
      (1 - r ^ 2) • ‖(z - (r : ℂ))⁻¹‖ ^ 2) 0 1 = 1 at h
  rw [circleAverage_fun_smul, smul_eq_mul] at h
  have hdiv : circleAverage (fun z : ℂ ↦ ‖(z - (r : ℂ))⁻¹‖ ^ 2) 0 1 =
      1 / (1 - r ^ 2) := by
    apply (eq_div_iff ha.ne').2
    simpa [mul_comm] using h
  simpa only [one_div] using hdiv

lemma circleAverage_one_sub_mul_reciprocal_norm_sq
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    circleAverage (fun z : ℂ ↦ ‖(1 - (r : ℂ) * z)⁻¹‖ ^ 2) 0 1 =
      (1 - r ^ 2)⁻¹ := by
  calc
    circleAverage (fun z : ℂ ↦ ‖(1 - (r : ℂ) * z)⁻¹‖ ^ 2) 0 1 =
        circleAverage (fun z : ℂ ↦ ‖(z⁻¹ - (r : ℂ))⁻¹‖ ^ 2) 0 1 := by
      apply circleAverage_congr_sphere
      intro z hz
      have hznorm : ‖z‖ = 1 := by
        simpa [Metric.mem_sphere] using hz
      have hz0 : z ≠ 0 := by
        exact norm_ne_zero_iff.mp (by simp [hznorm])
      have halg : z⁻¹ - (r : ℂ) = z⁻¹ * (1 - (r : ℂ) * z) := by
        field_simp
      change ‖(1 - (r : ℂ) * z)⁻¹‖ ^ 2 = ‖(z⁻¹ - (r : ℂ))⁻¹‖ ^ 2
      rw [halg, mul_inv_rev, norm_mul, norm_inv, inv_inv, hznorm]
      norm_num
    _ = circleAverage (fun z : ℂ ↦ ‖(z - (r : ℂ))⁻¹‖ ^ 2) 0 1 := by
      simpa only [Function.comp_apply] using
        (circleAverage_zero_one_congr_inv
          (f := fun z : ℂ ↦ ‖(z - (r : ℂ))⁻¹‖ ^ 2))
    _ = (1 - r ^ 2)⁻¹ := circleAverage_reciprocal_norm_sq r hr0 hr1

private lemma continuous_circleMap_zero_one :
    Continuous (fun t : ℝ ↦ circleMap (0 : ℂ) 1 t) := by
  fun_prop

lemma circleAverage_mul_le_sqrt_mul_sqrt
    {f g : ℂ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ z, 0 ≤ f z) (hg0 : ∀ z, 0 ≤ g z) :
    circleAverage (fun z ↦ f z * g z) 0 1 ≤
      Real.sqrt (circleAverage (fun z ↦ f z ^ 2) 0 1) *
        Real.sqrt (circleAverage (fun z ↦ g z ^ 2) 0 1) := by
  let F : ℝ → ℝ := fun t ↦ f (circleMap 0 1 t)
  let G : ℝ → ℝ := fun t ↦ g (circleMap 0 1 t)
  have hF : Continuous F := hf.comp continuous_circleMap_zero_one
  have hG : Continuous G := hg.comp continuous_circleMap_zero_one
  let μ : Measure ℝ := volume.restrict (Set.uIoc 0 (2 * π))
  have hF2 : MemLp F 2 μ := by
    rw [memLp_two_iff_integrable_sq hF.aestronglyMeasurable]
    exact intervalIntegrable_iff.mp ((hF.pow 2).intervalIntegrable 0 (2 * π))
  have hG2 : MemLp G 2 μ := by
    rw [memLp_two_iff_integrable_sq hG.aestronglyMeasurable]
    exact intervalIntegrable_iff.mp ((hG.pow 2).intervalIntegrable 0 (2 * π))
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (Real.HolderConjugate.two_two)
    (f := F) (g := G) (μ := μ)
    (Filter.Eventually.of_forall fun t ↦ hf0 _)
    (Filter.Eventually.of_forall fun t ↦ hg0 _)
    (by simpa using hF2) (by simpa using hG2)
  have hpi : 0 < 2 * π := mul_pos (by norm_num) Real.pi_pos
  have hholder' :
      (∫ t in 0..2 * π, F t * G t) ≤
        Real.sqrt (∫ t in 0..2 * π, F t ^ 2) *
          Real.sqrt (∫ t in 0..2 * π, G t ^ 2) := by
    simpa [μ, Set.uIoc_of_le hpi.le, ← intervalIntegral.integral_of_le hpi.le,
      Real.sqrt_eq_rpow, one_div] using hholder
  simp only [circleAverage_def, smul_eq_mul]
  dsimp [F, G] at hholder'
  have hscale : 0 < (2 * π : ℝ)⁻¹ := inv_pos.mpr hpi
  calc
    (2 * π : ℝ)⁻¹ * ∫ t in 0..2 * π,
          f (circleMap 0 1 t) * g (circleMap 0 1 t) ≤
        (2 * π : ℝ)⁻¹ *
          (Real.sqrt (∫ t in 0..2 * π, f (circleMap 0 1 t) ^ 2) *
            Real.sqrt (∫ t in 0..2 * π, g (circleMap 0 1 t) ^ 2)) :=
      mul_le_mul_of_nonneg_left hholder' hscale.le
    _ = Real.sqrt ((2 * π : ℝ)⁻¹ *
          ∫ t in 0..2 * π, f (circleMap 0 1 t) ^ 2) *
        Real.sqrt ((2 * π : ℝ)⁻¹ *
          ∫ t in 0..2 * π, g (circleMap 0 1 t) ^ 2) := by
      rw [Real.sqrt_mul hscale.le, Real.sqrt_mul hscale.le]
      nth_rewrite 1 [← Real.mul_self_sqrt hscale.le]
      ring

lemma two_mul_le_scaled_sq (u v lam : ℝ) (hlam : 0 < lam) :
    2 * u * v ≤ lam * u ^ 2 + lam⁻¹ * v ^ 2 := by
  apply le_of_mul_le_mul_left _ hlam
  have hinv : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hlam.ne'
  nlinarith [sq_nonneg (lam * u - v)]

noncomputable def ederivHardyCoeff (P : ℕ → ℂ) (r : ℝ) (n : ℕ) : ℂ :=
  ((n + 1 : ℕ) : ℂ) * P (n + 1) * (r : ℂ) ^ n

lemma summable_norm_ederivHardyCoeff
    (P : ℕ → ℂ) {C r : ℝ} (hC0 : 0 ≤ C) (hP : ∀ n, ‖P n‖ ≤ C)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n ↦ ‖ederivHardyCoeff P r n‖) := by
  have hrabs : |r| < 1 := by simpa [abs_of_nonneg hr0] using hr1
  have hmajor : Summable (fun n : ℕ ↦ C * (n + 1 : ℝ) * r ^ n) := by
    have hbase : Summable (fun n : ℕ ↦ (n + 1 : ℝ) * r ^ n) := by
      simpa using (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrabs)
    simpa only [mul_assoc] using hbase.mul_left C
  apply hmajor.of_nonneg_of_le
  · intro n
    positivity
  · intro n
    rw [ederivHardyCoeff, norm_mul, norm_mul, Complex.norm_natCast, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    have hn0 : 0 ≤ (n + 1 : ℝ) := by positivity
    have hrn0 : 0 ≤ r ^ n := pow_nonneg hr0 n
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hP (n + 1)) hn0) hrn0

lemma norm_ederivHardyCoeff_sq_le
    (P : ℕ → ℂ) {C r : ℝ} (hC0 : 0 ≤ C) (hP : ∀ n, ‖P n‖ ≤ C)
    (hr0 : 0 ≤ r) (n : ℕ) :
    ‖ederivHardyCoeff P r n‖ ^ 2 ≤
      2 * C ^ 2 * (((n + 2).choose 2 : ℕ) : ℝ) * (r ^ 2) ^ n := by
  have hchoose :
      2 * ((((n + 2).choose 2 : ℕ) : ℝ)) = (n + 2 : ℝ) * (n + 1 : ℝ) := by
    rw [Nat.cast_choose_two]
    push_cast
    ring
  rw [ederivHardyCoeff, norm_mul, norm_mul, Complex.norm_natCast, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
    Nat.cast_add, Nat.cast_one]
  have hcoeff := hP (n + 1)
  have hsqcoeff : ‖P (n + 1)‖ ^ 2 ≤ C ^ 2 := by
    nlinarith [norm_nonneg (P (n + 1))]
  calc
    (((n : ℝ) + 1) * ‖P (n + 1)‖ * r ^ n) ^ 2 =
        ((n : ℝ) + 1) ^ 2 * ‖P (n + 1)‖ ^ 2 * (r ^ 2) ^ n := by
      rw [mul_pow, mul_pow, ← pow_mul, show n * 2 = 2 * n by omega, pow_mul]
    _ ≤ ((n : ℝ) + 1) ^ 2 * C ^ 2 * (r ^ 2) ^ n := by
      gcongr
    _ ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) * C ^ 2 * (r ^ 2) ^ n := by
      gcongr <;> nlinarith
    _ = 2 * C ^ 2 * (((n + 2).choose 2 : ℕ) : ℝ) * (r ^ 2) ^ n := by
      rw [← hchoose]
      ring

lemma circleAverage_hardy_ederiv_sq_le
    (P : ℕ → ℂ) {C r : ℝ} (hC0 : 0 ≤ C) (hP : ∀ n, ‖P n‖ ≤ C)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    circleAverage (fun z ↦ ‖Hardy.hardySum (ederivHardyCoeff P r) z‖ ^ 2) 0 1 ≤
      2 * C ^ 2 / (1 - r ^ 2) ^ 3 := by
  rw [Hardy.infinite_norm_parseval
    (summable_norm_ederivHardyCoeff P hC0 hP hr0 hr1)]
  let g : ℕ → ℝ := fun n ↦
    2 * C ^ 2 * (((n + 2).choose 2 : ℕ) : ℝ) * (r ^ 2) ^ n
  have hrabs : |r ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg r)]
    nlinarith [sq_nonneg (r - 1)]
  have hg0 : ∀ n, 0 ≤ g n := by
    intro n
    dsimp [g]
    positivity
  have hsum : Summable g := by
    have hbase : Summable (fun n : ℕ ↦
        ((((n + 2).choose 2 : ℕ) : ℝ)) * (r ^ 2) ^ n) :=
      summable_choose_mul_geometric_of_norm_lt_one 2 hrabs
    change Summable (fun n : ℕ ↦
      2 * C ^ 2 * (((n + 2).choose 2 : ℕ) : ℝ) * (r ^ 2) ^ n)
    refine (hbase.mul_left (2 * C ^ 2)).congr ?_
    intro n
    ring
  have hpoint : ∀ n, ‖ederivHardyCoeff P r n‖ ^ 2 ≤ g n := by
    intro n
    exact norm_ederivHardyCoeff_sq_le P hC0 hP hr0 n
  have hcoeffsum : Summable (fun n ↦ ‖ederivHardyCoeff P r n‖ ^ 2) :=
    hsum.of_nonneg_of_le (fun n ↦ sq_nonneg _) hpoint
  calc
    ∑' n, ‖ederivHardyCoeff P r n‖ ^ 2 ≤ ∑' n, g n :=
      hcoeffsum.tsum_le_tsum hpoint hsum
    _ = 2 * C ^ 2 / (1 - r ^ 2) ^ 3 := by
      dsimp [g]
      calc
        (∑' n : ℕ, 2 * C ^ 2 * (((n + 2).choose 2 : ℕ) : ℝ) * (r ^ 2) ^ n) =
            ∑' n : ℕ, (2 * C ^ 2) *
              ((((n + 2).choose 2 : ℕ) : ℝ) * (r ^ 2) ^ n) := by
          apply tsum_congr
          intro n
          ring
        _ = (2 * C ^ 2) *
            ∑' n : ℕ, (((n + 2).choose 2 : ℕ) : ℝ) * (r ^ 2) ^ n := by
          rw [tsum_mul_left]
        _ = 2 * C ^ 2 / (1 - r ^ 2) ^ 3 := by
          rw [tsum_choose_mul_geometric_of_norm_lt_one 2 hrabs]
          ring

end Upper


noncomputable def Freal (A : Set ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, (indicator A n : ℝ) * x ^ n

noncomputable def FderivReal (A : Set ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, (n : ℝ) * (indicator A n : ℝ) * x ^ (n - 1)

noncomputable def Ereal (A : Set ℕ) (c x : ℝ) : ℝ :=
  ∑' n : ℕ, remainder A c n * x ^ n

noncomputable def EderivReal (A : Set ℕ) (c x : ℝ) : ℝ :=
  ∑' n : ℕ, (n : ℝ) * remainder A c n * x ^ (n - 1)

lemma ofReal_Freal (A : Set ℕ) (x : ℝ) :
    (Freal A x : ℂ) = F A (x : ℂ) := by
  rw [Freal, Complex.ofReal_tsum, F]
  apply tsum_congr
  intro n
  rw [indicatorC_eq_natCast]
  norm_cast

lemma ofReal_FderivReal (A : Set ℕ) (x : ℝ) :
    (FderivReal A x : ℂ) = Fderiv A (x : ℂ) := by
  rw [FderivReal, Complex.ofReal_tsum, Fderiv]
  apply tsum_congr
  intro n
  rw [indicatorC_eq_natCast]
  norm_cast

lemma ofReal_Ereal (A : Set ℕ) (c x : ℝ) :
    (Ereal A c x : ℂ) = E (remainderC A c) (x : ℂ) := by
  rw [Ereal, Complex.ofReal_tsum, E]
  apply tsum_congr
  intro n
  simp [remainderC]

lemma ofReal_EderivReal (A : Set ℕ) (c x : ℝ) :
    (EderivReal A c x : ℂ) = Ederiv (remainderC A c) (x : ℂ) := by
  rw [EderivReal, Complex.ofReal_tsum, Ederiv]
  apply tsum_congr
  intro n
  simp [remainderC]

lemma Freal_nonneg (A : Set ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Freal A x := by
  apply tsum_nonneg
  intro n
  positivity

lemma FderivReal_nonneg (A : Set ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ FderivReal A x := by
  apply tsum_nonneg
  intro n
  positivity

lemma tsum_nat_mul_pow_pred_eq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (∑' n : ℕ, (n : ℝ) * x ^ (n - 1)) = (1 - x)⁻¹ ^ 2 := by
  have hs0 : Summable (fun n : ℕ ↦ (n : ℝ) * x ^ (n - 1)) :=
    summable_nat_mul_pow_pred hx0 hx1
  have hshift : (∑' n : ℕ, (n : ℝ) * x ^ (n - 1)) =
      ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * x ^ (n + 1 - 1) := by
    have h := hs0.sum_add_tsum_nat_add 1
    simpa using h.symm
  rw [hshift]
  have hs1 : Summable (fun n : ℕ ↦ (n : ℝ) * x ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (by simpa [abs_of_nonneg hx0])
  have hs2 : Summable (fun n : ℕ ↦ x ^ n) :=
    summable_geometric_of_lt_one hx0 hx1
  calc
    ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * x ^ (n + 1 - 1) =
        ∑' n : ℕ, ((n : ℝ) * x ^ n + x ^ n) := by
          apply tsum_congr
          intro n
          push_cast
          ring
    _ = (∑' n : ℕ, (n : ℝ) * x ^ n) + ∑' n : ℕ, x ^ n :=
      Summable.tsum_add hs1 hs2
    _ = x / (1 - x) ^ 2 + (1 - x)⁻¹ := by
      rw [tsum_coe_mul_geometric_of_norm_lt_one (by simpa [abs_of_nonneg hx0]),
        tsum_geometric_of_lt_one hx0 hx1]
    _ = (1 - x)⁻¹ ^ 2 := by
      field_simp [ne_of_gt (sub_pos.mpr hx1)]
      ring

lemma abs_Ereal_le (A : Set ℕ) (c C x : ℝ)
    (hC : ∀ n, |remainder A c n| ≤ C) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    |Ereal A c x| ≤ C * (1 - x)⁻¹ := by
  have h := norm_E_le (remainderC A c) (fun n ↦ by simpa [norm_remainderC] using hC n)
    (z := (x : ℂ)) (by simpa [abs_of_nonneg hx0])
  rw [← ofReal_Ereal, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0] at h
  simpa [div_eq_mul_inv] using h

lemma abs_EderivReal_le (A : Set ℕ) (c C x : ℝ)
    (hC : ∀ n, |remainder A c n| ≤ C) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    |EderivReal A c x| ≤ C * (1 - x)⁻¹ ^ 2 := by
  have h := norm_Ederiv_le_tsum (remainderC A c)
    (fun n ↦ by simpa [norm_remainderC] using hC n)
    (z := (x : ℂ)) (by simpa [abs_of_nonneg hx0])
  rw [← ofReal_EderivReal, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0] at h
  rw [tsum_mul_left, tsum_nat_mul_pow_pred_eq hx0 hx1] at h
  exact h

lemma Freal_cube_identity (A : Set ℕ) (c C x : ℝ)
    (hC : ∀ n, |remainder A c n| ≤ C) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Freal A x ^ 3 = c * x / (1 - x) + (1 - x) * Ereal A c x := by
  have h := F_cube_eq_main_add_error_of_uniform_remainder_bound A c C hC
    (z := (x : ℂ)) (by simpa [abs_of_nonneg hx0])
  rw [← ofReal_Freal, ← ofReal_Ereal] at h
  exact_mod_cast h

lemma Freal_differentiated_identity (A : Set ℕ) (c C x : ℝ)
    (hC : ∀ n, |remainder A c n| ≤ C) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    3 * Freal A x ^ 2 * FderivReal A x =
      c / (1 - x) ^ 2 - Ereal A c x + (1 - x) * EderivReal A c x := by
  have h := differentiated_identity_of_uniform_remainder_bound A c C hC
    (z := (x : ℂ)) (by simpa [abs_of_nonneg hx0])
  rw [← ofReal_Freal, ← ofReal_FderivReal, ← ofReal_Ereal,
    ← ofReal_EderivReal] at h
  exact_mod_cast h

lemma radial_F_and_deriv_bounds (A : Set ℕ) (c C : ℝ)
    (hc : 0 < c) (hC : ∀ n, |remainder A c n| ≤ C)
    {t : ℕ} (ht : 2 ≤ t) (hlarge : 16 * C ≤ c * (t : ℝ) ^ 9) :
    let κ := c + C + 1
    Freal A (radius ((t : ℝ) ^ 9) ^ 2) ≤ κ * (t : ℝ) ^ 3 ∧
      c * (t : ℝ) ^ 12 / (24 * κ ^ 2) ≤
        FderivReal A (radius ((t : ℝ) ^ 9) ^ 2) := by
  dsimp
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : 0 < (t : ℝ) := lt_of_lt_of_le (by norm_num) htR
  have hX2 : 2 ≤ (t : ℝ) ^ 9 :=
    htR.trans (le_self_pow₀ (by linarith : (1 : ℝ) ≤ t) (by norm_num))
  have hX1 : 1 < (t : ℝ) ^ 9 := lt_of_lt_of_le (by norm_num) hX2
  have hr0 : 0 ≤ radius ((t : ℝ) ^ 9) :=
    radius_nonneg (le_trans (by norm_num) hX2)
  have hr1 : radius ((t : ℝ) ^ 9) < 1 :=
    radius_lt_one (by positivity)
  have hx0 : 0 ≤ radius ((t : ℝ) ^ 9) ^ 2 := sq_nonneg _
  have hx1 : radius ((t : ℝ) ^ 9) ^ 2 < 1 := by nlinarith
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (remainder A c 0)) (hC 0)
  let x := radius ((t : ℝ) ^ 9) ^ 2
  let EF := Ereal A c x
  let EF' := EderivReal A c x
  let FF := Freal A x
  let FF' := FderivReal A x
  have hE : |EF| ≤ C * (1 - radius ((t : ℝ) ^ 9) ^ 2)⁻¹ := by
    simpa [EF, x] using abs_Ereal_le A c C x hC hx0 hx1
  have hE' : |EF'| ≤ C * (1 - radius ((t : ℝ) ^ 9) ^ 2)⁻¹ ^ 2 := by
    simpa [EF', x] using abs_EderivReal_le A c C x hC hx0 hx1
  have hgf : FF ^ 3 = c * radius ((t : ℝ) ^ 9) ^ 2 *
      (1 - radius ((t : ℝ) ^ 9) ^ 2)⁻¹ +
        (1 - radius ((t : ℝ) ^ 9) ^ 2) * EF := by
    simpa [FF, EF, x, div_eq_mul_inv] using Freal_cube_identity A c C x hC hx0 hx1
  have hdiff : 3 * FF ^ 2 * FF' =
      c * (1 - radius ((t : ℝ) ^ 9) ^ 2)⁻¹ ^ 2 - EF +
        (1 - radius ((t : ℝ) ^ 9) ^ 2) * EF' := by
    simpa [FF, FF', EF, EF', x, div_eq_mul_inv] using
      Freal_differentiated_identity A c C x hC hx0 hx1
  let κ : ℝ := c + C + 1
  have hκ : 0 < κ := by dsimp [κ]; linarith
  have hcube : FF ^ 3 ≤ (c + C) * (t : ℝ) ^ 9 :=
    cube_upper_of_gf hX1 hc.le hC0 hE hgf
  have hcoeff : c + C ≤ κ ^ 3 := by
    have hκ1 : 1 < κ := by dsimp [κ]; linarith
    have hlin : c + C < κ := by dsimp [κ]; linarith
    exact hlin.le.trans (le_self_pow₀ hκ1.le (by norm_num))
  have hcube' : FF ^ 3 ≤ κ ^ 3 * (t : ℝ) ^ 9 := by
    exact hcube.trans (mul_le_mul_of_nonneg_right hcoeff (by positivity))
  have hFF0 : 0 ≤ FF := by exact Freal_nonneg A hx0
  have hFFupper : FF ≤ κ * (t : ℝ) ^ 3 :=
    ninth_power_cube_upper ht0.le hκ.le hFF0 hcube'
  have hnum : c * ((t : ℝ) ^ 9) ^ 2 / 8 ≤ 3 * FF ^ 2 * FF' :=
    differentiated_numerator_lower hX1 hc hC0 hlarge hE hE' hdiff
  have hnum' : c * (t : ℝ) ^ 18 / 8 ≤ 3 * FF ^ 2 * FF' := by
    convert hnum using 1 <;> ring
  have hderiv : c * (t : ℝ) ^ 12 / (24 * κ ^ 2) ≤ FF' :=
    derivative_lower_of_square_upper ht0 hc hκ hFF0 hFFupper hnum'
  exact ⟨hFFupper, hderiv⟩

lemma exists_large_natural_parameter (c C a b : ℝ) (K T : ℕ)
    (hc : 0 < c) (ha : 0 < a) :
    ∃ t : ℕ, T ≤ t ∧ 2 ≤ t ∧
      16 * C ≤ c * (t : ℝ) ^ 9 ∧
      64 * (K : ℝ) ^ 3 * (t : ℝ) ^ 3 ≤ (t : ℝ) ^ 9 ∧
      b / a < (t : ℝ) := by
  let B : ℝ := max (T : ℝ)
    (max 2 (max (16 * C / c) (max (64 * (K : ℝ) ^ 3) (b / a))))
  obtain ⟨t, ht⟩ := exists_nat_gt B
  refine ⟨t, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) ht).le
  · exact_mod_cast (lt_of_le_of_lt
      (le_trans (le_max_left (2 : ℝ) _) (le_max_right (T : ℝ) _)) ht).le
  · have htbound : 16 * C / c < (t : ℝ) := by
      exact lt_of_le_of_lt
        (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) ht
    have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast (show 2 ≤ t from by
      exact_mod_cast (lt_of_le_of_lt
        (le_trans (le_max_left (2 : ℝ) _) (le_max_right (T : ℝ) _)) ht).le)
    have htself : (t : ℝ) ≤ (t : ℝ) ^ 9 :=
      le_self_pow₀ (by linarith) (by norm_num)
    rw [div_lt_iff₀ hc] at htbound
    nlinarith
  · have hKbound : 64 * (K : ℝ) ^ 3 < (t : ℝ) := by
      exact lt_of_le_of_lt
        (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _) (le_max_right _ _)))) ht
    have ht2 : (2 : ℝ) ≤ t := by
      exact lt_of_le_of_lt
        (le_trans (le_max_left (2 : ℝ) _) (le_max_right (T : ℝ) _)) ht |>.le
    have ht6 : (t : ℝ) ≤ (t : ℝ) ^ 6 :=
      le_self_pow₀ (by linarith) (by norm_num)
    have hcoef : 64 * (K : ℝ) ^ 3 ≤ (t : ℝ) ^ 6 := hKbound.le.trans ht6
    have ht3 : 0 ≤ (t : ℝ) ^ 3 := by positivity
    calc
      64 * (K : ℝ) ^ 3 * (t : ℝ) ^ 3 ≤ (t : ℝ) ^ 6 * (t : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right hcoef ht3
      _ = (t : ℝ) ^ 9 := by ring
  · exact lt_of_le_of_lt
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _)))) ht

lemma final_fourier_bounds_contradiction
    {c C κ J : ℝ} {K t : ℕ}
    (hc : 0 < c) (hκ : 0 < κ) (hK : 0 < K) (ht : 2 ≤ t)
    (htlarge :
      (1024 * (c + C) * (K : ℝ) ^ 6 + 2 * C ^ 2 + 32 * (K : ℝ) ^ 3) /
          (c * (K : ℝ) ^ 3 / (4 * κ ^ 2)) < (t : ℝ))
    (hlower : c * (K : ℝ) ^ 3 / (4 * κ ^ 2) * (t : ℝ) ^ 16 ≤ J)
    (hupper : J ≤
      (1024 * (c + C) * (K : ℝ) ^ 6 + 2 * C ^ 2 + 32 * (K : ℝ) ^ 3) *
        (t : ℝ) ^ 15)
    (hC0 : 0 ≤ C) : False := by
  let a := c * (K : ℝ) ^ 3 / (4 * κ ^ 2)
  let b := 1024 * (c + C) * (K : ℝ) ^ 6 + 2 * C ^ 2 + 32 * (K : ℝ) ^ 3
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  exact power_sixteen_not_le_power_fifteen ha hb (by simpa [a, b] using htlarge)
    (by positivity : 0 ≤ (t : ℝ)) (hlower.trans hupper)

lemma half_card_le_sum_of_half_le {s : Finset ℕ} {f : ℕ → ℝ}
    (h : ∀ n ∈ s, (1 / 2 : ℝ) ≤ f n) :
    (s.card : ℝ) / 2 ≤ ∑ n ∈ s, f n := by
  calc
    (s.card : ℝ) / 2 = ∑ _n ∈ s, (1 / 2 : ℝ) := by simp; ring
    _ ≤ ∑ n ∈ s, f n := by
      apply Finset.sum_le_sum
      intro n hn
      exact h n hn

lemma half_nat_le_sum_range_radius_sq
    {X : ℝ} (hX : 1 ≤ X) {s : ℕ} (hbudget : 4 * (s : ℝ) ≤ X) :
    (s : ℝ) / 2 ≤ ∑ j ∈ Finset.range s, (radius X ^ 2) ^ j := by
  have h := half_card_le_sum_of_half_le
    (s := Finset.range s) (f := fun j ↦ (radius X ^ 2) ^ j) (by
      intro j hj
      apply radius_sq_pow_ge_half hX
      have hjs : (j : ℝ) ≤ s := by
        exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hj))
      linarith)
  simpa using h

lemma half_positiveCountingFunction_le_weighted_sum
    (A : Set ℕ) {X : ℝ} (hX : 1 ≤ X) {s : ℕ}
    (hbudget : 4 * (s : ℝ) ≤ X) :
    (positiveCountingFunction A s : ℝ) / 2 ≤
      ∑ a ∈ (Finset.Icc 1 s).filter (fun n ↦ n ∈ A), (radius X ^ 2) ^ a := by
  change ((((Finset.Icc 1 s).filter (fun n ↦ n ∈ A)).card : ℕ) : ℝ) / 2 ≤ _
  apply half_card_le_sum_of_half_le
  intro a ha
  apply radius_sq_pow_ge_half hX
  have has : (a : ℝ) ≤ s := by
    exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2
  linarith

lemma quarter_t_le_half_pred {t : ℕ} (ht : 2 ≤ t) :
    (t : ℝ) / 4 ≤ ((t - 1 : ℕ) : ℝ) / 2 := by
  have htcast : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hsub : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ t)]
    norm_num
  rw [hsub]
  linarith

namespace Hardy

/-- A finite collection of nonnegative diagonal coefficient products is bounded by the
actual circle inner product of two absolutely summable Hardy series. -/
lemma finite_nonneg_diagonal_le_circleAverage
    {u v : ℕ → ℂ}
    (hu : Summable (fun n ↦ ‖u n‖)) (hv : Summable (fun n ↦ ‖v n‖))
    (hdiag : ∀ n, 0 ≤ (u n * conj (v n)).re) (s : Finset ℕ) :
    ∑ n ∈ s, (u n * conj (v n)).re ≤
      Real.circleAverage
        (fun z ↦ (hardySum u z * conj (hardySum v z)).re) 0 1 := by
  rw [infinite_inner_parseval hu hv]
  exact (summable_re_mul_conj hu hv).sum_le_tsum s (fun n _ ↦ hdiag n)

/-- The Cauchy convolution of two `ℓ1` coefficient sequences is again `ℓ1`. -/
lemma summable_norm_convC_of_summable_norm {u v : ℕ → ℂ}
    (hu : Summable (fun n ↦ ‖u n‖)) (hv : Summable (fun n ↦ ‖v n‖)) :
    Summable (fun n ↦ ‖convC u v n‖) := by
  simpa only [convC] using
    summable_norm_sum_mul_antidiagonal_of_summable_norm hu hv

/-- Cauchy multiplication for the boundary values of two `ℓ1` Hardy series. -/
lemma hardySum_convC {u v : ℕ → ℂ}
    (hu : Summable (fun n ↦ ‖u n‖)) (hv : Summable (fun n ↦ ‖v n‖))
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    hardySum (convC u v) z = hardySum u z * hardySum v z := by
  have huz : Summable (fun n : ℕ ↦ ‖u n * z ^ n‖) := by
    apply hu.of_nonneg_of_le (fun n ↦ norm_nonneg _) fun n ↦ ?_
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)
  have hvz : Summable (fun n : ℕ ↦ ‖v n * z ^ n‖) := by
    apply hv.of_nonneg_of_le (fun n ↦ norm_nonneg _) fun n ↦ ?_
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)
  symm
  simpa only [hardySum, E] using tsum_mul_tsum_eq_E_conv huz hvz

lemma hardySum_const_mul (c : ℂ) {u : ℕ → ℂ}
    (hu : Summable (fun n ↦ ‖u n‖)) (z : ℂ) :
    hardySum (fun n ↦ c * u n) z = c * hardySum u z := by
  unfold hardySum
  calc
    ∑' n, (c * u n) * z ^ n = ∑' n, c * (u n * z ^ n) := by
      apply tsum_congr
      intro n
      ring
    _ = c * ∑' n, u n * z ^ n := tsum_mul_left

end Hardy

namespace FourierLower

open scoped Polynomial

noncomputable def radialFCoeff (A : Set ℕ) (r : ℝ) (n : ℕ) : ℂ :=
  indicatorC A n * (r : ℂ) ^ n

noncomputable def radialDirichletCoeff (m : ℕ) (r : ℝ) (n : ℕ) : ℂ :=
  if n < m then (r : ℂ) ^ n else 0

noncomputable def uCoeff (A : Set ℕ) (r : ℝ) (m : ℕ) : ℕ → ℂ :=
  fun n ↦ 3 * convC (convC (radialFCoeff A r)
    (Upper.ederivHardyCoeff (indicatorC A) r)) (radialDirichletCoeff m r) n

noncomputable def vCoeff (A : Set ℕ) (r : ℝ) (m : ℕ) : ℕ → ℂ :=
  convC (radialFCoeff A r) (radialDirichletCoeff m r)

lemma realCast_pow_re_im (r : ℝ) : ∀ n : ℕ,
    (((r : ℂ) ^ n).re = r ^ n ∧ ((r : ℂ) ^ n).im = 0) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      simp only [Complex.mul_re, Complex.mul_im, ih.1, ih.2, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
      exact ⟨True.intro, True.intro⟩

lemma realCast_pow_re (r : ℝ) (n : ℕ) : ((r : ℂ) ^ n).re = r ^ n :=
  (realCast_pow_re_im r n).1

lemma realCast_pow_im (r : ℝ) (n : ℕ) : ((r : ℂ) ^ n).im = 0 :=
  (realCast_pow_re_im r n).2

lemma indicatorC_im (A : Set ℕ) (n : ℕ) : (indicatorC A n).im = 0 := by
  classical
  by_cases hn : n ∈ A <;> simp [indicatorC, hn]

lemma indicatorC_re_nonneg (A : Set ℕ) (n : ℕ) : 0 ≤ (indicatorC A n).re := by
  classical
  by_cases hn : n ∈ A <;> simp [indicatorC, hn]

lemma radialFCoeff_im (A : Set ℕ) (r : ℝ) (n : ℕ) :
    (radialFCoeff A r n).im = 0 := by
  classical
  by_cases hn : n ∈ A
  · simp only [radialFCoeff, indicatorC, Set.indicator_of_mem hn, one_mul]
    exact realCast_pow_im r n
  · simp [radialFCoeff, indicatorC, hn]

lemma radialFCoeff_re_nonneg (A : Set ℕ) {r : ℝ} (hr0 : 0 ≤ r) (n : ℕ) :
    0 ≤ (radialFCoeff A r n).re := by
  classical
  by_cases hn : n ∈ A
  · simp only [radialFCoeff, indicatorC, Set.indicator_of_mem hn, one_mul]
    rw [realCast_pow_re]
    exact pow_nonneg hr0 n
  · simp [radialFCoeff, indicatorC, hn]

lemma ederivHardyCoeff_indicator_im (A : Set ℕ) (r : ℝ) (n : ℕ) :
    (Upper.ederivHardyCoeff (indicatorC A) r n).im = 0 := by
  classical
  by_cases hn : n + 1 ∈ A
  · simp only [Upper.ederivHardyCoeff, indicatorC, Set.indicator_of_mem hn, mul_one]
    rw [Complex.mul_im, realCast_pow_im]
    simp
  · simp [Upper.ederivHardyCoeff, indicatorC, hn]

lemma ederivHardyCoeff_indicator_re_nonneg
    (A : Set ℕ) {r : ℝ} (hr0 : 0 ≤ r) (n : ℕ) :
    0 ≤ (Upper.ederivHardyCoeff (indicatorC A) r n).re := by
  classical
  by_cases hn : n + 1 ∈ A
  · simp only [Upper.ederivHardyCoeff, indicatorC, Set.indicator_of_mem hn, mul_one]
    rw [Complex.mul_re, realCast_pow_re]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr0 n)
  · simp [Upper.ederivHardyCoeff, indicatorC, hn]

lemma radialDirichletCoeff_im (m : ℕ) (r : ℝ) (n : ℕ) :
    (radialDirichletCoeff m r n).im = 0 := by
  by_cases hn : n < m
  · rw [radialDirichletCoeff, if_pos hn]
    exact realCast_pow_im r n
  · simp [radialDirichletCoeff, hn]

lemma radialDirichletCoeff_re_nonneg (m : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (n : ℕ) :
    0 ≤ (radialDirichletCoeff m r n).re := by
  by_cases hn : n < m
  · rw [radialDirichletCoeff, if_pos hn, realCast_pow_re]
    exact pow_nonneg hr0 n
  · simp [radialDirichletCoeff, hn]

lemma convC_im_of_im_zero {f g : ℕ → ℂ}
    (hf : ∀ n, (f n).im = 0) (hg : ∀ n, (g n).im = 0) (n : ℕ) :
    (convC f g n).im = 0 := by
  simp [convC, Complex.mul_im, hf, hg]

lemma convC_re_nonneg_of_re_nonneg_of_im_zero {f g : ℕ → ℂ}
    (hf0 : ∀ n, 0 ≤ (f n).re) (hg0 : ∀ n, 0 ≤ (g n).re)
    (hf : ∀ n, (f n).im = 0) (hg : ∀ n, (g n).im = 0) (n : ℕ) :
    0 ≤ (convC f g n).re := by
  rw [convC, Complex.re_sum]
  apply Finset.sum_nonneg
  intro kl hkl
  simp only [Complex.mul_re, hf, hg, zero_mul, sub_zero]
  exact mul_nonneg (hf0 _) (hg0 _)

lemma uCoeff_im (A : Set ℕ) (r : ℝ) (m n : ℕ) :
    (uCoeff A r m n).im = 0 := by
  have hFD := convC_im_of_im_zero (radialFCoeff_im A r)
    (ederivHardyCoeff_indicator_im A r)
  have hFDK := convC_im_of_im_zero hFD (radialDirichletCoeff_im m r)
  simp [uCoeff, Complex.mul_im, hFDK]

lemma vCoeff_im (A : Set ℕ) (r : ℝ) (m n : ℕ) :
    (vCoeff A r m n).im = 0 := by
  exact convC_im_of_im_zero (radialFCoeff_im A r)
    (radialDirichletCoeff_im m r) n

lemma uCoeff_re_nonneg (A : Set ℕ) {r : ℝ} (m : ℕ) (hr0 : 0 ≤ r) (n : ℕ) :
    0 ≤ (uCoeff A r m n).re := by
  have hFim := radialFCoeff_im A r
  have hDim := ederivHardyCoeff_indicator_im A r
  have hKim := radialDirichletCoeff_im m r
  have hFD0 := convC_re_nonneg_of_re_nonneg_of_im_zero
    (radialFCoeff_re_nonneg A hr0) (ederivHardyCoeff_indicator_re_nonneg A hr0)
    hFim hDim
  have hFDim := convC_im_of_im_zero hFim hDim
  have hFDK0 := convC_re_nonneg_of_re_nonneg_of_im_zero hFD0
    (radialDirichletCoeff_re_nonneg m hr0) hFDim hKim n
  rw [uCoeff, Complex.mul_re]
  norm_num [hFDK0, convC_im_of_im_zero hFDim hKim n]

lemma vCoeff_re_nonneg (A : Set ℕ) {r : ℝ} (m : ℕ) (hr0 : 0 ≤ r) (n : ℕ) :
    0 ≤ (vCoeff A r m n).re := by
  exact convC_re_nonneg_of_re_nonneg_of_im_zero
    (radialFCoeff_re_nonneg A hr0) (radialDirichletCoeff_re_nonneg m hr0)
    (radialFCoeff_im A r) (radialDirichletCoeff_im m r) n

lemma summable_norm_radialFCoeff (A : Set ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n ↦ ‖radialFCoeff A r n‖) := by
  have hr : ‖(r : ℂ)‖ < 1 := by simpa [Complex.norm_real, abs_of_nonneg hr0] using hr1
  simpa only [radialFCoeff] using summable_norm_indicator_mul_pow A hr

lemma summable_norm_radialDirichletCoeff (m : ℕ) (r : ℝ) :
    Summable (fun n ↦ ‖radialDirichletCoeff m r n‖) := by
  apply summable_of_ne_finset_zero (s := Finset.range m)
  intro n hn
  rw [radialDirichletCoeff, if_neg]
  · simp
  · simpa only [Finset.mem_range] using hn

lemma summable_norm_uCoeff (A : Set ℕ) {r : ℝ} (m : ℕ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n ↦ ‖uCoeff A r m n‖) := by
  have hF := summable_norm_radialFCoeff A hr0 hr1
  have hD := Upper.summable_norm_ederivHardyCoeff (indicatorC A)
    (C := 1) (r := r) (by norm_num) (norm_indicator_le_one A) hr0 hr1
  have hK := summable_norm_radialDirichletCoeff m r
  have hconv := Hardy.summable_norm_convC_of_summable_norm
    (Hardy.summable_norm_convC_of_summable_norm hF hD) hK
  simpa [uCoeff] using hconv.mul_left 3

lemma summable_norm_vCoeff (A : Set ℕ) {r : ℝ} (m : ℕ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n ↦ ‖vCoeff A r m n‖) :=
  Hardy.summable_norm_convC_of_summable_norm
    (summable_norm_radialFCoeff A hr0 hr1)
    (summable_norm_radialDirichletCoeff m r)

lemma hardySum_radialFCoeff (A : Set ℕ) (r : ℝ) (z : ℂ) :
    Hardy.hardySum (radialFCoeff A r) z = F A ((r : ℂ) * z) := by
  unfold Hardy.hardySum radialFCoeff F
  apply tsum_congr
  intro n
  rw [mul_pow]
  ring

lemma hardySum_radialDirichletCoeff (m : ℕ) (r : ℝ) (z : ℂ) :
    Hardy.hardySum (radialDirichletCoeff m r) z =
      (Upper.dirichletPolynomial m).eval ((r : ℂ) * z) := by
  unfold Hardy.hardySum
  rw [tsum_eq_sum (s := Finset.range m)]
  · calc
      ∑ x ∈ Finset.range m, radialDirichletCoeff m r x * z ^ x =
          ∑ x ∈ Finset.range m, (r : ℂ) ^ x * z ^ x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [radialDirichletCoeff, if_pos (Finset.mem_range.mp hx)]
      _ = (Upper.dirichletPolynomial m).eval ((r : ℂ) * z) := by
        simp [Upper.dirichletPolynomial, Polynomial.eval_finsetSum, mul_pow]
  · intro n hn
    rw [radialDirichletCoeff, if_neg]
    · simp
    · simpa only [Finset.mem_range] using hn

lemma hardySum_ederivHardyCoeff (A : Set ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Hardy.hardySum (Upper.ederivHardyCoeff (indicatorC A) r) z =
      Fderiv A ((r : ℂ) * z) := by
  have hrnorm : ‖(r : ℂ)‖ = r := by simp [Complex.norm_real, abs_of_nonneg hr0]
  have hrz : ‖(r : ℂ) * z‖ < 1 := by
    rw [norm_mul, hrnorm]
    calc
      r * ‖z‖ ≤ r * 1 := mul_le_mul_of_nonneg_left hz hr0
      _ < 1 := by simpa using hr1
  let f : ℕ → ℂ := fun n ↦
    (n : ℂ) * indicatorC A n * ((r : ℂ) * z) ^ (n - 1)
  have hf : Summable f := by
    simpa only [f] using summable_indicator_deriv A hrz
  have hshift := hf.sum_add_tsum_nat_add 1
  have htail :
      (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * indicatorC A (n + 1) *
        ((r : ℂ) * z) ^ n) = Fderiv A ((r : ℂ) * z) := by
    simpa only [f, Finset.sum_range_one, Nat.cast_zero, zero_mul, zero_add,
      Nat.add_sub_cancel, Fderiv] using hshift
  rw [← htail]
  unfold Hardy.hardySum Upper.ederivHardyCoeff
  apply tsum_congr
  intro n
  rw [mul_pow]
  ring

lemma hardySum_uCoeff (A : Set ℕ) {r : ℝ} (m : ℕ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Hardy.hardySum (uCoeff A r m) z =
      3 * F A ((r : ℂ) * z) * Fderiv A ((r : ℂ) * z) *
        (Upper.dirichletPolynomial m).eval ((r : ℂ) * z) := by
  have hF := summable_norm_radialFCoeff A hr0 hr1
  have hD := Upper.summable_norm_ederivHardyCoeff (indicatorC A)
    (C := 1) (r := r) (by norm_num) (norm_indicator_le_one A) hr0 hr1
  have hK := summable_norm_radialDirichletCoeff m r
  have hFD := Hardy.summable_norm_convC_of_summable_norm hF hD
  have hFDK := Hardy.summable_norm_convC_of_summable_norm hFD hK
  change Hardy.hardySum (fun n ↦ 3 *
    convC (convC (radialFCoeff A r) (Upper.ederivHardyCoeff (indicatorC A) r))
      (radialDirichletCoeff m r) n) z = _
  rw [Hardy.hardySum_const_mul 3 hFDK]
  rw [Hardy.hardySum_convC hFD hK hz, Hardy.hardySum_convC hF hD hz]
  rw [hardySum_radialFCoeff, hardySum_ederivHardyCoeff A hr0 hr1 hz,
    hardySum_radialDirichletCoeff]
  ring

lemma hardySum_vCoeff (A : Set ℕ) {r : ℝ} (m : ℕ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Hardy.hardySum (vCoeff A r m) z =
      F A ((r : ℂ) * z) *
        (Upper.dirichletPolynomial m).eval ((r : ℂ) * z) := by
  have hF := summable_norm_radialFCoeff A hr0 hr1
  have hK := summable_norm_radialDirichletCoeff m r
  rw [vCoeff, Hardy.hardySum_convC hF hK hz,
    hardySum_radialFCoeff, hardySum_radialDirichletCoeff]

noncomputable def kernelAverage (A : Set ℕ) (r : ℝ) (m : ℕ) : ℝ :=
  Real.circleAverage (fun z : ℂ ↦
    3 * ‖F A ((r : ℂ) * z)‖ ^ 2 * ‖Fderiv A ((r : ℂ) * z)‖ *
      ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) 0 1

lemma circleAverage_hardy_inner_le_kernelAverage
    (A : Set ℕ) {r : ℝ} (m : ℕ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage (fun z ↦
        (Hardy.hardySum (uCoeff A r m) z *
          conj (Hardy.hardySum (vCoeff A r m) z)).re) 0 1 ≤
      kernelAverage A r m := by
  let s : Set ℂ := Metric.sphere 0 1
  have hu := summable_norm_uCoeff A m hr0 hr1
  have hv := summable_norm_vCoeff A m hr0 hr1
  have hUcont : ContinuousOn (Hardy.hardySum (uCoeff A r m)) s :=
    (Hardy.continuousOn_hardySum hu).mono Metric.sphere_subset_closedBall
  have hVcont : ContinuousOn (Hardy.hardySum (vCoeff A r m)) s :=
    (Hardy.continuousOn_hardySum hv).mono Metric.sphere_subset_closedBall
  have hleft : CircleIntegrable (fun z ↦
      (Hardy.hardySum (uCoeff A r m) z *
        conj (Hardy.hardySum (vCoeff A r m) z)).re) 0 1 := by
    apply ContinuousOn.circleIntegrable'
    have hVconj : ContinuousOn
        (fun z ↦ conj (Hardy.hardySum (vCoeff A r m) z)) s :=
      Complex.continuous_conj.comp_continuousOn hVcont
    have hcont := Complex.continuous_re.comp_continuousOn (hUcont.mul hVconj)
    have hcont' : ContinuousOn (fun z ↦
        (Hardy.hardySum (uCoeff A r m) z *
          conj (Hardy.hardySum (vCoeff A r m) z)).re) s := by
      refine hcont.congr ?_
      intro z hz
      rfl
    simpa [s] using hcont'
  have hFbase := summable_norm_radialFCoeff A hr0 hr1
  have hDbase := Upper.summable_norm_ederivHardyCoeff (indicatorC A)
    (C := 1) (r := r) (by norm_num) (norm_indicator_le_one A) hr0 hr1
  have hKbase := summable_norm_radialDirichletCoeff m r
  have hFcont : ContinuousOn (fun z ↦ F A ((r : ℂ) * z)) s := by
    refine ((Hardy.continuousOn_hardySum hFbase).mono
      Metric.sphere_subset_closedBall).congr ?_
    intro z hz
    exact (hardySum_radialFCoeff A r z).symm
  have hDcont : ContinuousOn (fun z ↦ Fderiv A ((r : ℂ) * z)) s := by
    refine ((Hardy.continuousOn_hardySum hDbase).mono
      Metric.sphere_subset_closedBall).congr ?_
    intro z hz
    have hznorm : ‖z‖ = 1 := by simpa [s, Metric.mem_sphere] using hz
    exact (hardySum_ederivHardyCoeff A hr0 hr1 hznorm.le).symm
  have hKcont : ContinuousOn (fun z ↦
      (Upper.dirichletPolynomial m).eval ((r : ℂ) * z)) s := by
    fun_prop
  have hright : CircleIntegrable (fun z : ℂ ↦
      3 * ‖F A ((r : ℂ) * z)‖ ^ 2 * ‖Fderiv A ((r : ℂ) * z)‖ *
        ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) 0 1 := by
    apply ContinuousOn.circleIntegrable'
    have hc : ContinuousOn (fun _ : ℂ ↦ (3 : ℝ)) s := continuousOn_const
    have hcont := (((hc.mul (hFcont.norm.pow 2)).mul hDcont.norm).mul
      (hKcont.norm.pow 2))
    have hcont' : ContinuousOn (fun z : ℂ ↦
        3 * ‖F A ((r : ℂ) * z)‖ ^ 2 * ‖Fderiv A ((r : ℂ) * z)‖ *
          ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) s := by
      refine hcont.congr ?_
      intro z hz
      rfl
    simpa [s] using hcont'
  apply Real.circleAverage_mono hleft hright
  intro z hz
  have hznorm : ‖z‖ ≤ 1 := by
    have : ‖z‖ = 1 := by simpa [Metric.mem_sphere] using hz
    linarith
  rw [hardySum_uCoeff A m hr0 hr1 hznorm,
    hardySum_vCoeff A m hr0 hr1 hznorm]
  calc
    ((3 * F A ((r : ℂ) * z) * Fderiv A ((r : ℂ) * z) *
        (Upper.dirichletPolynomial m).eval ((r : ℂ) * z)) *
      conj (F A ((r : ℂ) * z) *
        (Upper.dirichletPolynomial m).eval ((r : ℂ) * z))).re ≤
      ‖(3 * F A ((r : ℂ) * z) * Fderiv A ((r : ℂ) * z) *
        (Upper.dirichletPolynomial m).eval ((r : ℂ) * z)) *
      conj (F A ((r : ℂ) * z) *
        (Upper.dirichletPolynomial m).eval ((r : ℂ) * z))‖ := Complex.re_le_norm _
    _ = 3 * ‖F A ((r : ℂ) * z)‖ ^ 2 * ‖Fderiv A ((r : ℂ) * z)‖ *
        ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2 := by
      simp only [norm_mul, norm_conj]
      rw [show ‖(3 : ℂ)‖ = (3 : ℝ) by norm_num]
      ring

/-- A finite nonnegative polynomial coefficient minorant passes to the actual
infinite Hardy inner product.  This is the precise finite-truncation bridge:
no limiting interchange remains in clients of this lemma. -/
lemma circleAverage_poly_le_hardy_of_coeff_minorant
    (P Q : ℝ[X]) {u v : ℕ → ℂ}
    (hu : Summable (fun n ↦ ‖u n‖)) (hv : Summable (fun n ↦ ‖v n‖))
    (hP0 : ∀ n, 0 ≤ P.coeff n) (hQ0 : ∀ n, 0 ≤ Q.coeff n)
    (huim : ∀ n, (u n).im = 0) (hvim : ∀ n, (v n).im = 0)
    (hu0 : ∀ n, 0 ≤ (u n).re) (hv0 : ∀ n, 0 ≤ (v n).re)
    (hPu : ∀ n, P.coeff n ≤ (u n).re)
    (hQv : ∀ n, Q.coeff n ≤ (v n).re) :
    Real.circleAverage (fun z : ℂ ↦
        (((P.map Complex.ofRealHom).eval z) *
          conj ((Q.map Complex.ofRealHom).eval z)).re) 0 1 ≤
      Real.circleAverage (fun z ↦
        (Hardy.hardySum u z * conj (Hardy.hardySum v z)).re) 0 1 := by
  let s := (P.map Complex.ofRealHom).support ∪ (Q.map Complex.ofRealHom).support
  have hdiag (n : ℕ) :
      (u n * conj (v n)).re = (u n).re * (v n).re := by
    simp [Complex.mul_re, huim n, hvim n]
  rw [circleAverage_re_eval_mul_conj_eval]
  have hcoeff (n : ℕ) :
      (((P.map Complex.ofRealHom).coeff n) *
          conj ((Q.map Complex.ofRealHom).coeff n)).re =
        P.coeff n * Q.coeff n := by simp
  simp_rw [hcoeff]
  calc
    ∑ n ∈ s, P.coeff n * Q.coeff n ≤
        ∑ n ∈ s, (u n).re * (v n).re := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul (hPu n) (hQv n) (hQ0 n) (hu0 n)
    _ = ∑ n ∈ s, (u n * conj (v n)).re := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hdiag]
    _ ≤ Real.circleAverage (fun z ↦
        (Hardy.hardySum u z * conj (Hardy.hardySum v z)).re) 0 1 :=
      Hardy.finite_nonneg_diagonal_le_circleAverage hu hv
        (fun n ↦ by rw [hdiag]; exact mul_nonneg (hu0 n) (hv0 n)) s

/-- The selected zero-frequency graph `b=d`, `ell=a-1+j`, followed by the
finite-to-infinite Hardy bridge.  The two minorant hypotheses are exactly the
finite-truncation obligations for a concrete coefficient model. -/
lemma selected_b_eq_d_le_hardy
    (aFull dFull jFull bFull ellFull : Finset ℕ)
    (aSel dSel jSel : Finset ℕ)
    (wa wd wj wb wl : ℕ → ℝ)
    {u v : ℕ → ℂ}
    (haSub : aSel ⊆ aFull) (hdSub : dSel ⊆ dFull) (hjSub : jSel ⊆ jFull)
    (hdB : dSel ⊆ bFull)
    (hell : ∀ a ∈ aSel, ∀ j ∈ jSel, a - 1 + j ∈ ellFull)
    (haPos : ∀ a ∈ aSel, 1 ≤ a) (hdPos : ∀ d ∈ dSel, 1 ≤ d)
    (hwa : ∀ a ∈ aFull, 0 ≤ wa a) (hwd : ∀ d ∈ dFull, 0 ≤ wd d)
    (hwj : ∀ j ∈ jFull, 0 ≤ wj j) (hwb : ∀ b ∈ bFull, 0 ≤ wb b)
    (hwl : ∀ l ∈ ellFull, 0 ≤ wl l)
    (hu : Summable (fun n ↦ ‖u n‖)) (hv : Summable (fun n ↦ ‖v n‖))
    (huim : ∀ n, (u n).im = 0) (hvim : ∀ n, (v n).im = 0)
    (hu0 : ∀ n, 0 ≤ (u n).re) (hv0 : ∀ n, 0 ≤ (v n).re)
    (hPu : ∀ n,
      (monomialSum ((aFull.product dFull).product jFull)
        (fun x ↦ x.1.1 + (x.1.2 - 1) + x.2)
        (fun x ↦ 3 * wa x.1.1 * wd x.1.2 * wj x.2)).coeff n ≤ (u n).re)
    (hQv : ∀ n,
      (monomialSum (bFull.product ellFull)
        (fun x ↦ x.1 + x.2) (fun x ↦ wb x.1 * wl x.2)).coeff n ≤ (v n).re) :
    ∑ x ∈ (aSel.product dSel).product jSel,
        (3 * wa x.1.1 * wd x.1.2 * wj x.2) *
          (wb x.1.2 * wl (x.1.1 - 1 + x.2)) ≤
      Real.circleAverage (fun z ↦
        (Hardy.hardySum u z * conj (Hardy.hardySum v z)).re) 0 1 := by
  let P := monomialSum ((aFull.product dFull).product jFull)
    (fun x ↦ x.1.1 + (x.1.2 - 1) + x.2)
    (fun x ↦ 3 * wa x.1.1 * wd x.1.2 * wj x.2)
  let Q := monomialSum (bFull.product ellFull)
    (fun x ↦ x.1 + x.2) (fun x ↦ wb x.1 * wl x.2)
  have hP0 : ∀ n, 0 ≤ P.coeff n := by
    intro n
    rw [show P = monomialSum ((aFull.product dFull).product jFull)
      (fun x ↦ x.1.1 + (x.1.2 - 1) + x.2)
      (fun x ↦ 3 * wa x.1.1 * wd x.1.2 * wj x.2) from rfl,
      coeff_monomialSum]
    apply Finset.sum_nonneg
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hx, -⟩
    rcases Finset.mem_product.mp hx with ⟨had, hj⟩
    rcases Finset.mem_product.mp had with ⟨ha, hd⟩
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hwa _ ha))
      (hwd _ hd)) (hwj _ hj)
  have hQ0 : ∀ n, 0 ≤ Q.coeff n := by
    intro n
    rw [show Q = monomialSum (bFull.product ellFull)
      (fun x ↦ x.1 + x.2) (fun x ↦ wb x.1 * wl x.2) from rfl,
      coeff_monomialSum]
    apply Finset.sum_nonneg
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hx, -⟩
    rcases Finset.mem_product.mp hx with ⟨hb, hl⟩
    exact mul_nonneg (hwb _ hb) (hwl _ hl)
  have hfinite := erdosFuchs_selected_b_eq_d
    aFull dFull jFull bFull ellFull aSel dSel jSel wa wd wj wb wl
    haSub hdSub hjSub hdB hell haPos hdPos hwa hwd hwj hwb hwl
  exact hfinite.trans (circleAverage_poly_le_hardy_of_coeff_minorant P Q hu hv
    hP0 hQ0 huim hvim hu0 hv0 (by simpa only [P] using hPu)
      (by simpa only [Q] using hQv))

/-- Packaged lower bound for the actual infinite kernel integral.  Thus the
only remaining obligations in a concrete choice of truncation sets are the
two transparent coefficient-minorant inequalities. -/
lemma selected_b_eq_d_le_kernelAverage
    (A : Set ℕ) {r : ℝ} (m : ℕ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (aFull dFull jFull bFull ellFull : Finset ℕ)
    (aSel dSel jSel : Finset ℕ)
    (wa wd wj wb wl : ℕ → ℝ)
    (haSub : aSel ⊆ aFull) (hdSub : dSel ⊆ dFull) (hjSub : jSel ⊆ jFull)
    (hdB : dSel ⊆ bFull)
    (hell : ∀ a ∈ aSel, ∀ j ∈ jSel, a - 1 + j ∈ ellFull)
    (haPos : ∀ a ∈ aSel, 1 ≤ a) (hdPos : ∀ d ∈ dSel, 1 ≤ d)
    (hwa : ∀ a ∈ aFull, 0 ≤ wa a) (hwd : ∀ d ∈ dFull, 0 ≤ wd d)
    (hwj : ∀ j ∈ jFull, 0 ≤ wj j) (hwb : ∀ b ∈ bFull, 0 ≤ wb b)
    (hwl : ∀ l ∈ ellFull, 0 ≤ wl l)
    (hPu : ∀ n,
      (monomialSum ((aFull.product dFull).product jFull)
        (fun x ↦ x.1.1 + (x.1.2 - 1) + x.2)
        (fun x ↦ 3 * wa x.1.1 * wd x.1.2 * wj x.2)).coeff n ≤
          (uCoeff A r m n).re)
    (hQv : ∀ n,
      (monomialSum (bFull.product ellFull)
        (fun x ↦ x.1 + x.2) (fun x ↦ wb x.1 * wl x.2)).coeff n ≤
          (vCoeff A r m n).re) :
    ∑ x ∈ (aSel.product dSel).product jSel,
        (3 * wa x.1.1 * wd x.1.2 * wj x.2) *
          (wb x.1.2 * wl (x.1.1 - 1 + x.2)) ≤ kernelAverage A r m := by
  have hhardy := selected_b_eq_d_le_hardy
    aFull dFull jFull bFull ellFull aSel dSel jSel wa wd wj wb wl
    haSub hdSub hjSub hdB hell haPos hdPos hwa hwd hwj hwb hwl
    (summable_norm_uCoeff A m hr0 hr1) (summable_norm_vCoeff A m hr0 hr1)
    (uCoeff_im A r m) (vCoeff_im A r m)
    (uCoeff_re_nonneg A m hr0) (vCoeff_re_nonneg A m hr0) hPu hQv
  exact hhardy.trans (circleAverage_hardy_inner_le_kernelAverage A m hr0 hr1)

end FourierLower

namespace KernelUpper

open Complex Filter MeasureTheory Polynomial Real Set
open scoped ComplexConjugate

noncomputable def kernelAverage (A : Set ℕ) (r : ℝ) (m : ℕ) : ℝ :=
  circleAverage (fun z : ℂ ↦
    3 * ‖F A ((r : ℂ) * z)‖ ^ 2 * ‖Fderiv A ((r : ℂ) * z)‖ *
      ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) 0 1

noncomputable def eHardyCoeff (P : ℕ → ℂ) (r : ℝ) (n : ℕ) : ℂ :=
  P n * (r : ℂ) ^ n

lemma summable_norm_eHardyCoeff
    (P : ℕ → ℂ) {C r : ℝ} (hP : ∀ n, ‖P n‖ ≤ C)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n ↦ ‖eHardyCoeff P r n‖) := by
  have hrabs : |r| < 1 := by simpa [abs_of_nonneg hr0] using hr1
  have hC0 : 0 ≤ C := (norm_nonneg (P 0)).trans (hP 0)
  have hmajor : Summable (fun n : ℕ ↦ C * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left C
  apply hmajor.of_nonneg_of_le
  · intro n
    positivity
  · intro n
    rw [eHardyCoeff, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
    exact mul_le_mul_of_nonneg_right (hP n) (pow_nonneg hr0 n)

lemma E_eq_hardySum (P : ℕ → ℂ) (r : ℝ) (z : ℂ) :
    E P ((r : ℂ) * z) = Hardy.hardySum (eHardyCoeff P r) z := by
  apply tsum_congr
  intro n
  simp only [E, Hardy.hardySum, eHardyCoeff]
  rw [mul_pow]
  ring

lemma Ederiv_eq_hardySum (P : ℕ → ℂ) {C r : ℝ}
    (hP : ∀ n, ‖P n‖ ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    Ederiv P ((r : ℂ) * z) =
      Hardy.hardySum (Upper.ederivHardyCoeff P r) z := by
  have hs : Summable (fun n : ℕ ↦
      (n : ℂ) * P n * ((r : ℂ) * z) ^ (n - 1)) := by
    have hrz : ‖(r : ℂ) * z‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      calc
        r * ‖z‖ ≤ r * 1 := mul_le_mul_of_nonneg_left hz hr0
        _ < 1 := by simpa using hr1
    apply (summable_nat_mul_pow_pred (norm_nonneg ((r : ℂ) * z)) hrz).mul_left C
      |>.of_norm_bounded
    intro n
    rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow]
    calc
      (n : ℝ) * ‖P n‖ * ‖(r : ℂ) * z‖ ^ (n - 1) ≤
          (n : ℝ) * C * ‖(r : ℂ) * z‖ ^ (n - 1) := by
        gcongr
        exact hP n
      _ = C * ((n : ℝ) * ‖(r : ℂ) * z‖ ^ (n - 1)) := by ring
  rw [Ederiv]
  have hshift := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, zero_add] at hshift
  rw [← hshift]
  apply tsum_congr
  intro n
  simp only [Hardy.hardySum, Upper.ederivHardyCoeff]
  push_cast
  rw [mul_pow]
  ring

lemma norm_dirichlet_eval_le (m : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖(Upper.dirichletPolynomial m).eval w‖ ≤ m := by
  rw [Upper.dirichletPolynomial]
  simp only [eval_finsetSum, eval_pow, eval_X]
  calc
    ‖∑ x ∈ Finset.range m, w ^ x‖ ≤ ∑ x ∈ Finset.range m, ‖w ^ x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _x ∈ Finset.range m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg w) hw
    _ = m := by simp

lemma dirichlet_radial_circleAverage_sq_le
    (m : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    circleAverage (fun z : ℂ ↦
      ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) 0 1 ≤ m := by
  rw [← Upper.radialPolynomial_parseval (r : ℂ) (Upper.dirichletPolynomial m)]
  let q := Upper.radialPolynomial (r : ℂ) (Upper.dirichletPolynomial m)
  have hsupp : q.support ⊆ Finset.range m := by
    intro n hn
    have hn0 : q.coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
    by_contra hnm
    have hnot : ¬ n < m := by simpa using hnm
    apply hn0
    rw [Upper.radialPolynomial_coeff, Upper.dirichletPolynomial_coeff, if_neg hnot]
    simp
  calc
    ∑ n ∈ q.support,
        ‖(Upper.dirichletPolynomial m).coeff n * (r : ℂ) ^ n‖ ^ 2 ≤
        ∑ n ∈ Finset.range m,
          ‖(Upper.dirichletPolynomial m).coeff n * (r : ℂ) ^ n‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsupp
      intro n hn hnot
      positivity
    _ ≤
        ∑ _n ∈ Finset.range m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnm : n < m := Finset.mem_range.mp hn
      rw [Upper.dirichletPolynomial_coeff, if_pos hnm, one_mul, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      exact (sq_le_one_iff₀ (pow_nonneg hr0 n)).2 (pow_le_one₀ hr0 hr1)
    _ = m := by simp

lemma continuousOn_reciprocal_one_sub_mul
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn (fun z : ℂ ↦ (1 - (r : ℂ) * z)⁻¹) (Metric.sphere 0 1) := by
  apply ContinuousOn.inv₀
  · fun_prop
  · intro z hz hzero
    have hznorm : ‖z‖ = 1 := by simpa [Metric.mem_sphere] using hz
    have heq : (r : ℂ) * z = 1 := (sub_eq_zero.mp hzero).symm
    have := congrArg norm heq
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
      hznorm, mul_one, norm_one] at this
    linarith

lemma circleAverage_main_le
    {c r : ℝ} (m : ℕ) (hc : 0 ≤ c) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    circleAverage (fun z : ℂ ↦
      c * ‖(1 - (r : ℂ) * z)⁻¹‖ ^ 2 *
        ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) 0 1 ≤
      c * m ^ 2 * (1 - r ^ 2)⁻¹ := by
  have hrec := continuousOn_reciprocal_one_sub_mul hr0 hr1
  have hleft : CircleIntegrable (fun z : ℂ ↦
      c * ‖(1 - (r : ℂ) * z)⁻¹‖ ^ 2 *
        ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) 0 1 := by
    apply ContinuousOn.circleIntegrable'
    have hD : Continuous (fun z : ℂ ↦
        ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) := by
      fun_prop
    have hcont := ((hrec.norm.pow 2).const_mul c).mul hD.continuousOn
    have hcont' : ContinuousOn (fun z : ℂ ↦
        c * ‖(1 - (r : ℂ) * z)⁻¹‖ ^ 2 *
          ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2)
        (Metric.sphere 0 1) := by
      apply hcont.congr
      intro z hz
      rfl
    simpa only [abs_one] using hcont'
  have hright : CircleIntegrable (fun z : ℂ ↦
      (c * (m : ℝ) ^ 2) * ‖(1 - (r : ℂ) * z)⁻¹‖ ^ 2) 0 1 := by
    apply ContinuousOn.circleIntegrable'
    simpa only [abs_one, Pi.pow_apply] using
      (hrec.norm.pow 2).const_mul (c * (m : ℝ) ^ 2)
  calc
    circleAverage (fun z : ℂ ↦
        c * ‖(1 - (r : ℂ) * z)⁻¹‖ ^ 2 *
          ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) 0 1 ≤
        circleAverage (fun z : ℂ ↦
          (c * (m : ℝ) ^ 2) * ‖(1 - (r : ℂ) * z)⁻¹‖ ^ 2) 0 1 := by
      apply circleAverage_mono hleft hright
      intro z hz
      have hznorm : ‖z‖ = 1 := by simpa [Metric.mem_sphere] using hz
      have hw : ‖(r : ℂ) * z‖ ≤ 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, hznorm,
          mul_one]
        exact hr1.le
      have hD := norm_dirichlet_eval_le m hw
      have hrec0 : 0 ≤ ‖(1 - (r : ℂ) * z)⁻¹‖ ^ 2 := sq_nonneg _
      have hDsq : ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2 ≤
          (m : ℝ) ^ 2 := by
        nlinarith [norm_nonneg ((Upper.dirichletPolynomial m).eval ((r : ℂ) * z))]
      nlinarith [mul_nonneg hc hrec0,
        mul_le_mul_of_nonneg_left hDsq (mul_nonneg hc hrec0)]
    _ = c * m ^ 2 * (1 - r ^ 2)⁻¹ := by
      rw [show (fun z : ℂ ↦
          (c * (m : ℝ) ^ 2) * ‖(1 - (r : ℂ) * z)⁻¹‖ ^ 2) =
          (c * (m : ℝ) ^ 2) •
            (fun z : ℂ ↦ ‖(1 - (r : ℂ) * z)⁻¹‖ ^ 2) by rfl,
        circleAverage_smul, smul_eq_mul,
        Upper.circleAverage_one_sub_mul_reciprocal_norm_sq r hr0 hr1]

lemma circleAverage_error_le
    (P : ℕ → ℂ) {C r : ℝ} (m : ℕ) (hC0 : 0 ≤ C)
    (hP : ∀ n, ‖P n‖ ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    circleAverage (fun z : ℂ ↦
      ‖Hardy.hardySum (eHardyCoeff P r) z‖ *
        ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) 0 1 ≤
      (C / (1 - r)) * m := by
  have hs := summable_norm_eHardyCoeff P hP hr0 hr1
  have hEcont : ContinuousOn (Hardy.hardySum (eHardyCoeff P r))
      (Metric.sphere 0 1) :=
    (Hardy.continuousOn_hardySum hs).mono Metric.sphere_subset_closedBall
  have hDcont : Continuous (fun z : ℂ ↦
      ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) := by
    fun_prop
  have hleft : CircleIntegrable (fun z : ℂ ↦
      ‖Hardy.hardySum (eHardyCoeff P r) z‖ *
        ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) 0 1 := by
    apply ContinuousOn.circleIntegrable'
    have hcont := hEcont.norm.mul hDcont.continuousOn
    have hcont' : ContinuousOn (fun z : ℂ ↦
        ‖Hardy.hardySum (eHardyCoeff P r) z‖ *
          ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2)
        (Metric.sphere 0 1) := by
      apply hcont.congr
      intro z hz
      rfl
    simpa only [abs_one] using hcont'
  have hright : CircleIntegrable (fun z : ℂ ↦
      (C / (1 - r)) *
        ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) 0 1 := by
    apply ContinuousOn.circleIntegrable'
    simpa only [abs_one, Pi.pow_apply] using
      hDcont.continuousOn.const_mul (C / (1 - r))
  calc
    circleAverage (fun z : ℂ ↦
        ‖Hardy.hardySum (eHardyCoeff P r) z‖ *
          ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) 0 1 ≤
        circleAverage (fun z : ℂ ↦
          (C / (1 - r)) *
            ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) 0 1 := by
      apply circleAverage_mono hleft hright
      intro z hz
      have hznorm : ‖z‖ = 1 := by simpa [Metric.mem_sphere] using hz
      have hw : ‖(r : ℂ) * z‖ < 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
          hznorm, mul_one]
        exact hr1
      have hE := norm_E_le P hP hw
      rw [E_eq_hardySum] at hE
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
        hznorm, mul_one] at hE
      exact mul_le_mul_of_nonneg_right hE (sq_nonneg _)
    _ = (C / (1 - r)) * circleAverage (fun z : ℂ ↦
          ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) 0 1 := by
      rw [show (fun z : ℂ ↦ (C / (1 - r)) *
          ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) =
          (C / (1 - r)) • (fun z : ℂ ↦
            ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) by rfl,
        circleAverage_smul, smul_eq_mul]
    _ ≤ (C / (1 - r)) * m := by
      apply mul_le_mul_of_nonneg_left
        (dirichlet_radial_circleAverage_sq_le m hr0 hr1.le)
      exact div_nonneg hC0 (sub_nonneg.mpr hr1.le)

lemma circleAverage_derivative_error_le
    (P : ℕ → ℂ) {C r lam : ℝ} (m : ℕ) (hC0 : 0 ≤ C)
    (hP : ∀ n, ‖P n‖ ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hlam : 0 < lam) :
    circleAverage (fun z : ℂ ↦
      ‖(1 - (r : ℂ) * z) *
          Hardy.hardySum (Upper.ederivHardyCoeff P r) z‖ *
        ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) 0 1 ≤
      lam * (2 * C ^ 2 / (1 - r ^ 2) ^ 3) + lam⁻¹ * m := by
  have hs := Upper.summable_norm_ederivHardyCoeff P hC0 hP hr0 hr1
  have hEcont : ContinuousOn (Hardy.hardySum (Upper.ederivHardyCoeff P r))
      (Metric.sphere 0 1) :=
    (Hardy.continuousOn_hardySum hs).mono Metric.sphere_subset_closedBall
  have hDcont : Continuous (fun z : ℂ ↦
      (Upper.dirichletPolynomial m).eval ((r : ℂ) * z)) := by
    fun_prop
  have hleft : CircleIntegrable (fun z : ℂ ↦
      ‖(1 - (r : ℂ) * z) *
          Hardy.hardySum (Upper.ederivHardyCoeff P r) z‖ *
        ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) 0 1 := by
    apply ContinuousOn.circleIntegrable'
    have hfirst : ContinuousOn (fun z : ℂ ↦
        ‖(1 - (r : ℂ) * z) *
          Hardy.hardySum (Upper.ederivHardyCoeff P r) z‖)
        (Metric.sphere 0 1) := by
      exact ((by fun_prop : Continuous (fun z : ℂ ↦ 1 - (r : ℂ) * z)).continuousOn
        |>.mul hEcont).norm
    have hsecond : ContinuousOn (fun z : ℂ ↦
        ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2)
        (Metric.sphere 0 1) := by
      have h : Continuous (fun z : ℂ ↦
          ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) := by
        fun_prop
      exact h.continuousOn
    have hcont := hfirst.mul hsecond
    have hcont' : ContinuousOn (fun z : ℂ ↦
        ‖(1 - (r : ℂ) * z) *
            Hardy.hardySum (Upper.ederivHardyCoeff P r) z‖ *
          ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2)
        (Metric.sphere 0 1) := by
      apply hcont.congr
      intro z hz
      rfl
    simpa only [abs_one] using hcont'
  have hright : CircleIntegrable (fun z : ℂ ↦
      lam * ‖Hardy.hardySum (Upper.ederivHardyCoeff P r) z‖ ^ 2 +
        lam⁻¹ * ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) 0 1 := by
    apply ContinuousOn.circleIntegrable'
    have hEsq : ContinuousOn (fun z : ℂ ↦
        ‖Hardy.hardySum (Upper.ederivHardyCoeff P r) z‖ ^ 2)
        (Metric.sphere 0 1) := by
      have h := hEcont.norm.pow 2
      apply h.congr
      intro z hz
      rfl
    have hDsq : ContinuousOn (fun z : ℂ ↦
        ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2)
        (Metric.sphere 0 1) := by
      have h : Continuous (fun z : ℂ ↦
          ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) := by
        fun_prop
      exact h.continuousOn
    have h1 : ContinuousOn (fun z : ℂ ↦
        lam * ‖Hardy.hardySum (Upper.ederivHardyCoeff P r) z‖ ^ 2)
        (Metric.sphere 0 1) := hEsq.const_mul lam
    have h2 : ContinuousOn (fun z : ℂ ↦
        lam⁻¹ * ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2)
        (Metric.sphere 0 1) := hDsq.const_mul lam⁻¹
    have hcont := h1.add h2
    have hcont' : ContinuousOn (fun z : ℂ ↦
        lam * ‖Hardy.hardySum (Upper.ederivHardyCoeff P r) z‖ ^ 2 +
          lam⁻¹ * ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2)
        (Metric.sphere 0 1) := by
      apply hcont.congr
      intro z hz
      rfl
    simpa only [abs_one] using hcont'
  have havg : circleAverage (fun z : ℂ ↦
      ‖(1 - (r : ℂ) * z) *
          Hardy.hardySum (Upper.ederivHardyCoeff P r) z‖ *
        ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) 0 1 ≤
      circleAverage (fun z : ℂ ↦
        lam * ‖Hardy.hardySum (Upper.ederivHardyCoeff P r) z‖ ^ 2 +
          lam⁻¹ * ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) 0 1 := by
    apply circleAverage_mono hleft hright
    intro z hz
    have hznorm : ‖z‖ = 1 := by simpa [Metric.mem_sphere] using hz
    let w : ℂ := (r : ℂ) * z
    let D : ℂ := (Upper.dirichletPolynomial m).eval w
    let V : ℂ := Hardy.hardySum (Upper.ederivHardyCoeff P r) z
    have hw : ‖w‖ ≤ 1 := by
      dsimp [w]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
        hznorm, mul_one]
      exact hr1.le
    have hgeom : ‖(1 - w) * D‖ ≤ 2 := by
      have hid := Upper.eval_one_sub_mul_dirichletPolynomial m w
      dsimp [D]
      rw [hid]
      calc
        ‖1 - w ^ m‖ ≤ ‖(1 : ℂ)‖ + ‖w ^ m‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by
          rw [norm_one, norm_pow]
          gcongr
          exact pow_le_one₀ (norm_nonneg w) hw
        _ = 2 := by norm_num
    change ‖(1 - w) * V‖ * ‖D‖ ^ 2 ≤
      lam * ‖V‖ ^ 2 + lam⁻¹ * ‖D‖ ^ 2
    calc
      ‖(1 - w) * V‖ * ‖D‖ ^ 2 = ‖V‖ * ‖(1 - w) * D‖ * ‖D‖ := by
        rw [norm_mul, norm_mul]
        ring
      _ ≤ ‖V‖ * 2 * ‖D‖ := by gcongr
      _ = 2 * ‖V‖ * ‖D‖ := by ring
      _ ≤ lam * ‖V‖ ^ 2 + lam⁻¹ * ‖D‖ ^ 2 :=
        Upper.two_mul_le_scaled_sq ‖V‖ ‖D‖ lam hlam
  calc
    circleAverage (fun z : ℂ ↦
        ‖(1 - (r : ℂ) * z) *
            Hardy.hardySum (Upper.ederivHardyCoeff P r) z‖ *
          ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) 0 1 ≤
        circleAverage (fun z : ℂ ↦
          lam * ‖Hardy.hardySum (Upper.ederivHardyCoeff P r) z‖ ^ 2 +
            lam⁻¹ * ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) 0 1 := havg
    _ = lam * circleAverage (fun z : ℂ ↦
          ‖Hardy.hardySum (Upper.ederivHardyCoeff P r) z‖ ^ 2) 0 1 +
        lam⁻¹ * circleAverage (fun z : ℂ ↦
          ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) 0 1 := by
      have hi1 : CircleIntegrable (fun z : ℂ ↦
          ‖Hardy.hardySum (Upper.ederivHardyCoeff P r) z‖ ^ 2) 0 1 := by
        apply ContinuousOn.circleIntegrable'
        have h := hEcont.norm.pow 2
        have h' : ContinuousOn (fun z : ℂ ↦
            ‖Hardy.hardySum (Upper.ederivHardyCoeff P r) z‖ ^ 2)
            (Metric.sphere 0 1) := by
          apply h.congr
          intro z hz
          rfl
        simpa only [abs_one] using h'
      have hi2 : CircleIntegrable (fun z : ℂ ↦
          ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) 0 1 := by
        apply ContinuousOn.circleIntegrable'
        have h' : ContinuousOn (fun z : ℂ ↦
            ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2)
            (Metric.sphere 0 1) := by
          have h : Continuous (fun z : ℂ ↦
              ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) := by
            fun_prop
          exact h.continuousOn
        simpa only [abs_one] using h'
      rw [show (fun z : ℂ ↦
          lam * ‖Hardy.hardySum (Upper.ederivHardyCoeff P r) z‖ ^ 2 +
            lam⁻¹ * ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) =
          lam • (fun z : ℂ ↦
            ‖Hardy.hardySum (Upper.ederivHardyCoeff P r) z‖ ^ 2) +
          lam⁻¹ • (fun z : ℂ ↦
            ‖(Upper.dirichletPolynomial m).eval ((r : ℂ) * z)‖ ^ 2) by rfl,
        circleAverage_add hi1.const_smul hi2.const_smul,
        circleAverage_smul, circleAverage_smul]
      simp only [smul_eq_mul]
    _ ≤ lam * (2 * C ^ 2 / (1 - r ^ 2) ^ 3) + lam⁻¹ * m := by
      gcongr
      · exact Upper.circleAverage_hardy_ederiv_sq_le P hC0 hP hr0 hr1
      · exact dirichlet_radial_circleAverage_sq_le m hr0 hr1.le

theorem kernelAverage_le
    (A : Set ℕ) (P : ℕ → ℂ) {c C r lam : ℝ} (m : ℕ)
    (hc : 0 ≤ c) (hC0 : 0 ≤ C) (hP : ∀ n, ‖P n‖ ≤ C)
    (hSum : ∀ N, summatoryC (tripleCoeff A) N = P N + (c : ℂ) * N)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hlam : 0 < lam) :
    FourierLower.kernelAverage A r m ≤
      c * m ^ 2 * (1 - r ^ 2)⁻¹ + (C / (1 - r)) * m +
        (lam * (2 * C ^ 2 / (1 - r ^ 2) ^ 3) + lam⁻¹ * m) := by
  let s : Set ℂ := Metric.sphere 0 1
  let D : ℂ → ℂ := fun z ↦
    (Upper.dirichletPolynomial m).eval ((r : ℂ) * z)
  let H0 : ℂ → ℂ := fun z ↦ Hardy.hardySum
    (eHardyCoeff (indicatorC A) r) z
  let H1 : ℂ → ℂ := fun z ↦ Hardy.hardySum
    (Upper.ederivHardyCoeff (indicatorC A) r) z
  let E0 : ℂ → ℂ := fun z ↦ Hardy.hardySum (eHardyCoeff P r) z
  let E1 : ℂ → ℂ := fun z ↦ Hardy.hardySum
    (Upper.ederivHardyCoeff P r) z
  let M : ℂ → ℂ := fun z ↦ (c : ℂ) / (1 - (r : ℂ) * z) ^ 2
  let T : ℂ → ℝ := fun z ↦
    ‖M z - E0 z + (1 - (r : ℂ) * z) * E1 z‖ * ‖D z‖ ^ 2
  have hsH0 := summable_norm_eHardyCoeff (indicatorC A)
    (C := 1) (r := r) (norm_indicator_le_one A) hr0 hr1
  have hsH1 := Upper.summable_norm_ederivHardyCoeff (indicatorC A)
    (C := 1) (r := r) (by norm_num) (norm_indicator_le_one A) hr0 hr1
  have hsE0 := summable_norm_eHardyCoeff P hP hr0 hr1
  have hsE1 := Upper.summable_norm_ederivHardyCoeff P hC0 hP hr0 hr1
  have hH0cont : ContinuousOn H0 s :=
    (Hardy.continuousOn_hardySum hsH0).mono Metric.sphere_subset_closedBall
  have hH1cont : ContinuousOn H1 s :=
    (Hardy.continuousOn_hardySum hsH1).mono Metric.sphere_subset_closedBall
  have hE0cont : ContinuousOn E0 s :=
    (Hardy.continuousOn_hardySum hsE0).mono Metric.sphere_subset_closedBall
  have hE1cont : ContinuousOn E1 s :=
    (Hardy.continuousOn_hardySum hsE1).mono Metric.sphere_subset_closedBall
  have hDcont : Continuous D := by
    dsimp [D]
    fun_prop
  have hrec := continuousOn_reciprocal_one_sub_mul hr0 hr1
  have hMcont : ContinuousOn M s := by
    have h := (hrec.pow 2).const_mul (c : ℂ)
    apply h.congr
    intro z hz
    dsimp [M]
    simp only [div_eq_mul_inv, inv_pow]
  have hTcont : ContinuousOn T s := by
    have hsub := hMcont.sub hE0cont
    have hone : Continuous (fun z : ℂ ↦ 1 - (r : ℂ) * z) := by fun_prop
    have hsum := hsub.add (hone.continuousOn.mul hE1cont)
    have hDsq : Continuous (fun z ↦ ‖D z‖ ^ 2) := by fun_prop
    have h := hsum.norm.mul hDsq.continuousOn
    apply h.congr
    intro z hz
    rfl
  have hrewrite : FourierLower.kernelAverage A r m = circleAverage T 0 1 := by
    rw [FourierLower.kernelAverage]
    apply circleAverage_congr_sphere
    intro z hz
    have hznorm : ‖z‖ = 1 := by simpa [Metric.mem_sphere] using hz
    have hzle : ‖z‖ ≤ 1 := hznorm.le
    have hw : ‖(r : ℂ) * z‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
        hznorm, mul_one]
      exact hr1
    have hdgf := differentiated_bounded_error_identity A P (c : ℂ)
      hP hSum hw
    have hF : F A ((r : ℂ) * z) = H0 z := by
      change E (indicatorC A) ((r : ℂ) * z) = H0 z
      exact E_eq_hardySum (indicatorC A) r z
    have hF' : Fderiv A ((r : ℂ) * z) = H1 z := by
      change Ederiv (indicatorC A) ((r : ℂ) * z) = H1 z
      exact Ederiv_eq_hardySum (indicatorC A) (C := 1)
        (norm_indicator_le_one A) hr0 hr1 z hzle
    have hE : E P ((r : ℂ) * z) = E0 z := E_eq_hardySum P r z
    have hE' : Ederiv P ((r : ℂ) * z) = E1 z :=
      Ederiv_eq_hardySum P hP hr0 hr1 z hzle
    have hnorm :
        3 * ‖F A ((r : ℂ) * z)‖ ^ 2 * ‖Fderiv A ((r : ℂ) * z)‖ =
          ‖3 * F A ((r : ℂ) * z) ^ 2 * Fderiv A ((r : ℂ) * z)‖ := by
      simp [norm_mul, norm_pow]
    dsimp only [T, D, M, E0, E1]
    rw [hnorm, hdgf, hE, hE']
  rw [hrewrite]
  let U0 : ℂ → ℝ := fun z ↦
    c * ‖(1 - (r : ℂ) * z)⁻¹‖ ^ 2 * ‖D z‖ ^ 2
  let U1 : ℂ → ℝ := fun z ↦ ‖E0 z‖ * ‖D z‖ ^ 2
  let U2 : ℂ → ℝ := fun z ↦
    ‖(1 - (r : ℂ) * z) * E1 z‖ * ‖D z‖ ^ 2
  have hDsqcont : ContinuousOn (fun z ↦ ‖D z‖ ^ 2) s := by
    have h : Continuous (fun z ↦ ‖D z‖ ^ 2) := by fun_prop
    exact h.continuousOn
  have hU0cont : ContinuousOn U0 s := by
    have hleft := (hrec.norm.pow 2).const_mul c
    have h := hleft.mul hDsqcont
    apply h.congr
    intro z hz
    rfl
  have hU1cont : ContinuousOn U1 s := by
    have h := hE0cont.norm.mul hDsqcont
    apply h.congr
    intro z hz
    rfl
  have hU2cont : ContinuousOn U2 s := by
    have hone : Continuous (fun z : ℂ ↦ 1 - (r : ℂ) * z) := by fun_prop
    have hfirst := (hone.continuousOn.mul hE1cont).norm
    have h := hfirst.mul hDsqcont
    apply h.congr
    intro z hz
    rfl
  have hTint : CircleIntegrable T 0 1 := by
    apply ContinuousOn.circleIntegrable'
    simpa only [s, abs_one] using hTcont
  have hU0int : CircleIntegrable U0 0 1 := by
    apply ContinuousOn.circleIntegrable'
    simpa only [s, abs_one] using hU0cont
  have hU1int : CircleIntegrable U1 0 1 := by
    apply ContinuousOn.circleIntegrable'
    simpa only [s, abs_one] using hU1cont
  have hU2int : CircleIntegrable U2 0 1 := by
    apply ContinuousOn.circleIntegrable'
    simpa only [s, abs_one] using hU2cont
  have hmono : circleAverage T 0 1 ≤
      circleAverage (fun z ↦ U0 z + U1 z + U2 z) 0 1 := by
    apply circleAverage_mono hTint ((hU0int.add hU1int).add hU2int)
    intro z hz
    have htri : ‖M z - E0 z + (1 - (r : ℂ) * z) * E1 z‖ ≤
        ‖M z‖ + ‖E0 z‖ + ‖(1 - (r : ℂ) * z) * E1 z‖ := by
      calc
        ‖M z - E0 z + (1 - (r : ℂ) * z) * E1 z‖ ≤
            ‖M z - E0 z‖ + ‖(1 - (r : ℂ) * z) * E1 z‖ :=
          norm_add_le _ _
        _ ≤ (‖M z‖ + ‖E0 z‖) + ‖(1 - (r : ℂ) * z) * E1 z‖ := by
          gcongr
          exact norm_sub_le _ _
    have hmainnorm : ‖M z‖ = c * ‖(1 - (r : ℂ) * z)⁻¹‖ ^ 2 := by
      dsimp [M]
      rw [div_eq_mul_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hc, ← inv_pow, norm_pow]
    dsimp [T, U0, U1, U2]
    calc
      ‖M z - E0 z + (1 - (r : ℂ) * z) * E1 z‖ * ‖D z‖ ^ 2 ≤
          (‖M z‖ + ‖E0 z‖ + ‖(1 - (r : ℂ) * z) * E1 z‖) *
            ‖D z‖ ^ 2 := mul_le_mul_of_nonneg_right htri (sq_nonneg _)
      _ = c * ‖(1 - (r : ℂ) * z)⁻¹‖ ^ 2 * ‖D z‖ ^ 2 +
          ‖E0 z‖ * ‖D z‖ ^ 2 +
            ‖(1 - (r : ℂ) * z) * E1 z‖ * ‖D z‖ ^ 2 := by
        rw [hmainnorm]
        ring
  calc
    circleAverage T 0 1 ≤
        circleAverage (fun z ↦ U0 z + U1 z + U2 z) 0 1 := hmono
    _ = circleAverage U0 0 1 + circleAverage U1 0 1 + circleAverage U2 0 1 := by
      change circleAverage ((U0 + U1) + U2) 0 1 = _
      rw [circleAverage_add (hU0int.add hU1int) hU2int,
        circleAverage_add hU0int hU1int]
    _ ≤ c * m ^ 2 * (1 - r ^ 2)⁻¹ + (C / (1 - r)) * m +
          (lam * (2 * C ^ 2 / (1 - r ^ 2) ^ 3) + lam⁻¹ * m) := by
      dsimp [U0, U1, U2, D, E0, E1]
      gcongr
      · exact circleAverage_main_le m hc hr0 hr1
      · exact circleAverage_error_le P m hC0 hP hr0 hr1
      · exact circleAverage_derivative_error_le P m hC0 hP hr0 hr1 hlam

theorem kernelAverage_radius_le
    (A : Set ℕ) (P : ℕ → ℂ) {c C X lam : ℝ} (m : ℕ)
    (hc : 0 ≤ c) (hC0 : 0 ≤ C) (hP : ∀ n, ‖P n‖ ≤ C)
    (hSum : ∀ N, summatoryC (tripleCoeff A) N = P N + (c : ℂ) * N)
    (hX : 1 < X) (hlam : 0 < lam) :
    FourierLower.kernelAverage A (radius X) m ≤
      c * m ^ 2 * X + C * X * m +
        (lam * (2 * C ^ 2 * X ^ 3) + lam⁻¹ * m) := by
  have hX0 : 0 < X := lt_trans zero_lt_one hX
  have hr0 : 0 ≤ radius X := radius_nonneg hX.le
  have hr1 : radius X < 1 := radius_lt_one hX0
  have hbase := kernelAverage_le A P m hc hC0 hP hSum hr0 hr1 hlam
  have hinv := inv_one_sub_radius_sq_le_X hX
  have hdpos : 0 < 1 - radius X ^ 2 := one_sub_radius_sq_pos hX
  have hinv0 : 0 ≤ (1 - radius X ^ 2)⁻¹ := inv_nonneg.mpr hdpos.le
  have hinv3 : (1 - radius X ^ 2)⁻¹ ^ 3 ≤ X ^ 3 := by
    exact pow_le_pow_left₀ hinv0 hinv 3
  have herr : C / (1 - radius X) = C * X := by
    rw [radius]
    field_simp
    ring
  have hderiv : 2 * C ^ 2 / (1 - radius X ^ 2) ^ 3 ≤
      2 * C ^ 2 * X ^ 3 := by
    rw [div_eq_mul_inv, ← inv_pow]
    gcongr
  calc
    FourierLower.kernelAverage A (radius X) m ≤
        c * m ^ 2 * (1 - radius X ^ 2)⁻¹ +
          (C / (1 - radius X)) * m +
            (lam * (2 * C ^ 2 / (1 - radius X ^ 2) ^ 3) + lam⁻¹ * m) := hbase
    _ ≤ c * m ^ 2 * X + C * X * m +
          (lam * (2 * C ^ 2 * X ^ 3) + lam⁻¹ * m) := by
      rw [herr]
      gcongr

theorem kernelAverage_radius_le_coarse
    (A : Set ℕ) (P : ℕ → ℂ) {c C X lam : ℝ} (m : ℕ)
    (hc : 0 ≤ c) (hC0 : 0 ≤ C) (hP : ∀ n, ‖P n‖ ≤ C)
    (hSum : ∀ N, summatoryC (tripleCoeff A) N = P N + (c : ℂ) * N)
    (hX : 1 < X) (hlam : 0 < lam) (hm : 1 ≤ m) :
    FourierLower.kernelAverage A (radius X) m ≤
      (c + C) * m ^ 2 * X + lam * (2 * C ^ 2 * X ^ 3) + lam⁻¹ * m := by
  have h := kernelAverage_radius_le A P m hc hC0 hP hSum hX hlam
  have hX0 : 0 ≤ X := le_of_lt (lt_trans zero_lt_one hX)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := le_trans zero_le_one hmR
  have hm_sq : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have herr : C * X * (m : ℝ) ≤ C * (m : ℝ) ^ 2 * X := by
    nlinarith [mul_le_mul_of_nonneg_left hm_sq hC0,
      mul_nonneg hC0 hX0, mul_nonneg (sq_nonneg (m : ℝ)) hX0]
  nlinarith
end KernelUpper

namespace FourierLower

open scoped BigOperators Classical Real ComplexConjugate Polynomial
open Finset Complex MeasureTheory Set Filter

noncomputable def uTermAlt (A : Set ℕ) (r : ℝ) (m : ℕ)
    (y : Σ _p : ℕ × ℕ, ℕ × ℕ) : ℝ :=
  3 * (radialFCoeff A r y.2.1).re *
    (Upper.ederivHardyCoeff (indicatorC A) r y.2.2).re *
      (radialDirichletCoeff m r y.1.2).re

lemma uCoeff_re_eq_sigma_alt (A : Set ℕ) (r : ℝ) (m n : ℕ) :
    (uCoeff A r m n).re =
      ∑ y ∈ (antidiagonal n).sigma (fun p ↦ antidiagonal p.1), uTermAlt A r m y := by
  rw [Finset.sum_sigma]
  rw [uCoeff, Complex.mul_re]
  rw [show (3 : ℂ).re = 3 by norm_num, show (3 : ℂ).im = 0 by norm_num,
    zero_mul, sub_zero]
  rw [convC, Complex.re_sum]
  simp_rw [Complex.mul_re, radialDirichletCoeff_im, mul_zero, sub_zero]
  simp_rw [convC, Complex.re_sum, Complex.mul_re, radialFCoeff_im,
    ederivHardyCoeff_indicator_im, mul_zero, sub_zero]
  simp only [uTermAlt]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  ring

noncomputable def waRadAlt (A : Set ℕ) (r : ℝ) (a : ℕ) : ℝ :=
  (radialFCoeff A r a).re

noncomputable def wdRadAlt (A : Set ℕ) (r : ℝ) (d : ℕ) : ℝ :=
  (Upper.ederivHardyCoeff (indicatorC A) r (d - 1)).re

noncomputable def wkRadAlt (m : ℕ) (r : ℝ) (j : ℕ) : ℝ :=
  (radialDirichletCoeff m r j).re

noncomputable def tripleToNestedAlt (x : (ℕ × ℕ) × ℕ) :
    Σ _p : ℕ × ℕ, ℕ × ℕ :=
  ⟨(x.1.1 + (x.1.2 - 1), x.2), (x.1.1, x.1.2 - 1)⟩

lemma tripleToNestedAlt_injOn (aS dS jS : Finset ℕ)
    (hdpos : ∀ d ∈ dS, 1 ≤ d) :
    Set.InjOn tripleToNestedAlt ↑((aS.product dS).product jS) := by
  intro x hx y hy hxy
  have hq := congrArg Sigma.snd hxy
  have hp := congrArg Sigma.fst hxy
  rcases Finset.mem_product.mp hx with ⟨hxad, hxj⟩
  rcases Finset.mem_product.mp hxad with ⟨hxa, hxd⟩
  rcases Finset.mem_product.mp hy with ⟨hyad, hyj⟩
  rcases Finset.mem_product.mp hyad with ⟨hya, hyd⟩
  have hxdpos := hdpos x.1.2 hxd
  have hydpos := hdpos y.1.2 hyd
  simp only [tripleToNestedAlt] at hq hp
  have ha : x.1.1 = y.1.1 := by
    injection hq
  have hdsub : x.1.2 - 1 = y.1.2 - 1 := by
    injection hq
  have hj : x.2 = y.2 := by
    injection hp
  rcases x with ⟨⟨xa, xd⟩, xj⟩
  rcases y with ⟨⟨ya, yd⟩, yj⟩
  simp only at ha hdsub hj hxdpos hydpos ⊢
  congr
  omega

lemma coeff_u_monomialSum_le_alt
    (A : Set ℕ) {r : ℝ} (m : ℕ) (hr0 : 0 ≤ r)
    (aS dS jS : Finset ℕ) (hdpos : ∀ d ∈ dS, 1 ≤ d) (n : ℕ) :
    (monomialSum ((aS.product dS).product jS)
      (fun x ↦ x.1.1 + (x.1.2 - 1) + x.2)
      (fun x ↦ 3 * waRadAlt A r x.1.1 * wdRadAlt A r x.1.2 *
        wkRadAlt m r x.2)).coeff n ≤ (uCoeff A r m n).re := by
  rw [coeff_monomialSum, uCoeff_re_eq_sigma_alt]
  let S := ((aS.product dS).product jS).filter
    (fun x ↦ x.1.1 + (x.1.2 - 1) + x.2 = n)
  let T := (antidiagonal n).sigma (fun p ↦ antidiagonal p.1)
  have hinj : Set.InjOn tripleToNestedAlt ↑S :=
    (tripleToNestedAlt_injOn aS dS jS hdpos).mono fun x hx ↦
      (Finset.mem_filter.mp hx).1
  have himage : S.image tripleToNestedAlt ⊆ T := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rcases Finset.mem_filter.mp hx with ⟨hxmem, hexp⟩
    simp only [T, tripleToNestedAlt, Finset.mem_sigma]
    exact ⟨HasAntidiagonal.mem_antidiagonal.mpr (by simpa [add_assoc] using hexp),
      HasAntidiagonal.mem_antidiagonal.mpr rfl⟩
  change ∑ x ∈ S, 3 * waRadAlt A r x.1.1 * wdRadAlt A r x.1.2 *
      wkRadAlt m r x.2 ≤ ∑ y ∈ T, uTermAlt A r m y
  calc
    ∑ x ∈ S, 3 * waRadAlt A r x.1.1 * wdRadAlt A r x.1.2 *
        wkRadAlt m r x.2 = ∑ x ∈ S, uTermAlt A r m (tripleToNestedAlt x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rfl
    _ = ∑ y ∈ S.image tripleToNestedAlt, uTermAlt A r m y :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑ y ∈ T, uTermAlt A r m y := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro y hyT hyS
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (radialFCoeff_re_nonneg A hr0 _))
          (ederivHardyCoeff_indicator_re_nonneg A hr0 _))
        (radialDirichletCoeff_re_nonneg m hr0 _)

noncomputable def vTermAlt (A : Set ℕ) (r : ℝ) (m : ℕ)
    (p : ℕ × ℕ) : ℝ :=
  (radialFCoeff A r p.1).re * (radialDirichletCoeff m r p.2).re

lemma vCoeff_re_eq_antidiagonal_alt (A : Set ℕ) (r : ℝ) (m n : ℕ) :
    (vCoeff A r m n).re = ∑ p ∈ antidiagonal n, vTermAlt A r m p := by
  rw [vCoeff, convC, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Complex.mul_re, radialFCoeff_im, radialDirichletCoeff_im, zero_mul, sub_zero]
  rfl

lemma coeff_v_monomialSum_le_alt
    (A : Set ℕ) {r : ℝ} (m : ℕ) (hr0 : 0 ≤ r)
    (bS ellS : Finset ℕ) (n : ℕ) :
    (monomialSum (bS.product ellS) (fun x ↦ x.1 + x.2)
      (fun x ↦ waRadAlt A r x.1 * wkRadAlt m r x.2)).coeff n ≤
        (vCoeff A r m n).re := by
  rw [coeff_monomialSum, vCoeff_re_eq_antidiagonal_alt]
  let S := (bS.product ellS).filter (fun x ↦ x.1 + x.2 = n)
  have hsub : S ⊆ antidiagonal n := by
    intro p hp
    exact HasAntidiagonal.mem_antidiagonal.mpr (Finset.mem_filter.mp hp).2
  change ∑ p ∈ S, waRadAlt A r p.1 * wkRadAlt m r p.2 ≤
    ∑ p ∈ antidiagonal n, vTermAlt A r m p
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro p hp hpn
  exact mul_nonneg (radialFCoeff_re_nonneg A hr0 _)
    (radialDirichletCoeff_re_nonneg m hr0 _)

lemma waRadAlt_of_mem {A : Set ℕ} {r : ℝ} {a : ℕ} (ha : a ∈ A) :
    waRadAlt A r a = r ^ a := by
  simp only [waRadAlt, radialFCoeff, indicatorC, Set.indicator_of_mem ha, one_mul,
    realCast_pow_re]

lemma wdRadAlt_of_mem_pos {A : Set ℕ} {r : ℝ} {d : ℕ}
    (hd : d ∈ A) (hdpos : 1 ≤ d) :
    wdRadAlt A r d = (d : ℝ) * r ^ (d - 1) := by
  simp only [wdRadAlt, Upper.ederivHardyCoeff, indicatorC]
  rw [show d - 1 + 1 = d by omega, Set.indicator_of_mem hd, mul_one,
    Complex.mul_re, realCast_pow_re]
  simp

lemma wkRadAlt_of_lt {m : ℕ} {r : ℝ} {j : ℕ} (hj : j < m) :
    wkRadAlt m r j = r ^ j := by
  simp only [wkRadAlt, radialDirichletCoeff, if_pos hj, realCast_pow_re]

lemma selected_radial_term_eq
    {A : Set ℕ} {r : ℝ} {m a d j : ℕ}
    (ha : a ∈ A) (hd : d ∈ A) (hapos : 1 ≤ a) (hdpos : 1 ≤ d)
    (hj : j < m) (hell : a - 1 + j < m) :
    (3 * waRadAlt A r a * wdRadAlt A r d * wkRadAlt m r j) *
        (waRadAlt A r d * wkRadAlt m r (a - 1 + j)) =
      3 * ((d : ℝ) * (r ^ 2) ^ (d - 1)) * (r ^ 2) ^ a * (r ^ 2) ^ j := by
  rw [waRadAlt_of_mem ha, wdRadAlt_of_mem_pos hd hdpos, wkRadAlt_of_lt hj,
    waRadAlt_of_mem hd, wkRadAlt_of_lt hell]
  rw [← pow_mul, ← pow_mul, ← pow_mul]
  calc
    (3 * r ^ a * ((d : ℝ) * r ^ (d - 1)) * r ^ j) *
        (r ^ d * r ^ (a - 1 + j)) =
      3 * (d : ℝ) * (r ^ a * r ^ (d - 1) * r ^ j * r ^ d * r ^ (a - 1 + j)) := by
        ring
    _ = 3 * (d : ℝ) * r ^ (a + (d - 1) + j + d + (a - 1 + j)) := by
      rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
    _ = 3 * (d : ℝ) * r ^ (2 * (d - 1) + 2 * a + 2 * j) := by
      congr 2
      omega
    _ = 3 * ((d : ℝ) * r ^ (2 * (d - 1))) * r ^ (2 * a) * r ^ (2 * j) := by
      rw [pow_add, pow_add]
      ring

lemma summable_fderivReal_term_alt (A : Set ℕ) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable (fun d : ℕ ↦ (d : ℝ) * (indicator A d : ℝ) * x ^ (d - 1)) := by
  apply (summable_nat_mul_pow_pred hx0 hx1).of_nonneg_of_le
  · intro d
    positivity
  · intro d
    by_cases hd : d ∈ A
    · simp [indicator, hd]
    · simp [indicator, hd, mul_nonneg (Nat.cast_nonneg d) (pow_nonneg hx0 (d - 1))]

/-- A positive infinite radial derivative has a finite positive-index cutoff
carrying at least half of its mass. -/
lemma exists_finite_derivative_cutoff_alt
    (A : Set ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hpos : 0 < FderivReal A x) :
    ∃ N : ℕ, FderivReal A x / 2 ≤
      ∑ d ∈ (Finset.Ico 1 N).filter (fun d ↦ d ∈ A),
        (d : ℝ) * x ^ (d - 1) := by
  let f : ℕ → ℝ := fun d ↦ (d : ℝ) * (indicator A d : ℝ) * x ^ (d - 1)
  have hs : Summable f := by
    simpa only [f] using summable_fderivReal_term_alt A hx0 hx1
  have hhalf : FderivReal A x / 2 < FderivReal A x := by linarith
  have hlim : Tendsto (fun N : ℕ ↦ ∑ d ∈ Finset.range N, f d) atTop
      (nhds (FderivReal A x)) := by
    simpa only [FderivReal, f] using hs.hasSum.tendsto_sum_nat
  have hev : ∀ᶠ N : ℕ in atTop,
      FderivReal A x / 2 < ∑ d ∈ Finset.range N, f d :=
    hlim.eventually (Ioi_mem_nhds hhalf)
  obtain ⟨N, hN⟩ := hev.exists
  refine ⟨N, hN.le.trans_eq ?_⟩
  have hsub : Finset.Ico 1 N ⊆ Finset.range N := by
    intro d hd
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hd).2
  have hIco : ∑ d ∈ Finset.Ico 1 N, f d = ∑ d ∈ Finset.range N, f d := by
    apply Finset.sum_subset hsub
    intro d hdr hdIco
    have hd0 : d = 0 := by
      have hdlt : d < N := Finset.mem_range.mp hdr
      have : ¬ 1 ≤ d := fun hd1 ↦ hdIco (Finset.mem_Ico.mpr ⟨hd1, hdlt⟩)
      omega
    subst d
    simp [f]
  rw [← hIco]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdA : d ∈ A <;> simp [f, indicator, hdA]

lemma triple_product_sum_factor_alt
    {aS dS jS : Finset ℕ} (fa fd fj : ℕ → ℝ) :
    ∑ x ∈ (aS.product dS).product jS,
      3 * fd x.1.2 * fa x.1.1 * fj x.2 =
    3 * (∑ d ∈ dS, fd d) * (∑ a ∈ aS, fa a) *
      (∑ j ∈ jS, fj j) := by
  calc
    ∑ x ∈ (aS.product dS).product jS,
        3 * fd x.1.2 * fa x.1.1 * fj x.2 =
      ∑ ad ∈ aS.product dS, ∑ j ∈ jS,
        3 * fd ad.2 * fa ad.1 * fj j := by
          simpa using Finset.sum_product (aS.product dS) jS
            (fun x ↦ 3 * fd x.1.2 * fa x.1.1 * fj x.2)
    _ = ∑ a ∈ aS, ∑ d ∈ dS, ∑ j ∈ jS,
        3 * fd d * fa a * fj j := by
          simpa using Finset.sum_product aS dS
            (fun ad ↦ ∑ j ∈ jS, 3 * fd ad.2 * fa ad.1 * fj j)
    _ = ∑ a ∈ aS, ∑ d ∈ dS,
        (3 * fd d * fa a) * (∑ j ∈ jS, fj j) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
    _ = ∑ a ∈ aS,
        (3 * (∑ d ∈ dS, fd d) * fa a) * (∑ j ∈ jS, fj j) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- The selected-frequency argument specialized to radial coefficients and a
finite derivative cutoff. -/
lemma concrete_selected_lower_alt
    (A : Set ℕ) {X : ℝ} (hX : 1 ≤ X) {s N m : ℕ}
    (hm : 2 * s ≤ m) (hbudget : 4 * (s : ℝ) ≤ X)
    (hcut : FderivReal A (radius X ^ 2) / 2 ≤
      ∑ d ∈ (Finset.Ico 1 N).filter (fun d ↦ d ∈ A),
        (d : ℝ) * (radius X ^ 2) ^ (d - 1)) :
    3 * (FderivReal A (radius X ^ 2) / 2) *
        (positiveCountingFunction A s / 2) * ((s : ℝ) / 2) ≤
      kernelAverage A (radius X) m := by
  let aS := (Finset.Icc 1 s).filter (fun a ↦ a ∈ A)
  let dS := (Finset.Ico 1 N).filter (fun d ↦ d ∈ A)
  let jS := Finset.range s
  let ellS := Finset.range m
  have hr0 : 0 ≤ radius X := radius_nonneg hX
  have hr1 : radius X < 1 := radius_lt_one (lt_of_lt_of_le zero_lt_one hX)
  have hsle : s ≤ m := by omega
  have haPos : ∀ a ∈ aS, 1 ≤ a := by
    intro a ha
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
  have hdPos : ∀ d ∈ dS, 1 ≤ d := by
    intro d hd
    exact (Finset.mem_Ico.mp (Finset.mem_filter.mp hd).1).1
  have hell : ∀ a ∈ aS, ∀ j ∈ jS, a - 1 + j ∈ ellS := by
    intro a ha j hj
    apply Finset.mem_range.mpr
    have has := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2
    have hjs := Finset.mem_range.mp hj
    omega
  have hselected := selected_b_eq_d_le_kernelAverage
    A m hr0 hr1 aS dS jS dS ellS aS dS jS
    (waRadAlt A (radius X)) (wdRadAlt A (radius X))
    (wkRadAlt m (radius X)) (waRadAlt A (radius X))
    (wkRadAlt m (radius X))
    (fun _ h ↦ h) (fun _ h ↦ h) (fun _ h ↦ h) (fun _ h ↦ h)
    hell haPos hdPos
    (fun a ha ↦ radialFCoeff_re_nonneg A hr0 a)
    (fun d hd ↦ ederivHardyCoeff_indicator_re_nonneg A hr0 (d - 1))
    (fun j hj ↦ radialDirichletCoeff_re_nonneg m hr0 j)
    (fun d hd ↦ radialFCoeff_re_nonneg A hr0 d)
    (fun l hl ↦ radialDirichletCoeff_re_nonneg m hr0 l)
    (coeff_u_monomialSum_le_alt A m hr0 aS dS jS hdPos)
    (coeff_v_monomialSum_le_alt A m hr0 dS ellS)
  let fd : ℕ → ℝ := fun d ↦ (d : ℝ) * (radius X ^ 2) ^ (d - 1)
  let fa : ℕ → ℝ := fun a ↦ (radius X ^ 2) ^ a
  let fj : ℕ → ℝ := fun j ↦ (radius X ^ 2) ^ j
  have hfac :
      ∑ x ∈ (aS.product dS).product jS,
          (3 * waRadAlt A (radius X) x.1.1 * wdRadAlt A (radius X) x.1.2 *
              wkRadAlt m (radius X) x.2) *
            (waRadAlt A (radius X) x.1.2 *
              wkRadAlt m (radius X) (x.1.1 - 1 + x.2)) =
        3 * (∑ d ∈ dS, fd d) * (∑ a ∈ aS, fa a) *
          (∑ j ∈ jS, fj j) := by
    calc
      _ = ∑ x ∈ (aS.product dS).product jS,
          3 * fd x.1.2 * fa x.1.1 * fj x.2 := by
        apply Finset.sum_congr rfl
        intro x hx
        rcases Finset.mem_product.mp hx with ⟨hxad, hxj⟩
        rcases Finset.mem_product.mp hxad with ⟨hxa, hxd⟩
        have hxaA := (Finset.mem_filter.mp hxa).2
        have hxdA := (Finset.mem_filter.mp hxd).2
        have hxjlt : x.2 < m := (Finset.mem_range.mp hxj).trans_le hsle
        have hxell : x.1.1 - 1 + x.2 < m := Finset.mem_range.mp (hell _ hxa _ hxj)
        simpa only [fd, fa, fj] using
          selected_radial_term_eq (a := x.1.1) (d := x.1.2) (j := x.2)
            hxaA hxdA (haPos x.1.1 hxa) (hdPos x.1.2 hxd) hxjlt hxell
      _ = _ := triple_product_sum_factor_alt fa fd fj
  rw [hfac] at hselected
  have haWeight : positiveCountingFunction A s / 2 ≤ ∑ a ∈ aS, fa a := by
    simpa only [aS, fa] using half_positiveCountingFunction_le_weighted_sum A hX hbudget
  have hjWeight : (s : ℝ) / 2 ≤ ∑ j ∈ jS, fj j := by
    simpa only [jS, fj] using half_nat_le_sum_range_radius_sq hX hbudget
  have hderiv0 : 0 ≤ FderivReal A (radius X ^ 2) :=
    FderivReal_nonneg A (sq_nonneg _)
  have hcount0 : 0 ≤ (positiveCountingFunction A s : ℝ) / 2 := by positivity
  have hs0 : 0 ≤ (s : ℝ) / 2 := by positivity
  calc
    3 * (FderivReal A (radius X ^ 2) / 2) *
        (positiveCountingFunction A s / 2) * ((s : ℝ) / 2) ≤
      3 * (∑ d ∈ dS, fd d) * (∑ a ∈ aS, fa a) *
        (∑ j ∈ jS, fj j) := by gcongr
    _ ≤ kernelAverage A (radius X) m := hselected

end FourierLower

lemma scaled_specialized_upper_power_le {x k c C : ℝ}
    (hx : 1 ≤ x) (hk : 1 ≤ k) (hC : 0 ≤ C) :
    c * (32 * k ^ 3 * x ^ 3) ^ 2 * x ^ 9 +
        C * x ^ 9 * (32 * k ^ 3 * x ^ 3) +
          ((x ^ 12)⁻¹ * (2 * C ^ 2 * (x ^ 9) ^ 3) +
            x ^ 12 * (32 * k ^ 3 * x ^ 3)) ≤
      (1024 * (c + C) * k ^ 6 + 2 * C ^ 2 + 32 * k ^ 3) * x ^ 15 := by
  have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hx)
  have hid :
      c * (32 * k ^ 3 * x ^ 3) ^ 2 * x ^ 9 +
          C * x ^ 9 * (32 * k ^ 3 * x ^ 3) +
            ((x ^ 12)⁻¹ * (2 * C ^ 2 * (x ^ 9) ^ 3) +
              x ^ 12 * (32 * k ^ 3 * x ^ 3)) =
        1024 * c * k ^ 6 * x ^ 15 + 32 * C * k ^ 3 * x ^ 12 +
          (2 * C ^ 2 + 32 * k ^ 3) * x ^ 15 := by
    field_simp [hx0] <;> ring
  rw [hid]
  have hkpow : k ^ 3 ≤ k ^ 6 := pow_le_pow_right₀ hk (by omega)
  have hxpow : x ^ 12 ≤ x ^ 15 := pow_le_pow_right₀ hx (by omega)
  have hmiddle : 32 * C * k ^ 3 * x ^ 12 ≤ 1024 * C * k ^ 6 * x ^ 15 := by
    calc
      32 * C * k ^ 3 * x ^ 12 ≤ 1024 * C * k ^ 3 * x ^ 12 := by
        gcongr
        norm_num
      _ ≤ 1024 * C * k ^ 6 * x ^ 12 := by gcongr
      _ ≤ 1024 * C * k ^ 6 * x ^ 15 := by gcongr
  nlinarith

lemma scaled_selected_lower_power_coarse
    {J x k c κ D SA SJ : ℝ}
    (hx : 2 ≤ x) (hk : 0 ≤ k) (hc : 0 < c) (hκ : 0 < κ)
    (hD : c * x ^ 12 / (48 * κ ^ 2) ≤ D)
    (hSA : (x - 1) / 2 ≤ SA)
    (hSJ : 8 * k ^ 3 * x ^ 3 ≤ SJ)
    (hJ : 3 * D * SA * SJ ≤ J) :
    c * k ^ 3 / (8 * κ ^ 2) * x ^ 16 ≤ J := by
  have hD0 : 0 ≤ D :=
    (by positivity : 0 ≤ c * x ^ 12 / (48 * κ ^ 2)).trans hD
  have hxm10 : 0 ≤ x - 1 := by linarith
  have hSA0 : 0 ≤ SA := (div_nonneg hxm10 (by norm_num)).trans hSA
  have hSJ0 : 0 ≤ SJ := (by positivity : 0 ≤ 8 * k ^ 3 * x ^ 3).trans hSJ
  have hbase :
      3 * (c * x ^ 12 / (48 * κ ^ 2)) * ((x - 1) / 2) *
          (8 * k ^ 3 * x ^ 3) ≤ 3 * D * SA * SJ := by
    calc
      3 * (c * x ^ 12 / (48 * κ ^ 2)) * ((x - 1) / 2) *
          (8 * k ^ 3 * x ^ 3) ≤
          3 * D * ((x - 1) / 2) * (8 * k ^ 3 * x ^ 3) := by gcongr
      _ ≤ 3 * D * SA * (8 * k ^ 3 * x ^ 3) := by gcongr
      _ ≤ 3 * D * SA * SJ := by gcongr
  have hscale : 0 ≤ c * k ^ 3 * x ^ 15 / κ ^ 2 := by positivity
  have halg :
      c * k ^ 3 / (8 * κ ^ 2) * x ^ 16 ≤
        3 * (c * x ^ 12 / (48 * κ ^ 2)) * ((x - 1) / 2) *
          (8 * k ^ 3 * x ^ 3) := by
    calc
      c * k ^ 3 / (8 * κ ^ 2) * x ^ 16 =
          (c * k ^ 3 * x ^ 15 / κ ^ 2) * (x / 8) := by
            field_simp [ne_of_gt hκ] <;> ring
      _ ≤ (c * k ^ 3 * x ^ 15 / κ ^ 2) * ((x - 1) / 4) := by
        apply mul_le_mul_of_nonneg_left _ hscale
        linarith
      _ = 3 * (c * x ^ 12 / (48 * κ ^ 2)) * ((x - 1) / 2) *
          (8 * k ^ 3 * x ^ 3) := by
            field_simp [ne_of_gt hκ] <;> ring
  exact halg.trans (hbase.trans hJ)

/-- Negative resolution of Erdős Problem 764: the summatory ordered
three-fold additive convolution of a set indicator cannot be `c * N + O(1)`
for any positive real constant `c`. -/
theorem erdos_764 :
    ¬ ∃ A : Set ℕ, ∃ c : ℝ, 0 < c ∧
      remainder A c =O[Filter.atTop] (fun _ : ℕ ↦ (1 : ℝ)) := by
  rintro ⟨A, c, hc, hO⟩
  obtain ⟨C, hC⟩ := uniform_remainder_bound_of_isBigO_one A c hO
  have hC0 : 0 ≤ C := (abs_nonneg (remainder A c 0)).trans (hC 0)
  obtain ⟨K, hK, hcountEv⟩ :=
    exists_eventual_positiveCountingFunction_scaled_lower A c C hc hC
  let κ : ℝ := c + C + 1
  have hκ : 0 < κ := by dsimp [κ]; linarith
  let a : ℝ := c * (K : ℝ) ^ 3 / (8 * κ ^ 2)
  let b : ℝ :=
    1024 * (c + C) * (K : ℝ) ^ 6 + 2 * C ^ 2 + 32 * (K : ℝ) ^ 3
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  obtain ⟨T, hT⟩ := eventually_atTop.1 hcountEv
  obtain ⟨t, htT, ht, hlarge, hbudget64, htfinal⟩ :=
    exists_large_natural_parameter c C a b K T hc ha
  have hcount0 := hT t htT
  let s : ℕ := 16 * K ^ 3 * t ^ 3
  let m : ℕ := 32 * K ^ 3 * t ^ 3
  have harg : (4 * K * t) ^ 3 / 4 = s := by
    rw [show (4 * K * t) ^ 3 = 4 * (16 * K ^ 3 * t ^ 3) by ring]
    simp [s]
  have hcount : t - 1 ≤ positiveCountingFunction A s := by
    rwa [harg] at hcount0
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hX2 : 2 ≤ (t : ℝ) ^ 9 :=
    htR.trans (le_self_pow₀ (by linarith : (1 : ℝ) ≤ t) (by norm_num))
  have hX1 : 1 < (t : ℝ) ^ 9 := lt_of_lt_of_le (by norm_num) hX2
  obtain ⟨_hF, hD⟩ := radial_F_and_deriv_bounds A c C hc hC ht hlarge
  have hDpos : 0 < FderivReal A (radius ((t : ℝ) ^ 9) ^ 2) := by
    have : 0 < c * (t : ℝ) ^ 12 / (24 * κ ^ 2) := by positivity
    exact this.trans_le (by simpa [κ] using hD)
  have hr0 : 0 ≤ radius ((t : ℝ) ^ 9) := radius_nonneg hX1.le
  have hr1 : radius ((t : ℝ) ^ 9) < 1 := radius_lt_one (by positivity)
  have hx0 : 0 ≤ radius ((t : ℝ) ^ 9) ^ 2 := sq_nonneg _
  have hx1 : radius ((t : ℝ) ^ 9) ^ 2 < 1 := by nlinarith
  obtain ⟨N, hcut⟩ :=
    FourierLower.exists_finite_derivative_cutoff_alt A hx0 hx1 hDpos
  have hm : 2 * s ≤ m := by
    have : 2 * s = m := by simp [s, m]; ring
    exact this.le
  have hbudget : 4 * (s : ℝ) ≤ (t : ℝ) ^ 9 := by
    convert hbudget64 using 1 <;> dsimp [s] <;> push_cast <;> ring
  have hkernelLower :=
    FourierLower.concrete_selected_lower_alt A hX1.le
      (s := s) (N := N) (m := m) hm hbudget hcut
  have hDhalf :
      c * (t : ℝ) ^ 12 / (48 * κ ^ 2) ≤
        FderivReal A (radius ((t : ℝ) ^ 9) ^ 2) / 2 := by
    calc
      c * (t : ℝ) ^ 12 / (48 * κ ^ 2) =
          (c * (t : ℝ) ^ 12 / (24 * κ ^ 2)) / 2 := by ring
      _ ≤ FderivReal A (radius ((t : ℝ) ^ 9) ^ 2) / 2 := by
        exact div_le_div_of_nonneg_right (by simpa [κ] using hD) (by norm_num)
  have hSA :
      ((t : ℝ) - 1) / 2 ≤ (positiveCountingFunction A s : ℝ) / 2 := by
    have hcast : ((t - 1 : ℕ) : ℝ) ≤ positiveCountingFunction A s := by
      exact_mod_cast hcount
    calc
      ((t : ℝ) - 1) / 2 = ((t - 1 : ℕ) : ℝ) / 2 := by
        rw [Nat.cast_sub (by omega : 1 ≤ t)]
        norm_num
      _ ≤ (positiveCountingFunction A s : ℝ) / 2 :=
        div_le_div_of_nonneg_right hcast (by norm_num)
  have hSJ : 8 * (K : ℝ) ^ 3 * (t : ℝ) ^ 3 ≤ (s : ℝ) / 2 := by
    have heq : 8 * (K : ℝ) ^ 3 * (t : ℝ) ^ 3 = (s : ℝ) / 2 := by
      dsimp [s]
      push_cast
      ring
    exact heq.le
  have hlower : a * (t : ℝ) ^ 16 ≤
      FourierLower.kernelAverage A (radius ((t : ℝ) ^ 9)) m := by
    have h := scaled_selected_lower_power_coarse
      (J := FourierLower.kernelAverage A (radius ((t : ℝ) ^ 9)) m)
      (x := (t : ℝ)) (k := (K : ℝ)) (c := c) (κ := κ)
      (D := FderivReal A (radius ((t : ℝ) ^ 9) ^ 2) / 2)
      (SA := (positiveCountingFunction A s : ℝ) / 2)
      (SJ := (s : ℝ) / 2) htR (by positivity) hc hκ hDhalf hSA hSJ hkernelLower
    simpa [a] using h
  have hP : ∀ n, ‖remainderC A c n‖ ≤ C := by
    intro n
    simpa [norm_remainderC] using hC n
  have hSum : ∀ N, summatoryC (tripleCoeff A) N =
      remainderC A c N + (c : ℂ) * (N : ℂ) :=
    summatoryC_eq_remainderC_add_main A c
  have hlam : 0 < ((t : ℝ) ^ 12)⁻¹ := by positivity
  have hupperRaw := KernelUpper.kernelAverage_radius_le
    A (remainderC A c) m hc.le hC0 hP hSum hX1 hlam
  have hmCast : (m : ℝ) = 32 * (K : ℝ) ^ 3 * (t : ℝ) ^ 3 := by
    dsimp [m]
    push_cast
    ring
  have hupperPower := scaled_specialized_upper_power_le
    (x := (t : ℝ)) (k := (K : ℝ)) (c := c) (C := C)
    (by linarith : (1 : ℝ) ≤ t) (by exact_mod_cast hK) hC0
  have hupper : FourierLower.kernelAverage A (radius ((t : ℝ) ^ 9)) m ≤
      b * (t : ℝ) ^ 15 := by
    rw [hmCast] at hupperRaw
    exact hupperRaw.trans (by simpa [b] using hupperPower)
  exact (power_sixteen_not_le_power_fifteen ha hb
    (by simpa [a, b] using htfinal) (by positivity)) (hlower.trans hupper)


end Erdos764

#print axioms Erdos764.erdos_764
