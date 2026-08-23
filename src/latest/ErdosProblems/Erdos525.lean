/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 525.
https://www.erdosproblems.com/forum/thread/525

Informal authors:
- Nicholas A. Cook
- Hoi H. Nguyen

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos525.md
-/
import ErdosProblems.Erdos525.EvenLaw
import ErdosProblems.Erdos525.OddLaw

/-!
# Erdős Problem 525

For a sign vector `ε : SignVector N`, `littlewoodEval ε` is the degree-`N`
polynomial with coefficients in `{−1, 1}`, and `minModulus ε` is its minimum
modulus on the unit circle.  This file assembles the even- and odd-degree
Cook--Nguyen limits proved in the supporting modules, translates their
centered normalization to the degree normalization, and records both parts of
the resolution of Erdős Problem 525.
-/

open scoped Topology

namespace Erdos525

open Asymptotics Filter

/-- The bandwidth conversion used by the odd-degree integer-frequency model
converges to the identity. -/
lemma oddBandwidthParameter_tendsto (u : ℝ) :
    Tendsto (fun n : ℕ ↦ u * n / (n + 1 / 2 : ℝ)) atTop (𝓝 u) := by
  have hden : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1 / 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 / 2 : ℝ)
      tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1 / 2)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp hden).congr'
      (Eventually.of_forall fun _ ↦ rfl)
  have hratio : Tendsto (fun n : ℕ ↦
      1 - (1 / 2 : ℝ) * ((n : ℝ) + 1 / 2)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hinv.const_mul (1 / 2 : ℝ))
  have hscaled := hratio.const_mul u
  have hscaled' : Tendsto (fun n : ℕ ↦
      u * (1 - (1 / 2 : ℝ) * ((n : ℝ) + 1 / 2)⁻¹)) atTop (𝓝 u) := by
    simpa using hscaled
  apply hscaled'.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  have hden_ne : (n : ℝ) + 1 / 2 ≠ 0 := by positivity
  field_simp
  ring

/-- Odd-degree counterpart of `centeredTail_tendsto`, expressed in the
half-integer-centered normalization used by the public parity recombination.
-/
theorem oddCenteredTail_tendsto (u : ℝ) (hu : 0 < u) :
    Tendsto (fun n : ℕ ↦ oddCenteredTail n u) atTop
      (𝓝 (Real.exp (-2 * rate * u))) := by
  have hmove := tendsto_antitone_moving Odd.tail
    (fun v ↦ Real.exp (-2 * rate * v))
    (fun n : ℕ ↦ u * n / (n + 1 / 2 : ℝ)) u
    Odd.tail_antitone Odd.tail_tendsto (by fun_prop)
    (oddBandwidthParameter_tendsto u) hu
  apply hmove.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  exact (Odd.oddCenteredTail_eq_tail n hn u).symm

/-- The complete centered limiting law, with both parity classes included. -/
theorem centeredLimitingLaw : CenteredLimitingLaw := by
  constructor
  · exact centeredTail_tendsto
  · exact oddCenteredTail_tendsto

/-- **Cook--Nguyen limiting distribution for Erdős Problem 525.**

For every fixed positive `τ`, the proportion of degree-`N` sign polynomials
whose minimum modulus exceeds `τ / √N` tends to
`exp (−sqrt (π / 12) * τ)`.
-/
theorem erdos_525_limiting_distribution :
    ∀ τ : ℝ, 0 < τ →
      Tendsto (fun N : ℕ ↦ minimumTail N τ) atTop
        (𝓝 (Real.exp (-rate * τ))) :=
  limitingLaw_of_centeredLimitingLaw centeredLimitingLaw

/-- **Affirmative answer to the first question in Erdős Problem 525.**

The number of degree-`N` sign polynomials having no point of modulus strictly
below one on the unit circle is `o(2^N)`.
-/
theorem erdos_525_exceptional_family_isLittleO :
    IsLittleO atTop
      (fun N : ℕ ↦ ((exceptionalFamily N).card : ℝ))
      (fun N : ℕ ↦ (2 : ℝ) ^ N) :=
  exceptionalFamily_isLittleO_of_limitingLaw
    erdos_525_limiting_distribution

/-- Equivalent probability form of the affirmative answer: a uniformly
chosen degree-`N` sign polynomial has a unit-circle value of modulus below one
with probability tending to one. -/
theorem erdos_525_hasSmallValue_probability_tendsto_one :
    Tendsto
      (fun N : ℕ ↦
        uniformProbability (fun ε : SignVector N ↦ HasSmallValue ε))
      atTop (𝓝 1) :=
  hasSmallValue_probability_tendsto_one_of_limitingLaw
    erdos_525_limiting_distribution

/-- The full resolution: the exact limiting law, its `o(2^N)` counting
consequence, and the literal unit-circle small-value probability statement. -/
theorem erdos_525_resolution :
    (∀ τ : ℝ, 0 < τ →
      Tendsto (fun N : ℕ ↦ minimumTail N τ) atTop
        (𝓝 (Real.exp (-rate * τ)))) ∧
    IsLittleO atTop
      (fun N : ℕ ↦ ((exceptionalFamily N).card : ℝ))
      (fun N : ℕ ↦ (2 : ℝ) ^ N) ∧
    Tendsto
      (fun N : ℕ ↦
        uniformProbability (fun ε : SignVector N ↦ HasSmallValue ε))
      atTop (𝓝 1) :=
  ⟨erdos_525_limiting_distribution,
    erdos_525_exceptional_family_isLittleO,
    erdos_525_hasSmallValue_probability_tendsto_one⟩

#print axioms erdos_525_resolution

end Erdos525
