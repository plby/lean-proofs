import ErdosProblems.Erdos67b.PrimeGraph
import ErdosProblems.Erdos67b.LogEntropyConcentration
import Mathlib.NumberTheory.Chebyshev

/-!
# Exponentially rare prime-graph deviations

Discharge the finite Hoeffding budget with elementary Chebyshev and
logarithmic growth, retaining uniformity over all bounded blocks.
-/

open scoped BigOperators
open Filter Finset

namespace Erdos67b

noncomputable section

theorem eventually_primeCounting_le_four_mul_div_log :
    ∀ᶠ H : ℕ in atTop, (Nat.primeCounting H : ℝ) ≤ 4 * ((H : ℝ) / Real.log H) := by
  have hnat : Tendsto (fun H : ℕ ↦ (H : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hprime := hnat.eventually
    (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hprime, eventually_ge_atTop 2] with H hp hH
  have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  have hfour : Real.log 4 + 1 ≤ (4 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hp' : (Nat.primeCounting H : ℝ) ≤ (Real.log 4 + 1) * H / Real.log H := by
    simpa only [Nat.floor_natCast] using hp
  exact hp'.trans (by rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_right hfour (by positivity))

theorem eventually_log_four_le_mul_nat_div_log {c : ℝ} (hc : 0 < c) :
    ∀ᶠ H : ℕ in atTop, Real.log 4 ≤ c * ((H : ℝ) / Real.log H) := by
  have hlogfour : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hnat : Tendsto (fun H : ℕ ↦ (H : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsmall := hnat.eventually (Real.isLittleO_log_id_atTop.bound (div_pos hc hlogfour))
  filter_upwards [hsmall, eventually_ge_atTop 2] with H hsmall hH
  have hHr : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  have hsmall' : Real.log (H : ℝ) ≤ (c / Real.log 4) * H := by
    simpa only [Real.norm_eq_abs, abs_of_pos hlog, abs_of_pos hHr, id_eq] using hsmall
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hlog).mpr
  have h := mul_le_mul_of_nonneg_right hsmall' hlogfour.le
  have heq : ((c / Real.log 4) * (H : ℝ)) * Real.log 4 = c * H := by
    field_simp
  rw [heq] at h
  simpa only [mul_comm] using h

theorem primeGraphRadius_pos {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) :
    0 < primeGraphRadius B δ := by
  unfold primeGraphRadius
  positivity

/-- The scalar budget behind the graph's `H/log H` tail rate. -/
theorem primeGraph_tail_scalar_budget {N T R ρ : ℝ}
    (hN : 0 < N) (hT : 0 < T) (hR : 0 < R) (hρ : 0 < ρ)
    (hcount : N ≤ 4 * T)
    (hlarge : Real.log 4 ≤ (ρ ^ 2 / (64 * R ^ 2)) * T) :
    (ρ ^ 2 / (64 * R ^ 2)) * T + Real.log 4 ≤
      (ρ * T) ^ 2 / (8 * N * R ^ 2) := by
  let c := ρ ^ 2 / (64 * R ^ 2)
  have hc : 0 < c := by dsimp [c]; positivity
  have hden : 8 * N * R ^ 2 ≤ 32 * T * R ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hcount (sq_nonneg R)
    nlinarith
  have hcalc : (2 * c * T) * (32 * T * R ^ 2) = (ρ * T) ^ 2 := by
    dsimp [c]
    field_simp
    ring
  have hmid : 2 * c * T ≤ (ρ * T) ^ 2 / (8 * N * R ^ 2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      (2 * c * T) * (8 * N * R ^ 2) ≤ (2 * c * T) * (32 * T * R ^ 2) :=
        mul_le_mul_of_nonneg_left hden (by positivity)
      _ = (ρ * T) ^ 2 := hcalc
  change c * T + Real.log 4 ≤ _
  change Real.log 4 ≤ c * T at hlarge
  linarith

/-- Uniform graph concentration with no unproved counting or analytic
input. The constant and lower scale are chosen before the block. -/
theorem exists_primeGraph_exponential_tail {B δ ρ : ℝ}
    (hB : 0 < B) (hδ : 0 < δ) (hρ : 0 < ρ) :
    ∃ c : ℝ, 0 < c ∧ ∃ H₁ : ℕ, 2 ≤ H₁ ∧ ∀ H : ℕ, H₁ ≤ H →
      ∀ (b : Fin H → ℂ) (h : ℕ) (s : Finset ℕ),
        (∀ j, ‖b j‖ ≤ B) → (∀ p ∈ s, δ * H ≤ p) →
        ((Finset.univ.filter fun z : ZMod (primeGraphModulus H) ↦
          ρ * H / Real.log H ≤ ‖primeGraphSum b h s z - primeGraphMean b h s‖).card : ℝ) *
          Real.exp (c * H / Real.log H) ≤ primeGraphModulus H := by
  let R := primeGraphRadius B δ
  have hR : 0 < R := primeGraphRadius_pos hB hδ
  let c := ρ ^ 2 / (64 * R ^ 2)
  have hc : 0 < c := by dsimp [c]; positivity
  have hlarge := eventually_log_four_le_mul_nat_div_log hc
  have hevent : ∀ᶠ H : ℕ in atTop, 2 ≤ H ∧
      (Nat.primeCounting H : ℝ) ≤ 4 * ((H : ℝ) / Real.log H) ∧
      Real.log 4 ≤ c * ((H : ℝ) / Real.log H) := by
    filter_upwards [eventually_ge_atTop 2, eventually_primeCounting_le_four_mul_div_log, hlarge]
      with H hH hp hlarge
    exact ⟨hH, hp, hlarge⟩
  obtain ⟨H₁, hH₁⟩ := eventually_atTop.mp hevent
  refine ⟨c, hc, max 2 H₁, le_max_left _ _, ?_⟩
  intro H hH b h s hb hs
  obtain ⟨hHtwo, hcount, hlarge⟩ := hH₁ H ((le_max_right _ _).trans hH)
  have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  have hT : 0 < (H : ℝ) / Real.log H := div_pos (by positivity) hlog
  have hN : (0 : ℝ) < Nat.primeCounting H := by
    exact_mod_cast (card_primeGraphIndex H ▸ primeGraphIndex_card_pos hHtwo)
  apply primeGraph_tail_card_mul_exp_le b h s hB.le hδ hb hs (by positivity)
  have hbudget := primeGraph_tail_scalar_budget hN hT hR hρ hcount hlarge
  simpa only [c, R, mul_div_assoc] using hbudget

end

end Erdos67b
