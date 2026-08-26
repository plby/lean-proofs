/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.DominatedLimit
import Mathlib.Data.Nat.Log

/-!
# Erdős 730: pointwise decay at a fixed higher prime power

This module closes the depth/limit subnode needed to specialize the generic
Tannery theorem.  For fixed `p` and `a`, the complete-block depth

`log_p (X / p^a)`

tends to infinity.  Consequently every geometric digit-density factor with
ratio in `[0,1)` tends to zero.  The final theorem instantiates the exact
ratio `(p+1)/(2p)` used by the Erdős 730 higher-power count.
-/

open Filter Topology

namespace Erdos730

/-- Complete-block digit depth at the fixed prime power `p^a`. -/
def higherPowerDepth (p a X : ℕ) : ℕ :=
  Nat.log p (X / p ^ a)

/-- For every fixed base greater than one and fixed exponent, the available
complete-block depth tends to infinity with the interval cutoff. -/
theorem tendsto_higherPowerDepth_atTop
    {p : ℕ} (hp : 1 < p) (a : ℕ) :
    Tendsto (higherPowerDepth p a) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro r
  refine ⟨p ^ (a + r), fun X hX ↦ ?_⟩
  unfold higherPowerDepth
  apply Nat.le_log_of_pow_le hp
  rw [Nat.le_div_iff_mul_le (pow_pos (by omega : 0 < p) a)]
  calc
    p ^ r * p ^ a = p ^ (a + r) := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ X := hX

/-- Geometric decay after composing any ratio in `[0,1)` with the increasing
prime-power depth. -/
theorem tendsto_pow_higherPowerDepth_zero
    {p : ℕ} (hp : 1 < p) (a : ℕ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun X ↦ ρ ^ higherPowerDepth p a X) atTop (𝓝 0) :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp
    (tendsto_higherPowerDepth_atTop hp a)

/-- The exact permitted-digit ratio `rho_p=(p+1)/(2p)`. -/
noncomputable def higherPowerRho (p : ℕ) : ℝ :=
  (p + 1 : ℝ) / (2 * p : ℝ)

theorem higherPowerRho_nonneg (p : ℕ) : 0 ≤ higherPowerRho p := by
  unfold higherPowerRho
  positivity

theorem higherPowerRho_lt_one {p : ℕ} (hp : 1 < p) :
    higherPowerRho p < 1 := by
  unfold higherPowerRho
  rw [div_lt_one (by positivity : (0 : ℝ) < 2 * p)]
  exact_mod_cast (show p + 1 < 2 * p by omega)

/-- Pointwise vanishing of the normalized first term in equation (26), for a
fixed prime and exponent. -/
theorem tendsto_higherPower_normalizedTerm_zero
    {p : ℕ} (hp : p.Prime) (a : ℕ) :
    Tendsto
      (fun X ↦ (2 / (p : ℝ) ^ a) *
        higherPowerRho p ^ higherPowerDepth p a X)
      atTop (𝓝 0) := by
  simpa only [mul_zero] using
    (tendsto_pow_higherPowerDepth_zero hp.one_lt a
      (higherPowerRho_nonneg p) (higherPowerRho_lt_one hp.one_lt)).const_mul
      (2 / (p : ℝ) ^ a)

#print axioms tendsto_higherPowerDepth_atTop
#print axioms tendsto_pow_higherPowerDepth_zero
#print axioms higherPowerRho_lt_one
#print axioms tendsto_higherPower_normalizedTerm_zero

end Erdos730
