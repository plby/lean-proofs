/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTHarmonicCorrectionMoments
import ErdosProblems.Erdos4b.FGKMTBoundarySigned

/-!
# The signed harmonic main constant

For the denominators occurring in the sieve, `g p ≤ p - 1` at every
rough prime. Each signed rough Euler factor is therefore at least one.
The checked absolute moments give the upper bound, and the exact signed
boundary sum supplies the totient density. All constants are uniform in
the dimension and in the pre-sieve modulus.
-/

namespace Erdos4b.FGKMT

noncomputable section

open ArithmeticFunction Filter
open scoped BigOperators Topology

def sieveMainConstant (M : ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑' n, harmonicCorrection (roughSieveWeight M g) n

theorem roughHarmonicCorrection_local_tsum (M : ℕ) (g : ℕ → ℝ)
    {p : ℕ} (hp : p.Prime) :
    (∑' j, roughHarmonicCorrection M g (p ^ j)) =
      if p ∣ M then 1 else (1 + 1 / g p) * (1 - 1 / (p : ℝ)) := by
  rw [tsum_eq_sum (s := Finset.range 3) (fun j hj => by
    have hj3 : 3 ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
    exact roughHarmonicCorrection_prime_pow_ge_three M g hp hj3)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
    zero_add]
  rw [(roughHarmonicCorrection_isMultiplicative M g).map_one,
    roughHarmonicCorrection_prime M g hp, roughHarmonicCorrection_prime_sq M g hp]
  by_cases hpM : p ∣ M
  · simp only [if_pos hpM, add_zero]
  · simp only [if_neg hpM, one_div, mul_inv_rev]
    ring

theorem one_le_roughHarmonicCorrection_local_tsum {M p : ℕ} {g : ℕ → ℝ}
    (hp : p.Prime) (hg : ¬p ∣ M → 0 < g p) (hupper : ¬p ∣ M → g p ≤ p - 1) :
    1 ≤ ∑' j, roughHarmonicCorrection M g (p ^ j) := by
  rw [roughHarmonicCorrection_local_tsum M g hp]
  by_cases hpM : p ∣ M
  · rw [if_pos hpM]
  · rw [if_neg hpM]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hg0 := hg hpM
    have hidentity : (1 + 1 / g p) * (1 - 1 / (p : ℝ)) =
        1 + ((p : ℝ) - 1 - g p) / ((p : ℝ) * g p) := by
      field_simp [hp0.ne', hg0.ne']
      ring
    rw [hidentity]
    have hnonneg : 0 ≤ ((p : ℝ) - 1 - g p) / ((p : ℝ) * g p) :=
      div_nonneg (sub_nonneg.mpr (hupper hpM)) (mul_pos hp0 hg0).le
    linarith

theorem one_le_roughHarmonicCorrection_tsum {M : ℕ} {g : ℕ → ℝ}
    (hs : Summable (fun n => |roughHarmonicCorrection M g n|))
    (hg : ∀ p : ℕ, p.Prime → ¬p ∣ M → 0 < g p)
    (hupper : ∀ p : ℕ, p.Prime → ¬p ∣ M → g p ≤ p - 1) :
    1 ≤ ∑' n, roughHarmonicCorrection M g n := by
  have hnorm : Summable (fun n => ‖roughHarmonicCorrection M g n‖) := by
    simpa only [Real.norm_eq_abs] using hs
  apply ge_of_tendsto' ((roughHarmonicCorrection_isMultiplicative M g).eulerProduct hnorm)
  intro N
  apply Finset.one_le_prod
  intro p hp
  have hpPrime := Nat.prime_of_mem_primesBelow hp
  exact one_le_roughHarmonicCorrection_local_tsum hpPrime (hg p hpPrime) (hupper p hpPrime)

theorem sieveMainConstant_eq_rough_tsum_mul_totientDensity {M : ℕ} (hM : 0 < M)
    (g : ℕ → ℝ) (hs : Summable (fun n => |roughHarmonicCorrection M g n|)) :
    sieveMainConstant M g =
      (∑' n, roughHarmonicCorrection M g n) * ((M.totient : ℝ) / M) := by
  unfold sieveMainConstant
  simp only [harmonicCorrection_roughSieveWeight_eq]
  rw [(arithmetic_mul_hasSum _ _ hs (preSieveBoundary_absolute_sum_bound hM.ne').1).tsum_eq,
    preSieveBoundary_tsum_eq_totientDensity hM]

theorem sieveMainConstant_bounds {k M : ℕ} (hk : 0 < k) (hM : 0 < M)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) (g : ℕ → ℝ)
    (hg : ∀ p : ℕ, p.Prime → ¬p ∣ M → (p : ℝ) / 2 ≤ g p)
    (hclose : ∀ p : ℕ, p.Prime → ¬p ∣ M → |g p - p| ≤ 2 * (k : ℝ))
    (hupper : ∀ p : ℕ, p.Prime → ¬p ∣ M → g p ≤ p - 1) :
    (M.totient : ℝ) / M ≤ sieveMainConstant M g ∧
      sieveMainConstant M g ≤ Real.exp 12 * ((M.totient : ℝ) / M) := by
  obtain ⟨hs, hA, _, _⟩ := roughHarmonicCorrection_moments hk hsmall g hg hclose
  have hsigned : Summable (fun n => roughHarmonicCorrection M g n) := hs.of_abs
  have hlower : 1 ≤ ∑' n, roughHarmonicCorrection M g n := by
    apply one_le_roughHarmonicCorrection_tsum hs _ hupper
    intro p hp hpM
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact (half_pos hp0).trans_le (hg p hp hpM)
  have hsumUpper : (∑' n, roughHarmonicCorrection M g n) ≤ Real.exp 12 :=
    (Summable.tsum_le_tsum (fun n => le_abs_self _) hsigned hs).trans hA
  rw [sieveMainConstant_eq_rough_tsum_mul_totientDensity hM g hs]
  have hrho : (0 : ℝ) ≤ (M.totient : ℝ) / M := by positivity
  constructor
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hlower hrho
  · exact mul_le_mul_of_nonneg_right hsumUpper hrho

theorem sieveMainConstant_pos {k M : ℕ} (hk : 0 < k) (hM : 0 < M)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) (g : ℕ → ℝ)
    (hg : ∀ p : ℕ, p.Prime → ¬p ∣ M → (p : ℝ) / 2 ≤ g p)
    (hclose : ∀ p : ℕ, p.Prime → ¬p ∣ M → |g p - p| ≤ 2 * (k : ℝ))
    (hupper : ∀ p : ℕ, p.Prime → ¬p ∣ M → g p ≤ p - 1) :
    0 < sieveMainConstant M g := by
  have hrho : (0 : ℝ) < (M.totient : ℝ) / M :=
    div_pos (by exact_mod_cast Nat.totient_pos.mpr hM) (by exact_mod_cast hM)
  exact hrho.trans_le (sieveMainConstant_bounds hk hM hsmall g hg hclose hupper).1

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sieveMainConstant_bounds
#print axioms Erdos4b.FGKMT.sieveMainConstant_pos
