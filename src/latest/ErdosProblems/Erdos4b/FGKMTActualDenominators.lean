/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTMainConstant

/-!
# The actual shifted and pinned sieve denominators

The coordinate-summation recursion only uses shifts `s < k`. This
strict inequality gives the upper bound `g p ≤ p - 1`, so the signed
main-constant comparison applies to every denominator in the recursion.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem shiftedDenominator_bounds {k s : ℕ} (hk : 2 ≤ k) (hs : s < k)
    {p : ℝ} (hp : 2 * (k : ℝ) ^ 2 < p) :
    p / 2 ≤ p - k + s ∧ |p - k + s - p| ≤ 2 * (k : ℝ) ∧
      p - k + s ≤ p - 1 := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hsR : (s : ℝ) + 1 ≤ k := by exact_mod_cast hs
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hhalf := (rough_real_bounds hkR hp).2
  refine ⟨by linarith, ?_, by linarith⟩
  rw [abs_of_nonpos (by linarith : p - k + s - p ≤ 0)]
  linarith

theorem pinnedShiftedDenominator_bounds {k s : ℕ} (hk : 2 ≤ k) (hs : s < k)
    {p : ℝ} (hp : 2 * (k : ℝ) ^ 2 < p) :
    p / 2 ≤ pinnedLocalDenominator k p + s ∧
      |pinnedLocalDenominator k p + s - p| ≤ 2 * (k : ℝ) ∧
      pinnedLocalDenominator k p + s ≤ p - 1 := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hsR : (s : ℝ) + 1 ≤ k := by exact_mod_cast hs
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  obtain ⟨hp1, hhalf⟩ := rough_real_bounds hkR hp
  have hpk : (k : ℝ) < p := by linarith
  have hquot : 0 ≤ ((k : ℝ) - 1) / (p - 1) :=
    div_nonneg (by linarith) (by linarith)
  have hupper : pinnedLocalDenominator k p + s ≤ p - 1 := by
    rw [pinnedLocalDenominator_eq hp1.ne' hpk.ne']
    linarith
  obtain ⟨hden, hclose⟩ := pinnedLocalDenominator_bounds hkR hp
  refine ⟨by linarith, ?_, hupper⟩
  rw [abs_le] at hclose ⊢
  constructor <;> linarith

theorem shiftedDenominator_mainConstant_bounds {k M s : ℕ}
    (hk : 2 ≤ k) (hM : 0 < M) (hs : s < k)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) :
    (M.totient : ℝ) / M ≤ sieveMainConstant M (fun p => (p : ℝ) - k + s) ∧
      sieveMainConstant M (fun p => (p : ℝ) - k + s) ≤
        Real.exp 12 * ((M.totient : ℝ) / M) := by
  have hbounds : ∀ p : ℕ, p.Prime → ¬p ∣ M →
      (p : ℝ) / 2 ≤ (p : ℝ) - k + s ∧
        |(p : ℝ) - k + s - p| ≤ 2 * (k : ℝ) ∧
        (p : ℝ) - k + s ≤ p - 1 := by
    intro p hp hpM
    have hrough : 2 * k ^ 2 < p := by
      by_contra hnot
      exact hpM (hsmall p hp (by omega))
    exact shiftedDenominator_bounds hk hs (by exact_mod_cast hrough)
  exact sieveMainConstant_bounds (by omega : 0 < k) hM
    (fun p hp hpk => hsmall p hp (by omega)) _
    (fun p hp hpM => (hbounds p hp hpM).1)
    (fun p hp hpM => (hbounds p hp hpM).2.1)
    (fun p hp hpM => (hbounds p hp hpM).2.2)

theorem pinnedShiftedDenominator_mainConstant_bounds {k M s : ℕ}
    (hk : 2 ≤ k) (hM : 0 < M) (hs : s < k)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) :
    (M.totient : ℝ) / M ≤
        sieveMainConstant M (fun p => pinnedLocalDenominator k p + s) ∧
      sieveMainConstant M (fun p => pinnedLocalDenominator k p + s) ≤
        Real.exp 12 * ((M.totient : ℝ) / M) := by
  have hbounds : ∀ p : ℕ, p.Prime → ¬p ∣ M →
      (p : ℝ) / 2 ≤ pinnedLocalDenominator k p + s ∧
        |pinnedLocalDenominator k p + s - p| ≤ 2 * (k : ℝ) ∧
        pinnedLocalDenominator k p + s ≤ p - 1 := by
    intro p hp hpM
    have hrough : 2 * k ^ 2 < p := by
      by_contra hnot
      exact hpM (hsmall p hp (by omega))
    exact pinnedShiftedDenominator_bounds hk hs (by exact_mod_cast hrough)
  exact sieveMainConstant_bounds (by omega : 0 < k) hM
    (fun p hp hpk => hsmall p hp (by omega)) _
    (fun p hp hpM => (hbounds p hp hpM).1)
    (fun p hp hpM => (hbounds p hp hpM).2.1)
    (fun p hp hpM => (hbounds p hp hpM).2.2)

theorem roughSieveWeight_relative_cumulative_error_le {k M N : ℕ}
    (hk : 0 < k) (hM : 0 < M) (hN : 1 ≤ N)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) (g : ℕ → ℝ)
    (hg : ∀ p : ℕ, p.Prime → ¬p ∣ M → (p : ℝ) / 2 ≤ g p)
    (hclose : ∀ p : ℕ, p.Prime → ¬p ∣ M → |g p - p| ≤ 2 * (k : ℝ))
    (hupper : ∀ p : ℕ, p.Prime → ¬p ∣ M → g p ≤ p - 1) :
    |(∑ n ∈ Finset.Ioc 0 N, roughSieveWeight M g n) -
      sieveMainConstant M g * Real.log N| / sieveMainConstant M g ≤
        Real.exp 12 * ((M : ℝ) / M.totient) ^ 2 *
          (5 + ∑ p ∈ M.primeFactors, Real.log p / (p : ℝ)) := by
  have hc := sieveMainConstant_pos hk hM hsmall g hg hclose hupper
  have hlower := (sieveMainConstant_bounds hk hM hsmall g hg hclose hupper).1
  have hphi : (0 : ℝ) < M.totient := by exact_mod_cast Nat.totient_pos.mpr hM
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hnonneg : 0 ≤ Real.exp 12 * ((M : ℝ) / M.totient) *
      (5 + ∑ p ∈ M.primeFactors, Real.log p / (p : ℝ)) := by positivity
  calc
    _ ≤ (Real.exp 12 * ((M : ℝ) / M.totient) *
          (5 + ∑ p ∈ M.primeFactors, Real.log p / (p : ℝ))) / sieveMainConstant M g :=
      div_le_div_of_nonneg_right
        (roughSieveWeight_cumulative_error_le hk hM hN hsmall g hg hclose) hc.le
    _ ≤ (Real.exp 12 * ((M : ℝ) / M.totient) *
          (5 + ∑ p ∈ M.primeFactors, Real.log p / (p : ℝ))) /
            ((M.totient : ℝ) / M) :=
      div_le_div_of_nonneg_left hnonneg (div_pos hphi hMR) hlower
    _ = _ := by field_simp

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.pinnedShiftedDenominator_mainConstant_bounds
#print axioms Erdos4b.FGKMT.roughSieveWeight_relative_cumulative_error_le
