import ErdosProblems.Erdos402.LargeSieve

/-!
# A uniform sieve bound for rough affine values

The proved additive large sieve gives a count with an arbitrary cutoff.
The constant coefficient may be any integer, and the slope enters only
through its totient ratio. This is the counting input for the smooth-part
decomposition of the short-progression Delta sum.
-/

namespace Erdos587

theorem delta_rough_affine_nat_slope_card_le {B Q : ℕ} (hB : 0 < B) (hQ : 0 < Q)
    (S : Finset ℕ) (a H : ℕ) (A : ℤ) (hS : S ⊆ Finset.Ioc a (a + H))
    (hrough : ∀ n ∈ S, ∀ p : ℕ, p.Prime → p ≤ Q → ¬ (p : ℤ) ∣ A + B * n) :
    (S.card : ℝ) ≤ (B : ℝ) / B.totient *
      ((H : ℝ) + (Q : ℝ) ^ 2) / Real.log (Q + 1 : ℕ) := by
  let L : ℕ := Q.factorial
  let c : ℕ := (A % (L : ℤ)).toNat
  have hL : (L : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero Q
  have hc : (c : ℤ) = A % (L : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ hL)
  apply Erdos402.Sieve.card_le_log_bound hB hQ S a H c hS
  intro n hn d hd
  by_contra hcop
  obtain ⟨p, hp, hpn, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hpQ : p ≤ Q := (Nat.le_of_dvd (Finset.mem_Icc.mp hd).1 hpd).trans (Finset.mem_Icc.mp hd).2
  have hpL : (p : ℤ) ∣ (L : ℤ) := by
    exact_mod_cast Nat.dvd_factorial hp.pos hpQ
  have hpnZ : (p : ℤ) ∣ (c : ℤ) + B * n := by exact_mod_cast hpn
  apply hrough n hn p hp hpQ
  have heq : A + (B : ℤ) * n = ((c : ℤ) + B * n) + L * (A / L) := by
    rw [hc]
    have he := Int.emod_add_mul_ediv A (L : ℤ)
    linarith
  rw [heq]
  exact dvd_add hpnZ (dvd_mul_of_dvd_left hpL _)

/-- Signed affine coefficients cost no extra factor: negating both
coefficients preserves prime divisibility and makes the slope positive. -/
theorem delta_rough_affine_card_le {B : ℤ} (hB : B ≠ 0) {Q : ℕ} (hQ : 0 < Q)
    (S : Finset ℕ) (a H : ℕ) (A : ℤ) (hS : S ⊆ Finset.Ioc a (a + H))
    (hrough : ∀ n ∈ S, ∀ p : ℕ, p.Prime → p ≤ Q → ¬ (p : ℤ) ∣ A + B * n) :
    (S.card : ℝ) ≤ (B.natAbs : ℝ) / B.natAbs.totient *
      ((H : ℝ) + (Q : ℝ) ^ 2) / Real.log (Q + 1 : ℕ) := by
  have hBabs : 0 < B.natAbs := Int.natAbs_pos.mpr hB
  by_cases hBpos : 0 ≤ B
  · apply delta_rough_affine_nat_slope_card_le hBabs hQ S a H A hS
    simpa only [Int.natCast_natAbs, abs_of_nonneg hBpos] using hrough
  · apply delta_rough_affine_nat_slope_card_le hBabs hQ S a H (-A) hS
    intro n hn p hp hpQ hdiv
    apply hrough n hn p hp hpQ
    have heq : -A + (B.natAbs : ℤ) * n = -(A + B * n) := by
      rw [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hBpos)]
      ring
    rwa [heq, dvd_neg] at hdiv

/-- If the sieve cutoff has square at most the interval length, the
remainder is absorbed without dependence on either affine coefficient. -/
theorem delta_rough_affine_card_le_two {B : ℤ} (hB : B ≠ 0) {Q : ℕ} (hQ : 0 < Q)
    (S : Finset ℕ) (a H : ℕ) (A : ℤ) (hS : S ⊆ Finset.Ioc a (a + H))
    (hrough : ∀ n ∈ S, ∀ p : ℕ, p.Prime → p ≤ Q → ¬ (p : ℤ) ∣ A + B * n)
    (hcut : Q ^ 2 ≤ H) :
    (S.card : ℝ) ≤ 2 * ((B.natAbs : ℝ) / B.natAbs.totient) * H /
      Real.log (Q + 1 : ℕ) := by
  have hcutR : (Q : ℝ) ^ 2 ≤ H := by exact_mod_cast hcut
  calc
    _ ≤ (B.natAbs : ℝ) / B.natAbs.totient *
        ((H : ℝ) + (Q : ℝ) ^ 2) / Real.log (Q + 1 : ℕ) :=
      delta_rough_affine_card_le hB hQ S a H A hS hrough
    _ ≤ (B.natAbs : ℝ) / B.natAbs.totient * (2 * H) / Real.log (Q + 1 : ℕ) := by
      apply div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q + 1 by omega))
    _ = _ := by ring

end Erdos587
