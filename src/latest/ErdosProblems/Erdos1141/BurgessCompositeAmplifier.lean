import ErdosProblems.Erdos1141.BurgessScaleEstimates
import ErdosProblems.Erdos1141.BurgessDenominatorAsymptotics

/-!
# The Burgess amplifier on power scales
-/

namespace Pollack17.Burgess

open scoped BigOperators

theorem abs_productChar_natCast_of_coprime (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (u : ℕ) (hu : u.Coprime (primeModulus s)) : |productChar s hs u| = 1 := by
  classical
  rw [productChar, Finset.abs_prod]
  apply Finset.prod_eq_one
  intro p _
  have : Fact (Nat.Prime (p : ℕ)) := ⟨hs p p.property⟩
  have hcop : u.Coprime (p : ℕ) := hu.of_dvd_right (Finset.dvd_prod_of_mem id p.property)
  have hnz : (u : ZMod (p : ℕ)) ≠ 0 := by
    intro hz
    exact ((hs p p.property).coprime_iff_not_dvd.mp hcop.symm)
      ((ZMod.natCast_eq_zero_iff u (p : ℕ)).mp hz)
  rw [primeCRT_natCast]
  rcases quadraticChar_dichotomy hnz with h | h <;> simp [localChar, qchar, h]

theorem productChar_amplified_abs_le (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeModulus s)] {M H U V : ℕ} (hUV : U * V ≤ H) :
    ((coprimeDenominators s U).card : ℝ) * V *
        |∑ i ∈ Finset.range H, productChar s hs (M + i : ℕ)| ≤
      amplifierNumerator (productChar s hs) M H (coprimeDenominators s U) V +
        2 * ((coprimeDenominators s U).card : ℝ) * V * (U * V) := by
  exact amplified_abs_le (productChar s hs) (productChar_mul s hs)
    (abs_productChar_le_one s hs) (coprimeDenominators s U) (Finset.filter_subset _ _)
    (fun _ h => (Finset.mem_filter.mp h).2)
    (fun u h => abs_productChar_natCast_of_coprime s hs u (Finset.mem_filter.mp h).2) hUV

theorem amplifier_scale_le {q : ℕ} [NeZero q] (hq : 1 ≤ q)
    (f : ZMod q → ℝ) (M H U V k : ℕ) (D : Finset ℕ)
    (hD : D ⊆ Finset.Icc 1 U) (hcop : ∀ u ∈ D, u.Coprime q)
    (hH0 : 0 < H) (hU0 : 0 < U) (hsmall : 2 * (U * H) < q)
    {c u v δ : ℝ} (hu1 : u ≤ 1) (huδ : u ≤ c + δ)
    (hH : (H : ℝ) ≤ (q : ℝ) ^ c) (hU : (U : ℝ) ≤ (q : ℝ) ^ u)
    (hV : (V : ℝ) ≤ 2 * (q : ℝ) ^ v) (hv : v * (k + 1 : ℝ) = 1 / 2)
    (hlog : 1 + Real.log (q : ℝ) ≤ (q : ℝ) ^ δ)
    (hmoment : (∑ x : ZMod q, naturalShiftSum f V x ^ (2 * (k + 1))) ≤
      (q : ℝ) ^ δ * ((q : ℝ) * (V : ℝ) ^ (k + 1) +
        Real.sqrt q * (V : ℝ) ^ (2 * (k + 1)))) :
    amplifierNumerator f M H D V ^ (2 * (k + 1)) ≤
      (2 * ((2 : ℝ) ^ (k + 1) + 2 ^ (2 * (k + 1)))) *
        (q : ℝ) ^ ((c + u) * (2 * k + 1 : ℕ) + 3 / 2 + 3 * δ) := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  have hcard : (D.card : ℝ) ≤ U := by
    exact_mod_cast (Finset.card_le_card hD).trans_eq (by simp)
  have hHD : (H : ℝ) * D.card ≤ (q : ℝ) ^ (c + u) := by
    rw [Real.rpow_add hq0]
    exact mul_le_mul hH (hcard.trans hU) (Nat.cast_nonneg _) (Real.rpow_nonneg hq0.le _)
  have hpHD : ((H : ℝ) * D.card) ^ (2 * k) ≤ (q : ℝ) ^ ((c + u) * (2 * k : ℕ)) := by
    simpa only [one_mul, one_pow] using pow_le_scaled_rpow
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hq0.le
      (show (H : ℝ) * D.card ≤ 1 * (q : ℝ) ^ (c + u) by simpa only [one_mul] using hHD) (2 * k)
  have he := (naturalRatioEnergy_le (M := M) D hD hcop hH0 hU0 hsmall).trans
    (harmonic_energy_scale_le hq hU0 hu1 huδ hH hU hlog)
  have hm := hmoment.trans (moment_scale_le (by omega : 0 < q)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hv) hV)
  have hh := amplifierNumerator_even_power_le f M H D V k
  have he0 : 0 ≤ naturalRatioEnergy q M H D :=
    Finset.sum_nonneg fun x _ => sq_nonneg _
  have hm0 : 0 ≤ ∑ x : ZMod q, naturalShiftSum f V x ^ (2 * (k + 1)) :=
    Finset.sum_nonneg fun x _ => (even_two_mul _).pow_nonneg _
  calc
    _ ≤ ((H : ℝ) * D.card) ^ (2 * k) * naturalRatioEnergy q M H D *
        ∑ x : ZMod q, naturalShiftSum f V x ^ (2 * (k + 1)) := hh
    _ ≤ (q : ℝ) ^ ((c + u) * (2 * k : ℕ)) *
        (2 * (q : ℝ) ^ (c + u + 2 * δ)) *
        (((2 : ℝ) ^ (k + 1) + 2 ^ (2 * (k + 1))) * (q : ℝ) ^ (3 / 2 + δ)) := by
      exact mul_le_mul (mul_le_mul hpHD he he0 (Real.rpow_nonneg hq0.le _)) hm hm0
        (by positivity)
    _ = (2 * ((2 : ℝ) ^ (k + 1) + 2 ^ (2 * (k + 1)))) *
        ((q : ℝ) ^ ((c + u) * (2 * k : ℕ)) *
          (q : ℝ) ^ (c + u + 2 * δ) * (q : ℝ) ^ (3 / 2 + δ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]
      congr 2
      push_cast
      ring

end Pollack17.Burgess
