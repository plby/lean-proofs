import UnitFractions.ForMathlib.BasicEstimates
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.ZMod.Basic

/-! Polynomially bounded admissible shifts, with elementary prime supply. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Filter Asymptotics

theorem eventually_twice_le_primeCounting_square :
    ∀ᶠ k : ℕ in atTop, 2 * k ≤ Nat.primeCounting (k ^ 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound (show 0 < Real.log 2 / 8 by positivity)
  filter_upwards [hsmall, eventually_ge_atTop 2] with k hsmall hk
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_natCast_nonneg k
  have hsmall' : Real.log (k : ℝ) ≤ (Real.log 2 / 8) * (k : ℝ) := by
    simpa only [Function.comp_apply, Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg hlog, abs_of_pos hk0] using hsmall
  have hnat : k ^ 2 + 1 ≤ k ^ 3 := by
    have hpow : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ (by omega)
    calc
      _ ≤ k ^ 2 + k ^ 2 := Nat.add_le_add_left hpow _
      _ = 2 * k ^ 2 := by omega
      _ ≤ k * k ^ 2 := Nat.mul_le_mul_right _ hk
      _ = _ := by ring
  have hlogextra : Real.log (((k ^ 2 + 1 : ℕ) : ℝ)) ≤ 3 * Real.log (k : ℝ) := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < ((k ^ 2 + 1 : ℕ) : ℝ))
      (by exact_mod_cast hnat : ((k ^ 2 + 1 : ℕ) : ℝ) ≤ ((k ^ 3 : ℕ) : ℝ))
    simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using hh
  have hnum : (2 * (k : ℝ)) * Real.log ((k ^ 2 : ℕ) : ℝ) ≤
      ((k ^ 2 : ℕ) : ℝ) * Real.log 2 - Real.log (((k ^ 2 + 1 : ℕ) : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hsmall' (by positivity : 0 ≤ 8 * (k : ℝ))
    have hcoef := mul_nonneg (by linarith : 0 ≤ 4 * (k : ℝ) - 3) hlog
    rw [Nat.cast_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hden : 0 < Real.log ((k ^ 2 : ℕ) : ℝ) := Real.log_pos (by
    rw [Nat.cast_pow]
    nlinarith)
  have hpi := Chebyshev.pi_ge (k ^ 2)
  simp only [Nat.cast_add, Nat.cast_one] at hnum
  have hh := ((le_div_iff₀ hden).mpr hnum).trans hpi
  exact_mod_cast hh

theorem eventually_many_small_primes :
    ∀ᶠ k : ℕ in atTop, k ≤ ((k ^ 2).primesLE \ k.primesLE).card := by
  filter_upwards [eventually_twice_le_primeCounting_square, eventually_ge_atTop 1] with k hcount hk
  have hkk : k ≤ k ^ 2 := Nat.le_pow (by norm_num)
  rw [Finset.card_sdiff_of_subset (Nat.primesLE_mono hkk), Nat.primesLE_card_eq_primeCounting,
    Nat.primesLE_card_eq_primeCounting]
  have hh := prime_counting_le_self k
  omega

theorem prime_shifts_admissible {k : ℕ} (h : Fin k → ℕ)
    (hprime : ∀ i, (h i).Prime) (hlarge : ∀ i, k < h i) :
    ∀ p : ℕ, p.Prime → ∃ b : ZMod p, ∀ i, b + (h i : ZMod p) ≠ 0 := by
  classical
  intro p hp
  let : NeZero p := ⟨hp.ne_zero⟩
  by_cases hpk : p ≤ k
  · refine ⟨0, ?_⟩
    intro i hi
    have hd : p ∣ h i := (ZMod.natCast_eq_zero_iff (h i) p).mp (by simpa only [zero_add] using hi)
    have heq := (Nat.prime_dvd_prime_iff_eq hp (hprime i)).mp hd
    have hgt := hlarge i
    omega
  · let S : Finset (ZMod p) := Finset.univ.image (fun i : Fin k => -(h i : ZMod p))
    have hcard : S.card < (Finset.univ : Finset (ZMod p)).card := by
      have hs : S.card ≤ k := by
        simpa only [Finset.card_univ, Fintype.card_fin] using
          Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := fun i => -(h i : ZMod p))
      simpa only [Finset.card_univ, ZMod.card] using (show S.card < p by omega)
    obtain ⟨b, _hb, hbS⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    refine ⟨b, ?_⟩
    intro i hi
    apply hbS
    apply Finset.mem_image.mpr
    exact ⟨i, Finset.mem_univ i, (eq_neg_of_add_eq_zero_left hi).symm⟩

theorem exists_small_admissible_shifts :
    ∀ᶠ k : ℕ in atTop, ∃ h : Fin k → ℕ, Function.Injective h ∧
      (∀ i, (h i).Prime ∧ k < h i ∧ h i ≤ k ^ 2) ∧
      ∀ p : ℕ, p.Prime → ∃ b : ZMod p, ∀ i, b + (h i : ZMod p) ≠ 0 := by
  filter_upwards [eventually_many_small_primes] with k hk
  obtain ⟨h, hh⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin k) (s := (k ^ 2).primesLE \ k.primesLE) (by simpa only [Fintype.card_fin] using hk)
  have hprops : ∀ i, (h i).Prime ∧ k < h i ∧ h i ≤ k ^ 2 := by
    intro i
    have hmem := hh ⟨i, rfl⟩
    have hdata := Finset.mem_sdiff.mp hmem
    have htop := Nat.mem_primesLE.mp hdata.1
    have hlow : k < h i := by
      by_contra hle
      exact hdata.2 (Nat.mem_primesLE.mpr ⟨by omega, htop.2⟩)
    exact ⟨htop.2, hlow, htop.1⟩
  exact ⟨h, h.injective, hprops,
    prime_shifts_admissible h (fun i => (hprops i).1) (fun i => (hprops i).2.1)⟩

end Erdos4.FGKMT
