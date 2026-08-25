import ErdosProblems.Erdos1141b.ShortConvolutionMean
import ErdosProblems.Erdos1141b.SparseConvolutionMean
import ErdosProblems.Erdos1141b.SiegelLValue

/-!
# A small split prime outside a prescribed modulus

Only existence of one prime is needed. The short convolution mean and
Siegel's lower bound contradict the sparse support forced by its absence.
-/

open scoped BigOperators

namespace Erdos1141b

theorem exists_small_split_prime_cutoff :
    ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      ∀ q : ℕ, [NeZero q] → 1 < q → q ∣ M →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → χ ^ 2 = 1 →
      (∀ N : ℕ, (M : ℝ) ^ (15 / 32 : ℝ) ≤ (N : ℝ) →
        ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q)‖ ≤
          (N : ℝ) * (M : ℝ) ^ (-1 / 512 : ℝ)) →
      ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (M : ℝ) ^ (31 / 64 : ℝ) ∧
        ¬p ∣ M ∧ χ (p : ZMod q) = 1 := by
  obtain ⟨c, hc, hL⟩ := exists_siegel_LValue_lower_bound (1 / 2048) (by norm_num)
  obtain ⟨M1, hmean⟩ := exists_short_convolution_mean_cutoff
  obtain ⟨M2, hsparse⟩ := exists_sparse_convolution_mean_cutoff
  obtain ⟨M3, hconst⟩ := Filter.eventually_atTop.mp
    (eventually_const_le_rpow (8 / c) (1 / 2048) (by norm_num))
  obtain ⟨M4, hfloor⟩ := Filter.eventually_atTop.mp
    (eventually_const_le_rpow 2 (31 / 64) (by norm_num))
  refine ⟨max (max M1 M2) (max (max M3 M4) 2), ?_⟩
  intro M hM q _ hq hqdiv χ hχ hsquare hprefix
  have hM1 : M1 ≤ M := (le_max_left M1 M2).trans ((le_max_left _ _).trans hM)
  have hM2 : M2 ≤ M := (le_max_right M1 M2).trans ((le_max_left _ _).trans hM)
  have hM3 : M3 ≤ M := (le_max_left M3 M4).trans ((le_max_left _ _).trans
    ((le_max_right _ _).trans hM))
  have hM4 : M4 ≤ M := (le_max_right M3 M4).trans ((le_max_left _ _).trans
    ((le_max_right _ _).trans hM))
  have hMtwo : 2 ≤ M := (le_max_right _ _).trans ((le_max_right _ _).trans hM)
  have hMpos : 0 < M := by omega
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hqr : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hqM : q ≤ M := Nat.le_of_dvd hMpos hqdiv
  let X := ⌊(M : ℝ) ^ (31 / 64 : ℝ)⌋₊
  have hXlo : (M : ℝ) ^ (31 / 64 : ℝ) / 2 ≤ (X : ℝ) :=
    half_le_nat_floor (hfloor M hM4)
  have hXhi : (X : ℝ) ≤ (M : ℝ) ^ (31 / 64 : ℝ) := Nat.floor_le (by positivity)
  obtain ⟨hXpos, _, herror⟩ := hmean M hM1 q hq hqM χ hχ hprefix
  have hXr : (0 : ℝ) < X := by exact_mod_cast hXpos
  by_contra hnone
  have hprimes : ∀ p : ℕ, p.Prime → p ≤ X → ¬p ∣ M → χ (p : ZMod q) = -1 := by
    intro p hp hpX hpM
    have hpq : p.Coprime q := hp.coprime_iff_not_dvd.mpr (fun h ↦ hpM (h.trans hqdiv))
    have hu : IsUnit (p : ZMod q) := (ZMod.isUnit_iff_coprime _ _).mpr hpq
    have hzero : χ (p : ZMod q) ≠ 0 := (hu.map χ.toMonoidHom).ne_zero
    have hone : χ (p : ZMod q) ≠ 1 := by
      intro hone
      apply hnone
      exact ⟨p, hp, (by exact_mod_cast hpX : (p : ℝ) ≤ X).trans hXhi, hpM, hone⟩
    rcases (MulChar.isQuadratic_iff_sq_eq_one.mpr hsquare) (p : ZMod q) with h | h | h
    · exact (hzero h).elim
    · exact (hone h).elim
    · exact h
  have hsmall := hsparse M hM2 X hXlo hXhi q χ hprimes
  let S := ∑ n ∈ Finset.Icc 1 X, χ.zetaMul n
  have hmain : (X : ℝ) * (χ.LFunction 1).re ≤
      4 * (X : ℝ) * (M : ℝ) ^ (-1 / 1024 : ℝ) := by
    have hre := Complex.re_le_norm ((X : ℂ) * χ.LFunction 1)
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] at hre
    have htri : ‖(X : ℂ) * χ.LFunction 1‖ ≤ ‖S‖ + ‖S - (X : ℂ) * χ.LFunction 1‖ := by
      have hid : (X : ℂ) * χ.LFunction 1 = S - (S - (X : ℂ) * χ.LFunction 1) := by ring
      calc
        _ = ‖S - (S - (X : ℂ) * χ.LFunction 1)‖ := congrArg norm hid
        _ ≤ _ := norm_sub_le _ _
    change ‖S‖ ≤ _ at hsmall
    change ‖S - (X : ℂ) * χ.LFunction 1‖ ≤ _ at herror
    linarith
  have hLlower : c * (M : ℝ) ^ (-1 / 2048 : ℝ) ≤ (χ.LFunction 1).re := by
    calc
      _ ≤ c * (q : ℝ) ^ (-1 / 2048 : ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hqr (by exact_mod_cast hqM) (by norm_num)) hc.le
      _ ≤ _ := by simpa only [neg_div] using hL q hq χ hχ hsquare
  have hupper : c * (M : ℝ) ^ (-1 / 2048 : ℝ) ≤ 4 * (M : ℝ) ^ (-1 / 1024 : ℝ) := by
    apply (mul_le_mul_iff_of_pos_left hXr).mp
    have h := mul_le_mul_of_nonneg_left hLlower hXr.le
    nlinarith
  have h8 : 8 ≤ c * (M : ℝ) ^ (1 / 2048 : ℝ) := by
    have h := (div_le_iff₀ hc).mp (hconst M hM3)
    simpa only [mul_comm] using h
  have hlower : 8 * (M : ℝ) ^ (-1 / 1024 : ℝ) ≤ c * (M : ℝ) ^ (-1 / 2048 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right h8 (by positivity : 0 ≤ (M : ℝ) ^ (-1 / 1024 : ℝ))
    rwa [mul_assoc, ← Real.rpow_add hMr,
      show (1 / 2048 : ℝ) + -1 / 1024 = -1 / 2048 by norm_num] at h
  have hRpos : 0 < (M : ℝ) ^ (-1 / 1024 : ℝ) := by positivity
  linarith

end Erdos1141b
