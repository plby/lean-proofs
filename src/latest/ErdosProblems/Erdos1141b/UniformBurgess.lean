import ErdosProblems.Erdos1141b.TwistedBurgess

/-!
# Short sums uniform in a larger modulus
-/

open scoped BigOperators

namespace Erdos1141b

open CharacterSums

lemma polyaVinogradov_scale_le_of_sq_le {q M : ℕ} (hq : 1 < q) (hM : 1 ≤ M)
    (hsq : q ^ 2 ≤ M)
    (hlog : 2 * Real.log (M : ℝ) ≤ (M : ℝ) ^ (111 / 512 : ℝ)) :
    2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) ≤ (M : ℝ) ^ (239 / 512 : ℝ) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hqM : q ≤ M := (Nat.le_self_pow (by omega) q).trans hsq
  have hsqrt : Real.sqrt (q : ℝ) ≤ (M : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      _ = ((q : ℝ) ^ 2) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast_mul hqr.le, Real.sqrt_eq_rpow]; norm_num
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hsq) (by norm_num)
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq.le)
  calc
    _ = Real.sqrt (q : ℝ) * (2 * Real.log (q : ℝ)) := by ring
    _ ≤ (M : ℝ) ^ (1 / 4 : ℝ) * (2 * Real.log (M : ℝ)) := by
      gcongr
    _ ≤ (M : ℝ) ^ (1 / 4 : ℝ) * (M : ℝ) ^ (111 / 512 : ℝ) := by gcongr
    _ = _ := by rw [← Real.rpow_add hMr]; norm_num

/-- The bound is uniform even when the character's modulus is much smaller than `M`. -/
theorem exists_twisted_prefix_bound_relative_cutoff :
    ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      ∀ (t : ℕ) [NeZero t], t ≤ 8 →
      ∀ {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ i, Fact (p i).Prime]
        (hc : Pairwise fun i j ↦ (p i).Coprime (p j))
        (ht : t.Coprime (∏ i, p i)) (ψ : DirichletCharacter ℤ t),
        ψ.IsQuadratic → (∀ i, p i ≠ 2) →
        1 < t * ∏ i, p i → t * ∏ i, p i ≤ M →
        (crtMulChar ht ψ (primeProductMulChar p hc)).ringHomComp (Int.castRingHom ℂ) ≠ 1 →
        ∀ N : ℕ, (M : ℝ) ^ (15 / 32 : ℝ) ≤ (N : ℝ) →
          ‖∑ n ∈ Finset.Icc 1 N,
            ((crtMulChar ht ψ (primeProductMulChar p hc)).ringHomComp
              (Int.castRingHom ℂ)) (n : ZMod (t * ∏ i, p i))‖ ≤
            (N : ℝ) * (M : ℝ) ^ (-1 / 512 : ℝ) := by
  obtain ⟨q0, hshort⟩ := exists_twisted_prefix_bound_cutoff
  obtain ⟨M1, hlong⟩ := Filter.eventually_atTop.mp
    (eventually_two_log_le_rpow (111 / 512) (by norm_num))
  refine ⟨max (q0 ^ 2) (max M1 2), ?_⟩
  intro M hM t _ ht8 ι _ p _ hc ht ψ hψ hodd hq hqM hχ N hN
  let q := t * ∏ i, p i
  let χ := crtMulChar ht ψ (primeProductMulChar p hc)
  have hM2 : 2 ≤ M := (le_max_right M1 2).trans ((le_max_right _ _).trans hM)
  have hMr : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hqr : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq0M : q0 ^ 2 ≤ M := (le_max_left _ _).trans hM
  have hM1 : M1 ≤ M := (le_max_left M1 2).trans ((le_max_right _ _).trans hM)
  have hreal : |∑ n ∈ Finset.Icc 1 N, (χ (n : ZMod q) : ℝ)| ≤
      (N : ℝ) * (M : ℝ) ^ (-1 / 512 : ℝ) := by
    by_cases hbig : M ≤ q ^ 2
    · have hq0 : q0 ≤ q := by nlinarith
      have hNq : (q : ℝ) ^ (15 / 32 : ℝ) ≤ (N : ℝ) :=
        (Real.rpow_le_rpow hqr.le (by exact_mod_cast hqM) (by norm_num)).trans hN
      apply (hshort t ht8 p hc ht ψ hψ hodd hq0 hχ N hNq).trans
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      calc
        (q : ℝ) ^ (-1 / 256 : ℝ) = ((q : ℝ) ^ 2) ^ (-1 / 512 : ℝ) := by
          rw [← Real.rpow_natCast_mul hqr.le]; norm_num
        _ ≤ _ := Real.rpow_le_rpow_of_nonpos hMr
          (by exact_mod_cast hbig) (by norm_num)
    · apply (mulChar_prefix_polyaVinogradov_bound hq χ hχ N).trans
      calc
        _ ≤ (M : ℝ) ^ (239 / 512 : ℝ) :=
          polyaVinogradov_scale_le_of_sq_le hq (by omega)
            (show q ^ 2 ≤ M from (lt_of_not_ge hbig).le) (hlong M hM1)
        _ = (M : ℝ) ^ (15 / 32 : ℝ) * (M : ℝ) ^ (-1 / 512 : ℝ) := by
          rw [← Real.rpow_add hMr]; norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_right hN (by positivity)
  change ‖∑ n ∈ Finset.Icc 1 N, (χ (n : ZMod q) : ℂ)‖ ≤ _
  rw [← Int.cast_sum, Complex.norm_intCast]
  simpa only [← Int.cast_sum] using hreal

end Erdos1141b
