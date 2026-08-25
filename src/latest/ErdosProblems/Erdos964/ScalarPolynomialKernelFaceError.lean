import ErdosProblems.Erdos964.ScalarFaceMomentError
import ErdosProblems.Erdos964.ScalarFaceEndpointError
import ErdosProblems.Erdos964.ScalarSieveFace

/-!
# Uniform comparison of the polynomial kernel with its face main term
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem exists_scalar_polynomial_kernel_face_error (M : ℕ) (hM : 0 < M)
    (h2M : 2 ∣ M) (h3M : 3 ∣ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R p : ℕ, 2 ≤ R → 0 < p →
      |scalarPolynomialPrimeKernel M R p -
        (scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 4) * (Real.log R) ^ 4 *
          scalarSieveFace (Real.log p / Real.log R)| ≤
        1296 * coprimeHarmonicDensity M ^ 2 * (Real.log R) ^ 2 * (ε * (Real.log R) ^ 2 + C) +
          132 * (scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 4) * (Real.log R) ^ 4 *
            (Real.log 2 / Real.log R) := by
  obtain ⟨C, hC, hface⟩ := exists_scalar_face_moment_errors M hM h2M h3M ε hε
  refine ⟨C, hC, ?_⟩
  intro R p hR hp
  let δ := coprimeHarmonicDensity M
  let L := Real.log R
  let Q₁ := R - 1
  let Q₂ := (R - 1) / p
  let z := Real.log p / L
  let q₁ := Real.log Q₁ / L
  let q₂ := Real.log Q₂ / L
  let E := ε * L ^ 2 + C
  let w := δ ^ 2 * L ^ 2
  let A := (scalarSieveEulerConstant M * δ ^ 2) * L ^ 2
  let H := scalarLargeFacePrimitive q₁ + scalarSmallFacePrimitive z q₂ - scalarLargeFacePrimitive q₂
  let e := Real.log 2 / L
  have hL : 0 < L := Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hS : 0 ≤ scalarSieveEulerConstant M :=
    zero_le_one.trans (scalarSieveEulerConstant_ge_one M h2M h3M)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have hQ₁ : 1 ≤ Q₁ := by dsimp only [Q₁]; omega
  have hQ₁R : Q₁ ≤ R := Nat.sub_le R 1
  have hQ₂R : Q₂ ≤ R := (Nat.div_le_self _ _).trans hQ₁R
  have hlarge₁ : |scalarLargeLogMoment M R Q₁ - A * scalarLargeFacePrimitive q₁| ≤ 392 * E :=
    (hface R Q₁ hL hQ₁ hQ₁R).1
  have hother :
      (|scalarSmallLogMoment M R Q₂ z - A * scalarSmallFacePrimitive z q₂| ≤ 512 * E) ∧
      (|scalarLargeLogMoment M R Q₂ - A * scalarLargeFacePrimitive q₂| ≤ 392 * E) ∧
      |H - scalarSieveFace z| ≤ 132 * e := by
    by_cases hpR : p < R
    · have hQ₂ : 1 ≤ Q₂ := Nat.div_pos (by omega) hp
      have hz := (normalized_strict_endpoint_bounds R p hp hpR).1
      refine ⟨(hface R Q₂ hL hQ₂ hQ₂R).2 z hz, (hface R Q₂ hL hQ₂ hQ₂R).1, ?_⟩
      rw [scalarSieveFace_eq_small z hz.2]
      exact scalar_small_face_endpoint_error R p hp hpR
    · have hRp : R ≤ p := Nat.le_of_not_gt hpR
      have hQ₂ : Q₂ = 0 := Nat.div_eq_of_lt (by omega)
      have hq₂ : q₂ = 0 := by simp only [q₂, hQ₂, Nat.cast_zero, Real.log_zero, zero_div]
      have hsmall0 : scalarSmallLogMoment M R Q₂ z = 0 := by
        simp only [hQ₂, scalarSmallLogMoment, scalarLogMoment_zero, mul_zero, add_zero]
      have hlarge0 : scalarLargeLogMoment M R Q₂ = 0 := by
        simp only [hQ₂, scalarLargeLogMoment, scalarLogMoment_zero, mul_zero, sub_zero, add_zero]
      have hsp0 : scalarSmallFacePrimitive z q₂ = 0 := by simp [hq₂, scalarSmallFacePrimitive]
      have hlp0 : scalarLargeFacePrimitive q₂ = 0 := by simp [hq₂, scalarLargeFacePrimitive]
      refine ⟨?_, ?_, ?_⟩
      · rw [hsmall0, hsp0, mul_zero, sub_self, abs_zero]
        positivity
      · rw [hlarge0, hlp0, mul_zero, sub_self, abs_zero]
        positivity
      · have hz1 : 1 ≤ z := (le_div_iff₀ hL).mpr (by
          simpa only [one_mul] using Real.log_le_log
            (show (0 : ℝ) < R by exact_mod_cast (show 0 < R by omega))
            (show (R : ℝ) ≤ p by exact_mod_cast hRp))
        dsimp only [H]
        rw [hsp0, hlp0, add_zero, sub_zero, scalarSieveFace_eq_large z hz1]
        exact (scalar_large_face_endpoint_error R hR).trans (by nlinarith [he])
  have hinner :
      |(scalarLargeLogMoment M R Q₁ + scalarSmallLogMoment M R Q₂ z - scalarLargeLogMoment M R Q₂) -
        A * H| ≤ 1296 * E := by
    have hid :
        (scalarLargeLogMoment M R Q₁ + scalarSmallLogMoment M R Q₂ z -
          scalarLargeLogMoment M R Q₂) -
          A * H =
        ((scalarLargeLogMoment M R Q₁ - A * scalarLargeFacePrimitive q₁) +
          (scalarSmallLogMoment M R Q₂ z - A * scalarSmallFacePrimitive z q₂)) -
          (scalarLargeLogMoment M R Q₂ - A * scalarLargeFacePrimitive q₂) := by dsimp only [H]; ring
    rw [hid]
    calc
      _ ≤ |(scalarLargeLogMoment M R Q₁ - A * scalarLargeFacePrimitive q₁) +
            (scalarSmallLogMoment M R Q₂ z - A * scalarSmallFacePrimitive z q₂)| +
          |scalarLargeLogMoment M R Q₂ - A * scalarLargeFacePrimitive q₂| := abs_sub _ _
      _ ≤ (|scalarLargeLogMoment M R Q₁ - A * scalarLargeFacePrimitive q₁| +
            |scalarSmallLogMoment M R Q₂ z - A * scalarSmallFacePrimitive z q₂|) +
          |scalarLargeLogMoment M R Q₂ - A * scalarLargeFacePrimitive q₂| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ 1296 * E := by linarith [hother.1, hother.2.1]
  have hpoly : |scalarPolynomialPrimeKernel M R p - w * A * H| ≤ w * (1296 * E) := by
    rw [scalarPolynomialPrimeKernel_eq_log_moments M R p (by omega) hp]
    change |w * (scalarLargeLogMoment M R Q₁ + scalarSmallLogMoment M R Q₂ z -
      scalarLargeLogMoment M R Q₂) - w * A * H| ≤ _
    rw [mul_assoc w A H, ← mul_sub, abs_mul, abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_left hinner hw
  have hmain : |w * A * H - w * A * scalarSieveFace z| ≤ w * A * (132 * e) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (mul_nonneg hw hA)]
    exact mul_le_mul_of_nonneg_left hother.2.2 (mul_nonneg hw hA)
  have h := (abs_sub_le (scalarPolynomialPrimeKernel M R p) (w * A * H)
    (w * A * scalarSieveFace z)).trans (add_le_add hpoly hmain)
  have hfactor : w * A = (scalarSieveEulerConstant M * δ ^ 4) * L ^ 4 := by
    dsimp only [w, A]
    ring
  rw [hfactor] at h
  calc
    _ ≤ w * (1296 * E) + (scalarSieveEulerConstant M * δ ^ 4) * L ^ 4 * (132 * e) := h
    _ = _ := by dsimp only [w, E, e, L, δ]; ring

end Erdos964
