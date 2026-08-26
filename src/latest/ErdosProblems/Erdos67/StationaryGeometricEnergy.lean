import ErdosProblems.Erdos67.StationaryZeroAtom

/-!
# Averaged geometric sums and spectral energy

Away from zero frequency, the averaged squared geometric sums converge to
`2 / |e(θ) - 1|²`. This pointwise calculation is the input to Fatou's lemma.
-/

open scoped BigOperators ComplexConjugate Topology
open Finset Filter MeasureTheory

namespace Erdos67.StationaryModel

theorem fourier_nat_eq_pow (n : ℕ) (θ : FrequencyCircle) :
    fourier (n : ℤ) θ = fourier 1 θ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, pow_succ]

theorem geometricPolynomial_eq_sum (N : ℕ) (θ : FrequencyCircle) :
    geometricPolynomial N θ = ∑ j ∈ range N, fourier (j : ℤ) θ := by
  simp only [geometricPolynomial, signPolynomial, Complex.ofReal_one, one_mul]
  exact Fin.sum_univ_eq_sum_range (fun j ↦ fourier (j : ℤ) θ) N

theorem frequency_ne_one {θ : FrequencyCircle} (hθ : θ ≠ 0) : fourier 1 θ ≠ 1 := by
  intro he
  apply hθ
  apply AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0)
  apply Subtype.ext
  simpa only [fourier_one, AddCircle.toCircle_zero, Circle.coe_one] using he

theorem geometricPolynomial_eq_div {θ : FrequencyCircle} (hθ : θ ≠ 0) (N : ℕ) :
    geometricPolynomial N θ = (fourier (N : ℤ) θ - 1) / (fourier 1 θ - 1) := by
  rw [geometricPolynomial_eq_sum]
  simp_rw [fourier_nat_eq_pow]
  exact geom_sum_eq (frequency_ne_one hθ) N

theorem norm_fourier_frequency (h : ℤ) (θ : FrequencyCircle) : ‖fourier h θ‖ = 1 :=
  Circle.norm_coe _

theorem norm_geometricPolynomial_le {θ : FrequencyCircle} (hθ : θ ≠ 0) (N : ℕ) :
    ‖geometricPolynomial N θ‖ ≤ 2 / ‖fourier 1 θ - 1‖ := by
  rw [geometricPolynomial_eq_div hθ, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    _ ≤ ‖fourier (N : ℤ) θ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_fourier_frequency, norm_one]; norm_num

theorem tendsto_geometricPolynomial_average {θ : FrequencyCircle} (hθ : θ ≠ 0) :
    Tendsto (fun N : ℕ ↦ geometricPolynomial (N + 1) θ / ((N + 1 : ℕ) : ℂ)) atTop (nhds 0) := by
  apply squeeze_zero_norm (a := fun N : ℕ ↦
    (2 / ‖fourier 1 θ - 1‖) * (1 / ((N : ℝ) + 1)))
  · intro N
    rw [norm_div, Complex.norm_natCast]
    have hb := div_le_div_of_nonneg_right (norm_geometricPolynomial_le hθ (N + 1))
      (Nat.cast_nonneg (N + 1) : (0 : ℝ) ≤ (N + 1 : ℕ))
    simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, one_mul] using hb
  · simpa using tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem normSq_geometricPolynomial_eq {θ : FrequencyCircle} (hθ : θ ≠ 0) (N : ℕ) :
    Complex.normSq (geometricPolynomial N θ) =
      (2 - 2 * (fourier (N : ℤ) θ).re) / Complex.normSq (fourier 1 θ - 1) := by
  rw [geometricPolynomial_eq_div hθ, Complex.normSq_div, Complex.normSq_sub]
  simp only [Complex.normSq_eq_norm_sq, norm_fourier_frequency,
    map_one, mul_one, one_pow]
  congr 1
  ring

noncomputable def averagedGeometricEnergy (N : ℕ) (θ : FrequencyCircle) : ℝ :=
  (∑ m ∈ range (N + 1), Complex.normSq (geometricPolynomial m θ)) / (N + 1 : ℕ)

theorem continuous_averagedGeometricEnergy (N : ℕ) : Continuous (averagedGeometricEnergy N) :=
  (continuous_finsetSum _ fun m _ ↦
    Complex.continuous_normSq.comp (continuous_geometricPolynomial m)).div_const _

theorem averagedGeometricEnergy_nonneg (N : ℕ) (θ : FrequencyCircle) :
    0 ≤ averagedGeometricEnergy N θ :=
  div_nonneg (sum_nonneg fun m _ ↦ Complex.normSq_nonneg (geometricPolynomial m θ))
    (Nat.cast_nonneg _)

theorem averagedGeometricEnergy_eq {θ : FrequencyCircle} (hθ : θ ≠ 0) (N : ℕ) :
    averagedGeometricEnergy N θ =
      (2 - 2 * (geometricPolynomial (N + 1) θ / ((N + 1 : ℕ) : ℂ)).re) /
        Complex.normSq (fourier 1 θ - 1) := by
  unfold averagedGeometricEnergy
  simp_rw [normSq_geometricPolynomial_eq hθ]
  rw [← sum_div, sum_sub_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul,
    geometricPolynomial_eq_sum]
  rw [← Complex.ofReal_natCast, Complex.div_ofReal_re, Complex.re_sum]
  have hN : ((N + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero N)
  field_simp

noncomputable def spectralEnergy (θ : FrequencyCircle) : ℝ :=
  2 / Complex.normSq (fourier 1 θ - 1)

theorem tendsto_averagedGeometricEnergy {θ : FrequencyCircle} (hθ : θ ≠ 0) :
    Tendsto (fun N ↦ averagedGeometricEnergy N θ) atTop (nhds (spectralEnergy θ)) := by
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_geometricPolynomial_average hθ)
  have he := ((tendsto_const_nhds (x := (2 : ℝ))).sub
    ((tendsto_const_nhds (x := (2 : ℝ))).mul ht)).div_const
    (Complex.normSq (fourier 1 θ - 1))
  simpa only [Complex.zero_re, mul_zero, sub_zero, spectralEnergy, Function.comp_def,
    averagedGeometricEnergy_eq hθ] using he

end Erdos67.StationaryModel
