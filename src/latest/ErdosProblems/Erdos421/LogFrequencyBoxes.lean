import ErdosProblems.Erdos421.LogTaylorCoefficients
import ErdosProblems.Erdos421.TorusBoxes
import Mathlib.Data.Nat.Factorial.BigOperators

/-! # Exact volumes of the logarithmic coefficient boxes -/

namespace Erdos421

open MeasureTheory

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

noncomputable def logFrequencyBox (k : ℕ) (t M z : ℝ) : Set (UnitAddTorus (Fin k)) :=
  torusBox (fun j ↦ (logTaylorCoefficients k t z j : UnitAddCircle)) (polynomialBoxRadius k M)

theorem measurableSet_logFrequencyBox (k : ℕ) (t M z : ℝ) :
    MeasurableSet (logFrequencyBox k t M z) := measurableSet_torusBox _ _

theorem two_mul_polynomialBoxRadius_le_one {k : ℕ} (hk : 0 < k) {M : ℝ}
    (hM : 1 ≤ M) (j : Fin k) : 2 * polynomialBoxRadius k M j ≤ 1 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hj : (1 : ℝ) ≤ (((j : ℕ) + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos (j : ℕ)
  have hp : 1 ≤ M ^ ((j : ℕ) + 1) := one_le_pow₀ hM
  have hm : 1 ≤ (k : ℝ) * (((j : ℕ) + 1 : ℕ) : ℝ) * M ^ ((j : ℕ) + 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hkR hj) hp
  have hden : 2 ≤ 2 * Real.pi * k * (((j : ℕ) + 1 : ℕ) : ℝ) * M ^ ((j : ℕ) + 1) := by
    nlinarith [Real.two_le_pi]
  unfold polynomialBoxRadius
  rw [mul_one_div]
  apply (div_le_iff₀ (by positivity)).mpr
  simpa only [one_mul] using hden

theorem product_fin_successors (k : ℕ) : (∏ j : Fin k, ((j : ℕ) + 1)) = k.factorial := by
  rw [Fin.prod_univ_eq_prod_range (fun n : ℕ ↦ n + 1) k]
  exact (Nat.factorial_eq_prod_range_add_one k).symm

theorem sum_fin_successors (k : ℕ) :
    (∑ j : Fin k, ((j : ℕ) + 1)) = k + meanValueTriangle k := by
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ ↦ n + 1) k,
    Finset.sum_add_distrib, Finset.sum_range_id]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, meanValueTriangle]
  omega

theorem polynomialBoxRadius_product {k : ℕ} (hk : 0 < k) {M : ℝ} (hM : 0 < M) :
    (∏ j : Fin k, 2 * polynomialBoxRadius k M j) =
      1 / ((Real.pi * k) ^ k * k.factorial * M ^ (k + meanValueTriangle k)) := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hterm (j : Fin k) : 2 * polynomialBoxRadius k M j =
      1 / ((Real.pi * k) * (((j : ℕ) + 1 : ℕ) : ℝ) * M ^ ((j : ℕ) + 1)) := by
    have hj : (0 : ℝ) < (((j : ℕ) + 1 : ℕ) : ℝ) := by positivity
    unfold polynomialBoxRadius
    field_simp
  simp_rw [hterm]
  rw [Finset.prod_div_distrib, Finset.prod_const_one, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_pow_eq_pow_sum, sum_fin_successors]
  have hprod : (∏ j : Fin k, (((j : ℕ) + 1 : ℕ) : ℝ)) = k.factorial := by
    exact_mod_cast product_fin_successors k
  rw [hprod]

theorem logFrequencyBox_volume_real {k : ℕ} (hk : 0 < k) (t z : ℝ) {M : ℝ}
    (hM : 1 ≤ M) :
    volume.real (logFrequencyBox k t M z) =
      1 / ((Real.pi * k) ^ k * k.factorial * M ^ (k + meanValueTriangle k)) := by
  rw [logFrequencyBox, volume_torusBox_real _ _
    (fun j ↦ (polynomialBoxRadius_pos hk (by linarith) j).le)
    (two_mul_polynomialBoxRadius_le_one hk hM)]
  exact polynomialBoxRadius_product hk (by linarith)

theorem logFrequencyBox_volume_pos {k : ℕ} (hk : 0 < k) (t z : ℝ) {M : ℝ} (hM : 1 ≤ M) :
    0 < volume.real (logFrequencyBox k t M z) := by
  rw [logFrequencyBox_volume_real hk t z hM]
  have hf : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr (Nat.factorial_pos k)
  positivity

end Erdos421
