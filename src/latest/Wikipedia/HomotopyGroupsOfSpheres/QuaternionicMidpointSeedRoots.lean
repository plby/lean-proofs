import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMidpointSeedScalars
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Two exact complex square roots for the midpoint preimage construction -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed

open QuaternionicBottMatrix

def squareRoot (w : ℂ) : ℂ := Classical.choose (IsAlgClosed.exists_pow_nat_eq w zero_lt_two)

theorem squareRoot_sq (w : ℂ) : squareRoot w ^ 2 = w :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq w zero_lt_two)

theorem normSq_of_square_phase (m : ℝ) (hm : 0 ≤ m) (q : unitary ℂ) (a : ℂ)
    (ha : a ^ 2 = (m : ℂ) * star q.val) : Complex.normSq a = m := by
  have hq : Complex.normSq (star q.val) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_star, unitary_complex_norm, one_pow]
  have h := congrArg Complex.normSq ha
  rw [map_pow, map_mul, Complex.normSq_ofReal, hq, mul_one] at h
  exact (sq_eq_sq₀ (Complex.normSq_nonneg a) hm).mp (by nlinarith [h])

theorem star_of_square_phase (m : ℝ) (hm : 0 < m) (q : unitary ℂ) (a : ℂ)
    (ha : a ^ 2 = (m : ℂ) * star q.val) : star a = q.val * a := by
  have hn := normSq_of_square_phase m (le_of_lt hm) q a ha
  have hne : a ≠ 0 := by
    intro h
    rw [h, map_zero] at hn
    linarith
  apply mul_left_cancel₀ hne
  calc
    a * star a = (m : ℂ) := by
      rw [mul_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, hn]
    _ = (q.val * star q.val) * (m : ℂ) := by rw [q.property.2, one_mul]
    _ = q.val * ((m : ℂ) * star q.val) := by ring
    _ = q.val * a ^ 2 := by rw [ha]
    _ = a * (q.val * a) := by ring

def rootA : ℂ := squareRoot ((weight0 : ℂ) * star phase)
def rootB : ℂ := squareRoot (Complex.I * (weight1 : ℂ))
def rootC : ℂ := -(phase * rootA * rootB) / (delta : ℂ)

theorem rootA_sq : rootA ^ 2 = (weight0 : ℂ) * star phase := squareRoot_sq _
theorem rootB_sq : rootB ^ 2 = Complex.I * (weight1 : ℂ) := squareRoot_sq _

theorem rootA_normSq : Complex.normSq rootA = weight0 :=
  normSq_of_square_phase _ (le_of_lt weight0_pos) ⟨phase, phase_unitary⟩ _ rootA_sq

private def imaginaryPhase : unitary ℂ :=
  ⟨-Complex.I, by constructor <;> norm_num [Complex.star_def]⟩

private theorem rootB_sq_phase : rootB ^ 2 = (weight1 : ℂ) * star imaginaryPhase.val := by
  rw [rootB_sq]
  simp [imaginaryPhase, mul_comm]

theorem rootB_normSq : Complex.normSq rootB = weight1 :=
  normSq_of_square_phase _ (le_of_lt weight1_pos) imaginaryPhase _ rootB_sq_phase

theorem rootA_star : star rootA = phase * rootA :=
  star_of_square_phase _ weight0_pos ⟨phase, phase_unitary⟩ _ rootA_sq

theorem rootB_star : star rootB = -Complex.I * rootB :=
  star_of_square_phase _ weight1_pos imaginaryPhase _ rootB_sq_phase

theorem delta_rootC : (delta : ℂ) * rootC = -(phase * rootA * rootB) := by
  unfold rootC
  exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt delta_pos))

theorem rootC_normSq : Complex.normSq rootC = weight2 := by
  have h := congrArg Complex.normSq delta_rootC
  simp only [map_mul, Complex.normSq_ofReal, Complex.normSq_neg,
    phase_normSq, rootA_normSq, rootB_normSq, one_mul] at h
  apply mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt delta_pos))
  rw [delta_sq_mul_weight2]
  nlinarith [h]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed
