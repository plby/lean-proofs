import ErdosProblems.Erdos587.ReducedBasisGeometry
import ErdosProblems.Erdos587.CongruenceBasisImage

/-! Rounding basis coordinates places a point of the affine lattice near the rectangle center. -/

namespace Erdos587

lemma exists_lattice_real_coordinates {p q : ℤ × ℤ} (hdet : latticeDet p q ≠ 0) (x y : ℝ) :
    ∃ a b : ℝ, x = a * (p.1 : ℝ) + b * (q.1 : ℝ) ∧ y = a * (p.2 : ℝ) + b * (q.2 : ℝ) := by
  have hdetR : (p.1 : ℝ) * (q.2 : ℝ) - (p.2 : ℝ) * (q.1 : ℝ) ≠ 0 := by
    exact_mod_cast hdet
  refine ⟨(x * q.2 - y * q.1) / ((p.1 : ℝ) * q.2 - (p.2 : ℝ) * q.1),
    ((p.1 : ℝ) * y - (p.2 : ℝ) * x) / ((p.1 : ℝ) * q.2 - (p.2 : ℝ) * q.1), ?_, ?_⟩
  · calc
      x = (x * ((p.1 : ℝ) * q.2 - (p.2 : ℝ) * q.1)) /
          ((p.1 : ℝ) * q.2 - (p.2 : ℝ) * q.1) := (mul_div_cancel_right₀ x hdetR).symm
      _ = _ := by ring
  · calc
      y = (y * ((p.1 : ℝ) * q.2 - (p.2 : ℝ) * q.1)) /
          ((p.1 : ℝ) * q.2 - (p.2 : ℝ) * q.1) := (mul_div_cancel_right₀ y hdetR).symm
      _ = _ := by ring

lemma two_coordinate_rounding_error (a b P Q : ℝ) :
    |((round a : ℤ) - a) * P + ((round b : ℤ) - b) * Q| ≤ (|P| + |Q|) / 2 := by
  have ha : |(round a : ℤ) - a| ≤ (1 / 2 : ℝ) := by rw [abs_sub_comm]; exact abs_sub_round a
  have hb : |(round b : ℤ) - b| ≤ (1 / 2 : ℝ) := by rw [abs_sub_comm]; exact abs_sub_round b
  calc
    _ ≤ |((round a : ℤ) - a) * P| + |((round b : ℤ) - b) * Q| := abs_add_le _ _
    _ = |(round a : ℤ) - a| * |P| + |(round b : ℤ) - b| * |Q| := by rw [abs_mul, abs_mul]
    _ ≤ (1 / 2 : ℝ) * |P| + (1 / 2 : ℝ) * |Q| :=
      add_le_add (mul_le_mul_of_nonneg_right ha (abs_nonneg P))
        (mul_le_mul_of_nonneg_right hb (abs_nonneg Q))
    _ = _ := by ring

theorem exists_centered_congruence_point {g u v t : ℤ} {p q : ℤ × ℤ} {H J : ℝ}
    (hg : g ≠ 0) (hH : 0 < H) (hJ : 0 < J)
    (huv : IsCoprime u v) (hbasis : IsCongruenceBasis g u v p q) :
    ∃ z : ℤ × ℤ, g ∣ t + latticeLinear u v z ∧
      |(z.1 : ℝ) - H / 2| ≤ H * (latticeScaledNorm H J p + latticeScaledNorm H J q) / 2 ∧
      |(z.2 : ℝ) - J / 2| ≤ J * (latticeScaledNorm H J p + latticeScaledNorm H J q) / 2 := by
  have hdet : latticeDet p q ≠ 0 := by
    intro hh
    have hzero : g = 0 := by simpa only [hh, abs_zero] using hbasis.1.symm
    exact hg hzero
  obtain ⟨z₀, hz₀⟩ := exists_congruence_coset_point huv t g
  obtain ⟨a, b, hx, hy⟩ := exists_lattice_real_coordinates hdet
    (H / 2 - (z₀.1 : ℝ)) (J / 2 - (z₀.2 : ℝ))
  let z := z₀ + latticeCombination (round a) (round b) p q
  refine ⟨z, congruence_coset_add_basis hbasis hz₀ (round a) (round b), ?_, ?_⟩
  · have heq : (z.1 : ℝ) - H / 2 =
        ((round a : ℤ) - a) * (p.1 : ℝ) + ((round b : ℤ) - b) * (q.1 : ℝ) := by
      dsimp only [z, latticeCombination, Prod.fst_add]
      push_cast
      nlinarith [hx]
    rw [heq]
    apply (two_coordinate_rounding_error a b (p.1 : ℝ) (q.1 : ℝ)).trans
    have hp := abs_first_coordinate_le_scaledNorm (J := J) hH p
    have hq := abs_first_coordinate_le_scaledNorm (J := J) hH q
    nlinarith
  · have heq : (z.2 : ℝ) - J / 2 =
        ((round a : ℤ) - a) * (p.2 : ℝ) + ((round b : ℤ) - b) * (q.2 : ℝ) := by
      dsimp only [z, latticeCombination, Prod.snd_add]
      push_cast
      nlinarith [hy]
    rw [heq]
    apply (two_coordinate_rounding_error a b (p.2 : ℝ) (q.2 : ℝ)).trans
    have hp := abs_second_coordinate_le_scaledNorm (H := H) hJ p
    have hq := abs_second_coordinate_le_scaledNorm (H := H) hJ q
    nlinarith

end Erdos587
