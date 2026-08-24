import ErdosProblems.Erdos587.ReducedBasisGeometry

/-! A reduced basis controls the size of a positive linear functional. -/

namespace Erdos587

theorem plane_dual_sum_bound {x₁ x₂ y₁ y₂ P Q U V : ℝ}
    (hP : 0 < P) (hQ : 0 < Q) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hx₁ : |x₁| ≤ P) (hx₂ : |x₂| ≤ P) (hy₁ : |y₁| ≤ Q) (hy₂ : |y₂| ≤ Q)
    (hdet : P * Q ≤ 2 * |x₁ * y₂ - x₂ * y₁|) :
    (U + V) / 4 ≤ |U * x₁ + V * x₂| / P + |U * y₁ + V * y₂| / Q := by
  let A := |U * x₁ + V * x₂|
  let B := |U * y₁ + V * y₂|
  have hfirst : U * |x₁ * y₂ - x₂ * y₁| ≤ A * Q + B * P := by
    calc
      U * |x₁ * y₂ - x₂ * y₁| = |U * (x₁ * y₂ - x₂ * y₁)| := by rw [abs_mul, abs_of_nonneg hU]
      _ = |(U * x₁ + V * x₂) * y₂ - (U * y₁ + V * y₂) * x₂| := by congr 1; ring
      _ ≤ |(U * x₁ + V * x₂) * y₂| + |(U * y₁ + V * y₂) * x₂| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le
          ((U * x₁ + V * x₂) * y₂) 0 ((U * y₁ + V * y₂) * x₂)
      _ = A * |y₂| + B * |x₂| := by rw [abs_mul, abs_mul]
      _ ≤ A * Q + B * P := add_le_add
        (mul_le_mul_of_nonneg_left hy₂ (abs_nonneg _)) (mul_le_mul_of_nonneg_left hx₂ (abs_nonneg _))
  have hsecond : V * |x₁ * y₂ - x₂ * y₁| ≤ A * Q + B * P := by
    calc
      V * |x₁ * y₂ - x₂ * y₁| = |V * (x₁ * y₂ - x₂ * y₁)| := by rw [abs_mul, abs_of_nonneg hV]
      _ = |(U * y₁ + V * y₂) * x₁ - (U * x₁ + V * x₂) * y₁| := by congr 1; ring
      _ ≤ |(U * y₁ + V * y₂) * x₁| + |(U * x₁ + V * x₂) * y₁| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le
          ((U * y₁ + V * y₂) * x₁) 0 ((U * x₁ + V * x₂) * y₁)
      _ = B * |x₁| + A * |y₁| := by rw [abs_mul, abs_mul]
      _ ≤ B * P + A * Q := add_le_add
        (mul_le_mul_of_nonneg_left hx₁ (abs_nonneg _)) (mul_le_mul_of_nonneg_left hy₁ (abs_nonneg _))
      _ = A * Q + B * P := add_comm _ _
  have hscaled := mul_le_mul_of_nonneg_left hdet (add_nonneg hU hV)
  apply (mul_le_mul_iff_left₀ (mul_pos hP hQ)).mp
  have hcancel : (A / P + B / Q) * (P * Q) = A * Q + B * P := by field_simp
  change (U + V) / 4 * (P * Q) ≤ (A / P + B / Q) * (P * Q)
  rw [hcancel]
  nlinarith

theorem lattice_dual_sum_bound {g u v : ℤ} {p q : ℤ × ℤ} {H J : ℝ}
    (hH : 0 < H) (hJ : 0 < J) (hg : 0 < g) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hbasis : IsCongruenceBasis g u v p q)
    (horder : latticeScaledSq H J p ≤ latticeScaledSq H J q)
    (hinner : |latticeScaledInner H J p q| ≤ latticeScaledSq H J p / 2) :
    (u : ℝ) * H + (v : ℝ) * J ≤ 4 *
      (|(latticeLinear u v p : ℝ)| / latticeScaledNorm H J p +
        |(latticeLinear u v q : ℝ)| / latticeScaledNorm H J q) := by
  have hp := latticeScaledNorm_pos hH.ne' hJ.ne' (hbasis.first_ne_zero hg.ne')
  have hq := latticeScaledNorm_pos hH.ne' hJ.ne' (hbasis.second_ne_zero hg.ne')
  have hcoordX (r : ℤ × ℤ) : |(r.1 : ℝ) / H| ≤ latticeScaledNorm H J r := by
    rw [abs_div, abs_of_pos hH]
    apply (div_le_iff₀ hH).mpr
    simpa only [mul_comm H] using abs_first_coordinate_le_scaledNorm (J := J) hH r
  have hcoordY (r : ℤ × ℤ) : |(r.2 : ℝ) / J| ≤ latticeScaledNorm H J r := by
    rw [abs_div, abs_of_pos hJ]
    apply (div_le_iff₀ hJ).mpr
    simpa only [mul_comm J] using abs_second_coordinate_le_scaledNorm (H := H) hJ r
  have hdetEq : ((p.1 : ℝ) / H) * ((q.2 : ℝ) / J) -
      ((p.2 : ℝ) / J) * ((q.1 : ℝ) / H) = (latticeDet p q : ℝ) / (H * J) := by
    unfold latticeDet
    push_cast
    ring
  have hdetAbs : |(latticeDet p q : ℝ)| = (g : ℝ) := by exact_mod_cast hbasis.1
  have hdetBound : latticeScaledNorm H J p * latticeScaledNorm H J q ≤
      2 * |((p.1 : ℝ) / H) * ((q.2 : ℝ) / J) - ((p.2 : ℝ) / J) * ((q.1 : ℝ) / H)| := by
    rw [hdetEq, abs_div, abs_of_pos (mul_pos hH hJ), hdetAbs]
    exact (reduced_congruence_basis_product_bounds hH hJ hg hbasis horder hinner).2
  have huR : (0 : ℝ) ≤ u := by exact_mod_cast hu
  have hvR : (0 : ℝ) ≤ v := by exact_mod_cast hv
  have hh := plane_dual_sum_bound hp hq (mul_nonneg huR hH.le) (mul_nonneg hvR hJ.le)
    (hcoordX p) (hcoordY p) (hcoordX q) (hcoordY q) hdetBound
  have hlin (r : ℤ × ℤ) : ((u : ℝ) * H) * ((r.1 : ℝ) / H) +
      ((v : ℝ) * J) * ((r.2 : ℝ) / J) = (latticeLinear u v r : ℝ) := by
    unfold latticeLinear
    push_cast
    field_simp
  rw [hlin p, hlin q] at hh
  linarith

end Erdos587
