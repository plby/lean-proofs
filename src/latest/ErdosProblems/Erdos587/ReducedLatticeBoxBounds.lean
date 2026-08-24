import ErdosProblems.Erdos587.ReducedLatticeBox

/-! Ambient, volume and span bounds for the natural primitive image. -/

namespace Erdos587

lemma latticeBoxStep_mul_factor {g u v : ℕ} {p q : ℤ × ℤ}
    (hbasis : IsCongruenceBasis g u v p q) :
    (latticeBoxStep g u v p : ℝ) * g = |(latticeLinear u v p : ℝ)| := by
  have hh : (g : ℤ) * |latticeLinear u v p / (g : ℤ)| = |latticeLinear u v p| := by
    calc
      _ = |(g : ℤ) * (latticeLinear u v p / (g : ℤ))| := by
        rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg g)]
      _ = _ := by rw [Int.mul_ediv_cancel' hbasis.first_mem]
  have hR : (g : ℝ) * |((latticeLinear u v p / (g : ℤ) : ℤ) : ℝ)| =
      |(latticeLinear u v p : ℝ)| := by exact_mod_cast hh
  simpa only [latticeBoxStep, Nat.cast_natAbs, Int.cast_abs, mul_comm] using hR

namespace ReducedLatticeBox

variable {g u v t H J : ℕ} (P : ReducedLatticeBox g u v t H J)

noncomputable def maximum : ℕ := P.base + P.firstStep * P.firstWidth + P.secondStep * P.secondWidth

theorem value_bounds {x y : ℕ} (hx : x ≤ P.firstWidth) (hy : y ≤ P.secondWidth) :
    ((g : ℝ) * ((t : ℝ) + u * H + v * J)) / 4 ≤
      (g : ℝ) ^ 2 * ((P.base : ℝ) + P.firstStep * x + P.secondStep * y) ∧
    (g : ℝ) ^ 2 * ((P.base : ℝ) + P.firstStep * x + P.secondStep * y) ≤
      (g : ℝ) * ((t : ℝ) + u * H + v * J) := by
  let w := positiveLatticeBoxPoint g u v P.first P.second P.center P.firstHalfWidth P.secondHalfWidth x y
  have hw := P.central_quarter x hx y hy
  obtain ⟨hX, hY, hwx, hwy⟩ := natural_coordinates_of_central_quarter hw
  have hxR : (w.1.toNat : ℝ) = (w.1 : ℝ) := by exact_mod_cast hwx
  have hyR : (w.2.toNat : ℝ) = (w.2 : ℝ) := by exact_mod_cast hwy
  have hi := (lattice_box_natural_image P.factor_pos P.basis P.coset P.central_quarter x hx y hy).2.2
  have hiR : (g : ℝ) ^ 2 * ((P.base : ℝ) + P.firstStep * x + P.secondStep * y) =
      (g : ℝ) * ((t : ℝ) + u * w.1.toNat + v * w.2.toNat) := by exact_mod_cast hi
  have hxmin : (H : ℝ) / 4 ≤ w.1.toNat := by rw [hxR]; exact hw.1.1
  have hymin : (J : ℝ) / 4 ≤ w.2.toNat := by rw [hyR]; exact hw.2.1
  have hlo : ((t : ℝ) + u * H + v * J) / 4 ≤ (t : ℝ) + u * w.1.toNat + v * w.2.toNat := by
    have hh₁ := mul_le_mul_of_nonneg_left hxmin (Nat.cast_nonneg u)
    have hh₂ := mul_le_mul_of_nonneg_left hymin (Nat.cast_nonneg v)
    have ht := Nat.cast_nonneg (α := ℝ) t
    nlinarith
  have hhi : (t : ℝ) + u * w.1.toNat + v * w.2.toNat ≤ (t : ℝ) + u * H + v * J := by
    gcongr <;> exact_mod_cast (by assumption)
  rw [hiR]
  constructor
  · simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg g)
  · exact mul_le_mul_of_nonneg_left hhi (Nat.cast_nonneg g)

theorem maximum_bounds :
    ((g : ℝ) * ((t : ℝ) + u * H + v * J)) / (4 * (g : ℝ) ^ 2) ≤ P.maximum ∧
      (P.maximum : ℝ) ≤ ((g : ℝ) * ((t : ℝ) + u * H + v * J)) / (g : ℝ) ^ 2 := by
  have hh := P.value_bounds (x := P.firstWidth) (y := P.secondWidth) le_rfl le_rfl
  have hg : (0 : ℝ) < g := by exact_mod_cast P.factor_pos
  have hmaximum : (P.maximum : ℝ) =
      (P.base : ℝ) + P.firstStep * P.firstWidth + P.secondStep * P.secondWidth := by
    simp only [maximum, Nat.cast_add, Nat.cast_mul]
  rw [← hmaximum] at hh
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < 4 * (g : ℝ) ^ 2)).mpr
    nlinarith [hh.1]
  · apply (le_div_iff₀ (sq_pos_of_pos hg)).mpr
    nlinarith [hh.2]

theorem volume_lower : (H : ℝ) * J / (8192 * g) ≤ (P.firstWidth : ℝ) * P.secondWidth := by
  have hH : (0 : ℝ) < H := by exact_mod_cast P.width_pos
  have hJ : (0 : ℝ) < J := by exact_mod_cast P.height_pos
  have hg : (0 : ℝ) < g := by exact_mod_cast P.factor_pos
  have hgZ : (0 : ℤ) < g := by exact_mod_cast P.factor_pos
  have hprod := (reduced_congruence_basis_product_bounds hH hJ hgZ P.basis P.order P.reduced).2
  push_cast at hprod
  exact lattice_box_volume_lower P.firstNorm_pos P.secondNorm_pos hH hJ hg P.first_small P.small hprod

theorem span_lower : ((u : ℝ) * H + (v : ℝ) * J) / (256 * g) ≤
    (P.firstStep : ℝ) * P.firstWidth + (P.secondStep : ℝ) * P.secondWidth := by
  have hH : (0 : ℝ) < H := by exact_mod_cast P.width_pos
  have hJ : (0 : ℝ) < J := by exact_mod_cast P.height_pos
  have hg : (0 : ℝ) < g := by exact_mod_cast P.factor_pos
  have hgZ : (0 : ℤ) < g := by exact_mod_cast P.factor_pos
  have hdual := lattice_dual_sum_bound hH hJ hgZ (Int.natCast_nonneg u) (Int.natCast_nonneg v)
    P.basis P.order P.reduced
  push_cast at hdual
  have hh := lattice_box_span_lower P.firstNorm_pos P.secondNorm_pos P.first_small P.small
    (abs_nonneg (latticeLinear u v P.first : ℝ)) (abs_nonneg (latticeLinear u v P.second : ℝ)) hg hdual
  have hp : (P.firstStep : ℝ) * g = |(latticeLinear u v P.first : ℝ)| := latticeBoxStep_mul_factor P.basis
  have hq : (P.secondStep : ℝ) * g = |(latticeLinear u v P.second : ℝ)| :=
    latticeBoxStep_mul_factor P.basis.swap
  rw [← hp, ← hq] at hh
  have heq : (2 / (g : ℝ)) *
      ((P.firstHalfWidth : ℝ) * ((P.firstStep : ℝ) * g) +
        (P.secondHalfWidth : ℝ) * ((P.secondStep : ℝ) * g)) =
      (P.firstStep : ℝ) * P.firstWidth + (P.secondStep : ℝ) * P.secondWidth := by
    simp only [firstWidth, secondWidth, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
  exact hh.trans_eq heq

theorem span_control {C : ℝ} (hC : 0 ≤ C)
    (hspan : (g : ℝ) * ((t : ℝ) + u * H + v * J) ≤ C * g * ((u : ℝ) * H + v * J)) :
    (P.maximum : ℝ) ≤ (256 * C) *
      ((P.firstStep : ℝ) * P.firstWidth + (P.secondStep : ℝ) * P.secondWidth) := by
  have hg : (0 : ℝ) < g := by exact_mod_cast P.factor_pos
  have hmax := (le_div_iff₀ (sq_pos_of_pos hg)).mp P.maximum_bounds.2
  have hspanLower := (div_le_iff₀ (by positivity : 0 < 256 * (g : ℝ))).mp P.span_lower
  have hscaled := mul_le_mul_of_nonneg_left hspanLower (mul_nonneg hC hg.le)
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hg)).mp
  nlinarith

end ReducedLatticeBox

end Erdos587
