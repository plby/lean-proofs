import ErdosProblems.Erdos587.ReducedLatticeBoxBounds
import ErdosProblems.Erdos587.LatticeAxisWidth

/-! Lower bounds for both side lengths of the primitive image. -/

namespace Erdos587

lemma reciprocal_norm_width_lower {W d s : ℝ} (hW : 0 < W) (hd : 0 < d) (hs : 0 < s)
    (hbound : s ≤ 2 * d / W) : W / (128 * d) ≤ 1 / (64 * s) := by
  have hh := (le_div_iff₀ hW).mp hbound
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

namespace ReducedLatticeBox

variable {g u v t H J : ℕ} (P : ReducedLatticeBox g u v t H J)

theorem both_widths_lower :
    1 / (64 * latticeScaledNorm H J P.second) ≤ (P.firstWidth : ℝ) ∧
      1 / (64 * latticeScaledNorm H J P.second) ≤ (P.secondWidth : ℝ) :=
  lattice_box_both_widths_lower P.firstNorm_pos P.secondNorm_pos P.norm_order P.small

theorem widths_lower_of_second_coordinate (hp₂ : P.first.2 ≠ 0) :
    (H : ℝ) / (128 * g) ≤ P.firstWidth ∧ (H : ℝ) / (128 * g) ≤ P.secondWidth := by
  have hH : (0 : ℝ) < H := by exact_mod_cast P.width_pos
  have hJ : (0 : ℝ) < J := by exact_mod_cast P.height_pos
  have hg : (0 : ℝ) < g := by exact_mod_cast P.factor_pos
  have hgZ : (0 : ℤ) < g := by exact_mod_cast P.factor_pos
  have hnorm := reduced_basis_second_norm_of_second_coordinate hH hJ hgZ P.basis P.order P.reduced hp₂
  push_cast at hnorm
  have hh := reciprocal_norm_width_lower hH hg P.secondNorm_pos hnorm
  exact ⟨hh.trans P.both_widths_lower.1, hh.trans P.both_widths_lower.2⟩

theorem widths_lower_of_axis (hp₂ : P.first.2 = 0) :
    (J : ℝ) / (128 * (g.gcd u : ℝ)) ≤ P.firstWidth ∧
      (J : ℝ) / (128 * (g.gcd u : ℝ)) ≤ P.secondWidth := by
  have hH : (0 : ℝ) < H := by exact_mod_cast P.width_pos
  have hJ : (0 : ℝ) < J := by exact_mod_cast P.height_pos
  have hd : (0 : ℝ) < g.gcd u := by exact_mod_cast Nat.gcd_pos_of_pos_left u P.factor_pos
  have hnorm := reduced_basis_second_norm_of_axis hH hJ P.factor_pos P.basis P.order P.reduced hp₂
  have hh := reciprocal_norm_width_lower hJ hd P.secondNorm_pos hnorm
  exact ⟨hh.trans P.both_widths_lower.1, hh.trans P.both_widths_lower.2⟩

theorem widths_lower_of_short_side {T : ℝ} (hT : 0 < T)
    (hshort : (H : ℝ) * (g.gcd u : ℝ) ≤ 4 * Real.sqrt T) :
    min ((H : ℝ) / (128 * g)) ((H : ℝ) * J / (512 * Real.sqrt T)) ≤ P.firstWidth ∧
      min ((H : ℝ) / (128 * g)) ((H : ℝ) * J / (512 * Real.sqrt T)) ≤ P.secondWidth := by
  by_cases hp₂ : P.first.2 = 0
  · have hd : (0 : ℝ) < g.gcd u := by exact_mod_cast Nat.gcd_pos_of_pos_left u P.factor_pos
    have hroot : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
    have hcompare : (H : ℝ) * J / (512 * Real.sqrt T) ≤ (J : ℝ) / (128 * (g.gcd u : ℝ)) := by
      have hh := mul_le_mul_of_nonneg_right hshort (Nat.cast_nonneg J)
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    have hlower := (min_le_right ((H : ℝ) / (128 * g)) _).trans hcompare
    exact ⟨hlower.trans (P.widths_lower_of_axis hp₂).1, hlower.trans (P.widths_lower_of_axis hp₂).2⟩
  · have hh := P.widths_lower_of_second_coordinate hp₂
    exact ⟨(min_le_left _ _).trans hh.1, (min_le_left _ _).trans hh.2⟩

end ReducedLatticeBox

end Erdos587
