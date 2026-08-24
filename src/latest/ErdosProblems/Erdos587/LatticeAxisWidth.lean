import ErdosProblems.Erdos587.ReducedBasisGeometry
import ErdosProblems.Erdos587.LatticeBoxSize

/-! The two lower-width cases: a nonzero second coordinate, or an axis vector. -/

namespace Erdos587

lemma gcd_axis_divisibility {g u : ℕ} {a : ℤ} (hdiv : (g : ℤ) ∣ (u : ℤ) * a) :
    (g : ℤ) ∣ (g.gcd u : ℤ) * a := by
  have heq : (g.gcd u : ℤ) * a =
      (g : ℤ) * (g.gcdA u * a) + ((u : ℤ) * a) * g.gcdB u := by
    rw [Nat.gcd_eq_gcd_ab]
    ring
  rw [heq]
  exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left hdiv _)

lemma gcd_axis_coordinate_lower {g u : ℕ} (hg : 0 < g) {a : ℤ} (ha : a ≠ 0)
    (hdiv : (g : ℤ) ∣ (u : ℤ) * a) : (g : ℤ) ≤ (g.gcd u : ℤ) * |a| := by
  have hd : 0 < g.gcd u := Nat.gcd_pos_of_pos_left u hg
  have hdZ : (0 : ℤ) < g.gcd u := by exact_mod_cast hd
  have hne : (g.gcd u : ℤ) * a ≠ 0 := mul_ne_zero hdZ.ne' ha
  have hh := Int.le_of_dvd (abs_pos.mpr hne)
    ((dvd_abs (g : ℤ) ((g.gcd u : ℤ) * a)).mpr (gcd_axis_divisibility hdiv))
  simpa only [abs_mul, abs_of_pos hdZ] using hh

theorem reduced_basis_second_norm_of_second_coordinate {g u v : ℤ} {p q : ℤ × ℤ}
    {H J : ℝ} (hH : 0 < H) (hJ : 0 < J) (hg : 0 < g)
    (hbasis : IsCongruenceBasis g u v p q)
    (horder : latticeScaledSq H J p ≤ latticeScaledSq H J q)
    (hinner : |latticeScaledInner H J p q| ≤ latticeScaledSq H J p / 2)
    (hp₂ : p.2 ≠ 0) : latticeScaledNorm H J q ≤ 2 * (g : ℝ) / H := by
  have hfirst : 1 ≤ J * latticeScaledNorm H J p := by
    have hh : (1 : ℝ) ≤ |(p.2 : ℝ)| := by exact_mod_cast Int.one_le_abs hp₂
    exact hh.trans (abs_second_coordinate_le_scaledNorm hJ p)
  have hprod := (reduced_congruence_basis_product_bounds hH hJ hg hbasis horder hinner).2
  have hh := mul_le_mul_of_nonneg_left hprod hJ.le
  have hcancel : J * (2 * ((g : ℝ) / (H * J))) = 2 * (g : ℝ) / H := by field_simp
  rw [hcancel] at hh
  have hsmall := mul_le_mul_of_nonneg_right hfirst (latticeScaledNorm_nonneg H J q)
  nlinarith

theorem reduced_basis_second_norm_of_axis {g u v : ℕ} {p q : ℤ × ℤ}
    {H J : ℝ} (hH : 0 < H) (hJ : 0 < J) (hg : 0 < g)
    (hbasis : IsCongruenceBasis g u v p q)
    (horder : latticeScaledSq H J p ≤ latticeScaledSq H J q)
    (hinner : |latticeScaledInner H J p q| ≤ latticeScaledSq H J p / 2)
    (hp₂ : p.2 = 0) : latticeScaledNorm H J q ≤ 2 * (g.gcd u : ℝ) / J := by
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hdR : (0 : ℝ) < g.gcd u := by exact_mod_cast Nat.gcd_pos_of_pos_left u hg
  have hp : p ≠ 0 := hbasis.first_ne_zero hgZ.ne'
  have hp₁ : p.1 ≠ 0 := by
    intro hh
    apply hp
    ext <;> simp only [Prod.fst_zero, Prod.snd_zero] <;> assumption
  have hdiv : (g : ℤ) ∣ (u : ℤ) * p.1 := by
    simpa only [latticeLinear, hp₂, mul_zero, add_zero] using hbasis.first_mem
  have hcoord : (g : ℝ) ≤ (g.gcd u : ℝ) * |(p.1 : ℝ)| := by
    exact_mod_cast gcd_axis_coordinate_lower hg hp₁ hdiv
  have hfirst : (g : ℝ) ≤ (g.gcd u : ℝ) * (H * latticeScaledNorm H J p) :=
    hcoord.trans (mul_le_mul_of_nonneg_left (abs_first_coordinate_le_scaledNorm hH p) hdR.le)
  have hprod := (reduced_congruence_basis_product_bounds hH hJ hgZ hbasis horder hinner).2
  push_cast at hprod
  have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ (g.gcd u : ℝ) * H by positivity)
  have hcancel : ((g.gcd u : ℝ) * H) * (2 * ((g : ℝ) / (H * J))) =
      (g : ℝ) * (2 * (g.gcd u : ℝ) / J) := by field_simp
  rw [hcancel] at hh
  have hsmall := mul_le_mul_of_nonneg_right hfirst (latticeScaledNorm_nonneg H J q)
  apply (mul_le_mul_iff_right₀ hgR).mp
  nlinarith

end Erdos587
