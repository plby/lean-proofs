import ErdosProblems.Erdos587.ReducedBasisGeometry
import ErdosProblems.Erdos587.CongruenceBasisImage

/-! Properness prevents short lattice directions from having zero projected step. -/

namespace Erdos587

theorem latticeLinear_ne_zero_of_proper {t u v H J : ℕ} {p : ℤ × ℤ}
    (hproper : ∀ x₁ ≤ H, ∀ y₁ ≤ J, ∀ x₂ ≤ H, ∀ y₂ ≤ J,
      t + u * x₁ + v * y₁ = t + u * x₂ + v * y₂ → x₁ = x₂ ∧ y₁ = y₂)
    (hp : p ≠ 0) (hpx : |p.1| ≤ H) (hpy : |p.2| ≤ J) : latticeLinear u v p ≠ 0 := by
  have hxp : p.1.toNat ≤ H := Int.toNat_le.mpr ((le_abs_self p.1).trans hpx)
  have hxm : (-p.1).toNat ≤ H := Int.toNat_le.mpr ((neg_le_abs p.1).trans hpx)
  have hyp : p.2.toNat ≤ J := Int.toNat_le.mpr ((le_abs_self p.2).trans hpy)
  have hym : (-p.2).toNat ≤ J := Int.toNat_le.mpr ((neg_le_abs p.2).trans hpy)
  intro hzero
  have hzero' : (u : ℤ) * p.1 + (v : ℤ) * p.2 = 0 := hzero
  rw [← p.1.toNat_sub_toNat_neg, ← p.2.toNat_sub_toNat_neg] at hzero'
  have heqZ : (t : ℤ) + u * (p.1.toNat : ℤ) + v * (p.2.toNat : ℤ) =
      (t : ℤ) + u * ((-p.1).toNat : ℤ) + v * ((-p.2).toNat : ℤ) := by nlinarith
  have heq : t + u * p.1.toNat + v * p.2.toNat =
      t + u * (-p.1).toNat + v * (-p.2).toNat := by exact_mod_cast heqZ
  obtain ⟨hx, hy⟩ := hproper p.1.toNat hxp p.2.toNat hyp (-p.1).toNat hxm (-p.2).toNat hym heq
  apply hp
  ext <;> simp only [Prod.fst_zero, Prod.snd_zero] <;> omega

theorem latticeLinear_ne_zero_of_small_norm {t u v H J : ℕ} {p : ℤ × ℤ}
    (hH : 0 < H) (hJ : 0 < J)
    (hproper : ∀ x₁ ≤ H, ∀ y₁ ≤ J, ∀ x₂ ≤ H, ∀ y₂ ≤ J,
      t + u * x₁ + v * y₁ = t + u * x₂ + v * y₂ → x₁ = x₂ ∧ y₁ = y₂)
    (hp : p ≠ 0) (hsmall : latticeScaledNorm H J p ≤ 1) : latticeLinear u v p ≠ 0 := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  apply latticeLinear_ne_zero_of_proper hproper hp
  · have hh : |(p.1 : ℝ)| ≤ H := by
      calc
        _ ≤ (H : ℝ) * latticeScaledNorm H J p := abs_first_coordinate_le_scaledNorm hHR p
        _ ≤ (H : ℝ) * 1 := mul_le_mul_of_nonneg_left hsmall hHR.le
        _ = H := mul_one _
    exact_mod_cast hh
  · have hh : |(p.2 : ℝ)| ≤ J := by
      calc
        _ ≤ (J : ℝ) * latticeScaledNorm H J p := abs_second_coordinate_le_scaledNorm hJR p
        _ ≤ (J : ℝ) * 1 := mul_le_mul_of_nonneg_left hsmall hJR.le
        _ = J := mul_one _
    exact_mod_cast hh

theorem congruence_basis_image_nonzero {g t u v H J : ℕ} {p q : ℤ × ℤ}
    (hg : 0 < g) (hH : 0 < H) (hJ : 0 < J)
    (hbasis : IsCongruenceBasis g u v p q)
    (hproper : ∀ x₁ ≤ H, ∀ y₁ ≤ J, ∀ x₂ ≤ H, ∀ y₂ ≤ J,
      t + u * x₁ + v * y₁ = t + u * x₂ + v * y₂ → x₁ = x₂ ∧ y₁ = y₂)
    (hpSmall : latticeScaledNorm H J p ≤ 1) (hqSmall : latticeScaledNorm H J q ≤ 1) :
    latticeLinear u v p / (g : ℤ) ≠ 0 ∧ latticeLinear u v q / (g : ℤ) ≠ 0 := by
  have hgZ : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have hp := latticeLinear_ne_zero_of_small_norm hH hJ hproper (hbasis.first_ne_zero hgZ) hpSmall
  have hq := latticeLinear_ne_zero_of_small_norm hH hJ hproper (hbasis.second_ne_zero hgZ) hqSmall
  constructor
  · intro hh
    have hcancel := Int.mul_ediv_cancel' hbasis.first_mem
    rw [hh, mul_zero] at hcancel
    exact hp hcancel.symm
  · intro hh
    have hcancel := Int.mul_ediv_cancel' hbasis.second_mem
    rw [hh, mul_zero] at hcancel
    exact hq hcancel.symm

end Erdos587
