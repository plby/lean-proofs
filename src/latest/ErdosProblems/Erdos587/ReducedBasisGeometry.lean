import ErdosProblems.Erdos587.ReducedCongruenceBasis

/-! Determinant and norm bounds for the reduced rectangularly scaled basis. -/

namespace Erdos587

noncomputable def latticeScaledNorm (H J : ℝ) (p : ℤ × ℤ) : ℝ :=
  Real.sqrt (latticeScaledSq H J p)

lemma latticeScaledNorm_nonneg (H J : ℝ) (p : ℤ × ℤ) : 0 ≤ latticeScaledNorm H J p :=
  Real.sqrt_nonneg _

lemma latticeScaledNorm_sq (H J : ℝ) (p : ℤ × ℤ) :
    latticeScaledNorm H J p ^ 2 = latticeScaledSq H J p :=
  Real.sq_sqrt (latticeScaledSq_nonneg H J p)

lemma latticeScaledNorm_pos {H J : ℝ} (hH : H ≠ 0) (hJ : J ≠ 0)
    {p : ℤ × ℤ} (hp : p ≠ 0) : 0 < latticeScaledNorm H J p :=
  Real.sqrt_pos.mpr (latticeScaledSq_pos hH hJ hp)

lemma lattice_gram_identity (H J : ℝ) (p q : ℤ × ℤ) :
    latticeScaledSq H J p * latticeScaledSq H J q - latticeScaledInner H J p q ^ 2 =
      ((latticeDet p q : ℝ) / (H * J)) ^ 2 := by
  unfold latticeScaledSq latticeScaledInner latticeDet
  push_cast
  ring

lemma IsCongruenceBasis.first_ne_zero {g u v : ℤ} {p q : ℤ × ℤ}
    (h : IsCongruenceBasis g u v p q) (hg : g ≠ 0) : p ≠ 0 := by
  intro hp
  have hh := h.1
  simp only [hp, latticeDet, Prod.fst_zero, Prod.snd_zero, zero_mul, sub_zero, abs_zero] at hh
  exact hg hh.symm

lemma IsCongruenceBasis.second_ne_zero {g u v : ℤ} {p q : ℤ × ℤ}
    (h : IsCongruenceBasis g u v p q) (hg : g ≠ 0) : q ≠ 0 := h.swap.first_ne_zero hg

theorem reduced_congruence_basis_product_bounds {g u v : ℤ} {p q : ℤ × ℤ}
    {H J : ℝ} (hH : 0 < H) (hJ : 0 < J) (hg : 0 < g)
    (hbasis : IsCongruenceBasis g u v p q)
    (horder : latticeScaledSq H J p ≤ latticeScaledSq H J q)
    (hinner : |latticeScaledInner H J p q| ≤ latticeScaledSq H J p / 2) :
    (g : ℝ) / (H * J) ≤ latticeScaledNorm H J p * latticeScaledNorm H J q ∧
      latticeScaledNorm H J p * latticeScaledNorm H J q ≤ 2 * ((g : ℝ) / (H * J)) := by
  have hQp := latticeScaledSq_nonneg H J p
  have hQq := latticeScaledSq_nonneg H J q
  have hNp := latticeScaledNorm_nonneg H J p
  have hNq := latticeScaledNorm_nonneg H J q
  have hdelta : 0 < (g : ℝ) / (H * J) := by
    have hgR : (0 : ℝ) < g := by exact_mod_cast hg
    positivity
  have hdet : |(latticeDet p q : ℝ)| = (g : ℝ) := by exact_mod_cast hbasis.1
  have hgram : (latticeScaledNorm H J p * latticeScaledNorm H J q) ^ 2 -
      latticeScaledInner H J p q ^ 2 = ((g : ℝ) / (H * J)) ^ 2 := by
    rw [mul_pow, latticeScaledNorm_sq, latticeScaledNorm_sq, lattice_gram_identity]
    rw [div_pow, ← sq_abs (latticeDet p q : ℝ), hdet, ← div_pow]
  have hinnerSq : 4 * latticeScaledInner H J p q ^ 2 ≤
      latticeScaledSq H J p * latticeScaledSq H J q := by
    have hh := pow_le_pow_left₀ (abs_nonneg (latticeScaledInner H J p q)) hinner 2
    rw [sq_abs] at hh
    have hQQ := mul_le_mul_of_nonneg_left horder hQp
    nlinarith
  have hprodSq : (latticeScaledNorm H J p * latticeScaledNorm H J q) ^ 2 =
      latticeScaledSq H J p * latticeScaledSq H J q := by
    rw [mul_pow, latticeScaledNorm_sq, latticeScaledNorm_sq]
  have hprod0 := mul_nonneg hNp hNq
  constructor
  · nlinarith [sq_nonneg (latticeScaledInner H J p q)]
  · nlinarith

lemma abs_first_coordinate_le_scaledNorm {H J : ℝ} (hH : 0 < H) (p : ℤ × ℤ) :
    |(p.1 : ℝ)| ≤ H * latticeScaledNorm H J p := by
  have hh : ((p.1 : ℝ) / H) ^ 2 ≤ latticeScaledSq H J p := by
    unfold latticeScaledSq
    linarith [sq_nonneg ((p.2 : ℝ) / J)]
  have hroot := Real.sqrt_le_sqrt hh
  rw [Real.sqrt_sq_eq_abs, abs_div, abs_of_pos hH] at hroot
  change |(p.1 : ℝ)| / H ≤ latticeScaledNorm H J p at hroot
  have hscaled := (div_le_iff₀ hH).mp hroot
  nlinarith

lemma abs_second_coordinate_le_scaledNorm {H J : ℝ} (hJ : 0 < J) (p : ℤ × ℤ) :
    |(p.2 : ℝ)| ≤ J * latticeScaledNorm H J p := by
  have hh : ((p.2 : ℝ) / J) ^ 2 ≤ latticeScaledSq H J p := by
    unfold latticeScaledSq
    linarith [sq_nonneg ((p.1 : ℝ) / H)]
  have hroot := Real.sqrt_le_sqrt hh
  rw [Real.sqrt_sq_eq_abs, abs_div, abs_of_pos hJ] at hroot
  change |(p.2 : ℝ)| / J ≤ latticeScaledNorm H J p at hroot
  have hscaled := (div_le_iff₀ hJ).mp hroot
  nlinarith

lemma one_le_width_mul_scaledNorm {H J : ℝ} (hH : 0 < H) (hJ : 0 < J) (hJH : J ≤ H)
    {p : ℤ × ℤ} (hp : p ≠ 0) : 1 ≤ H * latticeScaledNorm H J p := by
  by_cases hx : p.1 = 0
  · have hy : p.2 ≠ 0 := by
      intro hh
      apply hp
      ext <;> simp only [Prod.fst_zero, Prod.snd_zero] <;> assumption
    have habs : (1 : ℝ) ≤ |(p.2 : ℝ)| := by exact_mod_cast Int.one_le_abs hy
    calc
      1 ≤ |(p.2 : ℝ)| := habs
      _ ≤ J * latticeScaledNorm H J p := abs_second_coordinate_le_scaledNorm hJ p
      _ ≤ H * latticeScaledNorm H J p :=
        mul_le_mul_of_nonneg_right hJH (latticeScaledNorm_nonneg H J p)
  · have habs : (1 : ℝ) ≤ |(p.1 : ℝ)| := by exact_mod_cast Int.one_le_abs hx
    exact habs.trans (abs_first_coordinate_le_scaledNorm hH p)

theorem reduced_congruence_basis_second_norm_le {g u v : ℤ} {p q : ℤ × ℤ}
    {H J : ℝ} (hH : 0 < H) (hJ : 0 < J) (hJH : J ≤ H) (hg : 0 < g)
    (hbasis : IsCongruenceBasis g u v p q)
    (horder : latticeScaledSq H J p ≤ latticeScaledSq H J q)
    (hinner : |latticeScaledInner H J p q| ≤ latticeScaledSq H J p / 2) :
    latticeScaledNorm H J q ≤ 2 * (g : ℝ) / J := by
  have hprod := (reduced_congruence_basis_product_bounds hH hJ hg hbasis horder hinner).2
  have hfirst := one_le_width_mul_scaledNorm hH hJ hJH (hbasis.first_ne_zero hg.ne')
  have hh := mul_le_mul_of_nonneg_left hprod hH.le
  have hcancel : H * (2 * ((g : ℝ) / (H * J))) = 2 * (g : ℝ) / J := by field_simp
  rw [hcancel] at hh
  have hsmall := mul_le_mul_of_nonneg_right hfirst (latticeScaledNorm_nonneg H J q)
  nlinarith

end Erdos587
