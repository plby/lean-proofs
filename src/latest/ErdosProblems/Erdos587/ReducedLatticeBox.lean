import ErdosProblems.Erdos587.LatticeNaturalRectangle
import ErdosProblems.Erdos587.LatticeProperness
import ErdosProblems.Erdos587.LatticeBoxSize
import ErdosProblems.Erdos587.LatticeDualBound

/-! A constructed reduced affine-lattice box, with its natural primitive image. -/

namespace Erdos587

structure ReducedLatticeBox (g u v t H J : ℕ) where
  first : ℤ × ℤ
  second : ℤ × ℤ
  center : ℤ × ℤ
  factor_pos : 0 < g
  width_pos : 0 < H
  height_pos : 0 < J
  coprime : u.Coprime v
  basis : IsCongruenceBasis g u v first second
  order : latticeScaledSq H J first ≤ latticeScaledSq H J second
  reduced : |latticeScaledInner H J first second| ≤ latticeScaledSq H J first / 2
  small : latticeScaledNorm H J second ≤ 1 / 128
  coset : (g : ℤ) ∣ t + latticeLinear u v center
  center_first : |(center.1 : ℝ) - (H : ℝ) / 2| ≤
    (H : ℝ) * (latticeScaledNorm H J first + latticeScaledNorm H J second) / 2
  center_second : |(center.2 : ℝ) - (J : ℝ) / 2| ≤
    (J : ℝ) * (latticeScaledNorm H J first + latticeScaledNorm H J second) / 2

theorem exists_reduced_lattice_box {g u v H J : ℕ} (t : ℕ)
    (hg : 0 < g) (hH : 0 < H) (hJ : 0 < J) (huv : u.Coprime v)
    (hJH : J ≤ H) (hsmall : 256 * g ≤ J) : Nonempty (ReducedLatticeBox g u v t H J) := by
  obtain ⟨p, q, hbasis, horder, hinner⟩ := exists_reduced_congruence_basis (g := g) huv hH hJ
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg
  have hnorm := reduced_congruence_basis_second_norm_le hHR hJR
    (by exact_mod_cast hJH) hgZ hbasis horder hinner
  have hnormSmall : latticeScaledNorm H J q ≤ 1 / 128 := by
    apply hnorm.trans
    apply (div_le_iff₀ hJR).mpr
    have hh : 256 * (g : ℝ) ≤ J := by exact_mod_cast hsmall
    push_cast
    linarith
  obtain ⟨z, hz, hx, hy⟩ := exists_centered_congruence_point (t := (t : ℤ))
    hgZ.ne' hHR hJR huv.isCoprime hbasis
  exact ⟨⟨p, q, z, hg, hH, hJ, huv, hbasis, horder, hinner, hnormSmall, hz, hx, hy⟩⟩

namespace ReducedLatticeBox

variable {g u v t H J : ℕ} (P : ReducedLatticeBox g u v t H J)

noncomputable def firstHalfWidth : ℕ := latticeHalfWidth (latticeScaledNorm H J P.first)
noncomputable def secondHalfWidth : ℕ := latticeHalfWidth (latticeScaledNorm H J P.second)
noncomputable def firstWidth : ℕ := 2 * P.firstHalfWidth
noncomputable def secondWidth : ℕ := 2 * P.secondHalfWidth
def firstStep : ℕ := latticeBoxStep g u v P.first
def secondStep : ℕ := latticeBoxStep g u v P.second
noncomputable def base : ℕ :=
  latticeBoxNaturalBase g u v t P.first P.second P.center P.firstHalfWidth P.secondHalfWidth

lemma first_ne_zero : P.first ≠ 0 := P.basis.first_ne_zero (by exact_mod_cast P.factor_pos.ne')
lemma second_ne_zero : P.second ≠ 0 := P.basis.second_ne_zero (by exact_mod_cast P.factor_pos.ne')

lemma firstNorm_pos : 0 < latticeScaledNorm H J P.first :=
  latticeScaledNorm_pos (by exact_mod_cast P.width_pos.ne')
    (by exact_mod_cast P.height_pos.ne') P.first_ne_zero

lemma secondNorm_pos : 0 < latticeScaledNorm H J P.second :=
  latticeScaledNorm_pos (by exact_mod_cast P.width_pos.ne')
    (by exact_mod_cast P.height_pos.ne') P.second_ne_zero

lemma norm_order : latticeScaledNorm H J P.first ≤ latticeScaledNorm H J P.second :=
  Real.sqrt_le_sqrt P.order

lemma first_small : latticeScaledNorm H J P.first ≤ 1 / 128 := P.norm_order.trans P.small

lemma firstWidth_pos : 0 < P.firstWidth := by
  exact Nat.mul_pos (by omega) (latticeHalfWidth_bounds P.firstNorm_pos P.first_small).1

lemma secondWidth_pos : 0 < P.secondWidth := by
  exact Nat.mul_pos (by omega) (latticeHalfWidth_bounds P.secondNorm_pos P.small).1

theorem central_quarter : ∀ x ≤ 2 * P.firstHalfWidth, ∀ y ≤ 2 * P.secondHalfWidth,
    let w := positiveLatticeBoxPoint g u v P.first P.second P.center P.firstHalfWidth P.secondHalfWidth x y
    ((w.1 : ℝ) ∈ Set.Icc ((H : ℝ) / 4) (3 * H / 4)) ∧
      ((w.2 : ℝ) ∈ Set.Icc ((J : ℝ) / 4) (3 * J / 4)) := by
  intro x hx y hy
  apply latticeHalfWidth_box_mem_central_quarter
    (by exact_mod_cast P.width_pos) (by exact_mod_cast P.height_pos) P.first_ne_zero P.second_ne_zero
    P.center_first P.center_second P.first_small P.small
  · exact signedBoxCoefficient_bound _ hx
  · exact signedBoxCoefficient_bound _ hy

theorem image : ∀ x ≤ P.firstWidth, ∀ y ≤ P.secondWidth,
    ∃ X ≤ H, ∃ Y ≤ J, g ^ 2 * (P.base + P.firstStep * x + P.secondStep * y) =
      g * (t + u * X + v * Y) := by
  intro x hx y hy
  obtain ⟨hX, hY, heq⟩ := lattice_box_natural_image P.factor_pos P.basis P.coset P.central_quarter x hx y hy
  exact ⟨_, hX, _, hY, heq⟩

theorem coprime_steps : P.firstStep.Coprime P.secondStep :=
  P.basis.image_natAbs_coprime (by exact_mod_cast P.factor_pos.ne') P.coprime.isCoprime

theorem positive_steps
    (hproper : ∀ x₁ ≤ H, ∀ y₁ ≤ J, ∀ x₂ ≤ H, ∀ y₂ ≤ J,
      t + u * x₁ + v * y₁ = t + u * x₂ + v * y₂ → x₁ = x₂ ∧ y₁ = y₂) :
    0 < P.firstStep ∧ 0 < P.secondStep := by
  have hh := congruence_basis_image_nonzero P.factor_pos P.width_pos P.height_pos P.basis hproper
    (by linarith [P.first_small]) (by linarith [P.small])
  exact ⟨Int.natAbs_pos.mpr hh.1, Int.natAbs_pos.mpr hh.2⟩

theorem proper
    (hproper : ∀ x₁ ≤ H, ∀ y₁ ≤ J, ∀ x₂ ≤ H, ∀ y₂ ≤ J,
      t + u * x₁ + v * y₁ = t + u * x₂ + v * y₂ → x₁ = x₂ ∧ y₁ = y₂) :
    ∀ x₁ ≤ P.firstWidth, ∀ y₁ ≤ P.secondWidth, ∀ x₂ ≤ P.firstWidth, ∀ y₂ ≤ P.secondWidth,
      P.base + P.firstStep * x₁ + P.secondStep * y₁ =
        P.base + P.firstStep * x₂ + P.secondStep * y₂ → x₁ = x₂ ∧ y₁ = y₂ :=
  lattice_box_natural_proper P.factor_pos P.basis P.coset P.central_quarter hproper

end ReducedLatticeBox

end Erdos587
