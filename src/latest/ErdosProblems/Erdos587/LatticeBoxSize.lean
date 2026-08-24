import ErdosProblems.Erdos587.LatticeBox

/-! Width, volume, and image-span budgets for the rounded lattice box. -/

namespace Erdos587

lemma latticeHalfWidth_lower {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 128) :
    1 / (128 * s) ≤ (latticeHalfWidth s : ℝ) := by
  have hh := (latticeHalfWidth_bounds hs hsmall).2.1
  apply (div_le_iff₀ (by positivity : 0 < 128 * s)).mpr
  nlinarith

lemma latticeFullWidth_lower {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 128) :
    1 / (64 * s) ≤ (2 * latticeHalfWidth s : ℕ) := by
  have hh := (latticeHalfWidth_bounds hs hsmall).2.1
  apply (div_le_iff₀ (by positivity : 0 < 64 * s)).mpr
  push_cast
  nlinarith

theorem lattice_box_volume_lower {s₁ s₂ H J g : ℝ}
    (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (hH : 0 < H) (hJ : 0 < J) (hg : 0 < g)
    (hsmall₁ : s₁ ≤ 1 / 128) (hsmall₂ : s₂ ≤ 1 / 128)
    (hprod : s₁ * s₂ ≤ 2 * (g / (H * J))) :
    H * J / (8192 * g) ≤
      (2 * latticeHalfWidth s₁ : ℕ) * (2 * latticeHalfWidth s₂ : ℕ) := by
  have hprod' : s₁ * s₂ * (H * J) ≤ 2 * g := by
    have hh := mul_le_mul_of_nonneg_right hprod (mul_pos hH hJ).le
    have heq : (2 * (g / (H * J))) * (H * J) = 2 * g := by field_simp
    rwa [heq] at hh
  calc
    H * J / (8192 * g) ≤ 1 / (4096 * s₁ * s₂) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    _ = (1 / (64 * s₁)) * (1 / (64 * s₂)) := by field_simp; norm_num
    _ ≤ (2 * latticeHalfWidth s₁ : ℕ) * (2 * latticeHalfWidth s₂ : ℕ) := by
      exact mul_le_mul (latticeFullWidth_lower hs₁ hsmall₁)
        (latticeFullWidth_lower hs₂ hsmall₂) (by positivity) (by positivity)

lemma lattice_box_both_widths_lower {s₁ s₂ : ℝ}
    (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (horder : s₁ ≤ s₂) (hsmall₂ : s₂ ≤ 1 / 128) :
    1 / (64 * s₂) ≤ (2 * latticeHalfWidth s₁ : ℕ) ∧
      1 / (64 * s₂) ≤ (2 * latticeHalfWidth s₂ : ℕ) := by
  refine ⟨?_, latticeFullWidth_lower hs₂ hsmall₂⟩
  calc
    _ ≤ 1 / (64 * s₁) := by gcongr
    _ ≤ _ := latticeFullWidth_lower hs₁ (horder.trans hsmall₂)

lemma latticeHalfWidth_controls_functional {s A : ℝ} (hs : 0 < s)
    (hsmall : s ≤ 1 / 128) (hA : 0 ≤ A) : A / s ≤ 128 * (latticeHalfWidth s : ℝ) * A := by
  have hh := mul_le_mul_of_nonneg_left (latticeHalfWidth_lower hs hsmall) (show 0 ≤ 128 * A by positivity)
  have heq : (128 * A) * (1 / (128 * s)) = A / s := by field_simp
  rw [heq] at hh
  nlinarith

theorem lattice_box_span_lower {s₁ s₂ A B W g : ℝ}
    (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (hsmall₁ : s₁ ≤ 1 / 128) (hsmall₂ : s₂ ≤ 1 / 128)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hg : 0 < g)
    (hdual : W ≤ 4 * (A / s₁ + B / s₂)) :
    W / (256 * g) ≤ (2 / g) * ((latticeHalfWidth s₁ : ℝ) * A + (latticeHalfWidth s₂ : ℝ) * B) := by
  have hp := latticeHalfWidth_controls_functional hs₁ hsmall₁ hA
  have hq := latticeHalfWidth_controls_functional hs₂ hsmall₂ hB
  apply (div_le_iff₀ (by positivity : 0 < 256 * g)).mpr
  have heq : ((2 / g) * ((latticeHalfWidth s₁ : ℝ) * A + (latticeHalfWidth s₂ : ℝ) * B)) *
      (256 * g) = 512 * ((latticeHalfWidth s₁ : ℝ) * A + (latticeHalfWidth s₂ : ℝ) * B) := by
    field_simp
    ring
  rw [heq]
  nlinarith

end Erdos587
