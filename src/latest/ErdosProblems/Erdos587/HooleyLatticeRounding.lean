import ErdosProblems.Erdos587.NVDevelopment

/-! # Projected rounding cells and control of real widths by lattice points -/

namespace Erdos587.GeneralizedAP

theorem delta_projected_cube_rounding {d n : ℕ}
    (q : (Fin d → ℤ) →ₗ[ℤ] (Fin n → ℤ)) (hq : Function.Surjective q)
    (x : Fin n → ℝ) :
    ∃ v : Fin n → ℤ, ∃ e : Fin d → ℝ,
      (∀ i, |e i| ≤ (1 / 2 : ℝ)) ∧ x - intCastVec v = intLinearMapRealExtension q e := by
  obtain ⟨y, hy⟩ := intLinearMapRealExtension_surjective q hq x
  let w : Fin d → ℤ := fun i => round (y i)
  let e := y - intCastVec w
  refine ⟨q w, e, ?_, ?_⟩
  · intro i
    exact abs_sub_round (y i)
  · rw [show e = y - intCastVec w from rfl, map_sub, intLinearMapRealExtension_intCastVec, hy]

theorem delta_real_width_le_twice_lattice_width {n : ℕ} {B : Set (Fin n → ℝ)}
    (hcompact : IsCompact B) (hzero : (0 : Fin n → ℝ) ∈ B) (hconv : Convex ℝ B)
    (hneg : ∀ x ∈ B, -x ∈ B)
    (hround : ∀ x : Fin n → ℝ, ∃ v : Fin n → ℤ,
      x - intCastVec v ∈ bodyDilate (1 / 4 : ℝ) B)
    (ℓ : (Fin n → ℝ) →ₗ[ℝ] ℝ) (M : ℝ)
    (hbound : ∀ v : Fin n → ℤ, intCastVec v ∈ B → |ℓ (intCastVec v)| ≤ M) :
    ∀ x ∈ B, |ℓ x| ≤ 2 * M := by
  have hcont : Continuous (fun x : Fin n → ℝ => |ℓ x|) :=
    continuous_abs.comp ℓ.continuous_of_finiteDimensional
  obtain ⟨x₀, hx₀, hmax⟩ := hcompact.exists_isMaxOn ⟨0, hzero⟩ hcont.continuousOn
  obtain ⟨v, e, he, heq⟩ := hround ((3 / 4 : ℝ) • x₀)
  have hv : intCastVec v ∈ B := by
    have hh := hconv hx₀ (hneg e he) (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (3 / 4 : ℝ) + 1 / 4 = 1)
    have hid : (3 / 4 : ℝ) • x₀ + (1 / 4 : ℝ) • (-e) = intCastVec v := by
      rw [smul_neg, heq]
      abel
    exact hid ▸ hh
  have hid : (3 / 4 : ℝ) • x₀ = intCastVec v + (1 / 4 : ℝ) • e := by
    rw [heq]
    abel
  have hmain : (3 / 4 : ℝ) * |ℓ x₀| ≤ M + (1 / 4 : ℝ) * |ℓ x₀| := by
    calc
      _ = |ℓ ((3 / 4 : ℝ) • x₀)| := by
        rw [map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)]
      _ = |ℓ (intCastVec v) + (1 / 4 : ℝ) * ℓ e| := by rw [hid, map_add, map_smul, smul_eq_mul]
      _ ≤ |ℓ (intCastVec v)| + |(1 / 4 : ℝ) * ℓ e| := abs_add_le _ _
      _ = |ℓ (intCastVec v)| + (1 / 4 : ℝ) * |ℓ e| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      _ ≤ M + (1 / 4 : ℝ) * |ℓ x₀| :=
        add_le_add (hbound v hv) (mul_le_mul_of_nonneg_left (hmax he) (by norm_num))
  have hmaxBound : |ℓ x₀| ≤ 2 * M := by linarith
  intro x hx
  exact (hmax hx).trans hmaxBound

end Erdos587.GeneralizedAP
