import ErdosProblems.Erdos587.NVDevelopment

/-! # Centered zonotopes and their exact one-dimensional widths -/

open scoped BigOperators

namespace Erdos587.CFP

noncomputable def deltaZonotope {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℝ) : Set (Fin d → ℝ) :=
  (Fintype.linearCombination ℝ v) '' Set.Icc (fun _ => -(1 / 2 : ℝ)) (fun _ => (1 / 2 : ℝ))

lemma deltaZonotope_zero {ι : Type*} [Fintype ι] {d : ℕ} (v : ι → Fin d → ℝ) :
    (0 : Fin d → ℝ) ∈ deltaZonotope v := by
  exact ⟨0, ⟨fun _ => by norm_num, fun _ => by norm_num⟩, map_zero _⟩

lemma deltaZonotope_convex {ι : Type*} [Fintype ι] {d : ℕ} (v : ι → Fin d → ℝ) :
    Convex ℝ (deltaZonotope v) := (convex_Icc _ _).linear_image _

lemma deltaZonotope_compact {ι : Type*} [Fintype ι] {d : ℕ} (v : ι → Fin d → ℝ) :
    IsCompact (deltaZonotope v) :=
  isCompact_Icc.image (Fintype.linearCombination ℝ v).continuous_of_finiteDimensional

lemma deltaZonotope_neg {ι : Type*} [Fintype ι] {d : ℕ} (v : ι → Fin d → ℝ) :
    ∀ x ∈ deltaZonotope v, -x ∈ deltaZonotope v := by
  rintro x ⟨θ, hθ, rfl⟩
  refine ⟨-θ, ⟨?_, ?_⟩, map_neg _ _⟩
  · intro i
    have hh := hθ.2 i
    change -(1 / 2 : ℝ) ≤ -(θ i)
    linarith
  · intro i
    have hh := hθ.1 i
    change -(θ i) ≤ (1 / 2 : ℝ)
    linarith

lemma deltaZonotope_exists_support_point {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℝ) (ℓ : (Fin d → ℝ) →ₗ[ℝ] ℝ) :
    ∃ x ∈ deltaZonotope v, ℓ x = (1 / 2 : ℝ) * ∑ i, |ℓ (v i)| := by
  classical
  let θ : ι → ℝ := fun i => if 0 ≤ ℓ (v i) then 1 / 2 else -(1 / 2)
  refine ⟨Fintype.linearCombination ℝ v θ, ⟨θ, ?_, rfl⟩, ?_⟩
  · constructor <;> intro i <;> dsimp only [θ] <;> split_ifs <;> norm_num
  · rw [Fintype.linearCombination_apply, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, smul_eq_mul]
    dsimp only [θ]
    by_cases hi : 0 ≤ ℓ (v i)
    · rw [if_pos hi, abs_of_nonneg hi]
    · rw [if_neg hi, abs_of_neg (lt_of_not_ge hi)]
      ring

lemma delta_zonotope_coordinate_mass_le {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℝ) {B : Set (Fin d → ℝ)} {δ M : ℝ} (hδ : 0 < δ)
    (hsub : ∀ x ∈ deltaZonotope v, δ • x ∈ B)
    (ℓ : (Fin d → ℝ) →ₗ[ℝ] ℝ) (hbound : ∀ x ∈ B, |ℓ x| ≤ M) :
    (∑ i, |ℓ (v i)|) ≤ 2 * M / δ := by
  obtain ⟨x, hx, heq⟩ := deltaZonotope_exists_support_point v ℓ
  have hh := (le_abs_self (ℓ (δ • x))).trans (hbound _ (hsub x hx))
  rw [map_smul, smul_eq_mul, heq] at hh
  apply (le_div_iff₀ hδ).mpr
  linarith

end Erdos587.CFP
