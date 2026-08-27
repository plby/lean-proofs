import ErdosProblems.Erdos587.HooleyShrunkenQuotient

/-! # Primitive normalization of a short kernel vector -/

namespace Erdos587.GeneralizedAP

lemma delta_exists_primitive_short_kernel (X : ConvexProgression) {η : ℝ}
    (e : Fin X.rank → ℤ) (he : e ≠ 0) (heval : X.eval e = 0)
    (hbody : intCastVec e ∈ bodyDilate η X.body) :
    ∃ u : Fin X.rank → ℤ, u ≠ 0 ∧ X.eval u = 0 ∧ PrimitiveIntVector u ∧
      intCastVec u ∈ bodyDilate η X.body := by
  classical
  have heCoord : ∃ i, e i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact he (funext hall)
  obtain ⟨c, u, hc, hfactor, hprim, _⟩ := exists_primitiveIntVector_factorization e heCoord
  have heu : e = c • u := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact hfactor i
  have hu : u ≠ 0 := by
    intro hzero
    rw [hzero, smul_zero] at heu
    exact he heu
  have hevalU : X.eval u = 0 := by
    rw [heu, map_zsmul] at heval
    exact (Int.mul_eq_zero.mp heval).resolve_left hc
  obtain ⟨y, hy, hyEq⟩ := hbody
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hinv : ‖(c : ℝ)⁻¹‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_inv]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Int.one_le_abs hc)
  refine ⟨u, hu, hevalU, hprim, (c : ℝ)⁻¹ • y,
    X.body_balanced.smul_mem hinv hy, ?_⟩
  rw [smul_comm, hyEq, heu, ConvexProgression.intCastVec_zsmul, inv_smul_smul₀ hcR]

lemma delta_small_cube_scale_le_quarter (r : ℕ) :
    (1 : ℝ) / 4 ^ (r + 2) ≤ (1 / 4 : ℝ) * (1 / 4 : ℝ) := by
  have hp : (1 : ℝ) ≤ 4 ^ r := one_le_pow₀ (by norm_num)
  rw [pow_add]
  norm_num
  exact inv_le_one_of_one_le₀ hp

lemma delta_small_cube_scale_half_step (n : ℕ) :
    (1 : ℝ) / 4 ^ (n + 1 + 2) ≤ (1 / 4 ^ (n + 2)) * (1 / 2 : ℝ) := by
  rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ]
  have hp : (0 : ℝ) < 4 ^ (n + 2) := by positivity
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 ^ (n + 2) * 4)).mpr
  field_simp
  norm_num

end Erdos587.GeneralizedAP
