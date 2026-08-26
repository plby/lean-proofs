/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The uniform integer-point estimate for irreducible affine plane curves.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.CurveUniformPower
import ErdosProblems.Erdos477.Geometry.BoundedShear

namespace Erdos477.Counting

open Filter Erdos477.Geometry

variable {K : Type*} [Field K] [CharZero K]

theorem exists_eventual_plane_curve_bound (D : ℕ) (hD : 1 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ P : MvPolynomial (Fin 2) K, Irreducible P → P.totalDegree = D →
      ∀ S : Finset (Fin 2 → ℤ),
      (∀ z ∈ S, MvPolynomial.eval (fun k => (z k : K)) P = 0) →
      (∀ z ∈ S, ∀ k, |(z k : ℝ)| ≤ B) →
      (S.card : ℝ) ≤ C * B ^ (1 / (D : ℝ) + ε) := by
  classical
  obtain ⟨C₀, hC₀, hbound⟩ := exists_uniform_curve_power_bound (K := K) D D hD ε hε
  have hDpos : (0 : ℝ) < D + 1 := by positivity
  have htendsto : Tendsto (fun B : ℝ => (D + 1 : ℝ) * B) atTop atTop :=
    Tendsto.const_mul_atTop hDpos tendsto_id
  refine ⟨C₀ * (D + 1 : ℝ) ^ (1 / (D : ℝ) + ε), by positivity, ?_⟩
  filter_upwards [htendsto.eventually hbound, eventually_ge_atTop (0 : ℝ)] with B hBbound hB
  intro P hP hdegree S hS hheight
  obtain ⟨a, ha, hsheardegree⟩ := exists_bounded_degree_shear P hP.ne_zero
  rw [hdegree] at ha hsheardegree
  let T := S.image (integerShear a)
  have hQ : Irreducible (shear (a : K) P) :=
    (MulEquiv.irreducible_iff (shearEquiv (a : K))).mpr hP
  have hcount := hBbound (shear (a : K) P) hQ
    ((totalDegree_shear _ _).trans hdegree) hsheardegree T (by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      rw [eval_integerShear]
      exact hS z hz) (by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      exact height_integerShear D a ha z B hB (hheight z hz))
  rw [show T.card = S.card from Finset.card_image_of_injective _ (integerShear_injective a),
    Real.mul_rpow hDpos.le hB, ← mul_assoc] at hcount
  exact hcount

noncomputable def integerPlaneBox (B : ℝ) : Finset (Fin 2 → ℤ) := by
  classical
  exact Fintype.piFinset (fun _ : Fin 2 => Finset.Icc (-(⌈B⌉₊ : ℤ)) ⌈B⌉₊)

lemma mem_integerPlaneBox_of_height (B : ℝ) (z : Fin 2 → ℤ)
    (hz : ∀ i, |(z i : ℝ)| ≤ B) : z ∈ integerPlaneBox B := by
  classical
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_Icc.mpr
  apply abs_le.mp
  have h := (hz i).trans (Nat.le_ceil B)
  exact_mod_cast h

/-- For each degree and each positive exponent loss, the constant is
uniform over all irreducible plane equations, including their coefficients. -/
theorem exists_plane_curve_bound (D : ℕ) (hD : 1 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 1 ≤ B →
      ∀ P : MvPolynomial (Fin 2) K, Irreducible P → P.totalDegree = D →
      ∀ S : Finset (Fin 2 → ℤ),
      (∀ z ∈ S, MvPolynomial.eval (fun k => (z k : K)) P = 0) →
      (∀ z ∈ S, ∀ k, |(z k : ℝ)| ≤ B) →
      (S.card : ℝ) ≤ C * B ^ (1 / (D : ℝ) + ε) := by
  obtain ⟨C₀, hC₀, hevent⟩ := exists_eventual_plane_curve_bound (K := K) D hD ε hε
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp hevent
  let F : ℝ := (integerPlaneBox B₀).card
  let C := max C₀ (F + 1)
  have hC : 0 < C := lt_of_lt_of_le hC₀ (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro B hB P hP hdegree S hS hheight
  by_cases hlarge : B₀ ≤ B
  · exact (hB₀ B hlarge P hP hdegree S hS hheight).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _))
  · have hsub : S ⊆ integerPlaneBox B₀ := by
      intro z hz
      exact mem_integerPlaneBox_of_height B₀ z (fun i =>
        (hheight z hz i).trans (le_of_not_ge hlarge))
    have hcard : (S.card : ℝ) ≤ F := by
      dsimp only [F]
      exact_mod_cast Finset.card_le_card hsub
    have hFC : F ≤ C := (le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _)
    have hpower : 1 ≤ B ^ (1 / (D : ℝ) + ε) := Real.one_le_rpow hB (by positivity)
    exact (hcard.trans hFC).trans (le_mul_of_one_le_right hC.le hpower)

#print axioms exists_plane_curve_bound
-- 'Erdos477.Counting.exists_plane_curve_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
