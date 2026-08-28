import Wikipedia.HopfProblem.DegreeCollapseMatrixComponentPaths
import Wikipedia.SmoothSixDPoincare.OpenCurveEndpointGerms
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Smooth invertible frame joins in arbitrary finite rank at least two

An actual continuous matrix-coordinate equivalence transfers the constructed
determinant-component paths to the original normed endomorphism space.
Smooth joining inside that open component retains both whole endpoint germs.
-/

noncomputable section

open Set Function Filter Module
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.LinearFramePaths

variable {D ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [Fintype ι] [DecidableEq ι]

def matrixCoordinates (b : Basis ι ℝ D) : (D →L[ℝ] D) ≃L[ℝ] Matrix ι ι ℝ :=
  (LinearMap.toContinuousLinearMap.symm.trans (LinearMap.toMatrix b b)).toContinuousLinearEquiv

theorem det_matrixCoordinates (b : Basis ι ℝ D) (A : D →L[ℝ] D) :
    Matrix.det (matrixCoordinates b A) = A.toLinearMap.det :=
  LinearMap.det_toMatrix b A.toLinearMap

def operatorComponent (σ : ℝ) : TopologicalSpace.Opens (D →L[ℝ] D) :=
  ⟨{A | 0 < σ * A.toLinearMap.det},
    isOpen_lt continuous_const (continuous_const.mul ContinuousLinearMap.continuous_det)⟩

variable [Nontrivial ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Same-sign operators are joined by an actual path in the original normed operator space. -/
theorem joined_operatorComponent [Finite ι] (b : Basis ι ℝ D) {σ : ℝ}
    (A B : operatorComponent (D := D) σ) : Joined A B := by
  classical
  let _ := Fintype.ofFinite ι
  let e := matrixCoordinates b
  let A' : determinantComponent (ι := ι) σ := ⟨e A, by
    change 0 < σ * Matrix.det (matrixCoordinates b A)
    rw [det_matrixCoordinates]
    exact A.property⟩
  let B' : determinantComponent (ι := ι) σ := ⟨e B, by
    change 0 < σ * Matrix.det (matrixCoordinates b B)
    rw [det_matrixCoordinates]
    exact B.property⟩
  let ψ : determinantComponent (ι := ι) σ → operatorComponent (D := D) σ := fun C =>
    ⟨e.symm C, by
      have hd := det_matrixCoordinates b (e.symm C)
      change Matrix.det (e (e.symm C)) = (e.symm C).toLinearMap.det at hd
      rw [e.apply_symm_apply] at hd
      change 0 < σ * (e.symm C).toLinearMap.det
      rw [← hd]
      exact C.property⟩
  have hψ : Continuous ψ := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _
  have hA : ψ A' = A := Subtype.ext (e.symm_apply_apply A)
  have hB : ψ B' = B := Subtype.ext (e.symm_apply_apply B)
  have h := (joined_determinantComponent A' B').map hψ
  rwa [hA, hB] at h

omit [Fintype ι] [DecidableEq ι] in
/-- In every finite rank at least two, construct a globally smooth invertible join
retaining both prescribed endpoint germs and their determinant component. -/
theorem exists_smooth_invertible_frame_join [Finite ι] (basis : Basis ι ℝ D)
    {a b : ℝ → (D →L[ℝ] D)} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V)
    (hU : IsOpen U) (hV : IsOpen V) (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V)
    (hsign : 0 < (a 0).toLinearMap.det * (b 1).toLinearMap.det) :
    ∃ L : ℝ → (D →L[ℝ] D), ContDiff ℝ ∞ L ∧
      (∀ t, Bijective (L t)) ∧
      (∀ t, 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det) ∧
      (L =ᶠ[𝓝 (0 : ℝ)] a) ∧ (L =ᶠ[𝓝 (1 : ℝ)] b) := by
  let σ := (a 0).toLinearMap.det
  let S := operatorComponent (D := D) σ
  have ha0ne : (a 0).toLinearMap.det ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hsign
    exact lt_irrefl _ hsign
  have ha0 : a 0 ∈ S := mul_self_pos.mpr ha0ne
  have hb1 : b 1 ∈ S := hsign
  let γ := (joined_operatorComponent basis (⟨a 0, ha0⟩ : S) ⟨b 1, hb1⟩).somePath
  obtain ⟨L, hL, hmem, hleft, hright⟩ := exists_smooth_open_curve_with_endpoint_germs S
    ha hb hU hV h0U h1V ha0 hb1 γ
  have hpositive (t : ℝ) : 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det := hmem t
  refine ⟨L, hL, ?_, hpositive, hleft, hright⟩
  intro t
  have hdet : (L t).toLinearMap.det ≠ 0 := by
    intro hz
    have hp := hpositive t
    rw [hz, mul_zero] at hp
    exact lt_irrefl _ hp
  have hker : (L t).toLinearMap.ker = ⊥ := by
    by_contra hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  have hi : Injective (L t) := LinearMap.ker_eq_bot.mp hker
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩

end Wikipedia.HopfProblem.DegreeCollapse.LinearFramePaths
