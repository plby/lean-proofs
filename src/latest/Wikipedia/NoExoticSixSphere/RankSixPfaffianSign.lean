import Wikipedia.NoExoticSixSphere.RankSixUnitSpinor
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# The constant Pfaffian sign and signed complex structures

The continuous Pfaffian has values in the two-point set of signs. It is
therefore constant on every preconnected parameter space. Multiplication
by either real sign preserves the actual complex-structure equations.
-/

namespace NoExoticSixSphere.RankSixComplexProjection

open RankSixSkewMatrix

theorem pfaffian_constant {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (J : C(X, OrthogonalComplexStructures.Space 6)) (x y : X) :
    pfaffian (matrix (J x)) = pfaffian (matrix (J y)) := by
  let f : X → ℝ := fun x ↦ pfaffian (matrix (J x))
  have hc : Continuous f := continuous_pfaffian.comp (continuous_matrix.comp J.continuous)
  have hf : (Set.range f).Finite := by
    apply (Set.toFinite ({1, -1} : Set ℝ)).subset
    rintro _ ⟨z, rfl⟩
    have hs := pfaffian_sq_one (matrix (J z)) (matrix_transpose _) (matrix_square _)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, f] using sq_eq_one_iff.mp hs
  exact ((isPreconnected_range hc).isDiscrete_iff_subsingleton.mp hf.isDiscrete)
    ⟨x, rfl⟩ ⟨y, rfl⟩

theorem matrix_injective : Function.Injective matrix := by
  intro J K h
  apply Subtype.ext
  apply Subtype.ext
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 6)).symm.injective h

noncomputable def signScale (c : ℝ) (hc : c ^ 2 = 1)
    (J : OrthogonalComplexStructures.Space 6) : OrthogonalComplexStructures.Space 6 :=
  ofMatrix (c • matrix J)
    (by simp only [Matrix.transpose_smul, matrix_transpose, smul_neg])
    (by
      rw [smul_mul_smul, matrix_square]
      simp only [← pow_two, hc, one_smul])

theorem matrix_signScale (c : ℝ) (hc : c ^ 2 = 1)
    (J : OrthogonalComplexStructures.Space 6) :
    matrix (signScale c hc J) = c • matrix J := matrix_ofMatrix _ _ _

theorem continuous_signScale (c : ℝ) (hc : c ^ 2 = 1) :
    Continuous (signScale c hc) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (LinearMap.continuous_of_finiteDimensional
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 6)).toAlgEquiv.toLinearMap).comp
      ((continuous_const : Continuous (fun _ : OrthogonalComplexStructures.Space 6 ↦ c)).smul
        continuous_matrix)

end NoExoticSixSphere.RankSixComplexProjection
