import Wikipedia.NoExoticSixSphere.OrthogonalComplexStructures
import Wikipedia.NoExoticSixSphere.SkewConjugation

/-!
# Continuous conjugation of orthogonal complex structures

The actual operator conjugate stays skew-adjoint and squares to minus the
identity. This lets orthogonal column transport act on complex structures
without losing their defining equations.
-/

namespace NoExoticSixSphere.OrthogonalComplexStructures

open GLOrthonormalization OrthogonalPaths CayleyTransform

variable {n : ℕ}

theorem conjugate_square (a : OrthogonalOperators n) (J : Space n) :
    (SkewConjugation.conjugate a J.1 : Vector n →L[ℝ] Vector n).comp
      (SkewConjugation.conjugate a J.1 : Vector n →L[ℝ] Vector n) =
        -(1 : Vector n →L[ℝ] Vector n) := by
  apply ContinuousLinearMap.ext
  intro x
  change a.1.1 (J.1.1 ((inverse a).1.1 (a.1.1 (J.1.1 ((inverse a).1.1 x))))) = -x
  rw [inverse_apply_self, square_apply, map_neg, self_apply_inverse]

noncomputable def conjugate (a : OrthogonalOperators n) (J : Space n) : Space n :=
  ⟨SkewConjugation.conjugate a J.1, conjugate_square a J⟩

theorem conjugate_apply (a : OrthogonalOperators n) (J : Space n) (x : Vector n) :
    (conjugate a J).1.1 x = a.1.1 (J.1.1 ((inverse a).1.1 x)) := rfl

theorem conjugate_identity (J : Space n) : conjugate (identity n) J = J := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  rw [conjugate_apply, inverse_identity]
  rfl

theorem conjugate_column (a : OrthogonalOperators n) (J : Space n) (v : Vector n)
    (ha : a.1.1 v = v) :
    (conjugate a J).1.1 v = a.1.1 (J.1.1 v) := by
  have hi : (inverse a).1.1 v = v := by
    exact (congrArg (inverse a).1.1 ha.symm).trans (inverse_apply_self a v)
  rw [conjugate_apply, hi]

variable {X : Type*} [TopologicalSpace X]

theorem continuous_conjugate (a : X → OrthogonalOperators n) (J : X → Space n)
    (ha : Continuous a) (hJ : Continuous J) :
    Continuous (fun x ↦ conjugate (a x) (J x)) := by
  have hA := continuous_subtype_val.comp (continuous_subtype_val.comp ha)
  have hK := continuous_subtype_val.comp (continuous_subtype_val.comp hJ)
  have hI := continuous_subtype_val.comp
    (continuous_subtype_val.comp (continuous_inverse a ha))
  exact ((hA.clm_comp (hK.clm_comp hI)).subtype_mk _).subtype_mk _

end NoExoticSixSphere.OrthogonalComplexStructures
