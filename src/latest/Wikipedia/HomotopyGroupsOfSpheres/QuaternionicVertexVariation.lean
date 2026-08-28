import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygon
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicVertexFamilies
import Wikipedia.NoExoticSixSphere.OrthogonalVertexVariation

/-! # Actual smooth exponential variations of symplectic polygon vertices -/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open VertexSpace Exponential

variable {n m : ℕ}

def vertexVariation (v : Space n m) (Z : Model n m) (s : ℝ) : Space n m :=
  fun i => v i * exp (s • Z i)

theorem contMDiff_vertexVariation (v : Space n m) (Z : Model n m) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model n m) ∞ (vertexVariation v Z) := by
  apply contMDiff_iff_coordinatewise.mpr
  intro i
  exact contMDiff_const.mul (contMDiff_exp_smul (Z i))

theorem forget_vertexVariation (v : Space n m) (Z : Model n m) (s : ℝ) :
    forget (vertexVariation v Z s) = NoExoticSixSphere.OrthogonalPolygon.vertexVariation
      (forget v) (fun i => toOrthogonalSkew n (Z i)) s := by
  funext i
  change (v i).val * NoExoticSixSphere.OrthogonalExponential.exp
    (toOrthogonalSkew n (s • Z i)) =
      (v i).val * NoExoticSixSphere.OrthogonalExponential.exp (s • toOrthogonalSkew n (Z i))
  rw [map_smul]

theorem vertexVariation_zero (v : Space n m) (Z : Model n m) : vertexVariation v Z 0 = v := by
  funext i
  simp only [vertexVariation, zero_smul, exp_zero, mul_one]

theorem vertexVariation_zero_field (v : Space n m) (s : ℝ) : vertexVariation v 0 s = v := by
  funext i
  simp only [vertexVariation, Pi.zero_apply, smul_zero, exp_zero, mul_one]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
