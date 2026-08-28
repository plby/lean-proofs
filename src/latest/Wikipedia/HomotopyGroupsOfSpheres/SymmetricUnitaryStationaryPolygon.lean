import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygonDifferential
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygonRealization
import Wikipedia.NoExoticSixSphere.OrthogonalStationaryPolygon

/-!
# Critical constrained polygons are single exponential paths

Restricted criticality forces every velocity jump to vanish. The orthogonal
classification then applies, with the first velocity proved to be reversible
and trace zero at the original starting matrix.
-/

noncomputable section

open scoped Matrix.Norms.Frobenius Manifold
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

open ComplexMatrixRealRepresentation

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem reversibleStep_orthogonal (B : SpecialSpace N) (K : ComplexSkewMatrices.Space N)
    (htrace : K.val.trace = 0) (hrev : K.val.transpose * B.val.val.val = B.val.val.val * K.val)
    (t : ℝ) : specialOrthogonal (reversibleStep B K htrace hrev t) =
      specialOrthogonal B *
        NoExoticSixSphere.OrthogonalExponential.exp
          (t • ComplexSkewMatrices.toOrthogonalSkew K) := by
  change orthogonal (B.val.val * ComplexSkewMatrices.exponential (t • K)) = _
  rw [map_mul, ComplexSkewMatrices.orthogonal_exponential, map_smul]
  rfl

namespace Polygon

open VertexSpace

variable {m : ℕ}

def firstDirection (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m) : ReversibleDirection a :=
  ⟨edgeVelocity a b τ v 0, (reversibleDirections a).smul_mem _
    (ShortLog.generator_mem_start (hv 0))⟩

theorem firstDirection_toOrthogonal (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m) :
    ComplexSkewMatrices.toOrthogonalSkew (firstDirection a b τ v hv).val =
      NoExoticSixSphere.OrthogonalPolygon.edgeVelocity (specialOrthogonal a) (specialOrthogonal b)
        τ (forget v) 0 := (edgeVelocity_forget a b τ hv 0).symm

theorem critical_vertices_exponential (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m)
    (hcrit : fderiv ℝ (localEnergy a b τ v) 0 = 0) (j : Fin (m + 2)) :
    vertices a b v j = reversibleStep a (firstDirection a b τ v hv).val
      (firstDirection a b τ v hv).property.1 (firstDirection a b τ v hv).property.2
      (τ j - τ 0) := by
  apply Subtype.ext
  apply Subtype.ext
  apply orthogonal_injective
  change specialOrthogonal (vertices a b v j) = specialOrthogonal (reversibleStep _ _ _ _ _)
  rw [vertices_forget, reversibleStep_orthogonal, firstDirection_toOrthogonal]
  exact NoExoticSixSphere.OrthogonalPolygon.vertices_eq_exponential_of_stationary
    (specialOrthogonal a) (specialOrthogonal b) τ hτ (forget v) (admissible_forget a b hv)
    (NoExoticSixSphere.OrthogonalPolygon.isStationary_of_mfderiv_eq_zero
      (specialOrthogonal a) (specialOrthogonal b) τ (forget v) (admissible_forget a b hv)
      (critical_forget a b τ v hv hcrit)) j

theorem critical_path_exponential (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m)
    (hcrit : fderiv ℝ (localEnergy a b τ v) 0 = 0)
    {t : ℝ} (ht : t ∈ Icc (τ 0) (τ (Fin.last (m + 1)))) :
    path a b τ hτ v hv t = reversibleStep a (firstDirection a b τ v hv).val
      (firstDirection a b τ v hv).property.1 (firstDirection a b τ v hv).property.2
      (t - τ 0) := by
  apply Subtype.ext
  apply Subtype.ext
  apply orthogonal_injective
  change specialOrthogonal (path a b τ hτ v hv t) =
    specialOrthogonal (reversibleStep _ _ _ _ _)
  rw [path_orthogonal, reversibleStep_orthogonal, firstDirection_toOrthogonal]
  exact NoExoticSixSphere.OrthogonalPolygon.path_eq_exponential_of_stationary
    (specialOrthogonal a) (specialOrthogonal b) τ hτ (forget v) (admissible_forget a b hv)
    (NoExoticSixSphere.OrthogonalPolygon.isStationary_of_mfderiv_eq_zero
      (specialOrthogonal a) (specialOrthogonal b) τ (forget v) (admissible_forget a b hv)
      (critical_forget a b τ v hv hcrit)) ht

theorem critical_is_exponential (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m)
    (hcrit : fderiv ℝ (localEnergy a b τ v) 0 = 0) :
    ∃ K : ReversibleDirection a,
      reversibleStep a K.val K.property.1 K.property.2 (τ (Fin.last (m + 1)) - τ 0) = b ∧
      ∀ t ∈ Icc (τ 0) (τ (Fin.last (m + 1))),
        path a b τ hτ v hv t = reversibleStep a K.val K.property.1 K.property.2 (t - τ 0) := by
  refine ⟨firstDirection a b τ v hv, ?_, fun _ ht ↦
    critical_path_exponential a b τ hτ v hv hcrit ht⟩
  have he := critical_vertices_exponential a b τ hτ v hv hcrit (Fin.last (m + 1))
  rw [vertices_last] at he
  exact he.symm

end Polygon
end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
