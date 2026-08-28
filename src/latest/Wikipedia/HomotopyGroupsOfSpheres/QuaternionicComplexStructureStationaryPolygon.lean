import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructurePolygonDifferential
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructurePolygonRealization
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicStationaryPolygon

/-!
# Critical complex-structure polygons are single anticommuting exponential curves

Restricted criticality forces the actual velocity jumps to vanish. The
symplectic polygon classification then applies, with the first velocity
proved to lie in the anticommuting model at the starting complex structure.
-/

noncomputable section

open Set
open scoped Manifold

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open ComplexStructures ComplexStructureVertices

variable {n m : ℕ}

def firstDirection (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m) : AntiSkewSpace a :=
  (1 / (τ (0 : Fin (m + 1)).succ - τ 0)) •
    ShortLog.direction a (vertices a b v (0 : Fin (m + 1)).succ) (hv 0)

theorem firstDirection_toSkew (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m) :
    antiSkewToSkew a (firstDirection a b τ v hv) =
      Polygon.edgeVelocity (toSymplectic a) (toSymplectic b) τ (forget v) 0 := by
  rw [Polygon.edgeVelocity, generator_forget]
  rfl

theorem critical_forget (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m)
    (hcrit : fderiv ℝ (localEnergy a b τ v) 0 = 0) :
    mfderiv 𝓘(ℝ, VertexSpace.Model n m) 𝓘(ℝ, ℝ)
      (Polygon.energy (toSymplectic a) (toSymplectic b) τ) (forget v) = 0 :=
  (Polygon.mfderiv_energy_eq_zero_iff (toSymplectic a) (toSymplectic b) τ
    (forget v) (admissible_forget a b hv)).mpr
      ((fderiv_localEnergy_eq_zero_iff a b τ v hv).mp hcrit)

theorem critical_vertices_exponential (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (v : ComplexStructureVertices.Space n m)
    (hv : v ∈ admissible a b m) (hcrit : fderiv ℝ (localEnergy a b τ v) 0 = 0)
    (j : Fin (m + 2)) :
    vertices a b v j = exponentialCurve a (firstDirection a b τ v hv) (τ j - τ 0) := by
  apply toSymplectic_injective
  rw [vertices_forget, exponentialCurve_toSymplectic, firstDirection_toSkew]
  exact Polygon.vertices_eq_exponential_of_stationary (toSymplectic a) (toSymplectic b)
    τ hτ (forget v) (admissible_forget a b hv)
    (Polygon.isStationary_of_mfderiv_eq_zero (toSymplectic a) (toSymplectic b) τ
      (forget v) (admissible_forget a b hv) (critical_forget a b τ v hv hcrit)) j

theorem critical_path_exponential (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (v : ComplexStructureVertices.Space n m)
    (hv : v ∈ admissible a b m) (hcrit : fderiv ℝ (localEnergy a b τ v) 0 = 0)
    {t : ℝ} (ht : t ∈ Icc (τ 0) (τ (Fin.last (m + 1)))) :
    path a b τ hτ v hv t = exponentialCurve a (firstDirection a b τ v hv) (t - τ 0) := by
  apply toSymplectic_injective
  rw [path_toSymplectic, exponentialCurve_toSymplectic, firstDirection_toSkew]
  exact Polygon.path_eq_exponential_of_stationary (toSymplectic a) (toSymplectic b)
    τ hτ (forget v) (admissible_forget a b hv)
    (Polygon.isStationary_of_mfderiv_eq_zero (toSymplectic a) (toSymplectic b) τ
      (forget v) (admissible_forget a b hv) (critical_forget a b τ v hv hcrit)) ht

theorem critical_is_exponential (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (v : ComplexStructureVertices.Space n m)
    (hv : v ∈ admissible a b m) (hcrit : fderiv ℝ (localEnergy a b τ v) 0 = 0) :
    ∃ K : AntiSkewSpace a,
      exponentialCurve a K (τ (Fin.last (m + 1)) - τ 0) = b ∧
      ∀ t ∈ Icc (τ 0) (τ (Fin.last (m + 1))),
        path a b τ hτ v hv t = exponentialCurve a K (t - τ 0) := by
  refine ⟨firstDirection a b τ v hv, ?_, fun _ ht ↦
    critical_path_exponential a b τ hτ v hv hcrit ht⟩
  have he := critical_vertices_exponential a b τ hτ v hv hcrit (Fin.last (m + 1))
  rw [vertices_last] at he
  exact he.symm

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
