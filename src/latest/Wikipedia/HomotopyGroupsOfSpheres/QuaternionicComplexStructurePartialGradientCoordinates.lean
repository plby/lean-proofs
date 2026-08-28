import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureNegativeHessianNeighborhood
import Wikipedia.NoExoticSixSphere.PartialGradientLocalData

/-!
# Partial-gradient coordinates at complex-structure critical polygons

The differential along the constrained negative family supplies the first
coordinate. The resulting local diffeomorphism is defined on admissible
coordinates in the actual dependent vertex model.
-/

open Set
open scoped ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open ComplexStructures ComplexStructureVertices

variable {n m : ℕ}

def localAdmissible (a b : ComplexStructures.Space n)
    (v : ComplexStructureVertices.Space n m) : Set (Model v) :=
  (atVertices v).symm ⁻¹' admissible a b m

theorem isOpen_localAdmissible (a b : ComplexStructures.Space n)
    (v : ComplexStructureVertices.Space n m) : IsOpen (localAdmissible a b v) :=
  (isOpen_admissible a b m).preimage (continuous_atVertices_symm v)

theorem zero_mem_localAdmissible (a b : ComplexStructures.Space n)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m) :
    (0 : Model v) ∈ localAdmissible a b v := by
  change (atVertices v).symm 0 ∈ admissible a b m
  simpa only [atVertices_symm_zero] using hv

theorem exists_partialGradient_coordinates (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m)
    (hcrit : fderiv ℝ (localEnergy a b τ v) 0 = 0)
    (hanti : (Cayley.relative a b).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (habove : ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 < energy a b τ v) :
    ∃ L : (Fin n → ℝ) →L[ℝ] Model v, Function.Injective L ∧
      Nonempty (PartialGradientCoordinates.LocalData (localEnergy a b τ v) L
        (localAdmissible a b v)) := by
  obtain ⟨L, hL, c, hc, ε, hε, hball⟩ :=
    exists_uniform_negative_hessian_neighborhood a b τ hτ hzero hone v hv hcrit hanti habove
  have h0ball : (0 : Model v) ∈ Metric.ball 0 ε := Metric.mem_ball_self hε
  have hsub : Metric.ball (0 : Model v) ε ⊆ localAdmissible a b v :=
    fun z hz ↦ (hball z hz).1
  have hdata := PartialGradientCoordinates.nonempty_localData_of_bound
    (D := Fin n → ℝ) (E := Model v) (localEnergy a b τ v) L
    (Metric.ball 0 ε) Metric.isOpen_ball h0ball
    ((contDiffOn_localEnergy a b τ v).mono hsub) hcrit c hc (fun z hz ↦ (hball z hz).2)
  exact ⟨L, hL, hdata.map (fun C ↦ C.mono hsub)⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
