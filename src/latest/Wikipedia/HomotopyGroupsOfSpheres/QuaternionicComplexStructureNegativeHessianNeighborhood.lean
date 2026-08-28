import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructurePolygonHessian
import Wikipedia.HomotopyGroupsOfSpheres.RealHessianNeighborhood

/-!
# Uniformly negative Hessian directions in complex-structure coordinates

The constrained negative family persists on a neighborhood in the actual
local model, with a uniform quadratic bound and admissible inverse images.
-/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open NoExoticSixSphere.GLOrthonormalization ComplexStructures ComplexStructureVertices

variable {n m : ℕ}

theorem exists_uniform_negative_hessian_neighborhood (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m)
    (hcrit : fderiv ℝ (localEnergy a b τ v) 0 = 0)
    (hanti : (Cayley.relative a b).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (habove : ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 < energy a b τ v) :
    ∃ L : (Fin n → ℝ) →L[ℝ] Model v, Function.Injective L ∧
      ∃ c > 0, ∃ ε > 0, ∀ z ∈ Metric.ball (0 : Model v) ε,
        (atVertices v).symm z ∈ admissible a b m ∧ ∀ w : Fin n → ℝ,
          realHessian (E := Model v) (localEnergy a b τ v) z (L w) (L w) ≤ -c * ‖w‖ ^ 2 := by
  obtain ⟨R, hR, hneg⟩ :=
    exists_negative_hessianFamily_of_critical a b τ hτ hzero hone v hv hcrit hanti habove
  let L : (Fin n → ℝ) →L[ℝ] Model v :=
    { toLinearMap := R
      cont := (finiteLinearMap_contDiff (E := Fin n → ℝ) (F := Model v) R).continuous }
  have hadm : (atVertices v).symm (0 : Model v) ∈ admissible a b m := by
    simpa only [atVertices_symm_zero] using hv
  have hmem : (atVertices v).symm ⁻¹' admissible a b m ∈ 𝓝 (0 : Model v) :=
    (continuous_atVertices_symm v).continuousAt.eventually
      ((isOpen_admissible a b m).mem_nhds hadm)
  obtain ⟨c, hc, ε, hε, hball⟩ := exists_uniform_negative_hessian_ball
    (D := Fin n → ℝ) (E := Model v) (localEnergy a b τ v) L
    (contDiffAt_localEnergy a b τ v hv) hneg _ hmem
  exact ⟨L, hR, c, hc, ε, hε, hball⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
