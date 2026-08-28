import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonHessian
import Wikipedia.HomotopyGroupsOfSpheres.RealHessianNeighborhood

/-! # Uniformly negative symplectic Hessian directions on actual coordinate neighborhoods -/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open NoExoticSixSphere.GLOrthonormalization VertexSpace

variable {n m : ℕ}

theorem exists_uniform_negative_hessian_neighborhood (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ shortDomain a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : (a⁻¹ * b).val.val.val = -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (habove : ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 < energy a b τ v) :
    ∃ L : (Fin n → ℝ) →L[ℝ] Model n m, Function.Injective L ∧
      ∃ c > 0, ∃ ε > 0, ∀ z ∈ Metric.ball (0 : Model n m) ε,
        (atVertices v).symm z ∈ admissible a b m ∧ ∀ w : Fin n → ℝ,
          realHessian (localEnergy a b τ v) z (L w) (L w) ≤ -c * ‖w‖ ^ 2 := by
  obtain ⟨R, hR, hneg⟩ :=
    exists_negative_hessianFamily_of_critical a b τ hτ hzero hone v hv hcrit hanti habove
  let L : (Fin n → ℝ) →L[ℝ] Model n m :=
    { toLinearMap := R
      cont := (finiteLinearMap_contDiff (E := Fin n → ℝ) (F := Model n m) R).continuous }
  have hadm : (atVertices v).symm (0 : Model n m) ∈ admissible a b m := by
    simpa only [atVertices_symm_zero] using hv.1
  have hmem : (atVertices v).symm ⁻¹' admissible a b m ∈ 𝓝 (0 : Model n m) :=
    (contMDiff_atVertices_symm v).continuous.continuousAt.eventually
      ((isOpen_admissible a b m).mem_nhds hadm)
  obtain ⟨c, hc, ε, hε, hball⟩ := exists_uniform_negative_hessian_ball
    (D := Fin n → ℝ) (E := Model n m) (localEnergy a b τ v) L
    (contDiffAt_localEnergy a b τ v hv.1) hneg _ hmem
  exact ⟨L, hR, c, hc, ε, hε, hball⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
