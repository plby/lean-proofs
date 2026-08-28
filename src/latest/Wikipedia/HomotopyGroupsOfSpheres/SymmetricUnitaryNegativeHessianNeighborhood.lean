import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygonCriticalIndex
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryVertexInverseContinuity
import Wikipedia.HomotopyGroupsOfSpheres.RealHessianNeighborhood

/-! # Uniformly negative directions in the actual constrained vertex chart -/

noncomputable section

open scoped Matrix.Norms.Frobenius ContDiff Topology
open Set Filter

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace BalancedRealInvolutions

theorem exists_uniform_negative_hessian_neighborhood (n : ℕ) {m : ℕ}
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : VertexSpace.Space (Index n) m) (hv : v ∈ admissible specialIdentity (antipode n) m)
    (hcrit : fderiv ℝ (localEnergy specialIdentity (antipode n) τ v) 0 = 0)
    (habove : (4 * n : ℝ) * Real.pi ^ 2 < energy specialIdentity (antipode n) τ v) :
    ∃ L : (Fin n → ℝ) →L[ℝ] Model (Index n) m, Function.Injective L ∧
      ∃ c > 0, ∃ ε > 0, ∀ z ∈ Metric.ball (0 : Model (Index n) m) ε,
        (atVertices v).symm z ∈ admissible specialIdentity (antipode n) m ∧ ∀ w : Fin n → ℝ,
          realHessian (E := Model (Index n) m) (localEnergy specialIdentity (antipode n) τ v)
            z (L w) (L w) ≤ -c * ‖w‖ ^ 2 := by
  obtain ⟨R, hR, hneg⟩ :=
    exists_negative_hessianFamily_of_critical n τ hτ hzero hone v hv hcrit habove
  let L : (Fin n → ℝ) →L[ℝ] Model (Index n) m :=
    { toLinearMap := R
      cont := (finiteLinearMap_contDiff R).continuous }
  have hadm : (atVertices v).symm (0 : Model (Index n) m) ∈
      admissible specialIdentity (antipode n) m := by simpa only [atVertices_symm_zero] using hv
  have hmem : (atVertices v).symm ⁻¹' admissible specialIdentity (antipode n) m ∈
      𝓝 (0 : Model (Index n) m) :=
    (continuous_atVertices_symm v).continuousAt.eventually
      ((isOpen_admissible specialIdentity (antipode n) m).mem_nhds hadm)
  obtain ⟨c, hc, ε, hε, hball⟩ := exists_uniform_negative_hessian_ball
    (D := Fin n → ℝ) (E := Model (Index n) m) (localEnergy specialIdentity (antipode n) τ v) L
    (contDiffAt_localEnergy specialIdentity (antipode n) τ v hv) hneg _ hmem
  exact ⟨L, hR, c, hc, ε, hε, hball⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
