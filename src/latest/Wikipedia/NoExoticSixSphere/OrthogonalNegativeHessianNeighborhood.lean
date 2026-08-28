import Wikipedia.NoExoticSixSphere.OrthogonalPolygonHessian
import Wikipedia.NoExoticSixSphere.NegativeFormNeighborhood

/-!
# A uniformly negative Hessian subspace near a nonminimal critical polygon

The actual coordinate Hessian is continuous. Its negative finite-dimensional
subspace therefore remains uniformly negative on a genuine coordinate ball
lying inside the admissible polygon domain.
-/

open Set Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization OrthogonalVertexSpace

variable {n m : ℕ}

theorem continuousAt_localEnergy_hessian (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) (hv : v ∈ admissible a b m) :
    ContinuousAt (fderiv ℝ (fderiv ℝ (localEnergy a b τ v))) 0 := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ (localEnergy a b τ v)) 0 :=
    (contDiffAt_localEnergy a b τ v hv).fderiv_right (WithTop.coe_le_coe.mpr le_top)
  exact hd.continuousAt_fderiv one_ne_zero

theorem exists_uniform_negative_hessian_neighborhood (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ shortDomain a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (habove : (n : ℝ) * Real.pi ^ 2 < energy a b τ v) :
    ∃ (d : ℕ) (L : (Fin d → ℝ) →L[ℝ] Model n m), d + 2 = n ∧ Function.Injective L ∧
      ∃ c > 0, ∃ ε > 0, ∀ z ∈ Metric.ball (0 : Model n m) ε,
        (atVertices v).symm z ∈ admissible a b m ∧ ∀ w : Fin d → ℝ,
          fderiv ℝ (fderiv ℝ (localEnergy a b τ v)) z (L w) (L w) ≤ -c * ‖w‖ ^ 2 := by
  obtain ⟨d, R, hd, hR, hneg⟩ :=
    exists_negative_hessianFamily_of_critical a b τ hτ hzero hone v hv hcrit hanti habove
  let L : (Fin d → ℝ) →L[ℝ] Model n m := R.toContinuousLinearMap
  obtain ⟨c, hc, hforms⟩ := NegativeFormNeighborhood.exists_uniform_bound
    (D := Fin d → ℝ) (E := Model n m) (localHessian a b τ v) L hneg
  have hnear : ∀ᶠ z in 𝓝 (0 : Model n m), ∀ w : Fin d → ℝ,
      fderiv ℝ (fderiv ℝ (localEnergy a b τ v)) z (L w) (L w) ≤ -c * ‖w‖ ^ 2 :=
    (continuousAt_localEnergy_hessian a b τ v hv.1).eventually hforms
  have hadm : (atVertices v).symm (0 : Model n m) ∈ admissible a b m := by
    simpa only [atVertices_symm_zero] using hv.1
  have hmem : ∀ᶠ z in 𝓝 (0 : Model n m), (atVertices v).symm z ∈ admissible a b m :=
    (contMDiff_atVertices_symm v).continuous.continuousAt.eventually
      ((isOpen_admissible a b m).mem_nhds hadm)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hmem.and hnear)
  exact ⟨d, L, hd, hR, c, hc, ε, hε, fun z hz ↦ hball hz⟩

end NoExoticSixSphere.OrthogonalPolygon
