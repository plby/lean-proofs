import Wikipedia.SmoothSixDPoincare.ReferenceSphereChart
import Wikipedia.SmoothSixDPoincare.StereographicInversion

/-! # Exact inversion formula for the constructed native reference chart -/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.NativeParametrization

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]

theorem centered_sphere_apply (v : sphere (0 : V) 1) (z : EuclideanSpace ℝ (Fin n)) :
    centered (D := EuclideanSpace ℝ (Fin n)) v z = (stereographic' n (-v)).symm z := by
  have hz : stereographic' n (-v) v = 0 := by
    change (OrthonormalBasis.fromOrthogonalSpanSingleton n
      (ne_zero_of_mem_unit_sphere (-v))).repr
        (stereographic (norm_eq_of_mem_sphere (-v)) v) = 0
    rw [stereographic_neg_apply, map_zero]
  change (stereographic' n (-v)).symm (z + stereographic' n (-v) v) = _
  rw [hz, add_zero]

end Wikipedia.SmoothSixDPoincare.NativeParametrization

namespace Wikipedia.SmoothSixDPoincare.SphereCoordinates

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] (n : ℕ) (hdim : Module.finrank ℝ F = n)

theorem referenceChart_apply (w : F) :
    letI : Fact (Module.finrank ℝ (Hemisphere.Ambient (n + 1)) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    referenceChart F n hdim w =
      (stereographic' n (-referencePole n)).symm (referenceIsometry F n hdim w) := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  exact NativeParametrization.centered_sphere_apply (referencePole n) (referenceIsometry F n hdim w)

theorem referenceChart_inversion {w : F} (hw : w ≠ 0) :
    referenceChart F n hdim ((‖w‖ ^ 2)⁻¹ • w) =
      -referenceChart F n hdim ((-4 : ℝ) • w) := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  rw [referenceChart_apply, referenceChart_apply, map_smul, map_smul]
  rw [← (referenceIsometry F n hdim).norm_map w]
  apply stereographic_symm_inversion
  exact fun h => hw ((referenceIsometry F n hdim).injective
    (h.trans (referenceIsometry F n hdim).map_zero.symm))

end Wikipedia.SmoothSixDPoincare.SphereCoordinates
