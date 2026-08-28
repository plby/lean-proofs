import Wikipedia.HopfProblem.OrbitPairNormalSphereConnectivity
import Wikipedia.HopfProblem.SphereHomologySimplyConnectedPiTwo

/-!
# The literal meridian sphere and its integral homology marking

Orthonormal coordinates and positive radial scaling identify the actual
transverse radius-`r` sphere with the standard two-sphere. Its homology
marking is induced by this homeomorphism followed by the proved sphere
homology calculation.
-/

noncomputable section

open Set Topology Metric

namespace Wikipedia.HopfProblem.OrbitPair

open SingularMayerVietoris PeriodTorusHigherHomology

theorem transverse_dimension : Module.finrank ℝ Transverse = 3 := by
  rw [(WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℝ).toLinearEquiv.finrank_eq]
  simp

def transverseEuclideanIsometry : Transverse ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ((stdOrthonormalBasis ℝ Transverse).reindex (finCongr transverse_dimension)).repr

def meridianUnitSphereHomeomorph : MeridianSphere 1 ≃ₜ SphereHomology.UnitSphere 2 :=
  transverseEuclideanIsometry.toHomeomorph.subtype (fun y => by
    simp only [mem_sphere, dist_zero_right]
    change ‖y‖ = 1 ↔ ‖transverseEuclideanIsometry y‖ = 1
    rw [transverseEuclideanIsometry.norm_map])

def meridianSphereHomeomorph (r : ℝ) (hr : 0 < r) :
    MeridianSphere r ≃ₜ SphereHomology.UnitSphere 2 :=
  (CuspCircleNormalTrivialization.Radial.sphereHomeomorph r hr).symm.trans
    meridianUnitSphereHomeomorph

theorem meridianSphere_simplyConnected (r : ℝ) (hr : 0 < r) :
    SimplyConnectedSpace (MeridianSphere r) :=
  (meridianSphereHomeomorph r hr).toHomotopyEquiv.simplyConnectedSpace

def meridianSphereHomologyTwoEquiv (r : ℝ) (hr : 0 < r) :
    SingularHomology (MeridianSphere r) 2 ≃ₗ[ℤ] ℤ :=
  (homeomorphHomologyEquiv (meridianSphereHomeomorph r hr) 2).trans
    (SphereHomology.unitSphereHomologyTopEquiv 1)

def meridianSphereTopClass (r : ℝ) (hr : 0 < r) : SingularHomology (MeridianSphere r) 2 :=
  (meridianSphereHomologyTwoEquiv r hr).symm 1

@[simp] theorem meridianSphereHomologyTwoEquiv_topClass (r : ℝ) (hr : 0 < r) :
    meridianSphereHomologyTwoEquiv r hr (meridianSphereTopClass r hr) = 1 :=
  (meridianSphereHomologyTwoEquiv r hr).apply_symm_apply 1

end Wikipedia.HopfProblem.OrbitPair
