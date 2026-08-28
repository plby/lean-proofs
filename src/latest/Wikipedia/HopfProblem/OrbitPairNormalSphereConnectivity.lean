import Wikipedia.HopfProblem.OrbitPairMeridian
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRadial
import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere

/-!
# Simple connectedness of the literal normal sphere

An orthonormal basis identifies the original Euclidean normal space
with real four-space. Positive radial scaling then identifies its
radius-`r` sphere with the standard three-sphere. These are actual
homeomorphisms of the inherited sphere topologies.
-/

noncomputable section

open Set Topology Metric

namespace Wikipedia.HopfProblem.OrbitPair

theorem normal_dimension : Module.finrank ℝ Normal = 4 := by
  rw [(WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).toLinearEquiv.finrank_eq]
  simp

def normalEuclideanIsometry : Normal ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
  ((stdOrthonormalBasis ℝ Normal).reindex (finCongr normal_dimension)).repr

def normalUnitSphereHomeomorph :
    NormalSphere 1 ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  normalEuclideanIsometry.toHomeomorph.subtype (fun v => by
    simp only [mem_sphere, dist_zero_right]
    change ‖v‖ = 1 ↔ ‖normalEuclideanIsometry v‖ = 1
    rw [normalEuclideanIsometry.norm_map])

def normalSphereHomeomorph (r : ℝ) (hr : 0 < r) :
    NormalSphere r ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  (CuspCircleNormalTrivialization.Radial.sphereHomeomorph r hr).symm.trans
    normalUnitSphereHomeomorph

theorem normalSphere_simplyConnected (r : ℝ) (hr : 0 < r) :
    SimplyConnectedSpace (NormalSphere r) :=
  (normalSphereHomeomorph r hr).toHomotopyEquiv.simplyConnectedSpace

end Wikipedia.HopfProblem.OrbitPair
