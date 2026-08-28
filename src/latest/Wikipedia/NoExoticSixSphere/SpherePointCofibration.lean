import Wikipedia.NoExoticSixSphere.MetricPointCofibration
import Wikipedia.NoExoticSixSphere.SpherePathCover
import Wikipedia.NoExoticSixSphere.Equator

/-!+# The inclusion of any point in the actual standard sphere is a cofibration

The punctured-sphere contraction is extended by a supported time cutoff.
Its domain contains the closed unit ball about the chosen point because
the antipodal point is at distance two.
-/

noncomputable section

open CategoryTheory Set Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.SpherePointCofibration

variable {n : ℕ} (b : Sphere n)

theorem dist_antipode : dist (antipode b) b = 2 := by
  change ‖-(b : EuclideanSpace ℝ (Fin (n + 1))) - b.val‖ = 2
  have hv : -(b : EuclideanSpace ℝ (Fin (n + 1))) - b.val =
      -((2 : ℝ) • b.val) := by
    rw [two_smul]
    abel
  rw [hv, norm_neg, norm_smul, ClosedHemisphere.unit_norm]
  norm_num

theorem base_mem : b ∈ ({antipode b}ᶜ : Set (Sphere n)) := by
  intro h
  have he : b = antipode b := h
  have hd := dist_antipode b
  rw [← he, dist_self] at hd
  norm_num at hd

theorem closedBall_subset : Metric.closedBall b 1 ⊆ ({antipode b}ᶜ : Set (Sphere n)) := by
  intro x hx he
  have he' : x = antipode b := he
  have hd : dist x b ≤ 1 := Metric.mem_closedBall.mp hx
  rw [he', dist_antipode] at hd
  norm_num at hd

def localContraction : C(I × ({antipode b}ᶜ : Set (Sphere n)), Sphere n) :=
  (⟨Subtype.val, continuous_subtype_val⟩ : C(({antipode b}ᶜ : Set (Sphere n)), Sphere n)).comp
    (SpherePathCover.contraction (antipode b) ⟨b, base_mem b⟩).toContinuousMap

theorem localContraction_zero (x : ({antipode b}ᶜ : Set (Sphere n))) :
    localContraction b (0, x) = x.val :=
  congrArg Subtype.val
    ((SpherePathCover.contraction (antipode b) ⟨b, base_mem b⟩).map_zero_left x)

theorem localContraction_fixed (t : I) (x : ({antipode b}ᶜ : Set (Sphere n)))
    (hx : x.val = b) : localContraction b (t, x) = b := by
  have hxe : x = ⟨b, base_mem b⟩ := Subtype.ext hx
  have ht := (SpherePathCover.contraction (antipode b) ⟨b, base_mem b⟩).prop' t x
    (show x ∈ ({⟨b, base_mem b⟩} : Set ({antipode b}ᶜ : Set (Sphere n))) from hxe)
  exact (congrArg Subtype.val ht).trans hx

theorem localContraction_one (x : ({antipode b}ᶜ : Set (Sphere n))) :
    localContraction b (1, x) = b :=
  congrArg Subtype.val
    ((SpherePathCover.contraction (antipode b) ⟨b, base_mem b⟩).map_one_left x)

def data : NeighborhoodDeformation.Data (MetricPointCofibration.inclusion b) :=
  MetricPointCofibration.data b isClosed_singleton.isOpen_compl (closedBall_subset b)
    (localContraction b) (localContraction_zero b) (localContraction_fixed b)
    (localContraction_one b)

theorem hasHomotopyExtension :
    HomotopyExtension.HasHomotopyExtension (MetricPointCofibration.inclusion b) :=
  NeighborhoodDeformation.hasHomotopyExtension (data b) IsEmbedding.subtypeVal

end NoExoticSixSphere.SpherePointCofibration
