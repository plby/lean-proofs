import Wikipedia.HopfProblem.OrbitPairSphereNormalVertexTangent

/-!
# Centered coordinates in the original sphere vertex atlas

These are translations of the existing product sphere chart, not a new
smooth structure. The inverse is smooth on its actual open chart domain.
No assertion of smoothness or invertibility outside that domain is needed.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.SphereVertexSpace

open NoExoticSixSphere

variable {n m : ℕ}

theorem contMDiffAt_inverse_eval_of_mem_target (v : Space n m) (j : Fin m)
    (K : Model n m) (hK : K ∈ (atVertices v).target) :
    ContMDiffAt 𝓘(ℝ, Model n m) (𝓡 n) ∞
      (fun L : Model n m => (atVertices v).symm L j) K := by
  have hj : K j ∈ (sphereChart (v j)).target := hK j (mem_univ j)
  have hi : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (sphereChart (v j)).symm (K j) :=
    (sphereChart (v j)).contMDiffOn_invFun.contMDiffAt
      ((sphereChart (v j)).open_target.mem_nhds hj)
  have he : ContMDiff 𝓘(ℝ, Model n m) (𝓡 n) ∞ (fun L : Model n m => L j) :=
    (contDiff_apply ℝ (EuclideanSpace ℝ (Fin n)) j).contMDiff
  exact ContMDiffAt.comp (g := (sphereChart (v j)).symm)
    (f := fun L : Model n m => L j) K hi he.contMDiffAt

theorem contMDiffAt_atVertices_symm (v : Space n m)
    (K : Model n m) (hK : K ∈ (atVertices v).target) :
    ContMDiffAt 𝓘(ℝ, Model n m) 𝓘(ℝ, Model n m) ∞ (atVertices v).symm K :=
  contMDiffAt_of_coordinate (fun j => contMDiffAt_inverse_eval_of_mem_target v j K hK)

def coordinates (v w : Space n m) : Model n m := atVertices v w - atVertices v v

def fromCoordinates (v : Space n m) (K : Model n m) : Space n m :=
  (atVertices v).symm (K + atVertices v v)

def coordinateDomain (v : Space n m) : Set (Model n m) :=
  {K | K + atVertices v v ∈ (atVertices v).target}

theorem isOpen_coordinateDomain (v : Space n m) : IsOpen (coordinateDomain v) :=
  (atVertices v).open_target.preimage (continuous_id.add continuous_const)

theorem zero_mem_coordinateDomain (v : Space n m) : (0 : Model n m) ∈ coordinateDomain v := by
  change 0 + atVertices v v ∈ (atVertices v).target
  rw [zero_add]
  exact (atVertices v).map_source (mem_atVertices_source v)

theorem coordinates_self (v : Space n m) : coordinates v v = 0 := sub_self _

theorem fromCoordinates_zero (v : Space n m) : fromCoordinates v 0 = v := by
  rw [fromCoordinates, zero_add]
  exact (atVertices v).left_inv (mem_atVertices_source v)

theorem fromCoordinates_coordinates (v w : Space n m) (hw : w ∈ (atVertices v).source) :
    fromCoordinates v (coordinates v w) = w := by
  rw [fromCoordinates, coordinates, sub_add_cancel]
  exact (atVertices v).left_inv hw

theorem coordinates_fromCoordinates (v : Space n m)
    (K : Model n m) (hK : K ∈ coordinateDomain v) :
    coordinates v (fromCoordinates v K) = K := by
  have htarget : K + atVertices v v ∈ (atVertices v).target := hK
  have hinv : atVertices v ((atVertices v).symm (K + atVertices v v)) = K + atVertices v v :=
    (atVertices v).right_inv htarget
  rw [coordinates, fromCoordinates, hinv, add_sub_cancel_right]

theorem contMDiffOn_fromCoordinates (v : Space n m) :
    ContMDiffOn 𝓘(ℝ, Model n m) 𝓘(ℝ, Model n m) ∞
      (fromCoordinates v) (coordinateDomain v) := by
  intro K hK
  have hi := contMDiffAt_atVertices_symm v (K + atVertices v v) hK
  have hs : ContMDiff 𝓘(ℝ, Model n m) 𝓘(ℝ, Model n m) ∞
      (fun L : Model n m => L + atVertices v v) := contMDiff_id.add contMDiff_const
  exact (ContMDiffAt.comp (g := (atVertices v).symm)
    (f := fun L : Model n m => L + atVertices v v) K hi hs.contMDiffAt).contMDiffWithinAt

theorem hasDerivAt_normalVariation_centeredCoordinates (v : Space n m) (W : Field v) :
    HasDerivAt (fun s => coordinates v (normalVariation v W s)) (normalChartTangent v W) 0 :=
  (hasDerivAt_normalVariation_coordinates v W).sub_const (atVertices v v)

theorem contDiffAt_normalVariation_centeredCoordinates (v : Space n m) (W : Field v) :
    ContDiffAt ℝ ∞ (fun s => coordinates v (normalVariation v W s)) 0 := by
  have hs : ContDiffAt ℝ ∞ (fun s : ℝ => s • W) 0 := contDiffAt_id.smul contDiffAt_const
  have hc : ContDiffAt ℝ ∞ (normalCoordinates v) ((0 : ℝ) • W) := by
    simpa only [zero_smul] using contDiffAt_normalCoordinates v
  exact (ContDiffAt.comp (g := normalCoordinates v) (f := fun s : ℝ => s • W)
    0 hc hs).sub contDiffAt_const

end Wikipedia.HopfProblem.OrbitPair.SphereVertexSpace
