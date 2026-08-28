import Wikipedia.NoExoticSixSphere.JamesSphereConeStageFibers
import Wikipedia.NoExoticSixSphere.QuotientRelativeCompression

/-!
# Deforming each auxiliary James cone stage onto its predecessor

The cone contraction first compresses the quotient presentation through
maps of pairs. The exact inverse image is a product-boundary cofibration,
and every nontrivial quotient fiber lies over the preceding stage. The
proved relative-compression descent therefore gives an actual strong
deformation retraction onto that embedded preceding stage.
-/

noncomputable section

open CategoryTheory Set Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.JamesSphere.ConeStage

def wordStageData (n k : ℕ) : NeighborhoodDeformation.Data (StageAttachment.inclusion n k) :=
  Classical.choice (NeighborhoodDeformation.exists_data (StageAttachment.inclusion n k)
    (StageAttachment.hasHomotopyExtension n k) (StageAttachment.isClosedEmbedding n k))

def preimageData (n k : ℕ) : NeighborhoodDeformation.Data
    (SubspaceCofibration.inclusion (quotientMap n (k + 1) ⁻¹' preceding n k)) := by
  rw [preimage_preceding]
  exact NeighborhoodProduct.data (ReducedCone.pointData n) (wordStageData n k)

def compressionEndpoint (n k : ℕ) :
    C(ReducedCone.Space n × James.stage (spherePole n) (k + 1), Space n (k + 1)) :=
  (quotientMap n (k + 1)).comp
    ⟨fun p ↦ (ReducedCone.base n, p.2), continuous_const.prodMk continuous_snd⟩

def compression (n k : ℕ) : (quotientMap n (k + 1)).Homotopy (compressionEndpoint n k) where
  toFun p := quotientMap n (k + 1) (ReducedCone.contract n (p.1, p.2.1), p.2.2)
  continuous_toFun := (quotientMap n (k + 1)).continuous.comp
    (((ReducedCone.contract n).continuous.comp
      (continuous_fst.prodMk continuous_snd.fst)).prodMk continuous_snd.snd)
  map_zero_left p := by
    change quotientMap n (k + 1) (ReducedCone.contract n (0, p.1), p.2) = _
    rw [ReducedCone.contract_zero]
  map_one_left p := by
    change quotientMap n (k + 1) (ReducedCone.contract n (1, p.1), p.2) = _
    rw [ReducedCone.contract_one]
    rfl

theorem compression_subspace (n k : ℕ) (t : I)
    (p : quotientMap n (k + 1) ⁻¹' preceding n k) :
    compression n k (t, p.val) ∈ preceding n k := by
  have hp := (quotient_mem_preceding_iff n k p.val.1 p.val.2).mp p.property
  change quotientMap n (k + 1) (ReducedCone.contract n (t, p.val.1), p.val.2) ∈ preceding n k
  apply (quotient_mem_preceding_iff n k _ _).mpr
  rcases hp with hw | hc
  · exact Or.inl hw
  · right
    rw [hc, ReducedCone.contract_base]

theorem compressionEndpoint_mem (n k : ℕ)
    (p : ReducedCone.Space n × James.stage (spherePole n) (k + 1)) :
    compressionEndpoint n k p ∈ preceding n k :=
  (quotient_mem_preceding_iff n k (ReducedCone.base n) p.2).mpr (Or.inr rfl)

theorem exists_stage_deformation (n k : ℕ) :
    ∃ R : C(Space n (k + 1), preceding n k), (∀ s : preceding n k, R s.val = s) ∧
      Nonempty ((ContinuousMap.id (Space n (k + 1))).HomotopyRel
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(preceding n k, Space n (k + 1))).comp R)
        (preceding n k)) := by
  have hi : HomotopyExtension.HasHomotopyExtension
      (QuotientAttachment.boundaryInclusion (TopCat.ofHom (quotientMap n (k + 1)))
        (preceding n k)) :=
    NeighborhoodDeformation.hasHomotopyExtension (preimageData n k) IsEmbedding.subtypeVal
  exact QuotientRelativeCompression.exists_deformation (TopCat.ofHom (quotientMap n (k + 1)))
    (preceding n k) (quotientMap_isQuotientMap n (k + 1)) (quotient_fiber_condition n k)
    hi (compression n k) (compression_subspace n k) (compressionEndpoint_mem n k)

end NoExoticSixSphere.JamesSphere.ConeStage
