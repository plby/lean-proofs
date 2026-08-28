import Wikipedia.NoExoticSixSphere.CompactAdjunctionTopology
import Wikipedia.NoExoticSixSphere.JamesSphereConeBoundary
import Wikipedia.NoExoticSixSphere.JamesSphereStageAction

/-!
# The actual auxiliary cone stages for James sphere words

The kth auxiliary space attaches the reduced cone times the kth word
stage to the next word stage by prepending the boundary letter. The
quotient is compact Hausdorff and contains that next word stage as an
actual closed subspace. Contractibility is not assumed in this construction.
-/

noncomputable section

open Set Topology

namespace NoExoticSixSphere.JamesSphere.ConeStage

def data (n k : ℕ) : CompactAdjunction.Data
    (Sphere n × James.stage (spherePole n) k)
    (ReducedCone.Space n × James.stage (spherePole n) k)
    (James.stage (spherePole n) (k + 1)) where
  embedding := (ReducedCone.boundary n).prodMap (ContinuousMap.id _)
  closedEmbedding := (ReducedCone.boundary_isClosedEmbedding n).prodMap .id
  attaching := stageAction n k
  attaching_surjective := stageAction_surjective n k

abbrev Space (n k : ℕ) := CompactAdjunction.Space (data n k)

def quotientMap (n k : ℕ) :
    C(ReducedCone.Space n × James.stage (spherePole n) k, Space n k) :=
  CompactAdjunction.quotientMap (data n k)

theorem quotientMap_isQuotientMap (n k : ℕ) : IsQuotientMap (quotientMap n k) :=
  CompactAdjunction.projection_isQuotientMap (data n k)

def words (n k : ℕ) : C(James.stage (spherePole n) (k + 1), Space n k) :=
  CompactAdjunction.inclusion (data n k)

theorem words_isClosedEmbedding (n k : ℕ) : IsClosedEmbedding (words n k) :=
  CompactAdjunction.inclusion_isClosedEmbedding (data n k)

theorem quotient_boundary (n k : ℕ) (x : Sphere n) (w : James.stage (spherePole n) k) :
    quotientMap n k (ReducedCone.boundary n x, w) = words n k (stageAction n k (x, w)) :=
  CompactAdjunction.quotientMap_embedding (data n k) (x, w)

theorem quotient_base (n k : ℕ) (w : James.stage (spherePole n) k) :
    quotientMap n k (ReducedCone.base n, w) = words n k (StageAttachment.inclusion n k w) := by
  rw [← ReducedCone.boundary_pole, quotient_boundary, stageAction_pole]

theorem quotient_eq_iff (n k : ℕ) (p q : ReducedCone.Space n × James.stage (spherePole n) k) :
    quotientMap n k p = quotientMap n k q ↔ p = q ∨
      ∃ a b : Sphere n × James.stage (spherePole n) k,
        (ReducedCone.boundary n a.1, a.2) = p ∧
        (ReducedCone.boundary n b.1, b.2) = q ∧ stageAction n k a = stageAction n k b :=
  CompactAdjunction.projection_eq_iff (data n k) p q

theorem quotient_mem_words_iff (n k : ℕ)
    (p : ReducedCone.Space n × James.stage (spherePole n) k) :
    quotientMap n k p ∈ Set.range (words n k) ↔ p.1 ∈ Set.range (ReducedCone.boundary n) := by
  have he := CompactAdjunction.preimage_range_inclusion (data n k)
  change p ∈ CompactAdjunction.quotientMap (data n k) ⁻¹'
    Set.range (CompactAdjunction.inclusion (data n k)) ↔ _
  rw [he]
  constructor
  · rintro ⟨⟨x, w⟩, hxw⟩
    exact ⟨x, congrArg Prod.fst hxw⟩
  · rintro ⟨x, hx⟩
    exact ⟨(x, p.2), Prod.ext hx rfl⟩

end NoExoticSixSphere.JamesSphere.ConeStage
