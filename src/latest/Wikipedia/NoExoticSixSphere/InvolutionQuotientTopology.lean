import Wikipedia.NoExoticSixSphere.InvolutionQuotient
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Hausdorff

/-!
# Separation and free neighborhoods in the actual involution quotient

The orbit quotient of a Hausdorff space is Hausdorff: its equivalence relation
is the union of the diagonal and the graph of the involution. The projection
is closed as well as open. Away from fixed points it is an open embedding
on a genuine open neighborhood disjoint from its swapped copy.
-/

open Set Function Topology

namespace NoExoticSixSphere.InvolutionQuotient

variable {X : Type*} [TopologicalSpace X]

theorem isClosedMap_proj (σ : X → X) (hσ : Involutive σ) (hc : Continuous σ) :
    IsClosedMap (proj σ hσ) := by
  intro S hS
  apply (isOpenQuotientMap_proj σ hσ hc).isQuotientMap.isClosed_preimage.mp
  rw [preimage_image_proj]
  exact hS.union (hS.preimage hc)

theorem t2Space_orbit [T2Space X] (σ : X → X) (hσ : Involutive σ)
    (hc : Continuous σ) : T2Space (Orbit σ hσ) := by
  apply (t2Space_iff_of_isOpenQuotientMap (isOpenQuotientMap_proj σ hσ hc)).mpr
  have he : {q : X × X | proj σ hσ q.1 = proj σ hσ q.2} =
      {q : X × X | q.1 = q.2} ∪ {q : X × X | σ q.1 = q.2} := by
    ext q
    exact proj_eq_iff σ hσ q.1 q.2
  rw [he]
  exact (isClosed_eq continuous_fst continuous_snd).union
    (isClosed_eq (hc.comp continuous_fst) continuous_snd)

theorem secondCountable_orbit [SecondCountableTopology X] (σ : X → X)
    (hσ : Involutive σ) (hc : Continuous σ) : SecondCountableTopology (Orbit σ hσ) :=
  (isOpenQuotientMap_proj σ hσ hc).isQuotientMap.secondCountableTopology
    (isOpenQuotientMap_proj σ hσ hc).isOpenMap

theorem exists_free_neighborhood [T2Space X] (σ : X → X) (hc : Continuous σ)
    (x : X) (hx : σ x ≠ x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Disjoint U (σ ⁻¹' U) := by
  obtain ⟨A, B, hA, hB, hxA, hxB, hAB⟩ := t2_separation hx.symm
  refine ⟨A ∩ σ ⁻¹' B, hA.inter (hB.preimage hc), ⟨hxA, hxB⟩, ?_⟩
  apply disjoint_left.mpr
  intro y hy hsy
  exact (disjoint_left.mp hAB) hsy.1 hy.2

theorem isOpenEmbedding_restrict_proj (σ : X → X) (hσ : Involutive σ)
    (hc : Continuous σ) {U : Set X} (hU : IsOpen U) (hdis : Disjoint U (σ ⁻¹' U)) :
    IsOpenEmbedding (fun x : U ↦ proj σ hσ x.val) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact (continuous_proj σ hσ).comp continuous_subtype_val
  · intro x y he
    rcases (proj_eq_iff σ hσ x.val y.val).mp he with he | he
    · exact Subtype.ext he
    · have hs : σ x.val ∈ U := he.symm ▸ y.property
      exact False.elim ((disjoint_left.mp hdis) x.property hs)
  · exact (isOpenQuotientMap_proj σ hσ hc).isOpenMap.comp
      hU.isOpenEmbedding_subtypeVal.isOpenMap

theorem isClosed_fixed_orbits [T2Space X] (σ : X → X) (hσ : Involutive σ)
    (hc : Continuous σ) : IsClosed (proj σ hσ '' {x | σ x = x}) :=
  isClosedMap_proj σ hσ hc _ (isClosed_eq hc continuous_id)

omit [TopologicalSpace X] in
theorem mem_fixed_orbits_iff (σ : X → X) (hσ : Involutive σ) (x : X) :
    proj σ hσ x ∈ proj σ hσ '' {y | σ y = y} ↔ σ x = x := by
  constructor
  · rintro ⟨y, hy, he⟩
    rcases (proj_eq_iff σ hσ y x).mp he with rfl | he
    · exact hy
    · rw [hy] at he
      exact he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

end NoExoticSixSphere.InvolutionQuotient
