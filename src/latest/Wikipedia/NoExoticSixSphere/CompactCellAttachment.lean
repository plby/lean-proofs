import Wikipedia.NoExoticSixSphere.CompactAdjunctionPushout
import Wikipedia.NoExoticSixSphere.PuncturedCellAttachment

/-!
# A concrete compact Hausdorff cell attachment

An identity copy of the base is included in the quotient presentation,
so no surjectivity of the boundary attaching map is required. The actual
base inclusion and characteristic disk satisfy the original topological
pushout property. Compactness and Hausdorff separation are inherited from
the proved compact adjunction construction.
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Set Metric Topology

namespace NoExoticSixSphere.CompactCellAttachment

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]

abbrev Disk (E : Type u) [NormedAddCommGroup E] := PuncturedCellAttachment.Disk E

def enlargedEmbedding : C(Y ⊕ sphere (0 : E) 1, Y ⊕ Disk E) :=
  ⟨Sum.elim Sum.inl (fun s ↦ Sum.inr (PuncturedCellAttachment.boundary s)),
    continuous_sumElim.mpr ⟨continuous_inl,
      continuous_inr.comp PuncturedCellAttachment.boundary.hom.continuous⟩⟩

theorem enlargedEmbedding_injective : Function.Injective (enlargedEmbedding (E := E) (Y := Y)) := by
  intro x y h
  cases x with
  | inl a =>
    cases y with
    | inl b => exact congrArg Sum.inl (Sum.inl.inj h)
    | inr b => cases h
  | inr a =>
    cases y with
    | inl b => cases h
    | inr b => exact congrArg Sum.inr (PuncturedCellAttachment.boundary_injective (Sum.inr.inj h))

variable (f : C(sphere (0 : E) 1, Y))

def enlargedAttaching : C(Y ⊕ sphere (0 : E) 1, Y) :=
  ⟨Sum.elim id f, continuous_sumElim.mpr ⟨continuous_id, f.continuous⟩⟩

def data : CompactAdjunction.Data (Y ⊕ sphere (0 : E) 1) (Y ⊕ Disk E) Y where
  embedding := enlargedEmbedding
  closedEmbedding := enlargedEmbedding.continuous.isClosedEmbedding enlargedEmbedding_injective
  attaching := enlargedAttaching f
  attaching_surjective y := ⟨Sum.inl y, rfl⟩

abbrev Space := CompactAdjunction.Space (data f)

def base : C(Y, Space f) := CompactAdjunction.inclusion (data f)

def cell : C(Disk E, Space f) :=
  (CompactAdjunction.quotientMap (data f)).comp ⟨Sum.inr, continuous_inr⟩

theorem quotient_inl (y : Y) : CompactAdjunction.quotientMap (data f) (Sum.inl y) = base f y :=
  CompactAdjunction.quotientMap_embedding (data f) (Sum.inl y)

theorem cell_boundary (s : sphere (0 : E) 1) :
    cell f (PuncturedCellAttachment.boundary s) = base f (f s) :=
  CompactAdjunction.quotientMap_embedding (data f) (Sum.inr s)

theorem space_cases (z : Space f) :
    (∃ y, base f y = z) ∨ ∃ x, cell f x = z := by
  obtain ⟨y | x, he⟩ := CompactAdjunction.projection_surjective (data f) z
  · exact Or.inl ⟨y, (quotient_inl f y).symm.trans he⟩
  · exact Or.inr ⟨x, he⟩

theorem base_isClosedEmbedding : IsClosedEmbedding (base f) :=
  CompactAdjunction.inclusion_isClosedEmbedding (data f)

variable {Z : Type v} [TopologicalSpace Z] (F : C(Y, Z)) (G : C(Disk E, Z))
  (hFG : ∀ s, F (f s) = G (PuncturedCellAttachment.boundary s))

def enlargedMap : C(Y ⊕ Disk E, Z) :=
  ⟨Sum.elim F G, continuous_sumElim.mpr ⟨F.continuous, G.continuous⟩⟩

include hFG in
theorem enlargedMap_compatible (x : Y ⊕ sphere (0 : E) 1) :
    enlargedMap F G ((data f).embedding x) = F ((data f).attaching x) := by
  cases x with
  | inl y => rfl
  | inr s => exact (hFG s).symm

def glue : C(Space f, Z) :=
  CompactAdjunction.glue (data f) (enlargedMap F G) F (enlargedMap_compatible f F G hFG)

theorem glue_base (y : Y) : glue f F G hFG (base f y) = F y :=
  CompactAdjunction.glue_inclusion (data f) (enlargedMap F G) F
    (enlargedMap_compatible f F G hFG) y

theorem glue_cell (x : Disk E) : glue f F G hFG (cell f x) = G x :=
  CompactAdjunction.glue_quotientMap (data f) (enlargedMap F G) F
    (enlargedMap_compatible f F G hFG) (Sum.inr x)

theorem isPushout : IsPushout (TopCat.ofHom f) PuncturedCellAttachment.boundary
    (TopCat.ofHom (base f)) (TopCat.ofHom (cell f)) := by
  apply IsPushout.mk'
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    exact fun s ↦ (cell_boundary f s).symm
  · intro T φ ψ hbase hcell
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    rcases space_cases f z with ⟨y, rfl⟩ | ⟨x, rfl⟩
    · exact congrArg (fun k ↦ k y) hbase
    · exact congrArg (fun k ↦ k x) hcell
  · intro T F G hw
    have h : ∀ s, F (f s) = G (PuncturedCellAttachment.boundary s) :=
      fun s ↦ congrArg (fun k ↦ k s) hw
    refine ⟨TopCat.ofHom (glue f F.hom G.hom h), ?_, ?_⟩
    · apply TopCat.hom_ext
      apply ContinuousMap.ext
      exact glue_base f F.hom G.hom h
    · apply TopCat.hom_ext
      apply ContinuousMap.ext
      exact glue_cell f F.hom G.hom h

end NoExoticSixSphere.CompactCellAttachment
