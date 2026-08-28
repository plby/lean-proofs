import Wikipedia.NoExoticSixSphere.RegularCollaredCylinder

/-!
# Actual endpoint fibers inside the bounded slab

The two endpoint inclusions retain the spatial point and insert the specified
time. Their images in the actual endpoint subset are closed, and both maps
are topological embeddings. These facts do not require compactness.
-/

open scoped Manifold ContDiff
open Set Topology

namespace NoExoticSixSphere.RegularCollaredCylinder

variable {B H M C H' N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace N] [ChartedSpace H' N]
  {b : N} {s t : ℝ} (d : RegularCollaredCylinder (M := M) I J b s t)

abbrev endpointBoundary :=
  {p : CylinderFiberSlab.slab d.map b s t // p.val.val.1 = s ∨ p.val.val.1 = t}

def leftEndpoint (x : {x : M // d.leftMap x = b}) : d.endpointBoundary :=
  ⟨⟨⟨(s, x.val), (d.left_eq s d.left_mem x.val).trans x.property⟩,
    ⟨le_rfl, d.time_lt.le⟩⟩, Or.inl rfl⟩

def rightEndpoint (x : {x : M // d.rightMap x = b}) : d.endpointBoundary :=
  ⟨⟨⟨(t, x.val), (d.right_eq t d.right_mem x.val).trans x.property⟩,
    ⟨d.time_lt.le, le_rfl⟩⟩, Or.inr rfl⟩

theorem continuous_endpointAmbient :
    Continuous (fun p : d.endpointBoundary ↦ p.val.val.val) :=
  (continuous_subtype_val : Continuous
    (Subtype.val : {p : ℝ × M // d.map p = b} → ℝ × M)).comp
      (continuous_subtype_val.comp continuous_subtype_val)

theorem continuous_leftEndpoint : Continuous d.leftEndpoint := by
  have h : Continuous (fun x : {x : M // d.leftMap x = b} ↦ (s, x.val)) :=
    continuous_const.prodMk continuous_subtype_val
  exact ((h.subtype_mk _).subtype_mk _).subtype_mk _

theorem continuous_rightEndpoint : Continuous d.rightEndpoint := by
  have h : Continuous (fun x : {x : M // d.rightMap x = b} ↦ (t, x.val)) :=
    continuous_const.prodMk continuous_subtype_val
  exact ((h.subtype_mk _).subtype_mk _).subtype_mk _

theorem leftMap_eq_value_of_time (p : CylinderFiberSlab.slab d.map b s t)
    (hp : p.val.val.1 = s) : d.leftMap p.val.val.2 = b := by
  have heq : (s, p.val.val.2) = p.val.val := Prod.ext hp.symm rfl
  exact (d.left_eq s d.left_mem _).symm.trans ((congrArg d.map heq).trans p.val.property)

theorem rightMap_eq_value_of_time (p : CylinderFiberSlab.slab d.map b s t)
    (hp : p.val.val.1 = t) : d.rightMap p.val.val.2 = b := by
  have heq : (t, p.val.val.2) = p.val.val := Prod.ext hp.symm rfl
  exact (d.right_eq t d.right_mem _).symm.trans ((congrArg d.map heq).trans p.val.property)

theorem range_leftEndpoint : range d.leftEndpoint = {p | p.val.val.val.1 = s} := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    rfl
  · intro hp
    refine ⟨⟨p.val.val.val.2, d.leftMap_eq_value_of_time p.val hp⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hp.symm rfl

theorem range_rightEndpoint : range d.rightEndpoint = {p | p.val.val.val.1 = t} := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    rfl
  · intro hp
    refine ⟨⟨p.val.val.val.2, d.rightMap_eq_value_of_time p.val hp⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hp.symm rfl

theorem isClosedEmbedding_leftEndpoint : IsClosedEmbedding d.leftEndpoint := by
  have he : IsEmbedding d.leftEndpoint := by
    apply IsEmbedding.of_comp d.continuous_leftEndpoint d.continuous_endpointAmbient.snd
    change IsEmbedding (Subtype.val : {x : M // d.leftMap x = b} → M)
    exact IsEmbedding.subtypeVal
  refine ⟨he, ?_⟩
  rw [d.range_leftEndpoint]
  exact isClosed_eq d.continuous_endpointAmbient.fst continuous_const

theorem isClosedEmbedding_rightEndpoint : IsClosedEmbedding d.rightEndpoint := by
  have he : IsEmbedding d.rightEndpoint := by
    apply IsEmbedding.of_comp d.continuous_rightEndpoint d.continuous_endpointAmbient.snd
    change IsEmbedding (Subtype.val : {x : M // d.rightMap x = b} → M)
    exact IsEmbedding.subtypeVal
  refine ⟨he, ?_⟩
  rw [d.range_rightEndpoint]
  exact isClosed_eq d.continuous_endpointAmbient.fst continuous_const

theorem injective_endpointSum :
    Function.Injective (Sum.elim d.leftEndpoint d.rightEndpoint) := by
  intro x y h
  cases x with
  | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (d.isClosedEmbedding_leftEndpoint.injective h)
      | inr y =>
          have he : s = t := congrArg (fun p : d.endpointBoundary ↦ p.val.val.val.1) h
          exact (d.time_lt.ne he).elim
  | inr x =>
      cases y with
      | inl y =>
          have he : t = s := congrArg (fun p : d.endpointBoundary ↦ p.val.val.val.1) h
          exact (d.time_lt.ne he.symm).elim
      | inr y => exact congrArg Sum.inr (d.isClosedEmbedding_rightEndpoint.injective h)

theorem surjective_endpointSum :
    Function.Surjective (Sum.elim d.leftEndpoint d.rightEndpoint) := by
  intro p
  rcases p.property with hp | hp
  · have hr : p ∈ range d.leftEndpoint := by rw [d.range_leftEndpoint]; exact hp
    obtain ⟨x, hx⟩ := hr
    exact ⟨Sum.inl x, hx⟩
  · have hr : p ∈ range d.rightEndpoint := by rw [d.range_rightEndpoint]; exact hp
    obtain ⟨x, hx⟩ := hr
    exact ⟨Sum.inr x, hx⟩

noncomputable def endpointHomeomorph :
    ({x : M // d.leftMap x = b} ⊕ {x : M // d.rightMap x = b}) ≃ₜ d.endpointBoundary :=
  (d.isClosedEmbedding_leftEndpoint.sumElim d.isClosedEmbedding_rightEndpoint
    d.injective_endpointSum).isEmbedding.toHomeomorphOfSurjective d.surjective_endpointSum

theorem endpointHomeomorph_inl (x : {x : M // d.leftMap x = b}) :
    d.endpointHomeomorph (Sum.inl x) = d.leftEndpoint x := rfl

theorem endpointHomeomorph_inr (x : {x : M // d.rightMap x = b}) :
    d.endpointHomeomorph (Sum.inr x) = d.rightEndpoint x := rfl

end NoExoticSixSphere.RegularCollaredCylinder
