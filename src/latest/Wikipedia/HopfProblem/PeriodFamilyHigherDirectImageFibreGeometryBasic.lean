import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageZeroBasic

/-!
# The actual inclusion of a native period-family fibre

The map is the original complex period-torus inclusion, retaining its
original real-coordinate values. It is injective and has finite point
fibres. When the base is Hausdorff, compactness of the native torus
makes this actual map closed. Its composite with the original family
projection is the literal constant map to the chosen base point.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreGeometry

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- The original native complex period-torus inclusion, as a morphism of spaces. -/
def fibreMap (P : HolomorphicPeriodMap V B) (b : B) :
    TopCat.of (P.point b).Torus ⟶ TopCat.of P.TotalSpace :=
  TopCat.ofHom ⟨P.fibreInclusion b,
    continuous_const.prodMk (P.torusHomeomorph b).symm.continuous⟩

@[simp] theorem fibreMap_apply (P : HolomorphicPeriodMap V B) (b : B)
    (t : (P.point b).Torus) : fibreMap P b t = P.fibreInclusion b t := rfl

theorem fibreMap_injective (P : HolomorphicPeriodMap V B) (b : B) :
    Function.Injective (fibreMap P b) := P.fibreInclusion_injective b

/-- The image is the literal fibre of the original projection. -/
theorem range_fibreMap (P : HolomorphicPeriodMap V B) (b : B) :
    Set.range (fibreMap P b) = P.projection ⁻¹' {b} := P.range_fibreInclusion b

/-- Injectivity proves finiteness of every actual point fibre. -/
theorem fibreMap_finite_fibres (P : HolomorphicPeriodMap V B) (b : B) (x : P.TotalSpace) :
    ((fibreMap P b) ⁻¹' {x}).Finite :=
  Set.Finite.preimage (fibreMap_injective P b).injOn (Set.finite_singleton x)

/-- In fact every point fibre has at most one point. -/
theorem fibreMap_pointFibre_subsingleton (P : HolomorphicPeriodMap V B) (b : B)
    (x : P.TotalSpace) : Subsingleton ((fibreMap P b) ⁻¹' {x}) :=
  ⟨fun s t => Subtype.ext ((fibreMap_injective P b) (s.property.trans t.property.symm))⟩

/-- Compactness of the original complex torus proves closedness of
the actual inclusion into the Hausdorff total space. -/
theorem fibreMap_isClosedMap [T2Space B] (P : HolomorphicPeriodMap V B) (b : B) :
    IsClosedMap (fibreMap P b) := (fibreMap P b).hom.continuous.isClosedMap

/-- The original base point as an actual constant morphism of spaces. -/
def constantBaseMap (P : HolomorphicPeriodMap V B) (b : B) :
    TopCat.of (P.point b).Torus ⟶ TopCat.of B :=
  TopCat.ofHom ⟨fun _ => b, continuous_const⟩

@[simp] theorem projection_fibreMap_apply (P : HolomorphicPeriodMap V B) (b : B)
    (t : (P.point b).Torus) : Zero.projectionMap P (fibreMap P b t) = b := rfl

/-- The actual topological triangle commutes with the literal constant base map. -/
theorem projection_fibreMap (P : HolomorphicPeriodMap V B) (b : B) :
    fibreMap P b ≫ Zero.projectionMap P = constantBaseMap P b := by
  ext t
  rfl

/-- A base neighborhood of the chosen point contains the entire actual fibre. -/
theorem fibreMap_mem_fullPreimage (P : HolomorphicPeriodMap V B) (b : B)
    {U : Opens B} (hb : b ∈ U) (t : (P.point b).Torus) :
    fibreMap P b t ∈ Zero.basePreimage P U := hb

/-- The genuine inverse image of a full base neighborhood is the whole native torus. -/
theorem fibreMap_preimage_fullPreimage (P : HolomorphicPeriodMap V B) (b : B)
    {U : Opens B} (hb : b ∈ U) :
    (Opens.map (fibreMap P b)).obj (Zero.basePreimage P U) = ⊤ := by
  apply TopologicalSpace.Opens.ext
  ext t
  exact iff_of_true (fibreMap_mem_fullPreimage P b hb t) (by trivial)

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreGeometry
