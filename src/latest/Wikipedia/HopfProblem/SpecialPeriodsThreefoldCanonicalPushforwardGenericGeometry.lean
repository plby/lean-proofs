import Wikipedia.HopfProblem.SpecialPeriodsThreefoldDirectImage
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalFiniteRegularSectionGeometry

/-!
# The actual generic base open for canonical pushforward

The sphere open excluding infinity and one pulls back exactly to the
already constructed finite regular-section domain.  Intersections,
restriction maps, and their native holomorphicity are literal ones for
the original spaces.  Density follows from the actual Cartier generic
set and the constructed continuous surjective sphere projection.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Generic

attribute [local instance] Threefold.chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The actual sphere open obtained by removing the cusp and order-four values. -/
def genericBase : Opens RiemannSphere :=
  ⟨{p | p ≠ (∞ : RiemannSphere) ∧ p ≠ ((1 : ℂ) : RiemannSphere)},
    isOpen_ne.inter isOpen_ne⟩

@[simp] theorem mem_genericBase (p : RiemannSphere) :
    p ∈ genericBase ↔ p ≠ (∞ : RiemannSphere) ∧ p ≠ ((1 : ℂ) : RiemannSphere) := Iff.rfl

/-- Restriction of an arbitrary sphere open to the actual generic base. -/
def genericPart (U : Opens RiemannSphere) : Opens RiemannSphere := U ⊓ genericBase

@[simp] theorem mem_genericPart (U : Opens RiemannSphere) (p : RiemannSphere) :
    p ∈ genericPart U ↔
      p ∈ U ∧ p ≠ (∞ : RiemannSphere) ∧ p ≠ ((1 : ℂ) : RiemannSphere) := Iff.rfl

theorem genericPart_le (U : Opens RiemannSphere) : genericPart U ≤ U := inf_le_left

theorem genericPart_le_genericBase (U : Opens RiemannSphere) :
    genericPart U ≤ genericBase := inf_le_right

theorem genericPart_mono {U V : Opens RiemannSphere} (hUV : U ≤ V) :
    genericPart U ≤ genericPart V := inf_le_inf_right _ hUV

@[simp] theorem mem_basePreimage_genericBase (x : Threefold.Space) :
    x ∈ Threefold.basePreimage genericBase ↔
      Threefold.projectionSphere x ≠ (∞ : RiemannSphere) ∧
        Threefold.projectionSphere x ≠ ((1 : ℂ) : RiemannSphere) := Iff.rfl

@[simp] theorem mem_basePreimage_genericPart (U : Opens RiemannSphere) (x : Threefold.Space) :
    x ∈ Threefold.basePreimage (genericPart U) ↔
      Threefold.projectionSphere x ∈ U ∧
        Threefold.projectionSphere x ≠ (∞ : RiemannSphere) ∧
          Threefold.projectionSphere x ≠ ((1 : ℂ) : RiemannSphere) := Iff.rfl

/-- The generic sphere preimage is the existing domain, not a new substitute. -/
theorem basePreimage_genericBase :
    Threefold.basePreimage genericBase = GlobalFiniteRegularSection.domain := by
  ext x
  exact (GlobalFiniteRegularSection.mem_domain x).symm

theorem basePreimage_inf (U V : Opens RiemannSphere) :
    Threefold.basePreimage (U ⊓ V) = Threefold.basePreimage U ⊓ Threefold.basePreimage V := by
  ext x
  rfl

theorem basePreimage_genericPart (U : Opens RiemannSphere) :
    Threefold.basePreimage (genericPart U) =
      Threefold.basePreimage U ⊓ GlobalFiniteRegularSection.domain := by
  rw [genericPart, basePreimage_inf, basePreimage_genericBase]

theorem preimage_genericPart_le (U : Opens RiemannSphere) :
    Threefold.basePreimage (genericPart U) ≤ Threefold.basePreimage U :=
  Threefold.basePreimage_mono (genericPart_le U)

theorem preimage_genericPart_le_domain (U : Opens RiemannSphere) :
    Threefold.basePreimage (genericPart U) ≤ GlobalFiniteRegularSection.domain := by
  rw [basePreimage_genericPart]
  exact inf_le_right

theorem preimage_genericPart_mono {U V : Opens RiemannSphere} (hUV : U ≤ V) :
    Threefold.basePreimage (genericPart U) ≤ Threefold.basePreimage (genericPart V) :=
  Threefold.basePreimage_mono (genericPart_mono hUV)

/-- Literal inclusion of a generic base point in the original base open. -/
def basePoint (U : Opens RiemannSphere) : genericPart U → U :=
  Set.inclusion (genericPart_le U)

/-- Literal inclusion in the full preimage of the original base open. -/
def preimagePoint (U : Opens RiemannSphere) :
    Threefold.basePreimage (genericPart U) → Threefold.basePreimage U :=
  Set.inclusion (preimage_genericPart_le U)

/-- The same actual total-space point, now in the existing section domain. -/
def domainPoint (U : Opens RiemannSphere) :
    Threefold.basePreimage (genericPart U) → GlobalFiniteRegularSection.domain :=
  Set.inclusion (preimage_genericPart_le_domain U)

@[simp] theorem basePoint_val (U : Opens RiemannSphere) (p : genericPart U) :
    (basePoint U p : RiemannSphere) = (p : RiemannSphere) := rfl

@[simp] theorem preimagePoint_val (U : Opens RiemannSphere)
    (x : Threefold.basePreimage (genericPart U)) :
    (preimagePoint U x : Threefold.Space) = (x : Threefold.Space) := rfl

@[simp] theorem domainPoint_val (U : Opens RiemannSphere)
    (x : Threefold.basePreimage (genericPart U)) :
    (domainPoint U x : Threefold.Space) = (x : Threefold.Space) := rfl

theorem basePoint_holomorphic (U : Opens RiemannSphere) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (basePoint U) := contMDiff_inclusion (genericPart_le U)

theorem preimagePoint_holomorphic (U : Opens RiemannSphere) :
    ContMDiff IF IF ω (preimagePoint U) := contMDiff_inclusion (preimage_genericPart_le U)

theorem domainPoint_holomorphic (U : Opens RiemannSphere) :
    ContMDiff IF IF ω (domainPoint U) := contMDiff_inclusion (preimage_genericPart_le_domain U)

/-- Restriction commutes with the actual base projection pointwise. -/
@[simp] theorem baseProjection_preimagePoint (U : Opens RiemannSphere)
    (x : Threefold.basePreimage (genericPart U)) :
    Threefold.baseProjection U (preimagePoint U x) =
      basePoint U (Threefold.baseProjection (genericPart U) x) := rfl

theorem baseProjection_genericPart_surjective (U : Opens RiemannSphere) :
    Function.Surjective (Threefold.baseProjection (genericPart U)) :=
  Threefold.baseProjection_surjective (genericPart U)

/-- Density comes from the already constructed actual Cartier domain. -/
theorem basePreimage_genericBase_dense :
    Dense (Threefold.basePreimage genericBase : Set Threefold.Space) := by
  rw [basePreimage_genericBase]
  exact GlobalPrescribedDivisor.genericSet_dense

theorem genericBase_dense : Dense (genericBase : Set RiemannSphere) :=
  Threefold.projectionSphere_surjective.denseRange.dense_of_mapsTo
    Threefold.projectionSphere_continuous basePreimage_genericBase_dense (fun _ hx => hx)

/-- Generic points remain dense after restricting to any original base open. -/
theorem genericPart_dense (U : Opens RiemannSphere) :
    Dense {p : U | (p : RiemannSphere) ∈ genericBase} :=
  genericBase_dense.preimage U.isOpen.isOpenMap_subtype_val

/-- The corresponding assertion on every full total-space preimage. -/
theorem preimage_genericPart_dense (U : Opens RiemannSphere) :
    Dense {x : Threefold.basePreimage U | (x : Threefold.Space) ∈
      GlobalFiniteRegularSection.domain} :=
  GlobalPrescribedDivisor.genericSet_dense.preimage
    (Threefold.basePreimage U).isOpen.isOpenMap_subtype_val

theorem basePoint_denseRange (U : Opens RiemannSphere) : DenseRange (basePoint U) := by
  apply (denseRange_inclusion_iff (genericPart_le U)).mpr
  exact genericBase_dense.open_subset_closure_inter U.isOpen

theorem preimagePoint_denseRange (U : Opens RiemannSphere) :
    DenseRange (preimagePoint U) := by
  apply (denseRange_inclusion_iff (preimage_genericPart_le U)).mpr
  rw [basePreimage_genericPart]
  exact GlobalPrescribedDivisor.genericSet_dense.open_subset_closure_inter
    (Threefold.basePreimage U).isOpen

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Generic
