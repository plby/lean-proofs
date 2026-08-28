import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Sets.Opens

/-!
# Local subgroup quotients inside an actual orbit space

If an open set is invariant under a subgroup and no other group element
returns it to itself, its subgroup orbit quotient is homeomorphic to its
image in the full orbit space.  Both quotients use the actual actions and
`MulAction.orbitRel`; the map is induced by the inclusion of the open set.

This applies to precisely invariant elliptic neighbourhoods in the
triangle action.  No freeness, separation, or complex atlas is assumed.
-/

noncomputable section

open Function Set Topology TopologicalSpace

namespace Wikipedia.HopfProblem.LocalOrbitQuotient

variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]

/-- Restrict the actual subgroup action to an invariant open set. -/
@[instance_reducible] def restrictedAction (H : Subgroup G) (U : Opens X)
    (hU : ∀ h : H, MapsTo (fun x : X => (h : G) • x) U U) : MulAction H U where
  smul h x := ⟨(h : G) • (x : X), hU h x.property⟩
  one_smul x := Subtype.ext (one_smul G (x : X))
  mul_smul h k x := Subtype.ext (mul_smul (h : G) (k : G) (x : X))

variable (H : Subgroup G) (U : Opens X)
variable (hU : ∀ h : H, MapsTo (fun x : X => (h : G) • x) U U)

/-- The actual subgroup orbit quotient of the invariant open set. -/
abbrev LocalQuotient :=
  letI := restrictedAction H U hU
  Quotient (MulAction.orbitRel H U)

/-- Projection to the local subgroup quotient. -/
def localProjection : U → LocalQuotient H U hU := Quotient.mk _

@[simp] theorem restricted_smul_val (h : H) (x : U) :
    letI := restrictedAction H U hU
    ((h • x : U) : X) = (h : G) • (x : X) := rfl

theorem localProjection_eq_iff (x y : U) :
    localProjection H U hU x = localProjection H U hU y ↔
      ∃ h : H, (h : G) • (y : X) = (x : X) := by
  let := restrictedAction H U hU
  rw [localProjection, Quotient.eq]
  change (∃ h : H, h • y = x) ↔ _
  exact exists_congr fun h => Subtype.ext_iff

theorem localProjection_surjective : Surjective (localProjection H U hU) :=
  Quotient.mk_surjective

theorem localProjection_continuous : Continuous (localProjection H U hU) :=
  continuous_quotient_mk'

variable [ContinuousConstSMul G X]

/-- The restricted action remains continuous on each group element. -/
theorem restricted_continuousConstSMul :
    letI := restrictedAction H U hU
    ContinuousConstSMul H U := by
  let := restrictedAction H U hU
  exact ⟨fun h =>
    ((continuous_const_smul (h : G)).comp continuous_subtype_val).subtype_mk _⟩

theorem localProjection_isOpenQuotientMap :
    IsOpenQuotientMap (localProjection H U hU) := by
  let := restrictedAction H U hU
  let := restricted_continuousConstSMul H U hU
  exact MulAction.isOpenQuotientMap_quotientMk

/-- The actual image of the open set in the full orbit quotient, as an
open set with the inherited topology. -/
def imageOpen : Opens (Quotient (MulAction.orbitRel G X)) :=
  ⟨Quotient.mk (MulAction.orbitRel G X) '' (U : Set X),
    MulAction.isOpenQuotientMap_quotientMk.isOpenMap _ U.isOpen⟩

@[simp] theorem mem_imageOpen (q : Quotient (MulAction.orbitRel G X)) :
    q ∈ imageOpen (G := G) U ↔
      ∃ x ∈ U, Quotient.mk (MulAction.orbitRel G X) x = q := Iff.rfl

/-- The full inverse image is precisely the union of all translates. -/
theorem preimage_imageOpen :
    Quotient.mk (MulAction.orbitRel G X) ⁻¹' (imageOpen (G := G) U : Set _) =
      ⋃ g : G, (g • ·) '' (U : Set X) :=
  MulAction.quotient_preimage_image_eq_union_mul (G := G) (U : Set X)

/-- The global projection restricted to the open set, with its actual
image as codomain. -/
def imageProjection : U → imageOpen (G := G) U :=
  fun x => ⟨Quotient.mk _ (x : X), x, x.property, rfl⟩

@[simp] theorem imageProjection_val (x : U) :
    (imageProjection (G := G) U x : Quotient (MulAction.orbitRel G X)) =
      Quotient.mk (MulAction.orbitRel G X) (x : X) := rfl

theorem imageProjection_surjective : Surjective (imageProjection (G := G) U) := by
  rintro ⟨q, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem imageProjection_continuous : Continuous (imageProjection (G := G) U) :=
  (continuous_quotient_mk'.comp continuous_subtype_val).subtype_mk _

theorem imageProjection_isOpenMap : IsOpenMap (imageProjection (G := G) U) :=
  (MulAction.isOpenQuotientMap_quotientMk.isOpenMap.comp
    U.isOpen.isOpenMap_subtype_val).subtype_mk _

theorem imageProjection_isOpenQuotientMap :
    IsOpenQuotientMap (imageProjection (G := G) U) :=
  ⟨imageProjection_surjective U, imageProjection_continuous U, imageProjection_isOpenMap U⟩

/-- The map from the local subgroup quotient to the image of the open
set in the full quotient.  It is induced by the literal inclusion. -/
def localToImage : LocalQuotient H U hU → imageOpen (G := G) U :=
  Quotient.lift (imageProjection (G := G) U) fun x y h => by
    apply Subtype.ext
    apply Quotient.sound
    obtain ⟨g, hg⟩ := h
    exact ⟨(g : G), congrArg Subtype.val hg⟩

@[simp] theorem localToImage_mk (x : U) :
    localToImage H U hU (localProjection H U hU x) = imageProjection (G := G) U x := rfl

theorem localToImage_continuous : Continuous (localToImage H U hU) :=
  (imageProjection_continuous U).quotient_lift _

theorem localToImage_surjective : Surjective (localToImage H U hU) := by
  intro q
  obtain ⟨x, rfl⟩ := imageProjection_surjective U q
  exact ⟨localProjection H U hU x, rfl⟩

theorem localToImage_isOpenMap : IsOpenMap (localToImage H U hU) :=
  IsOpenMap.of_comp (localProjection_continuous H U hU)
    (localProjection_surjective H U hU) (imageProjection_isOpenMap U)

/-- The return condition guarantees that two points in the open set
have the same global orbit exactly when they have the same local orbit. -/
theorem localToImage_injective
    (hreturn : ∀ g : G, (((g • ·) '' (U : Set X)) ∩ U).Nonempty → g ∈ H) :
    Injective (localToImage H U hU) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro x y h
  have hxy : Quotient.mk (MulAction.orbitRel G X) (x : X) =
      Quotient.mk (MulAction.orbitRel G X) (y : X) := congrArg Subtype.val h
  obtain ⟨g, hg⟩ := Quotient.exact hxy
  have hgH : g ∈ H := hreturn g ⟨x, ⟨y, y.property, hg⟩, x.property⟩
  exact (localProjection_eq_iff H U hU x y).mpr ⟨⟨g, hgH⟩, hg⟩

/-- A precisely invariant open set has its actual subgroup orbit space
homeomorphic to its open image in the full orbit quotient. -/
def localHomeomorph
    (hreturn : ∀ g : G, (((g • ·) '' (U : Set X)) ∩ U).Nonempty → g ∈ H) :
    LocalQuotient H U hU ≃ₜ imageOpen (G := G) U :=
  Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective (localToImage H U hU)
      ⟨localToImage_injective H U hU hreturn, localToImage_surjective H U hU⟩)
    (localToImage_continuous H U hU) (localToImage_isOpenMap H U hU)

@[simp] theorem localHomeomorph_apply
    (hreturn : ∀ g : G, (((g • ·) '' (U : Set X)) ∩ U).Nonempty → g ∈ H)
    (q : LocalQuotient H U hU) :
    localHomeomorph H U hU hreturn q = localToImage H U hU q := rfl

@[simp] theorem localHomeomorph_mk
    (hreturn : ∀ g : G, (((g • ·) '' (U : Set X)) ∩ U).Nonempty → g ∈ H) (x : U) :
    localHomeomorph H U hU hreturn (localProjection H U hU x) =
      imageProjection (G := G) U x := rfl

/-- The local homeomorphism commutes with the two genuine quotient
projections and with inclusion of its open image in the global quotient. -/
theorem localHomeomorph_mk_val
    (hreturn : ∀ g : G, (((g • ·) '' (U : Set X)) ∩ U).Nonempty → g ∈ H) (x : U) :
    (localHomeomorph H U hU hreturn (localProjection H U hU x) :
        Quotient (MulAction.orbitRel G X)) =
      Quotient.mk (MulAction.orbitRel G X) (x : X) := rfl

end Wikipedia.HopfProblem.LocalOrbitQuotient
