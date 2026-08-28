import Wikipedia.HopfProblem.CuspCentralHomologyFundamentalCell
import Wikipedia.HopfProblem.CuspCentralHomologyOpenCoverFibres

/-!
# The open interior part of the actual central cusp fibre

Compact fibre phases over the literal interior of the central hexagon
map injectively into the existing central cusp quotient.  Restricting
the proper fundamental-cell presentation identifies this product with
its actual open image, with the inherited subspace topology.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspCollapse CuspHoneycomb CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane

/-- Compact fibre phases over the literal planar interior of the central cell. -/
abbrev InteriorPhaseCell := CompactFibreTorus × (interior baseCell)

/-- Inclusion into the actual closed fundamental-cell presentation. -/
def interiorCellInclusion (p : InteriorPhaseCell) : FundamentalCell :=
  (p.1, ⟨(p.2 : Plane), interior_subset p.2.2⟩)

@[simp] theorem interiorCellInclusion_fst (p : InteriorPhaseCell) :
    (interiorCellInclusion p).1 = p.1 := rfl

@[simp] theorem interiorCellInclusion_snd_coe (p : InteriorPhaseCell) :
    ((interiorCellInclusion p).2 : Plane) = (p.2 : Plane) := rfl

theorem interiorCellInclusion_continuous : Continuous interiorCellInclusion :=
  continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

theorem interiorCellInclusion_injective : Function.Injective interiorCellInclusion := by
  intro p q hpq
  apply Prod.ext
  · exact congrArg (fun r : FundamentalCell => r.1) hpq
  · apply Subtype.ext
    exact congrArg (fun r : FundamentalCell => (r.2 : Plane)) hpq

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The fundamental-cell map restricted to the actual cell interior. -/
def interiorCellMap : InteriorPhaseCell → QuotientCentralFibre C ε :=
  fundamentalCellMap C ε hε ∘ interiorCellInclusion

theorem interiorCellMap_eq_fundamentalCellMap (p : InteriorPhaseCell) :
    interiorCellMap C ε hε p = fundamentalCellMap C ε hε (interiorCellInclusion p) := rfl

@[simp] theorem interiorCellMap_apply (p : InteriorPhaseCell) :
    interiorCellMap C ε hε p = honeycombCollapseMap C ε hε (p.1, (p.2 : Plane)) := rfl

theorem interiorCellMap_continuous : Continuous (interiorCellMap C ε hε) :=
  (fundamentalCellMap_continuous C ε hε).comp interiorCellInclusion_continuous

theorem interiorCellMap_injective : Function.Injective (interiorCellMap C ε hε) := by
  intro p q hpq
  apply interiorCellInclusion_injective
  exact fundamentalCellMap_eq_of_interior C ε hε (interiorCellInclusion p)
    (interiorCellInclusion q) p.2.2 hpq

/-- This is a subset of the original quotient, not a replacement topology. -/
def interiorImage : Set (QuotientCentralFibre C ε) := range (interiorCellMap C ε hε)

/-- The interior image is saturated for the actual fundamental-cell map. -/
theorem fundamentalCellMap_mem_interiorImage_iff (p : FundamentalCell) :
    fundamentalCellMap C ε hε p ∈ interiorImage C ε hε ↔
      (p.2 : Plane) ∈ interior baseCell := by
  constructor
  · rintro ⟨q, hq⟩
    have he := fundamentalCellMap_eq_of_interior C ε hε (interiorCellInclusion q) p q.2.2 hq
    rw [← he]
    exact q.2.2
  · intro hp
    exact ⟨(p.1, ⟨(p.2 : Plane), hp⟩), rfl⟩

theorem fundamentalCellMap_preimage_interiorImage :
    fundamentalCellMap C ε hε ⁻¹' interiorImage C ε hε =
      {p : FundamentalCell | (p.2 : Plane) ∈ interior baseCell} :=
  Set.ext (fundamentalCellMap_mem_interiorImage_iff C ε hε)

/-- The same map with its codomain restricted to its literal image. -/
def interiorCellMapToImage (p : InteriorPhaseCell) : interiorImage C ε hε :=
  ⟨interiorCellMap C ε hε p, mem_range_self p⟩

@[simp] theorem interiorCellMapToImage_coe (p : InteriorPhaseCell) :
    (interiorCellMapToImage C ε hε p : QuotientCentralFibre C ε) =
      interiorCellMap C ε hε p := rfl

theorem interiorCellMapToImage_continuous : Continuous (interiorCellMapToImage C ε hε) :=
  (interiorCellMap_continuous C ε hε).subtype_mk _

theorem interiorCellMapToImage_surjective : Function.Surjective (interiorCellMapToImage C ε hε) := by
  rintro ⟨y, p, hp⟩
  exact ⟨p, Subtype.ext hp⟩

theorem interiorCellMapToImage_injective : Function.Injective (interiorCellMapToImage C ε hε) := by
  intro p q hpq
  exact interiorCellMap_injective C ε hε (congrArg Subtype.val hpq)

/-- The literal product interior is precisely the source of the restriction
of the fundamental-cell map to its interior image. -/
def interiorPreimageHomeomorph :
    InteriorPhaseCell ≃ₜ (fundamentalCellMap C ε hε ⁻¹' interiorImage C ε hε) where
  toFun p := ⟨interiorCellInclusion p,
    (fundamentalCellMap_mem_interiorImage_iff C ε hε _).mpr p.2.2⟩
  invFun p := (p.1.1, ⟨(p.1.2 : Plane),
    (fundamentalCellMap_mem_interiorImage_iff C ε hε p.1).mp p.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := interiorCellInclusion_continuous.subtype_mk _
  continuous_invFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _)

@[simp] theorem interiorPreimageHomeomorph_coe (p : InteriorPhaseCell) :
    (interiorPreimageHomeomorph C ε hε p : FundamentalCell) = interiorCellInclusion p := rfl

@[simp] theorem interiorPreimageHomeomorph_symm_fst
    (p : fundamentalCellMap C ε hε ⁻¹' interiorImage C ε hε) :
    ((interiorPreimageHomeomorph C ε hε).symm p).1 = p.1.1 := rfl

@[simp] theorem interiorPreimageHomeomorph_symm_snd_coe
    (p : fundamentalCellMap C ε hε ⁻¹' interiorImage C ε hε) :
    (((interiorPreimageHomeomorph C ε hε).symm p).2 : Plane) = (p.1.2 : Plane) := rfl

variable (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

include hε1 hC hR

/-- Openness is proved in the original central cusp fibre by its genuine
quotient map and the exact saturation statement above. -/
theorem interiorImage_isOpen : IsOpen (interiorImage C ε hε) := by
  apply (fundamentalCellMap_isQuotientMap C ε hε hε1 hC hR).isCoinducing.isOpen_preimage.mp
  rw [fundamentalCellMap_preimage_interiorImage]
  exact isOpen_interior.preimage (continuous_subtype_val.comp continuous_snd)

/-- Properness is for the map to its actual image, not for inclusion of
that open image into the whole central fibre. -/
theorem interiorCellMapToImage_isProperMap : IsProperMap (interiorCellMapToImage C ε hε) := by
  have hf := (fundamentalCellMap_isProperMap C ε hε hε1 hC hR).restrictPreimage
    (interiorImage C ε hε)
  have hg := (interiorPreimageHomeomorph C ε hε).isProperMap
  have hc := hf.comp hg
  have he : (interiorImage C ε hε).restrictPreimage (fundamentalCellMap C ε hε) ∘
      interiorPreimageHomeomorph C ε hε = interiorCellMapToImage C ε hε := by
    funext p
    apply Subtype.ext
    rfl
  rw [he] at hc
  exact hc

theorem interiorCellMapToImage_isClosedMap : IsClosedMap (interiorCellMapToImage C ε hε) :=
  (interiorCellMapToImage_isProperMap C ε hε hε1 hC hR).isClosedMap

/-- The actual interior phase-cell product is homeomorphic to the inherited
open part of the actual central cusp quotient. -/
def interiorCellHomeomorph : InteriorPhaseCell ≃ₜ interiorImage C ε hε :=
  Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective (interiorCellMapToImage C ε hε)
      ⟨interiorCellMapToImage_injective C ε hε, interiorCellMapToImage_surjective C ε hε⟩)
    (interiorCellMapToImage_continuous C ε hε)
    (interiorCellMapToImage_isClosedMap C ε hε hε1 hC hR)

@[simp] theorem interiorCellHomeomorph_apply (p : InteriorPhaseCell) :
    interiorCellHomeomorph C ε hε hε1 hC hR p = interiorCellMapToImage C ε hε p := rfl

@[simp] theorem interiorCellHomeomorph_coe (p : InteriorPhaseCell) :
    (interiorCellHomeomorph C ε hε hε1 hC hR p : QuotientCentralFibre C ε) =
      interiorCellMap C ε hε p := rfl

@[simp] theorem interiorCellHomeomorph_honeycomb (p : InteriorPhaseCell) :
    (interiorCellHomeomorph C ε hε hε1 hC hR p : QuotientCentralFibre C ε) =
      honeycombCollapseMap C ε hε (p.1, (p.2 : Plane)) := rfl

@[simp] theorem interiorCellHomeomorph_symm_map (p : InteriorPhaseCell) :
    (interiorCellHomeomorph C ε hε hε1 hC hR).symm (interiorCellMapToImage C ε hε p) = p :=
  (interiorCellHomeomorph C ε hε hε1 hC hR).symm_apply_apply p

theorem interiorCellMap_isOpenEmbedding : IsOpenEmbedding (interiorCellMap C ε hε) := by
  have h := (interiorImage_isOpen C ε hε hε1 hC hR).isOpenEmbedding_subtypeVal.comp
    (interiorCellHomeomorph C ε hε hε1 hC hR).isOpenEmbedding
  have he : (Subtype.val : interiorImage C ε hε → QuotientCentralFibre C ε) ∘
      interiorCellHomeomorph C ε hε hε1 hC hR = interiorCellMap C ε hε := by
    funext p
    rfl
  rw [he] at h
  exact h

end Wikipedia.HopfProblem.CuspCentralHomology
