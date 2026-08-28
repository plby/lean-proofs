import Wikipedia.HopfProblem.CuspCentralHomologyOpenCover
import Wikipedia.HopfProblem.CuspCentralHomologyRadialCollar
import Mathlib.Topology.CompactOpen

/-!
# The actual outer-region deformation onto the central boundary

Compact phases over the open-inner-edge radial collar present the literal
outer region of the central cusp fibre. The phase-preserving radial
deformation respects the exact fibres of that presentation, since all
nontrivial identifications occur on the frontier, which is fixed.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspCollapse CuspHoneycomb CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane

/-- The literal product of compact phases with the radial outer collar. -/
abbrev CollarPhaseCell (a : ℝ) := CompactFibreTorus × Radial.OpenCollar a

def collarCellInclusion (a : ℝ) (p : CollarPhaseCell a) : FundamentalCell :=
  (p.1, ⟨(p.2 : Plane), (Radial.mem_baseCell_iff _).mpr p.2.2.2⟩)

@[simp] theorem collarCellInclusion_fst (a : ℝ) (p : CollarPhaseCell a) :
    (collarCellInclusion a p).1 = p.1 := rfl

@[simp] theorem collarCellInclusion_snd_coe (a : ℝ) (p : CollarPhaseCell a) :
    ((collarCellInclusion a p).2 : Plane) = (p.2 : Plane) := rfl

theorem collarCellInclusion_continuous (a : ℝ) : Continuous (collarCellInclusion a) :=
  continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

theorem collarCellInclusion_injective (a : ℝ) : Function.Injective (collarCellInclusion a) := by
  intro p q hpq
  apply Prod.ext
  · exact congrArg (fun r : FundamentalCell => r.1) hpq
  · apply Subtype.ext
    exact congrArg (fun r : FundamentalCell => (r.2 : Plane)) hpq

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (a : ℝ)

theorem fundamentalCellMap_mem_outerRegion_iff (p : FundamentalCell) :
    fundamentalCellMap C ε hε p ∈ outerRegion C ε hε a ↔
      a < Radial.cellGauge (p.2 : Plane) := by
  change a < centralRadius C ε hε (fundamentalCellMap C ε hε p) ↔ _
  rw [centralRadius_fundamentalCellMap]

/-- The collar presentation takes values in the actual outer region, with
its original subspace topology. -/
def collarCellMap (p : CollarPhaseCell a) : outerRegion C ε hε a :=
  ⟨fundamentalCellMap C ε hε (collarCellInclusion a p),
    (fundamentalCellMap_mem_outerRegion_iff C ε hε a _).mpr p.2.2.1⟩

@[simp] theorem collarCellMap_coe (p : CollarPhaseCell a) :
    (collarCellMap C ε hε a p : QuotientCentralFibre C ε) =
      honeycombCollapseMap C ε hε (p.1, (p.2 : Plane)) := rfl

theorem collarCellMap_eq_fundamentalCellMap (p : CollarPhaseCell a) :
    (collarCellMap C ε hε a p : QuotientCentralFibre C ε) =
      fundamentalCellMap C ε hε (collarCellInclusion a p) := rfl

@[simp] theorem centralRadius_collarCellMap (p : CollarPhaseCell a) :
    centralRadius C ε hε (collarCellMap C ε hε a p) = Radial.cellGauge (p.2 : Plane) :=
  centralRadius_fundamentalCellMap C ε hε (collarCellInclusion a p)

theorem collarCellMap_continuous : Continuous (collarCellMap C ε hε a) :=
  ((fundamentalCellMap_continuous C ε hε).comp (collarCellInclusion_continuous a)).subtype_mk _

theorem collarCellMap_surjective : Function.Surjective (collarCellMap C ε hε a) := by
  rintro ⟨q, hq⟩
  obtain ⟨p, hp⟩ := fundamentalCellMap_surjective C ε hε q
  have hg : a < Radial.cellGauge (p.2 : Plane) := by
    apply (fundamentalCellMap_mem_outerRegion_iff C ε hε a p).mp
    rwa [hp]
  refine ⟨(p.1, ⟨(p.2 : Plane), hg, (Radial.mem_baseCell_iff _).mp p.2.2⟩), ?_⟩
  apply Subtype.ext
  exact hp

/-- The source product is precisely the preimage of the actual outer
region under the proper fundamental-cell presentation. -/
def collarPreimageHomeomorph :
    CollarPhaseCell a ≃ₜ (fundamentalCellMap C ε hε ⁻¹' outerRegion C ε hε a) where
  toFun p := ⟨collarCellInclusion a p,
    (fundamentalCellMap_mem_outerRegion_iff C ε hε a _).mpr p.2.2.1⟩
  invFun p := (p.1.1, ⟨(p.1.2 : Plane),
    (fundamentalCellMap_mem_outerRegion_iff C ε hε a p.1).mp p.2,
    (Radial.mem_baseCell_iff _).mp p.1.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (collarCellInclusion_continuous a).subtype_mk _
  continuous_invFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _)

@[simp] theorem collarPreimageHomeomorph_coe (p : CollarPhaseCell a) :
    (collarPreimageHomeomorph C ε hε a p : FundamentalCell) = collarCellInclusion a p := rfl

section Topology

variable (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

include hε1 hC hR

theorem collarCellMap_isProperMap : IsProperMap (collarCellMap C ε hε a) := by
  have hf := (fundamentalCellMap_isProperMap C ε hε hε1 hC hR).restrictPreimage
    (outerRegion C ε hε a)
  have hc := hf.comp (collarPreimageHomeomorph C ε hε a).isProperMap
  have he : (outerRegion C ε hε a).restrictPreimage (fundamentalCellMap C ε hε) ∘
      collarPreimageHomeomorph C ε hε a = collarCellMap C ε hε a := by
    funext p
    apply Subtype.ext
    rfl
  rw [he] at hc
  exact hc

theorem collarCellMap_isClosedMap : IsClosedMap (collarCellMap C ε hε a) :=
  (collarCellMap_isProperMap C ε hε a hε1 hC hR).isClosedMap

theorem collarCellMap_isQuotientMap : IsQuotientMap (collarCellMap C ε hε a) :=
  (collarCellMap_isClosedMap C ε hε a hε1 hC hR).isQuotientMap
    (collarCellMap_continuous C ε hε a) (collarCellMap_surjective C ε hε a)

end Topology

/-- The outward radial deformation leaves the compact phase unchanged. -/
def collarCellHomotopy (ha : 0 ≤ a) (ha1 : a < 1) :
    C(unitInterval × CollarPhaseCell a, CollarPhaseCell a) where
  toFun p := (p.2.1, Radial.outwardOpenCollarHomotopy a ha ha1 (p.1, p.2.2))
  continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
    ((Radial.outwardOpenCollarHomotopy a ha ha1).continuous.comp
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))

@[simp] theorem collarCellHomotopy_fst (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (p : CollarPhaseCell a) :
    (collarCellHomotopy a ha ha1 (s, p)).1 = p.1 := rfl

@[simp] theorem collarCellHomotopy_zero (ha : 0 ≤ a) (ha1 : a < 1)
    (p : CollarPhaseCell a) : collarCellHomotopy a ha ha1 (0, p) = p := by
  apply Prod.ext
  · rfl
  · exact (Radial.outwardOpenCollarHomotopy a ha ha1).apply_zero p.2

theorem collarCellHomotopy_fixed (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (p : CollarPhaseCell a) (hp : (p.2 : Plane) ∈ frontier baseCell) :
    collarCellHomotopy a ha ha1 (s, p) = p := by
  apply Prod.ext
  · rfl
  · exact Radial.outwardOpenCollarHomotopy_fixed a ha ha1 s p.2 hp

/-- All original cusp identifications are preserved by each radial stage.
Nontrivial fibres consist of frontier points, which are fixed. -/
theorem collarCellHomotopy_compatible (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (p q : CollarPhaseCell a)
    (h : collarCellMap C ε hε a p = collarCellMap C ε hε a q) :
    collarCellMap C ε hε a (collarCellHomotopy a ha ha1 (s, p)) =
      collarCellMap C ε hε a (collarCellHomotopy a ha ha1 (s, q)) := by
  have he : fundamentalCellMap C ε hε (collarCellInclusion a p) =
      fundamentalCellMap C ε hε (collarCellInclusion a q) := congrArg Subtype.val h
  rcases fundamentalCellMap_eq_or_frontier C ε hε
    (collarCellInclusion a p) (collarCellInclusion a q) he with hpq | ⟨hp, hq⟩
  · rw [collarCellInclusion_injective a hpq]
  · rw [collarCellHomotopy_fixed a ha ha1 s p hp, collarCellHomotopy_fixed a ha ha1 s q hq]
    exact h

/-- The literal boundary inclusion into the actual outer open region. -/
def outerRegionBoundaryInclusion (ha1 : a < 1) :
    C(centralBoundary C ε hε, outerRegion C ε hε a) where
  toFun x := ⟨x, centralBoundary_subset_outerRegion C ε hε a ha1 x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp] theorem outerRegionBoundaryInclusion_coe (ha1 : a < 1)
    (x : centralBoundary C ε hε) :
    (outerRegionBoundaryInclusion C ε hε a ha1 x : QuotientCentralFibre C ε) = x := rfl

variable (ha : 0 ≤ a) (ha1 : a < 1)

/-- The actual radial deformation, defined by any collar representative.
Its value is independent of the representative by fibre compatibility. -/
def outerRegionDeformation (s : unitInterval) (x : outerRegion C ε hε a) :
    outerRegion C ε hε a :=
  CuspHoneycombHexagon.CommonFibres.descend (collarCellMap C ε hε a)
    (fun p => collarCellMap C ε hε a (collarCellHomotopy a ha ha1 (s, p)))
    (collarCellMap_surjective C ε hε a) x

@[simp] theorem outerRegionDeformation_collarCellMap
    (s : unitInterval) (p : CollarPhaseCell a) :
    outerRegionDeformation C ε hε a ha ha1 s (collarCellMap C ε hε a p) =
      collarCellMap C ε hε a (collarCellHomotopy a ha ha1 (s, p)) :=
  CuspHoneycombHexagon.CommonFibres.descend_apply (collarCellMap C ε hε a)
    (fun p => collarCellMap C ε hε a (collarCellHomotopy a ha ha1 (s, p)))
    (collarCellMap_surjective C ε hε a)
    (collarCellHomotopy_compatible C ε hε a ha ha1 s) p

/-- The descended deformation uses the explicit radial formula and does
not alter the compact phase of any collar representative. -/
theorem outerRegionDeformation_collarCellMap_coe
    (s : unitInterval) (p : CollarPhaseCell a) :
    (outerRegionDeformation C ε hε a ha ha1 s (collarCellMap C ε hε a p) :
        QuotientCentralFibre C ε) =
      honeycombCollapseMap C ε hε
        (p.1, ((1 - (s : ℝ)) + (s : ℝ) / Radial.cellGauge p.2) • (p.2 : Plane)) := by
  rw [outerRegionDeformation_collarCellMap, collarCellMap_coe]
  change honeycombCollapseMap C ε hε
    (p.1, (Radial.outwardOpenCollarHomotopy a ha ha1 (s, p.2) : Plane)) = _
  rw [Radial.outwardOpenCollarHomotopy_coe]

@[simp] theorem outerRegionDeformation_zero (x : outerRegion C ε hε a) :
    outerRegionDeformation C ε hε a ha ha1 0 x = x := by
  obtain ⟨p, rfl⟩ := collarCellMap_surjective C ε hε a x
  rw [outerRegionDeformation_collarCellMap, collarCellHomotopy_zero]

/-- The descended radius follows the same affine interpolation to one. -/
theorem outerRegionDeformation_radius (s : unitInterval) (x : outerRegion C ε hε a) :
    centralRadius C ε hε (outerRegionDeformation C ε hε a ha ha1 s x) =
      (1 - (s : ℝ)) * centralRadius C ε hε x + (s : ℝ) := by
  obtain ⟨p, rfl⟩ := collarCellMap_surjective C ε hε a x
  rw [outerRegionDeformation_collarCellMap, centralRadius_collarCellMap,
    centralRadius_collarCellMap]
  exact Radial.outwardOpenCollarHomotopy_gauge a ha ha1 s p.2

theorem outerRegionDeformation_one_mem_boundary (x : outerRegion C ε hε a) :
    (outerRegionDeformation C ε hε a ha ha1 1 x : QuotientCentralFibre C ε) ∈
      centralBoundary C ε hε := by
  change centralRadius C ε hε (outerRegionDeformation C ε hε a ha ha1 1 x) = 1
  rw [outerRegionDeformation_radius]
  simp

/-- Every point of the actual central boundary is fixed at every time. -/
theorem outerRegionDeformation_fixed (s : unitInterval) (x : outerRegion C ε hε a)
    (hx : (x : QuotientCentralFibre C ε) ∈ centralBoundary C ε hε) :
    outerRegionDeformation C ε hε a ha ha1 s x = x := by
  obtain ⟨p, rfl⟩ := collarCellMap_surjective C ε hε a x
  have hp : (p.2 : Plane) ∈ frontier baseCell := by
    apply (Radial.mem_frontier_baseCell_iff _).mpr
    change centralRadius C ε hε (collarCellMap C ε hε a p) = 1 at hx
    rwa [centralRadius_collarCellMap] at hx
  rw [outerRegionDeformation_collarCellMap, collarCellHomotopy_fixed a ha ha1 s p hp]

section DeformationTopology

variable (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

include hε1 hC hR

/-- Joint continuity is descended through the actual collar quotient.
The homotopy interval is locally compact, so its product preserves the
quotient property. -/
theorem outerRegionDeformation_continuous :
    Continuous (fun p : unitInterval × outerRegion C ε hε a =>
      outerRegionDeformation C ε hε a ha ha1 p.1 p.2) := by
  apply (collarCellMap_isQuotientMap C ε hε a hε1 hC hR).continuous_lift_prod_right
  have hc := (collarCellMap_continuous C ε hε a).comp
    (collarCellHomotopy a ha ha1).continuous
  simpa only [outerRegionDeformation_collarCellMap, Function.comp_def, Prod.eta] using hc

/-- Time one, with its codomain restricted to the original central boundary. -/
def outerRegionRetraction : C(outerRegion C ε hε a, centralBoundary C ε hε) where
  toFun x := ⟨outerRegionDeformation C ε hε a ha ha1 1 x,
    outerRegionDeformation_one_mem_boundary C ε hε a ha ha1 x⟩
  continuous_toFun :=
    (continuous_subtype_val.comp
      ((outerRegionDeformation_continuous C ε hε a ha ha1 hε1 hC hR).comp
        (continuous_const.prodMk continuous_id))).subtype_mk _

@[simp] theorem outerRegionRetraction_coe (x : outerRegion C ε hε a) :
    (outerRegionRetraction C ε hε a ha ha1 hε1 hC hR x : QuotientCentralFibre C ε) =
      outerRegionDeformation C ε hε a ha ha1 1 x := rfl

/-- On collar representatives the actual retraction is precisely division
of the planar coordinate by its gauge, with the compact phase unchanged. -/
theorem outerRegionRetraction_collarCellMap (p : CollarPhaseCell a) :
    (outerRegionRetraction C ε hε a ha ha1 hε1 hC hR
      (collarCellMap C ε hε a p) : QuotientCentralFibre C ε) =
        honeycombCollapseMap C ε hε
          (p.1, (Radial.cellGauge p.2)⁻¹ • (p.2 : Plane)) := by
  rw [outerRegionRetraction_coe, outerRegionDeformation_collarCellMap_coe]
  simp

@[simp] theorem outerRegionRetraction_comp_inclusion :
    (outerRegionRetraction C ε hε a ha ha1 hε1 hC hR).comp
      (outerRegionBoundaryInclusion C ε hε a ha1) =
        ContinuousMap.id (centralBoundary C ε hε) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (outerRegionDeformation C ε hε a ha ha1 1
    (outerRegionBoundaryInclusion C ε hε a ha1 x) : QuotientCentralFibre C ε) = x
  exact congrArg Subtype.val (outerRegionDeformation_fixed C ε hε a ha ha1 1
    (outerRegionBoundaryInclusion C ε hε a ha1 x) x.2)

/-- The genuine outer-region strong deformation retraction, relative to
the actual central boundary with its original subspace topology. -/
def outerRegionHomotopyRel :
    (ContinuousMap.id (outerRegion C ε hε a)).HomotopyRel
      ((outerRegionBoundaryInclusion C ε hε a ha1).comp
        (outerRegionRetraction C ε hε a ha ha1 hε1 hC hR))
      {x : outerRegion C ε hε a | (x : QuotientCentralFibre C ε) ∈ centralBoundary C ε hε} where
  toFun p := outerRegionDeformation C ε hε a ha ha1 p.1 p.2
  continuous_toFun := outerRegionDeformation_continuous C ε hε a ha ha1 hε1 hC hR
  map_zero_left := outerRegionDeformation_zero C ε hε a ha ha1
  map_one_left _ := rfl
  prop' := outerRegionDeformation_fixed C ε hε a ha ha1

/-- The actual outer region has the homotopy type of its literal central boundary. -/
def outerRegionBoundaryHomotopyEquiv :
    outerRegion C ε hε a ≃ₕ centralBoundary C ε hε where
  toFun := outerRegionRetraction C ε hε a ha ha1 hε1 hC hR
  invFun := outerRegionBoundaryInclusion C ε hε a ha1
  left_inv := ⟨(outerRegionHomotopyRel C ε hε a ha ha1 hε1 hC hR).toHomotopy.symm⟩
  right_inv := by
    refine ⟨?_⟩
    rw [outerRegionRetraction_comp_inclusion]
    exact ContinuousMap.Homotopy.refl _

@[simp] theorem outerRegionHomotopyRel_apply
    (s : unitInterval) (x : outerRegion C ε hε a) :
    outerRegionHomotopyRel C ε hε a ha ha1 hε1 hC hR (s, x) =
      outerRegionDeformation C ε hε a ha ha1 s x := rfl

@[simp] theorem outerRegionBoundaryHomotopyEquiv_apply (x : outerRegion C ε hε a) :
    outerRegionBoundaryHomotopyEquiv C ε hε a ha ha1 hε1 hC hR x =
      outerRegionRetraction C ε hε a ha ha1 hε1 hC hR x := rfl

@[simp] theorem outerRegionBoundaryHomotopyEquiv_symm_apply
    (x : centralBoundary C ε hε) :
    (outerRegionBoundaryHomotopyEquiv C ε hε a ha ha1 hε1 hC hR).symm x =
      outerRegionBoundaryInclusion C ε hε a ha1 x := rfl

end DeformationTopology

end Wikipedia.HopfProblem.CuspCentralHomology
