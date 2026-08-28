import Wikipedia.HopfProblem.CuspCentralHomologyOpenCoverModel
import Wikipedia.HopfProblem.CuspCentralHomologyRadialInterior
import Wikipedia.HopfProblem.CuspCentralHomologyRadialAnnulus

/-!
# The actual annular overlap and its inclusion into the inner region

The radial open-cover intersection in the original central quotient is
homeomorphic to compact fibre phases times the literal open hexagon annulus.
Radial coordinates identify this with phases, a frontier point, and a radius.
The explicit homotopy equivalences preserve the phase coordinate, so the
overlap inclusion into the inner region becomes the ordinary phase projection.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspHoneycomb CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane

/-- Phases over the literal strict gauge annulus. -/
abbrev OverlapPhaseCell (a : ℝ) := CompactFibreTorus × Radial.Annulus a

/-- The actual annulus embeds in the actual open cell, without changing either coordinate. -/
def annulusCellInclusion (a : ℝ) (p : OverlapPhaseCell a) : InteriorPhaseCell :=
  (p.1, ⟨(p.2 : Plane), (Radial.mem_interior_baseCell_iff _).mpr p.2.2.2⟩)

@[simp] theorem annulusCellInclusion_fst (a : ℝ) (p : OverlapPhaseCell a) :
    (annulusCellInclusion a p).1 = p.1 := rfl

@[simp] theorem annulusCellInclusion_snd_coe (a : ℝ) (p : OverlapPhaseCell a) :
    ((annulusCellInclusion a p).2 : Plane) = (p.2 : Plane) := rfl

theorem annulusCellInclusion_continuous (a : ℝ) : Continuous (annulusCellInclusion a) :=
  continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

theorem annulusCellInclusion_injective (a : ℝ) :
    Function.Injective (annulusCellInclusion a) := by
  intro p q hpq
  apply Prod.ext
  · exact congrArg (fun r : InteriorPhaseCell => r.1) hpq
  · apply Subtype.ext
    exact congrArg (fun r : InteriorPhaseCell => (r.2 : Plane)) hpq

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The literal intersection of the two open subsets of the central quotient. -/
def overlapRegion (a : ℝ) : Set (QuotientCentralFibre C ε) :=
  outerRegion C ε hε a ∩ innerRegion C ε hε

/-- Inclusion of the actual intersection into the actual inner open set. -/
def overlapIntoInner (a : ℝ) :
    C(overlapRegion C ε hε a, innerRegion C ε hε) :=
  ⟨fun q => ⟨(q : QuotientCentralFibre C ε), q.2.2⟩,
    continuous_subtype_val.subtype_mk _⟩

@[simp] theorem overlapIntoInner_coe (a : ℝ) (q : overlapRegion C ε hε a) :
    (overlapIntoInner C ε hε a q : QuotientCentralFibre C ε) =
      (q : QuotientCentralFibre C ε) := rfl

variable (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

include hε1 hC hR in
theorem overlapRegion_isOpen (a : ℝ) : IsOpen (overlapRegion C ε hε a) :=
  (outerRegion_isOpen C ε hε hε1 hC hR a).inter
    (innerRegion_isOpen C ε hε hε1 hC hR)

/-- The original honeycomb map on the strict annulus, with codomain its actual overlap. -/
def overlapCellMap (a : ℝ) (p : OverlapPhaseCell a) : overlapRegion C ε hε a :=
  ⟨(innerRegionHomeomorph C ε hε hε1 hC hR (annulusCellInclusion a p) :
      QuotientCentralFibre C ε), by
    constructor
    · change a < centralRadius C ε hε _
      rw [innerRegionHomeomorph_radius, annulusCellInclusion_snd_coe]
      exact p.2.2.1
    · exact (innerRegionHomeomorph C ε hε hε1 hC hR (annulusCellInclusion a p)).2⟩

@[simp] theorem overlapCellMap_coe (a : ℝ) (p : OverlapPhaseCell a) :
    (overlapCellMap C ε hε hε1 hC hR a p : QuotientCentralFibre C ε) =
      honeycombCollapseMap C ε hε (p.1, (p.2 : Plane)) :=
  innerRegionHomeomorph_honeycomb C ε hε hε1 hC hR (annulusCellInclusion a p)

theorem overlapCellMap_intoInner (a : ℝ) (p : OverlapPhaseCell a) :
    overlapIntoInner C ε hε a (overlapCellMap C ε hε hε1 hC hR a p) =
      innerRegionHomeomorph C ε hε hε1 hC hR (annulusCellInclusion a p) := rfl

theorem overlapCellMap_continuous (a : ℝ) :
    Continuous (overlapCellMap C ε hε hε1 hC hR a) :=
  (continuous_subtype_val.comp
    ((innerRegionHomeomorph C ε hε hε1 hC hR).continuous.comp
      (annulusCellInclusion_continuous a))).subtype_mk _

/-- Recover the unique phase and interior-cell representative of an overlap point. -/
def overlapCellInverse (a : ℝ) (q : overlapRegion C ε hε a) : OverlapPhaseCell a :=
  let p := (innerRegionHomeomorph C ε hε hε1 hC hR).symm
    (overlapIntoInner C ε hε a q)
  (p.1, ⟨(p.2 : Plane), by
    constructor
    · rw [← innerRegionHomeomorph_radius C ε hε hε1 hC hR p]
      dsimp only [p]
      rw [Homeomorph.apply_symm_apply]
      exact q.2.1
    · exact (Radial.mem_interior_baseCell_iff _).mp p.2.2⟩)

theorem overlapCellInverse_interior (a : ℝ) (q : overlapRegion C ε hε a) :
    annulusCellInclusion a (overlapCellInverse C ε hε hε1 hC hR a q) =
      (innerRegionHomeomorph C ε hε hε1 hC hR).symm
        (overlapIntoInner C ε hε a q) := rfl

theorem overlapCellInverse_continuous (a : ℝ) :
    Continuous (overlapCellInverse C ε hε hε1 hC hR a) := by
  have hp := (innerRegionHomeomorph C ε hε hε1 hC hR).symm.continuous.comp
    (overlapIntoInner C ε hε a).continuous
  exact (continuous_fst.comp hp).prodMk
    ((continuous_subtype_val.comp (continuous_snd.comp hp)).subtype_mk _)

/-- The product presentation of the actual overlap is a homeomorphism for its inherited topology. -/
def overlapPhaseHomeomorph (a : ℝ) :
    OverlapPhaseCell a ≃ₜ overlapRegion C ε hε a where
  toFun := overlapCellMap C ε hε hε1 hC hR a
  invFun := overlapCellInverse C ε hε hε1 hC hR a
  left_inv p := by
    apply annulusCellInclusion_injective a
    rw [overlapCellInverse_interior, overlapCellMap_intoInner, Homeomorph.symm_apply_apply]
  right_inv q := by
    apply Subtype.ext
    change (innerRegionHomeomorph C ε hε hε1 hC hR
      (annulusCellInclusion a (overlapCellInverse C ε hε hε1 hC hR a q)) :
        QuotientCentralFibre C ε) = (q : QuotientCentralFibre C ε)
    rw [overlapCellInverse_interior, Homeomorph.apply_symm_apply]
    rfl
  continuous_toFun := overlapCellMap_continuous C ε hε hε1 hC hR a
  continuous_invFun := overlapCellInverse_continuous C ε hε hε1 hC hR a

@[simp] theorem overlapPhaseHomeomorph_coe (a : ℝ) (p : OverlapPhaseCell a) :
    (overlapPhaseHomeomorph C ε hε hε1 hC hR a p : QuotientCentralFibre C ε) =
      honeycombCollapseMap C ε hε (p.1, (p.2 : Plane)) :=
  overlapCellMap_coe C ε hε hε1 hC hR a p

/-- Actual frontier direction and radius coordinates on the overlap. -/
def overlapHomeomorph (a : ℝ) (ha : 0 ≤ a) :
    overlapRegion C ε hε a ≃ₜ CompactFibreTorus × Radial.CellFrontier × Ioo a 1 :=
  (overlapPhaseHomeomorph C ε hε hε1 hC hR a).symm.trans
    ((Homeomorph.refl CompactFibreTorus).prodCongr (Radial.annulusHomeomorph a ha))

@[simp] theorem overlapHomeomorph_fst (a : ℝ) (ha : 0 ≤ a)
    (q : overlapRegion C ε hε a) :
    (overlapHomeomorph C ε hε hε1 hC hR a ha q).1 =
      ((innerRegionHomeomorph C ε hε hε1 hC hR).symm
        (overlapIntoInner C ε hε a q)).1 := rfl

theorem overlapHomeomorph_radius (a : ℝ) (ha : 0 ≤ a)
    (q : overlapRegion C ε hε a) :
    ((overlapHomeomorph C ε hε hε1 hC hR a ha q).2.2 : ℝ) =
      centralRadius C ε hε (q : QuotientCentralFibre C ε) := by
  change Radial.cellGauge
    (((innerRegionHomeomorph C ε hε hε1 hC hR).symm
      (overlapIntoInner C ε hε a q)).2 : Plane) = _
  simpa only [Homeomorph.apply_symm_apply, overlapIntoInner_coe] using
    (innerRegionHomeomorph_radius C ε hε hε1 hC hR
      ((innerRegionHomeomorph C ε hε hε1 hC hR).symm
        (overlapIntoInner C ε hε a q))).symm

theorem overlapHomeomorph_symm_coe (a : ℝ) (ha : 0 ≤ a)
    (p : CompactFibreTorus × Radial.CellFrontier × Ioo a 1) :
    ((overlapHomeomorph C ε hε hε1 hC hR a ha).symm p : QuotientCentralFibre C ε) =
      honeycombCollapseMap C ε hε (p.1, (p.2.2 : ℝ) • (p.2.1 : Plane)) := by
  change (overlapPhaseHomeomorph C ε hε hε1 hC hR a
    (p.1, (Radial.annulusHomeomorph a ha).symm p.2) : QuotientCentralFibre C ε) = _
  rw [overlapPhaseHomeomorph_coe]
  rfl

/-- The explicit inner-region homotopy equivalence is projection to the original compact phases. -/
def innerRegionHomotopyEquiv : innerRegion C ε hε ≃ₕ CompactFibreTorus :=
  (innerRegionHomeomorph C ε hε hε1 hC hR).symm.toHomotopyEquiv.trans
    (Radial.interiorCellProductHomotopyEquiv CompactFibreTorus)

@[simp] theorem innerRegionHomotopyEquiv_apply (q : innerRegion C ε hε) :
    innerRegionHomotopyEquiv C ε hε hε1 hC hR q =
      ((innerRegionHomeomorph C ε hε hε1 hC hR).symm q).1 := rfl

@[simp] theorem innerRegionHomotopyEquiv_symm_apply (φ : CompactFibreTorus) :
    (innerRegionHomotopyEquiv C ε hε hε1 hC hR).symm φ =
      innerRegionHomeomorph C ε hε hε1 hC hR (φ, Radial.interiorCellZero) := rfl

/-- The actual overlap has the homotopy type of phases times the ordinary circle. -/
def overlapCircleHomotopyEquiv (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    overlapRegion C ε hε a ≃ₕ CompactFibreTorus × Circle :=
  (overlapPhaseHomeomorph C ε hε hε1 hC hR a).symm.toHomotopyEquiv.trans
    (Radial.phaseAnnulusHomotopyEquiv CompactFibreTorus a ha ha1)

/-- Under the two explicitly constructed homotopy equivalences, the actual inclusion
into the inner open set is exactly the compact-phase projection. -/
theorem overlapIntoInner_phase (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (q : overlapRegion C ε hε a) :
    innerRegionHomotopyEquiv C ε hε hε1 hC hR (overlapIntoInner C ε hε a q) =
      (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1 q).1 := rfl

theorem overlapIntoInner_phase_map (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (innerRegionHomotopyEquiv C ε hε hε1 hC hR).toFun.comp
        (overlapIntoInner C ε hε a) =
      (ContinuousMap.fst : C(CompactFibreTorus × Circle, CompactFibreTorus)).comp
        (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1).toFun := by
  ext q
  rfl

end Wikipedia.HopfProblem.CuspCentralHomology
