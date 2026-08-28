import Wikipedia.HopfProblem.CuspCentralHomologyOpenCover
import Wikipedia.HopfProblem.CuspCentralHomologyOpenCoverInterior

/-!
# The genuine product model of the inner open region

The strict radial sublevel is exactly the image of the original compact
phases over the open fundamental hexagon. The proper restricted map
supplies a homeomorphism with that product, for the inherited topology of
the original central quotient. Its radius is the displayed hexagon gauge.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspHoneycomb CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

theorem innerRegion_eq_interiorImage : innerRegion C ε hε = interiorImage C ε hε := by
  ext q
  obtain ⟨p, rfl⟩ := fundamentalCellMap_surjective C ε hε q
  exact (fundamentalCellMap_mem_innerRegion_iff C ε hε p).trans
    (fundamentalCellMap_mem_interiorImage_iff C ε hε p).symm

theorem innerRegion_eq_image :
    innerRegion C ε hε = honeycombCollapseMap C ε hε ''
      ((univ : Set CompactFibreTorus) ×ˢ interior baseCell) := by
  rw [innerRegion_eq_interiorImage]
  ext q
  constructor
  · rintro ⟨⟨φ, x⟩, rfl⟩
    exact ⟨(φ, (x : Plane)), ⟨mem_univ _, x.2⟩, rfl⟩
  · rintro ⟨⟨φ, x⟩, ⟨_, hx⟩, rfl⟩
    exact ⟨(φ, ⟨x, hx⟩), rfl⟩

variable (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

/-- The actual inner open set is compact phases times the literal open
dual hexagon, with both original subspace topologies. -/
def innerRegionHomeomorph : InteriorPhaseCell ≃ₜ innerRegion C ε hε :=
  (interiorCellHomeomorph C ε hε hε1 hC hR).trans
    (Homeomorph.setCongr (innerRegion_eq_interiorImage C ε hε).symm)

@[simp] theorem innerRegionHomeomorph_coe (p : InteriorPhaseCell) :
    (innerRegionHomeomorph C ε hε hε1 hC hR p : QuotientCentralFibre C ε) =
      interiorCellMap C ε hε p :=
  interiorCellHomeomorph_coe C ε hε hε1 hC hR p

@[simp] theorem innerRegionHomeomorph_honeycomb (p : InteriorPhaseCell) :
    (innerRegionHomeomorph C ε hε hε1 hC hR p : QuotientCentralFibre C ε) =
      honeycombCollapseMap C ε hε (p.1, (p.2 : Plane)) := by
  rw [innerRegionHomeomorph_coe, interiorCellMap_apply]

theorem innerRegionHomeomorph_radius (p : InteriorPhaseCell) :
    centralRadius C ε hε
      (innerRegionHomeomorph C ε hε hε1 hC hR p : QuotientCentralFibre C ε) =
      Radial.cellGauge (p.2 : Plane) := by
  rw [innerRegionHomeomorph_coe, interiorCellMap_eq_fundamentalCellMap,
    centralRadius_fundamentalCellMap, interiorCellInclusion_snd_coe]

end Wikipedia.HopfProblem.CuspCentralHomology
