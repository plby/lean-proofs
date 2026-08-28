import Wikipedia.HopfProblem.CuspCentralHomologySpecializationCover
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationCoverShear
import Wikipedia.HopfProblem.CuspCentralHomologyBaseCoverMayerVietoris

/-!
# The actual specialization on the open-cover overlap

In the literal annulus coordinates, specialization is multiplication of
the compact phases by the frozen phase character.  This gives an actual
homeomorphism of the two inherited overlap subspaces.  The previously
constructed phase isotopy shows that it induces the identity under their
same phase-and-circle homology coordinates.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationCover

open ToricSpace CuspRetraction CuspHoneycomb CuspHoneycombTiling SpecializationModel
open SingularMayerVietoris PeriodTorusHigherHomology

local notation "Plane" => CuspHoneycombTiling.Plane

/-- The literal set defining the existing strict-annulus subtype. -/
abbrev annulusSet (a : ℝ) : Set Plane :=
  {y | a < Radial.cellGauge y ∧ Radial.cellGauge y < 1}

/-- The existing source overlap is exactly phases over the literal annulus. -/
def sourceOverlapPhaseHomeomorph (a : ℝ) :
    BaseCover.phaseOverlapRegion a ≃ₜ OverlapPhaseCell a :=
  (BaseCover.phaseOverlapRegionHomeomorph a).trans
    ((Homeomorph.refl CompactFibreTorus).prodCongr (BaseCover.annulusOverlapHomeomorph a).symm)

@[simp] theorem sourceOverlapPhaseHomeomorph_symm_coe (a : ℝ) (p : OverlapPhaseCell a) :
    ((sourceOverlapPhaseHomeomorph a).symm p : BaseCover.PhaseBase) =
      (p.1, BaseCover.basePoint (p.2 : Plane)) := rfl

theorem sourceOverlapCircle_factor (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (BaseCover.phaseOverlapCircleHomotopyEquiv a ha ha1).toFun =
      (Radial.phaseAnnulusHomotopyEquiv CompactFibreTorus a ha ha1).toFun.comp
        (sourceOverlapPhaseHomeomorph a : C(BaseCover.phaseOverlapRegion a, OverlapPhaseCell a)) :=
  rfl

theorem phaseCellShear_homologyMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (s : Set Plane) (n : ℕ) :
    singularHomologyMap
        (phaseCellShear C₀ s : C(CompactFibreTorus × s, CompactFibreTorus × s)) n =
      LinearMap.id := by
  have h := homotopy_homologyMap (phaseCellShearHomotopy C₀ s) n
  rw [singularHomologyMap_id] at h
  exact h.symm

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

/-- The literal specialization overlap map is a homeomorphism: the two
original annulus charts differ only by the displayed phase shear. -/
def collapseOverlapHomeomorph (a : ℝ) :
    BaseCover.phaseOverlapRegion a ≃ₜ overlapRegion C ε hε a :=
  (sourceOverlapPhaseHomeomorph a).trans
    ((phaseCellShear (C 0) (annulusSet a)).trans
      (overlapPhaseHomeomorph C ε hε hε1 hC hR a))

theorem collapseOverlapHomeomorph_apply (a : ℝ) (q : BaseCover.phaseOverlapRegion a) :
    collapseOverlapHomeomorph C ε hε hε1 hC hR a q = overlapMap C ε hε a q := by
  obtain ⟨p, rfl⟩ := (sourceOverlapPhaseHomeomorph a).symm.surjective q
  apply Subtype.ext
  rw [overlapMap_coe, sourceOverlapPhaseHomeomorph_symm_coe, productCollapse_basePoint]
  change (overlapPhaseHomeomorph C ε hε hε1 hC hR a
    (phaseCellShear (C 0) (annulusSet a)
      (sourceOverlapPhaseHomeomorph a ((sourceOverlapPhaseHomeomorph a).symm p))) :
        QuotientCentralFibre C ε) = _
  rw [Homeomorph.apply_symm_apply, overlapPhaseHomeomorph_coe]
  rfl

theorem collapseOverlapHomeomorph_toContinuousMap (a : ℝ) :
    (collapseOverlapHomeomorph C ε hε hε1 hC hR a :
      C(BaseCover.phaseOverlapRegion a, overlapRegion C ε hε a)) = overlapMap C ε hε a :=
  ContinuousMap.ext (collapseOverlapHomeomorph_apply C ε hε hε1 hC hR a)

/-- Exact original annulus coordinates of the actual restricted map. -/
theorem overlapMap_phase_coordinates (a : ℝ) (q : BaseCover.phaseOverlapRegion a) :
    (overlapPhaseHomeomorph C ε hε hε1 hC hR a).symm (overlapMap C ε hε a q) =
      phaseCellShear (C 0) (annulusSet a) (sourceOverlapPhaseHomeomorph a q) := by
  apply (overlapPhaseHomeomorph C ε hε hε1 hC hR a).injective
  rw [Homeomorph.apply_symm_apply]
  exact (collapseOverlapHomeomorph_apply C ε hε hε1 hC hR a q).symm

theorem targetOverlapCircle_factor (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1).toFun.comp
        (overlapMap C ε hε a) =
      (Radial.phaseAnnulusHomotopyEquiv CompactFibreTorus a ha ha1).toFun.comp
        ((phaseCellShear (C 0) (annulusSet a) :
          C(CompactFibreTorus × annulusSet a, CompactFibreTorus × annulusSet a)).comp
          (sourceOverlapPhaseHomeomorph a :
            C(BaseCover.phaseOverlapRegion a, OverlapPhaseCell a))) := by
  apply ContinuousMap.ext
  intro q
  change Radial.phaseAnnulusHomotopyEquiv CompactFibreTorus a ha ha1
    ((overlapPhaseHomeomorph C ε hε hε1 hC hR a).symm (overlapMap C ε hε a q)) = _
  rw [overlapMap_phase_coordinates]
  rfl

/-- The homology square uses the actual source and target overlap
equivalences and the actual restricted specialization map. -/
theorem overlapMap_homology_intertwining (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    (homotopyEquivHomologyEquiv
      (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1) n).toLinearMap.comp
        (singularHomologyMap (overlapMap C ε hε a) n) =
      (BaseCover.phaseOverlapHomologyEquiv a ha ha1 n).toLinearMap := by
  change (singularHomologyMap
    (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1).toFun n).comp
      (singularHomologyMap (overlapMap C ε hε a) n) =
    singularHomologyMap (BaseCover.phaseOverlapCircleHomotopyEquiv a ha ha1).toFun n
  rw [← singularHomologyMap_comp, targetOverlapCircle_factor,
    singularHomologyMap_comp, singularHomologyMap_comp, phaseCellShear_homologyMap,
    LinearMap.id_comp, sourceOverlapCircle_factor, singularHomologyMap_comp]

theorem overlapMap_homology_coordinates (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (n : ℕ) (x : SingularHomology (BaseCover.phaseOverlapRegion a) n) :
    homotopyEquivHomologyEquiv
        (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1) n
        (singularHomologyMap (overlapMap C ε hε a) n x) =
      BaseCover.phaseOverlapHomologyEquiv a ha ha1 n x :=
  LinearMap.congr_fun (overlapMap_homology_intertwining C ε hε hε1 hC hR a ha ha1 n) x

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationCover
