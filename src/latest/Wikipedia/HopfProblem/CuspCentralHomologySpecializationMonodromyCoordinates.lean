import Wikipedia.HopfProblem.CuspCentralHomologySpecializationMonodromyMap
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelShear
import Wikipedia.HopfProblem.CuspCentralHomologyPhaseTori
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMatrixMaps

/-!
# The actual source shear in the original four-period marking

The product source is ordered with its two base periods first and its two
compact phase periods last.  In this original source marking the literal
descended phase shear is conjugate to the actual four-circle torus map
of `M₀`.  Both maps, and both topologies, are the previously constructed
ones; no monodromy action is supplied as an assumption.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap Matrix

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspHoneycomb PeriodTorusHigherHomology

local notation "Plane" => CuspHoneycombTiling.Plane

/-- Original source order: the two marked base periods precede the two
integer phase periods. -/
def sourceProductCoordinateHomeomorph :
    (CompactFibreTorus × ProductTorus 2) ≃ₜ ProductTorus 4 :=
  ((Homeomorph.prodComm CompactFibreTorus (ProductTorus 2)).trans
    ((Homeomorph.refl (ProductTorus 2)).prodCongr compactFibreTorusHomeomorph)).trans
      (Fin.appendHomeomorph 2 2)

@[simp] theorem sourceProductCoordinateHomeomorph_apply
    (p : CompactFibreTorus × ProductTorus 2) :
    sourceProductCoordinateHomeomorph p =
      ![p.2 0, p.2 1, compactFibreTorusHomeomorph p.1 0,
        compactFibreTorusHomeomorph p.1 1] := by
  funext i
  fin_cases i <;> rfl

/-- The genuine source quotient in the original source period order
`(β₀, β₁, α₀, α₁)`. -/
def sourceCoordinateTorusHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    SourceModel C₀ ≃ₜ ProductTorus 4 :=
  (sourceProductHomeomorph C₀).trans sourceProductCoordinateHomeomorph

@[simp] theorem sourceCoordinateTorusHomeomorph_projection
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (p : PhasePlane) :
    sourceCoordinateTorusHomeomorph C₀ (sourceProjection C₀ p) =
      ![((-p.2 1 : ℝ) : AddCircle (1 : ℝ)), (p.2 0 : AddCircle (1 : ℝ)),
        compactFibreTorusHomeomorph (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹) 0,
        compactFibreTorusHomeomorph (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹) 1] := by
  rw [sourceCoordinateTorusHomeomorph, Homeomorph.trans_apply,
    sourceProductHomeomorph_projection, sourceProductCoordinateHomeomorph_apply]
  simp [realCuspVector]

theorem compactFibreTorusHomeomorph_planarPhase (y : Plane) :
    compactFibreTorusHomeomorph (planarPhase y) = coordinateProjection 2 y :=
  compactFibreTorusHomeomorph_exp y

/-- The literal matrix map on the four additive circles. -/
theorem sourceTorusMatrix_M₀_apply (x : ProductTorus 4) :
    torusMatrixMap M₀ x = ![x 0, x 1, x 1 + x 2, -x 0 + x 3] := by
  funext i
  fin_cases i <;> simp [torusMatrixMap_apply, M₀, Fin.sum_univ_four]

/-- The actual source shear is precisely the positive `M₀` map under
the original period marking, rather than its inverse. -/
theorem sourceCoordinateTorusHomeomorph_shear
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (x : SourceModel C₀) :
    sourceCoordinateTorusHomeomorph C₀ (sourceShear C₀ x) =
      torusMatrixMap M₀ (sourceCoordinateTorusHomeomorph C₀ x) := by
  obtain ⟨p, rfl⟩ := sourceProjection_surjective C₀ x
  rw [sourceShear_projection, sourceCoordinateTorusHomeomorph_projection,
    sourceCoordinateTorusHomeomorph_projection, sourceTorusMatrix_M₀_apply]
  have hp : (p.1 * planarPhase p.2) * (sourcePhaseCharacter C₀ p.2)⁻¹ =
      (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹) * planarPhase p.2 := by ac_rfl
  simp only [phasePlaneShear, hp, compactFibreTorusHomeomorph_mul,
    compactFibreTorusHomeomorph_planarPhase]
  funext i
  fin_cases i <;>
    simp [coordinateProjection_apply, QuotientAddGroup.mk_neg, add_comm]

/-- Bundled naturality of the original source coordinate map. -/
theorem sourceCoordinateTorusHomeomorph_shear_comp
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    (sourceCoordinateTorusHomeomorph C₀ : C(SourceModel C₀, ProductTorus 4)).comp
        (sourceShear C₀) =
      (torusMatrixMap M₀).comp
        (sourceCoordinateTorusHomeomorph C₀ : C(SourceModel C₀, ProductTorus 4)) := by
  apply ContinuousMap.ext
  exact sourceCoordinateTorusHomeomorph_shear C₀

/-- Exact continuous-map conjugacy, before applying singular homology. -/
theorem sourceCoordinateTorusHomeomorph_shear_conjugate
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    ((sourceCoordinateTorusHomeomorph C₀ : C(SourceModel C₀, ProductTorus 4)).comp
        (sourceShear C₀)).comp
        ((sourceCoordinateTorusHomeomorph C₀).symm : C(ProductTorus 4, SourceModel C₀)) =
      torusMatrixMap M₀ := by
  apply ContinuousMap.ext
  intro x
  change sourceCoordinateTorusHomeomorph C₀
    (sourceShear C₀ ((sourceCoordinateTorusHomeomorph C₀).symm x)) = _
  rw [sourceCoordinateTorusHomeomorph_shear, Homeomorph.apply_symm_apply]

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
