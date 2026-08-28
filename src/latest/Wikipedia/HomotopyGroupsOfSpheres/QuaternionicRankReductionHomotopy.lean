import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicEquatorialSection
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicReducedSevenCube

/-!
# The explicit rank reduction preserves the based Bott family up to conjugation

Contract both completion sections simultaneously. Their equality on every
angular boundary face and at the reference matrix keeps the whole homotopy
based. The final map is the actual stabilization of the reduced family.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicColumns QuaternionicSymmetricMatrices

local notation "Parameters" => (ℝ × ℝ) × Space (Fin 3)
local notation "CubeParameters" => Space (Fin 3) × (Fin 2 → I)

attribute [local irreducible] rotation

def rotationEquatorialColumn : C(Parameters, EquatorialColumn (0 : Fin 3)) where
  toFun z := ⟨column 0 (swap * rotation z.1.1 z.1.2 z.2), by
    change ((swap * rotation z.1.1 z.1.2 z.2).val 0 0).re = 0
    rw [swap_mul_first_row]
    exact rotation_offDiagonal_re _ _ _ 1 0 (by decide)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (column 0).continuous.comp (continuous_const.mul continuous_rotation)

theorem rotationEquatorialColumn_eq (z w : Parameters)
    (h : rotation z.1.1 z.1.2 z.2 = rotation w.1.1 w.1.2 w.2) :
    rotationEquatorialColumn z = rotationEquatorialColumn w := by
  apply Subtype.ext
  change column 0 (swap * rotation z.1.1 z.1.2 z.2) =
    column 0 (swap * rotation w.1.1 w.1.2 w.2)
  rw [h]

def rotationSectionPath : C(I × Parameters, SpGroup (Fin 3)) :=
  (equatorialSectionPath 0).comp
    ⟨fun p ↦ (p.1, rotationEquatorialColumn p.2),
      continuous_fst.prodMk (rotationEquatorialColumn.continuous.comp continuous_snd)⟩

theorem rotationSectionPath_zero (z : Parameters) : rotationSectionPath (0, z) = 1 :=
  equatorialSectionPath_zero 0 (rotationEquatorialColumn z)

theorem rotationSectionPath_one (z : Parameters) :
    rotationSectionPath (1, z) = reductionSection (rotationInDomain z) := by
  exact equatorialSectionPath_one 0 (rotationEquatorialColumn z)
    (reductionColumn (rotationInDomain z)).property

theorem rotationSectionPath_eq (r : I) (z w : Parameters)
    (h : rotation z.1.1 z.1.2 z.2 = rotation w.1.1 w.1.2 w.2) :
    rotationSectionPath (r, z) = rotationSectionPath (r, w) := by
  change equatorialSectionPath 0 (r, rotationEquatorialColumn z) =
    equatorialSectionPath 0 (r, rotationEquatorialColumn w)
  rw [rotationEquatorialColumn_eq z w h]

def referenceParameter : C(CubeParameters, CubeParameters) :=
  ⟨fun z ↦ (identity, z.2), continuous_const.prodMk continuous_snd⟩

def rawCubeRotation : C(CubeParameters, SpGroup (Fin 3)) :=
  ⟨fun z ↦ rotation ((z.2 0 : ℝ) * Real.pi) ((z.2 1 : ℝ) * Real.pi) z.1,
    (continuous_rotation (N := Fin 3)).comp (cubeAngles (N := Fin 3)).continuous⟩

theorem rawCubeRotation_boundary (B : Space (Fin 3)) (u : Fin 2 → I)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    rawCubeRotation (B, u) = rawCubeRotation (identity, u) :=
  mul_inv_eq_one.mp (twoCubeFamily_boundary B u hu)

def conjugatedTwoCubeFamily : C(CubeParameters, SpGroup (Fin 3)) :=
  ContinuousMap.const _ swap * twoCubeFamily * ContinuousMap.const _ swap⁻¹

def stabilizedReducedTwoCubeFamily : C(CubeParameters, SpGroup (Fin 3)) :=
  (⟨stabilization 2, continuous_stabilization 2⟩ :
    C(SpGroup (Fin 2), SpGroup (Fin 3))).comp reducedCubeFamily

def sectionCorrectedRotation : C(I × CubeParameters, SpGroup (Fin 3)) :=
  (rotationSectionPath.comp
    ⟨fun p ↦ (p.1, cubeAngles p.2),
      continuous_fst.prodMk (cubeAngles.continuous.comp continuous_snd)⟩)⁻¹ *
    (ContinuousMap.const _ swap * rawCubeRotation.comp ⟨Prod.snd, continuous_snd⟩)

theorem sectionCorrectedRotation_zero (z : CubeParameters) :
    sectionCorrectedRotation (0, z) = swap * rawCubeRotation z := by
  change (rotationSectionPath (0, cubeAngles z))⁻¹ * (swap * rawCubeRotation z) = _
  rw [rotationSectionPath_zero, inv_one, one_mul]

theorem sectionCorrectedRotation_one (z : CubeParameters) :
    sectionCorrectedRotation (1, z) = stabilization 2 (reducedRawCubeFamily z) := by
  change (rotationSectionPath (1, cubeAngles z))⁻¹ * (swap * rawCubeRotation z) = _
  rw [rotationSectionPath_one]
  exact (stabilization_reduce (rotationInDomain (cubeAngles z))).symm

theorem sectionCorrectedRotation_eq (r : I) (z w : CubeParameters)
    (h : rawCubeRotation z = rawCubeRotation w) :
    sectionCorrectedRotation (r, z) = sectionCorrectedRotation (r, w) := by
  change (rotationSectionPath (r, cubeAngles z))⁻¹ * (swap * rawCubeRotation z) =
    (rotationSectionPath (r, cubeAngles w))⁻¹ * (swap * rawCubeRotation w)
  rw [rotationSectionPath_eq r (cubeAngles z) (cubeAngles w) h, h]

def rankReductionHomotopy :
    conjugatedTwoCubeFamily.Homotopy stabilizedReducedTwoCubeFamily where
  toContinuousMap := sectionCorrectedRotation *
    (sectionCorrectedRotation.comp
      ⟨fun p ↦ (p.1, referenceParameter p.2),
        continuous_fst.prodMk (referenceParameter.continuous.comp continuous_snd)⟩)⁻¹
  map_zero_left z := by
    change sectionCorrectedRotation (0, z) *
      (sectionCorrectedRotation (0, referenceParameter z))⁻¹ = _
    rw [sectionCorrectedRotation_zero, sectionCorrectedRotation_zero]
    change (swap * rawCubeRotation z) * (swap * rawCubeRotation (referenceParameter z))⁻¹ =
      swap * (rawCubeRotation z * (rawCubeRotation (referenceParameter z))⁻¹) * swap⁻¹
    group
  map_one_left z := by
    change sectionCorrectedRotation (1, z) *
      (sectionCorrectedRotation (1, referenceParameter z))⁻¹ = _
    rw [sectionCorrectedRotation_one, sectionCorrectedRotation_one, ← map_inv, ← map_mul]
    rfl

theorem rankReductionHomotopy_identity (r : I) (u : Fin 2 → I) :
    rankReductionHomotopy (r, (identity, u)) = 1 := by
  exact mul_inv_cancel _

theorem rankReductionHomotopy_boundary (r : I) (B : Space (Fin 3)) (u : Fin 2 → I)
    (hu : u ∈ Cube.boundary (Fin 2)) : rankReductionHomotopy (r, (B, u)) = 1 := by
  change sectionCorrectedRotation (r, (B, u)) *
    (sectionCorrectedRotation (r, (identity, u)))⁻¹ = 1
  rw [sectionCorrectedRotation_eq r (B, u) (identity, u) (rawCubeRotation_boundary B u hu),
    mul_inv_cancel]

def rankReductionHomotopyRel :
    conjugatedTwoCubeFamily.HomotopyRel stabilizedReducedTwoCubeFamily
      {z | z.1 = identity ∨ z.2 ∈ Cube.boundary (Fin 2)} where
  toHomotopy := rankReductionHomotopy
  prop' r z hz := by
    change rankReductionHomotopy (r, z) = conjugatedTwoCubeFamily z
    rcases hz with h | h
    · rcases z with ⟨B, u⟩
      dsimp at h
      subst B
      rw [rankReductionHomotopy_identity]
      exact (rankReductionHomotopy.apply_zero (identity, u)).symm.trans
        (rankReductionHomotopy_identity 0 u) |>.symm
    · rw [rankReductionHomotopy_boundary r z.1 z.2 h]
      exact (rankReductionHomotopy.apply_zero z).symm.trans
        (rankReductionHomotopy_boundary 0 z.1 z.2 h) |>.symm

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
