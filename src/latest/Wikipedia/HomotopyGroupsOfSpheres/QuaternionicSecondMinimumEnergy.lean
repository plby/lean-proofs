import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondMinimalDirections
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMinimumEnergy

/-! # The energy of the original anticommuting rotation family -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.AnticommutingStructures

variable {n : ℕ} {a : ComplexStructures.Space n}

theorem energy_rotation (P : Space a) :
    NoExoticSixSphere.OrthogonalPathEnergy.energy
      (fun t ↦ (rotation P (t * Real.pi)).val.val) 0 1 =
        ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 := by
  have he : (fun t : ℝ ↦ (rotation P (t * Real.pi)).val.val) =
      (fun t : ℝ ↦ (ComplexStructures.toSymplectic a *
        Exponential.exp (t • (Real.pi • (generatorParameter P).val.val))).val.val.val) := by
    funext t
    have h := congrArg (fun q : symplecticSubgroup n ↦ q.val.val.val)
      (rotation_toSymplectic P (t * Real.pi))
    simpa only [smul_smul, ComplexStructures.toSymplectic_operator] using h
  rw [he]
  exact MinimumPaths.energy_complexStructure (ComplexStructures.toSymplectic a)
    (generatorParameter P).val

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.AnticommutingStructures
