import Wikipedia.HopfProblem.ToricHexagon
import Mathlib.Algebra.Module.Submodule.Ker

/-!
# Integral characters on the zero-sum phase triples

The first three actual hexagon rays give the determinant characters
`y`, `-x`, and `-x-y`.  Their combined map is surjective even after
restricting its domain to triples of lattice vectors with sum zero.
The proof constructs an explicit integral linear section.
-/

open scoped Matrix

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricComponent

/-- The pointwise sum of the three phase lattice vectors. -/
def thetaPhaseTripleSum : (Fin 3 → Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) where
  toFun v := ∑ j, v j
  map_add' v w := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]

theorem thetaPhaseTripleSum_apply (v : Fin 3 → Fin 2 → ℤ) (i : Fin 2) :
    thetaPhaseTripleSum v i = v 0 i + v 1 i + v 2 i := by
  simp [thetaPhaseTripleSum, Fin.sum_univ_succ, add_assoc]

/-- The determinant characters for the first three actual hexagon rays. -/
def thetaPhaseTripleCharacters : (Fin 3 → Fin 2 → ℤ) →ₗ[ℤ] (Fin 3 → ℤ) where
  toFun v := ![v 0 1, -(v 1 0), -(v 2 0) - v 2 1]
  map_add' v w := by
    funext j
    fin_cases j <;> simp <;> ring
  map_smul' c v := by
    funext j
    fin_cases j <;> simp
    ring

theorem thetaPhaseTripleCharacters_apply_zero (v : Fin 3 → Fin 2 → ℤ) :
    thetaPhaseTripleCharacters v 0 = v 0 1 := rfl

theorem thetaPhaseTripleCharacters_apply_one (v : Fin 3 → Fin 2 → ℤ) :
    thetaPhaseTripleCharacters v 1 = -(v 1 0) := rfl

theorem thetaPhaseTripleCharacters_apply_two (v : Fin 3 → Fin 2 → ℤ) :
    thetaPhaseTripleCharacters v 2 = -(v 2 0) - v 2 1 := rfl

/-- The coordinates are precisely the integral determinant against the
actual ray, with the ray as the first column. -/
theorem thetaPhaseTripleCharacters_eq_det (v : Fin 3 → Fin 2 → ℤ) (j : Fin 3) :
    thetaPhaseTripleCharacters v j =
      hexagonRay (j.castLE (by decide)) 0 * v j 1 -
        hexagonRay (j.castLE (by decide)) 1 * v j 0 := by
  fin_cases j <;> simp [thetaPhaseTripleCharacters, hexagonRay]
  ring

theorem thetaPhaseTripleCharacters_eq_matrix_det
    (v : Fin 3 → Fin 2 → ℤ) (j : Fin 3) :
    thetaPhaseTripleCharacters v j =
      Matrix.det (!![hexagonRay (j.castLE (by decide)) 0, v j 0;
        hexagonRay (j.castLE (by decide)) 1, v j 1]) := by
  rw [Matrix.det_fin_two]
  change thetaPhaseTripleCharacters v j =
    hexagonRay (j.castLE (by decide)) 0 * v j 1 -
      v j 0 * hexagonRay (j.castLE (by decide)) 1
  simpa only [mul_comm] using thetaPhaseTripleCharacters_eq_det v j

/-- An explicit integral triple with prescribed three character values. -/
def thetaPhaseTripleSection : (Fin 3 → ℤ) →ₗ[ℤ] (Fin 3 → Fin 2 → ℤ) where
  toFun z := ![![z 2 + z 1 - z 0, z 0], ![-z 1, 0], ![z 0 - z 2, -z 0]]
  map_add' z w := by
    funext j i
    fin_cases j <;> fin_cases i <;> simp <;> ring
  map_smul' c z := by
    funext j i
    fin_cases j <;> fin_cases i <;> simp <;> ring

theorem thetaPhaseTripleSection_apply (z : Fin 3 → ℤ) :
    thetaPhaseTripleSection z =
      ![![z 2 + z 1 - z 0, z 0], ![-z 1, 0], ![z 0 - z 2, -z 0]] := rfl

/-- The prescribed triple satisfies the actual zero-sum constraint. -/
theorem thetaPhaseTripleSum_section (z : Fin 3 → ℤ) :
    thetaPhaseTripleSum (thetaPhaseTripleSection z) = 0 := by
  funext i
  rw [thetaPhaseTripleSum_apply]
  fin_cases i <;> simp [thetaPhaseTripleSection]
  ring

theorem thetaPhaseTripleCharacters_section (z : Fin 3 → ℤ) :
    thetaPhaseTripleCharacters (thetaPhaseTripleSection z) = z := by
  funext j
  fin_cases j <;> simp [thetaPhaseTripleCharacters, thetaPhaseTripleSection]

/-- Restrict the actual three characters to the zero-sum phase lattice. -/
def thetaPhaseCharacterKernelMap :
    LinearMap.ker thetaPhaseTripleSum →ₗ[ℤ] (Fin 3 → ℤ) :=
  thetaPhaseTripleCharacters.domRestrict (LinearMap.ker thetaPhaseTripleSum)

theorem thetaPhaseCharacterKernelMap_apply (v : LinearMap.ker thetaPhaseTripleSum) :
    thetaPhaseCharacterKernelMap v = thetaPhaseTripleCharacters v := rfl

/-- The explicit section lands in the zero-sum kernel over the integers. -/
def thetaPhaseCharacterKernelSection :
    (Fin 3 → ℤ) →ₗ[ℤ] LinearMap.ker thetaPhaseTripleSum :=
  thetaPhaseTripleSection.codRestrict (LinearMap.ker thetaPhaseTripleSum)
    (fun z => LinearMap.mem_ker.mpr (thetaPhaseTripleSum_section z))

theorem thetaPhaseCharacterKernelSection_coe (z : Fin 3 → ℤ) :
    (thetaPhaseCharacterKernelSection z : Fin 3 → Fin 2 → ℤ) =
      thetaPhaseTripleSection z := rfl

theorem thetaPhaseCharacterKernelMap_section (z : Fin 3 → ℤ) :
    thetaPhaseCharacterKernelMap (thetaPhaseCharacterKernelSection z) = z :=
  thetaPhaseTripleCharacters_section z

theorem thetaPhaseCharacterKernelMap_comp_section :
    thetaPhaseCharacterKernelMap.comp thetaPhaseCharacterKernelSection =
      LinearMap.id := by
  apply LinearMap.ext
  exact thetaPhaseCharacterKernelMap_section

theorem thetaPhaseCharacterKernelMap_surjective :
    Function.Surjective thetaPhaseCharacterKernelMap :=
  fun z => ⟨thetaPhaseCharacterKernelSection z, thetaPhaseCharacterKernelMap_section z⟩

end Wikipedia.HopfProblem.CuspCentralHomology
