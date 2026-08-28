import Wikipedia.HomotopyGroupsOfSpheres.UnitaryBlockDiagonal
import Wikipedia.HomotopyGroupsOfSpheres.UnitaryPairMixing
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryProjection

/-! # Actual based symmetric homotopies obtained by conjugating the unitary block inclusion -/

noncomputable section

open scoped Matrix unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.UnitaryBlockConjugation

open QuaternionicSymmetricMatrices

variable {N : Type*} [Fintype N] [DecidableEq N]

local notation "U" => unitary (Matrix N N ℂ)
local notation "V" => unitary (Matrix (N ⊕ N) (N ⊕ N) ℂ)

def family (P : C(I, V)) : C(I × U, V) :=
  let p : C(I × U, V) := P.comp ⟨Prod.fst, continuous_fst⟩
  let d : C(I × U, V) :=
    ⟨fun z ↦ UnitaryBlockDiagonal.inclusion z.2,
      UnitaryBlockDiagonal.continuous_inclusion.comp continuous_snd⟩
  p⁻¹ * d * p

theorem family_zero (P : C(I, V)) (hP : P 0 = 1) (A : U) :
    family P (0, A) = UnitaryBlockDiagonal.inclusion A := by
  change (P 0)⁻¹ * UnitaryBlockDiagonal.inclusion A * P 0 = _
  rw [hP, inv_one, one_mul, mul_one]

theorem family_one (P : C(I, V)) (t : I) : family P (t, (1 : U)) = 1 := by
  change (P t)⁻¹ * UnitaryBlockDiagonal.inclusion 1 * P t = 1
  rw [map_one, mul_one, inv_mul_cancel]

def endpoint (P : C(I, V)) : C(U, V) :=
  (family P).comp ⟨fun A ↦ (1, A), continuous_const.prodMk continuous_id⟩

def homotopy (P : C(I, V)) (hP : P 0 = 1) :
    (UnitaryBlockDiagonal.inclusionMap (N := N)).Homotopy (endpoint P) where
  toContinuousMap := family P
  map_zero_left := family_zero P hP
  map_one_left _ := rfl

def symmetricHomotopy (P : C(I, V)) (hP : P 0 = 1) :
    (unitaryProjection.comp (UnitaryBlockDiagonal.inclusionMap (N := N))).HomotopyRel
      (unitaryProjection.comp (endpoint P)) {(1 : U)} :=
  unitaryProjectionHomotopyRel (N := N ⊕ N) (homotopy P hP) 1 (by
    intro t i j
    change star ((family P (t, (1 : U))).val i j) = (family P (t, (1 : U))).val i j
    rw [family_one]
    change star ((1 : Matrix (N ⊕ N) (N ⊕ N) ℂ) i j) =
      (1 : Matrix (N ⊕ N) (N ⊕ N) ℂ) i j
    simp [Matrix.one_apply])

def source : C(U, Space (N ⊕ N)) :=
  unitaryProjection.comp UnitaryBlockDiagonal.inclusionMap

def target : C(U, Space (N ⊕ N)) :=
  unitaryProjection.comp (endpoint UnitaryPairMixing.blockPath)

def mixingHomotopy : (source (N := N)).HomotopyRel target {(1 : U)} :=
  symmetricHomotopy UnitaryPairMixing.blockPath UnitaryPairMixing.blockPath_zero

end Wikipedia.HomotopyGroupsOfSpheres.UnitaryBlockConjugation
