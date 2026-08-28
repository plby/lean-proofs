import Wikipedia.HopfProblem.EllipticHigherHomologyData
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Integral invariants and coinvariants of the elliptic fibre

The actual restricted monodromy matrices have a primitive invariant line
and primitive coinvariant coordinate.  Explicit integer preimages identify
their difference images; no rank calculation over a field is used.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

/-- The degree-one monodromy difference on the actual fibre lattice. -/
def fibreDifference (j : Kind) : FibreLattice →ₗ[ℤ] FibreLattice :=
  (fibreMatrix j - 1).mulVecLin

theorem fibreDifference_apply (j : Kind) (v : FibreLattice) :
    fibreDifference j v = fibreMatrix j *ᵥ v - v := by
  simp [fibreDifference]

theorem fibreDifference_three_apply (v : FibreLattice) :
    fibreDifference .three v = ![v 1 - v 0, -v 0 - 2 * v 1, v 0] := by
  ext i
  fin_cases i <;> simp [fibreDifference, fibreMatrix, dotProduct, Fin.sum_univ_succ]
  all_goals ring

theorem fibreDifference_four_apply (v : FibreLattice) :
    fibreDifference .four v = ![-v 0 - v 1, v 0 - v 1, v 1] := by
  ext i
  fin_cases i <;> simp [fibreDifference, fibreMatrix, dotProduct, Fin.sum_univ_succ]
  all_goals ring

theorem fibreDifference_mem_ker_iff (j : Kind) (v : FibreLattice) :
    v ∈ LinearMap.ker (fibreDifference j) ↔ v 0 = 0 ∧ v 1 = 0 := by
  rw [LinearMap.mem_ker]
  cases j with
  | three =>
    rw [fibreDifference_three_apply]
    constructor
    · intro hv
      have h0 := congrFun hv 0
      have h2 := congrFun hv 2
      change v 1 - v 0 = 0 at h0
      change v 0 = 0 at h2
      omega
    · rintro ⟨h0, h1⟩
      ext i
      fin_cases i <;> simp [h0, h1]
  | four =>
    rw [fibreDifference_four_apply]
    constructor
    · intro hv
      have h0 := congrFun hv 0
      have h2 := congrFun hv 2
      change -v 0 - v 1 = 0 at h0
      change v 1 = 0 at h2
      omega
    · rintro ⟨h0, h1⟩
      ext i
      fin_cases i <;> simp [h0, h1]

/-- The primitive fixed vector in the three-dimensional fibre lattice. -/
def fibreKernelVector : FibreLattice := ![0, 0, 1]

theorem fibreDifference_ker_eq_span (j : Kind) :
    LinearMap.ker (fibreDifference j) = Submodule.span ℤ {fibreKernelVector} := by
  ext v
  rw [fibreDifference_mem_ker_iff, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨v 2, ?_⟩
    ext i
    fin_cases i <;> simp [fibreKernelVector, h0, h1]
  · rintro ⟨k, rfl⟩
    simp [fibreKernelVector]

/-- The invariant coefficient is the last coordinate, with its explicit
integral inverse along the primitive fixed vector. -/
def fibreKernelEquivInt (j : Kind) :
    LinearMap.ker (fibreDifference j) ≃ₗ[ℤ] ℤ where
  toFun v := v.1 2
  invFun k := ⟨![0, 0, k], (fibreDifference_mem_ker_iff j _).mpr (by simp)⟩
  left_inv v := by
    apply Subtype.ext
    obtain ⟨h0, h1⟩ := (fibreDifference_mem_ker_iff j v.1).mp v.2
    ext i
    fin_cases i <;> simp [h0, h1]
  right_inv k := rfl
  map_add' v w := rfl
  map_smul' k v := rfl

@[simp] theorem fibreKernelEquivInt_apply (j : Kind)
    (v : LinearMap.ker (fibreDifference j)) :
    fibreKernelEquivInt j v = v.1 2 := rfl

@[simp] theorem fibreKernelEquivInt_symm_apply (j : Kind) (k : ℤ) :
    ((fibreKernelEquivInt j).symm k : FibreLattice) = ![0, 0, k] := rfl

/-- The primitive integral functional that reads the coinvariant class. -/
def fibreCoinvariantCoordinate (j : Kind) : FibreLattice →ₗ[ℤ] ℤ where
  toFun v := match j with
    | .three => 2 * v 0 + v 1 + 3 * v 2
    | .four => v 0 + v 1 + 2 * v 2
  map_add' v w := by cases j <;> simp only [Pi.add_apply] <;> ring
  map_smul' k v := by
    cases j <;> simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring

@[simp] theorem fibreCoinvariantCoordinate_three_apply (v : FibreLattice) :
    fibreCoinvariantCoordinate .three v = 2 * v 0 + v 1 + 3 * v 2 := rfl

@[simp] theorem fibreCoinvariantCoordinate_four_apply (v : FibreLattice) :
    fibreCoinvariantCoordinate .four v = v 0 + v 1 + 2 * v 2 := rfl

@[simp] theorem fibreCoinvariantCoordinate_section (j : Kind) (k : ℤ) :
    fibreCoinvariantCoordinate j ![0, k, 0] = k := by
  cases j <;> simp

theorem fibreCoinvariantCoordinate_surjective (j : Kind) :
    Function.Surjective (fibreCoinvariantCoordinate j) :=
  fun k => ⟨![0, k, 0], fibreCoinvariantCoordinate_section j k⟩

@[simp] theorem fibreCoinvariantCoordinate_difference (j : Kind) (v : FibreLattice) :
    fibreCoinvariantCoordinate j (fibreDifference j v) = 0 := by
  cases j <;> simp [fibreDifference_three_apply, fibreDifference_four_apply] <;> ring

/-- Explicit integral preimages of the invariant-coordinate kernel. -/
def fibreRangePreimage (j : Kind) (v : FibreLattice) : FibreLattice :=
  match j with
  | .three => ![v 2, v 0 + v 2, 0]
  | .four => ![-v 0 - v 2, v 2, 0]

theorem fibreDifference_rangePreimage (j : Kind) (v : FibreLattice)
    (hv : fibreCoinvariantCoordinate j v = 0) :
    fibreDifference j (fibreRangePreimage j v) = v := by
  cases j with
  | three =>
    change 2 * v 0 + v 1 + 3 * v 2 = 0 at hv
    rw [fibreDifference_three_apply]
    ext i
    fin_cases i <;> simp [fibreRangePreimage]
    all_goals omega
  | four =>
    change v 0 + v 1 + 2 * v 2 = 0 at hv
    rw [fibreDifference_four_apply]
    ext i
    fin_cases i <;> simp [fibreRangePreimage]
    all_goals omega

theorem fibreDifference_range_iff (j : Kind) (v : FibreLattice) :
    v ∈ LinearMap.range (fibreDifference j) ↔ fibreCoinvariantCoordinate j v = 0 := by
  constructor
  · rintro ⟨w, rfl⟩
    exact fibreCoinvariantCoordinate_difference j w
  · intro hv
    exact ⟨fibreRangePreimage j v, fibreDifference_rangePreimage j v hv⟩

theorem fibreDifference_range_eq_ker (j : Kind) :
    LinearMap.range (fibreDifference j) = LinearMap.ker (fibreCoinvariantCoordinate j) := by
  ext v
  exact fibreDifference_range_iff j v

/-- The actual integral cokernel, including its primitive coordinate. -/
def fibreCokernelEquivInt (j : Kind) :
    (FibreLattice ⧸ LinearMap.range (fibreDifference j)) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ (fibreDifference_range_eq_ker j)).trans
    ((fibreCoinvariantCoordinate j).quotKerEquivOfSurjective
      (fibreCoinvariantCoordinate_surjective j))

@[simp] theorem fibreCokernelEquivInt_apply_mk (j : Kind) (v : FibreLattice) :
    fibreCokernelEquivInt j (Submodule.Quotient.mk v) = fibreCoinvariantCoordinate j v := rfl

@[simp] theorem fibreCokernelEquivInt_symm_apply (j : Kind) (k : ℤ) :
    (fibreCokernelEquivInt j).symm k = Submodule.Quotient.mk ![0, k, 0] := by
  apply (fibreCokernelEquivInt j).injective
  simp

end Wikipedia.HopfProblem.Elliptic.HigherHomology
