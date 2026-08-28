import Wikipedia.HopfProblem.EllipticHigherHomologyCoverAlgebraCoordinates
import Wikipedia.HopfProblem.EllipticHigherHomologyCoverAlgebraRange

/-!
# Integral cokernels from a first-axis image and a second-coordinate image

For any integer linear map into `ℤ²`, containing the first axis and having
second-coordinate image `dℤ` determine its full image and its cokernel.
The cokernel equivalence is explicit reduction of the second coordinate
modulo `d`.  The exact index is `d`, including the infinite-index
convention at `d = 0`.  At `d = 1` the map is surjective and its cokernel
is zero; quotienting its domain by its kernel gives an equivalence.

These are generic algebraic assembly lemmas.  No naturality statement
or identification of a topological covering map is assumed or asserted.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology.CoverAlgebra

variable {M : Type*} [AddCommGroup M] [Module ℤ M]

theorem range_eq_divisibleSecond (L : M →ₗ[ℤ] Coordinates)
    (haxis : ∀ t : ℤ, ![t, 0] ∈ LinearMap.range L)
    (d : ℕ) (hsecond : LinearMap.range (secondMap L) = Submodule.span ℤ {(d : ℤ)}) :
    LinearMap.range L = divisibleSecond d := by
  ext v
  rw [mem_range_iff_dvd L haxis d hsecond, mem_divisibleSecond_iff]

theorem range_eq_divisibleSecond_of_second_image (L : M →ₗ[ℤ] Coordinates)
    (haxis : ∀ t : ℤ, ![t, 0] ∈ LinearMap.range L)
    (d : ℕ) (hsecond : ∀ k : ℤ,
      k ∈ LinearMap.range (secondMap L) ↔ (d : ℤ) ∣ k) :
    LinearMap.range L = divisibleSecond d := by
  ext v
  rw [mem_range_iff_of_second L haxis d hsecond, mem_divisibleSecond_iff]

/-- The explicit cokernel equivalence supplied by the two image facts. -/
def cokernelEquivZMod (L : M →ₗ[ℤ] Coordinates)
    (haxis : ∀ t : ℤ, ![t, 0] ∈ LinearMap.range L)
    (d : ℕ) (hsecond : LinearMap.range (secondMap L) = Submodule.span ℤ {(d : ℤ)}) :
    (Coordinates ⧸ LinearMap.range L) ≃ₗ[ℤ] ZMod d :=
  (Submodule.quotEquivOfEq _ _ (range_eq_divisibleSecond L haxis d hsecond)).trans
    (divisibleSecondQuotientEquivZMod d)

@[simp] theorem cokernelEquivZMod_apply_mk (L : M →ₗ[ℤ] Coordinates)
    (haxis : ∀ t : ℤ, ![t, 0] ∈ LinearMap.range L)
    (d : ℕ) (hsecond : LinearMap.range (secondMap L) = Submodule.span ℤ {(d : ℤ)})
    (v : Coordinates) :
    cokernelEquivZMod L haxis d hsecond (Submodule.Quotient.mk v) = (v 1 : ZMod d) := rfl

@[simp] theorem cokernelEquivZMod_symm_apply_intCast (L : M →ₗ[ℤ] Coordinates)
    (haxis : ∀ t : ℤ, ![t, 0] ∈ LinearMap.range L)
    (d : ℕ) (hsecond : LinearMap.range (secondMap L) = Submodule.span ℤ {(d : ℤ)}) (k : ℤ) :
    (cokernelEquivZMod L haxis d hsecond).symm (k : ZMod d) =
      Submodule.Quotient.mk ![0, k] := by
  apply (cokernelEquivZMod L haxis d hsecond).injective
  rw [LinearEquiv.apply_symm_apply, cokernelEquivZMod_apply_mk]
  rfl

theorem range_index (L : M →ₗ[ℤ] Coordinates)
    (haxis : ∀ t : ℤ, ![t, 0] ∈ LinearMap.range L)
    (d : ℕ) (hsecond : LinearMap.range (secondMap L) = Submodule.span ℤ {(d : ℤ)}) :
    (LinearMap.range L).toAddSubgroup.index = d := by
  rw [range_eq_divisibleSecond L haxis d hsecond, divisibleSecond_index]

theorem range_finiteIndex (L : M →ₗ[ℤ] Coordinates)
    (haxis : ∀ t : ℤ, ![t, 0] ∈ LinearMap.range L)
    (d : ℕ) (hd : 0 < d)
    (hsecond : LinearMap.range (secondMap L) = Submodule.span ℤ {(d : ℤ)}) :
    (LinearMap.range L).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [range_index L haxis d hsecond]
  exact hd.ne'

/-- The elementwise projected-image criterion gives the same explicit equivalence. -/
def cokernelEquivZModOfSecondImage (L : M →ₗ[ℤ] Coordinates)
    (haxis : ∀ t : ℤ, ![t, 0] ∈ LinearMap.range L)
    (d : ℕ) (hsecond : ∀ k : ℤ,
      k ∈ LinearMap.range (secondMap L) ↔ (d : ℤ) ∣ k) :
    (Coordinates ⧸ LinearMap.range L) ≃ₗ[ℤ] ZMod d :=
  (Submodule.quotEquivOfEq _ _
    (range_eq_divisibleSecond_of_second_image L haxis d hsecond)).trans
      (divisibleSecondQuotientEquivZMod d)

@[simp] theorem cokernelEquivZModOfSecondImage_apply_mk (L : M →ₗ[ℤ] Coordinates)
    (haxis : ∀ t : ℤ, ![t, 0] ∈ LinearMap.range L)
    (d : ℕ) (hsecond : ∀ k : ℤ,
      k ∈ LinearMap.range (secondMap L) ↔ (d : ℤ) ∣ k) (v : Coordinates) :
    cokernelEquivZModOfSecondImage L haxis d hsecond (Submodule.Quotient.mk v) =
      (v 1 : ZMod d) := rfl

theorem range_index_of_second_image (L : M →ₗ[ℤ] Coordinates)
    (haxis : ∀ t : ℤ, ![t, 0] ∈ LinearMap.range L)
    (d : ℕ) (hsecond : ∀ k : ℤ,
      k ∈ LinearMap.range (secondMap L) ↔ (d : ℤ) ∣ k) :
    (LinearMap.range L).toAddSubgroup.index = d := by
  rw [range_eq_divisibleSecond_of_second_image L haxis d hsecond, divisibleSecond_index]

theorem cokernel_subsingleton_of_second_one (L : M →ₗ[ℤ] Coordinates)
    (haxis : ∀ t : ℤ, ![t, 0] ∈ LinearMap.range L)
    (hsecond : LinearMap.range (secondMap L) = Submodule.span ℤ {(1 : ℤ)}) :
    Subsingleton (Coordinates ⧸ LinearMap.range L) := by
  refine ⟨fun x y => ?_⟩
  apply (cokernelEquivZMod L haxis 1 hsecond).injective
  exact Subsingleton.elim _ _

theorem cokernel_eq_zero_of_second_one (L : M →ₗ[ℤ] Coordinates)
    (haxis : ∀ t : ℤ, ![t, 0] ∈ LinearMap.range L)
    (hsecond : LinearMap.range (secondMap L) = Submodule.span ℤ {(1 : ℤ)})
    (x : Coordinates ⧸ LinearMap.range L) : x = 0 := by
  apply (cokernelEquivZMod L haxis 1 hsecond).injective
  exact Subsingleton.elim _ _

end Wikipedia.HopfProblem.Elliptic.HigherHomology.CoverAlgebra
