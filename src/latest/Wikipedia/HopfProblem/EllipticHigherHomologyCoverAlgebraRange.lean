import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.FinCases

/-!
# Reconstructing an integral image from its second coordinate

If an integer linear map to `ℤ²` contains the entire first coordinate
axis in its image, its image is the inverse image of the projected second
coordinate image.  The converse is constructive: subtract the excess
first coordinate using the given first-axis witnesses.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology.CoverAlgebra

variable {M : Type*} [AddCommGroup M] [Module ℤ M]

/-- The second coordinate of an integer linear map to the two-dimensional lattice. -/
def secondMap (L : M →ₗ[ℤ] (Fin 2 → ℤ)) : M →ₗ[ℤ] ℤ :=
  (LinearMap.proj 1).comp L

@[simp] theorem secondMap_apply (L : M →ₗ[ℤ] (Fin 2 → ℤ)) (x : M) :
    secondMap L x = L x 1 := rfl

theorem mem_range_iff_second (L : M →ₗ[ℤ] (Fin 2 → ℤ))
    (haxis : ∀ t : ℤ, ![t, 0] ∈ LinearMap.range L) (v : Fin 2 → ℤ) :
    v ∈ LinearMap.range L ↔ v 1 ∈ LinearMap.range (secondMap L) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := haxis (v 0 - L x 0)
    refine ⟨x + y, ?_⟩
    rw [map_add, hy]
    change L x 1 = v 1 at hx
    ext i
    fin_cases i <;> simp [hx]

theorem range_eq_comap_second (L : M →ₗ[ℤ] (Fin 2 → ℤ))
    (haxis : ∀ t : ℤ, ![t, 0] ∈ LinearMap.range L) :
    LinearMap.range L =
      (LinearMap.range (secondMap L)).comap (LinearMap.proj 1) := by
  ext v
  exact mem_range_iff_second L haxis v

theorem mem_range_iff_of_second (L : M →ₗ[ℤ] (Fin 2 → ℤ))
    (haxis : ∀ t : ℤ, ![t, 0] ∈ LinearMap.range L)
    (d : ℕ) (hsecond : ∀ k : ℤ,
      k ∈ LinearMap.range (secondMap L) ↔ (d : ℤ) ∣ k) (v : Fin 2 → ℤ) :
    v ∈ LinearMap.range L ↔ (d : ℤ) ∣ v 1 := by
  rw [mem_range_iff_second L haxis, hsecond]

theorem mem_range_iff_dvd (L : M →ₗ[ℤ] (Fin 2 → ℤ))
    (haxis : ∀ t : ℤ, ![t, 0] ∈ LinearMap.range L)
    (d : ℕ) (hsecond : LinearMap.range (secondMap L) = Submodule.span ℤ {(d : ℤ)})
    (v : Fin 2 → ℤ) :
    v ∈ LinearMap.range L ↔ (d : ℤ) ∣ v 1 := by
  rw [mem_range_iff_second L haxis, hsecond, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa [smul_eq_mul, mul_comm] using ha.symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa [smul_eq_mul, mul_comm] using ha.symm⟩

theorem range_coe_eq_setOf_dvd (L : M →ₗ[ℤ] (Fin 2 → ℤ))
    (haxis : ∀ t : ℤ, ![t, 0] ∈ LinearMap.range L)
    (d : ℕ) (hsecond : LinearMap.range (secondMap L) = Submodule.span ℤ {(d : ℤ)}) :
    (LinearMap.range L : Set (Fin 2 → ℤ)) = {v | (d : ℤ) ∣ v 1} := by
  ext v
  exact mem_range_iff_dvd L haxis d hsecond v

theorem exists_vertical_generator (L : M →ₗ[ℤ] (Fin 2 → ℤ))
    (haxis : ∀ t : ℤ, ![t, 0] ∈ LinearMap.range L)
    (d : ℕ) (hsecond : LinearMap.range (secondMap L) = Submodule.span ℤ {(d : ℤ)}) :
    ∃ x : M, L x = ![0, (d : ℤ)] := by
  apply (mem_range_iff_dvd L haxis d hsecond _).mpr
  simp

theorem surjective_of_second_one (L : M →ₗ[ℤ] (Fin 2 → ℤ))
    (haxis : ∀ t : ℤ, ![t, 0] ∈ LinearMap.range L)
    (hsecond : LinearMap.range (secondMap L) = Submodule.span ℤ {(1 : ℤ)}) :
    Function.Surjective L := by
  intro v
  apply (mem_range_iff_dvd L haxis 1 hsecond v).mpr
  simp

theorem range_eq_top_of_second_one (L : M →ₗ[ℤ] (Fin 2 → ℤ))
    (haxis : ∀ t : ℤ, ![t, 0] ∈ LinearMap.range L)
    (hsecond : LinearMap.range (secondMap L) = Submodule.span ℤ {(1 : ℤ)}) :
    LinearMap.range L = ⊤ :=
  LinearMap.range_eq_top.mpr (surjective_of_second_one L haxis hsecond)

/-- Surjectivity gives an equivalence after quotienting the domain kernel;
no injectivity of the original map is assumed. -/
def quotientKernelEquivCoordinates (L : M →ₗ[ℤ] (Fin 2 → ℤ))
    (haxis : ∀ t : ℤ, ![t, 0] ∈ LinearMap.range L)
    (hsecond : LinearMap.range (secondMap L) = Submodule.span ℤ {(1 : ℤ)}) :
    (M ⧸ LinearMap.ker L) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (QuotientAddGroup.quotientKerEquivOfSurjective L.toAddMonoidHom
    (surjective_of_second_one L haxis hsecond)).toIntLinearEquiv

@[simp] theorem quotientKernelEquivCoordinates_apply_mk (L : M →ₗ[ℤ] (Fin 2 → ℤ))
    (haxis : ∀ t : ℤ, ![t, 0] ∈ LinearMap.range L)
    (hsecond : LinearMap.range (secondMap L) = Submodule.span ℤ {(1 : ℤ)}) (x : M) :
    quotientKernelEquivCoordinates L haxis hsecond (Submodule.Quotient.mk x) = L x := rfl

end Wikipedia.HopfProblem.Elliptic.HigherHomology.CoverAlgebra
