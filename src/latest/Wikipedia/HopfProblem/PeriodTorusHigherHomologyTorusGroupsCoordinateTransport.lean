import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroupsCoordinateBasis
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroupsPeriod

/-!
# Actual coordinate-subtorus homology bases on period tori

Transport along a homeomorphism preserves the proved basis of actual
coordinate-subtorus classes. The transported classes are explicitly the
actual induced homology maps of continuous maps into the target space.
In particular, to prove a map onto period-torus homology is surjective,
it suffices to put each of these actual classes in its range.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open Elliptic SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] {r : ℕ}

/-- The literal coordinate subtorus map transported into a homeomorphic space. -/
def coordinateTorusMapAlong (e : X ≃ₜ ProductTorus r) (n : ℕ) (i : Fin (r.choose n)) :
    C(ProductTorus n, X) :=
  (e.symm : C(ProductTorus r, X)).comp (coordinateTorusMap r n i)

/-- The actual induced homology class of a transported coordinate subtorus. -/
def coordinateTorusClassAlong (e : X ≃ₜ ProductTorus r) (n : ℕ)
    (i : Fin (r.choose n)) : SingularHomology X n :=
  singularHomologyMap (coordinateTorusMapAlong e n i) n (productTorusTopClass n)

/-- A basis of actual homology along a homeomorphism with a product torus. -/
def coordinateTorusBasisAlong (e : X ≃ₜ ProductTorus r) (n : ℕ) :
    Module.Basis (Fin (r.choose n)) ℤ (SingularHomology X n) :=
  (coordinateTorusBasis r n).map (homeomorphHomologyEquiv e n).symm

@[simp] theorem coordinateTorusBasisAlong_apply (e : X ≃ₜ ProductTorus r) (n : ℕ)
    (i : Fin (r.choose n)) :
    coordinateTorusBasisAlong e n i = coordinateTorusClassAlong e n i := by
  rw [coordinateTorusBasisAlong, Module.Basis.map_apply, coordinateTorusBasis_apply,
    homeomorphHomologyEquiv_symm_apply]
  change singularHomologyMap (e.symm : C(ProductTorus r, X)) n
      (singularHomologyMap (coordinateTorusMap r n i) n (productTorusTopClass n)) =
    singularHomologyMap ((e.symm : C(ProductTorus r, X)).comp
      (coordinateTorusMap r n i)) n (productTorusTopClass n)
  rw [singularHomologyMap_comp]
  rfl

theorem coordinateTorusBasisAlong_coe (e : X ≃ₜ ProductTorus r) (n : ℕ) :
    ⇑(coordinateTorusBasisAlong e n) = coordinateTorusClassAlong e n :=
  funext (coordinateTorusBasisAlong_apply e n)

theorem homologyEquiv_coordinateTorusClassAlong (e : X ≃ₜ ProductTorus r) (n : ℕ)
    (i : Fin (r.choose n)) :
    productTorusHomologyEquiv r n
      (homeomorphHomologyEquiv e n (coordinateTorusClassAlong e n i)) = Pi.single i 1 := by
  rw [← coordinateTorusBasisAlong_apply, coordinateTorusBasisAlong, Module.Basis.map_apply,
    LinearEquiv.apply_symm_apply, coordinateTorusBasis_apply,
    productTorusHomologyEquiv_coordinateTorusClass]

theorem coordinateTorusClassAlong_span (e : X ≃ₜ ProductTorus r) (n : ℕ) :
    Submodule.span ℤ (Set.range (coordinateTorusClassAlong e n)) = ⊤ := by
  simpa only [coordinateTorusBasisAlong_coe] using (coordinateTorusBasisAlong e n).span_eq

/-- Actual coordinate-subtorus classes suffice for surjectivity onto homology. -/
theorem surjective_of_coordinateTorusClassAlong_mem_range {M : Type*}
    [AddCommGroup M] [Module ℤ M] (e : X ≃ₜ ProductTorus r) (n : ℕ)
    (f : M →ₗ[ℤ] SingularHomology X n)
    (hf : ∀ i : Fin (r.choose n), coordinateTorusClassAlong e n i ∈ LinearMap.range f) :
    Function.Surjective f := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← coordinateTorusClassAlong_span e n]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact hf i

/-- The actual coordinate-subtorus maps into a complex period torus. -/
abbrev periodTorusCoordinateMap (p : PeriodDomain) (n : ℕ) (i : Fin (Nat.choose 4 n)) :
    C(ProductTorus n, p.Torus) :=
  coordinateTorusMapAlong (periodTorusCircleHomeomorph p) n i

/-- The actual homology classes of the coordinate subtori in a period torus. -/
abbrev periodTorusCoordinateClass (p : PeriodDomain) (n : ℕ) (i : Fin (Nat.choose 4 n)) :
    SingularHomology p.Torus n :=
  coordinateTorusClassAlong (periodTorusCircleHomeomorph p) n i

/-- The coordinate-subtorus basis of actual period-torus homology. -/
abbrev periodTorusCoordinateBasis (p : PeriodDomain) (n : ℕ) :
    Module.Basis (Fin (Nat.choose 4 n)) ℤ (SingularHomology p.Torus n) :=
  coordinateTorusBasisAlong (periodTorusCircleHomeomorph p) n

@[simp] theorem periodTorusCoordinateBasis_apply (p : PeriodDomain) (n : ℕ)
    (i : Fin (Nat.choose 4 n)) :
    periodTorusCoordinateBasis p n i = periodTorusCoordinateClass p n i :=
  coordinateTorusBasisAlong_apply (periodTorusCircleHomeomorph p) n i

@[simp] theorem periodTorusHomologyEquiv_coordinateClass (p : PeriodDomain) (n : ℕ)
    (i : Fin (Nat.choose 4 n)) :
    periodTorusHomologyEquiv p n (periodTorusCoordinateClass p n i) = Pi.single i 1 :=
  homologyEquiv_coordinateTorusClassAlong (periodTorusCircleHomeomorph p) n i

theorem periodTorusCoordinateClass_span (p : PeriodDomain) (n : ℕ) :
    Submodule.span ℤ (Set.range (periodTorusCoordinateClass p n)) = ⊤ :=
  coordinateTorusClassAlong_span (periodTorusCircleHomeomorph p) n

theorem surjective_of_periodTorusCoordinateClass_mem_range {M : Type*}
    [AddCommGroup M] [Module ℤ M] (p : PeriodDomain) (n : ℕ)
    (f : M →ₗ[ℤ] SingularHomology p.Torus n)
    (hf : ∀ i : Fin (Nat.choose 4 n), periodTorusCoordinateClass p n i ∈ LinearMap.range f) :
    Function.Surjective f :=
  surjective_of_coordinateTorusClassAlong_mem_range (periodTorusCircleHomeomorph p) n f hf

/-- The coordinate-subtorus map is the actual coordinate matrix map followed
by the inverse of the proved period-torus homeomorphism. -/
theorem periodTorusCoordinateMap_matrix (p : PeriodDomain) (n : ℕ)
    (i : Fin (Nat.choose 4 n)) :
    periodTorusCoordinateMap p n i =
      ((periodTorusCircleHomeomorph p).symm : C(ProductTorus 4, p.Torus)).comp
        (torusMatrixMap (coordinateTorusMatrix 4 n i)) := by
  unfold periodTorusCoordinateMap coordinateTorusMapAlong
  rw [coordinateTorusMap_eq_torusMatrixMap]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
