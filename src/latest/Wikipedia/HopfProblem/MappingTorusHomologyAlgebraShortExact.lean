import Wikipedia.HopfProblem.MappingTorusHomologyAlgebra
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The short exact Wang extension obtained from two-arc exactness

Given the actual three range/kernel equalities in the two-arc sequence,
the induced maps form the genuine short exact sequence

`0 → coker(id-F) → N → ker(id-F') → 0`.

The injection sends the class of `a` to `i a`.  The surjection is the
negative first coordinate of the given connecting map.  The quotient and
kernel are the actual Mathlib module quotient and submodule, and the final
short exactness assertion uses `CategoryTheory.ShortComplex.ShortExact`.
No splitting or topological exactness is assumed beyond the stated inputs.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.MappingTorusHomology.Algebra

open PeriodTorusHigherHomology

variable {M N P : Type*}
  [AddCommGroup M] [Module ℤ M]
  [AddCommGroup N] [Module ℤ N]
  [AddCommGroup P] [Module ℤ P]

/-- The inclusion induced from the actual quotient by the Wang difference. -/
def cokernelInclusion (F : M →ₗ[ℤ] M) (i : M →ₗ[ℤ] N)
    (hJ : LinearMap.range (twoArcMap F) = LinearMap.ker (i.comp (pairSumMap M))) :
    (M ⧸ LinearMap.range (difference F)) →ₗ[ℤ] N :=
  intLinearMapOfAddHom ((LinearMap.range (difference F)).liftQ i
    (range_difference_eq_ker F i hJ).le).toAddMonoidHom

@[simp] theorem cokernelInclusion_mk (F : M →ₗ[ℤ] M) (i : M →ₗ[ℤ] N)
    (hJ : LinearMap.range (twoArcMap F) = LinearMap.ker (i.comp (pairSumMap M))) (a : M) :
    cokernelInclusion F i hJ (Submodule.Quotient.mk a) = i a := rfl

theorem cokernelInclusion_injective (F : M →ₗ[ℤ] M) (i : M →ₗ[ℤ] N)
    (hJ : LinearMap.range (twoArcMap F) = LinearMap.ker (i.comp (pairSumMap M))) :
    Function.Injective (cokernelInclusion F i hJ) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := (LinearMap.range (difference F)).mkQ_surjective x
  obtain ⟨b, rfl⟩ := (LinearMap.range (difference F)).mkQ_surjective y
  change i a = i b at hxy
  apply (Submodule.Quotient.eq (LinearMap.range (difference F))).mpr
  rw [range_difference_eq_ker F i hJ]
  change i (a - b) = 0
  rw [map_sub, hxy, sub_self]

theorem cokernelInclusion_range (F : M →ₗ[ℤ] M) (i : M →ₗ[ℤ] N)
    (hJ : LinearMap.range (twoArcMap F) = LinearMap.ker (i.comp (pairSumMap M))) :
    LinearMap.range (cokernelInclusion F i hJ) = LinearMap.range i := by
  ext n
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := (LinearMap.range (difference F)).mkQ_surjective x
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨Submodule.Quotient.mk a, rfl⟩

/-- The signed boundary, with codomain restricted to the actual invariant kernel. -/
def kernelBoundary (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) :
    N →ₗ[ℤ] LinearMap.ker (difference F) :=
  intLinearMapOfAddHom
    { toFun n := ⟨boundary d n, boundary_mem_kernel F d hd n⟩
      map_zero' := by
        apply Subtype.ext
        exact map_zero (boundary d)
      map_add' n m := by
        apply Subtype.ext
        exact map_add (boundary d) n m }

@[simp] theorem kernelBoundary_coe (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) (n : N) :
    (kernelBoundary F d hd n : P) = boundary d n := rfl

theorem kernelBoundary_eq_zero_iff (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) (n : N) :
    kernelBoundary F d hd n = 0 ↔ boundary d n = 0 := by
  constructor
  · intro hn
    exact congrArg Subtype.val hn
  · intro hn
    exact Subtype.ext hn

theorem kernelBoundary_ker (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) :
    LinearMap.ker (kernelBoundary F d hd) = LinearMap.ker (boundary d) := by
  ext n
  exact kernelBoundary_eq_zero_iff F d hd n

theorem kernelBoundary_surjective (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) :
    Function.Surjective (kernelBoundary F d hd) := by
  intro b
  have hb : (b : P) ∈ LinearMap.range (boundary d) := by
    rw [boundary_range F d hd]
    exact b.property
  obtain ⟨n, hn⟩ := hb
  exact ⟨n, Subtype.ext hn⟩

/-- Exactness after passing to the actual cokernel and invariant kernel. -/
theorem cokernelInclusion_range_eq_ker_kernelBoundary
    (F : M →ₗ[ℤ] M) (F' : P →ₗ[ℤ] P) (i : M →ₗ[ℤ] N) (d : N →ₗ[ℤ] (P × P))
    (hJ : LinearMap.range (twoArcMap F) = LinearMap.ker (i.comp (pairSumMap M)))
    (hi : LinearMap.range i = LinearMap.ker d)
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F')) :
    LinearMap.range (cokernelInclusion F i hJ) = LinearMap.ker (kernelBoundary F' d hd) := by
  rw [cokernelInclusion_range, kernelBoundary_ker, boundary_ker F' d hd]
  exact hi

theorem kernelBoundary_comp_cokernelInclusion
    (F : M →ₗ[ℤ] M) (F' : P →ₗ[ℤ] P) (i : M →ₗ[ℤ] N) (d : N →ₗ[ℤ] (P × P))
    (hJ : LinearMap.range (twoArcMap F) = LinearMap.ker (i.comp (pairSumMap M)))
    (hi : LinearMap.range i = LinearMap.ker d)
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F')) :
    (kernelBoundary F' d hd).comp (cokernelInclusion F i hJ) = 0 := by
  apply LinearMap.ext
  intro x
  have hx : cokernelInclusion F i hJ x ∈ LinearMap.range (cokernelInclusion F i hJ) :=
    ⟨x, rfl⟩
  rw [cokernelInclusion_range_eq_ker_kernelBoundary F F' i d hJ hi hd] at hx
  exact LinearMap.mem_ker.mp hx

section Categorical

universe u

variable {M₀ N₀ P₀ : Type u}
  [AddCommGroup M₀] [Module ℤ M₀]
  [AddCommGroup N₀] [Module ℤ N₀]
  [AddCommGroup P₀] [Module ℤ P₀]

/-- The actual module short complex with the prescribed Wang maps. -/
def wangShortComplex
    (F : M₀ →ₗ[ℤ] M₀) (F' : P₀ →ₗ[ℤ] P₀)
    (i : M₀ →ₗ[ℤ] N₀) (d : N₀ →ₗ[ℤ] (P₀ × P₀))
    (hJ : LinearMap.range (twoArcMap F) = LinearMap.ker (i.comp (pairSumMap M₀)))
    (hi : LinearMap.range i = LinearMap.ker d)
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F')) :
    ShortComplex (ModuleCat.{u} ℤ) :=
  ModuleCat.shortComplexOfCompEqZero (cokernelInclusion F i hJ) (kernelBoundary F' d hd)
    (kernelBoundary_comp_cokernelInclusion F F' i d hJ hi hd)

/-- The genuine short exact Wang extension, extracted from the three supplied exactness proofs. -/
theorem wangShortComplex_shortExact
    (F : M₀ →ₗ[ℤ] M₀) (F' : P₀ →ₗ[ℤ] P₀)
    (i : M₀ →ₗ[ℤ] N₀) (d : N₀ →ₗ[ℤ] (P₀ × P₀))
    (hJ : LinearMap.range (twoArcMap F) = LinearMap.ker (i.comp (pairSumMap M₀)))
    (hi : LinearMap.range i = LinearMap.ker d)
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F')) :
    (wangShortComplex F F' i d hJ hi hd).ShortExact := by
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · change Function.Exact (cokernelInclusion F i hJ) (kernelBoundary F' d hd)
    exact LinearMap.exact_iff.mpr
      (cokernelInclusion_range_eq_ker_kernelBoundary F F' i d hJ hi hd).symm
  · exact cokernelInclusion_injective F i hJ
  · exact kernelBoundary_surjective F' d hd

@[simp] theorem wangShortComplex_f_mk
    (F : M₀ →ₗ[ℤ] M₀) (F' : P₀ →ₗ[ℤ] P₀)
    (i : M₀ →ₗ[ℤ] N₀) (d : N₀ →ₗ[ℤ] (P₀ × P₀))
    (hJ : LinearMap.range (twoArcMap F) = LinearMap.ker (i.comp (pairSumMap M₀)))
    (hi : LinearMap.range i = LinearMap.ker d)
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F')) (a : M₀) :
    (wangShortComplex F F' i d hJ hi hd).f (Submodule.Quotient.mk a) = i a := rfl

@[simp] theorem wangShortComplex_g_coe
    (F : M₀ →ₗ[ℤ] M₀) (F' : P₀ →ₗ[ℤ] P₀)
    (i : M₀ →ₗ[ℤ] N₀) (d : N₀ →ₗ[ℤ] (P₀ × P₀))
    (hJ : LinearMap.range (twoArcMap F) = LinearMap.ker (i.comp (pairSumMap M₀)))
    (hi : LinearMap.range i = LinearMap.ker d)
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F')) (n : N₀) :
    @Subtype.val P₀ (fun p => p ∈ LinearMap.ker (difference F'))
      ((wangShortComplex F F' i d hJ hi hd).g n) =
      -(d n).1 := rfl

end Categorical

end Wikipedia.HopfProblem.MappingTorusHomology.Algebra
