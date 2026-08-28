import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCoordinateAlgebra
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Projective

/-!
# Integral splitting with a free right endpoint

A surjection onto a free integral module has a linear section: this follows
from projectivity of free modules, rather than from a supplied splitting.
For an actual short exact sequence, adding the original left injection to
this constructed section gives a linear equivalence with the middle module.
Its inverse preserves both the original injection and the original projection.

No finite-generation hypothesis is needed for the splitting itself.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamilyHomologySplitting

open PeriodTorusHigherHomology

variable {L M K : Type*} [AddCommGroup L] [AddCommGroup M] [AddCommGroup K]
  [Module ℤ L] [Module ℤ M] [Module ℤ K] [Module.Free ℤ K]

/-- A linear section constructed by lifting the identity of the free right endpoint. -/
def freeRightSection (g : M →ₗ[ℤ] K) (hg : Function.Surjective g) : K →ₗ[ℤ] M :=
  Classical.choose (Module.projective_lifting_property g
    (LinearMap.id : K →ₗ[ℤ] K) hg)

/-- The constructed section is a right inverse as an actual integral linear map. -/
theorem freeRightSection_comp (g : M →ₗ[ℤ] K) (hg : Function.Surjective g) :
    g.comp (freeRightSection g hg) = LinearMap.id :=
  Classical.choose_spec (Module.projective_lifting_property g
    (LinearMap.id : K →ₗ[ℤ] K) hg)

@[simp] theorem freeRightSection_rightInverse (g : M →ₗ[ℤ] K)
    (hg : Function.Surjective g) (k : K) : g (freeRightSection g hg k) = k :=
  LinearMap.congr_fun (freeRightSection_comp g hg) k

/-- Addition of the original injection and the constructed linear section. -/
def freeRightSumMap (f : L →ₗ[ℤ] M) (g : M →ₗ[ℤ] K) (hg : Function.Surjective g) :
    (L × K) →ₗ[ℤ] M :=
  intLinearMapOfAddHom
    { toFun x := f x.1 + freeRightSection g hg x.2
      map_zero' := by simp
      map_add' x y := by
        dsimp
        rw [map_add, map_add]
        exact add_add_add_comm _ _ _ _ }

@[simp] theorem freeRightSumMap_apply (f : L →ₗ[ℤ] M) (g : M →ₗ[ℤ] K)
    (hg : Function.Surjective g) (x : L × K) :
    freeRightSumMap f g hg x = f x.1 + freeRightSection g hg x.2 := rfl

/-- Exactness and injectivity make the constructed sum map injective. -/
theorem freeRightSumMap_injective (f : L →ₗ[ℤ] M) (g : M →ₗ[ℤ] K)
    (hex : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    Function.Injective (freeRightSumMap f g hg) := by
  rintro ⟨a, k⟩ ⟨a', k'⟩ h
  change f a + freeRightSection g hg k = f a' + freeRightSection g hg k' at h
  have hk : k = k' := by
    have h' := congrArg g h
    simpa only [map_add, hex.apply_apply_eq_zero, freeRightSection_rightInverse,
      zero_add] using h'
  subst k'
  exact Prod.ext (hf (add_right_cancel h)) rfl

/-- Subtracting the constructed section puts each middle element in the
original injection image, proving surjectivity of the sum map. -/
theorem freeRightSumMap_surjective (f : L →ₗ[ℤ] M) (g : M →ₗ[ℤ] K)
    (hex : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Surjective (freeRightSumMap f g hg) := by
  intro m
  have hm : g (m - freeRightSection g hg (g m)) = 0 := by
    rw [map_sub, freeRightSection_rightInverse, sub_self]
  obtain ⟨a, ha⟩ := (hex _).mp hm
  refine ⟨(a, g m), ?_⟩
  rw [freeRightSumMap_apply, ha, sub_add_cancel]

/-- An actual short exact sequence with a free right endpoint splits
integrally. The section is derived from freeness, not assumed. -/
def freeRightSplitEquiv (f : L →ₗ[ℤ] M) (g : M →ₗ[ℤ] K)
    (hex : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    M ≃ₗ[ℤ] (L × K) :=
  (LinearEquiv.ofBijective (freeRightSumMap f g hg)
    ⟨freeRightSumMap_injective f g hex hf hg,
      freeRightSumMap_surjective f g hex hg⟩).symm

variable (f : L →ₗ[ℤ] M) (g : M →ₗ[ℤ] K)
  (hex : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g)

/-- The inverse equivalence uses the original injection and the constructed section. -/
@[simp] theorem freeRightSplitEquiv_symm_apply (x : L × K) :
    (freeRightSplitEquiv f g hex hf hg).symm x =
      f x.1 + freeRightSection g hg x.2 := rfl

/-- The original injection becomes exactly the first-factor inclusion. -/
@[simp] theorem freeRightSplitEquiv_inclusion (a : L) :
    freeRightSplitEquiv f g hex hf hg (f a) = (a, 0) := by
  apply (freeRightSplitEquiv f g hex hf hg).symm.injective
  rw [LinearEquiv.symm_apply_apply, freeRightSplitEquiv_symm_apply, map_zero, add_zero]

/-- The constructed section becomes exactly the second-factor inclusion. -/
@[simp] theorem freeRightSplitEquiv_section (k : K) :
    freeRightSplitEquiv f g hex hf hg (freeRightSection g hg k) = (0, k) := by
  apply (freeRightSplitEquiv f g hex hf hg).symm.injective
  rw [LinearEquiv.symm_apply_apply, freeRightSplitEquiv_symm_apply, map_zero, zero_add]

/-- The inverse equivalence retains the original projection on the second factor. -/
@[simp] theorem freeRightSplitEquiv_symm_projection (x : L × K) :
    g ((freeRightSplitEquiv f g hex hf hg).symm x) = x.2 := by
  rw [freeRightSplitEquiv_symm_apply, map_add, hex.apply_apply_eq_zero,
    freeRightSection_rightInverse, zero_add]

/-- The second coordinate of the equivalence is the original outgoing map. -/
@[simp] theorem freeRightSplitEquiv_snd (m : M) :
    (freeRightSplitEquiv f g hex hf hg m).2 = g m := by
  have h := congrArg g ((freeRightSplitEquiv f g hex hf hg).symm_apply_apply m)
  rw [freeRightSplitEquiv_symm_projection] at h
  exact h

@[simp] theorem freeRightSplitEquiv_symm_inl (a : L) :
    (freeRightSplitEquiv f g hex hf hg).symm (a, 0) = f a := by
  rw [freeRightSplitEquiv_symm_apply, map_zero, add_zero]

@[simp] theorem freeRightSplitEquiv_symm_inr (k : K) :
    (freeRightSplitEquiv f g hex hf hg).symm (0, k) = freeRightSection g hg k := by
  rw [freeRightSplitEquiv_symm_apply, map_zero, zero_add]

end Wikipedia.HopfProblem.TrianglePeriodFamilyHomologySplitting
