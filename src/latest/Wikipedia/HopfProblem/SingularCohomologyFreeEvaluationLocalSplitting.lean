import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluation
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Local splittings for integral cohomology evaluation

A linear map with projective image has a split kernel.  This is the
degreewise algebra needed for universal coefficients: it concerns the
actual chain differential and does not require a global homology
decomposition or a choice of chain homotopy equivalence.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SingularCohomologyFree.LocalEvaluation

section Algebra

variable {R : Type*} [Ring R]
  {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]

/-- A projective codomain supplies a linear section of an actual surjection. -/
theorem exists_section (q : M →ₗ[R] N) [Module.Projective R N]
    (hq : Function.Surjective q) :
    ∃ s : N →ₗ[R] M, ∀ y, q (s y) = y := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q
    (LinearMap.id : N →ₗ[R] N) hq
  exact ⟨s, fun y => LinearMap.congr_fun hs y⟩

/-- Projectivity of the image, not of either ambient module, splits the kernel. -/
theorem exists_kernel_retraction (d : M →ₗ[R] N)
    [Module.Projective R (LinearMap.range d)] :
    ∃ r : M →ₗ[R] LinearMap.ker d,
      ∀ z : LinearMap.ker d, r z = z := by
  obtain ⟨s, hs⟩ := exists_section d.rangeRestrict d.surjective_rangeRestrict
  let r₀ : M →ₗ[R] M := LinearMap.id - s.comp d.rangeRestrict
  have hr₀ (x : M) : r₀ x ∈ LinearMap.ker d := by
    change d (x - s (d.rangeRestrict x)) = 0
    rw [map_sub]
    have h := congrArg Subtype.val (hs (d.rangeRestrict x))
    change d (s (d.rangeRestrict x)) = d x at h
    rw [h, sub_self]
  refine ⟨r₀.codRestrict (LinearMap.ker d) hr₀, ?_⟩
  intro z
  apply Subtype.ext
  change z.val - s (d.rangeRestrict z.val) = z.val
  have hz : d.rangeRestrict z.val = 0 := Subtype.ext z.property
  rw [hz, map_zero, sub_zero]

/-- Every linear functional on a split kernel extends to the ambient module. -/
theorem exists_extension_from_kernel (d : M →ₗ[R] N)
    [Module.Projective R (LinearMap.range d)]
    (φ : LinearMap.ker d →ₗ[R] P) :
    ∃ ψ : M →ₗ[R] P, ∀ z : LinearMap.ker d, ψ z = φ z := by
  obtain ⟨r, hr⟩ := exists_kernel_retraction d
  exact ⟨φ.comp r, fun z => congrArg φ (hr z)⟩

/-- A functional annihilating the kernel factors through the actual image. -/
theorem exists_factor_through_range (d : M →ₗ[R] N) (φ : M →ₗ[R] P)
    (hφ : LinearMap.ker d ≤ LinearMap.ker φ) :
    ∃ ψ : LinearMap.range d →ₗ[R] P, ψ.comp d.rangeRestrict = φ := by
  let ψ := ((LinearMap.ker d).liftQ φ hφ).comp d.quotKerEquivRange.symm.toLinearMap
  refine ⟨ψ, ?_⟩
  ext x
  change (LinearMap.ker d).liftQ φ hφ
    (d.quotKerEquivRange.symm ⟨d x, LinearMap.mem_range_self d x⟩) = φ x
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

end Algebra

open CategoryTheory
open SingularMayerVietoris.ModuleHomology

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)

/-- The outgoing image relevant to a degreewise evaluation splitting. -/
abbrev OutgoingImage := LinearMap.range (K.d n ((ComplexShape.down ℕ).next n)).hom

instance outgoingImageModule : Module ℤ (OutgoingImage K n) := (OutgoingImage K n).module

/-- The genuine cycle inclusion splits when the outgoing boundary image is projective. -/
theorem exists_cycle_retraction [Module.Projective ℤ (OutgoingImage K n)] :
    ∃ r : K.X n →ₗ[ℤ] Cycle K n, ∀ z : Cycle K n, r z = z :=
  exists_kernel_retraction (K.d n ((ComplexShape.down ℕ).next n)).hom

/-- A local extension lemma for functionals on the genuine cycles. -/
theorem exists_extension_from_cycles [Module.Projective ℤ (OutgoingImage K n)]
    (φ : Cycle K n →ₗ[ℤ] ℤ) :
    ∃ ψ : K.X n →ₗ[ℤ] ℤ, ∀ z : Cycle K n, ψ z = φ z :=
  exists_extension_from_kernel (K.d n ((ComplexShape.down ℕ).next n)).hom φ

end Wikipedia.HopfProblem.SingularCohomologyFree.LocalEvaluation
