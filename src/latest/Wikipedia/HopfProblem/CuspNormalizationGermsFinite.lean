import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.BigOperators.Pi

/-!
# Finite integral extension from surjective branch restrictions

Let a ring map land in a finite product of rings, and suppose every
coordinate restriction is surjective. The coordinate idempotents generate
the product as a module over the actual image subring. Consequently the
actual image inclusion is a finite integral extension.

This is a general algebraic statement: the factors may in particular be
analytic germ rings. No polynomial model, integral-closedness hypothesis,
or assertion that the image already contains the idempotents is used.
-/

noncomputable section

open Function Set

namespace Wikipedia.HopfProblem.CuspNormalization.GermsFinite

universe u v w

variable {I : Type u} (B : I → Type v) [∀ i, CommRing (B i)]

/-- The coordinate idempotent in the actual product ring. -/
def coordinateIdempotent (i : I) : ∀ j, B j := by
  classical
  exact Pi.single i 1

@[simp] theorem coordinateIdempotent_self (i : I) :
    coordinateIdempotent B i i = 1 := by
  classical
  simp [coordinateIdempotent]

@[simp] theorem coordinateIdempotent_other {i j : I} (h : j ≠ i) :
    coordinateIdempotent B i j = 0 := by
  classical
  simp [coordinateIdempotent, h]

/-- These are idempotents in the ambient product, whether or not they
belong to the image subring. -/
theorem coordinateIdempotent_mul_self (i : I) :
    coordinateIdempotent B i * coordinateIdempotent B i = coordinateIdempotent B i := by
  classical
  ext j
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

theorem coordinateIdempotent_mul_of_ne {i j : I} (h : i ≠ j) :
    coordinateIdempotent B i * coordinateIdempotent B j = 0 := by
  classical
  ext k
  by_cases hk : k = i
  · subst k
    simp [h]
  · simp [hk]

/-- The coordinate idempotents partition the identity of the product. -/
theorem sum_coordinateIdempotents [Fintype I] :
    ∑ i, coordinateIdempotent B i = 1 := by
  classical
  exact Finset.univ_sum_single (fun i => (1 : B i))

/-- Coordinatewise surjectivity is enough for the coordinate idempotents
to span over the actual subring. It does not require product surjectivity. -/
theorem subring_span_coordinateIdempotents_eq_top [Finite I]
    (A : Subring (∀ i, B i))
    (hsurj : ∀ i, Surjective (fun a : A => (a : ∀ j, B j) i)) :
    Submodule.span A (range (coordinateIdempotent B)) = ⊤ := by
  classical
  rw [Submodule.eq_top_iff']
  intro b
  induction b using Pi.single_induction with
  | zero => exact Submodule.zero_mem _
  | add f g hf hg => exact Submodule.add_mem _ hf hg
  | single i b =>
      obtain ⟨a, ha⟩ := hsurj i b
      have hmem := (Submodule.span A (range (coordinateIdempotent B))).smul_mem a
        (Submodule.subset_span (mem_range_self i))
      have he : a • coordinateIdempotent B i = Pi.single i b := by
        ext j
        change (a : ∀ j, B j) j * coordinateIdempotent B i j = Pi.single i b j
        by_cases h : j = i
        · subst j
          simp [ha]
        · simp [h]
      exact he ▸ hmem

/-- A finite subdirect product is finite as a module over its given
subring, with the natural scalar multiplication by that inclusion. -/
theorem subring_moduleFinite [Finite I] (A : Subring (∀ i, B i))
    (hsurj : ∀ i, Surjective (fun a : A => (a : ∀ j, B j) i)) :
    Module.Finite A (∀ i, B i) := by
  rw [Module.finite_def, Submodule.fg_def]
  exact ⟨range (coordinateIdempotent B), finite_range _,
    subring_span_coordinateIdempotents_eq_top B A hsurj⟩

/-- The actual subring inclusion is integral by finite generation. -/
theorem subring_isIntegral [Finite I] (A : Subring (∀ i, B i))
    (hsurj : ∀ i, Surjective (fun a : A => (a : ∀ j, B j) i)) :
    Algebra.IsIntegral A (∀ i, B i) := by
  let := subring_moduleFinite B A hsurj
  infer_instance

variable {B} {R : Type w} [CommRing R] (ρ : R →+* ∀ i, B i)

/-- The actual restriction to one branch factor. -/
def coordinateMap (i : I) : R →+* B i := (Pi.evalRingHom B i).comp ρ

@[simp] theorem coordinateMap_apply (i : I) (r : R) :
    coordinateMap ρ i r = ρ r i := rfl

/-- Coordinate surjectivity passes from the original ring to its actual
image without imposing injectivity of the original restriction map. -/
theorem range_coordinate_surjective
    (hsurj : ∀ i, Surjective (coordinateMap ρ i)) (i : I) :
    Surjective (fun a : ρ.range => (a : ∀ j, B j) i) := by
  intro b
  obtain ⟨r, hr⟩ := hsurj i b
  exact ⟨ρ.rangeRestrict r, hr⟩

/-- The explicit generating family for the module over the actual image. -/
theorem span_coordinateIdempotents_eq_top [Finite I]
    (hsurj : ∀ i, Surjective (coordinateMap ρ i)) :
    Submodule.span ρ.range (range (coordinateIdempotent B)) = ⊤ :=
  subring_span_coordinateIdempotents_eq_top B ρ.range
    (range_coordinate_surjective ρ hsurj)

/-- The product is a finite module over the actual ring-homomorphism image. -/
theorem moduleFinite_range [Finite I]
    (hsurj : ∀ i, Surjective (coordinateMap ρ i)) :
    Module.Finite ρ.range (∀ i, B i) :=
  subring_moduleFinite B ρ.range (range_coordinate_surjective ρ hsurj)

/-- The natural inclusion of the actual image into the product is integral. -/
theorem isIntegral_range [Finite I]
    (hsurj : ∀ i, Surjective (coordinateMap ρ i)) :
    Algebra.IsIntegral ρ.range (∀ i, B i) :=
  subring_isIntegral B ρ.range (range_coordinate_surjective ρ hsurj)

/-- The same finite-extension statement explicitly names the literal
subring-inclusion ring homomorphism. -/
theorem range_inclusion_finite [Finite I]
    (hsurj : ∀ i, Surjective (coordinateMap ρ i)) : ρ.range.subtype.Finite := by
  change (algebraMap ρ.range (∀ i, B i)).Finite
  exact RingHom.finite_algebraMap.mpr (moduleFinite_range ρ hsurj)

/-- Integrality for the literal image-inclusion ring homomorphism. -/
theorem range_inclusion_isIntegral [Finite I]
    (hsurj : ∀ i, Surjective (coordinateMap ρ i)) : ρ.range.subtype.IsIntegral :=
  (range_inclusion_finite ρ hsurj).to_isIntegral

/-- The first isomorphism theorem identifies the quotient by the actual
restriction kernel with the actual image ring. -/
def quotientKerEquivImage : R ⧸ RingHom.ker ρ ≃+* ρ.range :=
  ρ.quotientKerEquivRange

/-- The total restriction kernel is the intersection of the branch
restriction kernels, for arbitrary (not necessarily finite) index sets. -/
theorem ker_eq_iInf_coordinate_ker :
    RingHom.ker ρ = ⨅ i, RingHom.ker (coordinateMap ρ i) := by
  ext r
  simp [RingHom.mem_ker, funext_iff]

end Wikipedia.HopfProblem.CuspNormalization.GermsFinite
