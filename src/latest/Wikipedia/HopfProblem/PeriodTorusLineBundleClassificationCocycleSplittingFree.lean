import Mathlib.LinearAlgebra.StdBasis

/-!
# Additive sections over a finite free abelian group

A surjective additive homomorphism onto a finite power of `ℤ` has an additive
section: lift the standard basis vectors and take integer linear combinations.
-/

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open scoped BigOperators

/-- A surjection onto a finite free abelian group admits an additive section. -/
theorem exists_additive_section_int_pi {ι A : Type*} [Finite ι] [AddCommGroup A]
    (f : A →+ (ι → ℤ)) (hf : Function.Surjective f) :
    ∃ s : (ι → ℤ) →+ A, f.comp s = AddMonoidHom.id _ := by
  classical
  let _ := Fintype.ofFinite ι
  let b : ι → A := fun i => Classical.choose (hf (Pi.single i 1))
  have hb (i : ι) : f (b i) = Pi.single i 1 :=
    Classical.choose_spec (hf (Pi.single i 1))
  let s : (ι → ℤ) →+ A :=
    { toFun := fun x => ∑ i, x i • b i
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [Pi.add_apply, add_zsmul, Finset.sum_add_distrib] }
  refine ⟨s, ?_⟩
  apply AddMonoidHom.ext
  intro x
  funext i
  change f (∑ j, x j • b j) i = x i
  simp only [map_sum, map_zsmul, hb, Finset.sum_apply, zsmul_eq_mul]
  simp [Pi.single_apply]

/-- The rank-four version used for the period lattice. -/
theorem exists_additive_section_int_four {A : Type*} [AddCommGroup A]
    (f : A →+ (Fin 4 → ℤ)) (hf : Function.Surjective f) :
    ∃ s : (Fin 4 → ℤ) →+ A, f.comp s = AddMonoidHom.id _ :=
  exists_additive_section_int_pi f hf

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
