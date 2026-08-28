import Wikipedia.HopfProblem.CuspCentralHomologyMiddleAlgebra

/-!
# Exact integer quotients and splitting by an actual section

A surjective integer-valued map vanishing on the kernel of an exact
integer quotient differs from that quotient by multiplication by a unit.
Its kernel is therefore exactly the same integral submodule.

Given an actual section of such a quotient, the final splitting has
forward map `(a,t) ↦ i a + s t`. Its second inverse coordinate is the
supplied quotient map, and both summands retain their specified maps.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology

open PeriodTorusHigherHomology

section IntegerQuotient

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
  [Module ℤ A] [Module ℤ B]

/-- A map killing the exact kernel is multiplication by one integer
on the supplied quotient coordinate. -/
theorem integerExtension_quotient_factorization
    (i : A →ₗ[ℤ] B) (d p : B →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d)
    (hpi : ∀ a, p (i a) = 0) (x : B) :
    p x = d x * p (integerExtensionLift d hd) := by
  calc
    p x = p ((splitIntegerExtensionEquiv i d hi hd hexact).symm
        (splitIntegerExtensionEquiv i d hi hd hexact x)) := by
      rw [LinearEquiv.symm_apply_apply]
    _ = d x * p (integerExtensionLift d hd) := by
      rw [splitIntegerExtensionEquiv_symm_apply, map_add, hpi, map_zsmul,
        splitIntegerExtensionEquiv_snd]
      simp only [zero_add, zsmul_eq_mul, Int.cast_id]

/-- Surjectivity forces the comparison coefficient to be a unit over
the integers, not merely nonzero over the rationals. -/
theorem integerExtension_quotient_coefficient_isUnit
    (i : A →ₗ[ℤ] B) (d p : B →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d)
    (hpi : ∀ a, p (i a) = 0) (hp : Function.Surjective p) :
    IsUnit (p (integerExtensionLift d hd)) := by
  obtain ⟨x, hx⟩ := hp 1
  have he : d x * p (integerExtensionLift d hd) = 1 :=
    (integerExtension_quotient_factorization i d p hi hd hexact hpi x).symm.trans hx
  exact ⟨⟨p (integerExtensionLift d hd), d x, (mul_comm _ _).trans he, he⟩, rfl⟩

/-- Replacing an exact integer quotient by a surjection annihilating
the same included summand preserves the exact integral kernel. -/
theorem integerExtension_replaceQuotient
    (i : A →ₗ[ℤ] B) (d p : B →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d)
    (hpi : ∀ a, p (i a) = 0) (hp : Function.Surjective p) :
    LinearMap.range i = LinearMap.ker p := by
  have hc : p (integerExtensionLift d hd) ≠ 0 :=
    (integerExtension_quotient_coefficient_isUnit i d p hi hd hexact hpi hp).ne_zero
  rw [hexact]
  ext x
  change d x = 0 ↔ p x = 0
  rw [integerExtension_quotient_factorization i d p hi hd hexact hpi x,
    mul_eq_zero]
  simp only [hc, or_false]

end IntegerQuotient

section ActualSection

variable {A B T : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup T]
  [Module ℤ A] [Module ℤ B] [Module ℤ T]

/-- The supplied sum map with the ambient integer-module structures. -/
def actualSectionAssembly (i : A →ₗ[ℤ] B) (s : T →ₗ[ℤ] B) : (A × T) →ₗ[ℤ] B :=
  intLinearMapOfAddHom (i.coprod s).toAddMonoidHom

@[simp] theorem actualSectionAssembly_apply (i : A →ₗ[ℤ] B) (s : T →ₗ[ℤ] B)
    (az : A × T) : actualSectionAssembly i s az = i az.1 + s az.2 := rfl

/-- The actual quotient reads the section coordinate of the sum map. -/
theorem coprod_projection_of_exact_section
    (i : A →ₗ[ℤ] B) (p : B →ₗ[ℤ] T) (s : T →ₗ[ℤ] B)
    (hexact : LinearMap.range i = LinearMap.ker p)
    (hps : ∀ t, p (s t) = t) (az : A × T) :
    p (i.coprod s az) = az.2 := by
  have hi : p (i az.1) = 0 := by
    have ha : i az.1 ∈ LinearMap.range i := ⟨az.1, rfl⟩
    rw [hexact] at ha
    exact ha
  rw [LinearMap.coprod_apply, map_add, hi, hps, zero_add]

theorem coprod_injective_of_exact_section
    (i : A →ₗ[ℤ] B) (p : B →ₗ[ℤ] T) (s : T →ₗ[ℤ] B)
    (hi : Function.Injective i) (hexact : LinearMap.range i = LinearMap.ker p)
    (hps : ∀ t, p (s t) = t) : Function.Injective (i.coprod s) := by
  intro az au h
  have hsnd : az.2 = au.2 := by
    have hp := congrArg p h
    simpa only [coprod_projection_of_exact_section i p s hexact hps] using hp
  apply Prod.ext _ hsnd
  apply hi
  apply add_right_cancel (b := s au.2)
  simpa only [LinearMap.coprod_apply, hsnd] using h

theorem coprod_surjective_of_exact_section
    (i : A →ₗ[ℤ] B) (p : B →ₗ[ℤ] T) (s : T →ₗ[ℤ] B)
    (hexact : LinearMap.range i = LinearMap.ker p)
    (hps : ∀ t, p (s t) = t) : Function.Surjective (i.coprod s) := by
  intro b
  have hk : b - s (p b) ∈ LinearMap.ker p := by
    change p (b - s (p b)) = 0
    rw [map_sub, hps, sub_self]
  rw [← hexact] at hk
  obtain ⟨a, ha⟩ := hk
  refine ⟨(a, p b), ?_⟩
  change i a + s (p b) = b
  rw [ha, sub_add_cancel]

/-- The splitting uses the supplied actual section, not a newly chosen
lift of the quotient generator. -/
def splitFromActualSection
    (i : A →ₗ[ℤ] B) (p : B →ₗ[ℤ] T) (s : T →ₗ[ℤ] B)
    (hi : Function.Injective i) (hexact : LinearMap.range i = LinearMap.ker p)
    (hps : ∀ t, p (s t) = t) : (A × T) ≃ₗ[ℤ] B :=
  LinearEquiv.ofBijective (actualSectionAssembly i s)
    ⟨coprod_injective_of_exact_section i p s hi hexact hps,
      coprod_surjective_of_exact_section i p s hexact hps⟩

variable (i : A →ₗ[ℤ] B) (p : B →ₗ[ℤ] T) (s : T →ₗ[ℤ] B)
  (hi : Function.Injective i) (hexact : LinearMap.range i = LinearMap.ker p)
  (hps : ∀ t, p (s t) = t)

@[simp] theorem splitFromActualSection_toLinearMap :
    (splitFromActualSection i p s hi hexact hps).toLinearMap =
      actualSectionAssembly i s := rfl

@[simp] theorem splitFromActualSection_apply (az : A × T) :
    splitFromActualSection i p s hi hexact hps az = i az.1 + s az.2 := rfl

@[simp] theorem splitFromActualSection_projection (az : A × T) :
    p (splitFromActualSection i p s hi hexact hps az) = az.2 :=
  coprod_projection_of_exact_section i p s hexact hps az

@[simp] theorem splitFromActualSection_symm_snd (b : B) :
    ((splitFromActualSection i p s hi hexact hps).symm b).2 = p b := by
  have he := splitFromActualSection_projection i p s hi hexact hps
    ((splitFromActualSection i p s hi hexact hps).symm b)
  rw [LinearEquiv.apply_symm_apply] at he
  exact he.symm

@[simp] theorem splitFromActualSection_apply_inl (a : A) :
    splitFromActualSection i p s hi hexact hps (a, 0) = i a := by
  rw [splitFromActualSection_apply, map_zero, add_zero]

@[simp] theorem splitFromActualSection_apply_inr (t : T) :
    splitFromActualSection i p s hi hexact hps (0, t) = s t := by
  rw [splitFromActualSection_apply, map_zero, zero_add]

@[simp] theorem splitFromActualSection_symm_inclusion (a : A) :
    (splitFromActualSection i p s hi hexact hps).symm (i a) = (a, 0) := by
  apply (splitFromActualSection i p s hi hexact hps).injective
  rw [LinearEquiv.apply_symm_apply, splitFromActualSection_apply_inl]

@[simp] theorem splitFromActualSection_symm_section (t : T) :
    (splitFromActualSection i p s hi hexact hps).symm (s t) = (0, t) := by
  apply (splitFromActualSection i p s hi hexact hps).injective
  rw [LinearEquiv.apply_symm_apply, splitFromActualSection_apply_inr]

end ActualSection

end Wikipedia.HopfProblem.CuspCentralHomology
