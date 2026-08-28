import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCoordinateAlgebra

/-!
# Algebra for the middle-degree Mayer–Vietoris calculation

An exact extension with quotient `ℤ` splits by choosing a lift of `1`.
The resulting equivalence is constructed explicitly from the map
`(a, z) ↦ i a + z • b`; no splitting or projectivity hypothesis is used.

The second calculation removes a summand killed by a surjective signed
inclusion. It identifies the injective remaining summand and proves that
its image is the image of the original map on the entire product.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology

open PeriodTorusHigherHomology

section IntegerExtension

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
  [Module ℤ A] [Module ℤ B]

/-- A chosen lift of the generator of the integer quotient. -/
def integerExtensionLift (d : B →ₗ[ℤ] ℤ) (hd : Function.Surjective d) : B :=
  Classical.choose (hd 1)

@[simp] theorem integerExtensionLift_spec (d : B →ₗ[ℤ] ℤ)
    (hd : Function.Surjective d) :
    d (integerExtensionLift d hd) = 1 :=
  Classical.choose_spec (hd 1)

/-- The explicit map assembling the kernel coordinate and an integer lift. -/
def integerExtensionAssembly (i : A →ₗ[ℤ] B) (b : B) : (A × ℤ) →ₗ[ℤ] B :=
  intLinearMapOfAddHom
    { toFun az := i az.1 + az.2 • b
      map_zero' := by simp only [Prod.fst_zero, Prod.snd_zero, map_zero, zero_smul,
        add_zero]
      map_add' az aw := by
        change i (az.1 + aw.1) + (az.2 + aw.2) • b =
          (i az.1 + az.2 • b) + (i aw.1 + aw.2 • b)
        rw [map_add, add_zsmul]
        exact add_add_add_comm _ _ _ _ }

@[simp] theorem integerExtensionAssembly_apply (i : A →ₗ[ℤ] B) (b : B)
    (az : A × ℤ) :
    integerExtensionAssembly i b az = i az.1 + az.2 • b := rfl

theorem integerExtension_boundary_inclusion (i : A →ₗ[ℤ] B) (d : B →ₗ[ℤ] ℤ)
    (hexact : LinearMap.range i = LinearMap.ker d) (a : A) :
    d (i a) = 0 := by
  have ha : i a ∈ LinearMap.range i := ⟨a, rfl⟩
  rw [hexact] at ha
  exact ha

/-- The quotient map reads the integer coordinate of the assembly. -/
theorem integerExtensionAssembly_boundary (i : A →ₗ[ℤ] B) (d : B →ₗ[ℤ] ℤ)
    (hexact : LinearMap.range i = LinearMap.ker d)
    (b : B) (hb : d b = 1) (az : A × ℤ) :
    d (integerExtensionAssembly i b az) = az.2 := by
  rw [integerExtensionAssembly_apply, map_add, map_zsmul,
    integerExtension_boundary_inclusion i d hexact, hb, zero_add]
  simp

theorem integerExtensionAssembly_injective (i : A →ₗ[ℤ] B) (d : B →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hexact : LinearMap.range i = LinearMap.ker d)
    (b : B) (hb : d b = 1) :
    Function.Injective (integerExtensionAssembly i b) := by
  intro az aw h
  have hsnd : az.2 = aw.2 := by
    have hd := congrArg d h
    simpa only [integerExtensionAssembly_boundary i d hexact b hb] using hd
  apply Prod.ext _ hsnd
  apply hi
  apply add_right_cancel (b := aw.2 • b)
  simpa only [integerExtensionAssembly_apply, hsnd] using h

theorem integerExtensionAssembly_surjective (i : A →ₗ[ℤ] B) (d : B →ₗ[ℤ] ℤ)
    (hexact : LinearMap.range i = LinearMap.ker d) (b : B) (hb : d b = 1) :
    Function.Surjective (integerExtensionAssembly i b) := by
  intro y
  have hk : y - d y • b ∈ LinearMap.ker d := by
    change d (y - d y • b) = 0
    rw [map_sub, map_zsmul, hb]
    simp
  rw [← hexact] at hk
  obtain ⟨a, ha⟩ := hk
  refine ⟨(a, d y), ?_⟩
  change i a + d y • b = y
  rw [ha, sub_add_cancel]

/-- Every exact integer-quotient extension splits, using an actual lift of `1`. -/
def splitIntegerExtensionEquiv (i : A →ₗ[ℤ] B) (d : B →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) : B ≃ₗ[ℤ] (A × ℤ) :=
  (LinearEquiv.ofBijective (integerExtensionAssembly i (integerExtensionLift d hd))
    ⟨integerExtensionAssembly_injective i d hi hexact
        (integerExtensionLift d hd) (integerExtensionLift_spec d hd),
      integerExtensionAssembly_surjective i d hexact
        (integerExtensionLift d hd) (integerExtensionLift_spec d hd)⟩).symm

variable (i : A →ₗ[ℤ] B) (d : B →ₗ[ℤ] ℤ)
  (hi : Function.Injective i) (hd : Function.Surjective d)
  (hexact : LinearMap.range i = LinearMap.ker d)

@[simp] theorem splitIntegerExtensionEquiv_symm_apply (az : A × ℤ) :
    (splitIntegerExtensionEquiv i d hi hd hexact).symm az =
      i az.1 + az.2 • integerExtensionLift d hd := rfl

/-- The second splitting coordinate is precisely the supplied quotient map. -/
@[simp] theorem splitIntegerExtensionEquiv_snd (b : B) :
    (splitIntegerExtensionEquiv i d hi hd hexact b).2 = d b := by
  have h := integerExtensionAssembly_boundary i d hexact
    (integerExtensionLift d hd) (integerExtensionLift_spec d hd)
    (splitIntegerExtensionEquiv i d hi hd hexact b)
  change d ((splitIntegerExtensionEquiv i d hi hd hexact).symm
    (splitIntegerExtensionEquiv i d hi hd hexact b)) = _ at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h.symm

@[simp] theorem splitIntegerExtensionEquiv_apply_inclusion (a : A) :
    splitIntegerExtensionEquiv i d hi hd hexact (i a) = (a, 0) := by
  apply (splitIntegerExtensionEquiv i d hi hd hexact).symm.injective
  rw [LinearEquiv.symm_apply_apply, splitIntegerExtensionEquiv_symm_apply]
  simp only [zero_smul, add_zero]

@[simp] theorem splitIntegerExtensionEquiv_symm_apply_inl (a : A) :
    (splitIntegerExtensionEquiv i d hi hd hexact).symm (a, 0) = i a := by
  rw [splitIntegerExtensionEquiv_symm_apply]
  simp only [zero_smul, add_zero]

@[simp] theorem splitIntegerExtensionEquiv_apply_lift :
    splitIntegerExtensionEquiv i d hi hd hexact (integerExtensionLift d hd) =
      (0, 1) := by
  apply (splitIntegerExtensionEquiv i d hi hd hexact).symm.injective
  rw [LinearEquiv.symm_apply_apply, splitIntegerExtensionEquiv_symm_apply]
  simp only [map_zero, one_smul, zero_add]

end IntegerExtension

section SignedSummand

variable {A B C E : Type*} [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [AddCommGroup E]
  [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ E]

/-- The signed inclusion of a map into the second summand. -/
def signedRightMap (A : Type*) [AddCommGroup A] [Module ℤ A]
    (p : E →ₗ[ℤ] C) : E →ₗ[ℤ] (A × C) :=
  intLinearMapOfAddHom
    { toFun e := (0, -p e)
      map_zero' := by simp only [map_zero, neg_zero, Prod.mk_zero_zero]
      map_add' e f := by
        apply Prod.ext
        · exact (add_zero 0).symm
        · exact (congrArg Neg.neg (p.map_add e f)).trans (neg_add (p e) (p f)) }

@[simp] theorem signedRightMap_apply (p : E →ₗ[ℤ] C) (e : E) :
    signedRightMap A p e = (0, -p e) := rfl

/-- The signed inclusion has exactly the kernel of the supplied map. -/
theorem signedRightMap_ker (A : Type*) [AddCommGroup A] [Module ℤ A]
    (p : E →ₗ[ℤ] C) :
    LinearMap.ker (signedRightMap A p) = LinearMap.ker p := by
  ext e
  change ((0 : A), -p e) = (0, 0) ↔ p e = 0
  constructor
  · intro h
    exact neg_eq_zero.mp (congrArg Prod.snd h)
  · intro h
    rw [h, neg_zero]

/-- Restriction of a product-domain map to its first summand. -/
def firstSummandMap (r : (A × C) →ₗ[ℤ] B) : A →ₗ[ℤ] B :=
  intLinearMapOfAddHom
    { toFun a := r (a, 0)
      map_zero' := r.map_zero
      map_add' a b := by
        simpa only [Prod.mk_add_mk, add_zero] using r.map_add (a, 0) (b, 0) }

omit [Module ℤ C] in
@[simp] theorem firstSummandMap_apply (r : (A × C) →ₗ[ℤ] B) (a : A) :
    firstSummandMap r a = r (a, 0) := rfl

/-- The first product inclusion with the ambient integer-module structures. -/
def intFirstInclusion (A C : Type*) [AddCommGroup A] [AddCommGroup C]
    [Module ℤ A] [Module ℤ C] : A →ₗ[ℤ] (A × C) :=
  intLinearMapOfAddHom (LinearMap.inl ℤ A C).toAddMonoidHom

@[simp] theorem intFirstInclusion_apply (a : A) :
    intFirstInclusion A C a = (a, 0) := rfl

/-- The first projection with the ambient integer-module structures. -/
def intFirstProjection (A C : Type*) [AddCommGroup A] [AddCommGroup C]
    [Module ℤ A] [Module ℤ C] : (A × C) →ₗ[ℤ] A :=
  intLinearMapOfAddHom (LinearMap.fst ℤ A C).toAddMonoidHom

@[simp] theorem intFirstProjection_apply (ac : A × C) :
    intFirstProjection A C ac = ac.1 := rfl

/-- The restriction is the actual composite with the product inclusion. -/
theorem firstSummandMap_eq_comp_inl (r : (A × C) →ₗ[ℤ] B) :
    firstSummandMap r = r.comp (intFirstInclusion A C) := by
  ext a
  rfl

/-- A surjective signed inclusion has the full second summand as its image. -/
theorem signedRightMap_range (p : E →ₗ[ℤ] C) (hp : Function.Surjective p) :
    LinearMap.range (signedRightMap A p) = LinearMap.ker (intFirstProjection A C) := by
  ext ac
  constructor
  · rintro ⟨e, he⟩
    change ac.1 = 0
    exact (congrArg Prod.fst he).symm
  · intro ha
    change ac.1 = 0 at ha
    obtain ⟨e, he⟩ := hp (-ac.2)
    refine ⟨e, ?_⟩
    apply Prod.ext ha.symm
    change -p e = ac.2
    rw [he, neg_neg]

/-- Exactness after a signed second-summand map makes the first summand
injective. This part does not require the preceding map to be surjective. -/
theorem firstSummandMap_injective (p : E →ₗ[ℤ] C) (r : (A × C) →ₗ[ℤ] B)
    (hker : LinearMap.ker r = LinearMap.range (signedRightMap A p)) :
    Function.Injective (firstSummandMap r) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro a ha
  have hmem : (a, 0) ∈ LinearMap.ker r := ha
  rw [hker] at hmem
  obtain ⟨e, he⟩ := hmem
  change a = 0
  exact (congrArg Prod.fst he).symm

/-- A surjective signed second-summand image is killed by the next map. -/
theorem secondSummand_eq_zero (p : E →ₗ[ℤ] C) (hp : Function.Surjective p)
    (r : (A × C) →ₗ[ℤ] B)
    (hker : LinearMap.ker r = LinearMap.range (signedRightMap A p)) (c : C) :
    r (0, c) = 0 := by
  have hmem : (0, c) ∈ LinearMap.range (signedRightMap A p) := by
    obtain ⟨e, he⟩ := hp (-c)
    refine ⟨e, ?_⟩
    simp only [signedRightMap_apply, he, neg_neg]
  rw [← hker] at hmem
  exact hmem

/-- Every product-domain value is represented by its first coordinate. -/
theorem firstSummandMap_apply_fst (p : E →ₗ[ℤ] C) (hp : Function.Surjective p)
    (r : (A × C) →ₗ[ℤ] B)
    (hker : LinearMap.ker r = LinearMap.range (signedRightMap A p)) (ac : A × C) :
    firstSummandMap r ac.1 = r ac := by
  have h := r.map_add (ac.1, 0) (0, ac.2)
  simpa only [firstSummandMap_apply, Prod.mk_add_mk, add_zero, zero_add,
    secondSummand_eq_zero p hp r hker] using h.symm

/-- Removing the killed second summand does not change the image. -/
theorem firstSummandMap_range (p : E →ₗ[ℤ] C) (hp : Function.Surjective p)
    (r : (A × C) →ₗ[ℤ] B)
    (hker : LinearMap.ker r = LinearMap.range (signedRightMap A p)) :
    LinearMap.range (firstSummandMap r) = LinearMap.range r := by
  ext b
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨(a, 0), ha⟩
  · rintro ⟨ac, hac⟩
    exact ⟨ac.1, (firstSummandMap_apply_fst p hp r hker ac).trans hac⟩

/-- The literal composite with the first inclusion is injective. -/
theorem comp_inl_injective_of_signed_exact (p : E →ₗ[ℤ] C)
    (r : (A × C) →ₗ[ℤ] B)
    (hker : LinearMap.ker r = LinearMap.range (signedRightMap A p)) :
    Function.Injective (r.comp (intFirstInclusion A C)) := by
  rw [← firstSummandMap_eq_comp_inl]
  exact firstSummandMap_injective p r hker

/-- The literal composite with the first inclusion has the entire image. -/
theorem comp_inl_range_of_signed_exact (p : E →ₗ[ℤ] C)
    (hp : Function.Surjective p) (r : (A × C) →ₗ[ℤ] B)
    (hker : LinearMap.ker r = LinearMap.range (signedRightMap A p)) :
    LinearMap.range (r.comp (intFirstInclusion A C)) = LinearMap.range r := by
  rw [← firstSummandMap_eq_comp_inl]
  exact firstSummandMap_range p hp r hker

/-- A pointwise formula identifies the preceding map with the signed inclusion. -/
theorem eq_signedRightMap_of_apply (left : E →ₗ[ℤ] (A × C)) (p : E →ₗ[ℤ] C)
    (hl : ∀ e, left e = (0, -p e)) : left = signedRightMap A p := by
  apply LinearMap.ext
  intro e
  exact hl e

/-- The remaining summand is injective for any actual map with the signed formula. -/
theorem firstSummandMap_injective_of_signed_formula (left : E →ₗ[ℤ] (A × C))
    (p : E →ₗ[ℤ] C) (r : (A × C) →ₗ[ℤ] B)
    (hl : ∀ e, left e = (0, -p e))
    (hexact : LinearMap.range left = LinearMap.ker r) :
    Function.Injective (firstSummandMap r) := by
  apply firstSummandMap_injective p r
  rw [← eq_signedRightMap_of_apply left p hl]
  exact hexact.symm

/-- The image equality uses only the actual signed formula, surjectivity, and exactness. -/
theorem firstSummandMap_range_of_signed_formula (left : E →ₗ[ℤ] (A × C))
    (p : E →ₗ[ℤ] C) (hp : Function.Surjective p) (r : (A × C) →ₗ[ℤ] B)
    (hl : ∀ e, left e = (0, -p e))
    (hexact : LinearMap.range left = LinearMap.ker r) :
    LinearMap.range (firstSummandMap r) = LinearMap.range r := by
  apply firstSummandMap_range p hp r
  rw [← eq_signedRightMap_of_apply left p hl]
  exact hexact.symm

end SignedSummand

end Wikipedia.HopfProblem.CuspCentralHomology
