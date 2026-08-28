import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleSplitAlgebra

/-!
# Signed coordinates for the circle splitting

The image of the circle connecting map lies on the antidiagonal. Its
negative first coordinate therefore has the same kernel as the connecting
map and is surjective. Together with a retraction, this gives the splitting
with prescribed coordinates `(p b, -(δ b).1)`.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

/-- An additive homomorphism is linear for any integer-module structures
on its source and target. -/
def intLinearMapOfAddHom {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {modA : Module ℤ A} {modB : Module ℤ B} (f : A →+ B) : A →ₗ[ℤ] B where
  toFun := f
  map_add' := f.map_add
  map_smul' n a := by
    change f (modA.smul n a) = modB.smul n (f a)
    rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
    exact f.map_zsmul n a

@[simp] theorem intLinearMapOfAddHom_apply {A B : Type*}
    [AddCommGroup A] [AddCommGroup B] {modA : Module ℤ A} {modB : Module ℤ B}
    (f : A →+ B) (a : A) :
    intLinearMapOfAddHom (modA := modA) (modB := modB) f a = f a := rfl

variable (A : Type*) [AddCommGroup A] [Module ℤ A]

/-- Addition of the two coordinates, with the ambient integer-module structures. -/
def pairSumMap : (A × A) →ₗ[ℤ] A :=
  intLinearMapOfAddHom
    { toFun ac := ac.1 + ac.2
      map_zero' := add_zero 0
      map_add' ac bd := add_add_add_comm ac.1 bd.1 ac.2 bd.2 }

/-- The negative of the first coordinate. -/
def negativeFirstMap : (A × A) →ₗ[ℤ] A :=
  intLinearMapOfAddHom
    { toFun ac := -ac.1
      map_zero' := neg_zero
      map_add' ac bd := neg_add ac.1 bd.1 }

/-- The sum in the first coordinate and its negative in the second. -/
def signedFoldMap : (A × A) →ₗ[ℤ] (A × A) :=
  intLinearMapOfAddHom
    { toFun ac := (ac.1 + ac.2, -(ac.1 + ac.2))
      map_zero' := by simp only [Prod.fst_zero, Prod.snd_zero, add_zero, neg_zero,
        Prod.mk_zero_zero]
      map_add' ac bd := by
        apply Prod.ext
        · exact add_add_add_comm ac.1 bd.1 ac.2 bd.2
        · change -((ac.1 + bd.1) + (ac.2 + bd.2)) =
            -(ac.1 + ac.2) + -(bd.1 + bd.2)
          rw [add_add_add_comm ac.1 bd.1 ac.2 bd.2, neg_add] }

@[simp] theorem pairSumMap_apply (ac : A × A) :
    pairSumMap A ac = ac.1 + ac.2 := rfl

@[simp] theorem negativeFirstMap_apply (ac : A × A) :
    negativeFirstMap A ac = -ac.1 := rfl

omit [Module ℤ A] in
@[simp] theorem signedFoldMap_apply (ac : A × A) :
    signedFoldMap A ac = (ac.1 + ac.2, -(ac.1 + ac.2)) := rfl

/-- The signed fold and the coordinate sum have the same kernel. -/
theorem signedFoldMap_ker :
    LinearMap.ker (signedFoldMap A) = LinearMap.ker (pairSumMap A) := by
  ext ac
  change (ac.1 + ac.2, -(ac.1 + ac.2)) = 0 ↔ ac.1 + ac.2 = 0
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h
    exact Prod.ext h (h ▸ neg_zero)

/-- Addition of the two coordinates is surjective. -/
theorem pairSumMap_surjective : Function.Surjective (pairSumMap A) := by
  intro a
  exact ⟨(a, 0), add_zero a⟩

variable {A} {B P : Type*} [AddCommGroup B] [AddCommGroup P]
  [Module ℤ B] [Module ℤ P]

/-- Exactness at the pair puts every boundary value on the antidiagonal. -/
theorem circleBoundary_sum_eq_zero (δ : B →ₗ[ℤ] (A × A))
    (hrange : LinearMap.range δ = LinearMap.ker (pairSumMap A)) (b : B) :
    (δ b).1 + (δ b).2 = 0 := by
  have hb : δ b ∈ LinearMap.range δ := ⟨b, rfl⟩
  rw [hrange] at hb
  exact hb

/-- On the antidiagonal image, the negative first coordinate detects zero. -/
theorem circleBoundary_negativeFirst_ker (δ : B →ₗ[ℤ] (A × A))
    (hrange : LinearMap.range δ = LinearMap.ker (pairSumMap A)) :
    LinearMap.ker ((negativeFirstMap A).comp δ) = LinearMap.ker δ := by
  ext b
  change -(δ b).1 = 0 ↔ δ b = 0
  constructor
  · intro hb
    have hfst : (δ b).1 = 0 := neg_eq_zero.mp hb
    have hsnd := circleBoundary_sum_eq_zero δ hrange b
    rw [hfst, zero_add] at hsnd
    exact Prod.ext hfst hsnd
  · intro hb
    rw [hb]
    exact neg_zero

/-- Every antidiagonal pair `(-a, a)` has a boundary lift. -/
theorem circleBoundary_negativeFirst_surjective (δ : B →ₗ[ℤ] (A × A))
    (hrange : LinearMap.range δ = LinearMap.ker (pairSumMap A)) :
    Function.Surjective ((negativeFirstMap A).comp δ) := by
  intro a
  have ha : (-a, a) ∈ LinearMap.ker (pairSumMap A) := neg_add_cancel a
  rw [← hrange] at ha
  obtain ⟨b, hb⟩ := ha
  refine ⟨b, ?_⟩
  change -(δ b).1 = a
  rw [hb]
  exact neg_neg a

/-- The circle splitting in the signed connecting-map coordinate. -/
def circleSplitExactEquiv (i : P →ₗ[ℤ] B) (p : B →ₗ[ℤ] P)
    (δ : B →ₗ[ℤ] (A × A)) (hpi : p.comp i = LinearMap.id)
    (hker : LinearMap.range i = LinearMap.ker δ)
    (hrange : LinearMap.range δ = LinearMap.ker (pairSumMap A)) :
    B ≃ₗ[ℤ] (P × A) :=
  splitExactEquiv i p ((negativeFirstMap A).comp δ) hpi
    (hker.trans (circleBoundary_negativeFirst_ker δ hrange).symm)
    (circleBoundary_negativeFirst_surjective δ hrange)

variable (i : P →ₗ[ℤ] B) (p : B →ₗ[ℤ] P) (δ : B →ₗ[ℤ] (A × A))
  (hpi : p.comp i = LinearMap.id) (hker : LinearMap.range i = LinearMap.ker δ)
  (hrange : LinearMap.range δ = LinearMap.ker (pairSumMap A))

@[simp] theorem circleSplitExactEquiv_apply (b : B) :
    circleSplitExactEquiv i p δ hpi hker hrange b = (p b, -(δ b).1) := rfl

@[simp] theorem circleSplitExactEquiv_fst (b : B) :
    (circleSplitExactEquiv i p δ hpi hker hrange b).1 = p b := rfl

@[simp] theorem circleSplitExactEquiv_snd (b : B) :
    (circleSplitExactEquiv i p δ hpi hker hrange b).2 = -(δ b).1 := rfl

@[simp] theorem circleSplitExactEquiv_symm_fst (pa : P × A) :
    p ((circleSplitExactEquiv i p δ hpi hker hrange).symm pa) = pa.1 :=
  congrArg Prod.fst ((circleSplitExactEquiv i p δ hpi hker hrange).apply_symm_apply pa)

@[simp] theorem circleSplitExactEquiv_symm_snd (pa : P × A) :
    -(δ ((circleSplitExactEquiv i p δ hpi hker hrange).symm pa)).1 = pa.2 :=
  congrArg Prod.snd ((circleSplitExactEquiv i p δ hpi hker hrange).apply_symm_apply pa)

/-- The full connecting-map value of an inverse-coordinate class. -/
theorem circleSplitExactEquiv_symm_boundary (pa : P × A) :
    δ ((circleSplitExactEquiv i p δ hpi hker hrange).symm pa) = (-pa.2, pa.2) := by
  have hneg := circleSplitExactEquiv_symm_snd i p δ hpi hker hrange pa
  have hfst : (δ ((circleSplitExactEquiv i p δ hpi hker hrange).symm pa)).1 =
      -pa.2 := by
    simpa only [neg_neg] using congrArg Neg.neg hneg
  have hsum := circleBoundary_sum_eq_zero δ hrange
    ((circleSplitExactEquiv i p δ hpi hker hrange).symm pa)
  rw [hfst] at hsum
  apply Prod.ext hfst
  exact (neg_add_eq_zero.mp hsum).symm

@[simp] theorem circleSplitExactEquiv_apply_inclusion (a : P) :
    circleSplitExactEquiv i p δ hpi hker hrange (i a) = (a, 0) :=
  splitExactEquiv_apply_inclusion i p ((negativeFirstMap A).comp δ) hpi
    (hker.trans (circleBoundary_negativeFirst_ker δ hrange).symm)
    (circleBoundary_negativeFirst_surjective δ hrange) a

@[simp] theorem circleSplitExactEquiv_symm_apply_inl (a : P) :
    (circleSplitExactEquiv i p δ hpi hker hrange).symm (a, 0) = i a := by
  apply (circleSplitExactEquiv i p δ hpi hker hrange).injective
  rw [LinearEquiv.apply_symm_apply, circleSplitExactEquiv_apply_inclusion]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
