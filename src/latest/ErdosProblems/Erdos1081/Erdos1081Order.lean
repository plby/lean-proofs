import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.NumberTheory.ClassNumber.Finite
import Mathlib.NumberTheory.ClassNumber.AdmissibleAbs
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.LinearAlgebra.TensorProduct.Quotient

open scoped nonZeroDivisors

namespace Erdos1081

noncomputable def zsqrtdLinearEquiv (d : ℤ) :
    Zsqrtd d ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun z := ![z.re, z.im]
  invFun x := ⟨x 0, x 1⟩
  left_inv z := by ext <;> rfl
  right_inv x := by funext i; fin_cases i <;> rfl
  map_add' x y := by funext i; fin_cases i <;> rfl
  map_smul' n x := by funext i; fin_cases i <;> simp

noncomputable def zsqrtdBasis (d : ℤ) : Module.Basis (Fin 2) ℤ (Zsqrtd d) :=
  Module.Basis.ofEquivFun (zsqrtdLinearEquiv d)

/-- The determinant norm for the explicit rank-two basis is the usual
quadratic norm `a² - d b²`. -/
theorem algebraNorm_zsqrtd (d : ℤ) (z : Zsqrtd d) :
    Algebra.norm ℤ z = z.norm := by
  rw [Algebra.norm_eq_matrix_det (zsqrtdBasis d), Matrix.det_fin_two]
  simp [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
    Module.Basis.ofEquivFun_repr_apply, Module.Basis.coe_ofEquivFun,
    zsqrtdBasis, zsqrtdLinearEquiv, Zsqrtd.norm_def]

noncomputable local instance (d : ℤ) : Module.Free ℤ (Zsqrtd d) :=
  Module.Free.of_basis (zsqrtdBasis d)

noncomputable local instance (d : ℤ) : Module.Finite ℤ (Zsqrtd d) :=
  Module.Finite.of_basis (zsqrtdBasis d)

def zsqrtdNoZeroDivisors (d : ℤ) (hd : d < 0) :
    NoZeroDivisors (Zsqrtd d) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b hab
    have hnorm : a.norm * b.norm = 0 := by
      rw [← Zsqrtd.norm_mul]
      simp [hab]
    rcases mul_eq_zero.mp hnorm with ha | hb
    · exact Or.inl ((Zsqrtd.norm_eq_zero_iff hd a).mp ha)
    · exact Or.inr ((Zsqrtd.norm_eq_zero_iff hd b).mp hb)

def zsqrtdIsDomain (d : ℤ) (hd : d < 0) : IsDomain (Zsqrtd d) := by
  let : NoZeroDivisors (Zsqrtd d) := zsqrtdNoZeroDivisors d hd
  exact NoZeroDivisors.to_isDomain _

/-- Away from the Gaussian exceptional order, a negative quadratic order
has only the two rational units.  This elementary form is the unit input
needed when lattice points are quotiented by associates. -/
theorem zsqrtd_isUnit_iff_eq_one_or_neg_one
    {d : ℤ} (hd : d ≤ -2) (z : Zsqrtd d) :
    IsUnit z ↔ z = 1 ∨ z = -1 := by
  constructor
  · intro hz
    have hnorm : z.norm = 1 :=
      (Zsqrtd.norm_eq_one_iff' (by omega : d ≤ 0) z).2 hz
    have him : z.im = 0 := by
      by_contra him
      have himsq : 1 ≤ z.im * z.im := by
        have hpos : 0 < z.im * z.im := mul_self_pos.mpr him
        omega
      have hdprod : d * (z.im * z.im) ≤ -2 := by
        calc
          d * (z.im * z.im) ≤ (-2 : ℤ) * (z.im * z.im) :=
            mul_le_mul_of_nonneg_right hd (mul_self_nonneg z.im)
          _ ≤ (-2 : ℤ) * 1 :=
            mul_le_mul_of_nonpos_left himsq (by norm_num)
          _ = -2 := by norm_num
      rw [Zsqrtd.norm_def] at hnorm
      nlinarith [mul_self_nonneg z.re]
    have hreSq : z.re * z.re = 1 := by
      simpa only [Zsqrtd.norm_def, him, mul_zero, sub_zero] using hnorm
    rcases mul_self_eq_one_iff.mp hreSq with hre | hre
    · left
      apply Zsqrtd.ext
      · simpa using hre
      · simpa using him
    · right
      apply Zsqrtd.ext
      · simpa using hre
      · simpa using him
  · rintro (rfl | rfl) <;> simp

example (d : ℤ) (hd : d < 0) : Ring.HasFiniteQuotients (Zsqrtd d) := by
  let : NoZeroDivisors (Zsqrtd d) := zsqrtdNoZeroDivisors d hd
  let : IsDomain (Zsqrtd d) := zsqrtdIsDomain d hd
  infer_instance

section General

variable {S : Type*} [CommRing S] [IsDomain S]

/-- The index of a principal ideal in a finite free order is the absolute
value of the determinant norm.  Mathlib's corresponding `Ideal.absNorm`
lemma is stated under a Dedekind hypothesis because that bundled norm is
multiplicative on every ideal; the principal-ideal calculation itself needs
only freeness and finiteness. -/
theorem cardQuot_span_singleton_eq_norm_natAbs
    [Module.Free ℤ S] [Module.Finite ℤ S] (r : S) :
    (Ideal.span ({r} : Set S)).cardQuot =
      (Algebra.norm ℤ r).natAbs := by
  rw [Algebra.norm_apply]
  by_cases hr : r = 0
  · subst r
    simp only [Set.singleton_zero, Ideal.span_zero]
    have hInfinite : Infinite S := Module.Free.infinite ℤ S
    rw [Submodule.cardQuot_bot]
    simp
  let b := Module.Free.chooseBasis ℤ S
  rw [Submodule.cardQuot_apply,
    ← Nat.card_congr
      (Submodule.Quotient.restrictScalarsEquiv ℤ
        (Ideal.span ({r} : Set S))).toEquiv,
    ← Submodule.natAbs_det_equiv
      ((Ideal.span ({r} : Set S)).restrictScalars ℤ)
      (b.equiv (Ideal.basisSpanSingleton b hr) (Equiv.refl _))]
  congr
  refine b.ext fun i => ?_
  change
    ((b.equiv (Ideal.basisSpanSingleton b hr) (Equiv.refl _)) (b i) : S) =
      r * b i
  rw [Module.Basis.equiv_apply]
  exact Ideal.basisSpanSingleton_apply b hr i

/-- Multiplication by a nonzero element identifies an ideal with its
principal multiple. -/
noncomputable def idealSpanMulLinearEquiv
    (I : Ideal S) {a : S} (ha : a ≠ 0) :
    I ≃ₗ[ℤ] Ideal.span ({a} : Set S) * I := by
  let f : I →ₗ[ℤ] Ideal.span ({a} : Set S) * I :=
    { toFun := fun x =>
        ⟨a * (x : S), Ideal.mem_span_singleton_mul.mpr
          ⟨x, x.property, rfl⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp [mul_add]
      map_smul' := by
        intro n x
        apply Subtype.ext
        simp [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply mul_left_cancel₀ ha
    exact congrArg Subtype.val hxy
  · intro y
    obtain ⟨x, hxI, hxy⟩ :=
      Ideal.mem_span_singleton_mul.mp y.property
    refine ⟨⟨x, hxI⟩, ?_⟩
    apply Subtype.ext
    exact hxy

@[simp] theorem idealSpanMulLinearEquiv_apply
    (I : Ideal S) {a : S} (ha : a ≠ 0) (x : I) :
    ((idealSpanMulLinearEquiv I ha x :
      Ideal.span ({a} : Set S) * I) : S) = a * (x : S) := rfl

/-- Quotient cardinality is the absolute determinant of any full-rank
integral basis of the ideal. -/
theorem cardQuot_eq_natAbs_det_basis_change
    [Module.Free ℤ S] [Module.Finite ℤ S]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ S) (I : Ideal S)
    (bI : Module.Basis ι ℤ I) :
    I.cardQuot = (b.det ((↑) ∘ bI)).natAbs := by
  rw [Submodule.cardQuot_apply,
    ← Nat.card_congr
      (Submodule.Quotient.restrictScalarsEquiv ℤ I).toEquiv]
  exact (Submodule.natAbs_det_basis_change
    b (I.restrictScalars ℤ) bI).symm

/-- Scaling a full-rank ideal by a principal ideal multiplies its index by
the absolute algebra norm of the generator. -/
theorem cardQuot_span_singleton_mul
    [Module.Free ℤ S] [Module.Finite ℤ S]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ S) (I : Ideal S)
    (bI : Module.Basis ι ℤ I) {a : S} (ha : a ≠ 0) :
    (Ideal.span ({a} : Set S) * I).cardQuot =
      (Algebra.norm ℤ a).natAbs * I.cardQuot := by
  let bMul : Module.Basis ι ℤ (Ideal.span ({a} : Set S) * I) :=
    bI.map (idealSpanMulLinearEquiv I ha)
  rw [cardQuot_eq_natAbs_det_basis_change b _ bMul,
    cardQuot_eq_natAbs_det_basis_change b I bI]
  have hvec : ((↑) ∘ bMul : ι → S) =
      (Algebra.lmul ℤ S a) ∘ ((↑) ∘ bI) := by
    funext i
    simp [bMul, Function.comp_apply]
  rw [hvec, Module.Basis.det_comp, ← Algebra.norm_apply, Int.natAbs_mul]

/-- A nonzero ideal in a finite free order has a full-rank basis indexed by
the same finite type as a chosen basis of the order. -/
noncomputable def idealFullBasis
    {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℤ S) (I : Ideal S) (hI : I ≠ ⊥) :
    Module.Basis ι ℤ I :=
  Submodule.smithNormalFormBotBasis b
    (Ideal.finrank_eq_finrank b I hI)

/-- The principal-scaling index formula with the basis of the ideal chosen
canonically by Smith normal form. -/
theorem cardQuot_span_singleton_mul_of_ne_bot
    [Module.Free ℤ S] [Module.Finite ℤ S]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ S) (I : Ideal S) (hI : I ≠ ⊥)
    {a : S} (ha : a ≠ 0) :
    (Ideal.span ({a} : Set S) * I).cardQuot =
      (Algebra.norm ℤ a).natAbs * I.cardQuot :=
  cardQuot_span_singleton_mul b I (idealFullBasis b I hI) ha

/-- Clearing denominators in an equality of nonzero ideals preserves the
expected quotient-cardinality ratio.  This is the non-Dedekind replacement
for the corresponding `Ideal.absNorm` calculation. -/
theorem cardQuot_ratio_of_principal_mul_eq
    [Module.Free ℤ S] [Module.Finite ℤ S]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ S) {I J : Ideal S}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) {a c : S}
    (ha : a ≠ 0) (hc : c ≠ 0)
    (h : Ideal.span ({a} : Set S) * I =
      Ideal.span ({c} : Set S) * J) :
    (Algebra.norm ℤ a).natAbs * I.cardQuot =
      (Algebra.norm ℤ c).natAbs * J.cardQuot := by
  rw [← cardQuot_span_singleton_mul_of_ne_bot b I hI ha,
    h, cardQuot_span_singleton_mul_of_ne_bot b J hJ hc]

open TensorProduct

/-- Tensoring an invertible module with a residue field makes it a
one-dimensional vector space.  Consequently multiplication by a maximal
ideal has relative additive index equal to the cardinality of the residue
field. -/
theorem relIndex_smul_invertible_submodule_eq_cardQuot
    {M : Type*} [AddCommGroup M] [Module S M]
    (P : Ideal S) (J : Submodule S M) [Module.Invertible S J]
    (hP : P.IsMaximal) :
    (P • J).toAddSubgroup.relIndex J.toAddSubgroup = P.cardQuot := by
  classical
  change Nat.card (J ⧸ (P • J).comap J.subtype) = Nat.card (S ⧸ P)
  let e : (J ⧸ (P • J).comap J.subtype) ≃ₗ[S] (S ⧸ P) ⊗[S] J :=
    Submodule.quotEquivOfEq _ (P • (⊤ : Submodule S J))
      (Submodule.map_injective_of_injective J.injective_subtype
        (by simp [Submodule.smul_le_right])) ≪≫ₗ
      (quotTensorEquivQuotSMul J P).symm
  rw [Nat.card_congr e.toEquiv]
  let : Field (S ⧸ P) :=
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient P).mp hP).toField
  let e' : ((S ⧸ P) ⊗[S] J) ≃ₗ[S ⧸ P] (S ⧸ P) :=
    (Module.Invertible.free_iff_linearEquiv.mp (by infer_instance)).some
  exact Nat.card_congr e'.toEquiv

/-- Multiplication on the left by a maximal ideal multiplies quotient
cardinality by its residue-field cardinality whenever the right ideal is
invertible as a module. -/
theorem cardQuot_mul_of_moduleInvertible_right
    (P J : Ideal S) [Module.Invertible S (J : Submodule S S)]
    (hP : P.IsMaximal) :
    (P * J).cardQuot = P.cardQuot * J.cardQuot := by
  calc
    (P * J).cardQuot =
        (P • (J : Submodule S S)).toAddSubgroup.index := rfl
    _ = (P • (J : Submodule S S)).toAddSubgroup.relIndex J.toAddSubgroup *
        J.toAddSubgroup.index :=
      (AddSubgroup.relIndex_mul_index Submodule.smul_le_right).symm
    _ = P.cardQuot * J.cardQuot := by
      rw [relIndex_smul_invertible_submodule_eq_cardQuot
        P (J : Submodule S S) hP]
      rfl

/-- The subtype of an integral ideal is linearly equivalent to the subtype
of its image in the fraction field. -/
noncomputable def idealSubtypeEquivCoeFractionalIdeal (J : Ideal S) :
    J ≃ₗ[S] ((J : FractionalIdeal S⁰ (FractionRing S)) :
      Submodule S (FractionRing S)) := by
  let f : J →ₗ[S] ((J : FractionalIdeal S⁰ (FractionRing S)) :
      Submodule S (FractionRing S)) :=
    { toFun := fun x ↦
        ⟨algebraMap S (FractionRing S) x.1,
          FractionalIdeal.mem_coeIdeal_of_mem S⁰ x.2⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact map_add (algebraMap S (FractionRing S)) x.1 y.1
      map_smul' := by
        intro r x
        apply Subtype.ext
        exact (Algebra.linearMap S (FractionRing S)).map_smul r x.1 }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    exact (IsFractionRing.injective S (FractionRing S))
      (congr_arg Subtype.val hxy)
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal S⁰).mp hy
    exact ⟨⟨x, hx⟩, rfl⟩

/-- An integral ideal which is a unit in the fractional-ideal monoid is an
invertible module. -/
noncomputable def moduleInvertibleIdealOfIsUnit (J : Ideal S)
    (hJ : IsUnit (J : FractionalIdeal S⁰ (FractionRing S))) :
    Module.Invertible S J := by
  let uF : (FractionalIdeal S⁰ (FractionRing S))ˣ := hJ.unit
  let uS : (Submodule S (FractionRing S))ˣ :=
    FractionalIdeal.unitsMulEquivSubmodule uF
  let : Module.Invertible S uS := inferInstance
  have hsub : (uS : Submodule S (FractionRing S)) =
      ((J : FractionalIdeal S⁰ (FractionRing S)) :
        Submodule S (FractionRing S)) := by
    change ((uF : FractionalIdeal S⁰ (FractionRing S)) :
      Submodule S (FractionRing S)) = _
    rw [hJ.unit_spec]
  let e : uS ≃ₗ[S] J :=
    LinearEquiv.ofEq _ _ hsub ≪≫ₗ (idealSubtypeEquivCoeFractionalIdeal J).symm
  exact Module.Invertible.congr e

/-- Quotient cardinality is multiplicative when the left factor is maximal
and the right integral ideal is invertible as a fractional ideal. -/
theorem cardQuot_mul_of_isUnit_right
    (P J : Ideal S) (hP : P.IsMaximal)
    (hJ : IsUnit (J : FractionalIdeal S⁰ (FractionRing S))) :
    (P * J).cardQuot = P.cardQuot * J.cardQuot := by
  let : Module.Invertible S J := moduleInvertibleIdealOfIsUnit J hJ
  exact cardQuot_mul_of_moduleInvertible_right P J hP

/-- The numerator of an invertible fractional ideal is an invertible integral
ideal in the same class; unlike `ClassGroup.mk0_integralRep`, this formulation
does not assume that every integral ideal is invertible. -/
theorem exists_integralUnitRep
    (I : (FractionalIdeal S⁰ (FractionRing S))ˣ) :
    ∃ J : (FractionalIdeal S⁰ (FractionRing S))ˣ,
      (J : FractionalIdeal S⁰ (FractionRing S)) = I.1.num ∧
      ClassGroup.mk (FractionRing S) J = ClassGroup.mk (FractionRing S) I := by
  obtain ⟨J, hJ⟩ := (FractionalIdeal.isUnit_num (I := I.1)).mpr I.isUnit
  refine ⟨J, hJ, ?_⟩
  rw [eq_comm, ClassGroup.mk_eq_mk]
  have hden0 : algebraMap S (FractionRing S) I.1.den ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors I.1.den.prop
  refine ⟨Units.mk0 (algebraMap S _ I.1.den) hden0, ?_⟩
  apply Units.ext
  rw [mul_comm, Units.val_mul, coe_toPrincipalIdeal, Units.val_mk0, hJ]
  exact FractionalIdeal.den_mul_self_eq_num' S⁰ (FractionRing S) I

section Approximation

open Module Ring

variable {R S K L : Type*} [EuclideanDomain R] [CommRing S] [IsDomain S]
variable [Field K] [Field L]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [Algebra R L] [IsScalarTower R K L]
variable [Algebra R S] [Algebra S L] [IsScalarTower R S L]
variable (abv : AbsoluteValue R ℤ)
variable {iota : Type*} [DecidableEq iota] [Fintype iota]
variable (bS : Module.Basis iota R S)
variable {abv}
variable (adm : abv.IsAdmissible)
variable [Infinite R] [DecidableEq R]

/-- A nonzero ideal contains an element of minimal norm.  This is the
non-Dedekind version of `ClassGroup.exists_min`; its proof only needs the
ideal to be nonzero. -/
theorem exists_min_nonzero (I : Ideal S) (hI : I ≠ ⊥) :
    ∃ b ∈ I, b ≠ 0 ∧
      ∀ c ∈ I, abv (Algebra.norm R c) < abv (Algebra.norm R b) → c = 0 := by
  obtain ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩, min⟩ := @Int.exists_least_of_bdd
      (fun a => ∃ b ∈ I, b ≠ (0 : S) ∧ abv (Algebra.norm R b) = a)
    (by
      use 0
      rintro _ ⟨b, _, _, rfl⟩
      apply abv.nonneg)
    (by
      obtain ⟨b, b_mem, b_ne_zero⟩ := I.ne_bot_iff.mp hI
      exact ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩⟩)
  refine ⟨b, b_mem, b_ne_zero, ?_⟩
  intro c hc lt
  contrapose! lt with c_ne_zero
  exact min _ ⟨c, hc, c_ne_zero, rfl⟩

/-- Minkowski's approximation argument for an invertible integral ideal.  The
Dedekind hypothesis in Mathlib's class-number theorem is needed only to know
that *all* integral ideals are invertible.  Retaining invertibility as data
gives the form required for nonmaximal quadratic orders. -/
theorem exists_integralUnitRep_mem_fixed
    [Algebra.IsAlgebraic R S]
    (I : (FractionalIdeal S⁰ (FractionRing S))ˣ) (I' : Ideal S)
    (hI : (I : FractionalIdeal S⁰ (FractionRing S)) = I') :
    ∃ J : (FractionalIdeal S⁰ (FractionRing S))ˣ, ∃ J' : Ideal S,
      (J : FractionalIdeal S⁰ (FractionRing S)) = J' ∧
      ClassGroup.mk (FractionRing S) J = ClassGroup.mk (FractionRing S) I ∧
      algebraMap R S (∏ m ∈ ClassGroup.finsetApprox bS adm, m) ∈ J' := by
  set M := ∏ m ∈ ClassGroup.finsetApprox bS adm, m
  have hM : algebraMap R S M ≠ 0 := ClassGroup.prod_finsetApprox_ne_zero bS adm
  have hI' : I' ≠ ⊥ := by
    intro hzero
    have : (I : FractionalIdeal S⁰ (FractionRing S)) = 0 := by simpa [hI, hzero]
    exact I.ne_zero this
  obtain ⟨b, b_mem, b_ne_zero, b_min⟩ :=
    exists_min_nonzero (abv := abv) I' hI'
  have hleIdeal : Ideal.span {algebraMap R S M} * I' ≤ Ideal.span {b} := by
    rw [Ideal.mul_le]
    intro r' hr' a ha
    rw [Ideal.mem_span_singleton] at hr' ⊢
    obtain ⟨q, r, r_mem, lt⟩ :=
      ClassGroup.exists_mem_finset_approx' bS adm a b_ne_zero
    apply @dvd_of_mul_left_dvd _ _ q
    simp only [Algebra.smul_def] at lt
    rw [← sub_eq_zero.mp
      (b_min _ (I'.sub_mem (I'.mul_mem_left _ ha) (I'.mul_mem_left _ b_mem)) lt)]
    refine mul_dvd_mul_right (dvd_trans (map_dvd _ ?_) hr') _
    exact Multiset.dvd_prod (Multiset.mem_map.mpr ⟨_, r_mem, rfl⟩)
  let P : FractionalIdeal S⁰ (FractionRing S) :=
    ((Ideal.span {b} : Ideal S) : FractionalIdeal S⁰ (FractionRing S))
  let Q : FractionalIdeal S⁰ (FractionRing S) :=
    ((Ideal.span {algebraMap R S M} : Ideal S) :
      FractionalIdeal S⁰ (FractionRing S))
  let A : FractionalIdeal S⁰ (FractionRing S) :=
    (I' : FractionalIdeal S⁰ (FractionRing S))
  let JF : FractionalIdeal S⁰ (FractionRing S) := Q * A * P⁻¹
  have hleFrac : Q * A ≤ P := by
    change
      ((Ideal.span {algebraMap R S M} : Ideal S) :
          FractionalIdeal S⁰ (FractionRing S)) *
          (I' : FractionalIdeal S⁰ (FractionRing S)) ≤
        ((Ideal.span {b} : Ideal S) : FractionalIdeal S⁰ (FractionRing S))
    rw [← FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.coeIdeal_le_coeIdeal (FractionRing S)]
    exact hleIdeal
  have hbUnit : IsUnit
      P := by
    refine IsUnit.of_mul_eq_one
      P⁻¹ ?_
    dsimp only [P]
    exact FractionalIdeal.coe_ideal_span_singleton_mul_inv (FractionRing S) b_ne_zero
  have hMUnit : IsUnit
      Q := by
    refine IsUnit.of_mul_eq_one
      Q⁻¹ ?_
    dsimp only [Q]
    exact FractionalIdeal.coe_ideal_span_singleton_mul_inv (FractionRing S) hM
  have hIUnit : IsUnit A := ⟨I, hI⟩
  have hPmul : P * P⁻¹ = 1 :=
    (FractionalIdeal.mul_inv_cancel_iff_isUnit (K := FractionRing S)).mpr hbUnit
  have hPinvUnit : IsUnit P⁻¹ := by
    refine IsUnit.of_mul_eq_one P ?_
    rw [mul_comm, hPmul]
  have hJFUnit : IsUnit JF := by
    exact (hMUnit.mul hIUnit).mul hPinvUnit
  have hJFle : JF ≤ 1 := by
    dsimp only [JF]
    have hmul : Q * A * P⁻¹ ≤ P * P⁻¹ := by gcongr
    calc
      Q * A * P⁻¹ ≤ P * P⁻¹ := hmul
      _ = 1 := hPmul
  obtain ⟨J', hJ'⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJFle
  obtain ⟨J, hJ⟩ := hJFUnit
  have hcoeJ : (J : FractionalIdeal S⁰ (FractionRing S)) = J' := hJ.trans hJ'.symm
  have hclassFrac : P * (J' : FractionalIdeal S⁰ (FractionRing S)) = Q * A := by
    rw [hJ']
    change P * (Q * A * P⁻¹) = Q * A
    calc
      P * (Q * A * P⁻¹) = (Q * A) * (P * P⁻¹) := by ac_rfl
      _ = Q * A := by rw [hPmul, mul_one]
  have hclassIdeal :
      Ideal.span {b} * J' = Ideal.span {algebraMap R S M} * I' := by
    apply FractionalIdeal.coeIdeal_injective (R := S) (K := FractionRing S)
    simpa only [P, Q, A, FractionalIdeal.coeIdeal_mul] using hclassFrac
  refine ⟨J, J', hcoeJ, ?_, ?_⟩
  · apply (ClassGroup.mk_eq_mk_of_coe_ideal hcoeJ hI).mpr
    exact ⟨b, algebraMap R S M, b_ne_zero, hM, hclassIdeal⟩
  · have hbFrac : P ≤ A := by
      simpa only [P, A, FractionalIdeal.coeIdeal_le_coeIdeal] using
        (Ideal.span_singleton_le_iff_mem I').mpr b_mem
    have hQleJF : Q ≤ JF := by
      have hQP : Q * P ≤ Q * A := by gcongr
      have hmul : (Q * P) * P⁻¹ ≤ (Q * A) * P⁻¹ := by gcongr
      calc
        Q = Q * 1 := (mul_one Q).symm
        _ = Q * (P * P⁻¹) := congrArg (Q * ·) hPmul.symm
        _ = (Q * P) * P⁻¹ := by ac_rfl
        _ ≤ (Q * A) * P⁻¹ := hmul
        _ = JF := rfl
    have hspan : Ideal.span {algebraMap R S M} ≤ J' := by
      apply (FractionalIdeal.coeIdeal_le_coeIdeal (FractionRing S)).mp
      rw [hJ']
      exact hQleJF
    exact (Ideal.span_singleton_le_iff_mem J').mp hspan

/-- The Picard/class group of a finite order is finite.  This version replaces
the Dedekind assumption in Mathlib's class-number theorem by the exact two
properties used here: finite quotients and invertibility of the ideals that
represent class-group elements. -/
noncomputable def fintypeClassGroupOfFiniteQuotients
    [Ring.HasFiniteQuotients S] [Algebra.IsAlgebraic R S] :
    Fintype (ClassGroup S) := by
  classical
  let m : S := algebraMap R S (∏ r ∈ ClassGroup.finsetApprox bS adm, r)
  have hm : m ≠ 0 := by
    simpa only [m] using ClassGroup.prod_finsetApprox_ne_zero bS adm
  let T := {J : Ideal S // m ∈ J ∧
    IsUnit (J : FractionalIdeal S⁰ (FractionRing S))}
  have hfinite :
      {J : Ideal S | m ∈ J ∧
        IsUnit (J : FractionalIdeal S⁰ (FractionRing S))}.Finite :=
    (Ring.HasFiniteQuotients.finite_setOfPred_mem m hm).subset fun _ hJ => hJ.1
  letI : Fintype T := hfinite.fintype
  let f : T → ClassGroup S := fun J =>
    ClassGroup.mk (FractionRing S) J.2.2.unit
  apply Fintype.ofSurjective f
  intro C
  refine ClassGroup.induction (FractionRing S) ?_ C
  intro I
  obtain ⟨Iu, hIu, hclassIu⟩ := exists_integralUnitRep I
  obtain ⟨J, J', hJ, hclassJ, hmemJ⟩ :=
    exists_integralUnitRep_mem_fixed bS adm Iu I.1.num hIu
  have hmemJ' : m ∈ J' := by simpa only [m] using hmemJ
  let t : T := ⟨J', hmemJ', ⟨J, hJ⟩⟩
  refine ⟨t, ?_⟩
  change ClassGroup.mk (FractionRing S) t.2.2.unit =
    ClassGroup.mk (FractionRing S) I
  calc
    ClassGroup.mk (FractionRing S) t.2.2.unit =
        ClassGroup.mk (FractionRing S) J := by
      congr 1
      apply Units.ext
      exact t.2.2.unit_spec.trans hJ.symm
    _ = ClassGroup.mk (FractionRing S) Iu := hclassJ
    _ = ClassGroup.mk (FractionRing S) I := hclassIu

end Approximation

end General

/-- The concrete ring class group attached to a negative quadratic order is
finite, including nonmaximal orders such as `ℤ[√(-p³)]`. -/
noncomputable def zsqrtdClassGroupFintype (d : ℤ) (hd : d < 0) :
    letI : IsDomain (Zsqrtd d) := zsqrtdIsDomain d hd
    Fintype (ClassGroup (Zsqrtd d)) := by
  letI : IsDomain (Zsqrtd d) := zsqrtdIsDomain d hd
  letI : Module.Free ℤ (Zsqrtd d) := Module.Free.of_basis (zsqrtdBasis d)
  letI : Module.Finite ℤ (Zsqrtd d) := Module.Finite.of_basis (zsqrtdBasis d)
  letI : Ring.HasFiniteQuotients (Zsqrtd d) := inferInstance
  exact fintypeClassGroupOfFiniteQuotients
    (bS := zsqrtdBasis d) AbsoluteValue.absIsAdmissible

end Erdos1081
