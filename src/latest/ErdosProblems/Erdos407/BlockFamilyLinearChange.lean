/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos407.SymmetricPower

/-!
# Block-dependent linear changes of variables

This file supplies the elementary substitution API for applying a possibly
different rational coordinate matrix in every block of a multiblock
polynomial.  Its first section gives the elementary algebra-homomorphism
action, composition, and invertibility.  The final section builds on the
symmetric-power and Hasse derivative developments to identify the exact
fixed-multidegree chain rule for a block-dependent family.

The matrix convention is the same as in `Erdos407.SymmetricPower`: rows are
old coordinates and columns are new coordinates.  Consequently applying
`T` and then `U` is substitution by the pointwise product `T h * U h`.
-/

namespace Erdos407.BlockFamilyLinearChange

open scoped BigOperators Matrix

noncomputable section

/-- Variables consisting of a block index and a coordinate in that block. -/
abbrev BlockVar (blocks coords : ℕ) :=
  AuxiliaryPolynomial.BlockVar blocks coords

/-- The rational linear form replacing an old coordinate.  The matrix may
depend on the block. -/
def familyBlockLinearForm {blocks coords : ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ)
    (x : BlockVar blocks coords) :
    MvPolynomial (BlockVar blocks coords) ℚ :=
  ∑ j, MvPolynomial.C (T x.1 x.2 j) * MvPolynomial.X (x.1, j)

/-- Apply the block-dependent rational linear substitution
`X_(h,i) ↦ ∑_j T h i j X_(h,j)`. -/
def familyBlockLinearChange {blocks coords : ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ) :
    MvPolynomial (BlockVar blocks coords) ℚ →ₐ[ℚ]
      MvPolynomial (BlockVar blocks coords) ℚ :=
  MvPolynomial.eval₂AlgHom ℚ (familyBlockLinearForm T)

@[simp] theorem familyBlockLinearChange_C {blocks coords : ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ) (a : ℚ) :
    familyBlockLinearChange T (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [familyBlockLinearChange]

@[simp] theorem familyBlockLinearChange_X {blocks coords : ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ)
    (x : BlockVar blocks coords) :
    familyBlockLinearChange T (MvPolynomial.X x) =
      familyBlockLinearForm T x := by
  simp [familyBlockLinearChange]

/-- Composition follows pointwise matrix multiplication in the old-row,
new-column convention. -/
theorem familyBlockLinearChange_comp {blocks coords : ℕ}
    (T U : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ)
    (P : MvPolynomial (BlockVar blocks coords) ℚ) :
    familyBlockLinearChange U (familyBlockLinearChange T P) =
      familyBlockLinearChange (fun h ↦ T h * U h) P := by
  have hhom :
      (familyBlockLinearChange U).comp (familyBlockLinearChange T) =
        familyBlockLinearChange (fun h ↦ T h * U h) := by
    apply MvPolynomial.algHom_ext
    intro x
    simp only [AlgHom.comp_apply, familyBlockLinearChange_X,
      familyBlockLinearForm, map_sum, map_mul, familyBlockLinearChange_C]
    simp only [Matrix.mul_apply, map_sum, MvPolynomial.C_mul,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  exact DFunLike.congr_fun hhom P

/-- The pointwise identity matrix induces the identity substitution. -/
@[simp] theorem familyBlockLinearChange_one {blocks coords : ℕ}
    (P : MvPolynomial (BlockVar blocks coords) ℚ) :
    familyBlockLinearChange
        (fun _ ↦ (1 : Matrix (Fin coords) (Fin coords) ℚ)) P = P := by
  have hhom :
      familyBlockLinearChange
          (fun _ ↦ (1 : Matrix (Fin coords) (Fin coords) ℚ)) =
        AlgHom.id ℚ (MvPolynomial (BlockVar blocks coords) ℚ) := by
    apply MvPolynomial.algHom_ext
    intro x
    simp [familyBlockLinearChange_X, familyBlockLinearForm,
      Matrix.one_apply]
  exact DFunLike.congr_fun hhom P

/-- If every block matrix has nonzero determinant, applying its pointwise
nonsingular inverse after it recovers the original polynomial. -/
theorem familyBlockLinearChange_nonsingInv_leftInverse {blocks coords : ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ)
    (hT : ∀ h, (T h).det ≠ 0)
    (P : MvPolynomial (BlockVar blocks coords) ℚ) :
    familyBlockLinearChange (fun h ↦ (T h)⁻¹)
        (familyBlockLinearChange T P) = P := by
  rw [familyBlockLinearChange_comp]
  have hmat :
      (fun h ↦ T h * (T h)⁻¹) =
        (fun _ ↦ (1 : Matrix (Fin coords) (Fin coords) ℚ)) := by
    funext h
    exact Matrix.mul_nonsing_inv (T h) (isUnit_iff_ne_zero.mpr (hT h))
  rw [hmat, familyBlockLinearChange_one]

/-- A family of invertible block matrices induces an injective substitution
on the whole polynomial ring. -/
theorem familyBlockLinearChange_injective {blocks coords : ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ)
    (hT : ∀ h, (T h).det ≠ 0) :
    Function.Injective (familyBlockLinearChange T) := by
  intro P Q hPQ
  have h := congrArg (familyBlockLinearChange (fun h ↦ (T h)⁻¹)) hPQ
  simpa only [familyBlockLinearChange_nonsingInv_leftInverse T hT] using h

/-- Invertible blockwise substitution preserves nonzero polynomials. -/
theorem familyBlockLinearChange_ne_zero {blocks coords : ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ)
    (hT : ∀ h, (T h).det ≠ 0)
    {P : MvPolynomial (BlockVar blocks coords) ℚ} (hP : P ≠ 0) :
    familyBlockLinearChange T P ≠ 0 := by
  intro hzero
  apply hP
  apply familyBlockLinearChange_injective T hT
  simpa using hzero

/-! ## Fixed-multidegree coefficient matrices -/

/-- The tensor product of the symmetric-power matrices belonging to the
individual blocks.  Rows are new multiexponents and columns are old
multiexponents. -/
def familyMultiblockSymmetricPowerMatrix {blocks coords : ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ)
    (degree : Fin blocks → ℕ) :
    Matrix (AuxiliaryPolynomial.MonomialIndex blocks coords degree)
      (AuxiliaryPolynomial.MonomialIndex blocks coords degree) ℚ :=
  fun new old ↦ ∏ h,
    SymmetricPower.symmetricPowerMatrix (T h) (degree h) (new h) (old h)

@[simp] theorem familyMultiblockSymmetricPowerMatrix_apply
    {blocks coords : ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ)
    (degree : Fin blocks → ℕ)
    (new old : AuxiliaryPolynomial.MonomialIndex blocks coords degree) :
    familyMultiblockSymmetricPowerMatrix T degree new old =
      ∏ h, SymmetricPower.symmetricPowerMatrix
        (T h) (degree h) (new h) (old h) :=
  rfl

/-- Change the outer variables of a Taylor polynomial by the same
block-dependent family, leaving its coefficient ring fixed. -/
def outerFamilyBlockLinearForm {blocks coords : ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ)
    (x : BlockVar blocks coords) :
    MvPolynomial (BlockVar blocks coords)
      (MvPolynomial (BlockVar blocks coords) ℚ) :=
  ∑ j, MvPolynomial.C (MvPolynomial.C (T x.1 x.2 j)) *
    MvPolynomial.X (x.1, j)

def outerFamilyBlockLinearChange {blocks coords : ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ) :
    MvPolynomial (BlockVar blocks coords)
        (MvPolynomial (BlockVar blocks coords) ℚ) →ₐ[
      MvPolynomial (BlockVar blocks coords) ℚ]
      MvPolynomial (BlockVar blocks coords)
        (MvPolynomial (BlockVar blocks coords) ℚ) :=
  MvPolynomial.eval₂AlgHom _ (outerFamilyBlockLinearForm T)

/-- Taylor expansion commutes with a block-dependent linear substitution. -/
theorem taylor_familyBlockLinearChange {blocks coords : ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ)
    (P : MvPolynomial (BlockVar blocks coords) ℚ) :
    SymmetricPower.taylor (familyBlockLinearChange T P) =
      outerFamilyBlockLinearChange T
        (MvPolynomial.map (familyBlockLinearChange T).toRingHom
          (SymmetricPower.taylor P)) := by
  let F : MvPolynomial (BlockVar blocks coords) ℚ →ₐ[ℚ]
      MvPolynomial (BlockVar blocks coords)
        (MvPolynomial (BlockVar blocks coords) ℚ) :=
    (outerFamilyBlockLinearChange T).restrictScalars ℚ |>.comp
      (MvPolynomial.mapAlgHom (familyBlockLinearChange T)) |>.comp
        SymmetricPower.taylor
  have hhom :
      SymmetricPower.taylor.comp (familyBlockLinearChange T) = F := by
    apply MvPolynomial.algHom_ext
    intro x
    simp [F, SymmetricPower.taylor, familyBlockLinearChange,
      familyBlockLinearForm, outerFamilyBlockLinearChange,
      outerFamilyBlockLinearForm]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  exact DFunLike.congr_fun hhom P

/-- The unrestricted all-order Hasse chain rule for a block-dependent
coordinate family. -/
theorem hasseDerivative_familyBlockLinearChange {blocks coords : ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ)
    (a : BlockVar blocks coords →₀ ℕ)
    (P : MvPolynomial (BlockVar blocks coords) ℚ) :
    SymmetricPower.hasseDerivative a (familyBlockLinearChange T P) =
      ∑ i ∈ (SymmetricPower.taylor P).support,
        MvPolynomial.coeff a
          (outerFamilyBlockLinearChange T (MvPolynomial.monomial i 1)) *
          familyBlockLinearChange T (SymmetricPower.hasseDerivative i P) := by
  rw [SymmetricPower.hasseDerivative, taylor_familyBlockLinearChange]
  conv_lhs =>
    rhs
    rw [MvPolynomial.as_sum (SymmetricPower.taylor P)]
  simp only [map_sum, MvPolynomial.map_monomial,
    outerFamilyBlockLinearChange, map_sum, MvPolynomial.coeff_sum,
    SymmetricPower.hasseDerivative]
  apply Finset.sum_congr rfl
  intro i hi
  change MvPolynomial.coeff a
      (outerFamilyBlockLinearChange T
        (MvPolynomial.monomial i
          (familyBlockLinearChange T
            (MvPolynomial.coeff i (SymmetricPower.taylor P))))) = _
  rw [show MvPolynomial.monomial i
      (familyBlockLinearChange T
        (MvPolynomial.coeff i (SymmetricPower.taylor P))) =
      MvPolynomial.C (familyBlockLinearChange T
        (MvPolynomial.coeff i (SymmetricPower.taylor P))) *
        MvPolynomial.monomial i 1 by
      rw [MvPolynomial.C_mul_monomial, mul_one],
    map_mul]
  rw [show outerFamilyBlockLinearChange T
      (MvPolynomial.C (familyBlockLinearChange T
        (MvPolynomial.coeff i (SymmetricPower.taylor P)))) =
      MvPolynomial.C (familyBlockLinearChange T
        (MvPolynomial.coeff i (SymmetricPower.taylor P))) by
    simp [outerFamilyBlockLinearChange]]
  rw [MvPolynomial.coeff_C_mul, mul_comm]
  rfl

theorem renameBlock_linearForm_family {blocks coords : ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ)
    (h : Fin blocks) (i : Fin coords) :
    SymmetricPower.renameBlock h (SymmetricPower.linearForm (T h) i) =
      familyBlockLinearForm T (h, i) := by
  simp [SymmetricPower.renameBlock, SymmetricPower.linearForm,
    familyBlockLinearForm]

/-- A changed multiblock monomial factors into independently changed
one-block monomials. -/
theorem familyBlockLinearChange_monomial_eq_prod {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ)
    (old : AuxiliaryPolynomial.MonomialIndex blocks coords degree) :
    familyBlockLinearChange T
        (MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp old) 1) =
      ∏ h, SymmetricPower.renameBlock h
        (SymmetricPower.linearChange (T h)
          (MvPolynomial.monomial
            (SymmetricPower.exponentFinsupp (old h)) 1)) := by
  classical
  simp only [familyBlockLinearChange, MvPolynomial.eval₂AlgHom_apply,
    MvPolynomial.eval₂Hom_monomial, map_one, one_mul,
    SymmetricPower.linearChange, MvPolynomial.eval₂AlgHom_apply,
    MvPolynomial.eval₂Hom_monomial, map_one, one_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  simp_rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), map_prod,
    map_pow, renameBlock_linearForm_family]
  rw [Fintype.prod_prod_type]
  simp [AuxiliaryPolynomial.toFinsupp_apply, AuxiliaryPolynomial.exponent,
    SymmetricPower.exponentFinsupp_apply]

/-- A changed basis monomial has the tensor-product symmetric-power column
as its full fixed-multidegree coefficient vector. -/
theorem familyBlockLinearChange_monomial_eq_ofCoefficients
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ)
    (old : AuxiliaryPolynomial.MonomialIndex blocks coords degree) :
    familyBlockLinearChange T
        (MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp old) 1) =
      AuxiliaryPolynomial.ofCoefficients
        (fun new : AuxiliaryPolynomial.MonomialIndex blocks coords degree ↦
          familyMultiblockSymmetricPowerMatrix T degree new old) := by
  rw [familyBlockLinearChange_monomial_eq_prod]
  have hone (h : Fin blocks) :
      SymmetricPower.linearChange (T h)
          (MvPolynomial.monomial
            (SymmetricPower.exponentFinsupp (old h)) 1) =
        SymmetricPower.ofBlockCoefficients
          (fun new : AuxiliaryPolynomial.BlockExponent coords (degree h) ↦
            SymmetricPower.symmetricPowerMatrix
              (T h) (degree h) new (old h)) := by
    symm
    exact SymmetricPower.ofBlockCoefficients_coeff_of_isHomogeneous
      (SymmetricPower.linearChange_isHomogeneous (T h)
        (MvPolynomial.isHomogeneous_monomial 1
          (SymmetricPower.exponentFinsupp_degree (old h))))
  simp_rw [hone]
  rw [SymmetricPower.prod_renameBlock_ofBlockCoefficients]
  rfl

theorem coeff_familyBlockLinearChange_monomial {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ)
    (new old : AuxiliaryPolynomial.MonomialIndex blocks coords degree) :
    MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp new)
        (familyBlockLinearChange T
          (MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp old) 1)) =
      familyMultiblockSymmetricPowerMatrix T degree new old := by
  rw [familyBlockLinearChange_monomial_eq_ofCoefficients,
    AuxiliaryPolynomial.coeff_ofCoefficients]

theorem coeff_familyBlockLinearChange_monomial_eq_zero_of_degree_ne
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ)
    (new : AuxiliaryPolynomial.MonomialIndex blocks coords degree)
    (d : BlockVar blocks coords →₀ ℕ)
    (hne : SymmetricPower.blockDegreeOfFinsupp d ≠ degree) :
    MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp new)
        (familyBlockLinearChange T (MvPolynomial.monomial d 1)) = 0 := by
  rw [← SymmetricPower.toFinsupp_monomialIndexOfFinsupp d,
    familyBlockLinearChange_monomial_eq_ofCoefficients]
  apply MvPolynomial.notMem_support_iff.mp
  intro hmem
  have hblock := AuxiliaryPolynomial.blockDegree_of_mem_support
    (fun A : AuxiliaryPolynomial.MonomialIndex blocks coords
      (SymmetricPower.blockDegreeOfFinsupp d) ↦
        familyMultiblockSymmetricPowerMatrix T
          (SymmetricPower.blockDegreeOfFinsupp d) A
          (SymmetricPower.monomialIndexOfFinsupp d)) hmem
  apply hne
  funext h
  calc
    SymmetricPower.blockDegreeOfFinsupp d h =
        ∑ j, ((new h).1 j : ℕ) := by
      simpa only [AuxiliaryPolynomial.toFinsupp_apply,
        AuxiliaryPolynomial.exponent] using (hblock h).symm
    _ = degree h := (new h).2

theorem coeff_familyBlockLinearChange_monomial_of_degree_eq
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ)
    (new : AuxiliaryPolynomial.MonomialIndex blocks coords degree)
    (d : BlockVar blocks coords →₀ ℕ)
    (hdegree : SymmetricPower.blockDegreeOfFinsupp d = degree) :
    MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp new)
        (familyBlockLinearChange T (MvPolynomial.monomial d 1)) =
      familyMultiblockSymmetricPowerMatrix T degree new
        (SymmetricPower.monomialIndexOfFinsuppOfEq d hdegree) := by
  let old := SymmetricPower.monomialIndexOfFinsuppOfEq d hdegree
  have hold : AuxiliaryPolynomial.toFinsupp old = d := by simp [old]
  calc
    MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp new)
        (familyBlockLinearChange T (MvPolynomial.monomial d 1)) =
        MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp new)
          (familyBlockLinearChange T
            (MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp old) 1)) := by
      rw [hold]
    _ = familyMultiblockSymmetricPowerMatrix T degree new old :=
      coeff_familyBlockLinearChange_monomial T new old
    _ = familyMultiblockSymmetricPowerMatrix T degree new
        (SymmetricPower.monomialIndexOfFinsuppOfEq d hdegree) := rfl

theorem outerFamilyBlockLinearChange_monomial {blocks coords : ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ)
    (d : BlockVar blocks coords →₀ ℕ) :
    outerFamilyBlockLinearChange T (MvPolynomial.monomial d 1) =
      MvPolynomial.map (MvPolynomial.C : ℚ →+*
        MvPolynomial (BlockVar blocks coords) ℚ)
        (familyBlockLinearChange T (MvPolynomial.monomial d 1)) := by
  simp only [outerFamilyBlockLinearChange, MvPolynomial.eval₂AlgHom_apply,
    MvPolynomial.eval₂Hom_monomial, map_one, one_mul,
    familyBlockLinearChange]
  calc
    (d.prod fun i k ↦ outerFamilyBlockLinearForm T i ^ k) =
        ∏ i, outerFamilyBlockLinearForm T i ^ d i :=
      Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)
    _ = ∏ i, MvPolynomial.map (MvPolynomial.C : ℚ →+*
        MvPolynomial (BlockVar blocks coords) ℚ)
          (familyBlockLinearForm T i ^ d i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [outerFamilyBlockLinearForm, familyBlockLinearForm]
    _ = MvPolynomial.map (MvPolynomial.C : ℚ →+*
        MvPolynomial (BlockVar blocks coords) ℚ)
          (∏ i, familyBlockLinearForm T i ^ d i) := by
      rw [map_prod]
    _ = MvPolynomial.map (MvPolynomial.C : ℚ →+*
        MvPolynomial (BlockVar blocks coords) ℚ)
          (d.prod fun i k ↦ familyBlockLinearForm T i ^ k) := by
      rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]

theorem coeff_outerFamilyBlockLinearChange_monomial {blocks coords : ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ)
    (a d : BlockVar blocks coords →₀ ℕ) :
    MvPolynomial.coeff a
        (outerFamilyBlockLinearChange T (MvPolynomial.monomial d 1)) =
      MvPolynomial.C (MvPolynomial.coeff a
        (familyBlockLinearChange T (MvPolynomial.monomial d 1))) := by
  rw [outerFamilyBlockLinearChange_monomial]
  rfl

/-- The all-order Hasse chain rule at a prescribed derivative
multidegree.  The coefficient matrix is the tensor product of the
block-specific symmetric-power matrices. -/
theorem hasseDerivative_familyBlockLinearChange_fixed {blocks coords : ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ)
    (degree : Fin blocks → ℕ)
    (new : AuxiliaryPolynomial.MonomialIndex blocks coords degree)
    (P : MvPolynomial (BlockVar blocks coords) ℚ) :
    SymmetricPower.hasseDerivative (AuxiliaryPolynomial.toFinsupp new)
        (familyBlockLinearChange T P) =
      ∑ old : AuxiliaryPolynomial.MonomialIndex blocks coords degree,
        MvPolynomial.C
            (familyMultiblockSymmetricPowerMatrix T degree new old) *
          familyBlockLinearChange T
            (SymmetricPower.hasseDerivative
              (AuxiliaryPolynomial.toFinsupp old) P) := by
  rw [hasseDerivative_familyBlockLinearChange]
  let S := (SymmetricPower.taylor P).support
  let Sd := S.filter
    (fun d ↦ SymmetricPower.blockDegreeOfFinsupp d = degree)
  let SI := (Finset.univ : Finset
    (AuxiliaryPolynomial.MonomialIndex blocks coords degree)).filter
      (fun old ↦ AuxiliaryPolynomial.toFinsupp old ∈ S)
  have hrestrict :
      (∑ d ∈ S,
        MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp new)
            (outerFamilyBlockLinearChange T (MvPolynomial.monomial d 1)) *
          familyBlockLinearChange T
            (SymmetricPower.hasseDerivative d P)) =
      ∑ d ∈ Sd,
        MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp new)
            (outerFamilyBlockLinearChange T (MvPolynomial.monomial d 1)) *
          familyBlockLinearChange T
            (SymmetricPower.hasseDerivative d P) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hdS hdnot
    have hne : SymmetricPower.blockDegreeOfFinsupp d ≠ degree := by
      simpa [Sd, hdS] using hdnot
    rw [coeff_outerFamilyBlockLinearChange_monomial,
      coeff_familyBlockLinearChange_monomial_eq_zero_of_degree_ne
        T new d hne]
    simp
  rw [hrestrict]
  calc
    (∑ d ∈ Sd,
        MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp new)
            (outerFamilyBlockLinearChange T (MvPolynomial.monomial d 1)) *
          familyBlockLinearChange T
            (SymmetricPower.hasseDerivative d P)) =
      ∑ old ∈ SI,
        MvPolynomial.C
            (familyMultiblockSymmetricPowerMatrix T degree new old) *
          familyBlockLinearChange T
            (SymmetricPower.hasseDerivative
              (AuxiliaryPolynomial.toFinsupp old) P) := by
      apply Finset.sum_bij
        (fun d hd ↦ SymmetricPower.monomialIndexOfFinsuppOfEq d
          ((Finset.mem_filter.mp hd).2))
      · intro d hd
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        have hdS := (Finset.mem_filter.mp hd).1
        simpa [SI, S] using hdS
      · intro d₁ hd₁ d₂ hd₂ heq
        apply Finsupp.ext
        intro x
        have := congrArg (fun old ↦
          AuxiliaryPolynomial.toFinsupp old x) heq
        simpa using this
      · intro old hold
        refine ⟨AuxiliaryPolynomial.toFinsupp old, ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          refine ⟨?_, ?_⟩
          · exact (Finset.mem_filter.mp hold).2
          · funext h
            exact (old h).2
        · apply AuxiliaryPolynomial.toFinsupp_injective
          simp
      · intro d hd
        rw [coeff_outerFamilyBlockLinearChange_monomial,
          coeff_familyBlockLinearChange_monomial_of_degree_eq T new d
            ((Finset.mem_filter.mp hd).2)]
        rw [SymmetricPower.toFinsupp_monomialIndexOfFinsuppOfEq]
    _ = ∑ old : AuxiliaryPolynomial.MonomialIndex blocks coords degree,
        MvPolynomial.C
            (familyMultiblockSymmetricPowerMatrix T degree new old) *
          familyBlockLinearChange T
            (SymmetricPower.hasseDerivative
              (AuxiliaryPolynomial.toFinsupp old) P) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro old holduniv holdnot
      have hnotmem : AuxiliaryPolynomial.toFinsupp old ∉ S := by
        simpa [SI] using holdnot
      have hzero : SymmetricPower.hasseDerivative
          (AuxiliaryPolynomial.toFinsupp old) P = 0 := by
        rw [SymmetricPower.hasseDerivative]
        exact MvPolynomial.notMem_support_iff.mp (by simpa [S] using hnotmem)
      rw [hzero, map_zero, mul_zero]

/-- If a transformed fixed-order Hasse derivative is nonzero at a point,
then one of the pre-change derivatives with the same block totals remains
nonzero at that point after applying the family change. -/
theorem exists_eval_familyBlockLinearChange_hasseDerivative_ne_zero
    {blocks coords : ℕ}
    (T : Fin blocks → Matrix (Fin coords) (Fin coords) ℚ)
    (degree : Fin blocks → ℕ)
    (new : AuxiliaryPolynomial.MonomialIndex blocks coords degree)
    (P : MvPolynomial (BlockVar blocks coords) ℚ)
    (z : BlockVar blocks coords → ℚ)
    (hne : MvPolynomial.eval z
      (SymmetricPower.hasseDerivative (AuxiliaryPolynomial.toFinsupp new)
        (familyBlockLinearChange T P)) ≠ 0) :
    ∃ old : AuxiliaryPolynomial.MonomialIndex blocks coords degree,
      MvPolynomial.eval z
        (familyBlockLinearChange T
          (SymmetricPower.hasseDerivative
            (AuxiliaryPolynomial.toFinsupp old) P)) ≠ 0 := by
  by_contra hex
  push Not at hex
  apply hne
  rw [hasseDerivative_familyBlockLinearChange_fixed]
  simp only [map_sum, map_mul, MvPolynomial.eval_C]
  apply Finset.sum_eq_zero
  intro old hold
  rw [hex old, mul_zero]

end

end Erdos407.BlockFamilyLinearChange
