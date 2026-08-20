/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos407.AuxiliaryPolynomial
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-!
# Invertibility of homogeneous coefficient changes

An invertible linear change of `coords` variables induces an invertible
change on the coefficient vectors of homogeneous polynomials of every fixed
degree.  This file gives the coefficient matrix with the orientation used by
the GLR auxiliary-polynomial argument: rows are exponents after the change,
and columns are exponents before the change.

The last section takes the dependent product of these symmetric-power
matrices.  It applies one fixed coordinate change independently in every
block and therefore acts on `AuxiliaryPolynomial.MonomialIndex` coefficient
vectors of any prescribed multidegree.
-/

namespace Erdos407.SymmetricPower

open scoped BigOperators Matrix
open Finset

noncomputable section

/-! ## One homogeneous block -/

/-- The ordinary finitely-supported exponent represented by a bounded exact
block exponent. -/
def exponentFinsupp {coords degree : ℕ}
    (e : AuxiliaryPolynomial.BlockExponent coords degree) : Fin coords →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i ↦ (e.1 i : ℕ))

@[simp] theorem exponentFinsupp_apply {coords degree : ℕ}
    (e : AuxiliaryPolynomial.BlockExponent coords degree) (i : Fin coords) :
    exponentFinsupp e i = (e.1 i : ℕ) := by
  rfl

theorem exponentFinsupp_degree {coords degree : ℕ}
    (e : AuxiliaryPolynomial.BlockExponent coords degree) :
    (exponentFinsupp e).degree = degree := by
  rw [Finsupp.degree_eq_sum]
  exact e.2

theorem exponentFinsupp_injective {coords degree : ℕ} :
    Function.Injective
      (exponentFinsupp : AuxiliaryPolynomial.BlockExponent coords degree →
        Fin coords →₀ ℕ) := by
  intro e f hef
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrArg (fun d : Fin coords →₀ ℕ ↦ d i) hef

/-- The homogeneous polynomial represented by a full coefficient vector for
one exact degree. -/
def ofBlockCoefficients {coords degree : ℕ}
    (c : AuxiliaryPolynomial.BlockExponent coords degree → ℚ) :
    MvPolynomial (Fin coords) ℚ :=
  ∑ e, MvPolynomial.monomial (exponentFinsupp e) (c e)

@[simp] theorem coeff_ofBlockCoefficients {coords degree : ℕ}
    (c : AuxiliaryPolynomial.BlockExponent coords degree → ℚ)
    (e : AuxiliaryPolynomial.BlockExponent coords degree) :
    MvPolynomial.coeff (exponentFinsupp e) (ofBlockCoefficients c) = c e := by
  classical
  simp only [ofBlockCoefficients, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single e]
  · simp
  · intro f _ hfe
    simp only [ite_eq_right_iff]
    intro h
    exact (hfe (exponentFinsupp_injective h)).elim
  · simp

theorem ofBlockCoefficients_isHomogeneous {coords degree : ℕ}
    (c : AuxiliaryPolynomial.BlockExponent coords degree → ℚ) :
    (ofBlockCoefficients c).IsHomogeneous degree := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro e he
  exact MvPolynomial.isHomogeneous_monomial _ (exponentFinsupp_degree e)

private def blockExponentOfFinsupp {coords degree : ℕ}
    (d : Fin coords →₀ ℕ) (hd : d.degree = degree) :
    AuxiliaryPolynomial.BlockExponent coords degree :=
  ⟨fun i ↦ ⟨d i, Nat.lt_succ_of_le <| by
      calc
        d i ≤ ∑ j, d j := Finset.single_le_sum
          (fun j _ ↦ Nat.zero_le (d j)) (Finset.mem_univ i)
        _ = degree := by rw [← Finsupp.degree_eq_sum, hd]⟩,
    by rw [← Finsupp.degree_eq_sum, hd]⟩

@[simp] private theorem exponentFinsupp_blockExponentOfFinsupp
    {coords degree : ℕ} (d : Fin coords →₀ ℕ) (hd : d.degree = degree) :
    exponentFinsupp (blockExponentOfFinsupp d hd) = d := by
  ext i
  rfl

/-- Reconstructing the full exact-degree coefficient vector of a homogeneous
polynomial gives the polynomial back. -/
theorem ofBlockCoefficients_coeff_of_isHomogeneous {coords degree : ℕ}
    {P : MvPolynomial (Fin coords) ℚ} (hP : P.IsHomogeneous degree) :
    ofBlockCoefficients (degree := degree)
        (fun e : AuxiliaryPolynomial.BlockExponent coords degree ↦
          MvPolynomial.coeff (exponentFinsupp e) P) = P := by
  classical
  apply MvPolynomial.ext
  intro d
  by_cases hd : d.degree = degree
  · let e := blockExponentOfFinsupp d hd
    have he : exponentFinsupp e = d := by simp [e]
    rw [← he, coeff_ofBlockCoefficients]
  · rw [(ofBlockCoefficients_isHomogeneous _).coeff_eq_zero hd,
      hP.coeff_eq_zero hd]

/-- The linear form replacing the old coordinate `i`. -/
def linearForm {coords : ℕ} (T : Matrix (Fin coords) (Fin coords) ℚ)
    (i : Fin coords) : MvPolynomial (Fin coords) ℚ :=
  ∑ j, MvPolynomial.C (T i j) * MvPolynomial.X j

/-- Substitute `X_i ↦ ∑ j, T i j X_j`.  Thus `T` has old-coordinate rows
and new-coordinate columns. -/
def linearChange {coords : ℕ} (T : Matrix (Fin coords) (Fin coords) ℚ) :
    MvPolynomial (Fin coords) ℚ →ₐ[ℚ] MvPolynomial (Fin coords) ℚ :=
  MvPolynomial.eval₂AlgHom ℚ (linearForm T)

@[simp] theorem linearChange_C {coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ) (a : ℚ) :
    linearChange T (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [linearChange]

@[simp] theorem linearChange_X {coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ) (i : Fin coords) :
    linearChange T (MvPolynomial.X i) = linearForm T i := by
  simp [linearChange]

theorem linearForm_isHomogeneous {coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ) (i : Fin coords) :
    (linearForm T i).IsHomogeneous 1 := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  exact (MvPolynomial.isHomogeneous_X ℚ j).C_mul (T i j)

theorem linearChange_isHomogeneous {coords degree : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ)
    {P : MvPolynomial (Fin coords) ℚ} (hP : P.IsHomogeneous degree) :
    (linearChange T P).IsHomogeneous degree := by
  change (MvPolynomial.eval₂ MvPolynomial.C (linearForm T) P).IsHomogeneous degree
  simpa only [one_mul] using hP.eval₂ MvPolynomial.C (linearForm T)
    (fun a ↦ MvPolynomial.isHomogeneous_C _ _) (linearForm_isHomogeneous T)

/-- Composition follows matrix multiplication in the stated old-row,
new-column convention. -/
theorem linearChange_comp {coords : ℕ}
    (T U : Matrix (Fin coords) (Fin coords) ℚ)
    (P : MvPolynomial (Fin coords) ℚ) :
    linearChange U (linearChange T P) = linearChange (T * U) P := by
  have hhom : (linearChange U).comp (linearChange T) = linearChange (T * U) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, linearChange_X, linearForm, map_sum, map_mul,
      linearChange_C]
    simp only [Matrix.mul_apply, map_sum,
      MvPolynomial.C_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  exact DFunLike.congr_fun hhom P

@[simp] theorem linearChange_one {coords : ℕ}
    (P : MvPolynomial (Fin coords) ℚ) :
    linearChange (1 : Matrix (Fin coords) (Fin coords) ℚ) P = P := by
  have hhom : linearChange (1 : Matrix (Fin coords) (Fin coords) ℚ) =
      AlgHom.id ℚ (MvPolynomial (Fin coords) ℚ) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [linearForm, Matrix.one_apply]
  exact DFunLike.congr_fun hhom P

/-- The degree-`degree` symmetric-power coefficient matrix of `T`.  Its row
is the new exponent and its column is the old exponent. -/
def symmetricPowerMatrix {coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ) (degree : ℕ) :
    Matrix (AuxiliaryPolynomial.BlockExponent coords degree)
      (AuxiliaryPolynomial.BlockExponent coords degree) ℚ :=
  fun new old ↦ MvPolynomial.coeff (exponentFinsupp new)
    (linearChange T (MvPolynomial.monomial (exponentFinsupp old) 1))

@[simp] theorem symmetricPowerMatrix_apply {coords degree : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ)
    (new old : AuxiliaryPolynomial.BlockExponent coords degree) :
    symmetricPowerMatrix T degree new old =
      MvPolynomial.coeff (exponentFinsupp new)
        (linearChange T (MvPolynomial.monomial (exponentFinsupp old) 1)) :=
  rfl

theorem linearChange_monomial_coeff {coords degree : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ)
    (new old : AuxiliaryPolynomial.BlockExponent coords degree) :
    MvPolynomial.coeff (exponentFinsupp new)
        (linearChange T (MvPolynomial.monomial (exponentFinsupp old) 1)) =
      symmetricPowerMatrix T degree new old :=
  rfl

/-- Matrix multiplication by `symmetricPowerMatrix` computes the coefficient
vector after the linear substitution. -/
theorem symmetricPowerMatrix_mulVec {coords degree : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ)
    (c : AuxiliaryPolynomial.BlockExponent coords degree → ℚ) :
    symmetricPowerMatrix T degree *ᵥ c = fun new ↦
      MvPolynomial.coeff (exponentFinsupp new)
        (linearChange T (ofBlockCoefficients c)) := by
  classical
  funext new
  simp only [Matrix.mulVec, dotProduct, symmetricPowerMatrix,
    ofBlockCoefficients, map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro old hold
  rw [show MvPolynomial.monomial (exponentFinsupp old) (c old) =
      MvPolynomial.C (c old) *
        MvPolynomial.monomial (exponentFinsupp old) 1 by
      rw [MvPolynomial.C_mul_monomial, mul_one],
    map_mul, linearChange_C, MvPolynomial.coeff_C_mul]
  ring

/-- Repackaging the transformed coefficients reproduces the transformed
homogeneous polynomial. -/
theorem ofBlockCoefficients_symmetricPowerMatrix_mulVec {coords degree : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ)
    (c : AuxiliaryPolynomial.BlockExponent coords degree → ℚ) :
    ofBlockCoefficients (symmetricPowerMatrix T degree *ᵥ c) =
      linearChange T (ofBlockCoefficients c) := by
  rw [symmetricPowerMatrix_mulVec]
  exact ofBlockCoefficients_coeff_of_isHomogeneous
    (linearChange_isHomogeneous T (ofBlockCoefficients_isHomogeneous c))

/-- A right inverse of the coordinate matrix gives a left inverse of its
symmetric-power action. -/
theorem symmetricPowerMatrix_mulVec_leftInverse {coords degree : ℕ}
    (T U : Matrix (Fin coords) (Fin coords) ℚ) (hTU : T * U = 1)
    (c : AuxiliaryPolynomial.BlockExponent coords degree → ℚ) :
    symmetricPowerMatrix U degree *ᵥ
        (symmetricPowerMatrix T degree *ᵥ c) = c := by
  funext new
  calc
    (symmetricPowerMatrix U degree *ᵥ
        (symmetricPowerMatrix T degree *ᵥ c)) new =
        MvPolynomial.coeff (exponentFinsupp new)
          (linearChange U
            (ofBlockCoefficients (symmetricPowerMatrix T degree *ᵥ c))) :=
      congrFun (symmetricPowerMatrix_mulVec U _) new
    _ = MvPolynomial.coeff (exponentFinsupp new)
        (linearChange U (linearChange T (ofBlockCoefficients c))) := by
      rw [ofBlockCoefficients_symmetricPowerMatrix_mulVec]
    _ = MvPolynomial.coeff (exponentFinsupp new)
        (linearChange (T * U) (ofBlockCoefficients c)) := by
      rw [linearChange_comp]
    _ = c new := by
      rw [hTU, linearChange_one, coeff_ofBlockCoefficients]

theorem symmetricPowerMatrix_mul_eq_one {coords degree : ℕ}
    (T U : Matrix (Fin coords) (Fin coords) ℚ) (hTU : T * U = 1) :
    symmetricPowerMatrix U degree * symmetricPowerMatrix T degree = 1 := by
  apply Matrix.mulVec_injective
  funext c
  rw [← Matrix.mulVec_mulVec, symmetricPowerMatrix_mulVec_leftInverse T U hTU,
    Matrix.one_mulVec]

/-- The symmetric-power coefficient transformation is injective whenever
the original rational matrix is nonsingular. -/
theorem symmetricPowerMatrix_mulVec_injective {coords degree : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ) (hT : T.det ≠ 0) :
    Function.Injective (symmetricPowerMatrix T degree).mulVec := by
  classical
  have hunit : IsUnit T.det := isUnit_iff_ne_zero.mpr hT
  apply Function.LeftInverse.injective
    (g := (symmetricPowerMatrix T⁻¹ degree).mulVec)
  intro c
  exact symmetricPowerMatrix_mulVec_leftInverse T T⁻¹
    (Matrix.mul_nonsing_inv T hunit) c

/-- The symmetric-power coefficient transformation is surjective whenever
the original rational matrix is nonsingular. -/
theorem symmetricPowerMatrix_mulVec_surjective {coords degree : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ) (hT : T.det ≠ 0) :
    Function.Surjective (symmetricPowerMatrix T degree).mulVec := by
  classical
  have hunit : IsUnit T.det := isUnit_iff_ne_zero.mpr hT
  apply Function.RightInverse.surjective
    (g := (symmetricPowerMatrix T⁻¹ degree).mulVec)
  intro c
  exact symmetricPowerMatrix_mulVec_leftInverse T⁻¹ T
    (Matrix.nonsing_inv_mul T hunit) c

theorem symmetricPowerMatrix_mulVec_bijective {coords degree : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ) (hT : T.det ≠ 0) :
    Function.Bijective (symmetricPowerMatrix T degree).mulVec :=
  ⟨symmetricPowerMatrix_mulVec_injective T hT,
    symmetricPowerMatrix_mulVec_surjective T hT⟩

/-! ## Independent changes in finitely many blocks -/

/-- The product of the fixed-degree symmetric-power matrices, one for every
block.  Rows are new multiexponents and columns are old multiexponents. -/
def multiblockSymmetricPowerMatrix {blocks coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ) (degree : Fin blocks → ℕ) :
    Matrix (AuxiliaryPolynomial.MonomialIndex blocks coords degree)
      (AuxiliaryPolynomial.MonomialIndex blocks coords degree) ℚ :=
  fun new old ↦ ∏ h, symmetricPowerMatrix T (degree h) (new h) (old h)

@[simp] theorem multiblockSymmetricPowerMatrix_apply {blocks coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ) (degree : Fin blocks → ℕ)
    (new old : AuxiliaryPolynomial.MonomialIndex blocks coords degree) :
    multiblockSymmetricPowerMatrix T degree new old =
      ∏ h, symmetricPowerMatrix T (degree h) (new h) (old h) :=
  rfl

theorem multiblockSymmetricPowerMatrix_mul_eq_one {blocks coords : ℕ}
    (T U : Matrix (Fin coords) (Fin coords) ℚ) (degree : Fin blocks → ℕ)
    (hTU : T * U = 1) :
    multiblockSymmetricPowerMatrix U degree *
        multiblockSymmetricPowerMatrix T degree = 1 := by
  classical
  ext new old
  rw [Matrix.mul_apply]
  calc
    (∑ middle,
        multiblockSymmetricPowerMatrix U degree new middle *
          multiblockSymmetricPowerMatrix T degree middle old) =
        ∑ middle : AuxiliaryPolynomial.MonomialIndex blocks coords degree, ∏ h,
          (symmetricPowerMatrix U (degree h) (new h) (middle h) *
            symmetricPowerMatrix T (degree h) (middle h) (old h)) := by
      apply Finset.sum_congr rfl
      intro middle hmiddle
      exact Finset.prod_mul_distrib.symm
    _ = ∏ h, ∑ middle : AuxiliaryPolynomial.BlockExponent coords (degree h),
        symmetricPowerMatrix U (degree h) (new h) middle *
          symmetricPowerMatrix T (degree h) middle (old h) := by
      symm
      simpa only [Fintype.piFinset_univ, sum_filter, mem_univ, ↓reduceIte] using
        (Finset.prod_univ_sum
          (fun h : Fin blocks ↦
            (Finset.univ : Finset
              (AuxiliaryPolynomial.BlockExponent coords (degree h))))
          (fun h middle ↦
            symmetricPowerMatrix U (degree h) (new h) middle *
              symmetricPowerMatrix T (degree h) middle (old h)))
    _ = ∏ h, (1 : Matrix
        (AuxiliaryPolynomial.BlockExponent coords (degree h))
        (AuxiliaryPolynomial.BlockExponent coords (degree h)) ℚ)
          (new h) (old h) := by
      apply Finset.prod_congr rfl
      intro h hh
      exact congrFun (congrFun
        (symmetricPowerMatrix_mul_eq_one T U hTU) (new h)) (old h)
    _ = (1 : Matrix
        (AuxiliaryPolynomial.MonomialIndex blocks coords degree)
        (AuxiliaryPolynomial.MonomialIndex blocks coords degree) ℚ) new old := by
      simp only [Matrix.one_apply]
      by_cases hno : new = old
      · subst old
        simp
      · have hex : ∃ h, new h ≠ old h := by
          contrapose! hno
          exact funext hno
        obtain ⟨h, hh⟩ := hex
        rw [if_neg hno]
        apply Finset.prod_eq_zero (Finset.mem_univ h)
        rw [if_neg hh]

/-- The fixed-multidegree block coefficient transformation is injective. -/
theorem multiblockSymmetricPowerMatrix_mulVec_injective {blocks coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ) (degree : Fin blocks → ℕ)
    (hT : T.det ≠ 0) :
    Function.Injective (multiblockSymmetricPowerMatrix T degree).mulVec := by
  classical
  have hunit : IsUnit T.det := isUnit_iff_ne_zero.mpr hT
  have hleft := multiblockSymmetricPowerMatrix_mul_eq_one
    T T⁻¹ degree (Matrix.mul_nonsing_inv T hunit)
  intro c d hcd
  have := congrArg (multiblockSymmetricPowerMatrix T⁻¹ degree).mulVec hcd
  simpa only [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec] using this

/-- The fixed-multidegree block coefficient transformation is surjective. -/
theorem multiblockSymmetricPowerMatrix_mulVec_surjective {blocks coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ) (degree : Fin blocks → ℕ)
    (hT : T.det ≠ 0) :
    Function.Surjective (multiblockSymmetricPowerMatrix T degree).mulVec := by
  classical
  have hunit : IsUnit T.det := isUnit_iff_ne_zero.mpr hT
  intro c
  refine ⟨multiblockSymmetricPowerMatrix T⁻¹ degree *ᵥ c, ?_⟩
  rw [Matrix.mulVec_mulVec,
    multiblockSymmetricPowerMatrix_mul_eq_one T⁻¹ T degree
      (Matrix.nonsing_inv_mul T hunit),
    Matrix.one_mulVec]

theorem multiblockSymmetricPowerMatrix_mulVec_bijective {blocks coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ) (degree : Fin blocks → ℕ)
    (hT : T.det ≠ 0) :
    Function.Bijective (multiblockSymmetricPowerMatrix T degree).mulVec :=
  ⟨multiblockSymmetricPowerMatrix_mulVec_injective T degree hT,
    multiblockSymmetricPowerMatrix_mulVec_surjective T degree hT⟩

/-- Vanishing of every transformed fixed-multidegree coefficient forces
vanishing of every original coefficient. -/
theorem eq_zero_of_forall_multiblock_sum_eq_zero {blocks coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ) (degree : Fin blocks → ℕ)
    (hT : T.det ≠ 0)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℚ)
    (hzero : ∀ new, ∑ old,
      multiblockSymmetricPowerMatrix T degree new old * c old = 0) :
    ∀ old, c old = 0 := by
  have hmul : multiblockSymmetricPowerMatrix T degree *ᵥ c = 0 := by
    funext new
    change (∑ old,
      multiblockSymmetricPowerMatrix T degree new old * c old) = 0
    exact hzero new
  have hinj := multiblockSymmetricPowerMatrix_mulVec_injective T degree hT
  have hc : c = 0 := by
    apply hinj
    simpa using hmul
  intro old
  exact congrFun hc old

/-! ## Taylor coefficients and the all-order block chain rule -/

/-- A short name for the variables in a block polynomial. -/
abbrev BlockVar (blocks coords : ℕ) :=
  AuxiliaryPolynomial.BlockVar blocks coords

/-- The rational linear form which replaces one old variable in a fixed
block.  The coordinate matrix has old-coordinate rows and new-coordinate
columns. -/
def blockLinearForm {blocks coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ) (x : BlockVar blocks coords) :
    MvPolynomial (BlockVar blocks coords) ℚ :=
  ∑ j, MvPolynomial.C (T x.2 j) * MvPolynomial.X (x.1, j)

/-- Apply the same rational coordinate change independently in every block. -/
def blockLinearChange {blocks coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ) :
    MvPolynomial (BlockVar blocks coords) ℚ →ₐ[ℚ]
      MvPolynomial (BlockVar blocks coords) ℚ :=
  MvPolynomial.eval₂AlgHom ℚ (blockLinearForm T)

/-- The universal Taylor expansion `P(X + Y)`.  The outer polynomial
variables are `Y`; the coefficient polynomials use the variables `X`. -/
def taylor {σ : Type*} :
    MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial σ (MvPolynomial σ ℚ) :=
  MvPolynomial.eval₂AlgHom ℚ
    (fun i ↦ MvPolynomial.C (MvPolynomial.X i) + MvPolynomial.X i)

/-- The coordinate change on the outer (Taylor) variables. -/
def outerBlockLinearForm {blocks coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ) (x : BlockVar blocks coords) :
    MvPolynomial (BlockVar blocks coords)
      (MvPolynomial (BlockVar blocks coords) ℚ) :=
  ∑ j, MvPolynomial.C (MvPolynomial.C (T x.2 j)) *
    MvPolynomial.X (x.1, j)

/-- Apply the block coordinate change to the outer variables of a Taylor
polynomial, leaving its coefficient ring fixed. -/
def outerBlockLinearChange {blocks coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ) :
    MvPolynomial (BlockVar blocks coords)
        (MvPolynomial (BlockVar blocks coords) ℚ) →ₐ[
      MvPolynomial (BlockVar blocks coords) ℚ]
      MvPolynomial (BlockVar blocks coords)
        (MvPolynomial (BlockVar blocks coords) ℚ) :=
  MvPolynomial.eval₂AlgHom _ (outerBlockLinearForm T)

/-- Taylor expansion commutes with a blockwise linear substitution: the
substitution acts on both the coefficient variables and the Taylor
variables. -/
theorem taylor_blockLinearChange {blocks coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ)
    (P : MvPolynomial (BlockVar blocks coords) ℚ) :
    taylor (blockLinearChange T P) =
      outerBlockLinearChange T
        (MvPolynomial.map (blockLinearChange (blocks := blocks) T).toRingHom
          (taylor P)) := by
  let F : MvPolynomial (BlockVar blocks coords) ℚ →ₐ[ℚ]
      MvPolynomial (BlockVar blocks coords)
        (MvPolynomial (BlockVar blocks coords) ℚ) :=
    (outerBlockLinearChange T).restrictScalars ℚ |>.comp
      (MvPolynomial.mapAlgHom (blockLinearChange T)) |>.comp taylor
  have hhom : taylor.comp (blockLinearChange T) = F := by
    apply MvPolynomial.algHom_ext
    intro x
    simp [F, taylor, blockLinearChange, blockLinearForm,
      outerBlockLinearChange, outerBlockLinearForm]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  exact DFunLike.congr_fun hhom P

/-- The multivariate Hasse derivative of order `a`, defined as the
corresponding coefficient of the universal Taylor polynomial. -/
def hasseDerivative {σ : Type*} (a : σ →₀ ℕ)
    (P : MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  MvPolynomial.coeff a (taylor P)

/-- The Hasse derivative of a monomial.  Its coefficient is the product of
the coordinatewise binomial coefficients and its exponent is truncated
subtraction by the derivative order. -/
theorem hasseDerivative_monomial {σ : Type*} [Fintype σ]
    (a : σ →₀ ℕ) (e : σ →₀ ℕ) (q : ℚ) :
    hasseDerivative a (MvPolynomial.monomial e q) =
      MvPolynomial.monomial (e - a)
        (q * ∏ x, (Nat.choose (e x) (a x) : ℚ)) := by
  classical
  have hpow (x : σ) :
      (MvPolynomial.C (MvPolynomial.X x) + MvPolynomial.X x) ^ e x =
        ∑ m ∈ Finset.range (e x + 1),
          MvPolynomial.C (MvPolynomial.X x) ^ (e x - m) *
            MvPolynomial.X x ^ m *
              ((e x).choose m :
                MvPolynomial σ (MvPolynomial σ ℚ)) := by
    rw [add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  have hfactor (x : σ) (m : ℕ) :
      MvPolynomial.C (MvPolynomial.X x) ^ (e x - m) *
          MvPolynomial.X x ^ m *
            ((e x).choose m : MvPolynomial σ (MvPolynomial σ ℚ)) =
        MvPolynomial.C
            (MvPolynomial.X x ^ (e x - m) *
              MvPolynomial.C ((e x).choose m : ℚ)) *
          MvPolynomial.X x ^ m := by
    rw [← map_pow]
    change MvPolynomial.C (MvPolynomial.X x ^ (e x - m)) *
        MvPolynomial.X x ^ m * MvPolynomial.C
          (MvPolynomial.C ((e x).choose m : ℚ)) = _
    rw [mul_assoc, mul_comm (MvPolynomial.X x ^ m), ← mul_assoc,
      ← MvPolynomial.C_mul]
  have hcoeff (b : σ → ℕ) :
      MvPolynomial.coeff a
          (∏ i, MvPolynomial.C (MvPolynomial.X i) ^ (e i - b i) *
            MvPolynomial.X i ^ b i *
              ((e i).choose (b i) : MvPolynomial σ (MvPolynomial σ ℚ))) =
        if (∀ i, b i = a i) then
          MvPolynomial.monomial (e - a)
            (∏ i, ((e i).choose (a i) : ℚ))
        else 0 := by
    simp_rw [hfactor]
    change MvPolynomial.coeff a
      (∏ i ∈ (Finset.univ : Finset σ),
        MvPolynomial.C (MvPolynomial.X i ^ (e i - b i) *
          MvPolynomial.C ((e i).choose (b i) : ℚ)) *
            MvPolynomial.X i ^ b i) = _
    rw [Finset.prod_mul_distrib, ← map_prod, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_prod_X_pow]
    have hind :
        a = Finsupp.indicator (Finset.univ : Finset σ) (fun i _ ↦ b i) ↔
          ∀ i, b i = a i := by
      constructor
      · intro h i
        have hi := DFunLike.congr_fun h i
        simpa using hi.symm
      · intro h
        ext i
        simp [h i]
    by_cases hb : ∀ i, b i = a i
    · rw [if_pos hb, if_pos (hind.mpr hb), mul_one]
      have hba : b = fun i ↦ a i := funext hb
      subst b
      rw [MvPolynomial.monomial_eq]
      change (∏ i ∈ (Finset.univ : Finset σ),
          MvPolynomial.X i ^ (e i - a i) *
            MvPolynomial.C ((e i).choose (a i) : ℚ)) = _
      rw [Finset.prod_mul_distrib, ← map_prod]
      rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
      simp only [Finsupp.coe_tsub, Pi.sub_apply]
      ring
    · have hleft : ¬a = Finsupp.indicator (Finset.univ : Finset σ)
          (fun i _ ↦ b i) := fun h ↦ hb (hind.mp h)
      rw [if_neg hb, if_neg hleft, mul_zero]
  simp [hasseDerivative, taylor]
  simp_rw [hpow]
  rw [Finset.prod_univ_sum]
  rw [MvPolynomial.coeff_sum]
  by_cases ha : ∀ x, a x ≤ e x
  · rw [Finset.sum_eq_single (fun x ↦ a x)]
    · rw [hcoeff]
      simp
      rw [MvPolynomial.C_mul_monomial]
    · intro b hb hba
      rw [hcoeff, if_neg]
      intro hall
      apply hba
      funext i
      exact hall i
    · intro hnot
      exfalso
      apply hnot
      rw [Fintype.mem_piFinset]
      intro i
      simp [ha i]
  · push Not at ha
    obtain ⟨i, hi⟩ := ha
    have hchoose : (∏ x, ((e x).choose (a x) : ℚ)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [Nat.choose_eq_zero_of_lt hi]
      norm_num
    rw [hchoose, mul_zero, MvPolynomial.monomial_zero]
    have hsum :
        (∑ b ∈ Fintype.piFinset (fun x ↦ Finset.range (e x + 1)),
          MvPolynomial.coeff a
            (∏ j, MvPolynomial.C (MvPolynomial.X j) ^ (e j - b j) *
              MvPolynomial.X j ^ b j *
                ((e j).choose (b j) :
                  MvPolynomial σ (MvPolynomial σ ℚ)))) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      rw [hcoeff, if_neg]
      intro hall
      have hbi := hall i
      have hbmem := Fintype.mem_piFinset.mp hb i
      simp only [Finset.mem_range] at hbmem
      omega
    rw [hsum, mul_zero]

/-- The unrestricted all-order chain rule.  The finite sum is over the
Taylor support of `P`; the next lemmas identify the outer coefficients with
the fixed-multidegree symmetric-power matrix. -/
theorem hasseDerivative_blockLinearChange {blocks coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ)
    (a : BlockVar blocks coords →₀ ℕ)
    (P : MvPolynomial (BlockVar blocks coords) ℚ) :
    hasseDerivative a (blockLinearChange T P) =
      ∑ i ∈ (taylor P).support,
        MvPolynomial.coeff a
          (outerBlockLinearChange T (MvPolynomial.monomial i 1)) *
          blockLinearChange T (hasseDerivative i P) := by
  rw [hasseDerivative, taylor_blockLinearChange]
  conv_lhs =>
    rhs
    rw [MvPolynomial.as_sum (taylor P)]
  simp only [map_sum, MvPolynomial.map_monomial,
    outerBlockLinearChange, map_sum, MvPolynomial.coeff_sum,
    hasseDerivative]
  apply Finset.sum_congr rfl
  intro i hi
  change MvPolynomial.coeff a
      (outerBlockLinearChange T
        (MvPolynomial.monomial i
          (blockLinearChange T (MvPolynomial.coeff i (taylor P))))) = _
  rw [show MvPolynomial.monomial i
      (blockLinearChange T (MvPolynomial.coeff i (taylor P))) =
      MvPolynomial.C (blockLinearChange T (MvPolynomial.coeff i (taylor P))) *
        MvPolynomial.monomial i 1 by
      rw [MvPolynomial.C_mul_monomial, mul_one],
    map_mul]
  rw [show outerBlockLinearChange T
      (MvPolynomial.C (blockLinearChange T
        (MvPolynomial.coeff i (taylor P)))) =
      MvPolynomial.C (blockLinearChange T
        (MvPolynomial.coeff i (taylor P))) by
    simp [outerBlockLinearChange]]
  rw [MvPolynomial.coeff_C_mul, mul_comm]
  rfl

/-- Rename the variables of a one-block polynomial into block `h`. -/
def renameBlock {blocks coords : ℕ} (h : Fin blocks) :
    MvPolynomial (Fin coords) ℚ →ₐ[ℚ]
      MvPolynomial (BlockVar blocks coords) ℚ :=
  MvPolynomial.rename (fun j ↦ (h, j))

theorem renameBlock_linearForm {blocks coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ) (h : Fin blocks)
    (i : Fin coords) :
    renameBlock h (linearForm T i) = blockLinearForm T (h, i) := by
  simp [renameBlock, linearForm, blockLinearForm]

/-- A changed multiblock monomial is the product of the independently
changed one-block monomials. -/
theorem blockLinearChange_monomial_eq_prod {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ)
    (old : AuxiliaryPolynomial.MonomialIndex blocks coords degree) :
    blockLinearChange T
        (MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp old) 1) =
      ∏ h, renameBlock h
        (linearChange T
          (MvPolynomial.monomial (exponentFinsupp (old h)) 1)) := by
  classical
  simp only [blockLinearChange, MvPolynomial.eval₂AlgHom_apply,
    MvPolynomial.eval₂Hom_monomial, map_one, one_mul,
    linearChange, MvPolynomial.eval₂AlgHom_apply,
    MvPolynomial.eval₂Hom_monomial, map_one, one_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  simp_rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), map_prod, map_pow,
    renameBlock_linearForm]
  rw [Fintype.prod_prod_type]
  simp [AuxiliaryPolynomial.toFinsupp_apply, AuxiliaryPolynomial.exponent,
    exponentFinsupp_apply]

theorem sum_mapDomain_exponentFinsupp {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (M : AuxiliaryPolynomial.MonomialIndex blocks coords degree) :
    ∑ h, (exponentFinsupp (M h)).mapDomain (fun j ↦ (h, j)) =
      AuxiliaryPolynomial.toFinsupp M := by
  classical
  ext x
  rw [Finset.sum_apply', Finset.sum_eq_single x.1]
  · rw [Finsupp.mapDomain_apply (fun a b hab ↦ congrArg Prod.snd hab)]
    simp [AuxiliaryPolynomial.toFinsupp_apply, AuxiliaryPolynomial.exponent]
  · intro h hh hne
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨j, hj⟩
    exact hne (congrArg Prod.fst hj)
  · simp

/-- The product of renamed full coefficient vectors is the corresponding
multiblock coefficient vector. -/
theorem prod_renameBlock_ofBlockCoefficients {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (c : ∀ h, AuxiliaryPolynomial.BlockExponent coords (degree h) → ℚ) :
    ∏ h, renameBlock h (ofBlockCoefficients (c h)) =
      AuxiliaryPolynomial.ofCoefficients
        (fun M : AuxiliaryPolynomial.MonomialIndex blocks coords degree ↦
          ∏ h, c h (M h)) := by
  classical
  simp only [ofBlockCoefficients, map_sum,
    AuxiliaryPolynomial.ofCoefficients]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr
  · simp [Fintype.piFinset_univ]
  · intro M hM
    simp only [renameBlock, MvPolynomial.rename_monomial]
    have hmono := (MvPolynomial.monomial_sum_prod
      (R := ℚ) (Finset.univ : Finset (Fin blocks))
      (fun h ↦ (exponentFinsupp (M h)).mapDomain (fun j ↦ (h, j)))
      (fun h ↦ c h (M h))).symm
    simpa only [sum_mapDomain_exponentFinsupp] using hmono

/-- A changed basis monomial is the multiblock polynomial whose coefficient
vector is the product symmetric-power column. -/
theorem blockLinearChange_monomial_eq_ofCoefficients {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ)
    (old : AuxiliaryPolynomial.MonomialIndex blocks coords degree) :
    blockLinearChange T
        (MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp old) 1) =
      AuxiliaryPolynomial.ofCoefficients
        (fun new : AuxiliaryPolynomial.MonomialIndex blocks coords degree ↦
          multiblockSymmetricPowerMatrix T degree new old) := by
  rw [blockLinearChange_monomial_eq_prod]
  have hone (h : Fin blocks) :
      linearChange T
          (MvPolynomial.monomial (exponentFinsupp (old h)) 1) =
        ofBlockCoefficients
          (fun new : AuxiliaryPolynomial.BlockExponent coords (degree h) ↦
            symmetricPowerMatrix T (degree h) new (old h)) := by
    symm
    exact ofBlockCoefficients_coeff_of_isHomogeneous
      (linearChange_isHomogeneous T
        (MvPolynomial.isHomogeneous_monomial 1
          (exponentFinsupp_degree (old h))))
  simp_rw [hone]
  rw [prod_renameBlock_ofBlockCoefficients]
  rfl

/-- The coefficient of a changed fixed-multidegree basis monomial is the
corresponding entry of the product symmetric-power matrix. -/
theorem coeff_blockLinearChange_monomial {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ)
    (new old : AuxiliaryPolynomial.MonomialIndex blocks coords degree) :
    MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp new)
        (blockLinearChange T
          (MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp old) 1)) =
      multiblockSymmetricPowerMatrix T degree new old := by
  rw [blockLinearChange_monomial_eq_ofCoefficients,
    AuxiliaryPolynomial.coeff_ofCoefficients]

/-- The vector of total degrees in each block of an arbitrary exponent. -/
def blockDegreeOfFinsupp {blocks coords : ℕ}
    (d : BlockVar blocks coords →₀ ℕ) (h : Fin blocks) : ℕ :=
  ∑ j, d (h, j)

/-- Package an arbitrary exponent as a bounded multiblock exponent, using
its actual block totals. -/
def monomialIndexOfFinsupp {blocks coords : ℕ}
    (d : BlockVar blocks coords →₀ ℕ) :
    AuxiliaryPolynomial.MonomialIndex blocks coords (blockDegreeOfFinsupp d) :=
  fun h ↦
    ⟨fun j ↦ ⟨d (h, j), Nat.lt_succ_of_le <| by
        exact Finset.single_le_sum
          (fun i _ ↦ Nat.zero_le (d (h, i))) (Finset.mem_univ j)⟩,
      rfl⟩

@[simp] theorem toFinsupp_monomialIndexOfFinsupp {blocks coords : ℕ}
    (d : BlockVar blocks coords →₀ ℕ) :
    AuxiliaryPolynomial.toFinsupp (monomialIndexOfFinsupp d) = d := by
  ext x
  rfl

/-- A blockwise linear change cannot turn a monomial of one multidegree
into a monomial of a different multidegree. -/
theorem coeff_blockLinearChange_monomial_eq_zero_of_degree_ne
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ)
    (new : AuxiliaryPolynomial.MonomialIndex blocks coords degree)
    (d : BlockVar blocks coords →₀ ℕ)
    (hne : blockDegreeOfFinsupp d ≠ degree) :
    MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp new)
        (blockLinearChange T (MvPolynomial.monomial d 1)) = 0 := by
  rw [← toFinsupp_monomialIndexOfFinsupp d,
    blockLinearChange_monomial_eq_ofCoefficients]
  apply MvPolynomial.notMem_support_iff.mp
  intro hmem
  have hblock := AuxiliaryPolynomial.blockDegree_of_mem_support
    (fun A : AuxiliaryPolynomial.MonomialIndex blocks coords
      (blockDegreeOfFinsupp d) ↦
        multiblockSymmetricPowerMatrix T (blockDegreeOfFinsupp d) A
          (monomialIndexOfFinsupp d)) hmem
  apply hne
  funext h
  calc
    blockDegreeOfFinsupp d h = ∑ j, ((new h).1 j : ℕ) := by
      simpa only [AuxiliaryPolynomial.toFinsupp_apply,
        AuxiliaryPolynomial.exponent] using (hblock h).symm
    _ = degree h := (new h).2

/-- Transport the canonical index of an exponent to a specified, equal
multidegree. -/
def monomialIndexOfFinsuppOfEq {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (d : BlockVar blocks coords →₀ ℕ)
    (hdegree : blockDegreeOfFinsupp d = degree) :
    AuxiliaryPolynomial.MonomialIndex blocks coords degree :=
  hdegree ▸ monomialIndexOfFinsupp d

@[simp] theorem toFinsupp_monomialIndexOfFinsuppOfEq {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (d : BlockVar blocks coords →₀ ℕ)
    (hdegree : blockDegreeOfFinsupp d = degree) :
    AuxiliaryPolynomial.toFinsupp
      (monomialIndexOfFinsuppOfEq d hdegree) = d := by
  subst degree
  exact toFinsupp_monomialIndexOfFinsupp d

theorem coeff_blockLinearChange_monomial_of_degree_eq
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ)
    (new : AuxiliaryPolynomial.MonomialIndex blocks coords degree)
    (d : BlockVar blocks coords →₀ ℕ)
    (hdegree : blockDegreeOfFinsupp d = degree) :
    MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp new)
        (blockLinearChange T (MvPolynomial.monomial d 1)) =
      multiblockSymmetricPowerMatrix T degree new
        (monomialIndexOfFinsuppOfEq d hdegree) := by
  let old := monomialIndexOfFinsuppOfEq d hdegree
  have hold : AuxiliaryPolynomial.toFinsupp old = d := by simp [old]
  calc
    MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp new)
        (blockLinearChange T (MvPolynomial.monomial d 1)) =
        MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp new)
          (blockLinearChange T
            (MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp old) 1)) := by
      rw [hold]
    _ = multiblockSymmetricPowerMatrix T degree new old :=
      coeff_blockLinearChange_monomial T new old
    _ = multiblockSymmetricPowerMatrix T degree new
        (monomialIndexOfFinsuppOfEq d hdegree) := rfl

/-- The outer-variable change is obtained by mapping the rational
coefficients of the ordinary block change into the inner polynomial ring. -/
theorem outerBlockLinearChange_monomial {blocks coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ)
    (d : BlockVar blocks coords →₀ ℕ) :
    outerBlockLinearChange T (MvPolynomial.monomial d 1) =
      MvPolynomial.map (MvPolynomial.C : ℚ →+*
        MvPolynomial (BlockVar blocks coords) ℚ)
        (blockLinearChange T (MvPolynomial.monomial d 1)) := by
  simp only [outerBlockLinearChange, MvPolynomial.eval₂AlgHom_apply,
    MvPolynomial.eval₂Hom_monomial, map_one, one_mul,
    blockLinearChange]
  calc
    (d.prod fun i k ↦ outerBlockLinearForm T i ^ k) =
        ∏ i, outerBlockLinearForm T i ^ d i :=
      Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)
    _ = ∏ i, MvPolynomial.map (MvPolynomial.C : ℚ →+*
        MvPolynomial (BlockVar blocks coords) ℚ)
          (blockLinearForm T i ^ d i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [outerBlockLinearForm, blockLinearForm]
    _ = MvPolynomial.map (MvPolynomial.C : ℚ →+*
        MvPolynomial (BlockVar blocks coords) ℚ)
          (∏ i, blockLinearForm T i ^ d i) := by
      rw [map_prod]
    _ = MvPolynomial.map (MvPolynomial.C : ℚ →+*
        MvPolynomial (BlockVar blocks coords) ℚ)
          (d.prod fun i k ↦ blockLinearForm T i ^ k) := by
      rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]

theorem coeff_outerBlockLinearChange_monomial {blocks coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ)
    (a d : BlockVar blocks coords →₀ ℕ) :
    MvPolynomial.coeff a
        (outerBlockLinearChange T (MvPolynomial.monomial d 1)) =
      MvPolynomial.C (MvPolynomial.coeff a
        (blockLinearChange T (MvPolynomial.monomial d 1))) := by
  rw [outerBlockLinearChange_monomial]
  rfl

/-- The all-order Hasse chain rule at a prescribed derivative multidegree.
It is exactly multiplication by the product of the symmetric-power
matrices.  No homogeneity hypothesis on `P` is needed: source Taylor
monomials of the wrong block totals have zero coefficient after the
block-diagonal linear change. -/
theorem hasseDerivative_blockLinearChange_fixed {blocks coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ)
    (degree : Fin blocks → ℕ)
    (new : AuxiliaryPolynomial.MonomialIndex blocks coords degree)
    (P : MvPolynomial (BlockVar blocks coords) ℚ) :
    hasseDerivative (AuxiliaryPolynomial.toFinsupp new)
        (blockLinearChange T P) =
      ∑ old : AuxiliaryPolynomial.MonomialIndex blocks coords degree,
        MvPolynomial.C (multiblockSymmetricPowerMatrix T degree new old) *
          blockLinearChange T
            (hasseDerivative (AuxiliaryPolynomial.toFinsupp old) P) := by
  rw [hasseDerivative_blockLinearChange]
  let S := (taylor P).support
  let Sd := S.filter (fun d ↦ blockDegreeOfFinsupp d = degree)
  let SI := (Finset.univ : Finset
    (AuxiliaryPolynomial.MonomialIndex blocks coords degree)).filter
      (fun old ↦ AuxiliaryPolynomial.toFinsupp old ∈ S)
  have hrestrict :
      (∑ d ∈ S,
        MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp new)
            (outerBlockLinearChange T (MvPolynomial.monomial d 1)) *
          blockLinearChange T (hasseDerivative d P)) =
      ∑ d ∈ Sd,
        MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp new)
            (outerBlockLinearChange T (MvPolynomial.monomial d 1)) *
          blockLinearChange T (hasseDerivative d P) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hdS hdnot
    have hne : blockDegreeOfFinsupp d ≠ degree := by
      simpa [Sd, hdS] using hdnot
    rw [coeff_outerBlockLinearChange_monomial,
      coeff_blockLinearChange_monomial_eq_zero_of_degree_ne T new d hne]
    simp
  rw [hrestrict]
  calc
    (∑ d ∈ Sd,
        MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp new)
            (outerBlockLinearChange T (MvPolynomial.monomial d 1)) *
          blockLinearChange T (hasseDerivative d P)) =
      ∑ old ∈ SI,
        MvPolynomial.C (multiblockSymmetricPowerMatrix T degree new old) *
          blockLinearChange T
            (hasseDerivative (AuxiliaryPolynomial.toFinsupp old) P) := by
      apply Finset.sum_bij
        (fun d hd ↦ monomialIndexOfFinsuppOfEq d
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
        rw [coeff_outerBlockLinearChange_monomial,
          coeff_blockLinearChange_monomial_of_degree_eq T new d
            ((Finset.mem_filter.mp hd).2)]
        rw [toFinsupp_monomialIndexOfFinsuppOfEq]
    _ = ∑ old : AuxiliaryPolynomial.MonomialIndex blocks coords degree,
        MvPolynomial.C (multiblockSymmetricPowerMatrix T degree new old) *
          blockLinearChange T
            (hasseDerivative (AuxiliaryPolynomial.toFinsupp old) P) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro old holduniv holdnot
      have hnotmem : AuxiliaryPolynomial.toFinsupp old ∉ S := by
        simpa [SI] using holdnot
      have hzero : hasseDerivative (AuxiliaryPolynomial.toFinsupp old) P = 0 := by
        rw [hasseDerivative]
        exact MvPolynomial.notMem_support_iff.mp (by simpa [S] using hnotmem)
      rw [hzero, map_zero, mul_zero]

/-- Coefficientwise form of the fixed-multidegree Hasse chain rule.  This is
the form used after fixing a residual monomial in the GLR argument. -/
theorem coeff_hasseDerivative_blockLinearChange_fixed {blocks coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ)
    (degree : Fin blocks → ℕ)
    (new : AuxiliaryPolynomial.MonomialIndex blocks coords degree)
    (P : MvPolynomial (BlockVar blocks coords) ℚ)
    (residual : BlockVar blocks coords →₀ ℕ) :
    MvPolynomial.coeff residual
        (hasseDerivative (AuxiliaryPolynomial.toFinsupp new)
          (blockLinearChange T P)) =
      ∑ old : AuxiliaryPolynomial.MonomialIndex blocks coords degree,
        multiblockSymmetricPowerMatrix T degree new old *
          MvPolynomial.coeff residual
            (blockLinearChange T
              (hasseDerivative (AuxiliaryPolynomial.toFinsupp old) P)) := by
  rw [hasseDerivative_blockLinearChange_fixed]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]

/-- The vector of residual coefficients of all Hasse derivatives with the
fixed block totals `degree`, taken after the coordinate change. -/
def postChangeHasseVector {blocks coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ)
    (degree : Fin blocks → ℕ)
    (P : MvPolynomial (BlockVar blocks coords) ℚ)
    (residual : BlockVar blocks coords →₀ ℕ) :
    AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℚ :=
  fun new ↦ MvPolynomial.coeff residual
    (hasseDerivative (AuxiliaryPolynomial.toFinsupp new)
      (blockLinearChange T P))

/-- The vector of residual coefficients obtained by differentiating first
and then applying the coordinate change. -/
def preChangeHasseVector {blocks coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ)
    (degree : Fin blocks → ℕ)
    (P : MvPolynomial (BlockVar blocks coords) ℚ)
    (residual : BlockVar blocks coords →₀ ℕ) :
    AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℚ :=
  fun old ↦ MvPolynomial.coeff residual
    (blockLinearChange T
      (hasseDerivative (AuxiliaryPolynomial.toFinsupp old) P))

/-- Exact vector identity: the post-change Hasse coefficient vector is the
product symmetric-power matrix applied to the pre-change vector. -/
theorem postChangeHasseVector_eq_mulVec {blocks coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℚ)
    (degree : Fin blocks → ℕ)
    (P : MvPolynomial (BlockVar blocks coords) ℚ)
    (residual : BlockVar blocks coords →₀ ℕ) :
    postChangeHasseVector T degree P residual =
      Matrix.mulVec (multiblockSymmetricPowerMatrix T degree)
        (preChangeHasseVector T degree P residual) := by
  funext new
  rw [Matrix.mulVec_apply]
  exact coeff_hasseDerivative_blockLinearChange_fixed
    T degree new P residual

end

end Erdos407.SymmetricPower
