/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos407.GLRAuxiliary
import ErdosProblems.Erdos407.RestrictionIndex
import ErdosProblems.Erdos407.RestrictionHasse
import ErdosProblems.Erdos407.SmallIntegerNonvanishing
import ErdosProblems.Erdos407.AdelicMinkowski
import ErdosProblems.Erdos407.BlockFamilyLinearChange
import ErdosProblems.Erdos407.SIntegerApproximation
import ErdosProblems.Erdos407.EvertseBasis
import ErdosProblems.Erdos407.HeightBoxes

/-!
# Nonvanishing on an S-integral hyperplane basis

This file contains the algebraic part of GLR Lemma 5.1 used by the
three-place rank-drop argument.  A basis of the kernel of a nonzero rational
linear form, completed by a canonical normal vector, gives a nonsingular
coordinate matrix.  Consequently a nonzero restriction of an auxiliary
polynomial remains nonzero after the basis substitution.  The finite-grid
lemma then supplies bounded integral combinations and a low extra Hasse
order.

The file deliberately does not import `RankDrop`: its public theorem is an
acyclic input to that module.
-/

namespace Erdos407.BasisNonvanishing

open scoped BigOperators Matrix

noncomputable section

open Erdos407.GeneralizedRoth
open Erdos407.BlockFamilyLinearChange
open Erdos407.PadicSubspace

abbrev RatVector (n : ℕ) := Fin n → ℚ

/-- Evaluation of the coefficient vector of a rational linear form. -/
def formValue {n : ℕ} (M x : RatVector n) : ℚ :=
  ∑ k, M k * x k

/-- The canonical vector on which `M` has value one: it is supported at the
canonical pivot of `M`. -/
def normalUnitVector {n : ℕ} (M : RatVector (n + 1)) (hM : M ≠ 0) :
    RatVector (n + 1) :=
  Pi.single (GeneralizedRoth.pivotIndex M hM)
    (M (GeneralizedRoth.pivotIndex M hM))⁻¹

@[simp] theorem formValue_normalUnitVector {n : ℕ}
    (M : RatVector (n + 1)) (hM : M ≠ 0) :
    formValue M (normalUnitVector M hM) = 1 := by
  classical
  rw [formValue, normalUnitVector, Finset.sum_eq_single
    (GeneralizedRoth.pivotIndex M hM)]
  · simp [GeneralizedRoth.pivotIndex_coeff_ne_zero M hM]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp

/-- Complete a kernel basis by the canonical normal unit vector.  The first
`n` columns are the supplied basis and the last column is the normal vector.
Rows are old coordinates and columns are new coordinates, matching the
linear-change convention in `SymmetricPower`. -/
def completedBasisMatrix {n : ℕ} (M : RatVector (n + 1)) (hM : M ≠ 0)
    (x : Fin n → RatVector (n + 1)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  fun k j ↦ Fin.lastCases (normalUnitVector M hM k) (fun i ↦ x i k) j

@[simp] theorem completedBasisMatrix_col_last {n : ℕ}
    (M : RatVector (n + 1)) (hM : M ≠ 0)
    (x : Fin n → RatVector (n + 1)) :
    (completedBasisMatrix M hM x).col (Fin.last n) = normalUnitVector M hM := by
  funext k
  simp [completedBasisMatrix, Matrix.col]

@[simp] theorem completedBasisMatrix_col_castSucc {n : ℕ}
    (M : RatVector (n + 1)) (hM : M ≠ 0)
    (x : Fin n → RatVector (n + 1)) (i : Fin n) :
    (completedBasisMatrix M hM x).col i.castSucc = x i := by
  funext k
  simp [completedBasisMatrix, Matrix.col]

/-- A linearly independent basis of `ker M`, completed by a vector of
`M`-value one, is linearly independent in the ambient space. -/
theorem completedBasisMatrix_cols_linearIndependent {n : ℕ}
    (M : RatVector (n + 1)) (hM : M ≠ 0)
    (x : Fin n → RatVector (n + 1))
    (hxlin : LinearIndependent ℚ x)
    (hxker : ∀ i, formValue M (x i) = 0) :
    LinearIndependent ℚ (completedBasisMatrix M hM x).col := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hform_sum :
      formValue M (∑ i, g i • (completedBasisMatrix M hM x).col i) =
        ∑ i, g i * formValue M ((completedBasisMatrix M hM x).col i) := by
    simp only [formValue, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hlast : g (Fin.last n) = 0 := by
    have hzero :
        (∑ i, g i * formValue M ((completedBasisMatrix M hM x).col i)) = 0 := by
      rw [← hform_sum, hg]
      simp [formValue]
    rw [Fin.sum_univ_castSucc] at hzero
    simpa [hxker] using hzero
  have hbasis_sum : ∑ i : Fin n, g i.castSucc • x i = 0 := by
    rw [Fin.sum_univ_castSucc] at hg
    simpa [hlast] using hg
  have hcoeff : ∀ i : Fin n, g i.castSucc = 0 :=
    (Fintype.linearIndependent_iff.mp hxlin) _ hbasis_sum
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · exact hlast
  · exact hcoeff i

theorem completedBasisMatrix_det_ne_zero {n : ℕ}
    (M : RatVector (n + 1)) (hM : M ≠ 0)
    (x : Fin n → RatVector (n + 1))
    (hxlin : LinearIndependent ℚ x)
    (hxker : ∀ i, formValue M (x i) = 0) :
    (completedBasisMatrix M hM x).det ≠ 0 := by
  have hinj : Function.Injective (completedBasisMatrix M hM x).mulVec :=
    Matrix.mulVec_injective_iff.mpr
      (completedBasisMatrix_cols_linearIndependent M hM x hxlin hxker)
  have hunit : IsUnit (completedBasisMatrix M hM x) :=
    Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det (completedBasisMatrix M hM x)).mp hunit)

/-! ## Finite-grid nonvanishing on an arbitrary finite coordinate type -/

theorem translate_rename_equiv {ι κ : Type*} (e : ι ≃ κ)
    (a : ι → ℚ) (P : MvPolynomial ι ℚ) :
    RothIndex.translate (a ∘ e.symm) (MvPolynomial.rename e P) =
      MvPolynomial.rename e (RothIndex.translate a P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [RothIndex.translate]
  | add P Q hP hQ =>
      rw [map_add, RothIndex.translate_add, RothIndex.translate_add,
        map_add, hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, MvPolynomial.rename_X, RothIndex.translate_mul,
        RothIndex.translate_X, RothIndex.translate_mul,
        RothIndex.translate_X, map_mul, map_add, MvPolynomial.rename_C, hP]
      simp [Function.comp_apply]

theorem hasseCoeff_rename_equiv {ι κ : Type*} (e : ι ≃ κ)
    (P : MvPolynomial ι ℚ) (a : ι → ℚ) (J : ι →₀ ℕ) :
    RothIndex.hasseCoeff (MvPolynomial.rename e P) (a ∘ e.symm)
        (Finsupp.mapDomain e J) =
      RothIndex.hasseCoeff P a J := by
  unfold RothIndex.hasseCoeff
  rw [translate_rename_equiv, MvPolynomial.coeff_rename_mapDomain e e.injective]

theorem translate_rename_injective {ι κ : Type*}
    (f : ι → κ) (hf : Function.Injective f)
    (a : κ → ℚ) (P : MvPolynomial ι ℚ) :
    RothIndex.translate a (MvPolynomial.rename f P) =
      MvPolynomial.rename f (RothIndex.translate (a ∘ f) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [RothIndex.translate]
  | add P Q hP hQ =>
      rw [map_add, RothIndex.translate_add, RothIndex.translate_add,
        map_add, hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, MvPolynomial.rename_X, RothIndex.translate_mul,
        RothIndex.translate_X, RothIndex.translate_mul,
        RothIndex.translate_X, map_mul, map_add, MvPolynomial.rename_C, hP]
      simp [Function.comp_apply]

theorem hasseCoeff_rename_injective {ι κ : Type*}
    (f : ι → κ) (hf : Function.Injective f)
    (P : MvPolynomial ι ℚ) (a : κ → ℚ) (J : ι →₀ ℕ) :
    RothIndex.hasseCoeff (MvPolynomial.rename f P) a
        (Finsupp.mapDomain f J) =
      RothIndex.hasseCoeff P (a ∘ f) J := by
  unfold RothIndex.hasseCoeff
  rw [translate_rename_injective f hf,
    MvPolynomial.coeff_rename_mapDomain f hf]

/-- The finite-grid lemma in a coordinate-free finite-type form. -/
theorem exists_smallInteger_hasseCoeff_ne_zero_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : MvPolynomial ι ℚ) (hP : P ≠ 0) (B : ℕ) :
    ∃ z : ι → ℤ,
      (∀ i, |z i| ≤ (B : ℤ)) ∧
      ∃ I : ι →₀ ℕ,
        (∀ i, I i ≤ MvPolynomial.degreeOf i P / (B + 1)) ∧
        RothIndex.hasseCoeff P (fun i ↦ (z i : ℚ)) I ≠ 0 := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let Q : MvPolynomial (Fin (Fintype.card ι)) ℚ := MvPolynomial.rename e P
  have hQ : Q ≠ 0 := by
    exact (MvPolynomial.rename_injective e e.injective).ne hP
  obtain ⟨z, hz, J, hJ, hnonzero⟩ :=
    SmallIntegerNonvanishing.exists_smallInteger_hasseCoeff_ne_zero Q hQ B
  let z' : ι → ℤ := fun i ↦ z (e i)
  let I : ι →₀ ℕ := Finsupp.mapDomain e.symm J
  have hmap : Finsupp.mapDomain e I = J := by
    ext j
    simp [I]
  refine ⟨z', ?_, I, ?_, ?_⟩
  · intro i
    exact hz (e i)
  · intro i
    have hJi := hJ (e i)
    have hdegree := MvPolynomial.degreeOf_rename_of_injective
      (p := P) e.injective i
    simpa [I, Q, hdegree] using hJi
  · have hrename := hasseCoeff_rename_equiv e P
      (fun i ↦ (z' i : ℚ)) I
    rw [hmap] at hrename
    have hpoints : (fun i ↦ ((z' i : ℤ) : ℚ)) ∘ e.symm =
        fun j ↦ (z j : ℚ) := by
      funext j
      simp [z']
    rw [hpoints] at hrename
    exact fun hzero ↦ hnonzero (by simpa [Q] using hrename.trans hzero)

/-! ## Substitution of a hyperplane basis -/

/-- Embed the `n` basis parameters of every block as the first `n`
coordinates of the completed `(n+1)`-coordinate system. -/
def parameterEmbedding {m n : ℕ} :
    (Fin m × Fin n) → (Fin m × Fin (n + 1)) :=
  fun u ↦ (u.1, u.2.castSucc)

theorem parameterEmbedding_injective {m n : ℕ} :
    Function.Injective (parameterEmbedding :
      (Fin m × Fin n) → (Fin m × Fin (n + 1))) := by
  rintro ⟨h, i⟩ ⟨k, j⟩ heq
  simp only [parameterEmbedding, Prod.mk.injEq, Fin.castSucc_inj] at heq
  exact Prod.ext heq.1 heq.2

/-- Substitute, in every block, a rational family of `n` vectors into an
ambient `(n+1)`-coordinate polynomial. -/
def basisParameterChange {m n : ℕ}
    (x : Fin m → Fin n → RatVector (n + 1))
    (P : MvPolynomial (Fin m × Fin (n + 1)) ℚ) :
    MvPolynomial (Fin m × Fin n) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun u ↦ ∑ j, MvPolynomial.C (x u.1 j u.2) * MvPolynomial.X (u.1, j)) P

def completedBasisMatrixFamily {m n : ℕ}
    (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (x : Fin m → Fin n → RatVector (n + 1)) :
    Fin m → Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  fun h ↦ completedBasisMatrix (M h) (hM h) (x h)

theorem familyBlockLinearForm_completed_eq_rename
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (x : Fin m → Fin n → RatVector (n + 1))
    (u : Fin m × Fin (n + 1))
    (hu : u.2 ≠ GeneralizedRoth.pivotIndex (M u.1) (hM u.1)) :
    familyBlockLinearForm (completedBasisMatrixFamily M hM x) u =
      MvPolynomial.rename parameterEmbedding
        (∑ j, MvPolynomial.C (x u.1 j u.2) * MvPolynomial.X (u.1, j)) := by
  classical
  unfold familyBlockLinearForm completedBasisMatrixFamily
  rw [Fin.sum_univ_castSucc]
  have hnormal : normalUnitVector (M u.1) (hM u.1) u.2 = 0 := by
    simp [normalUnitVector, Pi.single_apply, hu]
  simp only [completedBasisMatrix, Fin.lastCases_castSucc,
    Fin.lastCases_last, hnormal, MvPolynomial.C_0, zero_mul, add_zero,
    map_sum, map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X,
    parameterEmbedding]

/-- On a tangential monomial, substitution by the completed square matrix
is precisely the renamed substitution by the hyperplane basis parameters. -/
theorem familyChange_tangentialMonomial_eq_rename_basisParameter
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (x : Fin m → Fin n → RatVector (n + 1))
    (e : RothIndex.MultiIndex m n) (c : ℚ) :
    familyBlockLinearChange (completedBasisMatrixFamily M hM x)
        (MvPolynomial.monomial
          (RestrictionIndex.tangentialExponent M hM e) c) =
      MvPolynomial.rename parameterEmbedding
        (basisParameterChange x
          (MvPolynomial.monomial
            (RestrictionIndex.tangentialExponent M hM e) c)) := by
  classical
  simp only [familyBlockLinearChange, MvPolynomial.eval₂AlgHom_apply,
    MvPolynomial.eval₂Hom_monomial, basisParameterChange]
  simp only [map_mul, MvPolynomial.rename_C]
  congr 1
  simp only [Finsupp.prod]
  rw [map_prod]
  simp only [map_pow]
  apply Finset.prod_congr rfl
  intro u hu
  have hnonpivot :
      u.2 ≠ GeneralizedRoth.pivotIndex (M u.1) (hM u.1) := by
    rcases u with ⟨h, k⟩
    intro hpivot
    change k = GeneralizedRoth.pivotIndex (M h) (hM h) at hpivot
    subst k
    have hzero := RestrictionIndex.tangentialExponent_pivot M hM e h
    exact (Finsupp.mem_support_iff.mp hu) hzero
  rw [familyBlockLinearForm_completed_eq_rename M hM x u hnonpivot]

/-- The restricted derivative after substituting the chosen hyperplane
bases.  Its variables are the basis coefficients in every block. -/
def restrictedBasisPolynomial {m n : ℕ}
    (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (x : Fin m → Fin n → RatVector (n + 1))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (I : RestrictionIndex.NormalOrder m) :
    MvPolynomial (Fin m × Fin n) ℚ :=
  basisParameterChange x (RestrictionIndex.restrictedDividedDerivative M hM P I)

theorem familyChange_restrictedDividedDerivative_eq_rename
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (x : Fin m → Fin n → RatVector (n + 1))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (I : RestrictionIndex.NormalOrder m) :
    familyBlockLinearChange (completedBasisMatrixFamily M hM x)
        (RestrictionIndex.restrictedDividedDerivative M hM P I) =
      MvPolynomial.rename parameterEmbedding
        (restrictedBasisPolynomial M hM x P I) := by
  classical
  unfold restrictedBasisPolynomial
  unfold RestrictionIndex.restrictedDividedDerivative
    RestrictionIndex.restrictedDividedDerivativeInAdaptedCoordinates
  unfold basisParameterChange
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro e he
  exact familyChange_tangentialMonomial_eq_rename_basisParameter M hM x e _

theorem restrictedBasisPolynomial_ne_zero
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (x : Fin m → Fin n → RatVector (n + 1))
    (hxlin : ∀ h, LinearIndependent ℚ (x h))
    (hxker : ∀ h i, formValue (M h) (x h i) = 0)
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (I : RestrictionIndex.NormalOrder m)
    (hI : RestrictionIndex.restrictedDividedDerivative M hM P I ≠ 0) :
    restrictedBasisPolynomial M hM x P I ≠ 0 := by
  have hdet : ∀ h, (completedBasisMatrixFamily M hM x h).det ≠ 0 :=
    fun h ↦ completedBasisMatrix_det_ne_zero (M h) (hM h) (x h)
      (hxlin h) (hxker h)
  have hfull := familyBlockLinearChange_ne_zero
    (completedBasisMatrixFamily M hM x) hdet hI
  rw [familyChange_restrictedDividedDerivative_eq_rename] at hfull
  exact fun hz ↦ hfull (by rw [hz]; simp)

/-! ## The adapted square substitution and parameter derivative order -/

/-- In form-adapted coordinates, the supplied kernel basis has zero pivot
coordinate.  The final column is the adapted normal coordinate. -/
def adaptedBasisMatrix {m n : ℕ}
    (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (x : Fin m → Fin n → RatVector (n + 1)) :
    Fin m → Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  fun h k j ↦
    if k = GeneralizedRoth.pivotIndex (M h) (hM h) then
      if j = Fin.last n then 1 else 0
    else
      Fin.lastCases 0 (fun i ↦ x h i k) j

/-- Matrix of the canonical triangular change from form-adapted coordinates
back to the original homogeneous coordinates. -/
def toFormCoordinateMatrix {m n : ℕ}
    (M : FormFamily m n) (hM : ∀ h, M h ≠ 0) :
    Fin m → Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  fun h old new ↦
    if hold : old = GeneralizedRoth.pivotIndex (M h) (hM h) then
      (M h old)⁻¹ *
        (if new = GeneralizedRoth.pivotIndex (M h) (hM h) then 1
          else -M h new)
    else if new = old then 1 else 0

theorem familyBlockLinearForm_toFormCoordinateMatrix {m n : ℕ}
    (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (u : RothIndex.BlockVar m n) :
    familyBlockLinearForm (toFormCoordinateMatrix M hM) u =
      GeneralizedRoth.toFormCoordinateVar M hM u := by
  classical
  rcases u with ⟨h, old⟩
  by_cases hold : old = GeneralizedRoth.pivotIndex (M h) (hM h)
  · subst old
    unfold familyBlockLinearForm toFormCoordinateMatrix
      GeneralizedRoth.toFormCoordinateVar GeneralizedRoth.offPivotPolynomial
    rw [dif_pos rfl]
    simp only [Prod.fst, Prod.snd, dif_pos rfl]
    simp only [dif_pos trivial]
    rw [← Finset.add_sum_erase Finset.univ
      (fun new : Fin (n + 1) ↦
        MvPolynomial.C
            ((M h (GeneralizedRoth.pivotIndex (M h) (hM h)))⁻¹ *
              (if new = GeneralizedRoth.pivotIndex (M h) (hM h) then 1
                else -M h new)) *
          MvPolynomial.X (h, new))
      (Finset.mem_univ (GeneralizedRoth.pivotIndex (M h) (hM h)))]
    simp only [if_pos, map_one, mul_one]
    have hoff :
        (∑ x ∈ Finset.univ.erase
              (GeneralizedRoth.pivotIndex (M h) (hM h)),
            MvPolynomial.C
                (M h (GeneralizedRoth.pivotIndex (M h) (hM h)))⁻¹ *
              MvPolynomial.C
                (if x = GeneralizedRoth.pivotIndex (M h) (hM h) then 1
                  else -M h x) *
              MvPolynomial.X (h, x)) =
          -MvPolynomial.C
              (M h (GeneralizedRoth.pivotIndex (M h) (hM h)))⁻¹ *
            (∑ x ∈ Finset.univ.erase
                (GeneralizedRoth.pivotIndex (M h) (hM h)),
              MvPolynomial.C (M h x) * MvPolynomial.X (h, x)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [if_neg (Finset.mem_erase.mp hx).1]
      simp only [map_neg]
      ring
    simp_rw [MvPolynomial.C_mul]
    rw [hoff]
    ring
  · unfold familyBlockLinearForm toFormCoordinateMatrix
      GeneralizedRoth.toFormCoordinateVar
    rw [dif_neg hold]
    rw [Finset.sum_eq_single old]
    · simp [hold]
    · intro new hnew hne
      simp [hold, hne]
    · simp

theorem familyBlockLinearChange_toFormCoordinateMatrix {m n : ℕ}
    (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) :
    familyBlockLinearChange (toFormCoordinateMatrix M hM) P =
      GeneralizedRoth.toFormCoordinates M hM P := by
  unfold familyBlockLinearChange GeneralizedRoth.toFormCoordinates
  apply congrArg (fun f : RothIndex.BlockVar m n →
      MvPolynomial (RothIndex.BlockVar m n) ℚ ↦
    MvPolynomial.eval₂Hom MvPolynomial.C f P)
  funext u
  exact familyBlockLinearForm_toFormCoordinateMatrix M hM u

/-- A block-dependent linear change preserves exact multihomogeneity. -/
theorem familyBlockLinearChange_isMultiHomogeneous {m n : ℕ}
    (T : Fin m → Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ}
    {d : Fin m → ℕ} (hP : RothIndex.IsMultiHomogeneous P d) :
    RothIndex.IsMultiHomogeneous (familyBlockLinearChange T P) d := by
  classical
  intro J hJ h
  by_contra hdegree
  apply hJ
  rw [MvPolynomial.as_sum P]
  simp only [map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro e he
  have hedegree : SymmetricPower.blockDegreeOfFinsupp e = d := by
    funext b
    exact hP (MvPolynomial.mem_support_iff.mp he) b
  let old := SymmetricPower.monomialIndexOfFinsuppOfEq e hedegree
  have hold : AuxiliaryPolynomial.toFinsupp old = e := by simp [old]
  rw [show MvPolynomial.monomial e (MvPolynomial.coeff e P) =
      MvPolynomial.C (MvPolynomial.coeff e P) *
        MvPolynomial.monomial e 1 by
        rw [MvPolynomial.C_mul_monomial, mul_one], map_mul]
  rw [← hold, familyBlockLinearChange_monomial_eq_ofCoefficients]
  simp only [familyBlockLinearChange, MvPolynomial.eval₂AlgHom_apply,
    MvPolynomial.eval₂Hom_C]
  change MvPolynomial.coeff J
    (MvPolynomial.C (MvPolynomial.coeff
        (AuxiliaryPolynomial.toFinsupp old) P) *
      AuxiliaryPolynomial.ofCoefficients
        (fun new : AuxiliaryPolynomial.MonomialIndex m (n + 1) d ↦
          familyMultiblockSymmetricPowerMatrix T d new old)) = 0
  rw [MvPolynomial.coeff_C_mul]
  have hnot : J ∉
      (AuxiliaryPolynomial.ofCoefficients
        (fun new : AuxiliaryPolynomial.MonomialIndex m (n + 1) d ↦
          familyMultiblockSymmetricPowerMatrix T d new old)).support := by
    intro hmem
    apply hdegree
    exact AuxiliaryPolynomial.blockDegree_of_mem_support _ hmem h
  rw [MvPolynomial.notMem_support_iff.mp hnot, mul_zero]

theorem toFormCoordinates_isMultiHomogeneous {m n : ℕ}
    (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ}
    {d : Fin m → ℕ} (hP : RothIndex.IsMultiHomogeneous P d) :
    RothIndex.IsMultiHomogeneous
      (GeneralizedRoth.toFormCoordinates M hM P) d := by
  rw [← familyBlockLinearChange_toFormCoordinateMatrix M hM P]
  exact familyBlockLinearChange_isMultiHomogeneous
    (toFormCoordinateMatrix M hM) hP

theorem blockOrder_tangentialExponent_add_normalOrderOfExponent
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (e : RothIndex.MultiIndex m n) (h : Fin m) :
    RothIndex.blockOrder (RestrictionIndex.tangentialExponent M hM e) h +
        RestrictionIndex.normalOrderOfExponent M hM e h =
      RothIndex.blockOrder e h := by
  classical
  let p := GeneralizedRoth.pivotIndex (M h) (hM h)
  unfold RothIndex.blockOrder RestrictionIndex.normalOrderOfExponent
  rw [← Finset.add_sum_erase Finset.univ
    (fun j : Fin (n + 1) ↦
      RestrictionIndex.tangentialExponent M hM e (h, j))
    (Finset.mem_univ p)]
  rw [← Finset.add_sum_erase Finset.univ
    (fun j : Fin (n + 1) ↦ e (h, j)) (Finset.mem_univ p)]
  have hp : p = GeneralizedRoth.pivotIndex (M h) (hM h) := rfl
  simp only [RestrictionIndex.tangentialExponent_apply, hp, ne_eq,
    not_true_eq_false, if_false, zero_add]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjp : j ≠ p := (Finset.mem_erase.mp hj).1
  simp [RestrictionIndex.tangentialExponent, hjp, p]

theorem restrictedDividedDerivativeInAdaptedCoordinates_isMultiHomogeneous
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    {Q : MvPolynomial (RothIndex.BlockVar m n) ℚ}
    {d : Fin m → ℕ} (hQ : RothIndex.IsMultiHomogeneous Q d)
    (N : RestrictionIndex.NormalOrder m) :
    RothIndex.IsMultiHomogeneous
      (RestrictionIndex.restrictedDividedDerivativeInAdaptedCoordinates
        M hM Q N) (fun h ↦ d h - N h) := by
  classical
  intro K hK h
  have hex : ∃ e ∈ Q.support.filter
      (fun e ↦ RestrictionIndex.normalOrderOfExponent M hM e = N),
      MvPolynomial.coeff K
        (MvPolynomial.monomial
          (RestrictionIndex.tangentialExponent M hM e)
          (MvPolynomial.coeff e Q)) ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hK
    unfold RestrictionIndex.restrictedDividedDerivativeInAdaptedCoordinates
    simp only [MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro e he
    exact hnone e he
  obtain ⟨e, he, hcoeff⟩ := hex
  have hKe : K = RestrictionIndex.tangentialExponent M hM e := by
    by_contra hne
    rw [MvPolynomial.coeff_monomial, if_neg (Ne.symm hne)] at hcoeff
    exact hcoeff rfl
  subst K
  have henormal := (Finset.mem_filter.mp he).2
  have heQ := (Finset.mem_filter.mp he).1
  have htotal :
      RothIndex.blockOrder
          (RestrictionIndex.tangentialExponent M hM e) h + N h = d h := by
    simpa [congrFun henormal h, hQ.of_mem_support heQ h] using
      (blockOrder_tangentialExponent_add_normalOrderOfExponent
        M hM e h)
  exact Nat.eq_sub_of_add_eq htotal

theorem restrictedDividedDerivative_isMultiHomogeneous
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ}
    {d : Fin m → ℕ} (hP : RothIndex.IsMultiHomogeneous P d)
    (N : RestrictionIndex.NormalOrder m) :
    RothIndex.IsMultiHomogeneous
      (RestrictionIndex.restrictedDividedDerivative M hM P N)
      (fun h ↦ d h - N h) := by
  exact restrictedDividedDerivativeInAdaptedCoordinates_isMultiHomogeneous
    M hM (toFormCoordinates_isMultiHomogeneous M hM hP) N

theorem familyBlockLinearForm_adapted_pivot {m n : ℕ}
    (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (x : Fin m → Fin n → RatVector (n + 1)) (h : Fin m) :
    familyBlockLinearForm (adaptedBasisMatrix M hM x)
        (h, GeneralizedRoth.pivotIndex (M h) (hM h)) =
      MvPolynomial.X (h, Fin.last n) := by
  classical
  unfold familyBlockLinearForm adaptedBasisMatrix
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp
  · intro j hj hne
    simp [hne]
  · simp

theorem familyBlockLinearForm_adapted_nonpivot {m n : ℕ}
    (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (x : Fin m → Fin n → RatVector (n + 1))
    (u : Fin m × Fin (n + 1))
    (hu : u.2 ≠ GeneralizedRoth.pivotIndex (M u.1) (hM u.1)) :
    familyBlockLinearForm (adaptedBasisMatrix M hM x) u =
      MvPolynomial.rename parameterEmbedding
        (∑ j, MvPolynomial.C (x u.1 j u.2) * MvPolynomial.X (u.1, j)) := by
  classical
  unfold familyBlockLinearForm adaptedBasisMatrix
  rw [Fin.sum_univ_castSucc]
  simp only [hu, if_false, Fin.lastCases_castSucc, Fin.lastCases_last,
    MvPolynomial.C_0, zero_mul, add_zero, map_sum, map_mul,
    MvPolynomial.rename_C, MvPolynomial.rename_X, parameterEmbedding]

theorem familyChange_adapted_tangentialMonomial_eq_rename
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (x : Fin m → Fin n → RatVector (n + 1))
    (e : RothIndex.MultiIndex m n) (c : ℚ) :
    familyBlockLinearChange (adaptedBasisMatrix M hM x)
        (MvPolynomial.monomial
          (RestrictionIndex.tangentialExponent M hM e) c) =
      MvPolynomial.rename parameterEmbedding
        (basisParameterChange x
          (MvPolynomial.monomial
            (RestrictionIndex.tangentialExponent M hM e) c)) := by
  classical
  simp only [familyBlockLinearChange, MvPolynomial.eval₂AlgHom_apply,
    MvPolynomial.eval₂Hom_monomial, basisParameterChange]
  simp only [map_mul, MvPolynomial.rename_C]
  congr 1
  simp only [Finsupp.prod]
  rw [map_prod]
  simp only [map_pow]
  apply Finset.prod_congr rfl
  intro u hu
  have hnonpivot :
      u.2 ≠ GeneralizedRoth.pivotIndex (M u.1) (hM u.1) := by
    intro hpivot
    have hzero : RestrictionIndex.tangentialExponent M hM e u = 0 := by
      simp [RestrictionIndex.tangentialExponent, hpivot]
    exact (Finsupp.mem_support_iff.mp hu) hzero
  rw [familyBlockLinearForm_adapted_nonpivot M hM x u hnonpivot]

theorem familyChange_adapted_restrictedDividedDerivative_eq_rename
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (x : Fin m → Fin n → RatVector (n + 1))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (I : RestrictionIndex.NormalOrder m) :
    familyBlockLinearChange (adaptedBasisMatrix M hM x)
        (RestrictionIndex.restrictedDividedDerivative M hM P I) =
      MvPolynomial.rename parameterEmbedding
        (restrictedBasisPolynomial M hM x P I) := by
  classical
  unfold restrictedBasisPolynomial
  unfold RestrictionIndex.restrictedDividedDerivative
    RestrictionIndex.restrictedDividedDerivativeInAdaptedCoordinates
  unfold basisParameterChange
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro e he
  exact familyChange_adapted_tangentialMonomial_eq_rename M hM x e _

/-- Extend a parameter point by a zero final (normal) coordinate. -/
def fullGridPoint {m n : ℕ} (z : Fin m × Fin n → ℤ) :
    RothIndex.BlockVar m n → ℚ :=
  fun u ↦ Fin.lastCases 0 (fun j ↦ (z (u.1, j) : ℚ)) u.2

/-- Regard a parameter Hasse order as an ambient order supported away from
the final normal coordinate. -/
def embeddedParameterOrder {m n : ℕ} (J : Fin m × Fin n →₀ ℕ) :
    RothIndex.BlockVar m n →₀ ℕ :=
  Finsupp.mapDomain parameterEmbedding J

@[simp] theorem embeddedParameterOrder_apply_castSucc {m n : ℕ}
    (J : Fin m × Fin n →₀ ℕ) (h : Fin m) (j : Fin n) :
    embeddedParameterOrder J (h, j.castSucc) = J (h, j) := by
  change (Finsupp.mapDomain parameterEmbedding J)
    (parameterEmbedding (h, j)) = J (h, j)
  exact Finsupp.mapDomain_apply parameterEmbedding_injective J (h, j)

@[simp] theorem embeddedParameterOrder_apply_last {m n : ℕ}
    (J : Fin m × Fin n →₀ ℕ) (h : Fin m) :
    embeddedParameterOrder J (h, Fin.last n) = 0 := by
  unfold embeddedParameterOrder
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨u, hu⟩
  have hsnd := congrArg Prod.snd hu
  exact Fin.castSucc_ne_last u.2 hsnd

theorem blockOrder_embeddedParameterOrder {m n : ℕ}
    (J : Fin m × Fin n →₀ ℕ) (h : Fin m) :
    RothIndex.blockOrder (embeddedParameterOrder J) h =
      ∑ j, J (h, j) := by
  unfold RothIndex.blockOrder
  rw [Fin.sum_univ_castSucc]
  simp only [embeddedParameterOrder_apply_castSucc,
    embeddedParameterOrder_apply_last, add_zero]

/-- The exact block totals of an embedded parameter derivative. -/
def parameterDerivativeDegree {m n : ℕ} (J : Fin m × Fin n →₀ ℕ) :
    Fin m → ℕ :=
  SymmetricPower.blockDegreeOfFinsupp (embeddedParameterOrder J)

theorem parameterDerivativeDegree_eq_sum {m n : ℕ}
    (J : Fin m × Fin n →₀ ℕ) (h : Fin m) :
    parameterDerivativeDegree J h = ∑ j, J (h, j) := by
  exact blockOrder_embeddedParameterOrder J h

/-- The embedded order packaged as the exact monomial index required by the
fixed-multidegree family chain rule. -/
def parameterDerivativeIndex {m n : ℕ} (J : Fin m × Fin n →₀ ℕ) :
    AuxiliaryPolynomial.MonomialIndex m (n + 1) (parameterDerivativeDegree J) :=
  SymmetricPower.monomialIndexOfFinsupp (embeddedParameterOrder J)

@[simp] theorem toFinsupp_parameterDerivativeIndex {m n : ℕ}
    (J : Fin m × Fin n →₀ ℕ) :
    AuxiliaryPolynomial.toFinsupp (parameterDerivativeIndex J) =
      embeddedParameterOrder J := by
  unfold parameterDerivativeIndex
  exact SymmetricPower.toFinsupp_monomialIndexOfFinsupp
    (embeddedParameterOrder J)

theorem fullGridPoint_comp_parameterEmbedding {m n : ℕ}
    (z : Fin m × Fin n → ℤ) :
    fullGridPoint z ∘ parameterEmbedding = fun u ↦ (z u : ℚ) := by
  funext u
  rcases u with ⟨h, j⟩
  simp [fullGridPoint, parameterEmbedding]

/-- The point in the old coordinates obtained by applying a family of
linear substitutions to a point in the new coordinates. -/
def familyMatrixPoint {m n : ℕ}
    (T : Fin m → Matrix (Fin n) (Fin n) ℚ)
    (z : Fin m × Fin n → ℚ) : Fin m × Fin n → ℚ :=
  fun u ↦ ∑ j, T u.1 u.2 j * z (u.1, j)

theorem eval_familyBlockLinearChange {m n : ℕ}
    (T : Fin m → Matrix (Fin n) (Fin n) ℚ)
    (P : MvPolynomial (Fin m × Fin n) ℚ)
    (z : Fin m × Fin n → ℚ) :
    MvPolynomial.eval z (familyBlockLinearChange T P) =
      MvPolynomial.eval (familyMatrixPoint T z) P := by
  unfold familyBlockLinearChange
  change MvPolynomial.eval z
      (MvPolynomial.eval₂ MvPolynomial.C (familyBlockLinearForm T) P) = _
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun a : Fin m × Fin n → ℚ ↦ MvPolynomial.eval a P)
  funext u
  simp [familyBlockLinearForm, familyMatrixPoint, Function.comp_apply]

/-- The adapted coordinates of the integer combination of the kernel
basis: the pivot coordinate is zero and every other coordinate is the
corresponding ordinary coordinate of the combination. -/
def adaptedGridImage {m n : ℕ}
    (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (x : Fin m → Fin n → RatVector (n + 1))
    (z : Fin m × Fin n → ℤ) : RothIndex.BlockVar m n → ℚ :=
  fun u ↦
    if u.2 = GeneralizedRoth.pivotIndex (M u.1) (hM u.1) then 0
    else ∑ j, (z (u.1, j) : ℚ) * x u.1 j u.2

theorem familyMatrixPoint_adaptedBasisMatrix_fullGridPoint {m n : ℕ}
    (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (x : Fin m → Fin n → RatVector (n + 1))
    (z : Fin m × Fin n → ℤ) :
    familyMatrixPoint (adaptedBasisMatrix M hM x) (fullGridPoint z) =
      adaptedGridImage M hM x z := by
  funext u
  rcases u with ⟨h, k⟩
  by_cases hk : k = GeneralizedRoth.pivotIndex (M h) (hM h)
  · subst k
    simp [familyMatrixPoint, adaptedBasisMatrix, fullGridPoint,
      adaptedGridImage]
  · rw [familyMatrixPoint, adaptedGridImage]
    simp only [hk, if_false]
    rw [Fin.sum_univ_castSucc]
    simp only [adaptedBasisMatrix, hk, if_false, Fin.lastCases_castSucc,
      Fin.lastCases_last, fullGridPoint, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    ring

/-- Hasse coefficients are evaluations of the corresponding universal
Hasse derivative. -/
theorem hasseCoeff_eq_eval_hasseDerivative {ι : Type*} [Fintype ι]
    (P : MvPolynomial ι ℚ) (a : ι → ℚ) (I : ι →₀ ℕ) :
    RothIndex.hasseCoeff P a I =
      MvPolynomial.eval a (SymmetricPower.hasseDerivative I P) := by
  let f : MvPolynomial ι ℚ →+* ℚ :=
    MvPolynomial.eval₂Hom (RingHom.id ℚ) a
  have hmap : MvPolynomial.map f (SymmetricPower.taylor P) =
      RothIndex.translate a P := by
    change ((MvPolynomial.map f).comp SymmetricPower.taylor.toRingHom) P =
      (MvPolynomial.eval₂Hom MvPolynomial.C
        (fun i ↦ MvPolynomial.X i + MvPolynomial.C (a i))) P
    congr 1
    ext r i
    · simp [f]
    · simp [f, SymmetricPower.taylor, add_comm]
  unfold RothIndex.hasseCoeff SymmetricPower.hasseDerivative
  rw [← hmap, MvPolynomial.coeff_map]
  rfl

theorem hasseDerivative_restricted_eq_zero_of_pivot_ne_zero
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (Q : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (N : RestrictionIndex.NormalOrder m)
    (A : RothIndex.BlockVar m n →₀ ℕ) (h : Fin m)
    (hA : A (h, GeneralizedRoth.pivotIndex (M h) (hM h)) ≠ 0) :
    SymmetricPower.hasseDerivative A
        (RestrictionIndex.restrictedDividedDerivativeInAdaptedCoordinates
          M hM Q N) = 0 := by
  classical
  unfold RestrictionIndex.restrictedDividedDerivativeInAdaptedCoordinates
  unfold SymmetricPower.hasseDerivative
  simp only [map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro e he
  change SymmetricPower.hasseDerivative A
    (MvPolynomial.monomial
      (RestrictionIndex.tangentialExponent M hM e)
      (MvPolynomial.coeff e Q)) = 0
  rw [SymmetricPower.hasseDerivative_monomial]
  have hprod : (∏ u, (Nat.choose
      (RestrictionIndex.tangentialExponent M hM e u) (A u) : ℚ)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ
      (h, GeneralizedRoth.pivotIndex (M h) (hM h)))
    rw [RestrictionIndex.tangentialExponent_pivot]
    exact_mod_cast Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hA)
  rw [hprod, mul_zero, MvPolynomial.monomial_zero]

/-- A nonzero parameter Hasse coefficient of the restricted basis
polynomial yields a tangential derivative, of the same block totals, which
is nonzero at the associated zero-normal adapted point. -/
theorem exists_tangentialDerivative_eval_ne_zero
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (x : Fin m → Fin n → RatVector (n + 1))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (N : RestrictionIndex.NormalOrder m)
    (z : Fin m × Fin n → ℤ) (J : Fin m × Fin n →₀ ℕ)
    (hJ : RothIndex.hasseCoeff
      (restrictedBasisPolynomial M hM x P N)
      (fun u ↦ (z u : ℚ)) J ≠ 0) :
    ∃ A : AuxiliaryPolynomial.MonomialIndex m (n + 1)
        (parameterDerivativeDegree J),
      (∀ h, AuxiliaryPolynomial.toFinsupp A
          (h, GeneralizedRoth.pivotIndex (M h) (hM h)) = 0) ∧
      MvPolynomial.eval (adaptedGridImage M hM x z)
        (SymmetricPower.hasseDerivative
          (AuxiliaryPolynomial.toFinsupp A)
          (RestrictionIndex.restrictedDividedDerivative M hM P N)) ≠ 0 := by
  let D := RestrictionIndex.restrictedDividedDerivative M hM P N
  have htrans : MvPolynomial.eval (fullGridPoint z)
      (SymmetricPower.hasseDerivative
        (AuxiliaryPolynomial.toFinsupp (parameterDerivativeIndex J))
        (familyBlockLinearChange (adaptedBasisMatrix M hM x) D)) ≠ 0 := by
    rw [toFinsupp_parameterDerivativeIndex]
    rw [familyChange_adapted_restrictedDividedDerivative_eq_rename]
    rw [← hasseCoeff_eq_eval_hasseDerivative]
    change RothIndex.hasseCoeff
      (MvPolynomial.rename parameterEmbedding
        (restrictedBasisPolynomial M hM x P N))
      (fullGridPoint z) (Finsupp.mapDomain parameterEmbedding J) ≠ 0
    rw [hasseCoeff_rename_injective parameterEmbedding
      parameterEmbedding_injective]
    rw [fullGridPoint_comp_parameterEmbedding]
    exact hJ
  obtain ⟨A, hAeval⟩ :=
    exists_eval_familyBlockLinearChange_hasseDerivative_ne_zero
      (adaptedBasisMatrix M hM x) (parameterDerivativeDegree J)
      (parameterDerivativeIndex J) D (fullGridPoint z) htrans
  refine ⟨A, ?_, ?_⟩
  · intro h
    by_contra hne
    have hz := hasseDerivative_restricted_eq_zero_of_pivot_ne_zero
      M hM (GeneralizedRoth.toFormCoordinates M hM P) N
      (AuxiliaryPolynomial.toFinsupp A) h hne
    apply hAeval
    rw [show D = RestrictionIndex.restrictedDividedDerivativeInAdaptedCoordinates
        M hM (GeneralizedRoth.toFormCoordinates M hM P) N by rfl]
    rw [hz, map_zero]
    simp
  · rw [← familyMatrixPoint_adaptedBasisMatrix_fullGridPoint M hM x z]
    rw [← eval_familyBlockLinearChange]
    exact hAeval

/-- Add the extracted normal order to a tangential ambient order. -/
def combinedAdaptedOrder {m n : ℕ}
    (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (N : RestrictionIndex.NormalOrder m)
    (A : RothIndex.BlockVar m n →₀ ℕ) :
    RothIndex.BlockVar m n →₀ ℕ :=
  A + RestrictionIndex.normalMultiIndex M hM N

theorem blockDegreeOfFinsupp_combinedAdaptedOrder
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (N : RestrictionIndex.NormalOrder m)
    (A : RothIndex.BlockVar m n →₀ ℕ) (h : Fin m) :
    SymmetricPower.blockDegreeOfFinsupp
        (combinedAdaptedOrder M hM N A) h =
      SymmetricPower.blockDegreeOfFinsupp A h + N h := by
  classical
  unfold SymmetricPower.blockDegreeOfFinsupp combinedAdaptedOrder
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  change _ + RothIndex.blockOrder
      (RestrictionIndex.normalMultiIndex M hM N) h = _
  rw [RestrictionIndex.blockOrder_normalMultiIndex]

/-- The full adapted derivative order, packaged for the fixed-degree family
chain rule. -/
def combinedAdaptedDerivativeIndex {m n : ℕ}
    (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (N : RestrictionIndex.NormalOrder m)
    (A : RothIndex.BlockVar m n →₀ ℕ) :
    AuxiliaryPolynomial.MonomialIndex m (n + 1)
      (SymmetricPower.blockDegreeOfFinsupp
        (combinedAdaptedOrder M hM N A)) :=
  SymmetricPower.monomialIndexOfFinsupp
    (combinedAdaptedOrder M hM N A)

@[simp] theorem toFinsupp_combinedAdaptedDerivativeIndex
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (N : RestrictionIndex.NormalOrder m)
    (A : RothIndex.BlockVar m n →₀ ℕ) :
    AuxiliaryPolynomial.toFinsupp
        (combinedAdaptedDerivativeIndex M hM N A) =
      combinedAdaptedOrder M hM N A := by
  exact SymmetricPower.toFinsupp_monomialIndexOfFinsupp _

/-- Pull the nonzero restricted/grid derivative all the way back through
the canonical form-coordinate change.  The returned order is an order of
the original polynomial, and its block totals are exactly the normal totals
plus the extra finite-grid totals. -/
theorem exists_originalDerivative_eval_matrixPoint_ne_zero
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (x : Fin m → Fin n → RatVector (n + 1))
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (N : RestrictionIndex.NormalOrder m)
    (z : Fin m × Fin n → ℤ) (J : Fin m × Fin n →₀ ℕ)
    (hJ : RothIndex.hasseCoeff
      (restrictedBasisPolynomial M hM x P N)
      (fun u ↦ (z u : ℚ)) J ≠ 0) :
    ∃ A : AuxiliaryPolynomial.MonomialIndex m (n + 1)
        (fun h ↦ parameterDerivativeDegree J h + N h),
      MvPolynomial.eval
        (familyMatrixPoint (toFormCoordinateMatrix M hM)
          (adaptedGridImage M hM x z))
        (SymmetricPower.hasseDerivative
          (AuxiliaryPolynomial.toFinsupp A) P) ≠ 0 := by
  obtain ⟨Atan, hAtanPivot, hAtanEval⟩ :=
    exists_tangentialDerivative_eval_ne_zero M hM x P N z J hJ
  let Q := GeneralizedRoth.toFormCoordinates M hM P
  have hadaptZero : ∀ h,
      adaptedGridImage M hM x z
        (h, GeneralizedRoth.pivotIndex (M h) (hM h)) = 0 := by
    intro h
    simp [adaptedGridImage]
  have hcombined : MvPolynomial.eval (adaptedGridImage M hM x z)
      (SymmetricPower.hasseDerivative
        (combinedAdaptedOrder M hM N (AuxiliaryPolynomial.toFinsupp Atan))
        Q) ≠ 0 := by
    unfold combinedAdaptedOrder
    rw [← RestrictionHasse.eval_hasseDerivative_restrictedDividedDerivativeInAdaptedCoordinates
      M hM Q N (AuxiliaryPolynomial.toFinsupp Atan) hAtanPivot
      (adaptedGridImage M hM x z) hadaptZero]
    exact hAtanEval
  have htrans : MvPolynomial.eval (adaptedGridImage M hM x z)
      (SymmetricPower.hasseDerivative
        (AuxiliaryPolynomial.toFinsupp
          (combinedAdaptedDerivativeIndex M hM N
            (AuxiliaryPolynomial.toFinsupp Atan)))
        (familyBlockLinearChange (toFormCoordinateMatrix M hM) P)) ≠ 0 := by
    rw [toFinsupp_combinedAdaptedDerivativeIndex,
      familyBlockLinearChange_toFormCoordinateMatrix]
    exact hcombined
  obtain ⟨Aold, hAold⟩ :=
    exists_eval_familyBlockLinearChange_hasseDerivative_ne_zero
      (toFormCoordinateMatrix M hM)
      (SymmetricPower.blockDegreeOfFinsupp
        (combinedAdaptedOrder M hM N
          (AuxiliaryPolynomial.toFinsupp Atan)))
      (combinedAdaptedDerivativeIndex M hM N
        (AuxiliaryPolynomial.toFinsupp Atan)) P
      (adaptedGridImage M hM x z) htrans
  let eDegree :
      (SymmetricPower.blockDegreeOfFinsupp
        (combinedAdaptedOrder M hM N
          (AuxiliaryPolynomial.toFinsupp Atan))) =
        (fun h ↦ parameterDerivativeDegree J h + N h) := by
    funext h
    rw [blockDegreeOfFinsupp_combinedAdaptedOrder]
    change SymmetricPower.blockDegreeOfFinsupp
      (AuxiliaryPolynomial.toFinsupp Atan) h + N h = _
    rw [← (Atan h).2]
    rfl
  let A : AuxiliaryPolynomial.MonomialIndex m (n + 1)
      (fun h ↦ parameterDerivativeDegree J h + N h) :=
    fun h ↦
      ⟨fun j ↦ ⟨AuxiliaryPolynomial.exponent Aold (h, j),
          Nat.lt_succ_of_le <| by
            calc
              AuxiliaryPolynomial.exponent Aold (h, j) ≤
                  ∑ k, AuxiliaryPolynomial.exponent Aold (h, k) :=
                Finset.single_le_sum
                  (fun k _ ↦ Nat.zero_le
                    (AuxiliaryPolynomial.exponent Aold (h, k)))
                  (Finset.mem_univ j)
              _ = parameterDerivativeDegree J h + N h := by
                rw [AuxiliaryPolynomial.sum_exponent_block Aold h,
                  congrFun eDegree h]⟩,
        by
          simp only [Fin.val_mk]
          rw [AuxiliaryPolynomial.sum_exponent_block Aold h,
            congrFun eDegree h]⟩
  refine ⟨A, ?_⟩
  have hfs : AuxiliaryPolynomial.toFinsupp A =
      AuxiliaryPolynomial.toFinsupp Aold := by
    ext u
    rfl
  rw [hfs]
  rw [← eval_familyBlockLinearChange]
  exact hAold

/-! ## Evaluation and arithmetic of the selected basis combination -/

def basisCombination {m n : ℕ}
    (x : Fin m → Fin n → RatVector (n + 1))
    (z : Fin m × Fin n → ℤ) (h : Fin m) : RatVector (n + 1) :=
  ∑ j, (z (h, j) : ℚ) • x h j

theorem basisCombination_inZOneSix {m n : ℕ}
    (x : Fin m → Fin n → RatVector (n + 1))
    (hx : ∀ h j, AdelicMinkowski.InZOneSix (x h j))
    (z : Fin m × Fin n → ℤ) (h : Fin m) :
    AdelicMinkowski.InZOneSix (basisCombination x z h) := by
  classical
  unfold basisCombination
  let s : Finset (Fin n) := Finset.univ
  change AdelicMinkowski.InZOneSix
    (∑ j ∈ s, (z (h, j) : ℚ) • x h j)
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, AdelicMinkowski.inDenominatorLattice_zero⟩
  | @insert j s hj ih =>
      rw [Finset.sum_insert hj]
      exact (PadicSubspace.SIntegerApproximation.InZOneSixScalar.intCast
          (z (h, j))).smul
        (hx h j) |>.add ih

theorem formValue_basisCombination {m n : ℕ}
    (x : Fin m → Fin n → RatVector (n + 1))
    (z : Fin m × Fin n → ℤ) (h : Fin m)
    (F : RatVector (n + 1)) :
    formValue F (basisCombination x z h) =
      ∑ j, (z (h, j) : ℚ) * formValue F (x h j) := by
  classical
  unfold basisCombination formValue
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- At each of the three retained places, a bounded integral coefficient has
local norm at most `max 1 B`.  The maximum simultaneously accounts for the
ordinary Archimedean bound and the fact that every integer is in the unit
ball at the `2`- and `3`-adic places. -/
theorem realPlaceNorm_intCast_le_max_one_nat
    (v : Place23) (z : ℤ) (B : ℕ) (hz : |z| ≤ (B : ℤ)) :
    HeightBoxes.realPlaceNorm v (z : ℚ) ≤ max 1 (B : ℝ) := by
  fin_cases v
  · unfold HeightBoxes.realPlaceNorm placeNorm
    have hzR : ((|(z : ℚ)| : ℚ) : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast hz
    exact hzR.trans (le_max_right _ _)
  · unfold HeightBoxes.realPlaceNorm placeNorm
    have hzq := padicNorm.of_int (p := 2) z
    have hzR : ((padicNorm 2 (z : ℚ) : ℚ) : ℝ) ≤ 1 := by
      exact_mod_cast hzq
    exact hzR.trans (le_max_left _ _)
  · unfold HeightBoxes.realPlaceNorm placeNorm
    have hzq := padicNorm.of_int (p := 3) z
    have hzR : ((padicNorm 3 (z : ℚ) : ℚ) : ℝ) ≤ 1 := by
      exact_mod_cast hzq
    exact hzR.trans (le_max_left _ _)

/-- Local form bounds are preserved by the small integral grid, up to the
uniform factor `n * max 1 B`.  This is the quantitative evaluation bridge
from the S-integral approximation-box basis to the point where the selected
derivative is nonzero. -/
theorem realPlaceNorm_basisCombination_le
    {m n : ℕ}
    (L : Place23 → Fin (n + 1) → PadicSubspace.RatLinearForm (n + 1))
    (Q : Fin m → ℕ) (c : HeightBoxes.LocalConstants (n + 1))
    (x : Fin m → Fin n → RatVector (n + 1))
    (hx : ∀ h j, HeightBoxes.InApproximationBox L (Q h : ℝ) c (x h j))
    (z : Fin m × Fin n → ℤ) (B : ℕ)
    (hz : ∀ u, |z u| ≤ (B : ℤ))
    (h : Fin m) (v : Place23) (i : Fin (n + 1)) :
    HeightBoxes.realPlaceNorm v (L v i (basisCombination x z h)) ≤
      (n : ℝ) * max 1 (B : ℝ) *
        HeightBoxes.exponentRadius (Q h : ℝ) c v i := by
  classical
  let R : ℝ := HeightBoxes.exponentRadius (Q h : ℝ) c v i
  let C : ℝ := max 1 (B : ℝ)
  have hR : 0 ≤ R := Real.rpow_nonneg (by positivity) _
  have hC : 0 ≤ C := le_trans zero_le_one (le_max_left _ _)
  have heval : L v i (basisCombination x z h) =
      ∑ j, (z (h, j) : ℚ) * L v i (x h j) := by
    simp [basisCombination]
  rw [heval]
  by_cases hv : v = Place23.infinite
  · subst v
    have hsum := EvertseBasis.real_placeNorm_infinite_fin_sum_le_nat_mul
      (fun j : Fin n ↦ (z (h, j) : ℚ) *
        L Place23.infinite i (x h j))
      (C * R) (fun j ↦ EvertseBasis.real_placeNorm_mul_le_mul
        Place23.infinite (z (h, j) : ℚ)
        (L Place23.infinite i (x h j)) C R
        (realPlaceNorm_intCast_le_max_one_nat _ _ _ (hz (h, j)))
        (hx h j Place23.infinite i) hC)
    change HeightBoxes.realPlaceNorm Place23.infinite
        (∑ j, (z (h, j) : ℚ) * L Place23.infinite i (x h j)) ≤
      (n : ℝ) * C * R
    simpa only [HeightBoxes.realPlaceNorm, mul_assoc] using hsum
  · cases n with
    | zero =>
        simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero, zero_mul]
        change HeightBoxes.realPlaceNorm v 0 ≤ 0
        unfold HeightBoxes.realPlaceNorm
        rw [placeNorm_zero]
        norm_num
    | succ n =>
        have hsum := EvertseBasis.real_placeNorm_fin_sum_le_of_ne_infinite
          v hv (fun j : Fin (n + 1) ↦
            (z (h, j) : ℚ) * L v i (x h j))
          (C * R) (mul_nonneg hC hR)
          (fun j ↦ EvertseBasis.real_placeNorm_mul_le_mul
            v (z (h, j) : ℚ) (L v i (x h j)) C R
            (realPlaceNorm_intCast_le_max_one_nat _ _ _ (hz (h, j)))
            (hx h j v i) hC)
        change HeightBoxes.realPlaceNorm v
            (∑ j : Fin (n + 1), (z (h, j) : ℚ) * L v i (x h j)) ≤
          ((n + 1 : ℕ) : ℝ) * C * R
        have hone : (1 : ℝ) ≤ (n + 1 : ℕ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        calc
          _ ≤ C * R := by
            simpa only [HeightBoxes.realPlaceNorm] using hsum
          _ ≤ ((n + 1 : ℕ) : ℝ) * C * R := by
            have hC' : C ≤ ((n + 1 : ℕ) : ℝ) * C := by
              simpa using mul_le_mul_of_nonneg_right hone hC
            exact mul_le_mul_of_nonneg_right hC' hR

/-- The form-coordinate matrix image of the zero-normal adapted grid point
is exactly the actual integer linear combination of the supplied kernel
basis. -/
theorem familyMatrixPoint_toForm_adapted_eq_basisCombination
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (x : Fin m → Fin n → RatVector (n + 1))
    (hxker : ∀ h i, formValue (M h) (x h i) = 0)
    (z : Fin m × Fin n → ℤ) :
    familyMatrixPoint (toFormCoordinateMatrix M hM)
        (adaptedGridImage M hM x z) =
      fun u ↦ basisCombination x z u.1 u.2 := by
  funext u
  rcases u with ⟨h, k⟩
  let p := GeneralizedRoth.pivotIndex (M h) (hM h)
  let y := basisCombination x z h
  have hyker : formValue (M h) y = 0 := by
    rw [formValue_basisCombination]
    simp [hxker]
  by_cases hk : k = p
  · subst k
    have hp : M h p ≠ 0 :=
      GeneralizedRoth.pivotIndex_coeff_ne_zero (M h) (hM h)
    have hsplit :
        M h p * y p + ∑ j ∈ Finset.univ.erase p, M h j * y j = 0 := by
      rw [← hyker]
      unfold formValue
      rw [← Finset.add_sum_erase Finset.univ
        (fun j ↦ M h j * y j) (Finset.mem_univ p)]
    calc
      familyMatrixPoint (toFormCoordinateMatrix M hM)
          (adaptedGridImage M hM x z) (h, p) =
          -(M h p)⁻¹ *
            (∑ j ∈ Finset.univ.erase p, M h j * y j) := by
        unfold familyMatrixPoint toFormCoordinateMatrix
        rw [← Finset.add_sum_erase Finset.univ
          (fun j : Fin (n + 1) ↦
            (if hold : p = GeneralizedRoth.pivotIndex (M h) (hM h) then
                (M h p)⁻¹ *
                  (if j = GeneralizedRoth.pivotIndex (M h) (hM h) then 1
                    else -M h j)
              else if j = p then 1 else 0) *
              adaptedGridImage M hM x z (h, j))
          (Finset.mem_univ p)]
        have hpdef : p = GeneralizedRoth.pivotIndex (M h) (hM h) := rfl
        simp only [hpdef, dif_pos, if_pos, adaptedGridImage]
        simp only [mul_zero, zero_add]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjp : j ≠ p := (Finset.mem_erase.mp hj).1
        have hjpivot :
            j ≠ GeneralizedRoth.pivotIndex (M h) (hM h) := by
          simpa [p] using hjp
        simp only [hjpivot, if_false]
        change (M h p)⁻¹ * (-M h j) *
            (∑ i, (z (h, i) : ℚ) * x h i j) =
          -(M h p)⁻¹ * (M h j * y j)
        simp only [y, basisCombination, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul]
        ring
      _ = y p := by
        field_simp
        linarith
      _ = basisCombination x z h p := rfl
  · unfold familyMatrixPoint toFormCoordinateMatrix
    have hkpivot :
        k ≠ GeneralizedRoth.pivotIndex (M h) (hM h) := by
      simpa [p] using hk
    rw [Finset.sum_eq_single k]
    · simp [hkpivot, adaptedGridImage, basisCombination, y]
    · intro j hj hjk
      simp [hkpivot, hjk]
    · simp

theorem exists_originalDerivative_eval_basisCombination_ne_zero
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (x : Fin m → Fin n → RatVector (n + 1))
    (hxker : ∀ h i, formValue (M h) (x h i) = 0)
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (N : RestrictionIndex.NormalOrder m)
    (z : Fin m × Fin n → ℤ) (J : Fin m × Fin n →₀ ℕ)
    (hJ : RothIndex.hasseCoeff
      (restrictedBasisPolynomial M hM x P N)
      (fun u ↦ (z u : ℚ)) J ≠ 0) :
    ∃ A : AuxiliaryPolynomial.MonomialIndex m (n + 1)
        (fun h ↦ parameterDerivativeDegree J h + N h),
      MvPolynomial.eval (fun u ↦ basisCombination x z u.1 u.2)
        (SymmetricPower.hasseDerivative
          (AuxiliaryPolynomial.toFinsupp A) P) ≠ 0 := by
  obtain ⟨A, hA⟩ := exists_originalDerivative_eval_matrixPoint_ne_zero
    M hM x P N z J hJ
  refine ⟨A, ?_⟩
  rw [← familyMatrixPoint_toForm_adapted_eq_basisCombination
    M hM x hxker z]
  exact hA

/-- Every individual basis parameter occurs with degree at most the original
degree of its block.  This is the degree input needed by the finite-grid
Hermite lemma. -/
theorem degreeOf_restrictedBasisPolynomial_le
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (x : Fin m → Fin n → RatVector (n + 1))
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ}
    {d : Fin m → ℕ} (hP : RothIndex.IsMultiHomogeneous P d)
    (N : RestrictionIndex.NormalOrder m) (h : Fin m) (j : Fin n) :
    MvPolynomial.degreeOf (h, j)
        (restrictedBasisPolynomial M hM x P N) ≤ d h := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro K hK
  let D := RestrictionIndex.restrictedDividedDerivative M hM P N
  let R := restrictedBasisPolynomial M hM x P N
  have hrename : MvPolynomial.coeff (embeddedParameterOrder K)
      (MvPolynomial.rename parameterEmbedding R) =
        MvPolynomial.coeff K R := by
    exact MvPolynomial.coeff_rename_mapDomain parameterEmbedding
      parameterEmbedding_injective R K
  have hmapped : embeddedParameterOrder K ∈
      (familyBlockLinearChange (adaptedBasisMatrix M hM x) D).support := by
    rw [familyChange_adapted_restrictedDividedDerivative_eq_rename]
    rw [MvPolynomial.mem_support_iff, hrename]
    exact MvPolynomial.mem_support_iff.mp hK
  have hdegree :=
    (familyBlockLinearChange_isMultiHomogeneous
      (adaptedBasisMatrix M hM x)
      (restrictedDividedDerivative_isMultiHomogeneous M hM hP N)).of_mem_support
        hmapped h
  rw [blockOrder_embeddedParameterOrder] at hdegree
  calc
    K (h, j) ≤ ∑ k, K (h, k) :=
      Finset.single_le_sum (fun k _ ↦ Nat.zero_le (K (h, k)))
        (Finset.mem_univ j)
    _ = d h - N h := hdegree
    _ ≤ d h := Nat.sub_le _ _

theorem blockDegreeOfFinsupp_le_of_eval_hasseDerivative_ne_zero
    {m n : ℕ} {P : MvPolynomial (RothIndex.BlockVar m n) ℚ}
    {d : Fin m → ℕ} (hP : RothIndex.IsMultiHomogeneous P d)
    (A : RothIndex.BlockVar m n →₀ ℕ)
    (a : RothIndex.BlockVar m n → ℚ)
    (hne : MvPolynomial.eval a (SymmetricPower.hasseDerivative A P) ≠ 0)
    (h : Fin m) :
    SymmetricPower.blockDegreeOfFinsupp A h ≤ d h := by
  by_contra hnot
  have hlt : d h < SymmetricPower.blockDegreeOfFinsupp A h :=
    Nat.lt_of_not_ge hnot
  have hz : SymmetricPower.hasseDerivative A P = 0 := by
    classical
    rw [MvPolynomial.as_sum P]
    unfold SymmetricPower.hasseDerivative
    simp only [map_sum, MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro e he
    change SymmetricPower.hasseDerivative A
      (MvPolynomial.monomial e (MvPolynomial.coeff e P)) = 0
    rw [SymmetricPower.hasseDerivative_monomial]
    have hex : ∃ j : Fin (n + 1), e (h, j) < A (h, j) := by
      by_contra hall
      push Not at hall
      have hsum : (∑ j, A (h, j)) ≤ ∑ j, e (h, j) :=
        Finset.sum_le_sum fun j _ ↦ hall j
      have hedegree := hP.of_mem_support he h
      unfold SymmetricPower.blockDegreeOfFinsupp at hlt
      unfold RothIndex.blockOrder at hedegree
      omega
    obtain ⟨j, hj⟩ := hex
    have hprod : (∏ u, (Nat.choose (e u) (A u) : ℚ)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ (h, j))
      rw [Nat.choose_eq_zero_of_lt hj]
      norm_num
    rw [hprod, mul_zero, MvPolynomial.monomial_zero]
  apply hne
  rw [hz]
  simp

/-! ## End-to-end extraction -/

/-- From the form-index bound and an actual hyperplane box basis, extract a
bounded integer grid point and an original-polynomial derivative with exact
block totals. -/
theorem exists_grid_originalDerivative_of_formIndex_le
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (x : Fin m → Fin n → RatVector (n + 1))
    (hxlin : ∀ h, LinearIndependent ℚ (x h))
    (hxker : ∀ h i, formValue (M h) (x h i) = 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    {d : Fin m → ℕ} (hhom : RothIndex.IsMultiHomogeneous P d)
    {indexBound : ℚ}
    (hindex : GeneralizedRoth.formIndex M hM P d ≤ indexBound)
    (B : ℕ) :
    ∃ N : RestrictionIndex.NormalOrder m,
      RestrictionIndex.normalWeight d N ≤ indexBound ∧
      ∃ z : Fin m × Fin n → ℤ,
        (∀ u, |z u| ≤ (B : ℤ)) ∧
        ∃ J : Fin m × Fin n →₀ ℕ,
          (∀ h j, J (h, j) ≤ d h / (B + 1)) ∧
          ∃ A : AuxiliaryPolynomial.MonomialIndex m (n + 1)
              (fun h ↦ parameterDerivativeDegree J h + N h),
            MvPolynomial.eval (fun u ↦ basisCombination x z u.1 u.2)
              (SymmetricPower.hasseDerivative
                (AuxiliaryPolynomial.toFinsupp A) P) ≠ 0 := by
  obtain ⟨N, hNweight, hN⟩ :=
    RestrictionIndex.exists_restrictedDividedDerivative_of_formIndex_le
      M hM hP d hindex
  have hR : restrictedBasisPolynomial M hM x P N ≠ 0 :=
    restrictedBasisPolynomial_ne_zero M hM x hxlin hxker P N hN
  obtain ⟨z, hz, J, hJdegree, hJ⟩ :=
    exists_smallInteger_hasseCoeff_ne_zero_fintype
      (restrictedBasisPolynomial M hM x P N) hR B
  have hJdegree' : ∀ h j, J (h, j) ≤ d h / (B + 1) := by
    intro h j
    exact (hJdegree (h, j)).trans
      (Nat.div_le_div_right
        (degreeOf_restrictedBasisPolynomial_le M hM x hhom N h j))
  obtain ⟨A, hA⟩ := exists_originalDerivative_eval_basisCombination_ne_zero
    M hM x hxker P N z J hJ
  exact ⟨N, hNweight, z, hz, J, hJdegree', A, hA⟩

/-- Repackage an exact derivative monomial whose block totals are bounded by
the auxiliary multidegrees as the standard GLR derivative-index type. -/
def packageDerivativeIndex {m n : ℕ} (d total : Fin m → ℕ)
    (htotal : ∀ h, total h ≤ d h)
    (A : AuxiliaryPolynomial.MonomialIndex m (n + 1) total) :
    GLRAuxiliary.DerivativeIndex m (n + 1) d := by
  let k : GLRAuxiliary.DerivativeDegree m d :=
    fun h ↦ ⟨total h, Nat.lt_succ_of_le (htotal h)⟩
  let A' : AuxiliaryPolynomial.MonomialIndex m (n + 1) (fun h ↦ k h) :=
    fun h ↦
      ⟨fun j ↦ ⟨(A h).1 j, by
          simpa [k] using ((A h).1 j).isLt⟩,
        by simpa [k] using (A h).2⟩
  exact GLRAuxiliary.fixedDerivativeIndex k A'

@[simp] theorem packageDerivativeIndex_blockOrder {m n : ℕ}
    (d total : Fin m → ℕ) (htotal : ∀ h, total h ≤ d h)
    (A : AuxiliaryPolynomial.MonomialIndex m (n + 1) total) (h : Fin m) :
    (packageDerivativeIndex d total htotal A).blockOrder h = total h := by
  rfl

@[simp] theorem orderFinsupp_packageDerivativeIndex {m n : ℕ}
    (d total : Fin m → ℕ) (htotal : ∀ h, total h ≤ d h)
    (A : AuxiliaryPolynomial.MonomialIndex m (n + 1) total) :
    GLRAuxiliary.orderFinsupp (packageDerivativeIndex d total htotal A) =
      AuxiliaryPolynomial.toFinsupp A := by
  ext u
  rfl

/-- Standard-GLR-index form of the basis nonvanishing bridge, with its
explicit normalized weight loss `m*n/(B+1)`. -/
theorem exists_standardDerivativeIndex_of_formIndex_le
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (x : Fin m → Fin n → RatVector (n + 1))
    (hxlin : ∀ h, LinearIndependent ℚ (x h))
    (hxker : ∀ h i, formValue (M h) (x h i) = 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    {d : Fin m → ℕ} (hd : ∀ h, 0 < d h)
    (hhom : RothIndex.IsMultiHomogeneous P d)
    {indexBound : ℚ}
    (hindex : GeneralizedRoth.formIndex M hM P d ≤ indexBound)
    (B : ℕ) :
    ∃ I : GLRAuxiliary.DerivativeIndex m (n + 1) d,
      GLRAuxiliary.derivativeWeight I ≤
        indexBound + (m : ℚ) * (n : ℚ) / (B + 1 : ℚ) ∧
      ∃ z : Fin m × Fin n → ℤ,
        (∀ u, |z u| ≤ (B : ℤ)) ∧
        MvPolynomial.eval (fun u ↦ basisCombination x z u.1 u.2)
          (SymmetricPower.hasseDerivative
            (GLRAuxiliary.orderFinsupp I) P) ≠ 0 := by
  obtain ⟨N, hNweight, z, hz, J, hJdegree, A, hA⟩ :=
    exists_grid_originalDerivative_of_formIndex_le
      M hM x hxlin hxker hP hhom hindex B
  let total : Fin m → ℕ := fun h ↦ parameterDerivativeDegree J h + N h
  have htotal : ∀ h, total h ≤ d h := by
    intro h
    have hblock := blockDegreeOfFinsupp_le_of_eval_hasseDerivative_ne_zero
      hhom (AuxiliaryPolynomial.toFinsupp A)
      (fun u ↦ basisCombination x z u.1 u.2) hA h
    change parameterDerivativeDegree J h + N h ≤ d h
    have heq : SymmetricPower.blockDegreeOfFinsupp
        (AuxiliaryPolynomial.toFinsupp A) h =
        parameterDerivativeDegree J h + N h := by
      change (∑ j, AuxiliaryPolynomial.exponent A (h, j)) = _
      exact (A h).2
    rw [← heq]
    exact hblock
  let I := packageDerivativeIndex d total htotal A
  have hparameter : ∀ h,
      parameterDerivativeDegree J h ≤ n * (d h / (B + 1)) := by
    intro h
    rw [parameterDerivativeDegree_eq_sum]
    calc
      (∑ j, J (h, j)) ≤ ∑ _j : Fin n, d h / (B + 1) :=
        Finset.sum_le_sum fun j _ ↦ hJdegree h j
      _ = n * (d h / (B + 1)) := by simp
  have hextra : ∀ h,
      (parameterDerivativeDegree J h : ℚ) / (d h : ℚ) ≤
        (n : ℚ) / (B + 1 : ℚ) := by
    intro h
    have hdq : (0 : ℚ) < d h := by exact_mod_cast hd h
    have hBq : (0 : ℚ) < B + 1 := by positivity
    rw [div_le_div_iff₀ hdq hBq]
    have hpq : (parameterDerivativeDegree J h : ℚ) ≤
        (n : ℚ) * (d h / (B + 1) : ℕ) := by
      exact_mod_cast hparameter h
    have hfloor : ((d h / (B + 1) : ℕ) : ℚ) * (B + 1 : ℚ) ≤ d h := by
      exact_mod_cast Nat.div_mul_le_self (d h) (B + 1)
    nlinarith
  refine ⟨I, ?_, z, hz, ?_⟩
  · unfold GLRAuxiliary.derivativeWeight
    calc
      (∑ h, ((I.blockOrder h : ℕ) : ℚ) / (d h : ℚ)) =
          RestrictionIndex.normalWeight d N +
            ∑ h, (parameterDerivativeDegree J h : ℚ) / (d h : ℚ) := by
        unfold RestrictionIndex.normalWeight I total
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro h hh
        simp only [packageDerivativeIndex_blockOrder]
        push_cast
        ring
      _ ≤ indexBound + ∑ _h : Fin m, (n : ℚ) / (B + 1 : ℚ) :=
        add_le_add hNweight (Finset.sum_le_sum fun h _ ↦ hextra h)
      _ = indexBound + (m : ℚ) * (n : ℚ) / (B + 1 : ℚ) := by
        simp
        ring
  · rw [orderFinsupp_packageDerivativeIndex]
    exact hA

/-- Integral-coefficient specialization used by the product-formula stage.
The nonzero value is stated for the actual integral divided-derivative
polynomial, while every coordinate of the selected point remains in
`Z[1/6]`. -/
theorem exists_integralDerivativeIndex_of_formIndex_le
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (x : Fin m → Fin n → RatVector (n + 1))
    (hxlin : ∀ h, LinearIndependent ℚ (x h))
    (hxker : ∀ h i, formValue (M h) (x h i) = 0)
    (hxS : ∀ h j, AdelicMinkowski.InZOneSix (x h j))
    {d : Fin m → ℕ} (hd : ∀ h, 0 < d h)
    (c : AuxiliaryPolynomial.MonomialIndex m (n + 1) d → ℤ)
    (hc : AuxiliaryPolynomial.ofCoefficients c ≠ 0)
    {indexBound : ℚ}
    (hindex : GeneralizedRoth.formIndex M hM
      (AuxiliaryPolynomial.ofCoefficients (fun A ↦ (c A : ℚ))) d ≤
        indexBound)
    (B : ℕ) :
    ∃ I : GLRAuxiliary.DerivativeIndex m (n + 1) d,
      GLRAuxiliary.derivativeWeight I ≤
        indexBound + (m : ℚ) * (n : ℚ) / (B + 1 : ℚ) ∧
      ∃ z : Fin m × Fin n → ℤ,
        (∀ u, |z u| ≤ (B : ℤ)) ∧
        (∀ h, AdelicMinkowski.InZOneSix (basisCombination x z h)) ∧
        MvPolynomial.eval₂ (Int.castRingHom ℚ)
          (fun u ↦ basisCombination x z u.1 u.2)
          (GLRAuxiliary.dividedDerivativeOfCoefficients I c) ≠ 0 := by
  let P : MvPolynomial (RothIndex.BlockVar m n) ℚ :=
    AuxiliaryPolynomial.ofCoefficients (fun A ↦ (c A : ℚ))
  have hcfn : c ≠ 0 := by
    intro hzero
    apply hc
    simp [hzero, AuxiliaryPolynomial.ofCoefficients]
  have hcqfn : (fun A ↦ (c A : ℚ)) ≠ 0 := by
    intro hzero
    apply hcfn
    funext A
    have hA : (c A : ℚ) = 0 := by
      simpa using congrFun hzero A
    exact_mod_cast hA
  have hP : P ≠ 0 := AuxiliaryPolynomial.ofCoefficients_ne_zero hcqfn
  have hhom : RothIndex.IsMultiHomogeneous P d := by
    intro J hJ h
    exact AuxiliaryPolynomial.blockDegree_of_mem_support
      (fun A ↦ (c A : ℚ)) (MvPolynomial.mem_support_iff.mpr hJ) h
  obtain ⟨I, hIweight, z, hz, hne⟩ :=
    exists_standardDerivativeIndex_of_formIndex_le
      M hM x hxlin hxker hP hd hhom hindex B
  refine ⟨I, hIweight, z, hz, fun h ↦ basisCombination_inZOneSix x hxS z h, ?_⟩
  have hmap := GLRAuxiliary.map_dividedDerivativeOfCoefficients I c
  rw [MvPolynomial.eval₂_eq_eval_map]
  rw [hmap]
  exact hne

theorem exists_integralDerivativeIndex_weight_le_blocks_mul
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ h, M h ≠ 0)
    (x : Fin m → Fin n → RatVector (n + 1))
    (hxlin : ∀ h, LinearIndependent ℚ (x h))
    (hxker : ∀ h i, formValue (M h) (x h i) = 0)
    (hxS : ∀ h j, AdelicMinkowski.InZOneSix (x h j))
    {d : Fin m → ℕ} (hd : ∀ h, 0 < d h)
    (c : AuxiliaryPolynomial.MonomialIndex m (n + 1) d → ℤ)
    (hc : AuxiliaryPolynomial.ofCoefficients c ≠ 0)
    {indexBound eta : ℚ}
    (hindex : GeneralizedRoth.formIndex M hM
      (AuxiliaryPolynomial.ofCoefficients (fun A ↦ (c A : ℚ))) d ≤
        indexBound)
    (B : ℕ)
    (hbudget : indexBound + (m : ℚ) * (n : ℚ) / (B + 1 : ℚ) ≤
      (m : ℚ) * eta) :
    ∃ I : GLRAuxiliary.DerivativeIndex m (n + 1) d,
      GLRAuxiliary.derivativeWeight I ≤ (m : ℚ) * eta ∧
      ∃ z : Fin m × Fin n → ℤ,
        (∀ u, |z u| ≤ (B : ℤ)) ∧
        (∀ h, AdelicMinkowski.InZOneSix (basisCombination x z h)) ∧
        MvPolynomial.eval₂ (Int.castRingHom ℚ)
          (fun u ↦ basisCombination x z u.1 u.2)
          (GLRAuxiliary.dividedDerivativeOfCoefficients I c) ≠ 0 := by
  obtain ⟨I, hI, z, hz, hS, hne⟩ :=
    exists_integralDerivativeIndex_of_formIndex_le
      M hM x hxlin hxker hxS hd c hc hindex B
  exact ⟨I, hI.trans hbudget, z, hz, hS, hne⟩

end

end Erdos407.BasisNonvanishing
