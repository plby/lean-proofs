import Wikipedia.SzemeredisTheorem.Transference.GeneralizedConvolution
import Wikipedia.SzemeredisTheorem.Transference.PolynomialApproximation

/-!
# Reduction of bounded cut tests to Boolean cut tests

On a finite space, a `[0,1]`-valued cut-test family is a convex mixture of
its Boolean vertices.  Since every monomial in a cut correlation uses each
test coordinate at most once, the correlation is exactly the same convex
mixture of Boolean correlations.  Consequently it is enough to control the
finite family of Boolean cut tests in the dense-model theorem.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators Polynomial

/-! ## Finite Bernoulli mixtures -/

/-- Product Bernoulli weight of a Boolean assignment. -/
def bernoulliAssignmentWeight
    {κ : Type*} [Fintype κ]
    (p : κ → ℝ) (b : κ → Bool) : ℝ :=
  ∏ i, if b i then p i else 1 - p i

/-- Real indicator of one bit of an assignment. -/
def booleanValue {κ : Type*} (b : κ → Bool) (i : κ) : ℝ :=
  if b i then 1 else 0

theorem bernoulliAssignmentWeight_nonneg
    {κ : Type*} [Fintype κ]
    {p : κ → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (b : κ → Bool) :
    0 ≤ bernoulliAssignmentWeight p b := by
  apply Finset.prod_nonneg
  intro i _
  by_cases hi : b i
  · simpa [hi] using hp0 i
  · simp only [hi, Bool.false_eq_true,
      ↓reduceIte]
    linarith [hp1 i]

/-- Product Bernoulli weights sum to one. -/
theorem sum_bernoulliAssignmentWeight
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p : κ → ℝ) :
    ∑ b : κ → Bool, bernoulliAssignmentWeight p b = 1 := by
  change
    (∑ b : κ → Bool,
      ∏ i, if b i then p i else 1 - p i) = 1
  calc
    (∑ b : κ → Bool,
        ∏ i, if b i then p i else 1 - p i) =
        ∏ i, ∑ bit : Bool,
          if bit then p i else 1 - p i :=
      (Fintype.prod_sum
        (fun i : κ => fun bit : Bool =>
          if bit then p i else 1 - p i)).symm
    _ = ∏ _i : κ, (1 : ℝ) := by
      apply Fintype.prod_congr
      intro i
      simp
    _ = 1 := by simp

/-- Bernoulli moment of a selected finite set of coordinates. -/
theorem sum_bernoulliAssignmentWeight_mul_selected
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p : κ → ℝ) (s : Finset κ) :
    ∑ b : κ → Bool,
        bernoulliAssignmentWeight p b *
          ∏ i ∈ s, booleanValue b i =
      ∏ i ∈ s, p i := by
  calc
    (∑ b : κ → Bool,
        bernoulliAssignmentWeight p b *
          ∏ i ∈ s, booleanValue b i) =
        ∑ b : κ → Bool,
          ∏ i,
            (if b i then p i else 1 - p i) *
              (if i ∈ s then booleanValue b i else 1) := by
      apply Fintype.sum_congr
      intro b
      have hselected :
          (∏ i ∈ s, booleanValue b i) =
            ∏ i, if i ∈ s then booleanValue b i else 1 :=
        (Fintype.prod_ite_mem s
          (fun i => booleanValue b i)).symm
      rw [bernoulliAssignmentWeight, hselected]
      rw [← Finset.prod_mul_distrib]
    _ = ∏ i, ∑ bit : Bool,
          (if bit then p i else 1 - p i) *
            (if i ∈ s then
              (if bit then (1 : ℝ) else 0) else 1) :=
      (Fintype.prod_sum
        (fun i : κ => fun bit : Bool =>
          (if bit then p i else 1 - p i) *
            (if i ∈ s then
              (if bit then (1 : ℝ) else 0) else 1))).symm
    _ = ∏ i, if i ∈ s then p i else 1 := by
      apply Fintype.prod_congr
      intro i
      by_cases hi : i ∈ s <;> simp [hi]
    _ = ∏ i ∈ s, p i := by
      exact Fintype.prod_ite_mem s p

/-- Bernoulli moment pulled back along an embedding. -/
theorem sum_bernoulliAssignmentWeight_mul_embedding
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ]
    (p : κ → ℝ) (e : ι ↪ κ) :
    ∑ b : κ → Bool,
        bernoulliAssignmentWeight p b *
          ∏ i : ι, booleanValue b (e i) =
      ∏ i : ι, p (e i) := by
  simpa only [Finset.prod_map, Finset.mem_univ, true_and,
    Finset.coe_univ, Function.Embedding.coeFn_mk] using
    (sum_bernoulliAssignmentWeight_mul_selected p
      (Finset.univ.map e))

/-! ## Boolean cut coordinates -/

/-- One scalar coordinate in a cut-test family. -/
abbrev CutTestCoordinate (G : Type*) (r : ℕ) :=
  Fin r × (Fin (r - 1) → G)

/-- A Boolean choice for every scalar coordinate of a cut-test family. -/
abbrev BooleanCutAssignment (G : Type*) (r : ℕ) :=
  CutTestCoordinate G r → Bool

/-- Regard a Boolean assignment as a `{0,1}`-valued cut-test family. -/
def cutTestFamilyOfBooleanAssignment
    {G : Type*} {r : ℕ}
    (b : BooleanCutAssignment G r) :
    CutTestFamily G r :=
  fun i y => booleanValue b ⟨i, y⟩

theorem cutTestFamilyOfBooleanAssignment_bounded
    {G : Type*} {r : ℕ}
    (b : BooleanCutAssignment G r) :
    IsBoundedCutTest (cutTestFamilyOfBooleanAssignment b) := by
  constructor <;> intro i y <;>
    unfold cutTestFamilyOfBooleanAssignment booleanValue <;>
    split <;> norm_num

/-- Flatten a cut-test family to its finite vector of scalar coordinates. -/
def cutTestCoordinateValue
    {G : Type*} {r : ℕ}
    (u : CutTestFamily G r) :
    CutTestCoordinate G r → ℝ :=
  fun q => u q.1 q.2

/-- The coordinates selected by one full tuple, as an embedding indexed by
the edge colour.  Injectivity is immediate from the colour component. -/
def usedCutTestCoordinateEmbedding
    {G : Type*} {r : ℕ} (x : Fin r → G) :
    Fin r ↪ CutTestCoordinate G r where
  toFun i := ⟨i, eraseCoordinate i x⟩
  inj' := by
    intro i j h
    exact congrArg Prod.fst h

@[simp]
theorem usedCutTestCoordinateEmbedding_apply
    {G : Type*} {r : ℕ} (x : Fin r → G) (i : Fin r) :
    usedCutTestCoordinateEmbedding x i =
      (i, eraseCoordinate i x) :=
  rfl

/-- Exact Bernoulli mixture identity for one product of cut tests. -/
theorem cutTestProduct_eq_sum_boolean
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (u : CutTestFamily G r) (x : Fin r → G) :
    cutTestProduct u x =
      ∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          cutTestProduct
            (cutTestFamilyOfBooleanAssignment b) x := by
  classical
  symm
  simpa [cutTestProduct, cutTestCoordinateValue,
    cutTestFamilyOfBooleanAssignment,
    usedCutTestCoordinateEmbedding_apply] using
    (sum_bernoulliAssignmentWeight_mul_embedding
      (cutTestCoordinateValue u)
      (usedCutTestCoordinateEmbedding x))

/-- Exact convex-mixture formula for a cut correlation. -/
theorem cutCorrelation_eq_sum_boolean
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : CutTestFamily G r) :
    cutCorrelation r f g u =
      ∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          cutCorrelation r f g
            (cutTestFamilyOfBooleanAssignment b) := by
  unfold cutCorrelation
  calc
    mean (fun x : Fin r → G =>
        (f (∑ i, x i) - g (∑ i, x i)) *
          ∏ i, u i (eraseCoordinate i x)) =
        mean (fun x : Fin r → G =>
          ∑ b : BooleanCutAssignment G r,
            bernoulliAssignmentWeight
                (cutTestCoordinateValue u) b *
              ((f (∑ i, x i) - g (∑ i, x i)) *
                cutTestProduct
                  (cutTestFamilyOfBooleanAssignment b) x)) := by
      apply congrArg mean
      funext x
      change
        (f (∑ i, x i) - g (∑ i, x i)) *
            cutTestProduct u x =
          _
      rw [cutTestProduct_eq_sum_boolean u x]
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro b
      ring
    _ = ∑ b : BooleanCutAssignment G r,
        mean (fun x : Fin r → G =>
          bernoulliAssignmentWeight
              (cutTestCoordinateValue u) b *
            ((f (∑ i, x i) - g (∑ i, x i)) *
              cutTestProduct
                (cutTestFamilyOfBooleanAssignment b) x)) := by
      unfold mean
      exact Finset.expect_sum_comm Finset.univ Finset.univ _
    _ = ∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          mean (fun x : Fin r → G =>
            (f (∑ i, x i) - g (∑ i, x i)) *
              cutTestProduct
                (cutTestFamilyOfBooleanAssignment b) x) := by
      apply Fintype.sum_congr
      intro b
      exact mean_smul
        (bernoulliAssignmentWeight
          (cutTestCoordinateValue u) b) _
    _ = _ := by
      rfl

/-- It is enough to bound all Boolean cut correlations. -/
theorem abs_cutCorrelation_le_of_boolean
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε : ℝ}
    (u : CutTestFamily G r) (hu : IsBoundedCutTest u)
    (hboolean :
      ∀ b : BooleanCutAssignment G r,
        |cutCorrelation r f g
          (cutTestFamilyOfBooleanAssignment b)| ≤ ε) :
    |cutCorrelation r f g u| ≤ ε := by
  rw [cutCorrelation_eq_sum_boolean]
  calc
    |∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          cutCorrelation r f g
            (cutTestFamilyOfBooleanAssignment b)| ≤
        ∑ b : BooleanCutAssignment G r,
          |bernoulliAssignmentWeight
              (cutTestCoordinateValue u) b *
            cutCorrelation r f g
              (cutTestFamilyOfBooleanAssignment b)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b * ε := by
      apply Finset.sum_le_sum
      intro b _
      have hw :
          0 ≤ bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b :=
        bernoulliAssignmentWeight_nonneg
          (p := cutTestCoordinateValue u)
          (fun q => hu.nonneg q.1 q.2)
          (fun q => hu.le_one q.1 q.2) b
      rw [abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (hboolean b) hw
    _ = ε := by
      rw [← Finset.sum_mul,
        sum_bernoulliAssignmentWeight, one_mul]

/-! ## The finite dense-model test family -/

/-- Generalized convolution belonging to one Boolean cut assignment. -/
noncomputable def booleanCutConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (b : BooleanCutAssignment G r) : G → ℝ :=
  generalizedConvolution r
    (cutTestFamilyOfBooleanAssignment b)

/-- At positive arity every Boolean generalized convolution is
`[0,1]`-valued. -/
theorem booleanCutConvolution_unitBounded
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r)
    (b : BooleanCutAssignment G r) :
    IsUnitBounded (booleanCutConvolution r b) := by
  constructor
  · intro z
    exact generalizedConvolution_nonneg hr
      (cutTestFamilyOfBooleanAssignment_bounded b) z
  · intro z
    exact generalizedConvolution_le_one hr
      (cutTestFamilyOfBooleanAssignment_bounded b) z

/-- The finite Boolean convolution family is pointwise unit bounded at
positive arity. -/
theorem booleanCutConvolution_unitBoundedFamily
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r) :
    IsUnitBoundedTestFamily
      (booleanCutConvolution (G := G) r) :=
  fun b => booleanCutConvolution_unitBounded hr b

/-- Pairing with a Boolean generalized convolution is exactly its Boolean
cut correlation. -/
theorem cutCorrelation_boolean_eq_pairing
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ)
    (b : BooleanCutAssignment G r) :
    cutCorrelation r f g
        (cutTestFamilyOfBooleanAssignment b) =
      finitePairing (f - g) (booleanCutConvolution r b) := by
  rw [cutCorrelation_eq_mean_mul_generalizedConvolution]
  rfl

/-- A model matching all finitely many Boolean generalized convolutions
already satisfies the full cut-discrepancy relation against arbitrary
`[0,1]`-valued cut tests. -/
theorem exists_cutDiscrepancy_model_of_finiteBooleanModel
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (r : ℕ) (f : G → ℝ) {ε : ℝ}
    (hmodel :
      HasFiniteDenseModel
        (booleanCutConvolution (G := G) r) f ε) :
    ∃ g : G → ℝ, IsUnitBounded g ∧
      CutDiscrepancyLe r f g ε := by
  obtain ⟨g, hg, hmatch⟩ := hmodel
  refine ⟨g, hg, ?_⟩
  intro u hu0 hu1
  apply abs_cutCorrelation_le_of_boolean u ⟨hu0, hu1⟩
  intro b
  rw [cutCorrelation_boolean_eq_pairing]
  exact hmatch b

/-- Dense-model theorem in the cut norm.  Its sole pseudorandomness input
is the homogeneous positive-part correlation bound for the finite family
of Boolean generalized convolutions. -/
theorem exists_cutDiscrepancy_model_of_positivePartCorrelationBound
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (r : ℕ) {f ν : G → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    (hpseudo :
      HasPositivePartCorrelationBound
        (booleanCutConvolution (G := G) r) ν ε) :
    ∃ g : G → ℝ, IsUnitBounded g ∧
      CutDiscrepancyLe r f g ε := by
  apply exists_cutDiscrepancy_model_of_finiteBooleanModel r f
  exact hasFiniteDenseModel_of_positivePartCorrelationBound
    (booleanCutConvolution (G := G) r)
    hε hf0 hfν hpseudo

/-- Polynomial dense-model theorem in the cut norm.  It replaces the
positive-part hypothesis by finite correlation estimates for products of
Boolean generalized convolutions, with all quantitative losses explicit. -/
theorem exists_cutDiscrepancy_model_of_monomialCorrelationBound
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (r : ℕ) (hr : 0 < r)
    {f ν : G → ℝ}
    {p : ℝ[X]} {δ η M : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hM0 : 0 ≤ M)
    (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    (hp : ApproximatesPositivePartOnUnitInterval p δ)
    (hM : centeredAbsoluteMean ν ≤ M)
    (hmono :
      HasMonomialCorrelationBound
        (booleanCutConvolution (G := G) r)
        ν p.natDegree η) :
    ∃ g : G → ℝ, IsUnitBounded g ∧
      CutDiscrepancyLe r f g
        (polynomialCoefficientL1 p * η + δ * M) := by
  apply
    exists_cutDiscrepancy_model_of_positivePartCorrelationBound
      r
  · exact add_nonneg
      (mul_nonneg (polynomialCoefficientL1_nonneg p) hη)
      (mul_nonneg hδ hM0)
  · exact hf0
  · exact hfν
  · exact hasPositivePartCorrelationBound_of_polynomial
      (booleanCutConvolution_unitBoundedFamily hr)
      hδ hp hM hmono

end Wikipedia.SzemeredisTheorem
