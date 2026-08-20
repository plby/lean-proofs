/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

namespace Erdos407.RothIndex

open scoped BigOperators

noncomputable section

/-! ## Hasse coefficients and order of vanishing -/

/-- Translate the origin to `x`.  The coefficients of this polynomial are
the multivariate Hasse derivatives of `P` at `x`. -/
def translate {ι : Type*} (x : ι → ℚ) (P : MvPolynomial ι ℚ) :
    MvPolynomial ι ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i ↦ MvPolynomial.X i + MvPolynomial.C (x i)) P

@[simp] theorem translate_C {ι : Type*} (x : ι → ℚ) (a : ℚ) :
    translate x (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [translate]

@[simp] theorem translate_X {ι : Type*} (x : ι → ℚ) (i : ι) :
    translate x (MvPolynomial.X i) =
      MvPolynomial.X i + MvPolynomial.C (x i) := by
  simp [translate]

@[simp] theorem translate_add {ι : Type*} (x : ι → ℚ)
    (P Q : MvPolynomial ι ℚ) :
    translate x (P + Q) = translate x P + translate x Q := by
  exact map_add (MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i ↦ MvPolynomial.X i + MvPolynomial.C (x i))) P Q

@[simp] theorem translate_mul {ι : Type*} (x : ι → ℚ)
    (P Q : MvPolynomial ι ℚ) :
    translate x (P * Q) = translate x P * translate x Q := by
  exact map_mul (MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i ↦ MvPolynomial.X i + MvPolynomial.C (x i))) P Q

/-- Translation by `x` is inverted by translation by `-x`. -/
theorem translate_neg_translate {ι : Type*} (x : ι → ℚ)
    (P : MvPolynomial ι ℚ) :
    translate (fun i ↦ -x i) (translate x P) = P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP => simp [hP, add_assoc]

@[simp] theorem translate_zero {ι : Type*} (P : MvPolynomial ι ℚ) :
    translate (fun _ ↦ 0) P = P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP => simp [hP]

/-- Successive translations add their centers. -/
theorem translate_translate {ι : Type*} (x y : ι → ℚ)
    (P : MvPolynomial ι ℚ) :
    translate x (translate y P) = translate (fun i ↦ x i + y i) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP => simp [hP, add_assoc]

theorem translate_ne_zero {ι : Type*} {x : ι → ℚ}
    {P : MvPolynomial ι ℚ} (hP : P ≠ 0) : translate x P ≠ 0 := by
  intro hzero
  have := congrArg (translate (fun i ↦ -x i)) hzero
  rw [translate_neg_translate] at this
  simpa [translate] using hP this

/-- The `J`th multivariate Hasse coefficient of `P` at `x`. -/
def hasseCoeff {ι : Type*} (P : MvPolynomial ι ℚ)
    (x : ι → ℚ) (J : ι →₀ ℕ) : ℚ :=
  MvPolynomial.coeff J (translate x P)

@[simp] theorem hasseCoeff_zero {ι : Type*} (P : MvPolynomial ι ℚ)
    (J : ι →₀ ℕ) :
    hasseCoeff P (fun _ ↦ 0) J = MvPolynomial.coeff J P := by
  simp [hasseCoeff]

theorem exists_hasseCoeff_ne_zero {ι : Type*} {P : MvPolynomial ι ℚ}
    (hP : P ≠ 0) (x : ι → ℚ) :
    ∃ J : ι →₀ ℕ, hasseCoeff P x J ≠ 0 := by
  have hsupp : (translate x P).support.Nonempty :=
    MvPolynomial.support_nonempty.mpr (translate_ne_zero hP)
  obtain ⟨J, hJ⟩ := hsupp
  exact ⟨J, MvPolynomial.mem_support_iff.mp hJ⟩

/-- The zeroth Hasse coefficient is ordinary evaluation. -/
@[simp] theorem hasseCoeff_zeroIndex {ι : Type*}
    (P : MvPolynomial ι ℚ) (x : ι → ℚ) :
    hasseCoeff P x 0 = MvPolynomial.eval x P := by
  unfold hasseCoeff
  rw [← MvPolynomial.constantCoeff_eq]
  induction P using MvPolynomial.induction_on with
  | C a => simp [translate]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP => simp [hP]

/-! ## Block multi-indices and normalized index -/

/-- The variables in `m` blocks of projective dimension `n`. -/
abbrev BlockVar (m n : ℕ) := Fin m × Fin (n + 1)

/-- A multi-index for a block polynomial. -/
abbrev MultiIndex (m n : ℕ) := BlockVar m n →₀ ℕ

/-- The order of a multi-index in one block. -/
def blockOrder {m n : ℕ} (J : MultiIndex m n) (j : Fin m) : ℕ :=
  ∑ k : Fin (n + 1), J (j, k)

/-- The normalized weight `sum_j |J_j| / d_j` used in Roth's index. -/
def normalizedWeight {m n : ℕ} (d : Fin m → ℕ)
    (J : MultiIndex m n) : ℚ :=
  ∑ j : Fin m, (blockOrder J j : ℚ) / (d j : ℚ)

theorem normalizedWeight_nonneg {m n : ℕ} (d : Fin m → ℕ)
    (J : MultiIndex m n) : 0 ≤ normalizedWeight d J := by
  unfold normalizedWeight
  positivity

@[simp] theorem normalizedWeight_zero {m n : ℕ} (d : Fin m → ℕ) :
    normalizedWeight (n := n) d 0 = 0 := by
  simp [normalizedWeight, blockOrder]

/-- A tuple of `m` rational projective vectors. -/
abbrev MultiPoint (m n : ℕ) := Fin m → Fin (n + 1) → ℚ

/-- Flatten a tuple of projective vectors to a value for every block variable. -/
def flattenPoint {m n : ℕ} (x : MultiPoint m n) : BlockVar m n → ℚ :=
  fun i ↦ x i.1 i.2

/-- The Hasse coefficient of a block polynomial at a tuple of points. -/
def blockHasseCoeff {m n : ℕ} (P : MvPolynomial (BlockVar m n) ℚ)
    (x : MultiPoint m n) (J : MultiIndex m n) : ℚ :=
  hasseCoeff P (flattenPoint x) J

@[simp] theorem blockHasseCoeff_zeroIndex {m n : ℕ}
    (P : MvPolynomial (BlockVar m n) ℚ) (x : MultiPoint m n) :
    blockHasseCoeff P x 0 = MvPolynomial.eval (flattenPoint x) P := by
  simp [blockHasseCoeff]

/-- Multihomogeneity of degree `d`, expressed directly in terms of the block
orders of all occurring monomials. -/
def IsMultiHomogeneous {m n : ℕ} (P : MvPolynomial (BlockVar m n) ℚ)
    (d : Fin m → ℕ) : Prop :=
  ∀ ⦃J : MultiIndex m n⦄, MvPolynomial.coeff J P ≠ 0 →
    ∀ j : Fin m, blockOrder J j = d j

theorem IsMultiHomogeneous.of_mem_support {m n : ℕ}
    {P : MvPolynomial (BlockVar m n) ℚ} {d : Fin m → ℕ}
    (hP : IsMultiHomogeneous P d) {J : MultiIndex m n}
    (hJ : J ∈ P.support) (j : Fin m) : blockOrder J j = d j :=
  hP (MvPolynomial.mem_support_iff.mp hJ) j

/-- The finite set of weights of the nonzero Hasse coefficients. -/
def indexWeights {m n : ℕ} (P : MvPolynomial (BlockVar m n) ℚ)
    (d : Fin m → ℕ) (x : MultiPoint m n) : Finset ℚ :=
  (translate (flattenPoint x) P).support.image (normalizedWeight d)

/-- Roth's normalized index.  For the zero polynomial we use the harmless
totalized value `0`; all substantive theorems assume `P ≠ 0`. -/
def normalizedIndex {m n : ℕ} (P : MvPolynomial (BlockVar m n) ℚ)
    (d : Fin m → ℕ) (x : MultiPoint m n) : ℚ :=
  if h : (indexWeights P d x).Nonempty then (indexWeights P d x).min' h else 0

/-- A nonzero polynomial has a nonzero Hasse coefficient realizing its
normalized index. -/
theorem exists_blockHasseCoeff_weight_eq_index {m n : ℕ}
    {P : MvPolynomial (BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) (x : MultiPoint m n) :
    ∃ J : MultiIndex m n,
      blockHasseCoeff P x J ≠ 0 ∧
      normalizedWeight d J = normalizedIndex P d x := by
  have hsupp : (translate (flattenPoint x) P).support.Nonempty :=
    MvPolynomial.support_nonempty.mpr (translate_ne_zero hP)
  have hw : (indexWeights P d x).Nonempty := by
    exact hsupp.image _
  have hmin : (indexWeights P d x).min' hw ∈ indexWeights P d x :=
    Finset.min'_mem _ _
  obtain ⟨J, hJsupp, hJweight⟩ := Finset.mem_image.mp hmin
  refine ⟨J, MvPolynomial.mem_support_iff.mp hJsupp, ?_⟩
  rw [normalizedIndex, dif_pos hw]
  exact hJweight

/-- The index is no larger than the weight of any nonzero Hasse coefficient. -/
theorem normalizedIndex_le_weight {m n : ℕ}
    {P : MvPolynomial (BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) (x : MultiPoint m n) (J : MultiIndex m n)
    (hJ : blockHasseCoeff P x J ≠ 0) :
    normalizedIndex P d x ≤ normalizedWeight d J := by
  have hsupp : (translate (flattenPoint x) P).support.Nonempty :=
    MvPolynomial.support_nonempty.mpr (translate_ne_zero hP)
  have hw : (indexWeights P d x).Nonempty := hsupp.image _
  rw [normalizedIndex, dif_pos hw]
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨J, MvPolynomial.mem_support_iff.mpr hJ, rfl⟩

theorem normalizedIndex_nonneg {m n : ℕ}
    {P : MvPolynomial (BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) (x : MultiPoint m n) :
    0 ≤ normalizedIndex P d x := by
  obtain ⟨J, _, hw⟩ := exists_blockHasseCoeff_weight_eq_index hP d x
  rw [← hw]
  exact normalizedWeight_nonneg d J

/-- Nonvanishing at the point is equivalent to index zero in the forward
direction needed by applications. -/
theorem normalizedIndex_eq_zero_of_eval_ne_zero {m n : ℕ}
    {P : MvPolynomial (BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) (x : MultiPoint m n)
    (heval : MvPolynomial.eval (flattenPoint x) P ≠ 0) :
    normalizedIndex P d x = 0 := by
  apply le_antisymm
  · simpa using normalizedIndex_le_weight hP d x 0 (by simpa using heval)
  · exact normalizedIndex_nonneg hP d x

/-- Strict index bounds are exactly nonvanishing of a lower-weight Hasse
coefficient.  This is the form consumed after the quantitative Roth lemma. -/
theorem normalizedIndex_lt_iff_exists {m n : ℕ}
    {P : MvPolynomial (BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) (x : MultiPoint m n) (t : ℚ) :
    normalizedIndex P d x < t ↔
      ∃ J : MultiIndex m n,
        normalizedWeight d J < t ∧ blockHasseCoeff P x J ≠ 0 := by
  constructor
  · intro h
    obtain ⟨J, hJ, hw⟩ := exists_blockHasseCoeff_weight_eq_index hP d x
    exact ⟨J, hw.trans_lt h, hJ⟩
  · rintro ⟨J, hw, hJ⟩
    exact (normalizedIndex_le_weight hP d x J hJ).trans_lt hw

/-- The reusable lower-index conclusion: any quantitative upper bound for
Roth's index produces an explicit lower-weight nonvanishing Hasse
coefficient. -/
theorem exists_nonzero_lowerIndex_of_bound {m n : ℕ}
    {P : MvPolynomial (BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) (x : MultiPoint m n) {B t : ℚ}
    (hindex : normalizedIndex P d x ≤ B) (hBt : B < t) :
    ∃ J : MultiIndex m n,
      normalizedWeight d J < t ∧ blockHasseCoeff P x J ≠ 0 := by
  exact (normalizedIndex_lt_iff_exists hP d x t).mp (hindex.trans_lt hBt)

/-- Real-valued wrapper used by logarithmic-height estimates. -/
def normalizedIndexReal {m n : ℕ}
    (P : MvPolynomial (BlockVar m n) ℚ) (d : Fin m → ℕ)
    (x : MultiPoint m n) : ℝ := normalizedIndex P d x

/-- Real-valued normalized multi-index weight. -/
def normalizedWeightReal {m n : ℕ} (d : Fin m → ℕ)
    (J : MultiIndex m n) : ℝ := normalizedWeight d J

/-- A strict real index bound produces a nonvanishing Hasse coefficient of
strictly smaller real weight. -/
theorem normalizedIndexReal_lt_iff_exists {m n : ℕ}
    {P : MvPolynomial (BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) (x : MultiPoint m n) (t : ℚ) :
    normalizedIndexReal P d x < (t : ℝ) ↔
      ∃ J : MultiIndex m n,
        normalizedWeightReal d J < (t : ℝ) ∧ blockHasseCoeff P x J ≠ 0 := by
  simpa only [normalizedIndexReal, normalizedWeightReal, Rat.cast_lt] using
    (normalizedIndex_lt_iff_exists hP d x t)

theorem exists_nonzero_lowerIndex_of_real_bound {m n : ℕ}
    {P : MvPolynomial (BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) (x : MultiPoint m n) {B : ℝ} {t : ℚ}
    (hindex : normalizedIndexReal P d x ≤ B) (hBt : B < (t : ℝ)) :
    ∃ J : MultiIndex m n,
      normalizedWeightReal d J < (t : ℝ) ∧ blockHasseCoeff P x J ≠ 0 := by
  exact (normalizedIndexReal_lt_iff_exists hP d x t).mp (hindex.trans_lt hBt)

/-- All Hasse coefficients of normalized weight strictly below `t` vanish. -/
def VanishesBelow {m n : ℕ} (P : MvPolynomial (BlockVar m n) ℚ)
    (d : Fin m → ℕ) (x : MultiPoint m n) (t : ℚ) : Prop :=
  ∀ J : MultiIndex m n,
    normalizedWeight d J < t → blockHasseCoeff P x J = 0

/-- The finite-support definition of index agrees exactly with the usual
vanishing-threshold formulation. -/
theorem vanishesBelow_iff_le_normalizedIndex {m n : ℕ}
    {P : MvPolynomial (BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) (x : MultiPoint m n) (t : ℚ) :
    VanishesBelow P d x t ↔ t ≤ normalizedIndex P d x := by
  constructor
  · intro hvan
    obtain ⟨J, hJ, hw⟩ := exists_blockHasseCoeff_weight_eq_index hP d x
    apply le_of_not_gt
    intro hlt
    exact hJ (hvan J (hw.trans_lt hlt))
  · intro hle J hweight
    by_contra hJ
    have hindex := normalizedIndex_le_weight hP d x J hJ
    exact (not_lt_of_ge (hle.trans hindex)) hweight

theorem not_vanishesBelow_iff_exists {m n : ℕ}
    (P : MvPolynomial (BlockVar m n) ℚ) (d : Fin m → ℕ)
    (x : MultiPoint m n) (t : ℚ) :
    ¬ VanishesBelow P d x t ↔
      ∃ J : MultiIndex m n,
        normalizedWeight d J < t ∧ blockHasseCoeff P x J ≠ 0 := by
  unfold VanishesBelow
  constructor <;> intro h
  · push Not at h
    exact h
  · push Not
    exact h

/-! ## The rational one-variable Roth height bound -/

/-- The logarithmic Mahler height of an integral polynomial.  For a primitive
linear polynomial this is exactly the usual logarithmic projective height of
its two coefficients. -/
def mahlerHeight (P : Polynomial ℤ) : ℝ :=
  (P.map (Int.castRingHom ℂ)).logMahlerMeasure

/-- Integral linear polynomial with coefficient pair `(a,b)`. -/
def integerLinearPolynomial (a b : ℤ) : Polynomial ℤ :=
  Polynomial.C a * Polynomial.X + Polynomial.C b

/-- For a genuine linear polynomial, Mahler height is the logarithm of the
maximum norm of its coefficient pair, hence the standard projective height
for primitive `(a,b)`. -/
theorem mahlerHeight_integerLinearPolynomial {a b : ℤ} (ha : a ≠ 0) :
    mahlerHeight (integerLinearPolynomial a b) =
      Real.log (max ‖(a : ℂ)‖ ‖(b : ℂ)‖) := by
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  rw [mahlerHeight, Polynomial.logMahlerMeasure_eq_log_MahlerMeasure]
  simp only [integerLinearPolynomial, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X]
  change Real.log
    (Polynomial.C (a : ℂ) * Polynomial.X + Polynomial.C (b : ℂ)).mahlerMeasure = _
  rw [Polynomial.mahlerMeasure_C_mul_X_add_C haC]

theorem mahlerHeight_nonneg {P : Polynomial ℤ} (hP : P ≠ 0) :
    0 ≤ mahlerHeight P := by
  rw [mahlerHeight, Polynomial.logMahlerMeasure_eq_log_MahlerMeasure]
  exact Real.log_nonneg (Polynomial.one_le_mahlerMeasure_of_ne_zero hP)

/-- A power of a nonconstant primitive linear factor consumes the same
multiple of its projective height.  This is the arithmetic heart of the
`m = 1` case of Roth's lemma. -/
theorem nat_mul_mahlerHeight_le_of_pow_dvd
    {L P : Polynomial ℤ} {e : ℕ} (hL : L ≠ 0) (hP : P ≠ 0)
    (hdiv : L ^ e ∣ P) :
    (e : ℝ) * mahlerHeight L ≤ mahlerHeight P := by
  obtain ⟨Q, hQeq⟩ := hdiv
  have hQ : Q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hQeq
    exact hP hQeq
  let LC : Polynomial ℂ := L.map (Int.castRingHom ℂ)
  let QC : Polynomial ℂ := Q.map (Int.castRingHom ℂ)
  have hLC : LC ≠ 0 := by
    intro hzero
    apply hL
    exact (Polynomial.map_injective (f := Int.castRingHom ℂ)
      Int.cast_injective) (by simpa [LC] using hzero)
  have hQC : QC ≠ 0 := by
    intro hzero
    apply hQ
    exact (Polynomial.map_injective (f := Int.castRingHom ℂ)
      Int.cast_injective) (by simpa [QC] using hzero)
  have hprod : LC ^ e * QC ≠ 0 := mul_ne_zero (pow_ne_zero _ hLC) hQC
  have log_pow : ∀ k : ℕ, (LC ^ k).logMahlerMeasure =
      (k : ℝ) * LC.logMahlerMeasure := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ,
          Polynomial.logMahlerMeasure_mul_eq_add_logMahlerMeasure
            (mul_ne_zero (pow_ne_zero _ hLC) hLC), ih]
        push_cast
        ring
  have hpow := log_pow e
  have hadd : (LC ^ e * QC).logMahlerMeasure =
      (e : ℝ) * LC.logMahlerMeasure + QC.logMahlerMeasure := by
    rw [Polynomial.logMahlerMeasure_mul_eq_add_logMahlerMeasure hprod]
    exact congrArg (fun z ↦ z + QC.logMahlerMeasure) hpow
  have hQCnonneg : 0 ≤ QC.logMahlerMeasure := by
    rw [Polynomial.logMahlerMeasure_eq_log_MahlerMeasure]
    exact Real.log_nonneg (Polynomial.one_le_mahlerMeasure_of_ne_zero hQ)
  change (e : ℝ) * LC.logMahlerMeasure ≤
    (P.map (Int.castRingHom ℂ)).logMahlerMeasure
  rw [hQeq, Polynomial.map_mul, Polynomial.map_pow]
  change (e : ℝ) * LC.logMahlerMeasure ≤ (LC ^ e * QC).logMahlerMeasure
  rw [hadd]
  linarith

/-- Quantitative one-variable Roth lemma over `ℚ`, in its factor form.  If
the Mahler height of `P` is at most `η r` times the height of a rational
linear factor, that factor cannot occur with normalized multiplicity more
than `η`. -/
theorem oneVariable_roth_bound
    {L P : Polynomial ℤ} {e r : ℕ} {η : ℝ}
    (hL : L ≠ 0) (hP : P ≠ 0) (hr : 0 < r)
    (hLheight : 0 < mahlerHeight L) (hdiv : L ^ e ∣ P)
    (hheight : mahlerHeight P ≤ η * (r : ℝ) * mahlerHeight L) :
    (e : ℝ) / (r : ℝ) ≤ η := by
  have hfactor := nat_mul_mahlerHeight_le_of_pow_dvd hL hP hdiv
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  apply (div_le_iff₀ hrR).2
  nlinarith

end
end Erdos407.RothIndex
