import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.MvPolynomial
import Mathlib.NumberTheory.SiegelsLemma
import Mathlib.RingTheory.Trace.Basic

/-!
# Elementary zero estimates for linear forms in exponentials

This file contains the algebraic zero-estimate layer used by the
auxiliary-function proof of the fixed-rank logarithmic-form estimate needed
for Erdős Problem 841.  The first results are the ordinary Vandermonde case:
an exponential sum with `r` distinct bases cannot vanish at each of the first
`r` nonnegative integers unless all of its coefficients vanish.

No transcendence input is used here.  Keeping these lemmas separate makes it
possible to reuse them when the auxiliary function is differentiated and the
ordinary Vandermonde system is replaced by its confluent analogue.
-/

open scoped BigOperators Topology

namespace Erdos841.LinearForms

noncomputable section

open Finset Set Filter

attribute [local instance] Matrix.seminormedAddCommGroup

/-! ## A coefficientwise form of Siegel's lemma -/

/-- An underdetermined integral matrix has a nonzero integral kernel vector
whose individual coefficients satisfy the explicit sup-norm bound from
Siegel's lemma.  This wrapper records the ceiling as a natural number, the
form needed by the height estimate for an auxiliary exponential sum. -/
theorem exists_bounded_nonzero_integer_kernel
    {rows cols : Type*} [Fintype rows] [Fintype cols]
    (A : Matrix rows cols ℤ)
    (hcard : Fintype.card rows < Fintype.card cols)
    (hrows : 0 < Fintype.card rows) :
    ∃ c : cols → ℤ, c ≠ 0 ∧ A.mulVec c = 0 ∧
      ∀ j, (c j).natAbs ≤ Nat.ceil
        (((Fintype.card cols : ℝ) * max 1 ‖A‖) ^
          ((Fintype.card rows : ℝ) /
            ((Fintype.card cols : ℝ) - Fintype.card rows))) := by
  obtain ⟨c, hc, hker, hnorm⟩ :=
    Int.Matrix.exists_ne_zero_int_vec_norm_le A hcard hrows
  refine ⟨c, hc, hker, fun j ↦ ?_⟩
  let R : ℝ :=
    ((Fintype.card cols : ℝ) * max 1 ‖A‖) ^
      ((Fintype.card rows : ℝ) /
        ((Fintype.card cols : ℝ) - Fintype.card rows))
  have happly : ‖c j‖ ≤ ‖c‖ := by
    rw [Pi.norm_def]
    exact_mod_cast (Finset.le_sup (s := Finset.univ)
      (f := fun b : cols ↦ ‖c b‖₊) (Finset.mem_univ j))
  have hj : ‖c j‖ ≤ R := happly.trans hnorm
  have hceil : R ≤ Nat.ceil R := Nat.le_ceil R
  have hreal : ((c j).natAbs : ℝ) ≤ (Nat.ceil R : ℝ) := by
    simpa [Int.norm_eq_abs] using hj.trans hceil
  change (c j).natAbs ≤ Nat.ceil R
  exact_mod_cast hreal

/-! ### Clearing algebraic entries by one integral scale -/

/-- A finite family of number-field elements of logarithmic height at most
`H` admits one common positive integral scale.  The scale is at most the
product of the individual multiplicative heights, hence at most
`exp(H)^card κ`. -/
theorem exists_common_integral_scale
    {K κ : Type*} [Field K] [NumberField K] [Fintype κ]
    (x : κ → K) {H : ℝ} (hx : ∀ i, Height.logHeight₁ (x i) ≤ H) :
    ∃ Q : ℕ, Q ≠ 0 ∧
      (Q : ℝ) ≤ Real.exp H ^ Fintype.card κ ∧
      ∀ i, IsIntegral ℤ ((Q : K) * x i) := by
  classical
  choose q hq0 hqle hqint using
    fun i ↦ NumberField.exists_nat_le_mulHeight₁ (x i)
  let Q : ℕ := ∏ i, q i
  have hqexp : ∀ i, (q i : ℝ) ≤ Real.exp H := by
    intro i
    calc
      (q i : ℝ) ≤ Height.mulHeight₁ (x i) := hqle i
      _ = Real.exp (Height.logHeight₁ (x i)) := by
        rw [Height.logHeight₁_eq_log_mulHeight₁,
          Real.exp_log (Height.mulHeight₁_pos (x i))]
      _ ≤ Real.exp H := Real.exp_le_exp.mpr (hx i)
  have hQ0 : Q ≠ 0 := by
    dsimp [Q]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ hq0 i
  refine ⟨Q, hQ0, ?_, fun i ↦ ?_⟩
  · dsimp [Q]
    push_cast
    calc
      ∏ i, (q i : ℝ) ≤ ∏ _i : κ, Real.exp H := by
        exact Finset.prod_le_prod (fun _ _ ↦ by positivity)
          (fun i _ ↦ hqexp i)
      _ = Real.exp H ^ Fintype.card κ := by simp
  · have hdiv : q i ∣ Q := by
      dsimp [Q]
      exact Finset.dvd_prod_of_mem (fun j ↦ q j) (Finset.mem_univ i)
    obtain ⟨r, hr⟩ := hdiv
    have heq : (Q : K) * x i = (r : K) * ((q i : K) * x i) := by
      rw [hr]
      push_cast
      ring
    rw [heq]
    exact (isIntegral_natCast (R := ℤ) (B := K) r).mul (hqint i)

/-- Integral trace coordinates for a number-field matrix after clearing all
its entries by one common scale.  Testing against an integral rational basis
turns every algebraic row equation into ordinary integer equations. -/
def traceConstraintMatrix
    {K rows cols ι : Type*} [Field K] [NumberField K]
    [Fintype cols]
    (b : Module.Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i))
    (A : Matrix rows cols K) (Q : ℕ)
    (hQA : ∀ r j, IsIntegral ℤ ((Q : K) * A r j)) :
    Matrix (rows × ι) cols ℤ :=
  fun ri j ↦ Algebra.trace ℤ (NumberField.RingOfIntegers K)
    (⟨(Q : K) * A ri.1 j, hQA ri.1 j⟩ * ⟨b ri.2, hb ri.2⟩)

/-- A vector in the integral trace-coordinate kernel is already in the
original number-field kernel.  Nondegeneracy of the trace pairing is the
only algebraic input. -/
lemma traceConstraintMatrix_kernel
    {K rows cols ι : Type*} [Field K] [NumberField K]
    [Fintype cols] [Fintype ι]
    (b : Module.Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i))
    (A : Matrix rows cols K) (Q : ℕ) (hQ : Q ≠ 0)
    (hQA : ∀ r j, IsIntegral ℤ ((Q : K) * A r j))
    (c : cols → ℤ)
    (hc : (traceConstraintMatrix b hb A Q hQA).mulVec c = 0) :
    A.mulVec (fun j ↦ (c j : K)) = 0 := by
  funext r
  let y : K := ∑ j, (c j : K) * A r j
  have htrace : ∀ i, Algebra.trace ℚ K ((Q : K) * y * b i) = 0 := by
    intro i
    have hi := congrFun hc (r, i)
    change ∑ j, traceConstraintMatrix b hb A Q hQA (r, i) j * c j = 0 at hi
    have hiQ := congrArg (fun z : ℤ ↦ (z : ℚ)) hi
    rw [Int.cast_sum] at hiQ
    simp only [Int.cast_mul, Int.cast_zero] at hiQ
    have hterm : ∀ j,
        ((traceConstraintMatrix b hb A Q hQA (r, i) j : ℤ) : ℚ) =
          Algebra.trace ℚ K (((Q : K) * A r j) * b i) := by
      intro j
      exact Algebra.coe_trace_int
        (⟨(Q : K) * A r j, hQA r j⟩ * ⟨b i, hb i⟩)
    simp_rw [hterm] at hiQ
    have heq : (Q : K) * y * b i =
        ∑ j, (c j : ℚ) • (((Q : K) * A r j) * b i) := by
      dsimp [y]
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Algebra.smul_def]
      norm_num
      ring
    rw [heq, map_sum]
    simpa [map_smul, mul_comm] using hiQ
  have hzero : (Q : K) * y = 0 := by
    apply (traceForm_nondegenerate ℚ K).1
    intro z
    rw [← b.sum_repr z]
    simp only [map_sum, Algebra.traceForm_apply,
      Algebra.smul_def, mul_assoc]
    apply Finset.sum_eq_zero
    intro i hi
    have heq : (Q : K) *
        (y * ((algebraMap ℚ K) ((b.repr z) i) * b i)) =
        ((b.repr z) i) • ((Q : K) * y * b i) := by
      simp only [Algebra.smul_def]
      ring
    rw [heq, map_smul]
    simp [htrace i]
  have hy : y = 0 := by
    exact (mul_eq_zero.mp hzero).resolve_left (Nat.cast_ne_zero.mpr hQ)
  simpa [Matrix.mulVec, dotProduct, mul_comm, y] using hy

/-- The integral moment matrix attached to a finite family of integer
vectors and a finite family of multi-indices. -/
def momentMatrix
    {kappa iota mu : Type*} [Fintype kappa] [Fintype iota]
    (v : kappa → iota → ℤ) (u : mu → iota → ℕ) :
    Matrix mu kappa ℤ :=
  fun p k ↦ ∏ i, v k i ^ u p i

/-- Siegel's lemma applied directly to an integral moment system.  The
returned vector is nonzero, annihilates every requested monomial moment,
and retains the coefficientwise quantitative bound. -/
theorem exists_bounded_nonzero_integer_moment_coefficients
    {kappa iota mu : Type*} [Fintype kappa] [Fintype iota] [Fintype mu]
    (v : kappa → iota → ℤ) (u : mu → iota → ℕ)
    (hcard : Fintype.card mu < Fintype.card kappa)
    (hmu : 0 < Fintype.card mu) :
    ∃ c : kappa → ℤ, c ≠ 0 ∧
      (∀ p, ∑ k, c k * ∏ i, v k i ^ u p i = 0) ∧
      ∀ k, (c k).natAbs ≤ Nat.ceil
        (((Fintype.card kappa : ℝ) *
            max 1 ‖momentMatrix v u‖) ^
          ((Fintype.card mu : ℝ) /
            ((Fintype.card kappa : ℝ) - Fintype.card mu))) := by
  obtain ⟨c, hc, hker, hbound⟩ :=
    exists_bounded_nonzero_integer_kernel (momentMatrix v u) hcard hmu
  refine ⟨c, hc, ?_, hbound⟩
  intro p
  have hp := congrFun hker p
  simpa [momentMatrix, Matrix.mulVec, dotProduct, mul_comm] using hp

/-- A uniform coordinate bound and a total-degree bound control the sup
norm of the integral moment matrix. -/
theorem momentMatrix_norm_le
    {kappa iota mu : Type*} [Fintype kappa] [Fintype iota] [Fintype mu]
    (v : kappa → iota → ℤ) (u : mu → iota → ℕ)
    {V : ℝ} {D : ℕ} (hV : 1 ≤ V)
    (hv : ∀ k i, ‖v k i‖ ≤ V)
    (hu : ∀ p, ∑ i, u p i ≤ D) :
    ‖momentMatrix v u‖ ≤ V ^ D := by
  rw [Matrix.norm_le_iff (pow_nonneg (by positivity) _)]
  intro p k
  rw [momentMatrix, norm_prod]
  calc
    ∏ i, ‖v k i ^ u p i‖ ≤ ∏ i, V ^ u p i := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hv k i) _
    _ = V ^ ∑ i, u p i := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ V ^ D := pow_le_pow_right₀ hV (hu p)

/-! ## Rectangular moment systems -/

/-- The row type for the rectangular system: one exponent below `T` for
the distinguished coordinate and one exponent below `S` for every
remaining coordinate. -/
abbrev RectangularMomentIndex (iota : Type*) (T S : ℕ) :=
  Fin T × (iota → Fin S)

/-- The integral rectangular moment matrix used in the auxiliary-function
construction. -/
def rectangularMomentMatrix
    {kappa iota : Type*} [Fintype kappa] [Fintype iota]
    (a : kappa → ℤ) (r : kappa → iota → ℤ) (T S : ℕ) :
    Matrix (RectangularMomentIndex iota T S) kappa ℤ :=
  fun qu k ↦ a k ^ (qu.1 : ℕ) * ∏ i, r k i ^ (qu.2 i : ℕ)

/-- If the exponent box has more columns than rectangular moment
conditions, Siegel's lemma supplies nonzero integral auxiliary
coefficients satisfying every moment needed below orders `T` and `S`. -/
theorem exists_rectangular_moment_coefficients
    {kappa iota : Type*} [Fintype kappa] [Fintype iota]
    [DecidableEq iota]
    (a : kappa → ℤ) (r : kappa → iota → ℤ) (T S : ℕ)
    (hT : 0 < T) (hS : 0 < S)
    (hcard : T * S ^ Fintype.card iota < Fintype.card kappa) :
    ∃ c : kappa → ℤ, c ≠ 0 ∧
      (∀ q, q < T → ∀ p, p < S →
        ∀ u ∈ Finset.piAntidiag (Finset.univ : Finset iota) p,
          ∑ k, c k * a k ^ q * ∏ i, r k i ^ u i = 0) ∧
      ∀ k, (c k).natAbs ≤ Nat.ceil
        (((Fintype.card kappa : ℝ) *
            max 1 ‖rectangularMomentMatrix a r T S‖) ^
          (((T * S ^ Fintype.card iota : ℕ) : ℝ) /
            ((Fintype.card kappa : ℝ) -
              (T * S ^ Fintype.card iota : ℕ)))) := by
  let rows := RectangularMomentIndex iota T S
  let A : Matrix rows kappa ℤ := rectangularMomentMatrix a r T S
  have hrowsCard : Fintype.card rows = T * S ^ Fintype.card iota := by
    simp [rows, RectangularMomentIndex]
  have hrowsPos : 0 < Fintype.card rows := by
    rw [hrowsCard]
    positivity
  have hcard' : Fintype.card rows < Fintype.card kappa := by
    simpa [hrowsCard] using hcard
  obtain ⟨c, hc, hker, hcBound⟩ :=
    exists_bounded_nonzero_integer_kernel A hcard' hrowsPos
  refine ⟨c, hc, ?_, ?_⟩
  · intro q hq p hp u hu
    have husum : ∑ i, u i = p := (Finset.mem_piAntidiag.mp hu).1
    have hui : ∀ i, u i < S := by
      intro i
      have hsingle : u i ≤ ∑ j, u j := by
        exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le (u j))
          (Finset.mem_univ i)
      omega
    let row : rows :=
      (⟨q, hq⟩, fun i ↦ ⟨u i, hui i⟩)
    have hrow := congrFun hker row
    simpa [A, rectangularMomentMatrix, Matrix.mulVec, dotProduct,
      row, mul_comm, mul_assoc] using hrow
  · intro k
    simpa [A, hrowsCard] using hcBound k

/-- Full rectangular form of `exists_rectangular_moment_coefficients`.
Unlike its total-degree interface, this theorem exposes every row of the
integral kernel matrix and is therefore the exact input expected by the
multipoint extrapolation lemmas. -/
theorem exists_rectangular_moment_coefficients_full
    {kappa iota : Type*} [Fintype kappa] [Fintype iota]
    [DecidableEq iota]
    (a : kappa → ℤ) (r : kappa → iota → ℤ) (T S : ℕ)
    (hT : 0 < T) (hS : 0 < S)
    (hcard : T * S ^ Fintype.card iota < Fintype.card kappa) :
    ∃ c : kappa → ℤ, c ≠ 0 ∧
      (∀ q : Fin T, ∀ u : iota → Fin S,
          ∑ k, c k * a k ^ (q : ℕ) *
            ∏ i, r k i ^ (u i : ℕ) = 0) ∧
      ∀ k, (c k).natAbs ≤ Nat.ceil
        (((Fintype.card kappa : ℝ) *
            max 1 ‖rectangularMomentMatrix a r T S‖) ^
          (((T * S ^ Fintype.card iota : ℕ) : ℝ) /
            ((Fintype.card kappa : ℝ) -
              (T * S ^ Fintype.card iota : ℕ)))) := by
  let rows := RectangularMomentIndex iota T S
  let A : Matrix rows kappa ℤ := rectangularMomentMatrix a r T S
  have hrowsCard : Fintype.card rows =
      T * S ^ Fintype.card iota := by
    simp [rows, RectangularMomentIndex]
  have hrowsPos : 0 < Fintype.card rows := by
    rw [hrowsCard]
    positivity
  have hcard' : Fintype.card rows < Fintype.card kappa := by
    simpa [hrowsCard] using hcard
  obtain ⟨c, hc, hker, hcBound⟩ :=
    exists_bounded_nonzero_integer_kernel A hcard' hrowsPos
  refine ⟨c, hc, ?_, ?_⟩
  · intro q u
    have hrow := congrFun hker (q, u)
    simpa [A, rectangularMomentMatrix, Matrix.mulVec, dotProduct,
      mul_comm, mul_assoc] using hrow
  · intro k
    simpa [A, hrowsCard] using hcBound k

/-- The rectangular moment matrix has an explicit sup-norm bound in terms
of a common coordinate majorant. -/
theorem rectangularMomentMatrix_norm_le
    {kappa iota : Type*} [Fintype kappa] [Fintype iota]
    [DecidableEq iota]
    (a : kappa → ℤ) (r : kappa → iota → ℤ) (T S : ℕ)
    {V : ℝ} (hV : 1 ≤ V)
    (ha : ∀ k, ‖a k‖ ≤ V) (hr : ∀ k i, ‖r k i‖ ≤ V) :
    ‖rectangularMomentMatrix a r T S‖ ≤
      V ^ (T + Fintype.card iota * S) := by
  rw [Matrix.norm_le_iff (pow_nonneg (by positivity) _)]
  intro qu k
  rw [rectangularMomentMatrix, norm_mul, norm_pow, norm_prod]
  calc
    ‖a k‖ ^ (qu.1 : ℕ) * ∏ i, ‖r k i ^ (qu.2 i : ℕ)‖ ≤
        V ^ (qu.1 : ℕ) * ∏ i, V ^ (qu.2 i : ℕ) := by
      gcongr
      · exact ha k
      · rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hr k i) _
    _ = V ^ ((qu.1 : ℕ) + ∑ i, (qu.2 i : ℕ)) := by
      rw [Finset.prod_pow_eq_pow_sum, pow_add]
    _ ≤ V ^ (T + Fintype.card iota * S) := by
      apply pow_le_pow_right₀ hV
      have hsum : ∑ i, (qu.2 i : ℕ) ≤ Fintype.card iota * S := by
        calc
          ∑ i, (qu.2 i : ℕ) ≤ ∑ _i : iota, S := by
            gcongr with i hi
            exact (qu.2 i).isLt.le
          _ = Fintype.card iota * S := by simp
      omega

/-! ## Exponent boxes and the distinguished change of variables -/

/-- The rectangular exponent box `[0,K)^n`. -/
abbrev ExponentBox (n K : ℕ) := Fin n → Fin K

/-- The logarithmic linear form associated with one exponent vector. -/
def boxLinearForm {n K : ℕ} (ell : Fin n → ℂ)
    (k : ExponentBox n K) : ℂ :=
  ∑ i, ((k i : ℕ) : ℂ) * ell i

/-- The exponent in the distinguished coordinate. -/
def boxDistinguishedExponent {r K : ℕ}
    (k : ExponentBox (r + 1) K) : ℤ :=
  (k 0 : ℕ)

/-- The integral transformed coordinates
`b₀ kᵢ - k₀ bᵢ` away from the distinguished coordinate. -/
def boxTransformedExponent {r K : ℕ} (b : Fin (r + 1) → ℤ)
    (k : ExponentBox (r + 1) K) (i : Fin r) : ℤ :=
  b 0 * (k i.succ : ℕ) - (k 0 : ℕ) * b i.succ

/-- Exact box-indexed form of the distinguished-coefficient identity. -/
theorem box_distinguished_linearForm_identity
    {r K : ℕ} (ell : Fin (r + 1) → ℂ) (b : Fin (r + 1) → ℤ)
    (k : ExponentBox (r + 1) K) :
    (b 0 : ℂ) * boxLinearForm ell k =
      (boxDistinguishedExponent k : ℂ) * ∑ i, (b i : ℂ) * ell i +
        ∑ i : Fin r,
          (boxTransformedExponent b k i : ℂ) * ell i.succ := by
  simp only [boxLinearForm, boxDistinguishedExponent, boxTransformedExponent]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  push_cast
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

lemma boxDistinguishedExponent_natAbs_lt
    {r K : ℕ} (k : ExponentBox (r + 1) K) :
    (boxDistinguishedExponent k).natAbs < K := by
  simp [boxDistinguishedExponent, (k 0).isLt]

lemma boxTransformedExponent_natAbs_le
    {r K B : ℕ} (b : Fin (r + 1) → ℤ)
    (hb : ∀ i, (b i).natAbs ≤ B)
    (k : ExponentBox (r + 1) K) (i : Fin r) :
    (boxTransformedExponent b k i).natAbs ≤ 2 * B * K := by
  rw [boxTransformedExponent]
  calc
    (b 0 * (k i.succ : ℕ) - (k 0 : ℕ) * b i.succ).natAbs ≤
        (b 0 * (k i.succ : ℕ)).natAbs +
          ((k 0 : ℕ) * b i.succ).natAbs := Int.natAbs_sub_le _ _
    _ = (b 0).natAbs * (k i.succ : ℕ) +
          (k 0 : ℕ) * (b i.succ).natAbs := by
      simp [Int.natAbs_mul]
    _ ≤ B * K + K * B := by
      gcongr
      · exact hb 0
      · exact (k i.succ).isLt.le
      · exact (k 0).isLt.le
      · exact hb i.succ
    _ = 2 * B * K := by ring

lemma boxDistinguishedExponent_norm_le
    {r K : ℕ} (k : ExponentBox (r + 1) K) :
    ‖boxDistinguishedExponent k‖ ≤ (K : ℝ) := by
  rw [Int.norm_eq_abs, ← Int.cast_abs, ← Int.natCast_natAbs]
  exact_mod_cast (boxDistinguishedExponent_natAbs_lt k).le

lemma boxTransformedExponent_norm_le
    {r K B : ℕ} (b : Fin (r + 1) → ℤ)
    (hb : ∀ i, (b i).natAbs ≤ B)
    (k : ExponentBox (r + 1) K) (i : Fin r) :
    ‖boxTransformedExponent b k i‖ ≤ (2 * B * K : ℕ) := by
  rw [Int.norm_eq_abs, ← Int.cast_abs, ← Int.natCast_natAbs]
  exact_mod_cast boxTransformedExponent_natAbs_le b hb k i

/-! ## Algebraic monomials indexed by an exponent box -/

/-- The algebraic monomial represented by an exponent vector. -/
def boxMonomial {G : Type*} [CommMonoid G] {n K : ℕ}
    (alpha : Fin n → G) (k : ExponentBox n K) : G :=
  ∏ i, alpha i ^ (k i : ℕ)

lemma boxMonomial_ne_zero
    {F : Type*} [Field F] {n K : ℕ} (alpha : Fin n → F)
    (halpha : ∀ i, alpha i ≠ 0) (k : ExponentBox n K) :
    boxMonomial alpha k ≠ 0 := by
  rw [boxMonomial]
  exact Finset.prod_ne_zero_iff.mpr fun i hi ↦ pow_ne_zero _ (halpha i)

/-- Every box monomial has height at most `K` times the sum of the input
heights. -/
lemma logHeight₁_boxMonomial_le
    {F : Type*} [Field F] [NumberField F] {n K : ℕ}
    (alpha : Fin n → F) (k : ExponentBox n K) :
    Height.logHeight₁ (boxMonomial alpha k) ≤
      (K : ℝ) * ∑ i, Height.logHeight₁ (alpha i) := by
  calc
    Height.logHeight₁ (boxMonomial alpha k) ≤
        ∑ i, Height.logHeight₁ (alpha i ^ (k i : ℕ)) := by
      rw [boxMonomial]
      exact Height.logHeight₁_prod_le Finset.univ _
    _ = ∑ i, (k i : ℕ) * Height.logHeight₁ (alpha i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Height.logHeight₁_pow]
    _ ≤ ∑ i, (K : ℝ) * Height.logHeight₁ (alpha i) := by
      gcongr with i hi
      exact_mod_cast (k i).isLt.le
    _ = (K : ℝ) * ∑ i, Height.logHeight₁ (alpha i) := by
      rw [Finset.mul_sum]

/-- Exponentiating the box linear form of principal logarithms recovers
the corresponding algebraic monomial. -/
lemma exp_boxLinearForm_log
    {n K : ℕ} (alpha : Fin n → ℂ) (halpha : ∀ i, alpha i ≠ 0)
    (k : ExponentBox n K) :
    Complex.exp (boxLinearForm (fun i ↦ Complex.log (alpha i)) k) =
      boxMonomial alpha k := by
  rw [boxLinearForm, Complex.exp_sum, boxMonomial]
  apply Finset.prod_congr rfl
  intro i hi
  calc
    Complex.exp (((k i : ℕ) : ℂ) * Complex.log (alpha i)) =
        Complex.exp (Complex.log (alpha i)) ^ (k i : ℕ) :=
      Complex.exp_nat_mul _ _
    _ = alpha i ^ (k i : ℕ) := by
      rw [Complex.exp_log (halpha i)]

lemma map_boxMonomial
    {F E : Type*} [CommMonoid F] [CommMonoid E] (phi : F →* E)
    {n K : ℕ} (alpha : Fin n → F) (k : ExponentBox n K) :
    phi (boxMonomial alpha k) =
      boxMonomial (fun i ↦ phi (alpha i)) k := by
  simp [boxMonomial]

lemma boxLinearForm_norm_le
    {n K : ℕ} (ell : Fin n → ℂ) (k : ExponentBox n K) :
    ‖boxLinearForm ell k‖ ≤ (K : ℝ) * ∑ i, ‖ell i‖ := by
  rw [boxLinearForm]
  calc
    ‖∑ i, ((k i : ℕ) : ℂ) * ell i‖ ≤
        ∑ i, ‖((k i : ℕ) : ℂ) * ell i‖ := norm_sum_le _ _
    _ = ∑ i, ((k i : ℕ) : ℝ) * ‖ell i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul, norm_natCast]
    _ ≤ ∑ i, (K : ℝ) * ‖ell i‖ := by
      gcongr with i hi
      exact_mod_cast (k i).isLt.le
    _ = (K : ℝ) * ∑ i, ‖ell i‖ := by
      rw [Finset.mul_sum]

lemma boxTransformedLinearForm_norm_le
    {r K B : ℕ} (ell : Fin r → ℂ) (b : Fin (r + 1) → ℤ)
    (hb : ∀ i, (b i).natAbs ≤ B) (k : ExponentBox (r + 1) K) :
    ‖∑ i, (boxTransformedExponent b k i : ℂ) * ell i‖ ≤
      (2 * B * K : ℕ) * ∑ i, ‖ell i‖ := by
  calc
    ‖∑ i, (boxTransformedExponent b k i : ℂ) * ell i‖ ≤
        ∑ i, ‖(boxTransformedExponent b k i : ℂ) * ell i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, ((2 * B * K : ℕ) : ℝ) * ‖ell i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_intCast]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa [Int.norm_eq_abs] using boxTransformedExponent_norm_le b hb k i
    _ = ((2 * B * K : ℕ) : ℝ) * ∑ i, ‖ell i‖ := by
      rw [Finset.mul_sum]

/-- Siegel coefficients for the distinguished rectangular moments over a
full exponent box. -/
theorem exists_box_rectangular_moment_coefficients
    {r K B T S : ℕ} (b : Fin (r + 1) → ℤ)
    (_hb : ∀ i, (b i).natAbs ≤ B)
    (hT : 0 < T) (hS : 0 < S)
    (hcard : T * S ^ r < K ^ (r + 1)) :
    ∃ c : ExponentBox (r + 1) K → ℤ, c ≠ 0 ∧
      (∀ q, q < T → ∀ p, p < S →
        ∀ u ∈ Finset.piAntidiag (Finset.univ : Finset (Fin r)) p,
          ∑ k, c k * boxDistinguishedExponent k ^ q *
            ∏ i, boxTransformedExponent b k i ^ u i = 0) ∧
      ∀ k, (c k).natAbs ≤ Nat.ceil
        ((((K ^ (r + 1) : ℕ) : ℝ) * max 1
            ‖rectangularMomentMatrix
              (fun k : ExponentBox (r + 1) K ↦ boxDistinguishedExponent k)
              (fun (k : ExponentBox (r + 1) K) (i : Fin r) ↦
                boxTransformedExponent b k i) T S‖) ^
          (((T * S ^ r : ℕ) : ℝ) /
            (((K ^ (r + 1) : ℕ) : ℝ) -
              ((T * S ^ r : ℕ) : ℝ)))) := by
  simpa [ExponentBox] using
    (exists_rectangular_moment_coefficients
      (a := fun k : ExponentBox (r + 1) K ↦ boxDistinguishedExponent k)
      (r := fun k i ↦ boxTransformedExponent b k i)
      T S hT hS (by simpa [ExponentBox] using hcard))

/-- Full rectangular Siegel kernel over an exponent box.  Its coefficient
bound is identical to the total-degree wrapper, but it retains every
coordinatewise moment used by exact and approximate propagation. -/
theorem exists_box_rectangular_moment_coefficients_full
    {r K B T S : ℕ} (b : Fin (r + 1) → ℤ)
    (_hb : ∀ i, (b i).natAbs ≤ B)
    (hT : 0 < T) (hS : 0 < S)
    (hcard : T * S ^ r < K ^ (r + 1)) :
    ∃ c : ExponentBox (r + 1) K → ℤ, c ≠ 0 ∧
      (∀ q : Fin T, ∀ u : Fin r → Fin S,
        ∑ k, c k * boxDistinguishedExponent k ^ (q : ℕ) *
          ∏ i, boxTransformedExponent b k i ^ (u i : ℕ) = 0) ∧
      ∀ k, (c k).natAbs ≤ Nat.ceil
        ((((K ^ (r + 1) : ℕ) : ℝ) * max 1
            ‖rectangularMomentMatrix
              (fun k : ExponentBox (r + 1) K ↦ boxDistinguishedExponent k)
              (fun (k : ExponentBox (r + 1) K) (i : Fin r) ↦
                boxTransformedExponent b k i) T S‖) ^
          (((T * S ^ r : ℕ) : ℝ) /
            (((K ^ (r + 1) : ℕ) : ℝ) -
              ((T * S ^ r : ℕ) : ℝ)))) := by
  simpa [ExponentBox] using
    (exists_rectangular_moment_coefficients_full
      (a := fun k : ExponentBox (r + 1) K ↦ boxDistinguishedExponent k)
      (r := fun k i ↦ boxTransformedExponent b k i)
      T S hT hS (by simpa [ExponentBox] using hcard))

/-- A common integral bound for the distinguished and transformed box
coordinates. -/
def boxMomentCoordinateBound (B K : ℕ) : ℕ := max K (2 * B * K)

lemma one_le_boxMomentCoordinateBound {B K : ℕ} (hK : 0 < K) :
    1 ≤ boxMomentCoordinateBound B K := by
  exact (Nat.one_le_iff_ne_zero.mpr hK.ne').trans (le_max_left _ _)

/-- Fully explicit norm bound for the moment matrix attached to the
distinguished coefficient vector. -/
theorem box_rectangularMomentMatrix_norm_le
    {r K B T S : ℕ} (b : Fin (r + 1) → ℤ)
    (hb : ∀ i, (b i).natAbs ≤ B) (hK : 0 < K) :
    ‖rectangularMomentMatrix
        (fun k : ExponentBox (r + 1) K ↦ boxDistinguishedExponent k)
        (fun k i ↦ boxTransformedExponent b k i) T S‖ ≤
      (boxMomentCoordinateBound B K : ℝ) ^ (T + r * S) := by
  have h := rectangularMomentMatrix_norm_le
      (a := fun k : ExponentBox (r + 1) K ↦ boxDistinguishedExponent k)
      (r := fun (k : ExponentBox (r + 1) K) (i : Fin r) ↦
        boxTransformedExponent b k i) T S
      (V := (boxMomentCoordinateBound B K : ℕ))
      (by exact_mod_cast one_le_boxMomentCoordinateBound hK)
      (by
        intro k
        exact (boxDistinguishedExponent_norm_le k).trans (by
          exact_mod_cast (le_max_left K (2 * B * K))))
      (by
        intro k i
        exact (boxTransformedExponent_norm_le b hb k i).trans (by
          exact_mod_cast (le_max_right K (2 * B * K))))
  simpa using h

/-- The ordinary Vandermonde zero estimate for an exponential sum. -/
theorem exponentialSum_coefficients_eq_zero
    {K : Type*} [CommRing K] [IsDomain K] {r : ℕ}
    (alpha coeff : Fin r → K) (halpha : Function.Injective alpha)
    (hzero : ∀ k : Fin r,
      ∑ i : Fin r, coeff i * alpha i ^ (k : ℕ) = 0) :
    coeff = 0 := by
  exact Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero halpha hzero

/-- Natural-index form of `exponentialSum_coefficients_eq_zero`. -/
theorem exponentialSum_coefficients_eq_zero_of_lt
    {K : Type*} [CommRing K] [IsDomain K] {r : ℕ}
    (alpha coeff : Fin r → K) (halpha : Function.Injective alpha)
    (hzero : ∀ k : ℕ, k < r →
      ∑ i : Fin r, coeff i * alpha i ^ k = 0) :
    coeff = 0 := by
  apply exponentialSum_coefficients_eq_zero alpha coeff halpha
  intro k
  exact hzero k k.isLt

/-- A nonzero exponential sum with `r` distinct bases has a nonzero value
among the first `r` nonnegative integers. -/
theorem exists_exponentialSum_ne_zero
    {K : Type*} [CommRing K] [IsDomain K] {r : ℕ}
    (alpha coeff : Fin r → K) (halpha : Function.Injective alpha)
    (hcoeff : coeff ≠ 0) :
    ∃ k : Fin r, ∑ i : Fin r, coeff i * alpha i ^ (k : ℕ) ≠ 0 := by
  by_contra h
  push Not at h
  exact hcoeff (exponentialSum_coefficients_eq_zero alpha coeff halpha h)

/-- The ordinary zero estimate with an arbitrary finite indexing type.
The returned sample still lies among the first `card κ` nonnegative
integers; this form avoids choosing a global numbering of an exponent box. -/
theorem exists_finite_exponentialSum_ne_zero
    {R κ : Type*} [CommRing R] [IsDomain R]
    [Fintype κ] [DecidableEq κ]
    (alpha coeff : κ → R) (halpha : Function.Injective alpha)
    (hcoeff : coeff ≠ 0) :
    ∃ t : Fin (Fintype.card κ),
      ∑ k, coeff k * alpha k ^ (t : ℕ) ≠ 0 := by
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let alpha' : Fin (Fintype.card κ) → R := fun i ↦ alpha (e.symm i)
  let coeff' : Fin (Fintype.card κ) → R := fun i ↦ coeff (e.symm i)
  have halpha' : Function.Injective alpha' := by
    intro i j hij
    apply e.symm.injective
    exact halpha hij
  have hcoeff' : coeff' ≠ 0 := by
    intro hzero
    apply hcoeff
    funext k
    have hk := congrFun hzero (e k)
    simpa [coeff', e] using hk
  obtain ⟨t, ht⟩ :=
    exists_exponentialSum_ne_zero alpha' coeff' halpha' hcoeff'
  refine ⟨t, ?_⟩
  contrapose! ht
  change (∑ i, coeff (e.symm i) * alpha (e.symm i) ^ (t : ℕ)) = 0
  rw [e.symm.sum_comp (fun k ↦ coeff k * alpha k ^ (t : ℕ))]
  exact ht

/-- Integral quantitative form of the ordinary zero estimate.  Integrality
turns nonvanishing into the sharp elementary lower bound `1`. -/
theorem exists_one_le_abs_exponentialSum
    {r : ℕ} (alpha coeff : Fin r → ℤ)
    (halpha : Function.Injective alpha) (hcoeff : coeff ≠ 0) :
    ∃ k : Fin r,
      (1 : ℤ) ≤ |∑ i : Fin r, coeff i * alpha i ^ (k : ℕ)| := by
  obtain ⟨k, hk⟩ :=
    exists_exponentialSum_ne_zero alpha coeff halpha hcoeff
  exact ⟨k, Int.one_le_abs hk⟩

/-- The same integral estimate stated with `Int.natAbs`, which is the form
used by coefficient-height calculations. -/
theorem exists_one_le_natAbs_exponentialSum
    {r : ℕ} (alpha coeff : Fin r → ℤ)
    (halpha : Function.Injective alpha) (hcoeff : coeff ≠ 0) :
    ∃ k : Fin r,
      1 ≤ Int.natAbs (∑ i : Fin r, coeff i * alpha i ^ (k : ℕ)) := by
  obtain ⟨k, hk⟩ :=
    exists_exponentialSum_ne_zero alpha coeff halpha hcoeff
  exact ⟨k, Int.natAbs_pos.mpr hk⟩

/-! ## The confluent zero estimate -/

/-- A polynomial of degree below `(#ι) * multiplicity` which vanishes,
together with its first `multiplicity - 1` derivatives, at `#ι` distinct
points is zero.  This is the kernel statement for the confluent
Vandermonde matrix.

The proof deliberately goes through root multiplicities: each evaluation
point contributes at least `multiplicity` roots, counted with multiplicity,
whereas a nonzero polynomial has at most `natDegree` roots. -/
theorem polynomial_eq_zero_of_iterateDerivative_vanishes
    {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    {ι : Type*} [Fintype ι] (alpha : ι → K)
    (halpha : Function.Injective alpha) {multiplicity : ℕ}
    {P : Polynomial K}
    (hdegree : P.natDegree < Fintype.card ι * multiplicity)
    (hvanish : ∀ i : ι, ∀ j : ℕ, j < multiplicity →
      ((Polynomial.derivative^[j]) P).eval (alpha i) = 0) :
    P = 0 := by
  classical
  by_contra hP
  have hm : 0 < multiplicity := by
    by_contra hm
    have : multiplicity = 0 := Nat.eq_zero_of_not_pos hm
    simp [this] at hdegree
  let s : Finset K := Finset.univ.image alpha
  have hmult : ∀ i : ι, multiplicity ≤ P.rootMultiplicity (alpha i) := by
    intro i
    have hlt : multiplicity - 1 < P.rootMultiplicity (alpha i) := by
      apply Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative hP
      intro j hj
      rw [Polynomial.IsRoot]
      apply hvanish i j
      omega
    omega
  have hsroots : s ⊆ P.roots.toFinset := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset]
    exact Multiset.count_pos.mp <| by
      rw [Polynomial.count_roots]
      exact lt_of_lt_of_le hm (hmult i)
  have hlow : s.card * multiplicity ≤
      ∑ x ∈ s, P.roots.count x := by
    calc
      s.card * multiplicity = ∑ _x ∈ s, multiplicity := by simp
      _ ≤ ∑ x ∈ s, P.roots.count x := by
        exact Finset.sum_le_sum fun x hx ↦ by
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
          simpa only [Polynomial.count_roots] using hmult i
  have hupp : (∑ x ∈ s, P.roots.count x) ≤ P.roots.card := by
    exact (Finset.sum_le_sum_of_subset hsroots).trans_eq
      (Multiset.toFinset_sum_count_eq P.roots)
  have hcard : s.card = Fintype.card ι := by
    exact (Finset.card_image_of_injective Finset.univ halpha).trans
      Finset.card_univ
  have : Fintype.card ι * multiplicity ≤ P.natDegree := by
    rw [← hcard]
    exact hlow.trans (hupp.trans (Polynomial.card_roots' P))
  omega

/-- Coefficient-vector form of the confluent Vandermonde zero estimate.
The polynomial represented by `coeff` has precisely
`(#ι) * multiplicity` available coefficients. -/
theorem confluentVandermonde_coefficients_eq_zero
    {K : Type*} [CommRing K] [IsDomain K] [CharZero K] [DecidableEq K]
    {ι : Type*} [Fintype ι] (alpha : ι → K)
    (halpha : Function.Injective alpha) (multiplicity : ℕ)
    (coeff : Fin (Fintype.card ι * multiplicity) → K)
    (hvanish : ∀ i : ι, ∀ j : ℕ, j < multiplicity →
      ((Polynomial.derivative^[j])
          (Polynomial.ofFn (Fintype.card ι * multiplicity) coeff)).eval
        (alpha i) = 0) :
    coeff = 0 := by
  classical
  by_cases hN : Fintype.card ι * multiplicity = 0
  · funext i
    exact Fin.elim0 (Fin.cast hN i)
  · have hdegree :
        (Polynomial.ofFn (Fintype.card ι * multiplicity) coeff).natDegree <
          Fintype.card ι * multiplicity :=
      Polynomial.ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr hN) coeff
    have hpoly :
        Polynomial.ofFn (Fintype.card ι * multiplicity) coeff = 0 :=
      polynomial_eq_zero_of_iterateDerivative_vanishes alpha halpha
        hdegree hvanish
    apply Polynomial.injective_ofFn (Fintype.card ι * multiplicity)
    simpa using hpoly

/-- Explicit formula for a derivative-evaluation row of the confluent
Vandermonde matrix. -/
theorem eval_iterateDerivative_ofFn
    {K : Type*} [CommRing K] [DecidableEq K]
    {N : ℕ} (coeff : Fin N → K) (j : ℕ) (x : K) :
    ((Polynomial.derivative^[j]) (Polynomial.ofFn N coeff)).eval x =
      ∑ k : Fin N,
        coeff k * (Nat.descFactorial (k : ℕ) j : K) *
          x ^ ((k : ℕ) - j) := by
  rw [Polynomial.ofFn_eq_sum_monomial,
    Polynomial.iterate_derivative_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Polynomial.C_mul_X_pow_eq_monomial,
    Polynomial.iterate_derivative_C_mul,
    Polynomial.iterate_derivative_X_pow_eq_C_mul]
  simp [mul_assoc]

/-- Fully explicit confluent Vandermonde kernel statement, in terms of its
descending-factorial matrix entries. -/
theorem confluentVandermonde_descFactorial_coefficients_eq_zero
    {K : Type*} [CommRing K] [IsDomain K] [CharZero K] [DecidableEq K]
    {ι : Type*} [Fintype ι] (alpha : ι → K)
    (halpha : Function.Injective alpha) (multiplicity : ℕ)
    (coeff : Fin (Fintype.card ι * multiplicity) → K)
    (hzero : ∀ i : ι, ∀ j : ℕ, j < multiplicity →
      ∑ k : Fin (Fintype.card ι * multiplicity),
        coeff k * (Nat.descFactorial (k : ℕ) j : K) *
          alpha i ^ ((k : ℕ) - j) = 0) :
    coeff = 0 := by
  apply confluentVandermonde_coefficients_eq_zero alpha halpha
    multiplicity coeff
  intro i j hj
  rw [eval_iterateDerivative_ofFn]
  exact hzero i j hj

/-- A nonzero coefficient vector has a nonzero confluent-Vandermonde row. -/
theorem exists_confluentVandermonde_descFactorial_ne_zero
    {K : Type*} [CommRing K] [IsDomain K] [CharZero K] [DecidableEq K]
    {ι : Type*} [Fintype ι] (alpha : ι → K)
    (halpha : Function.Injective alpha) (multiplicity : ℕ)
    (coeff : Fin (Fintype.card ι * multiplicity) → K)
    (hcoeff : coeff ≠ 0) :
    ∃ i : ι, ∃ j : ℕ, j < multiplicity ∧
      ∑ k : Fin (Fintype.card ι * multiplicity),
        coeff k * (Nat.descFactorial (k : ℕ) j : K) *
          alpha i ^ ((k : ℕ) - j) ≠ 0 := by
  by_contra h
  push Not at h
  exact hcoeff <|
    confluentVandermonde_descFactorial_coefficients_eq_zero
      alpha halpha multiplicity coeff h

/-- Quantitative integral version: some confluent-Vandermonde row has
absolute value at least one. -/
theorem exists_one_le_abs_confluentVandermonde
    {ι : Type*} [Fintype ι] (alpha : ι → ℤ)
    (halpha : Function.Injective alpha) (multiplicity : ℕ)
    (coeff : Fin (Fintype.card ι * multiplicity) → ℤ)
    (hcoeff : coeff ≠ 0) :
    ∃ i : ι, ∃ j : ℕ, j < multiplicity ∧
      (1 : ℤ) ≤
        |∑ k : Fin (Fintype.card ι * multiplicity),
          coeff k * (Nat.descFactorial (k : ℕ) j : ℤ) *
            alpha i ^ ((k : ℕ) - j)| := by
  classical
  obtain ⟨i, j, hj, hne⟩ :=
    exists_confluentVandermonde_descFactorial_ne_zero
      alpha halpha multiplicity coeff hcoeff
  exact ⟨i, j, hj, Int.one_le_abs hne⟩

/-! ## Transposition: polynomial-exponential sequences -/

/-- The square confluent Vandermonde matrix.  Rows are indexed by a node
and a derivative order (encoded by `finProdFinEquiv`), and columns by
monomial degree. -/
def confluentVandermondeMatrix
    {K : Type*} [CommRing K] {r : ℕ}
    (alpha : Fin r → K) (multiplicity : ℕ) :
    Matrix (Fin (r * multiplicity)) (Fin (r * multiplicity)) K :=
  fun row column ↦
    let ij := (@finProdFinEquiv r multiplicity).symm row
    (Nat.descFactorial (column : ℕ) (ij.2 : ℕ) : K) *
      alpha ij.1 ^ ((column : ℕ) - (ij.2 : ℕ))

/-- The defining derivative-evaluation map of the confluent Vandermonde
matrix is injective. -/
theorem confluentVandermondeMatrix_mulVec_eq_zero
    {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    {r : ℕ} (alpha : Fin r → K) (halpha : Function.Injective alpha)
    (multiplicity : ℕ) (coeff : Fin (r * multiplicity) → K)
    (hzero : (confluentVandermondeMatrix alpha multiplicity).mulVec coeff = 0) :
    coeff = 0 := by
  classical
  by_cases hN : r * multiplicity = 0
  · funext k
    exact Fin.elim0 (Fin.cast hN k)
  · have hdegree :
        (Polynomial.ofFn (r * multiplicity) coeff).natDegree <
          Fintype.card (Fin r) * multiplicity := by
      simpa using Polynomial.ofFn_natDegree_lt
        (Nat.one_le_iff_ne_zero.mpr hN) coeff
    have hvanish : ∀ i : Fin r, ∀ j : ℕ, j < multiplicity →
        ((Polynomial.derivative^[j])
          (Polynomial.ofFn (r * multiplicity) coeff)).eval (alpha i) = 0 := by
      intro i j hj
      rw [eval_iterateDerivative_ofFn]
      let q : Fin (r * multiplicity) :=
        @finProdFinEquiv r multiplicity (i, ⟨j, hj⟩)
      have hq := congrFun hzero q
      simpa [confluentVandermondeMatrix, Matrix.mulVec, dotProduct, q,
        mul_assoc, mul_comm, mul_left_comm] using hq
    have hpoly :=
      polynomial_eq_zero_of_iterateDerivative_vanishes
        alpha halpha hdegree hvanish
    apply Polynomial.injective_ofFn (r * multiplicity)
    simpa using hpoly

/-- The confluent Vandermonde determinant is nonzero. -/
theorem confluentVandermondeMatrix_det_ne_zero
    {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    {r : ℕ} (alpha : Fin r → K) (halpha : Function.Injective alpha)
    (multiplicity : ℕ) :
    (confluentVandermondeMatrix alpha multiplicity).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨coeff, hcoeff, hzero⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact hcoeff <|
    confluentVandermondeMatrix_mulVec_eq_zero
      alpha halpha multiplicity coeff hzero

/-- Since the matrix is square, its transpose has trivial kernel too. -/
theorem confluentVandermondeMatrix_vecMul_eq_zero
    {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    {r : ℕ} (alpha : Fin r → K) (halpha : Function.Injective alpha)
    (multiplicity : ℕ) (coeff : Fin (r * multiplicity) → K)
    (hzero : Matrix.vecMul coeff
      (confluentVandermondeMatrix alpha multiplicity) = 0) :
    coeff = 0 := by
  classical
  exact Matrix.eq_zero_of_vecMul_eq_zero
    (confluentVandermondeMatrix_det_ne_zero
      alpha halpha multiplicity) hzero

/-- A generalized exponential sequence
`sum_i sum_j c i j * (k)_j * alpha_i^(k-j)` cannot vanish at all of the
first `r * multiplicity` integers unless all coefficients vanish.  This is
the transposed confluent-Vandermonde zero estimate used for exponential
polynomials. -/
theorem generalizedExponentialSequence_coefficients_eq_zero
    {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    {r : ℕ} (alpha : Fin r → K) (halpha : Function.Injective alpha)
    (multiplicity : ℕ) (coeff : Fin r → Fin multiplicity → K)
    (hzero : ∀ k : Fin (r * multiplicity),
      ∑ i : Fin r, ∑ j : Fin multiplicity,
        coeff i j * (Nat.descFactorial (k : ℕ) (j : ℕ) : K) *
          alpha i ^ ((k : ℕ) - (j : ℕ)) = 0) :
    coeff = 0 := by
  classical
  let flat : Fin (r * multiplicity) → K := fun q ↦
    let ij := (@finProdFinEquiv r multiplicity).symm q
    coeff ij.1 ij.2
  have hflat : Matrix.vecMul flat
      (confluentVandermondeMatrix alpha multiplicity) = 0 := by
    funext k
    rw [Pi.zero_apply]
    change (∑ q, flat q *
      confluentVandermondeMatrix alpha multiplicity q k) = 0
    rw [← Equiv.sum_comp (@finProdFinEquiv r multiplicity)]
    rw [Fintype.sum_prod_type]
    have hflat_apply (i : Fin r) (j : Fin multiplicity) :
        flat (@finProdFinEquiv r multiplicity (i, j)) = coeff i j := by
      dsimp [flat]
      rw [Equiv.symm_apply_apply]
    have hmatrix_apply (i : Fin r) (j : Fin multiplicity) :
        confluentVandermondeMatrix alpha multiplicity
            (@finProdFinEquiv r multiplicity (i, j)) k =
          (Nat.descFactorial (k : ℕ) (j : ℕ) : K) *
            alpha i ^ ((k : ℕ) - (j : ℕ)) := by
      dsimp [confluentVandermondeMatrix]
      rw [Equiv.symm_apply_apply]
    simp_rw [hflat_apply, hmatrix_apply]
    simpa [mul_assoc] using hzero k
  have hflatzero := confluentVandermondeMatrix_vecMul_eq_zero
    alpha halpha multiplicity flat hflat
  funext i j
  let q : Fin (r * multiplicity) :=
    @finProdFinEquiv r multiplicity (i, j)
  have hq := congrFun hflatzero q
  change coeff ((@finProdFinEquiv r multiplicity).symm q).1
      ((@finProdFinEquiv r multiplicity).symm q).2 = 0 at hq
  rw [show (@finProdFinEquiv r multiplicity).symm q = (i, j) by
    exact Equiv.symm_apply_apply _ _] at hq
  exact hq

/-- Nonzero coefficients force a nonzero value among the first
`r * multiplicity` samples. -/
theorem exists_generalizedExponentialSequence_ne_zero
    {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    {r : ℕ} (alpha : Fin r → K) (halpha : Function.Injective alpha)
    (multiplicity : ℕ) (coeff : Fin r → Fin multiplicity → K)
    (hcoeff : coeff ≠ 0) :
    ∃ k : Fin (r * multiplicity),
      ∑ i : Fin r, ∑ j : Fin multiplicity,
        coeff i j * (Nat.descFactorial (k : ℕ) (j : ℕ) : K) *
          alpha i ^ ((k : ℕ) - (j : ℕ)) ≠ 0 := by
  by_contra h
  push Not at h
  exact hcoeff <|
    generalizedExponentialSequence_coefficients_eq_zero
      alpha halpha multiplicity coeff h

/-- Integral quantitative form of the generalized exponential-sequence
zero estimate. -/
theorem exists_one_le_abs_generalizedExponentialSequence
    {r : ℕ} (alpha : Fin r → ℤ) (halpha : Function.Injective alpha)
    (multiplicity : ℕ) (coeff : Fin r → Fin multiplicity → ℤ)
    (hcoeff : coeff ≠ 0) :
    ∃ k : Fin (r * multiplicity), (1 : ℤ) ≤
      |∑ i : Fin r, ∑ j : Fin multiplicity,
        coeff i j * (Nat.descFactorial (k : ℕ) (j : ℕ) : ℤ) *
          alpha i ^ ((k : ℕ) - (j : ℕ))| := by
  obtain ⟨k, hk⟩ := exists_generalizedExponentialSequence_ne_zero
    alpha halpha multiplicity coeff hcoeff
  exact ⟨k, Int.one_le_abs hk⟩

/-- The falling-factorial polynomial-exponential sequences with values
`cᵢₘ (h)ₘ αᵢ^h` are linearly independent.  This rescaled form of the
confluent Vandermonde theorem is the zero estimate naturally matched by
polynomially weighted auxiliary functions at integer nodes. -/
theorem generalizedPochhammerExponentialSequence_coefficients_eq_zero
    {F : Type*} [Field F] [CharZero F] {r multiplicity : ℕ}
    (alpha : Fin r → F) (halpha : Function.Injective alpha)
    (halpha0 : ∀ i, alpha i ≠ 0)
    (coeff : Fin r → Fin multiplicity → F)
    (hzero : ∀ h : Fin (r * multiplicity),
      ∑ i : Fin r, ∑ m : Fin multiplicity,
        coeff i m * (Nat.descFactorial (h : ℕ) (m : ℕ) : F) *
          alpha i ^ (h : ℕ) = 0) :
    coeff = 0 := by
  let coeff' : Fin r → Fin multiplicity → F := fun i m ↦
    coeff i m * alpha i ^ (m : ℕ)
  have hzero' : ∀ h : Fin (r * multiplicity),
      ∑ i : Fin r, ∑ m : Fin multiplicity,
        coeff' i m * (Nat.descFactorial (h : ℕ) (m : ℕ) : F) *
          alpha i ^ ((h : ℕ) - (m : ℕ)) = 0 := by
    intro h
    rw [show (∑ i : Fin r, ∑ m : Fin multiplicity,
        coeff' i m * (Nat.descFactorial (h : ℕ) (m : ℕ) : F) *
          alpha i ^ ((h : ℕ) - (m : ℕ))) =
        ∑ i : Fin r, ∑ m : Fin multiplicity,
          coeff i m * (Nat.descFactorial (h : ℕ) (m : ℕ) : F) *
            alpha i ^ (h : ℕ) by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hmh : (m : ℕ) ≤ (h : ℕ)
      · dsimp [coeff']
        calc
          coeff i m * alpha i ^ (m : ℕ) *
                (Nat.descFactorial (h : ℕ) (m : ℕ) : F) *
                alpha i ^ ((h : ℕ) - (m : ℕ)) =
              coeff i m * (Nat.descFactorial (h : ℕ) (m : ℕ) : F) *
                (alpha i ^ (m : ℕ) *
                  alpha i ^ ((h : ℕ) - (m : ℕ))) := by ring
          _ = _ := by rw [← pow_add, Nat.add_sub_of_le hmh]
      · have hlt : (h : ℕ) < (m : ℕ) := lt_of_not_ge hmh
        rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]
        simp]
    exact hzero h
  have hcoeff' := generalizedExponentialSequence_coefficients_eq_zero
    alpha halpha multiplicity coeff' hzero'
  funext i m
  have him := congrFun (congrFun hcoeff' i) m
  dsimp [coeff'] at him
  exact (mul_eq_zero.mp him).resolve_right (pow_ne_zero _ (halpha0 i))

/-- Nonzero coefficients in the falling-factorial basis force a nonzero
algebraic sample before `r * multiplicity`. -/
theorem exists_generalizedPochhammerExponentialSequence_ne_zero
    {F : Type*} [Field F] [CharZero F] {r multiplicity : ℕ}
    (alpha : Fin r → F) (halpha : Function.Injective alpha)
    (halpha0 : ∀ i, alpha i ≠ 0)
    (coeff : Fin r → Fin multiplicity → F) (hcoeff : coeff ≠ 0) :
    ∃ h : Fin (r * multiplicity),
      ∑ i : Fin r, ∑ m : Fin multiplicity,
        coeff i m * (Nat.descFactorial (h : ℕ) (m : ℕ) : F) *
          alpha i ^ (h : ℕ) ≠ 0 := by
  by_contra h
  push Not at h
  exact hcoeff <|
    generalizedPochhammerExponentialSequence_coefficients_eq_zero
      alpha halpha halpha0 coeff h

/-! ## Archimedean determinant upper bounds -/

/-- A columnwise form of the elementary Leibniz/Hadamard bound.  It is
stated for complex matrices because interpolation determinants are evaluated
at a distinguished complex embedding. -/
theorem norm_det_le_factorial_mul_prod
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (R : Fin n → ℝ)
    (_hRnonneg : ∀ j, 0 ≤ R j)
    (hR : ∀ i j, ‖M i j‖ ≤ R j) :
    ‖M.det‖ ≤ (n.factorial : ℝ) * ∏ j, R j := by
  classical
  rw [Matrix.det_apply']
  calc
    ‖∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (σ i) i‖ ≤
        ∑ σ : Equiv.Perm (Fin n),
          ‖((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (σ i) i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), ∏ j, R j := by
      apply Finset.sum_le_sum
      intro σ _
      rw [norm_mul, Complex.norm_intCast, ← Int.cast_abs,
        Equiv.Perm.sign_abs, Int.cast_one, one_mul, norm_prod]
      exact Finset.prod_le_prod
        (fun j _ ↦ norm_nonneg _) (fun j _ ↦ hR _ _)
    _ = (n.factorial : ℝ) * ∏ j, R j := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_perm, Fintype.card_fin]

/-- Uniform-entry specialization of `norm_det_le_factorial_mul_prod`. -/
theorem norm_det_le_factorial_mul_pow
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) {R : ℝ}
    (hRnonneg : 0 ≤ R) (hR : ∀ i j, ‖M i j‖ ≤ R) :
    ‖M.det‖ ≤ (n.factorial : ℝ) * R ^ n := by
  simpa using norm_det_le_factorial_mul_prod M (fun _ ↦ R)
    (fun _ ↦ hRnonneg) hR

/-! ## Global height bounds for determinants -/

/-- A columnwise logarithmic-height bound for a determinant over a number
field.  The first term is the cost of summing the `n!` Leibniz terms; the
second bounds each product term and then sums over all permutations. -/
theorem logHeight₁_det_le_factorial_mul_sum
    {K : Type*} [Field K] [NumberField K]
    {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (A : Fin n → ℝ)
    (hA : ∀ i j, Height.logHeight₁ (M i j) ≤ A j) :
    Height.logHeight₁ M.det ≤
      (Module.finrank ℚ K : ℝ) * Real.log (n.factorial : ℝ) +
        (n.factorial : ℝ) * ∑ j, A j := by
  classical
  rw [Matrix.det_apply']
  calc
    Height.logHeight₁
        (∑ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, M (σ i) i) ≤
        (Module.finrank ℚ K : ℝ) *
            Real.log ((Finset.univ : Finset (Equiv.Perm (Fin n))).card : ℝ) +
          ∑ σ : Equiv.Perm (Fin n), Height.logHeight₁
            (((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, M (σ i) i) := by
      rw [← NumberField.totalWeight_eq_finrank K]
      simpa using Height.logHeight₁_sum_le
        (Finset.univ : Finset (Equiv.Perm (Fin n)))
        (fun σ ↦ ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, M (σ i) i)
    _ ≤ (Module.finrank ℚ K : ℝ) * Real.log (n.factorial : ℝ) +
          ∑ _σ : Equiv.Perm (Fin n), ∑ j, A j := by
      rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
      gcongr with σ
      calc
        Height.logHeight₁ (((Equiv.Perm.sign σ : ℤ) : K) *
            ∏ i, M (σ i) i) ≤
            Height.logHeight₁ ((Equiv.Perm.sign σ : ℤ) : K) +
              Height.logHeight₁ (∏ i, M (σ i) i) :=
          Height.logHeight₁_mul_le _ _
        _ ≤ 0 + ∑ j, Height.logHeight₁ (M (σ j) j) := by
          gcongr
          · rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
              simp [h]
          · simpa using Height.logHeight₁_prod_le
              (Finset.univ : Finset (Fin n)) (fun j ↦ M (σ j) j)
        _ ≤ ∑ j, A j := by
          simp only [zero_add]
          exact Finset.sum_le_sum fun j _ ↦ hA _ _
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_perm, Fintype.card_fin]

/-- Uniform-entry specialization of
`logHeight₁_det_le_factorial_mul_sum`. -/
theorem logHeight₁_det_le_factorial_mul
    {K : Type*} [Field K] [NumberField K]
    {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {A : ℝ}
    (hA : ∀ i j, Height.logHeight₁ (M i j) ≤ A) :
    Height.logHeight₁ M.det ≤
      (Module.finrank ℚ K : ℝ) * Real.log (n.factorial : ℝ) +
        (n.factorial : ℝ) * n * A := by
  simpa [Finset.sum_const, nsmul_eq_mul, mul_assoc] using
    logHeight₁_det_le_factorial_mul_sum M (fun _ ↦ A) hA

/-! ## Derivatives of exponential polynomials -/

/-- A monomial times one complex exponential, the elementary building block
of the auxiliary interpolation function. -/
def exponentialMonomial (c : ℂ) (m : ℕ) : ℂ → ℂ :=
  fun z ↦ z ^ m * Complex.exp (c * z)

lemma exponentialMonomial_contDiff (c : ℂ) (m : ℕ) :
    ContDiff ℂ ⊤ (exponentialMonomial c m) := by
  unfold exponentialMonomial
  fun_prop

/-- The derivative at zero of `z^m exp(cz)`.  This is the analytic source of
the descending-factorial kernel in the confluent Vandermonde matrix. -/
theorem iteratedDeriv_exponentialMonomial_zero (c : ℂ) (m k : ℕ) :
    iteratedDeriv k (exponentialMonomial c m) 0 =
      (Nat.descFactorial k m : ℂ) * c ^ (k - m) := by
  rw [show exponentialMonomial c m = (fun z : ℂ ↦ z ^ m) *
      (fun z : ℂ ↦ Complex.exp (c * z)) by rfl]
  rw [iteratedDeriv_mul (by fun_prop) (by fun_prop)]
  have hexp (q : ℕ) :
      iteratedDeriv q (fun z : ℂ ↦ Complex.exp (c * z)) 0 = c ^ q := by
    rw [congrFun (iteratedDeriv_cexp_const_mul q c) 0]
    simp
  simp_rw [hexp]
  by_cases hmk : m ≤ k
  · rw [Finset.sum_eq_single m]
    · rw [iteratedDeriv_pow]
      have hdf : (Nat.descFactorial m m : ℂ) = (m.factorial : ℂ) := by
        rw [Nat.descFactorial_self]
      rw [hdf]
      simp only [Nat.sub_self, pow_zero, mul_one]
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      push_cast
      ring
    · intro q hq hqm
      simp only [Finset.mem_range] at hq
      rw [iteratedDeriv_pow]
      by_cases hqm' : q < m
      · have hsub : m - q ≠ 0 := Nat.sub_ne_zero_of_lt hqm'
        simp [hsub]
      · have hmq : m < q := lt_of_le_of_ne (le_of_not_gt hqm') hqm.symm
        simp [Nat.descFactorial_eq_zero_iff_lt.mpr hmq]
    · intro hmnot
      exact (hmnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hmk))).elim
  · have hkm : k < m := lt_of_not_ge hmk
    have : ∀ q ∈ Finset.range (k + 1),
        (k.choose q : ℂ) * iteratedDeriv q (fun z : ℂ ↦ z ^ m) 0 *
          c ^ (k - q) = 0 := by
      intro q hq
      have hqk : q ≤ k := by simp only [Finset.mem_range] at hq; omega
      have hqm : q < m := lt_of_le_of_lt hqk hkm
      rw [iteratedDeriv_pow]
      have hsub : m - q ≠ 0 := Nat.sub_ne_zero_of_lt hqm
      simp [hsub]
    rw [Finset.sum_eq_zero this]
    simp [Nat.descFactorial_eq_zero_iff_lt.mpr hkm]

/-- A finite exponential polynomial with a common multiplicity cutoff. -/
def exponentialPolynomial {r multiplicity : ℕ}
    (c : Fin r → ℂ) (coeff : Fin r → Fin multiplicity → ℂ) : ℂ → ℂ :=
  fun z ↦ ∑ i, ∑ j, coeff i j * exponentialMonomial (c i) j z

/-- Its derivatives at zero are exactly the generalized exponential sequence
controlled by the confluent Vandermonde zero estimate. -/
theorem iteratedDeriv_exponentialPolynomial_zero
    {r multiplicity : ℕ}
    (c : Fin r → ℂ) (coeff : Fin r → Fin multiplicity → ℂ) (k : ℕ) :
    iteratedDeriv k (exponentialPolynomial c coeff) 0 =
      ∑ i, ∑ j, coeff i j *
        (Nat.descFactorial k j : ℂ) * c i ^ (k - j) := by
  unfold exponentialPolynomial
  have houter : (fun z ↦ ∑ i : Fin r, ∑ j : Fin multiplicity,
      coeff i j * exponentialMonomial (c i) j z) =
      ∑ i : Fin r, (fun z ↦ ∑ j : Fin multiplicity,
        coeff i j * exponentialMonomial (c i) j z) := by
    funext z
    simp
  rw [houter]
  rw [iteratedDeriv_sum (I := Finset.univ) (by
    intro i _
    apply ContDiffAt.sum
    intro j _
    unfold exponentialMonomial
    fun_prop)]
  apply Finset.sum_congr rfl
  intro i _
  have hinner : (fun z ↦ ∑ j : Fin multiplicity,
      coeff i j * exponentialMonomial (c i) j z) =
      ∑ j : Fin multiplicity, (fun z ↦
        coeff i j * exponentialMonomial (c i) j z) := by
    funext z
    simp
  rw [hinner]
  rw [iteratedDeriv_sum (I := Finset.univ) (by
    intro j _
    unfold exponentialMonomial
    fun_prop)]
  apply Finset.sum_congr rfl
  intro j _
  rw [iteratedDeriv_const_mul (coeff i j) (by
    unfold exponentialMonomial
    fun_prop)]
  rw [iteratedDeriv_exponentialMonomial_zero]
  ring

/-- A nonzero exponential polynomial with pairwise distinct exponents has a
nonzero derivative among the first `r * multiplicity` derivatives at zero. -/
theorem exists_iteratedDeriv_exponentialPolynomial_ne_zero
    {r multiplicity : ℕ}
    (c : Fin r → ℂ) (hc : Function.Injective c)
    (coeff : Fin r → Fin multiplicity → ℂ) (hcoeff : coeff ≠ 0) :
    ∃ k : Fin (r * multiplicity),
      iteratedDeriv (k : ℕ) (exponentialPolynomial c coeff) 0 ≠ 0 := by
  obtain ⟨k, hk⟩ := exists_generalizedExponentialSequence_ne_zero
    c hc multiplicity coeff hcoeff
  refine ⟨k, ?_⟩
  rw [iteratedDeriv_exponentialPolynomial_zero]
  exact hk

/-- Equivalent vanishing formulation of the derivative zero estimate. -/
theorem exponentialPolynomial_coefficients_eq_zero
    {r multiplicity : ℕ}
    (c : Fin r → ℂ) (hc : Function.Injective c)
    (coeff : Fin r → Fin multiplicity → ℂ)
    (hzero : ∀ k : Fin (r * multiplicity),
      iteratedDeriv (k : ℕ) (exponentialPolynomial c coeff) 0 = 0) :
    coeff = 0 := by
  apply generalizedExponentialSequence_coefficients_eq_zero
    c hc multiplicity coeff
  intro k
  rw [← iteratedDeriv_exponentialPolynomial_zero]
  exact hzero k

/-! ## Ordinary auxiliary exponential sums -/

/-- A finite auxiliary exponential sum. -/
def auxiliaryExponentialSum {ι : Type*} [Fintype ι]
    (c coeff : ι → ℂ) : ℂ → ℂ :=
  fun z ↦ ∑ i, coeff i * Complex.exp (c i * z)

/-- Exact derivative formula for a finite auxiliary exponential sum. -/
theorem iteratedDeriv_auxiliaryExponentialSum
    {ι : Type*} [Fintype ι]
    (c coeff : ι → ℂ) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (auxiliaryExponentialSum c coeff) z =
      ∑ i, coeff i * c i ^ k * Complex.exp (c i * z) := by
  unfold auxiliaryExponentialSum
  have hfun : (fun w ↦ ∑ i : ι, coeff i * Complex.exp (c i * w)) =
      ∑ i : ι, (fun w ↦ coeff i * Complex.exp (c i * w)) := by
    funext w
    simp
  rw [hfun]
  rw [iteratedDeriv_sum (I := Finset.univ) (by intros; fun_prop)]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedDeriv_const_mul (coeff i) (by fun_prop)]
  rw [congrFun (iteratedDeriv_cexp_const_mul k (c i)) z]
  ring

/-- At a nonnegative integer, exponentiating the principal logarithm of a
nonzero complex number recovers an ordinary algebraic power. -/
theorem auxiliaryExponentialSum_nat_log
    {r : ℕ} (alpha coeff : Fin r → ℂ)
    (halpha : ∀ i, alpha i ≠ 0) (t : ℕ) :
    auxiliaryExponentialSum (fun i ↦ Complex.log (alpha i)) coeff (t : ℂ) =
      ∑ i, coeff i * alpha i ^ t := by
  unfold auxiliaryExponentialSum
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  calc
    Complex.exp (Complex.log (alpha i) * (t : ℂ)) =
        Complex.exp ((t : ℂ) * Complex.log (alpha i)) := by rw [mul_comm]
    _ = Complex.exp (Complex.log (alpha i)) ^ t :=
      Complex.exp_nat_mul _ _
    _ = alpha i ^ t := by rw [Complex.exp_log (halpha i)]

/-- Number-field form of the preceding identity: integer values of the
auxiliary sum are embeddings of explicit algebraic sums. -/
theorem auxiliaryExponentialSum_nat_log_numberField
    {K : Type*} [Field K] [NumberField K]
    (phi : K →+* ℂ) {r : ℕ} (alpha : Fin r → K)
    (halpha : ∀ i, alpha i ≠ 0) (coeff : Fin r → ℤ) (t : ℕ) :
    auxiliaryExponentialSum (fun i ↦ Complex.log (phi (alpha i)))
        (fun i ↦ (coeff i : ℂ)) (t : ℂ) =
      phi (∑ i, (coeff i : K) * alpha i ^ t) := by
  rw [auxiliaryExponentialSum_nat_log
    (fun i ↦ phi (alpha i)) (fun i ↦ (coeff i : ℂ))
    (fun i ↦ (map_ne_zero phi).2 (halpha i))]
  simp

/-! ## Heights of auxiliary-function values -/

/-- Casting a natural number into a number field costs at most its degree
times the ordinary logarithm. -/
theorem logHeight₁_natCast_le
    {K : Type*} [Field K] [NumberField K] (n : ℕ) :
    Height.logHeight₁ (n : K) ≤
      (Module.finrank ℚ K : ℝ) * Real.log (max 1 n : ℕ) := by
  by_cases hn : n = 0
  · simp [hn]
  have hsum : (n : K) = ∑ _i ∈ Finset.range n, (1 : K) := by simp
  rw [hsum]
  calc
    Height.logHeight₁ (∑ _i ∈ Finset.range n, (1 : K)) ≤
        (Height.totalWeight K : ℝ) * Real.log ((Finset.range n).card : ℝ) +
          ∑ _i ∈ Finset.range n, Height.logHeight₁ (1 : K) :=
      Height.logHeight₁_sum_le (Finset.range n) (fun _ ↦ (1 : K))
    _ = (Module.finrank ℚ K : ℝ) * Real.log (max 1 n : ℕ) := by
      rw [NumberField.totalWeight_eq_finrank]
      simp [max_eq_right (Nat.one_le_iff_ne_zero.mpr hn)]

/-- Integer-cast variant, expressed using `natAbs`. -/
theorem logHeight₁_intCast_le
    {K : Type*} [Field K] [NumberField K] (z : ℤ) :
    Height.logHeight₁ (z : K) ≤
      (Module.finrank ℚ K : ℝ) * Real.log (max 1 z.natAbs : ℕ) := by
  cases z with
  | ofNat n => simpa using logHeight₁_natCast_le (K := K) n
  | negSucc n =>
      rw [show ((Int.negSucc n : ℤ) : K) = -((n + 1 : ℕ) : K) by simp,
        Height.logHeight₁_neg]
      simpa using logHeight₁_natCast_le (K := K) (n + 1)

/-- Uniform height bound for the algebraic value represented by an auxiliary
exponential sum at a natural integer. -/
theorem logHeight₁_auxiliaryAlgebraicValue_le
    {K : Type*} [Field K] [NumberField K]
    {r t C : ℕ} (alpha : Fin r → K) (coeff : Fin r → ℤ) {A : ℝ}
    (hC : 1 ≤ C) (hcoeff : ∀ i, (coeff i).natAbs ≤ C)
    (hA : ∀ i, Height.logHeight₁ (alpha i) ≤ A) :
    Height.logHeight₁ (∑ i, (coeff i : K) * alpha i ^ t) ≤
      (Module.finrank ℚ K : ℝ) * Real.log (r : ℝ) +
        (r : ℝ) * ((Module.finrank ℚ K : ℝ) * Real.log (C : ℝ) +
          (t : ℝ) * A) := by
  classical
  calc
    Height.logHeight₁ (∑ i, (coeff i : K) * alpha i ^ t) ≤
        (Height.totalWeight K : ℝ) *
            Real.log ((Finset.univ : Finset (Fin r)).card : ℝ) +
          ∑ i, Height.logHeight₁ ((coeff i : K) * alpha i ^ t) := by
      simpa using Height.logHeight₁_sum_le (Finset.univ : Finset (Fin r))
        (fun i ↦ (coeff i : K) * alpha i ^ t)
    _ ≤ (Module.finrank ℚ K : ℝ) * Real.log (r : ℝ) +
          ∑ _i : Fin r, ((Module.finrank ℚ K : ℝ) * Real.log (C : ℝ) +
            (t : ℝ) * A) := by
      rw [NumberField.totalWeight_eq_finrank, Finset.card_univ, Fintype.card_fin]
      gcongr with i
      calc
        Height.logHeight₁ ((coeff i : K) * alpha i ^ t) ≤
            Height.logHeight₁ (coeff i : K) + Height.logHeight₁ (alpha i ^ t) :=
          Height.logHeight₁_mul_le _ _
        _ ≤ (Module.finrank ℚ K : ℝ) * Real.log (C : ℝ) +
            (t : ℝ) * A := by
          gcongr
          · refine (logHeight₁_intCast_le (K := K) (coeff i)).trans ?_
            gcongr
            exact_mod_cast max_le hC (hcoeff i)
          · rw [Height.logHeight₁_pow]
            gcongr
            exact hA i
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]

/-- One-place Liouville lower bound, included here in the form used for
auxiliary values. -/
theorem neg_logHeight₁_le_log_norm_embedding
    {K : Type*} [Field K] [NumberField K]
    (phi : K →+* ℂ) {x : K} (_hx : x ≠ 0) :
    -Height.logHeight₁ x ≤ Real.log ‖phi x‖ := by
  let w : NumberField.InfinitePlace K := NumberField.InfinitePlace.mk phi
  have harchTerm :
      (w.mult : ℝ) * Real.posLog (w (x⁻¹)) ≤
        ∑ v : NumberField.InfinitePlace K,
          (v.mult : ℝ) * Real.posLog (v (x⁻¹)) := by
    exact Finset.single_le_sum
      (fun (v : NumberField.InfinitePlace K) _ ↦
        mul_nonneg (Nat.cast_nonneg v.mult)
          (show 0 ≤ Real.posLog (v (x⁻¹)) from Real.posLog_nonneg))
      (Finset.mem_univ w)
  have hnonarch : 0 ≤
      ∑ᶠ v : NumberField.FinitePlace K, Real.posLog (v (x⁻¹)) :=
    finsum_nonneg fun v : NumberField.FinitePlace K ↦
      (show 0 ≤ Real.posLog (v (x⁻¹)) from Real.posLog_nonneg)
  have htermHeight :
      (w.mult : ℝ) * Real.posLog (w (x⁻¹)) ≤
        Height.logHeight₁ x := by
    calc
      _ ≤ ∑ v : NumberField.InfinitePlace K,
          (v.mult : ℝ) * Real.posLog (v (x⁻¹)) := harchTerm
      _ ≤ (∑ v : NumberField.InfinitePlace K,
          (v.mult : ℝ) * Real.posLog (v (x⁻¹))) +
          ∑ᶠ v : NumberField.FinitePlace K,
            Real.posLog (v (x⁻¹)) := le_add_of_nonneg_right hnonarch
      _ = Height.logHeight₁ (x⁻¹) :=
        (NumberField.logHeight₁_eq (x⁻¹)).symm
      _ = Height.logHeight₁ x := Height.logHeight₁_inv x
  have hwInv : w (x⁻¹) = ‖phi x‖⁻¹ := by simp [w]
  have hneglog : -Real.log ‖phi x‖ ≤ Real.posLog (w (x⁻¹)) := by
    rw [hwInv]
    change -Real.log ‖phi x‖ ≤ max 0 (Real.log ‖phi x‖⁻¹)
    rw [Real.log_inv]
    exact le_max_right _ _
  have hmult : Real.posLog (w (x⁻¹)) ≤
      (w.mult : ℝ) * Real.posLog (w (x⁻¹)) := by
    nth_rewrite 1 [← one_mul (Real.posLog (w (x⁻¹)))]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr w.mult_ne_zero)
      Real.posLog_nonneg
  linarith

/-- A nonzero algebraic auxiliary value cannot be smaller than the explicit
height majorant just proved. -/
theorem auxiliaryExponentialSum_nat_log_lower
    {K : Type*} [Field K] [NumberField K]
    (phi : K →+* ℂ) {r t C : ℕ} (alpha : Fin r → K)
    (halpha : ∀ i, alpha i ≠ 0) (coeff : Fin r → ℤ) {A : ℝ}
    (hC : 1 ≤ C) (hcoeff : ∀ i, (coeff i).natAbs ≤ C)
    (hA : ∀ i, Height.logHeight₁ (alpha i) ≤ A)
    (hvalue : (∑ i, (coeff i : K) * alpha i ^ t) ≠ 0) :
    -((Module.finrank ℚ K : ℝ) * Real.log (r : ℝ) +
        (r : ℝ) * ((Module.finrank ℚ K : ℝ) * Real.log (C : ℝ) +
          (t : ℝ) * A)) ≤
      Real.log ‖auxiliaryExponentialSum
        (fun i ↦ Complex.log (phi (alpha i)))
        (fun i ↦ (coeff i : ℂ)) (t : ℂ)‖ := by
  let x : K := ∑ i, (coeff i : K) * alpha i ^ t
  have hheight := logHeight₁_auxiliaryAlgebraicValue_le
    (t := t) (C := C) alpha coeff hC hcoeff hA
  have hlocal := neg_logHeight₁_le_log_norm_embedding phi hvalue
  rw [auxiliaryExponentialSum_nat_log_numberField
    phi alpha halpha coeff t]
  linarith

/-! ## Algebraic auxiliary values over an exponent box -/

/-- The algebraic value of the box-indexed auxiliary exponential sum at a
nonnegative integer. -/
def boxAuxiliaryAlgebraicValue
    {F : Type*} [Field F] {n K : ℕ}
    (alpha : Fin n → F) (coeff : ExponentBox n K → ℤ) (t : ℕ) : F :=
  ∑ k, (coeff k : F) * boxMonomial alpha k ^ t

/-- If the box monomials are distinct and the integral coefficient vector
is nonzero, one of the first `K^n` algebraic samples is nonzero. -/
theorem exists_boxAuxiliaryAlgebraicValue_ne_zero
    {F : Type*} [Field F] [CharZero F] {n K : ℕ}
    (alpha : Fin n → F) (coeff : ExponentBox n K → ℤ)
    (hinj : Function.Injective
      (fun k : ExponentBox n K ↦ boxMonomial alpha k))
    (hcoeff : coeff ≠ 0) :
    ∃ t : Fin (Fintype.card (ExponentBox n K)),
      boxAuxiliaryAlgebraicValue alpha coeff t ≠ 0 := by
  have hcoeffF : (fun k ↦ (coeff k : F)) ≠ 0 := by
    intro hzero
    apply hcoeff
    funext k
    have hk := congrFun hzero k
    exact (Int.cast_injective : Function.Injective (fun z : ℤ ↦ (z : F)))
      (by simpa using hk)
  obtain ⟨t, ht⟩ := exists_finite_exponentialSum_ne_zero
    (boxMonomial alpha) (fun k ↦ (coeff k : F)) hinj hcoeffF
  exact ⟨t, by simpa [boxAuxiliaryAlgebraicValue] using ht⟩

/-- Global height bound for a box-indexed auxiliary value. -/
theorem logHeight₁_boxAuxiliaryAlgebraicValue_le
    {F : Type*} [Field F] [NumberField F] {n K C t : ℕ}
    (alpha : Fin n → F) (coeff : ExponentBox n K → ℤ)
    (hC : 1 ≤ C) (hcoeff : ∀ k, (coeff k).natAbs ≤ C) :
    Height.logHeight₁ (boxAuxiliaryAlgebraicValue alpha coeff t) ≤
      (Module.finrank ℚ F : ℝ) * Real.log ((K ^ n : ℕ) : ℝ) +
        ((K ^ n : ℕ) : ℝ) *
          ((Module.finrank ℚ F : ℝ) * Real.log (C : ℝ) +
            (t : ℝ) *
              ((K : ℝ) * ∑ i, Height.logHeight₁ (alpha i))) := by
  rw [boxAuxiliaryAlgebraicValue]
  calc
    Height.logHeight₁
        (∑ k, (coeff k : F) * boxMonomial alpha k ^ t) ≤
      (Height.totalWeight F : ℝ) *
          Real.log ((Finset.univ : Finset (ExponentBox n K)).card : ℝ) +
        ∑ k, Height.logHeight₁
          ((coeff k : F) * boxMonomial alpha k ^ t) := by
      exact Height.logHeight₁_sum_le Finset.univ _
    _ ≤ (Module.finrank ℚ F : ℝ) * Real.log ((K ^ n : ℕ) : ℝ) +
        ∑ _k : ExponentBox n K,
          ((Module.finrank ℚ F : ℝ) * Real.log (C : ℝ) +
            (t : ℝ) *
              ((K : ℝ) * ∑ i, Height.logHeight₁ (alpha i))) := by
      rw [NumberField.totalWeight_eq_finrank, Finset.card_univ]
      simp only [ExponentBox, Fintype.card_fun, Fintype.card_fin]
      gcongr with k
      calc
        Height.logHeight₁ ((coeff k : F) * boxMonomial alpha k ^ t) ≤
            Height.logHeight₁ (coeff k : F) +
              Height.logHeight₁ (boxMonomial alpha k ^ t) :=
          Height.logHeight₁_mul_le _ _
        _ ≤ (Module.finrank ℚ F : ℝ) * Real.log (C : ℝ) +
              (t : ℝ) *
                ((K : ℝ) * ∑ i, Height.logHeight₁ (alpha i)) := by
          gcongr
          · refine (logHeight₁_intCast_le (K := F) (coeff k)).trans ?_
            gcongr
            exact_mod_cast max_le hC (hcoeff k)
          · rw [Height.logHeight₁_pow]
            gcongr
            exact logHeight₁_boxMonomial_le alpha k
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      simp only [ExponentBox, Fintype.card_fun, Fintype.card_fin]

/-- The distinguished embedding identifies the algebraic box value with
the corresponding sum of complex exponentials. -/
theorem boxAuxiliaryAlgebraicValue_embedding
    {F : Type*} [Field F] [NumberField F] (phi : F →+* ℂ)
    {n K : ℕ} (alpha : Fin n → F) (halpha : ∀ i, alpha i ≠ 0)
    (coeff : ExponentBox n K → ℤ) (t : ℕ) :
    phi (boxAuxiliaryAlgebraicValue alpha coeff t) =
      ∑ k, (coeff k : ℂ) *
        Complex.exp
          (boxLinearForm (fun i ↦ Complex.log (phi (alpha i))) k * t) := by
  rw [boxAuxiliaryAlgebraicValue, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_mul, map_intCast, map_pow]
  have hmap : phi (boxMonomial alpha k) =
      boxMonomial (fun i ↦ phi (alpha i)) k := by
    exact map_boxMonomial phi.toMonoidHom alpha k
  rw [hmap]
  congr 1
  rw [← exp_boxLinearForm_log (fun i ↦ phi (alpha i))
    (fun i ↦ (map_ne_zero phi).2 (halpha i)) k]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- Evaluation of the two-entry tuple `[α,1]` along the first `j` slots. -/
lemma powerTuple_apply_aux
    {F : Type*} [Field F] [Height.AdmissibleAbsValues F]
    (alpha : F) (K : ℕ) (j : Fin K) :
    (∏ i : Fin K, ![alpha, (1 : F)]
        (if (i : ℕ) < (j : ℕ) then (0 : Fin 2) else 1)) =
      alpha ^ (j : ℕ) := by
  simp only [apply_ite, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Finset.prod_ite]
  rw [Finset.prod_const_one, mul_one, Finset.prod_const]
  congr
  have hfilter : ((Finset.univ : Finset (Fin K)).filter
      (fun i : Fin K ↦ (i : ℕ) < (j : ℕ))) = Finset.Iio j := by
    ext i
    simp
  rw [hfilter]
  exact Fin.card_Iio j

/-- The projective height of the tuple `1, α, ..., α^(K-1)` is at most
`K h(α)`. -/
lemma logHeight_powerTuple_le
    {F : Type*} [Field F] [Height.AdmissibleAbsValues F]
    (alpha : F) (K : ℕ) :
    Height.logHeight (fun j : Fin K ↦ alpha ^ (j : ℕ)) ≤
      (K : ℝ) * Height.logHeight₁ alpha := by
  let x : Fin K → Fin 2 → F := fun _ ↦ ![alpha, (1 : F)]
  let p : (Fin K → Fin 2) → F := fun I ↦ ∏ i, x i (I i)
  let f : Fin K → (Fin K → Fin 2) := fun j i ↦
    if (i : ℕ) < (j : ℕ) then 0 else 1
  have hx : ∀ i, x i ≠ 0 := by
    intro i hzero
    have h := congrFun hzero 1
    simp [x] at h
  have hp : Height.logHeight p =
      ∑ _i : Fin K, Height.logHeight ![alpha, (1 : F)] := by
    simpa [p, x] using Height.logHeight_fun_prod_eq hx
  have hcomp := Height.logHeight_comp_le f p
  have heq : p ∘ f = fun j : Fin K ↦ alpha ^ (j : ℕ) := by
    funext j
    simpa [p, x, f] using powerTuple_apply_aux alpha K j
  rw [heq] at hcomp
  calc
    Height.logHeight (fun j : Fin K ↦ alpha ^ (j : ℕ)) ≤
        Height.logHeight p := hcomp
    _ = ∑ _i : Fin K, Height.logHeight ![alpha, (1 : F)] := hp
    _ = (K : ℝ) * Height.logHeight₁ alpha := by
      simp [Height.logHeight₁_eq_logHeight]

lemma infinitePlace_intCast_apply
    {F : Type*} [Field F] [NumberField F]
    (v : NumberField.InfinitePlace F) (z : ℤ) :
    v (z : F) = |(z : ℝ)| := by
  simp [Int.norm_eq_abs, ← Int.cast_abs]

/-- The projective height of a bounded tuple of rational integers is
bounded by the field degree times the logarithm of the common bound, with
no factor for the number of coordinates. -/
lemma logHeight_intTuple_le
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (z : ι → ℤ) {C : ℕ} (hC : 1 ≤ C)
    (hz : ∀ i, (z i).natAbs ≤ C) :
    Height.logHeight (fun i ↦ (z i : F)) ≤
      (Module.finrank ℚ F : ℝ) * Real.log C := by
  let x : ι → F := fun i ↦ (z i : F)
  have hlogC : 0 ≤ Real.log (C : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hC)
  by_cases hx : x = 0
  · change Height.logHeight x ≤ _
    rw [hx]
    rw [Height.logHeight_zero]
    exact mul_nonneg
      (by exact_mod_cast Nat.zero_le (Module.finrank ℚ F)) hlogC
  let : Nonempty ι := (Function.ne_iff.mp hx).nonempty
  have hC0 : (0 : ℝ) < C := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC)
  have hinf :
      (∏ v : NumberField.InfinitePlace F,
          (⨆ i, v (x i)) ^ v.mult) ≤
        (C : ℝ) ^ (Module.finrank ℚ F) := by
    calc
      (∏ v : NumberField.InfinitePlace F,
          (⨆ i, v (x i)) ^ v.mult) ≤
          ∏ v : NumberField.InfinitePlace F, (C : ℝ) ^ v.mult := by
        apply Finset.prod_le_prod
        · intro v hv
          exact pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass v _) _
        · intro v hv
          apply pow_le_pow_left₀
            (Real.iSup_nonneg_of_nonnegHomClass v _)
          refine ciSup_le fun i ↦ ?_
          dsimp [x]
          rw [infinitePlace_intCast_apply v (z i)]
          rw [← Int.cast_abs, ← Int.natCast_natAbs]
          exact_mod_cast hz i
      _ = (C : ℝ) ^ ∑ v : NumberField.InfinitePlace F, v.mult := by
        rw [← Finset.prod_pow_eq_pow_sum]
      _ = (C : ℝ) ^ (Module.finrank ℚ F) := by
        rw [NumberField.InfinitePlace.sum_mult_eq]
  have hfin :
      (∏ᶠ v : NumberField.FinitePlace F, ⨆ i, v (x i)) ≤ 1 := by
    calc
      (∏ᶠ v : NumberField.FinitePlace F, ⨆ i, v (x i)) ≤
          ∏ᶠ _v : NumberField.FinitePlace F, (1 : ℝ) := by
        apply finprod_le_finprod (by fun_prop)
          (fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v _)
          (by fun_prop)
        intro v
        refine ciSup_le fun i ↦ ?_
        dsimp [x]
        exact IsNonarchimedean.apply_intCast_le_one (n := z i) v.add_le
      _ = 1 := by simp
  have hmul : Height.mulHeight x ≤
      (C : ℝ) ^ (Module.finrank ℚ F) := by
    rw [NumberField.mulHeight_eq hx]
    calc
      (∏ v : NumberField.InfinitePlace F,
          (⨆ i, v (x i)) ^ v.mult) *
            ∏ᶠ v : NumberField.FinitePlace F, ⨆ i, v (x i) ≤
          (C : ℝ) ^ (Module.finrank ℚ F) * 1 := by
        exact mul_le_mul hinf hfin
          (finprod_nonneg fun v ↦
            Real.iSup_nonneg_of_nonnegHomClass v _)
          (pow_nonneg hC0.le _)
      _ = _ := mul_one _
  rw [Height.logHeight_eq_log_mulHeight]
  calc
    Real.log (Height.mulHeight x) ≤
        Real.log ((C : ℝ) ^ (Module.finrank ℚ F)) :=
      Real.log_le_log (Height.mulHeight_pos x) hmul
    _ = (Module.finrank ℚ F : ℝ) * Real.log C := by
      rw [Real.log_pow]

/-- The projective height of the entire exponent-box monomial tuple only
charges each original generator once per exponent, rather than once per
box point. -/
lemma logHeight_boxMonomialTuple_le
    {F : Type*} [Field F] [NumberField F] {n K : ℕ}
    (alpha : Fin n → F) :
    Height.logHeight (fun k : ExponentBox n K ↦ boxMonomial alpha k) ≤
      (K : ℝ) * ∑ i, Height.logHeight₁ (alpha i) := by
  by_cases hK : K = 0
  · subst K
    simp [ExponentBox, boxMonomial]
  let x : (i : Fin n) → Fin K → F := fun i j ↦ alpha i ^ (j : ℕ)
  have hx : ∀ i, x i ≠ 0 := by
    intro i hzero
    let j : Fin K := ⟨0, Nat.pos_of_ne_zero hK⟩
    have hj := congrFun hzero j
    simp [x, j] at hj
  have heq : Height.logHeight
      (fun k : ExponentBox n K ↦ boxMonomial alpha k) =
      ∑ i, Height.logHeight (x i) := by
    simpa [ExponentBox, boxMonomial, x] using
      (Height.logHeight_fun_prod_eq hx)
  rw [heq]
  calc
    ∑ i, Height.logHeight (x i) ≤
        ∑ i, (K : ℝ) * Height.logHeight₁ (alpha i) := by
      gcongr with i hi
      exact logHeight_powerTuple_le (alpha i) K
    _ = (K : ℝ) * ∑ i, Height.logHeight₁ (alpha i) := by
      rw [Finset.mul_sum]

/-- Structured projective-height bound for a box auxiliary value.  This is
the sharp height scale needed by Baker's auxiliary-function argument. -/
theorem logHeight₁_boxAuxiliaryAlgebraicValue_projective_le
    {F : Type*} [Field F] [NumberField F] {n K C t : ℕ}
    (alpha : Fin n → F) (coeff : ExponentBox n K → ℤ)
    (hK : 0 < K) (hC : 1 ≤ C) (hcoeff : ∀ k, (coeff k).natAbs ≤ C) :
    Height.logHeight₁ (boxAuxiliaryAlgebraicValue alpha coeff t) ≤
      (Module.finrank ℚ F : ℝ) * Real.log (K ^ n + 1 : ℕ) +
        (Module.finrank ℚ F : ℝ) * Real.log C +
        (t : ℝ) * ((K : ℝ) *
          ∑ i, Height.logHeight₁ (alpha i)) := by
  let κ := ExponentBox n K
  let ι := Sum κ Unit
  let mon : κ → F := fun k ↦ boxMonomial alpha k ^ t
  let x : ι → F := Sum.elim mon (fun _ ↦ 1)
  let z : Fin 2 × ι → ℤ := fun ji ↦
    if ji.1 = 0 then Sum.elim coeff (fun _ ↦ 0) ji.2
    else Sum.elim (fun _ ↦ 0) (fun _ ↦ 1) ji.2
  let A : Fin 2 × ι → F := fun ji ↦ (z ji : F)
  have hz : ∀ ji, (z ji).natAbs ≤ C := by
    intro ji
    rcases ji with ⟨j, i⟩
    fin_cases j <;> cases i with
    | inl k => simp [z, hcoeff k, hC]
    | inr u =>
        cases u
        simp [z, hC]
  have hAheight : Height.logHeight A ≤
      (Module.finrank ℚ F : ℝ) * Real.log C := by
    simpa [A] using logHeight_intTuple_le z hC hz
  let kzero : κ := fun _ ↦ ⟨0, hK⟩
  let g : ι → κ := Sum.elim id (fun _ ↦ kzero)
  let f : κ → ι := Sum.inl
  have hmonZero : mon kzero = 1 := by
    simp [mon, kzero, boxMonomial]
  have hxg : mon ∘ g = x := by
    funext i
    cases i with
    | inl k => rfl
    | inr u => simpa [g, x] using hmonZero
  have hxf : x ∘ f = mon := by rfl
  have hxheight : Height.logHeight x = Height.logHeight mon := by
    apply le_antisymm
    · rw [← hxg]
      exact Height.logHeight_comp_le g mon
    · rw [← hxf]
      exact Height.logHeight_comp_le f x
  have hmonheight : Height.logHeight mon ≤
      (t : ℝ) * ((K : ℝ) *
        ∑ i, Height.logHeight₁ (alpha i)) := by
    have hmon : mon = (fun k : κ ↦ boxMonomial alpha k) ^ t := by
      funext k
      simp [mon]
    calc
      Height.logHeight mon =
          (t : ℝ) * Height.logHeight
            (fun k : κ ↦ boxMonomial alpha k) := by
        rw [hmon, Height.logHeight_pow]
      _ ≤ (t : ℝ) * ((K : ℝ) *
          ∑ i, Height.logHeight₁ (alpha i)) := by
        gcongr
        simpa [κ] using logHeight_boxMonomialTuple_le alpha
  have hout : (fun j : Fin 2 ↦ ∑ i, A (j, i) * x i) =
      ![boxAuxiliaryAlgebraicValue alpha coeff t, (1 : F)] := by
    funext j
    fin_cases j
    · simp [A, z, x, mon, ι, κ, boxAuxiliaryAlgebraicValue]
    · simp [A, z, x, mon, ι, κ]
  have hlinear := Height.logHeight_linearMap_apply_le A x
  rw [hout, ← Height.logHeight₁_eq_logHeight] at hlinear
  calc
    Height.logHeight₁ (boxAuxiliaryAlgebraicValue alpha coeff t) ≤
        (Height.totalWeight F : ℝ) * Real.log (Nat.card ι) +
          Height.logHeight A + Height.logHeight x := hlinear
    _ ≤ (Module.finrank ℚ F : ℝ) * Real.log (K ^ n + 1 : ℕ) +
        (Module.finrank ℚ F : ℝ) * Real.log C +
        (t : ℝ) * ((K : ℝ) *
          ∑ i, Height.logHeight₁ (alpha i)) := by
      rw [NumberField.totalWeight_eq_finrank, hxheight]
      have hcard : Nat.card ι = K ^ n + 1 := by
        simp [ι, κ, ExponentBox]
      rw [hcard]
      linarith

/-- Liouville lower bound at the structured projective-height scale. -/
theorem boxAuxiliaryAlgebraicValue_projective_log_norm_lower
    {F : Type*} [Field F] [NumberField F] (phi : F →+* ℂ)
    {n K C t : ℕ} (alpha : Fin n → F)
    (coeff : ExponentBox n K → ℤ)
    (hK : 0 < K) (hC : 1 ≤ C)
    (hcoeff : ∀ k, (coeff k).natAbs ≤ C)
    (hne : boxAuxiliaryAlgebraicValue alpha coeff t ≠ 0) :
    -((Module.finrank ℚ F : ℝ) * Real.log (K ^ n + 1 : ℕ) +
        (Module.finrank ℚ F : ℝ) * Real.log C +
        (t : ℝ) * ((K : ℝ) *
          ∑ i, Height.logHeight₁ (alpha i))) ≤
      Real.log ‖phi (boxAuxiliaryAlgebraicValue alpha coeff t)‖ := by
  have hh := logHeight₁_boxAuxiliaryAlgebraicValue_projective_le
    (t := t) alpha coeff hK hC hcoeff
  have hl := neg_logHeight₁_le_log_norm_embedding phi hne
  linarith

/-- A nonzero coefficient vector with distinct box monomials has a nonzero
sample whose Liouville bound uses the structured projective height. -/
theorem exists_boxAuxiliary_sample_projective_log_norm_lower
    {F : Type*} [Field F] [NumberField F] (phi : F →+* ℂ)
    {n K C : ℕ} (alpha : Fin n → F) (halpha : ∀ i, alpha i ≠ 0)
    (coeff : ExponentBox n K → ℤ)
    (hinj : Function.Injective
      (fun k : ExponentBox n K ↦ boxMonomial alpha k))
    (hcoeff : coeff ≠ 0) (hK : 0 < K)
    (hC : 1 ≤ C) (hcoeffBound : ∀ k, (coeff k).natAbs ≤ C) :
    ∃ t : ℕ, t < K ^ n ∧
      -((Module.finrank ℚ F : ℝ) * Real.log (K ^ n + 1 : ℕ) +
          (Module.finrank ℚ F : ℝ) * Real.log C +
          (t : ℝ) * ((K : ℝ) *
            ∑ i, Height.logHeight₁ (alpha i))) ≤
        Real.log ‖∑ k, (coeff k : ℂ) *
          Complex.exp
            (boxLinearForm (fun i ↦ Complex.log (phi (alpha i))) k * t)‖ := by
  obtain ⟨t, ht⟩ :=
    exists_boxAuxiliaryAlgebraicValue_ne_zero alpha coeff hinj hcoeff
  refine ⟨t, ?_, ?_⟩
  · simpa [ExponentBox] using t.isLt
  · rw [← boxAuxiliaryAlgebraicValue_embedding phi alpha halpha coeff t]
    exact boxAuxiliaryAlgebraicValue_projective_log_norm_lower
      phi alpha coeff hK hC hcoeffBound ht

/-- Liouville lower bound for a nonzero box auxiliary value. -/
theorem boxAuxiliaryAlgebraicValue_log_norm_lower
    {F : Type*} [Field F] [NumberField F] (phi : F →+* ℂ)
    {n K C t : ℕ} (alpha : Fin n → F)
    (coeff : ExponentBox n K → ℤ)
    (hC : 1 ≤ C) (hcoeff : ∀ k, (coeff k).natAbs ≤ C)
    (hne : boxAuxiliaryAlgebraicValue alpha coeff t ≠ 0) :
    -((Module.finrank ℚ F : ℝ) * Real.log ((K ^ n : ℕ) : ℝ) +
        ((K ^ n : ℕ) : ℝ) *
          ((Module.finrank ℚ F : ℝ) * Real.log (C : ℝ) +
            (t : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i)))) ≤
      Real.log ‖phi (boxAuxiliaryAlgebraicValue alpha coeff t)‖ := by
  have hh := logHeight₁_boxAuxiliaryAlgebraicValue_le
    (t := t) alpha coeff hC hcoeff
  have hl := neg_logHeight₁_le_log_norm_embedding phi hne
  linarith

/-- A nonzero coefficient vector with distinct algebraic box monomials has
a nonzero algebraic sample before time `K^n`; at that sample the complex
exponential sum satisfies the explicit Liouville lower bound. -/
theorem exists_boxAuxiliary_sample_log_norm_lower
    {F : Type*} [Field F] [NumberField F] (phi : F →+* ℂ)
    {n K C : ℕ} (alpha : Fin n → F) (halpha : ∀ i, alpha i ≠ 0)
    (coeff : ExponentBox n K → ℤ)
    (hinj : Function.Injective
      (fun k : ExponentBox n K ↦ boxMonomial alpha k))
    (hcoeff : coeff ≠ 0)
    (hC : 1 ≤ C) (hcoeffBound : ∀ k, (coeff k).natAbs ≤ C) :
    ∃ t : ℕ, t < K ^ n ∧
      -((Module.finrank ℚ F : ℝ) * Real.log ((K ^ n : ℕ) : ℝ) +
          ((K ^ n : ℕ) : ℝ) *
            ((Module.finrank ℚ F : ℝ) * Real.log (C : ℝ) +
              (t : ℝ) * ((K : ℝ) *
                ∑ i, Height.logHeight₁ (alpha i)))) ≤
        Real.log ‖∑ k, (coeff k : ℂ) *
          Complex.exp
            (boxLinearForm (fun i ↦ Complex.log (phi (alpha i))) k * t)‖ := by
  obtain ⟨t, ht⟩ :=
    exists_boxAuxiliaryAlgebraicValue_ne_zero alpha coeff hinj hcoeff
  refine ⟨t, ?_, ?_⟩
  · simpa [ExponentBox] using t.isLt
  · rw [← boxAuxiliaryAlgebraicValue_embedding phi alpha halpha coeff t]
    exact boxAuxiliaryAlgebraicValue_log_norm_lower
      phi alpha coeff hC hcoeffBound ht

/-! ## The distinguished-coefficient change of variables -/

/-- If `Λ = ∑ bᵢ ℓᵢ`, multiplying an auxiliary exponent `∑ kᵢ ℓᵢ`
by a distinguished coefficient `bᵢ₀` separates one multiple of `Λ` from
the remaining `n - 1` logarithms.  This exact integer identity is what makes
the moment equations in Baker's auxiliary-function construction integral. -/
theorem distinguishedCoefficient_linearForm_identity
    {n : ℕ} (ell : Fin n → ℂ) (b k : Fin n → ℤ) (i0 : Fin n) :
    (b i0 : ℂ) * ∑ i, (k i : ℂ) * ell i =
      (k i0 : ℂ) * ∑ i, (b i : ℂ) * ell i +
        ∑ i ∈ (Finset.univ.erase i0),
          (((b i0 * k i - k i0 * b i : ℤ) : ℂ) * ell i) := by
  rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun i ↦ (k i : ℂ) * ell i) (Finset.mem_univ i0)]
  rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun i ↦ (b i : ℂ) * ell i) (Finset.mem_univ i0)]
  have hcomp :
      (∑ i ∈ (Finset.univ.erase i0),
          (((b i0 * k i - k i0 * b i : ℤ) : ℂ) * ell i)) =
        (b i0 : ℂ) *
            ∑ i ∈ (Finset.univ.erase i0), (k i : ℂ) * ell i -
          (k i0 : ℂ) *
            ∑ i ∈ (Finset.univ.erase i0), (b i : ℂ) * ell i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  rw [hcomp]
  ring

/-! ## Integral moment cancellation -/

/-- Vanishing of every degree-`p` monomial moment implies vanishing after
substitution into an arbitrary linear form.  This is the multinomial bridge
from the integer matrix produced by Siegel's lemma to the analytic auxiliary
function. -/
theorem sum_coeff_mul_linearForm_pow_eq_zero_of_moments
    {R : Type*} [CommRing R] {kappa iota : Type*}
    [Fintype kappa] [Fintype iota] [DecidableEq iota]
    (coeff : kappa → R) (q : kappa → iota → R)
    (ell : iota → R) (p : ℕ)
    (h : ∀ u ∈ Finset.piAntidiag (Finset.univ : Finset iota) p,
      ∑ k, coeff k * ∏ i, q k i ^ u i = 0) :
    ∑ k, coeff k * (∑ i, q k i * ell i) ^ p = 0 := by
  simp_rw [Finset.sum_pow_eq_sum_piAntidiag]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro u hu
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  calc
    ∑ x, coeff x *
        ((Nat.multinomial Finset.univ u : R) *
          ((∏ i, q x i ^ u i) * ∏ i, ell i ^ u i)) =
      (Nat.multinomial Finset.univ u : R) * (∏ i, ell i ^ u i) *
        ∑ x, coeff x * ∏ i, q x i ^ u i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = 0 := by rw [h u hu, mul_zero]

/-- The explicit remainder after extracting the terms below order `T` in a
binomial expansion. -/
def binomialRemainder
    {R : Type*} [CommRing R] {kappa : Type*} [Fintype kappa]
    (coeff a r : kappa → R) (Lambda : R) (s T : ℕ) : R :=
  ∑ q ∈ (Finset.range (s + 1)).filter (T ≤ ·),
    (s.choose q : R) * Lambda ^ (q - T) *
      ∑ k, coeff k * a k ^ q * r k ^ (s - q)

/-- If all binomial moments below order `T` vanish, the corresponding sum of
`s`-th powers is `Λ^T` times the explicit binomial remainder. -/
theorem sum_eq_pow_mul_binomialRemainder_of_moments
    {R : Type*} [CommRing R] {kappa : Type*} [Fintype kappa]
    (coeff a r : kappa → R) (Lambda : R) (s T : ℕ)
    (h : ∀ q ∈ Finset.range (s + 1), q < T →
      ∑ k, coeff k * a k ^ q * r k ^ (s - q) = 0) :
    ∑ k, coeff k * (a k * Lambda + r k) ^ s =
      Lambda ^ T * binomialRemainder coeff a r Lambda s T := by
  simp_rw [add_pow]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.range (s + 1)) (T ≤ ·)]
  have hlow : ∑ q ∈ (Finset.range (s + 1)).filter (¬ T ≤ ·),
      ∑ k, coeff k * ((a k * Lambda) ^ q * r k ^ (s - q) *
        (s.choose q : R)) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    rw [Finset.mem_filter] at hq
    have hm := h q hq.1 (by omega)
    calc
      ∑ k, coeff k * ((a k * Lambda) ^ q * r k ^ (s - q) *
        (s.choose q : R)) =
          (s.choose q : R) * Lambda ^ q *
            ∑ k, coeff k * a k ^ q * r k ^ (s - q) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              rw [mul_pow]
              ring
      _ = 0 := by rw [hm, mul_zero]
  rw [hlow, add_zero]
  dsimp [binomialRemainder]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mem_filter] at hq
  have hpow : Lambda ^ q = Lambda ^ T * Lambda ^ (q - T) := by
    rw [← pow_add, Nat.add_sub_of_le hq.2]
  calc
    ∑ k, coeff k * ((a k * Lambda) ^ q * r k ^ (s - q) *
      (s.choose q : R)) =
        (s.choose q : R) * Lambda ^ q *
          ∑ k, coeff k * a k ^ q * r k ^ (s - q) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            rw [mul_pow]
            ring
    _ = Lambda ^ T *
        ((s.choose q : R) * Lambda ^ (q - T) *
          ∑ k, coeff k * a k ^ q * r k ^ (s - q)) := by
            rw [hpow]
            ring

/-- Divisibility-only wrapper around
`sum_eq_pow_mul_binomialRemainder_of_moments`. -/
theorem exists_eq_pow_mul_of_binomialMoments
    {R : Type*} [CommRing R] {kappa : Type*} [Fintype kappa]
    (coeff a r : kappa → R) (Lambda : R) (s T : ℕ)
    (h : ∀ q ∈ Finset.range (s + 1), q < T →
      ∑ k, coeff k * a k ^ q * r k ^ (s - q) = 0) :
    ∃ Q : R,
      ∑ k, coeff k * (a k * Lambda + r k) ^ s = Lambda ^ T * Q :=
  ⟨binomialRemainder coeff a r Lambda s T,
    sum_eq_pow_mul_binomialRemainder_of_moments coeff a r Lambda s T h⟩

/-- The binomial remainder has the elementary Archimedean bound required in
the extrapolation step.  The factor `2^s` is the sum of the binomial
coefficients; no division by `Λ` occurs because only powers `q - T` with
`q ≥ T` appear. -/
theorem binomialRemainder_norm_le
    {kappa : Type*} [Fintype kappa]
    (coeff a r : kappa → ℂ) (Lambda : ℂ) (s T : ℕ)
    {C M : ℝ}
    (hC : 0 ≤ C) (hM : 1 ≤ M)
    (hcoeff : ∀ k, ‖coeff k‖ ≤ C)
    (ha : ∀ k, ‖a k‖ ≤ M)
    (hr : ∀ k, ‖r k‖ ≤ M)
    (hLambda : ‖Lambda‖ ≤ 1) :
    ‖binomialRemainder coeff a r Lambda s T‖ ≤
      (Fintype.card kappa : ℝ) * C * M ^ s * (2 : ℝ) ^ s := by
  rw [binomialRemainder]
  calc
    ‖∑ q ∈ (Finset.range (s + 1)).filter (T ≤ ·),
        (s.choose q : ℂ) * Lambda ^ (q - T) *
          ∑ k, coeff k * a k ^ q * r k ^ (s - q)‖ ≤
        ∑ q ∈ (Finset.range (s + 1)).filter (T ≤ ·),
          ‖(s.choose q : ℂ) * Lambda ^ (q - T) *
            ∑ k, coeff k * a k ^ q * r k ^ (s - q)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ (Finset.range (s + 1)).filter (T ≤ ·),
          (s.choose q : ℝ) * ((Fintype.card kappa : ℝ) * C * M ^ s) := by
      gcongr with q hq
      rw [Finset.mem_filter, Finset.mem_range] at hq
      rw [norm_mul, norm_mul, norm_natCast, norm_pow]
      have hLpow : ‖Lambda‖ ^ (q - T) ≤ 1 := by
        simpa using pow_le_one₀ (norm_nonneg Lambda) hLambda
      have hinner : ‖∑ k, coeff k * a k ^ q * r k ^ (s - q)‖ ≤
          (Fintype.card kappa : ℝ) * C * M ^ s := by
        calc
          ‖∑ k, coeff k * a k ^ q * r k ^ (s - q)‖ ≤
              ∑ k, ‖coeff k * a k ^ q * r k ^ (s - q)‖ :=
            norm_sum_le _ _
          _ ≤ ∑ _k : kappa, C * M ^ s := by
            gcongr with k hk
            rw [norm_mul, norm_mul, norm_pow, norm_pow]
            calc
              ‖coeff k‖ * ‖a k‖ ^ q * ‖r k‖ ^ (s - q) ≤
                  C * M ^ q * M ^ (s - q) := by
                    gcongr
                    · exact hcoeff k
                    · exact ha k
                    · exact hr k
              _ = C * M ^ s := by
                rw [mul_assoc, ← pow_add,
                  Nat.add_sub_of_le (Nat.le_of_lt_succ hq.1)]
          _ = (Fintype.card kappa : ℝ) * (C * M ^ s) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
          _ = (Fintype.card kappa : ℝ) * C * M ^ s := by ring
      calc
        (s.choose q : ℝ) * ‖Lambda‖ ^ (q - T) *
            ‖∑ k, coeff k * a k ^ q * r k ^ (s - q)‖ ≤
          (s.choose q : ℝ) * 1 *
            ((Fintype.card kappa : ℝ) * C * M ^ s) := by gcongr
        _ = (s.choose q : ℝ) *
            ((Fintype.card kappa : ℝ) * C * M ^ s) := by ring
    _ = (∑ q ∈ (Finset.range (s + 1)).filter (T ≤ ·),
          (s.choose q : ℝ)) *
          ((Fintype.card kappa : ℝ) * C * M ^ s) := by
      rw [Finset.sum_mul]
    _ ≤ ((2 : ℝ) ^ s) *
          ((Fintype.card kappa : ℝ) * C * M ^ s) := by
      gcongr
      calc
        ∑ q ∈ (Finset.range (s + 1)).filter (T ≤ ·),
            (s.choose q : ℝ) ≤
            ∑ q ∈ Finset.range (s + 1), (s.choose q : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro i hi hnot
            exact_mod_cast Nat.zero_le (s.choose i)
        _ = (2 : ℝ) ^ s := by
          exact_mod_cast Nat.sum_range_choose s
    _ = (Fintype.card kappa : ℝ) * C * M ^ s * (2 : ℝ) ^ s := by
      ring

/-- Rectangular moment cancellation is sufficient for the `Λ^T`
factorization.  The `q`-coordinate records the distinguished exponent and
the multi-index records the remaining transformed coordinates. -/
theorem sum_eq_pow_mul_binomialRemainder_of_rectangular_moments
    {R : Type*} [CommRing R] {kappa iota : Type*}
    [Fintype kappa] [Fintype iota] [DecidableEq iota]
    (coeff a : kappa → R) (r : kappa → iota → R)
    (ell : iota → R) (Lambda : R) (s T S : ℕ)
    (hs : s < S)
    (h : ∀ q, q < T → ∀ p, p < S →
      ∀ u ∈ Finset.piAntidiag (Finset.univ : Finset iota) p,
        ∑ k, coeff k * a k ^ q * ∏ i, r k i ^ u i = 0) :
    ∑ k, coeff k * (a k * Lambda + ∑ i, r k i * ell i) ^ s =
      Lambda ^ T * binomialRemainder coeff a
        (fun k ↦ ∑ i, r k i * ell i) Lambda s T := by
  apply sum_eq_pow_mul_binomialRemainder_of_moments
  intro q hqs hqT
  apply sum_coeff_mul_linearForm_pow_eq_zero_of_moments
  intro u hu
  simpa [mul_assoc] using h q hqT (s - q) (by omega) u hu

/-- The corresponding factorization for a derivative of the auxiliary
exponential sum.  A change of variables of the form
`b₀ Lₖ = aₖ Λ + rₖ⋅ℓ`, together with rectangular integral moments,
forces the scaled derivative to contain the factor `Λ^T`. -/
theorem auxiliaryDerivative_eq_pow_mul_binomialRemainder
    {κ iota : Type*} [Fintype κ] [Fintype iota] [DecidableEq iota]
    (c L : κ → ℂ) (b0 Lambda : ℂ)
    (a : κ → ℂ) (r : κ → iota → ℂ)
    (ell : iota → ℂ) (s T S : ℕ)
    (hs : s < S)
    (hcoord : ∀ k, b0 * L k = a k * Lambda + ∑ i, r k i * ell i)
    (hmoment : ∀ q, q < T → ∀ p, p < S →
      ∀ u ∈ Finset.piAntidiag (Finset.univ : Finset iota) p,
        ∑ k, c k * a k ^ q * ∏ i, r k i ^ u i = 0) :
    b0 ^ s * iteratedDeriv s (auxiliaryExponentialSum L c) 0 =
      Lambda ^ T * binomialRemainder c a
        (fun k ↦ ∑ i, r k i * ell i) Lambda s T := by
  rw [iteratedDeriv_auxiliaryExponentialSum]
  simp only [mul_zero, Complex.exp_zero, mul_one]
  rw [Finset.mul_sum]
  have hrewrite :
      ∑ k, b0 ^ s * (c k * L k ^ s) =
        ∑ k, c k * (a k * Lambda + ∑ i, r k i * ell i) ^ s := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [← hcoord k, mul_pow]
    ring
  rw [hrewrite]
  exact sum_eq_pow_mul_binomialRemainder_of_rectangular_moments
    c a r ell Lambda s T S hs hmoment

/-- Quantitative derivative estimate obtained by combining the exact
factorization with the Archimedean remainder bound. -/
theorem auxiliaryDerivative_norm_le_of_rectangular_moments
    {κ iota : Type*} [Fintype κ] [Fintype iota] [DecidableEq iota]
    (c L : κ → ℂ) (b0 Lambda : ℂ)
    (a : κ → ℂ) (r : κ → iota → ℂ)
    (ell : iota → ℂ) (s T S : ℕ) {C M : ℝ}
    (hs : s < S) (hC : 0 ≤ C) (hM : 1 ≤ M)
    (hc : ∀ k, ‖c k‖ ≤ C) (ha : ∀ k, ‖a k‖ ≤ M)
    (hr : ∀ k, ‖∑ i, r k i * ell i‖ ≤ M)
    (hLambda : ‖Lambda‖ ≤ 1)
    (hcoord : ∀ k, b0 * L k = a k * Lambda + ∑ i, r k i * ell i)
    (hmoment : ∀ q, q < T → ∀ p, p < S →
      ∀ u ∈ Finset.piAntidiag (Finset.univ : Finset iota) p,
        ∑ k, c k * a k ^ q * ∏ i, r k i ^ u i = 0) :
    ‖b0‖ ^ s * ‖iteratedDeriv s (auxiliaryExponentialSum L c) 0‖ ≤
      ‖Lambda‖ ^ T *
        ((Fintype.card κ : ℝ) * C * M ^ s * (2 : ℝ) ^ s) := by
  have heq := auxiliaryDerivative_eq_pow_mul_binomialRemainder
    c L b0 Lambda a r ell s T S hs hcoord hmoment
  have hrem := binomialRemainder_norm_le c a
    (fun k ↦ ∑ i, r k i * ell i) Lambda s T hC hM hc ha hr hLambda
  have hnorm := congrArg norm heq
  rw [norm_mul, norm_pow, norm_mul, norm_pow] at hnorm
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg _) _)
  simpa using hrem

/-! ## Taylor bounds for auxiliary exponential sums -/

/-- A uniform Taylor-remainder estimate for a finite auxiliary exponential
sum.  It is a direct summation of `Complex.exp_bound'` and is stated in
terms of the iterated derivatives, so it can be combined immediately with
`auxiliaryDerivative_norm_le_of_rectangular_moments`. -/
theorem auxiliaryExponentialSum_taylor_remainder_norm_le
    {κ : Type*} [Fintype κ] {S : ℕ}
    (L c : κ → ℂ) (z : ℂ) {C R : ℝ}
    (hC : 0 ≤ C)
    (hc : ∀ i, ‖c i‖ ≤ C) (hL : ∀ i, ‖L i‖ ≤ R)
    (hsmall : R * ‖z‖ / (S + 1 : ℕ) ≤ 1 / 2) :
    ‖auxiliaryExponentialSum L c z -
        ∑ s ∈ Finset.range S,
          iteratedDeriv s (auxiliaryExponentialSum L c) 0 *
            z ^ s / (s.factorial : ℂ)‖ ≤
      (Fintype.card κ : ℝ) * C *
        ((R * ‖z‖) ^ S / S.factorial * 2) := by
  have hrewrite :
      auxiliaryExponentialSum L c z -
          ∑ s ∈ Finset.range S,
            iteratedDeriv s (auxiliaryExponentialSum L c) 0 *
              z ^ s / (s.factorial : ℂ) =
        ∑ i, c i * (Complex.exp (L i * z) -
          ∑ s ∈ Finset.range S,
            (L i * z) ^ s / (s.factorial : ℂ)) := by
    change (∑ i, c i * Complex.exp (L i * z)) - _ = _
    simp_rw [iteratedDeriv_auxiliaryExponentialSum]
    simp only [mul_zero, Complex.exp_zero, mul_one]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    congr 1
    calc
      ∑ s ∈ Finset.range S, (∑ i, c i * L i ^ s) * z ^ s /
          (s.factorial : ℂ) =
          ∑ s ∈ Finset.range S, ∑ i,
            c i * (L i * z) ^ s / (s.factorial : ℂ) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.sum_mul, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_pow]
        ring
      _ = ∑ i, ∑ s ∈ Finset.range S,
          c i * (L i * z) ^ s / (s.factorial : ℂ) := by
        rw [Finset.sum_comm]
      _ = ∑ i, c i * ∑ s ∈ Finset.range S,
          (L i * z) ^ s / (s.factorial : ℂ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        ring
  rw [hrewrite]
  calc
    ‖∑ i, c i * (Complex.exp (L i * z) -
        ∑ s ∈ Finset.range S,
          (L i * z) ^ s / (s.factorial : ℂ))‖ ≤
      ∑ i, ‖c i * (Complex.exp (L i * z) -
        ∑ s ∈ Finset.range S,
          (L i * z) ^ s / (s.factorial : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : κ, C * ((R * ‖z‖) ^ S / S.factorial * 2) := by
      gcongr with i hi
      rw [norm_mul]
      have hLi : ‖L i * z‖ / (S + 1 : ℕ) ≤ 1 / 2 := by
        calc
          ‖L i * z‖ / (S + 1 : ℕ) =
              ‖L i‖ * ‖z‖ / (S + 1 : ℕ) := by rw [norm_mul]
          _ ≤ R * ‖z‖ / (S + 1 : ℕ) := by
            gcongr
            exact hL i
          _ ≤ 1 / 2 := hsmall
      have hexp := Complex.exp_bound' hLi
      calc
        ‖c i‖ * ‖Complex.exp (L i * z) -
            ∑ s ∈ Finset.range S,
              (L i * z) ^ s / (s.factorial : ℂ)‖ ≤
          C * (‖L i * z‖ ^ S / S.factorial * 2) := by
            gcongr
            exact hc i
        _ ≤ C * ((R * ‖z‖) ^ S / S.factorial * 2) := by
          gcongr
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hL i) (norm_nonneg z)
    _ = (Fintype.card κ : ℝ) *
        (C * ((R * ‖z‖) ^ S / S.factorial * 2)) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ = (Fintype.card κ : ℝ) * C *
        ((R * ‖z‖) ^ S / S.factorial * 2) := by
      ring

/-- A power below order `S` is bounded by the larger of `1` and the
`S`-th power. -/
lemma pow_le_max_one_pow {x : ℝ} {s S : ℕ}
    (hx : 0 ≤ x) (hs : s ≤ S) : x ^ s ≤ max 1 (x ^ S) := by
  rcases le_total x 1 with hx1 | h1x
  · exact (pow_le_one₀ hx hx1).trans (le_max_left _ _)
  · exact (pow_le_pow_right₀ h1x hs).trans (le_max_right _ _)

/-- Evaluation bound obtained from the small initial derivatives and the
Taylor remainder.  This is the local analytic extrapolation inequality:
all dependence on the logarithmic form occurs through `‖Λ‖^T`. -/
theorem auxiliaryExponentialSum_norm_le_of_rectangular_moments
    {κ iota : Type*} [Fintype κ] [Fintype iota] [DecidableEq iota]
    (c L : κ → ℂ) (b0 Lambda : ℂ)
    (a : κ → ℂ) (r : κ → iota → ℂ)
    (ell : iota → ℂ) (z : ℂ) (T S : ℕ) {C M R : ℝ}
    (hC : 0 ≤ C) (hM : 1 ≤ M) (hb0 : 1 ≤ ‖b0‖)
    (hc : ∀ k, ‖c k‖ ≤ C) (ha : ∀ k, ‖a k‖ ≤ M)
    (hr : ∀ k, ‖∑ i, r k i * ell i‖ ≤ M)
    (hLambda : ‖Lambda‖ ≤ 1) (hL : ∀ i, ‖L i‖ ≤ R)
    (hsmall : R * ‖z‖ / (S + 1 : ℕ) ≤ 1 / 2)
    (hcoord : ∀ k, b0 * L k = a k * Lambda + ∑ i, r k i * ell i)
    (hmoment : ∀ q, q < T → ∀ p, p < S →
      ∀ u ∈ Finset.piAntidiag (Finset.univ : Finset iota) p,
        ∑ k, c k * a k ^ q * ∏ i, r k i ^ u i = 0) :
    ‖auxiliaryExponentialSum L c z‖ ≤
      (S : ℝ) *
          (‖Lambda‖ ^ T * ((Fintype.card κ : ℝ) * C)) *
          max 1 ((2 * M * ‖z‖) ^ S) +
        (Fintype.card κ : ℝ) * C *
          ((R * ‖z‖) ^ S / S.factorial * 2) := by
  let F : ℂ → ℂ := auxiliaryExponentialSum L c
  let P : ℂ := ∑ s ∈ Finset.range S,
    iteratedDeriv s F 0 * z ^ s / (s.factorial : ℂ)
  have htail : ‖F z - P‖ ≤
      (Fintype.card κ : ℝ) * C *
        ((R * ‖z‖) ^ S / S.factorial * 2) := by
    simpa [F, P] using auxiliaryExponentialSum_taylor_remainder_norm_le
      L c z hC hc hL hsmall
  have hterm : ∀ s ∈ Finset.range S,
      ‖iteratedDeriv s F 0 * z ^ s / (s.factorial : ℂ)‖ ≤
        (‖Lambda‖ ^ T * ((Fintype.card κ : ℝ) * C)) *
          max 1 ((2 * M * ‖z‖) ^ S) := by
    intro s hs
    have hsS : s < S := Finset.mem_range.mp hs
    have hdscaled := auxiliaryDerivative_norm_le_of_rectangular_moments
      c L b0 Lambda a r ell s T S (C := C) (M := M)
        hsS hC hM hc ha hr hLambda hcoord hmoment
    have hbone : 1 ≤ ‖b0‖ ^ s := one_le_pow₀ hb0
    have hd : ‖iteratedDeriv s F 0‖ ≤
        ‖Lambda‖ ^ T *
          ((Fintype.card κ : ℝ) * C * M ^ s * 2 ^ s) := by
      dsimp [F]
      calc
        ‖iteratedDeriv s (auxiliaryExponentialSum L c) 0‖ ≤
            ‖b0‖ ^ s *
              ‖iteratedDeriv s (auxiliaryExponentialSum L c) 0‖ := by
          nth_rewrite 1 [← one_mul
            ‖iteratedDeriv s (auxiliaryExponentialSum L c) 0‖]
          exact mul_le_mul_of_nonneg_right hbone (norm_nonneg _)
        _ ≤ _ := hdscaled
    rw [norm_div, norm_mul, norm_pow, norm_natCast]
    calc
      ‖iteratedDeriv s F 0‖ * ‖z‖ ^ s / (s.factorial : ℝ) ≤
          (‖Lambda‖ ^ T *
              ((Fintype.card κ : ℝ) * C * M ^ s * 2 ^ s)) *
            ‖z‖ ^ s / (s.factorial : ℝ) := by gcongr
      _ ≤ (‖Lambda‖ ^ T * ((Fintype.card κ : ℝ) * C)) *
            (2 * M * ‖z‖) ^ s := by
        have hfac : (1 : ℝ) ≤ s.factorial := by
          exact_mod_cast Nat.factorial_pos s
        calc
          (‖Lambda‖ ^ T *
              ((Fintype.card κ : ℝ) * C * M ^ s * 2 ^ s)) *
                ‖z‖ ^ s / (s.factorial : ℝ) ≤
              (‖Lambda‖ ^ T *
                  ((Fintype.card κ : ℝ) * C * M ^ s * 2 ^ s)) *
                ‖z‖ ^ s := by
            rw [div_le_iff₀ (by positivity : (0 : ℝ) < s.factorial)]
            nlinarith [mul_nonneg
              (mul_nonneg (pow_nonneg (norm_nonneg Lambda) T)
              (mul_nonneg (Nat.cast_nonneg (Fintype.card κ)) hC))
              (mul_nonneg (pow_nonneg (by positivity : 0 ≤ M) s)
                (mul_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ 2) s)
                  (pow_nonneg (norm_nonneg z) s)))]
          _ = (‖Lambda‖ ^ T * ((Fintype.card κ : ℝ) * C)) *
                (2 * M * ‖z‖) ^ s := by
            rw [mul_pow]
            ring
      _ ≤ (‖Lambda‖ ^ T * ((Fintype.card κ : ℝ) * C)) *
            max 1 ((2 * M * ‖z‖) ^ S) := by
        gcongr
        exact pow_le_max_one_pow (by positivity) (Nat.le_of_lt hsS)
  have hP : ‖P‖ ≤
      (S : ℝ) *
        ((‖Lambda‖ ^ T * ((Fintype.card κ : ℝ) * C)) *
        max 1 ((2 * M * ‖z‖) ^ S)) := by
    dsimp [P]
    calc
      ‖∑ s ∈ Finset.range S,
          iteratedDeriv s F 0 * z ^ s / (s.factorial : ℂ)‖ ≤
          ∑ s ∈ Finset.range S,
            ‖iteratedDeriv s F 0 * z ^ s / (s.factorial : ℂ)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _s ∈ Finset.range S,
          ((‖Lambda‖ ^ T * ((Fintype.card κ : ℝ) * C)) *
            max 1 ((2 * M * ‖z‖) ^ S)) := by
        gcongr with s hs
        exact hterm s hs
      _ = (S : ℝ) *
          ((‖Lambda‖ ^ T * ((Fintype.card κ : ℝ) * C)) *
          max 1 ((2 * M * ‖z‖) ^ S)) := by simp
  calc
    ‖F z‖ = ‖P + (F z - P)‖ := by ring_nf
    _ ≤ ‖P‖ + ‖F z - P‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [mul_assoc]
      exact add_le_add hP htail

/-! ## Exponent-box analytic wrapper -/

/-- The local analytic estimate specialized to the distinguished change of
variables on an exponent box.  Its moment hypotheses are integral, exactly
as returned by `exists_box_rectangular_moment_coefficients`; all casts to
the complex analytic identity are discharged here. -/
theorem boxAuxiliaryExponentialSum_norm_le_of_rectangular_moments
    {r K T S : ℕ} (ell : Fin (r + 1) → ℂ)
    (b : Fin (r + 1) → ℤ) (coeff : ExponentBox (r + 1) K → ℤ)
    (z : ℂ) {C M R : ℝ}
    (hC : 0 ≤ C) (hM : 1 ≤ M) (hb0 : 1 ≤ ‖(b 0 : ℂ)‖)
    (hcoeff : ∀ k, ‖(coeff k : ℂ)‖ ≤ C)
    (ha : ∀ k : ExponentBox (r + 1) K,
      ‖(boxDistinguishedExponent k : ℂ)‖ ≤ M)
    (hr : ∀ k : ExponentBox (r + 1) K, ‖∑ i : Fin r,
      (boxTransformedExponent b k i : ℂ) * ell i.succ‖ ≤ M)
    (hLambda : ‖∑ i, (b i : ℂ) * ell i‖ ≤ 1)
    (hL : ∀ k : ExponentBox (r + 1) K,
      ‖boxLinearForm ell k‖ ≤ R)
    (hsmall : R * ‖z‖ / (S + 1 : ℕ) ≤ 1 / 2)
    (hmoment : ∀ q, q < T → ∀ p, p < S →
      ∀ u ∈ Finset.piAntidiag (Finset.univ : Finset (Fin r)) p,
        ∑ k, coeff k * boxDistinguishedExponent k ^ q *
          ∏ i, boxTransformedExponent b k i ^ u i = 0) :
    ‖∑ k, (coeff k : ℂ) *
        Complex.exp (boxLinearForm ell k * z)‖ ≤
      (S : ℝ) *
          (‖∑ i, (b i : ℂ) * ell i‖ ^ T *
            ((K ^ (r + 1) : ℕ) * C)) *
          max 1 ((2 * M * ‖z‖) ^ S) +
        ((K ^ (r + 1) : ℕ) : ℝ) * C *
          ((R * ‖z‖) ^ S / S.factorial * 2) := by
  let Lambda : ℂ := ∑ i, (b i : ℂ) * ell i
  have hmomentC : ∀ q, q < T → ∀ p, p < S →
      ∀ u ∈ Finset.piAntidiag (Finset.univ : Finset (Fin r)) p,
        ∑ k, (coeff k : ℂ) *
            (boxDistinguishedExponent k : ℂ) ^ q *
            ∏ i, (boxTransformedExponent b k i : ℂ) ^ u i = 0 := by
    intro q hq p hp u hu
    exact_mod_cast hmoment q hq p hp u hu
  have h := auxiliaryExponentialSum_norm_le_of_rectangular_moments
    (fun k ↦ (coeff k : ℂ)) (fun k ↦ boxLinearForm ell k)
    (b 0 : ℂ) Lambda
    (fun k ↦ (boxDistinguishedExponent k : ℂ))
    (fun k i ↦ (boxTransformedExponent b k i : ℂ))
    (fun i ↦ ell i.succ) z T S hC hM hb0 hcoeff ha hr
    (by simpa [Lambda] using hLambda) hL hsmall
    (fun k ↦ by
      simpa [Lambda] using box_distinguished_linearForm_identity ell b k)
    hmomentC
  simpa [auxiliaryExponentialSum, ExponentBox] using h

/-! ## Algebraic multipoint moment systems -/

/-- Rows for a rectangular moment system imposed at several integer nodes. -/
abbrev MultipointRectangularMomentIndex (iota : Type*) (A T S : ℕ) :=
  Fin A × RectangularMomentIndex iota T S

/-- The algebraic moment matrix whose rows record a node, a distinguished
power, and a rectangular multi-index in the remaining coordinates. -/
def multipointRectangularMomentMatrix
    {F kappa iota : Type*} [CommRing F]
    [Fintype kappa] [Fintype iota]
    (beta : kappa → F) (a : kappa → ℤ) (r : kappa → iota → ℤ)
    (A T S : ℕ) :
    Matrix (MultipointRectangularMomentIndex iota A T S) kappa F :=
  fun hqu k ↦ beta k ^ (hqu.1 : ℕ) * (a k : F) ^ (hqu.2.1 : ℕ) *
    ∏ i, (r k i : F) ^ (hqu.2.2 i : ℕ)

/-- Coordinate form of the kernel of the multipoint moment matrix. -/
lemma multipointRectangularMomentMatrix_kernel_iff
    {F kappa iota : Type*} [CommRing F]
    [Fintype kappa] [Fintype iota]
    (beta : kappa → F) (a : kappa → ℤ) (r : kappa → iota → ℤ)
    (A T S : ℕ) (c : kappa → ℤ) :
    (multipointRectangularMomentMatrix beta a r A T S).mulVec
        (fun k ↦ (c k : F)) = 0 ↔
      ∀ h : Fin A, ∀ q : Fin T, ∀ u : iota → Fin S,
        ∑ k, (c k : F) * beta k ^ (h : ℕ) * (a k : F) ^ (q : ℕ) *
          ∏ i, (r k i : F) ^ (u i : ℕ) = 0 := by
  constructor
  · intro hker h q u
    have hz := congrFun hker (h, q, u)
    simpa [multipointRectangularMomentMatrix, Matrix.mulVec, dotProduct,
      mul_assoc, mul_comm, mul_left_comm] using hz
  · intro h
    funext hqu
    rcases hqu with ⟨hnode, q, u⟩
    simpa [multipointRectangularMomentMatrix, Matrix.mulVec, dotProduct,
      mul_assoc, mul_comm, mul_left_comm] using h hnode q u

/-- A common height bound for every entry of the algebraic multipoint
matrix.  The node powers cost `A * H`; all integer moment coordinates are
absorbed by one bound `V`. -/
theorem logHeight₁_multipointRectangularMomentMatrix_le
    {F kappa iota : Type*} [Field F] [NumberField F]
    [Fintype kappa] [Fintype iota]
    (beta : kappa → F) (a : kappa → ℤ) (r : kappa → iota → ℤ)
    (A T S : ℕ) {H V : ℝ} (hV : 1 ≤ V)
    (hbeta : ∀ k, Height.logHeight₁ (beta k) ≤ H)
    (ha : ∀ k, ‖a k‖ ≤ V) (hr : ∀ k i, ‖r k i‖ ≤ V) :
    ∀ row k,
      Height.logHeight₁
          (multipointRectangularMomentMatrix beta a r A T S row k) ≤
        (A : ℝ) * H +
          ((T + Fintype.card iota * S : ℕ) : ℝ) *
            ((Module.finrank ℚ F : ℝ) * Real.log V) := by
  intro row k
  rcases row with ⟨h, q, u⟩
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg hV
  have haHeight : Height.logHeight₁ (a k : F) ≤
      (Module.finrank ℚ F : ℝ) * Real.log V := by
    refine (logHeight₁_intCast_le (K := F) (a k)).trans ?_
    have hmax : ((max 1 (a k).natAbs : ℕ) : ℝ) ≤ V := by
      rw [Nat.cast_max]
      exact max_le (by simpa using hV)
        (by simpa [Int.norm_eq_abs] using ha k)
    gcongr
  have hrHeight : ∀ i, Height.logHeight₁ (r k i : F) ≤
      (Module.finrank ℚ F : ℝ) * Real.log V := by
    intro i
    refine (logHeight₁_intCast_le (K := F) (r k i)).trans ?_
    have hmax : ((max 1 (r k i).natAbs : ℕ) : ℝ) ≤ V := by
      rw [Nat.cast_max]
      exact max_le (by simpa using hV)
        (by simpa [Int.norm_eq_abs] using hr k i)
    gcongr
  have hprod : Height.logHeight₁
      (∏ i, (r k i : F) ^ (u i : ℕ)) ≤
        ((Fintype.card iota * S : ℕ) : ℝ) *
          ((Module.finrank ℚ F : ℝ) * Real.log V) := by
    calc
      Height.logHeight₁ (∏ i, (r k i : F) ^ (u i : ℕ)) ≤
          ∑ i, Height.logHeight₁ ((r k i : F) ^ (u i : ℕ)) :=
        Height.logHeight₁_prod_le Finset.univ _
      _ = ∑ i, (u i : ℕ) * Height.logHeight₁ (r k i : F) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Height.logHeight₁_pow]
      _ ≤ ∑ _i : iota, (S : ℝ) *
          ((Module.finrank ℚ F : ℝ) * Real.log V) := by
        gcongr with i hi
        · exact_mod_cast (u i).isLt.le
        · exact hrHeight i
      _ = ((Fintype.card iota * S : ℕ) : ℝ) *
          ((Module.finrank ℚ F : ℝ) * Real.log V) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        push_cast
        ring
  simp only [multipointRectangularMomentMatrix]
  calc
    Height.logHeight₁
        (beta k ^ (h : ℕ) * (a k : F) ^ (q : ℕ) *
          ∏ i, (r k i : F) ^ (u i : ℕ)) ≤
      Height.logHeight₁ (beta k ^ (h : ℕ)) +
        Height.logHeight₁ ((a k : F) ^ (q : ℕ)) +
          Height.logHeight₁ (∏ i, (r k i : F) ^ (u i : ℕ)) := by
      calc
        _ ≤ Height.logHeight₁ (beta k ^ (h : ℕ) * (a k : F) ^ (q : ℕ)) +
            Height.logHeight₁ (∏ i, (r k i : F) ^ (u i : ℕ)) :=
          Height.logHeight₁_mul_le _ _
        _ ≤ (Height.logHeight₁ (beta k ^ (h : ℕ)) +
            Height.logHeight₁ ((a k : F) ^ (q : ℕ))) +
            Height.logHeight₁ (∏ i, (r k i : F) ^ (u i : ℕ)) := by
          gcongr
          exact Height.logHeight₁_mul_le _ _
        _ = _ := by ring
    _ ≤ (A : ℝ) * H + (T : ℝ) *
          ((Module.finrank ℚ F : ℝ) * Real.log V) +
        ((Fintype.card iota * S : ℕ) : ℝ) *
          ((Module.finrank ℚ F : ℝ) * Real.log V) := by
      rw [Height.logHeight₁_pow, Height.logHeight₁_pow]
      have hH : 0 ≤ H :=
        (Height.zero_le_logHeight₁ (beta k)).trans (hbeta k)
      have hDlog : 0 ≤
          (Module.finrank ℚ F : ℝ) * Real.log V := by positivity
      have hbpow : (h : ℝ) * Height.logHeight₁ (beta k) ≤
          (A : ℝ) * H := by
        exact mul_le_mul (by exact_mod_cast h.isLt.le) (hbeta k)
          (Height.zero_le_logHeight₁ _) (by positivity)
      have hapow : (q : ℝ) * Height.logHeight₁ (a k : F) ≤
          (T : ℝ) * ((Module.finrank ℚ F : ℝ) * Real.log V) := by
        exact mul_le_mul (by exact_mod_cast q.isLt.le) haHeight
          (Height.zero_le_logHeight₁ _) (by positivity)
      exact add_le_add (add_le_add hbpow hapow) hprod
    _ = (A : ℝ) * H +
          ((T + Fintype.card iota * S : ℕ) : ℝ) *
            ((Module.finrank ℚ F : ℝ) * Real.log V) := by
      push_cast
      ring

/-- One algebraic value in the multipoint moment table. -/
def multipointMomentValue
    {F kappa iota : Type*} [CommRing F]
    [Fintype kappa] [Fintype iota]
    (beta : kappa → F) (a : kappa → ℤ) (r : kappa → iota → ℤ)
    (c : kappa → ℤ) (h q : ℕ) (u : iota → ℕ) : F :=
  ∑ k, (c k : F) * beta k ^ h * (a k : F) ^ q *
    ∏ i, (r k i : F) ^ u i

/-- The full integer box kernel, viewed as algebraic multipoint moments at
the initial node `0`.  The node power disappears there, so no denominator
clearing in the ambient number field is required. -/
theorem exists_box_initial_multipoint_moment_coefficients
    {F : Type*} [Field F] [NumberField F]
    {r K B T S : ℕ} (alpha : Fin (r + 1) → F)
    (b : Fin (r + 1) → ℤ) (hb : ∀ i, (b i).natAbs ≤ B)
    (hT : 0 < T) (hS : 0 < S)
    (hcard : T * S ^ r < K ^ (r + 1)) :
    ∃ c : ExponentBox (r + 1) K → ℤ, c ≠ 0 ∧
      (∀ node : Fin 1, ∀ q : Fin T, ∀ u : Fin r → Fin S,
        multipointMomentValue (boxMonomial alpha)
          boxDistinguishedExponent (boxTransformedExponent b) c
          node q (fun i ↦ u i) = 0) ∧
      ∀ k, (c k).natAbs ≤ Nat.ceil
        ((((K ^ (r + 1) : ℕ) : ℝ) * max 1
            ‖rectangularMomentMatrix
              (fun k : ExponentBox (r + 1) K ↦ boxDistinguishedExponent k)
              (fun (k : ExponentBox (r + 1) K) (i : Fin r) ↦
                boxTransformedExponent b k i) T S‖) ^
          (((T * S ^ r : ℕ) : ℝ) /
            (((K ^ (r + 1) : ℕ) : ℝ) -
              ((T * S ^ r : ℕ) : ℝ)))) := by
  obtain ⟨c, hc, hmoment, hbound⟩ :=
    exists_box_rectangular_moment_coefficients_full b hb hT hS hcard
  refine ⟨c, hc, ?_, hbound⟩
  intro node q u
  have hzero := hmoment q u
  have hzeroF :
      (∑ k, (c k : F) *
        (boxDistinguishedExponent k : F) ^ (q : ℕ) *
          ∏ i, (boxTransformedExponent b k i : F) ^ (u i : ℕ)) = 0 := by
    exact_mod_cast hzero
  simpa [multipointMomentValue] using hzeroF

/-- Global logarithmic-height bound for one moment value. -/
theorem logHeight₁_multipointMomentValue_le
    {F kappa iota : Type*} [Field F] [NumberField F]
    [Fintype kappa] [Fintype iota]
    (beta : kappa → F) (a : kappa → ℤ) (r : kappa → iota → ℤ)
    (c : kappa → ℤ) (h q : ℕ) (u : iota → ℕ)
    {C H V : ℝ} (hC : 1 ≤ C) (hV : 1 ≤ V)
    (hc : ∀ k, (c k).natAbs ≤ C)
    (hbeta : ∀ k, Height.logHeight₁ (beta k) ≤ H)
    (ha : ∀ k, ‖a k‖ ≤ V) (hr : ∀ k i, ‖r k i‖ ≤ V) :
    Height.logHeight₁ (multipointMomentValue beta a r c h q u) ≤
      (Module.finrank ℚ F : ℝ) * Real.log (Fintype.card kappa : ℝ) +
        (Fintype.card kappa : ℝ) *
          ((Module.finrank ℚ F : ℝ) * Real.log C +
            (h : ℝ) * H +
            ((q + ∑ i, u i : ℕ) : ℝ) *
              ((Module.finrank ℚ F : ℝ) * Real.log V)) := by
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg hV
  have haHeight : ∀ k, Height.logHeight₁ (a k : F) ≤
      (Module.finrank ℚ F : ℝ) * Real.log V := by
    intro k
    refine (logHeight₁_intCast_le (K := F) (a k)).trans ?_
    gcongr
    rw [Nat.cast_max]
    exact max_le (by simpa using hV)
      (by simpa [Int.norm_eq_abs] using ha k)
  have hrHeight : ∀ k i, Height.logHeight₁ (r k i : F) ≤
      (Module.finrank ℚ F : ℝ) * Real.log V := by
    intro k i
    refine (logHeight₁_intCast_le (K := F) (r k i)).trans ?_
    gcongr
    rw [Nat.cast_max]
    exact max_le (by simpa using hV)
      (by simpa [Int.norm_eq_abs] using hr k i)
  rw [multipointMomentValue]
  calc
    Height.logHeight₁ (∑ k, (c k : F) * beta k ^ h *
        (a k : F) ^ q * ∏ i, (r k i : F) ^ u i) ≤
      (Height.totalWeight F : ℝ) *
          Real.log ((Finset.univ : Finset kappa).card : ℝ) +
        ∑ k, Height.logHeight₁ ((c k : F) * beta k ^ h *
          (a k : F) ^ q * ∏ i, (r k i : F) ^ u i) := by
      exact Height.logHeight₁_sum_le Finset.univ _
    _ ≤ (Module.finrank ℚ F : ℝ) *
          Real.log (Fintype.card kappa : ℝ) +
        ∑ _k : kappa,
          ((Module.finrank ℚ F : ℝ) * Real.log C +
            (h : ℝ) * H +
            ((q + ∑ i, u i : ℕ) : ℝ) *
              ((Module.finrank ℚ F : ℝ) * Real.log V)) := by
      rw [NumberField.totalWeight_eq_finrank, Finset.card_univ]
      gcongr with k
      have hcHeight : Height.logHeight₁ (c k : F) ≤
          (Module.finrank ℚ F : ℝ) * Real.log C := by
        refine (logHeight₁_intCast_le (K := F) (c k)).trans ?_
        gcongr
        rw [Nat.cast_max]
        exact max_le (by simpa using hC)
          (by exact_mod_cast hc k)
      have hprod : Height.logHeight₁
          (∏ i, (r k i : F) ^ u i) ≤
            ((∑ i, u i : ℕ) : ℝ) *
              ((Module.finrank ℚ F : ℝ) * Real.log V) := by
        calc
          Height.logHeight₁ (∏ i, (r k i : F) ^ u i) ≤
              ∑ i, Height.logHeight₁ ((r k i : F) ^ u i) :=
            Height.logHeight₁_prod_le Finset.univ _
          _ = ∑ i, (u i : ℕ) * Height.logHeight₁ (r k i : F) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Height.logHeight₁_pow]
          _ ≤ ∑ i, (u i : ℝ) *
              ((Module.finrank ℚ F : ℝ) * Real.log V) := by
            gcongr with i hi
            exact hrHeight k i
          _ = ((∑ i, u i : ℕ) : ℝ) *
              ((Module.finrank ℚ F : ℝ) * Real.log V) := by
            push_cast
            rw [Finset.sum_mul]
      calc
        Height.logHeight₁ ((c k : F) * beta k ^ h *
            (a k : F) ^ q * ∏ i, (r k i : F) ^ u i) ≤
          Height.logHeight₁ (c k : F) + Height.logHeight₁ (beta k ^ h) +
            Height.logHeight₁ ((a k : F) ^ q) +
              Height.logHeight₁ (∏ i, (r k i : F) ^ u i) := by
            calc
              _ ≤ Height.logHeight₁ ((c k : F) * beta k ^ h *
                    (a k : F) ^ q) +
                  Height.logHeight₁ (∏ i, (r k i : F) ^ u i) :=
                Height.logHeight₁_mul_le _ _
              _ ≤ (Height.logHeight₁ ((c k : F) * beta k ^ h) +
                    Height.logHeight₁ ((a k : F) ^ q)) +
                  Height.logHeight₁ (∏ i, (r k i : F) ^ u i) := by
                gcongr
                exact Height.logHeight₁_mul_le _ _
              _ ≤ ((Height.logHeight₁ (c k : F) +
                    Height.logHeight₁ (beta k ^ h)) +
                    Height.logHeight₁ ((a k : F) ^ q)) +
                  Height.logHeight₁ (∏ i, (r k i : F) ^ u i) := by
                gcongr
                exact Height.logHeight₁_mul_le _ _
              _ = _ := by ring
        _ ≤ (Module.finrank ℚ F : ℝ) * Real.log C +
            (h : ℝ) * H +
            ((q + ∑ i, u i : ℕ) : ℝ) *
              ((Module.finrank ℚ F : ℝ) * Real.log V) := by
          rw [Height.logHeight₁_pow, Height.logHeight₁_pow]
          have hβ0 : 0 ≤ H :=
            (Height.zero_le_logHeight₁ (beta k)).trans (hbeta k)
          have hdlog : 0 ≤
              (Module.finrank ℚ F : ℝ) * Real.log V := by positivity
          calc
            _ ≤ (Module.finrank ℚ F : ℝ) * Real.log C +
                (h : ℝ) * H + (q : ℝ) *
                  ((Module.finrank ℚ F : ℝ) * Real.log V) +
                ((∑ i, u i : ℕ) : ℝ) *
                  ((Module.finrank ℚ F : ℝ) * Real.log V) := by
              exact add_le_add
                (add_le_add
                  (add_le_add hcHeight
                    (mul_le_mul_of_nonneg_left (hbeta k) (by positivity)))
                  (mul_le_mul_of_nonneg_left (haHeight k) (by positivity)))
                hprod
            _ = _ := by push_cast; ring
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- The distinguished embedding identifies an algebraic moment with the
corresponding complex weighted exponential value at an integer node. -/
theorem multipointMomentValue_embedding
    {F kappa iota : Type*} [Field F] [NumberField F]
    [Fintype kappa] [Fintype iota]
    (φ : F →+* ℂ) (beta : kappa → F)
    (a : kappa → ℤ) (r : kappa → iota → ℤ)
    (c : kappa → ℤ) (h q : ℕ) (u : iota → ℕ) :
    φ (multipointMomentValue beta a r c h q u) =
      ∑ k, (c k : ℂ) * φ (beta k) ^ h * (a k : ℂ) ^ q *
        ∏ i, (r k i : ℂ) ^ u i := by
  simp [multipointMomentValue]

/-- Algebraic multipoint moments force exact high-order zeros of the
associated complex exponential polynomial at every prescribed node.  The
change of variables is the same distinguished-coordinate identity used in
the small-value estimate; below order `T` its binomial remainder is empty. -/
theorem iteratedDeriv_auxiliaryExponentialSum_eq_zero_of_multipoint_moments
    {kappa iota : Type*} [Fintype kappa] [Fintype iota]
    [DecidableEq iota]
    (c beta L : kappa → ℂ) (b0 Lambda : ℂ)
    (a : kappa → ℤ) (r : kappa → iota → ℤ) (ell : iota → ℂ)
    {A T S : ℕ} (hb0 : b0 ≠ 0)
    (hexp : ∀ k, Complex.exp (L k) = beta k)
    (hcoord : ∀ k, b0 * L k = (a k : ℂ) * Lambda +
      ∑ i, (r k i : ℂ) * ell i)
    (hmoment : ∀ h : Fin A, ∀ q, q < T → ∀ p, p < S →
      ∀ u ∈ Finset.piAntidiag (Finset.univ : Finset iota) p,
        ∑ k, c k * beta k ^ (h : ℕ) * (a k : ℂ) ^ q *
          ∏ i, (r k i : ℂ) ^ u i = 0) :
    ∀ h : Fin A, ∀ s, s < T → s < S →
      iteratedDeriv s (auxiliaryExponentialSum L c) (h : ℂ) = 0 := by
  intro h s hsT hsS
  let ch : kappa → ℂ := fun k ↦ c k * beta k ^ (h : ℕ)
  have hmoment' : ∀ q, q < T → ∀ p, p < S →
      ∀ u ∈ Finset.piAntidiag (Finset.univ : Finset iota) p,
        ∑ k, ch k * (a k : ℂ) ^ q *
          ∏ i, (r k i : ℂ) ^ u i = 0 := by
    intro q hq p hp u hu
    simpa [ch, mul_assoc] using hmoment h q hq p hp u hu
  have heq := auxiliaryDerivative_eq_pow_mul_binomialRemainder
    ch L b0 Lambda (fun k ↦ (a k : ℂ))
      (fun k i ↦ (r k i : ℂ)) ell s T S hsS hcoord hmoment'
  have hrem : binomialRemainder ch (fun k ↦ (a k : ℂ))
      (fun k ↦ ∑ i, (r k i : ℂ) * ell i) Lambda s T = 0 := by
    rw [binomialRemainder]
    rw [show (Finset.range (s + 1)).filter (T ≤ ·) = ∅ by
      apply Finset.filter_eq_empty_iff.mpr
      intro q hq
      simp only [not_le]
      have hqs : q < s + 1 := Finset.mem_range.mp hq
      omega]
    simp
  rw [hrem, mul_zero] at heq
  have hbderiv : b0 ^ s *
      iteratedDeriv s (auxiliaryExponentialSum L c) (h : ℂ) = 0 := by
    rw [iteratedDeriv_auxiliaryExponentialSum]
    rw [Finset.mul_sum]
    calc
      ∑ k, b0 ^ s *
          (c k * L k ^ s * Complex.exp (L k * (h : ℂ))) =
          b0 ^ s * iteratedDeriv s (auxiliaryExponentialSum L ch) 0 := by
        rw [iteratedDeriv_auxiliaryExponentialSum, Finset.mul_sum]
        simp only [mul_zero, Complex.exp_zero, mul_one]
        apply Finset.sum_congr rfl
        intro k hk
        have hp : Complex.exp (L k * (h : ℂ)) = beta k ^ (h : ℕ) := by
          calc
            Complex.exp (L k * (h : ℂ)) =
                Complex.exp ((h : ℂ) * L k) := by rw [mul_comm]
            _ = Complex.exp (L k) ^ (h : ℕ) := Complex.exp_nat_mul _ _
            _ = beta k ^ (h : ℕ) := by rw [hexp]
        rw [hp]
        dsimp [ch]
        ring
      _ = 0 := heq
  exact (mul_eq_zero.mp hbderiv).resolve_left (pow_ne_zero _ hb0)

/-- A rectangular block of multipoint moments also gives high-order zeros
for every moment-weighted auxiliary sum.  Differentiating `j` times spends
at most `j` units in the distinguished coordinate and in each remaining
coordinate, which is the bookkeeping invariant used in every
extrapolation round. -/
theorem iteratedDeriv_weightedAuxiliaryExponentialSum_eq_zero_of_multipoint_moments
    {kappa iota : Type*} [Fintype kappa] [Fintype iota]
    [DecidableEq iota]
    (c beta L : kappa → ℂ) (b0 Lambda : ℂ)
    (a : kappa → ℤ) (r : kappa → iota → ℤ) (ell : iota → ℂ)
    {A T S : ℕ} (hb0 : b0 ≠ 0)
    (hexp : ∀ k, Complex.exp (L k) = beta k)
    (hcoord : ∀ k, b0 * L k = (a k : ℂ) * Lambda +
      ∑ i, (r k i : ℂ) * ell i)
    (hmoment : ∀ h : Fin A, ∀ q : Fin T, ∀ u : iota → Fin S,
      ∑ k, c k * beta k ^ (h : ℕ) * (a k : ℂ) ^ (q : ℕ) *
        ∏ i, (r k i : ℂ) ^ (u i : ℕ) = 0)
    (h : Fin A) (q0 : ℕ) (u0 : iota → ℕ) (j : ℕ)
    (hq : q0 + j < T) (hu : ∀ i, u0 i + j < S) :
    iteratedDeriv j
      (auxiliaryExponentialSum L (fun k ↦
        c k * (a k : ℂ) ^ q0 * ∏ i, (r k i : ℂ) ^ u0 i))
      (h : ℂ) = 0 := by
  let d : kappa → ℂ := fun k ↦
    c k * (a k : ℂ) ^ q0 * ∏ i, (r k i : ℂ) ^ u0 i
  let ch : kappa → ℂ := fun k ↦ d k * beta k ^ (h : ℕ)
  have hmom' : ∀ q, q < j + 1 → ∀ p, p < j + 1 →
      ∀ v ∈ Finset.piAntidiag (Finset.univ : Finset iota) p,
        ∑ k, ch k * (a k : ℂ) ^ q *
          ∏ i, (r k i : ℂ) ^ v i = 0 := by
    intro q hqj p hpj v hv
    have hqT : q0 + q < T := by omega
    have hvle : ∀ i, v i ≤ p := by
      intro i
      exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le (v j))
        (Finset.mem_univ i) |>.trans_eq (Finset.mem_piAntidiag.mp hv).1
    have huvS : ∀ i, u0 i + v i < S := by
      intro i
      have hvj : v i ≤ j := (hvle i).trans (by omega)
      exact (Nat.add_le_add_left hvj (u0 i)).trans_lt (hu i)
    let qT : Fin T := ⟨q0 + q, hqT⟩
    let uS : iota → Fin S := fun i ↦ ⟨u0 i + v i, huvS i⟩
    have hz := hmoment h qT uS
    rw [show (∑ k, ch k * (a k : ℂ) ^ q *
          ∏ i, (r k i : ℂ) ^ v i) =
        ∑ k, c k * beta k ^ (h : ℕ) *
          (a k : ℂ) ^ (q0 + q) *
            ∏ i, (r k i : ℂ) ^ (u0 i + v i) by
      apply Finset.sum_congr rfl
      intro k hk
      simp_rw [pow_add, Finset.prod_mul_distrib]
      dsimp [ch, d]
      ring]
    simpa only [qT, uS] using hz
  have heq := auxiliaryDerivative_eq_pow_mul_binomialRemainder
    ch L b0 Lambda (fun k ↦ (a k : ℂ))
      (fun k i ↦ (r k i : ℂ)) ell j (j + 1) (j + 1)
      (by omega) hcoord hmom'
  have hrem : binomialRemainder ch (fun k ↦ (a k : ℂ))
      (fun k ↦ ∑ i, (r k i : ℂ) * ell i) Lambda j (j + 1) = 0 := by
    rw [binomialRemainder]
    rw [show (Finset.range (j + 1)).filter (j + 1 ≤ ·) = ∅ by simp]
    simp
  rw [hrem, mul_zero] at heq
  have hbderiv : b0 ^ j *
      iteratedDeriv j (auxiliaryExponentialSum L d) (h : ℂ) = 0 := by
    rw [iteratedDeriv_auxiliaryExponentialSum]
    rw [Finset.mul_sum]
    calc
      ∑ k, b0 ^ j * (d k * L k ^ j *
          Complex.exp (L k * (h : ℂ))) =
          b0 ^ j * iteratedDeriv j (auxiliaryExponentialSum L ch) 0 := by
        rw [iteratedDeriv_auxiliaryExponentialSum, Finset.mul_sum]
        simp only [mul_zero, Complex.exp_zero, mul_one]
        apply Finset.sum_congr rfl
        intro k hk
        have hp : Complex.exp (L k * (h : ℂ)) = beta k ^ (h : ℕ) := by
          calc
            Complex.exp (L k * (h : ℂ)) =
                Complex.exp ((h : ℂ) * L k) := by rw [mul_comm]
            _ = Complex.exp (L k) ^ (h : ℕ) := Complex.exp_nat_mul _ _
            _ = beta k ^ (h : ℕ) := by rw [hexp]
        rw [hp]
        dsimp [ch]
        ring
      _ = 0 := heq
  change iteratedDeriv j (auxiliaryExponentialSum L d) (h : ℂ) = 0
  exact (mul_eq_zero.mp hbderiv).resolve_left (pow_ne_zero _ hb0)

/-! ## Multipoint analytic extrapolation -/

/-- Uniform growth bound for every derivative of a finite exponential
polynomial on a closed disk.  This is the boundary estimate used by the
maximum-modulus extrapolation step. -/
theorem iteratedDeriv_auxiliaryExponentialSum_norm_le
    {κ : Type*} [Fintype κ]
    (L c : κ → ℂ) (m : ℕ) {z : ℂ} {C U R : ℝ}
    (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hc : ∀ k, ‖c k‖ ≤ C) (hL : ∀ k, ‖L k‖ ≤ U)
    (hz : ‖z‖ ≤ R) :
    ‖iteratedDeriv m (auxiliaryExponentialSum L c) z‖ ≤
      (Fintype.card κ : ℝ) * C * U ^ m * Real.exp (U * R) := by
  rw [iteratedDeriv_auxiliaryExponentialSum]
  calc
    ‖∑ k, c k * L k ^ m * Complex.exp (L k * z)‖ ≤
        ∑ k, ‖c k * L k ^ m * Complex.exp (L k * z)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _k : κ, C * U ^ m * Real.exp (U * R) := by
      gcongr with k hk
      rw [norm_mul, norm_mul, norm_pow]
      have hexp : ‖Complex.exp (L k * z)‖ ≤ Real.exp (U * R) := by
        rw [Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        calc
          (L k * z).re ≤ ‖L k * z‖ := Complex.re_le_norm _
          _ = ‖L k‖ * ‖z‖ := norm_mul _ _
          _ ≤ U * R := mul_le_mul (hL k) hz (norm_nonneg z) hU
      exact mul_le_mul
        (mul_le_mul (hc k)
          (pow_le_pow_left₀ (norm_nonneg (L k)) (hL k) m)
          (pow_nonneg (norm_nonneg _) _) hC)
        hexp (norm_nonneg _) (mul_nonneg hC (pow_nonneg hU m))
    _ = (Fintype.card κ : ℝ) * C * U ^ m * Real.exp (U * R) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      ring

/-- The complex nodes `0, 1, ..., A-1` used in Baker's extrapolation. -/
def natNodeFinset (A : ℕ) : Finset ℂ :=
  (Finset.range A).map (Nat.castEmbedding : ℕ ↪ ℂ)

@[simp] lemma mem_natNodeFinset {A : ℕ} {z : ℂ} :
    z ∈ natNodeFinset A ↔ ∃ h < A, (h : ℂ) = z := by
  simp [natNodeFinset]

@[simp] lemma card_natNodeFinset (A : ℕ) :
    (natNodeFinset A).card = A := by
  simp [natNodeFinset]

lemma norm_le_of_mem_natNodeFinset {A : ℕ} {z : ℂ}
    (hz : z ∈ natNodeFinset A) : ‖z‖ ≤ (A : ℝ) := by
  obtain ⟨h, hh, rfl⟩ := mem_natNodeFinset.mp hz
  rw [Complex.norm_natCast]
  exact_mod_cast hh.le

lemma natCast_mem_natNodeFinset {A h : ℕ} (hh : h < A) :
    (h : ℂ) ∈ natNodeFinset A := by
  rw [mem_natNodeFinset]
  exact ⟨h, hh, rfl⟩

/-- Iterating the derivative `k` times after taking `m` derivatives is the
`(m+k)`-th derivative. -/
lemma iteratedDeriv_iteratedDeriv (f : ℂ → ℂ) (m k : ℕ) :
    iteratedDeriv k (iteratedDeriv m f) = iteratedDeriv (m + k) f := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    iteratedDeriv_eq_iterate]
  rw [Nat.add_comm m k, Function.iterate_add_apply]

/-- Every iterated derivative of an entire function is entire. -/
lemma analyticAt_iteratedDeriv (f : ℂ → ℂ)
    (hf : ∀ z, AnalyticAt ℂ f z) (m : ℕ) :
    ∀ z, AnalyticAt ℂ (iteratedDeriv m f) z := by
  induction m with
  | zero => simpa
  | succ m ih =>
      rw [show m + 1 = Nat.succ m by omega, iteratedDeriv_succ]
      exact fun z ↦ (ih z).deriv

/-- Vanishing to order at least `m` at one point factors an entire function
globally by the corresponding centered power.  The quotient is defined by
division away from the center and by the local analytic quotient at the
center; the local factorization makes the two definitions agree. -/
lemma exists_global_factor_centered_pow
    (f : ℂ → ℂ) (a : ℂ) (m : ℕ)
    (hf : ∀ z, AnalyticAt ℂ f z)
    (hm : (m : ℕ∞) ≤ analyticOrderAt f a) :
    ∃ g : ℂ → ℂ, (∀ z, AnalyticAt ℂ g z) ∧
      ∀ z, f z = (z - a) ^ m * g z := by
  obtain ⟨g₀, hg₀, hlocal⟩ :=
    (natCast_le_analyticOrderAt (hf a)).mp hm
  let g : ℂ → ℂ := fun z ↦ if z = a then g₀ z else f z / (z - a) ^ m
  have hga : g =ᶠ[𝓝 a] g₀ := by
    filter_upwards [hlocal] with z hz
    by_cases hza : z = a
    · simp [g, hza]
    · simp only [g, if_neg hza]
      rw [show f z = (z - a) ^ m * g₀ z by
        simpa [smul_eq_mul] using hz]
      field_simp
  have hgan : AnalyticAt ℂ g a := hg₀.congr hga.symm
  have hg : ∀ z, AnalyticAt ℂ g z := by
    intro z
    by_cases hza : z = a
    · simpa [hza] using hgan
    · have hne : ∀ᶠ w in 𝓝 z, w ≠ a :=
        (isOpen_compl_singleton.mem_nhds hza)
      have heq : g =ᶠ[𝓝 z] fun w ↦ f w / (w - a) ^ m := by
        filter_upwards [hne] with w hw
        simp [g, hw]
      have hden : AnalyticAt ℂ (fun w : ℂ ↦ (w - a) ^ m) z := by
        fun_prop
      have hdenz : (z - a) ^ m ≠ 0 :=
        pow_ne_zero m (sub_ne_zero.mpr hza)
      apply ((hf z).div hden hdenz).congr heq.symm
  refine ⟨g, hg, fun z ↦ ?_⟩
  by_cases hza : z = a
  · subst z
    have ha := hlocal.self_of_nhds
    simpa [g] using ha
  · simp only [g, if_neg hza]
    field_simp

/-- Product of equal-order centered factors over a finite zero set. -/
def centeredPowerProduct (s : Finset ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  ∏ a ∈ s, (z - a) ^ m

/-- Simultaneous finite-order vanishing at finitely many distinct points
factors an entire function by the product of all centered powers. -/
lemma exists_global_factor_finset
    (f : ℂ → ℂ) (s : Finset ℂ) (m : ℕ)
    (hf : ∀ z, AnalyticAt ℂ f z)
    (hm : ∀ a ∈ s, (m : ℕ∞) ≤ analyticOrderAt f a) :
    ∃ g : ℂ → ℂ, (∀ z, AnalyticAt ℂ g z) ∧
      ∀ z, f z = centeredPowerProduct s m z * g z := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty =>
      refine ⟨f, hf, fun z ↦ ?_⟩
      simp [centeredPowerProduct]
  | @insert a s ha ih =>
      obtain ⟨g₁, hg₁, hfac₁⟩ :=
        exists_global_factor_centered_pow f a m hf (hm a (by simp))
      have hmg₁ : ∀ b ∈ s, (m : ℕ∞) ≤ analyticOrderAt g₁ b := by
        intro b hb
        have hba : b ≠ a := by
          intro h
          subst b
          exact ha hb
        have horder : analyticOrderAt f b = analyticOrderAt g₁ b := by
          rw [analyticOrderAt_congr
            (Filter.Eventually.of_forall (fun z ↦ hfac₁ z))]
          change analyticOrderAt ((fun z : ℂ ↦ (z - a) ^ m) * g₁) b = _
          rw [analyticOrderAt_mul (by fun_prop) (hg₁ b)]
          have hp0 : analyticOrderAt (fun z : ℂ ↦ (z - a) ^ m) b = 0 :=
            (show AnalyticAt ℂ (fun z : ℂ ↦ (z - a) ^ m) b by
              fun_prop).analyticOrderAt_eq_zero.mpr
                (pow_ne_zero m (sub_ne_zero.mpr hba))
          rw [hp0, zero_add]
        rw [← horder]
        exact hm b (by simp [hb])
      obtain ⟨g, hg, hfac⟩ := ih g₁ hg₁ hmg₁
      refine ⟨g, hg, fun z ↦ ?_⟩
      rw [hfac₁ z, hfac z]
      simp only [centeredPowerProduct, Finset.prod_insert ha]
      ring

/-- Maximum-modulus extrapolation after dividing out a finite collection
of prescribed zeros.  `D` bounds the zero product from below on the outer
circle and `E` bounds it from above at the target point. -/
lemma analytic_norm_le_of_many_zeros
    (f : ℂ → ℂ) (s : Finset ℂ) (m : ℕ)
    {R D E M : ℝ} (hR : 0 < R) (hD : 0 < D)
    (hf : ∀ z, AnalyticAt ℂ f z)
    (hm : ∀ a ∈ s, (m : ℕ∞) ≤ analyticOrderAt f a)
    (hboundary : ∀ w ∈ Metric.sphere (0 : ℂ) R, ‖f w‖ ≤ M)
    (hden : ∀ w ∈ Metric.sphere (0 : ℂ) R,
      D ≤ ‖centeredPowerProduct s m w‖)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) R)
    (htarget : ‖centeredPowerProduct s m z‖ ≤ E) :
    ‖f z‖ ≤ E * (M / D) := by
  obtain ⟨g, hg, hfac⟩ := exists_global_factor_finset f s m hf hm
  have hgd : Differentiable ℂ g := fun w ↦ (hg w).differentiableAt
  have hgboundary : ∀ w ∈ frontier (Metric.ball (0 : ℂ) R),
      ‖g w‖ ≤ M / D := by
    intro w hw
    rw [frontier_ball 0 hR.ne'] at hw
    have hfacNorm := congrArg norm (hfac w)
    rw [norm_mul] at hfacNorm
    rw [le_div_iff₀ hD]
    calc
      ‖g w‖ * D ≤ ‖g w‖ * ‖centeredPowerProduct s m w‖ := by
        gcongr
        exact hden w hw
      _ = ‖f w‖ := by rw [mul_comm, hfacNorm]
      _ ≤ M := hboundary w hw
  have hzg : ‖g z‖ ≤ M / D := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le
      (Metric.isBounded_ball) hgd.diffContOnCl hgboundary
    rwa [closure_ball 0 hR.ne']
  rw [hfac z, norm_mul]
  calc
    ‖centeredPowerProduct s m z‖ * ‖g z‖ ≤ E * ‖g z‖ :=
      mul_le_mul_of_nonneg_right htarget (norm_nonneg _)
    _ ≤ E * (M / D) :=
      mul_le_mul_of_nonneg_left hzg ((norm_nonneg _).trans htarget)

/-- Derivative form of the maximum-modulus extrapolation lemma.  Zeros of
the consecutive derivatives `m, ..., m+k-1` are exactly order-`k` zeros of
the `m`-th derivative. -/
lemma iteratedDeriv_norm_le_of_many_zeros
    (f : ℂ → ℂ) (s : Finset ℂ) (m k : ℕ)
    {R D E M : ℝ} (hR : 0 < R) (hD : 0 < D)
    (hf : ∀ z, AnalyticAt ℂ f z)
    (hzero : ∀ a ∈ s, ∀ j < k,
      iteratedDeriv (m + j) f a = 0)
    (hboundary : ∀ w ∈ Metric.sphere (0 : ℂ) R,
      ‖iteratedDeriv m f w‖ ≤ M)
    (hden : ∀ w ∈ Metric.sphere (0 : ℂ) R,
      D ≤ ‖centeredPowerProduct s k w‖)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) R)
    (htarget : ‖centeredPowerProduct s k z‖ ≤ E) :
    ‖iteratedDeriv m f z‖ ≤ E * (M / D) := by
  let g : ℂ → ℂ := iteratedDeriv m f
  have hg : ∀ z, AnalyticAt ℂ g z := analyticAt_iteratedDeriv f hf m
  have horder : ∀ a ∈ s, (k : ℕ∞) ≤ analyticOrderAt g a := by
    intro a ha
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hg a)]
    intro j hj
    rw [show iteratedDeriv j g a = iteratedDeriv (m + j) f a by
      simpa [g] using congrFun (iteratedDeriv_iteratedDeriv f m j) a]
    exact hzero a ha j hj
  exact analytic_norm_le_of_many_zeros g s k hR hD hg horder
    hboundary hden hz htarget

/-- Geometric lower bound for the centered zero product on an outer
circle containing every prescribed zero. -/
lemma centeredPowerProduct_norm_lower
    (s : Finset ℂ) (m : ℕ) {A R : ℝ} (hRA : 0 ≤ R - A)
    (ha : ∀ a ∈ s, ‖a‖ ≤ A) {w : ℂ}
    (hw : w ∈ Metric.sphere (0 : ℂ) R) :
    (R - A) ^ (m * s.card) ≤ ‖centeredPowerProduct s m w‖ := by
  have hwNorm : ‖w‖ = R := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hw
  rw [centeredPowerProduct, Complex.norm_prod]
  calc
    (R - A) ^ (m * s.card) = ∏ a ∈ s, (R - A) ^ m := by
      simp [← pow_mul]
    _ ≤ ∏ a ∈ s, ‖(w - a) ^ m‖ := by
      apply Finset.prod_le_prod
      · intro a haS
        positivity
      · intro a haS
        rw [norm_pow]
        gcongr
        calc
          R - A ≤ ‖w‖ - ‖a‖ := by linarith [ha a haS]
          _ ≤ ‖w - a‖ := norm_sub_norm_le _ _

/-- Geometric upper bound for the centered zero product at an inner
target point. -/
lemma centeredPowerProduct_norm_upper
    (s : Finset ℂ) (m : ℕ) {A Z : ℝ}
    (ha : ∀ a ∈ s, ‖a‖ ≤ A) {z : ℂ} (hz : ‖z‖ ≤ Z) :
    ‖centeredPowerProduct s m z‖ ≤ (Z + A) ^ (m * s.card) := by
  rw [centeredPowerProduct]
  calc
    ‖∏ a ∈ s, (z - a) ^ m‖ = ∏ a ∈ s, ‖(z - a) ^ m‖ := by
      rw [Complex.norm_prod]
    _ ≤ ∏ a ∈ s, (Z + A) ^ m := by
      apply Finset.prod_le_prod
      · intro a haS
        positivity
      · intro a haS
        rw [norm_pow]
        gcongr
        exact (norm_sub_le z a).trans (add_le_add hz (ha a haS))
    _ = (Z + A) ^ (m * s.card) := by simp [← pow_mul]

/-- Concrete maximum-modulus extrapolation from the consecutive integer
nodes `0, ..., A-1`.  It combines the derivative growth estimate with the
two elementary bounds for the centered zero product, leaving no analytic
side conditions for later arithmetic applications. -/
theorem auxiliaryExponentialSum_iteratedDeriv_norm_le_of_nat_nodes
    {κ : Type*} [Fintype κ]
    (L c : κ → ℂ) (m k A : ℕ) {z : ℂ} {C U R Z : ℝ}
    (hC : 0 ≤ C) (hU : 0 ≤ U) (hA : (A : ℝ) < R)
    (hc : ∀ i, ‖c i‖ ≤ C) (hL : ∀ i, ‖L i‖ ≤ U)
    (hzero : ∀ h < A, ∀ j < k,
      iteratedDeriv (m + j) (auxiliaryExponentialSum L c) (h : ℂ) = 0)
    (hz : ‖z‖ ≤ Z) (hZR : Z ≤ R) :
    ‖iteratedDeriv m (auxiliaryExponentialSum L c) z‖ ≤
      (Z + A) ^ (k * A) *
        (((Fintype.card κ : ℝ) * C * U ^ m * Real.exp (U * R)) /
          (R - A) ^ (k * A)) := by
  let s := natNodeFinset A
  have hR : 0 < R := lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ A) hA
  have hD : 0 < (R - A) ^ (k * A) := by positivity
  apply iteratedDeriv_norm_le_of_many_zeros
    (f := auxiliaryExponentialSum L c) (s := s) (m := m) (k := k)
    (R := R) (D := (R - A) ^ (k * A))
    (E := (Z + A) ^ (k * A))
    (M := (Fintype.card κ : ℝ) * C * U ^ m * Real.exp (U * R))
    hR hD
  · intro w
    unfold auxiliaryExponentialSum
    fun_prop
  · intro a ha j hj
    obtain ⟨h, hh, rfl⟩ := mem_natNodeFinset.mp ha
    exact hzero h hh j hj
  · intro w hw
    apply iteratedDeriv_auxiliaryExponentialSum_norm_le L c m hC hU hc hL
    have : ‖w‖ = R := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hw
    exact this.le
  · intro w hw
    simpa [s] using centeredPowerProduct_norm_lower
      (s := natNodeFinset A) (m := k) (A := (A : ℝ))
      (R := R) (by linarith) (fun a ha ↦ norm_le_of_mem_natNodeFinset ha) hw
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact hz.trans hZR
  · simpa [s] using centeredPowerProduct_norm_upper
      (s := natNodeFinset A) (m := k) (A := (A : ℝ)) (Z := Z)
      (fun a ha ↦ norm_le_of_mem_natNodeFinset ha) hz

/-- One extrapolation step for the algebraic moment system.  Analytic
smallness, the height estimate, and Liouville's inequality force the new
moment value to vanish exactly. -/
theorem multipointMomentValue_eq_zero_of_extrapolation
    {F kappa iota : Type*} [Field F] [NumberField F]
    [Fintype kappa] [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) (beta : kappa → F)
    (c : kappa → ℤ) (L : kappa → ℂ) (b0 Lambda : ℂ)
    (a : kappa → ℤ) (r : kappa → iota → ℤ) (ell : iota → ℂ)
    {A T S k h q0 : ℕ} (u0 : iota → ℕ)
    {C H V U R Z : ℝ}
    (hb0 : b0 ≠ 0) (hC : 1 ≤ C) (hV : 1 ≤ V) (hU : 0 ≤ U)
    (hc : ∀ x, (c x).natAbs ≤ C)
    (hbeta : ∀ x, Height.logHeight₁ (beta x) ≤ H)
    (ha : ∀ x, ‖a x‖ ≤ V) (hr : ∀ x i, ‖r x i‖ ≤ V)
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (beta x))
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin A, ∀ q : Fin T, ∀ u : iota → Fin S,
      multipointMomentValue beta a r c node q (fun i ↦ u i) = 0)
    (hq : q0 + k ≤ T) (hu : ∀ i, u0 i + k ≤ S)
    (hAR : (A : ℝ) < R) (hhZ : (h : ℝ) ≤ Z) (hZR : Z ≤ R)
    (hsmall :
      (Z + A) ^ (k * A) *
          (((Fintype.card kappa : ℝ) *
              (C * V ^ (q0 + ∑ i, u0 i)) *
              Real.exp (U * R)) /
            (R - A) ^ (k * A)) <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (Fintype.card kappa : ℝ) +
            (Fintype.card kappa : ℝ) *
              ((Module.finrank ℚ F : ℝ) * Real.log C +
                (h : ℝ) * H +
                ((q0 + ∑ i, u0 i : ℕ) : ℝ) *
                  ((Module.finrank ℚ F : ℝ) * Real.log V))))) :
    multipointMomentValue beta a r c h q0 u0 = 0 := by
  let d : kappa → ℂ := fun x ↦
    (c x : ℂ) * (a x : ℂ) ^ q0 * ∏ i, (r x i : ℂ) ^ u0 i
  have hd : ∀ x, ‖d x‖ ≤ C * V ^ (q0 + ∑ i, u0 i) := by
    intro x
    have hcR : ‖(c x : ℂ)‖ ≤ C := by
      simpa [Complex.norm_intCast, Int.cast_abs, Int.natCast_natAbs] using hc x
    dsimp [d]
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_prod]
    have hprod : ∏ i, ‖((r x i : ℂ) ^ u0 i)‖ ≤
        V ^ (∑ i, u0 i) := by
      calc
        ∏ i, ‖((r x i : ℂ) ^ u0 i)‖ =
            ∏ i, ‖(r x i : ℂ)‖ ^ u0 i := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [norm_pow]
        _ ≤ ∏ i, V ^ u0 i := by
          gcongr with i hi
          simpa [Int.norm_eq_abs] using hr x i
        _ = V ^ (∑ i, u0 i) := by rw [← Finset.prod_pow_eq_pow_sum]
    calc
      ‖(c x : ℂ)‖ * ‖(a x : ℂ)‖ ^ q0 *
          ∏ i, ‖((r x i : ℂ) ^ u0 i)‖ ≤
        C * V ^ q0 * V ^ (∑ i, u0 i) := by
          have haR : ‖(a x : ℂ)‖ ≤ V := by
            simpa [Int.norm_eq_abs] using ha x
          have hpowA : ‖(a x : ℂ)‖ ^ q0 ≤ V ^ q0 := by
            exact pow_le_pow_left₀ (norm_nonneg _) haR q0
          have hfirst : ‖(c x : ℂ)‖ * ‖(a x : ℂ)‖ ^ q0 ≤
              C * V ^ q0 :=
            mul_le_mul hcR hpowA (by positivity) (zero_le_one.trans hC)
          exact mul_le_mul hfirst hprod (by positivity) (by positivity)
      _ = C * V ^ (q0 + ∑ i, u0 i) := by rw [pow_add]; ring
  have hmomentC : ∀ node : Fin A, ∀ q : Fin T, ∀ u : iota → Fin S,
      ∑ x, (c x : ℂ) * φ (beta x) ^ (node : ℕ) *
        (a x : ℂ) ^ (q : ℕ) * ∏ i, (r x i : ℂ) ^ (u i : ℕ) = 0 := by
    intro node q u
    rw [← multipointMomentValue_embedding φ beta a r c node q (fun i ↦ u i)]
    rw [hmoment node q u, map_zero]
  have hzero : ∀ node < A, ∀ j < k,
      iteratedDeriv j (auxiliaryExponentialSum L d) (node : ℂ) = 0 := by
    intro node hnode j hj
    let nodeA : Fin A := ⟨node, hnode⟩
    have hq' : q0 + j < T := by omega
    have hu' : ∀ i, u0 i + j < S := by
      intro i
      exact (Nat.add_lt_add_left hj (u0 i)).trans_le (hu i)
    simpa [d] using
      iteratedDeriv_weightedAuxiliaryExponentialSum_eq_zero_of_multipoint_moments
        (fun x ↦ (c x : ℂ)) (fun x ↦ φ (beta x)) L b0 Lambda
        a r ell hb0 hexp hcoord hmomentC nodeA q0 u0 j hq' hu'
  have hzero' : ∀ node < A, ∀ j < k,
      iteratedDeriv (0 + j) (auxiliaryExponentialSum L d) (node : ℂ) = 0 := by
    simpa using hzero
  have hanalytic := auxiliaryExponentialSum_iteratedDeriv_norm_le_of_nat_nodes
    L d 0 k A (C := C * V ^ (q0 + ∑ i, u0 i))
      (by positivity) hU hAR hd hL hzero'
      (z := (h : ℂ)) (Z := Z) (R := R) (by simpa using hhZ) hZR
  simp only [iteratedDeriv_zero, pow_zero, mul_one] at hanalytic
  have heval : auxiliaryExponentialSum L d (h : ℂ) =
      φ (multipointMomentValue beta a r c h q0 u0) := by
    rw [multipointMomentValue_embedding]
    unfold auxiliaryExponentialSum
    apply Finset.sum_congr rfl
    intro x hx
    have hp : Complex.exp (L x * (h : ℂ)) = φ (beta x) ^ h := by
      calc
        Complex.exp (L x * (h : ℂ)) =
            Complex.exp ((h : ℂ) * L x) := by rw [mul_comm]
        _ = Complex.exp (L x) ^ h := Complex.exp_nat_mul _ _
        _ = φ (beta x) ^ h := by rw [hexp]
    rw [hp]
    dsimp [d]
    ring
  by_contra hne
  have hvalueNe : multipointMomentValue beta a r c h q0 u0 ≠ 0 := hne
  have hheight := logHeight₁_multipointMomentValue_le
    beta a r c h q0 u0 hC hV hc hbeta ha hr
  have hlocal := neg_logHeight₁_le_log_norm_embedding φ hvalueNe
  have hlower : Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (Fintype.card kappa : ℝ) +
            (Fintype.card kappa : ℝ) *
              ((Module.finrank ℚ F : ℝ) * Real.log C +
                (h : ℝ) * H +
                ((q0 + ∑ i, u0 i : ℕ) : ℝ) *
                  ((Module.finrank ℚ F : ℝ) * Real.log V)))) ≤
      ‖φ (multipointMomentValue beta a r c h q0 u0)‖ := by
    have hlog : -((Module.finrank ℚ F : ℝ) *
              Real.log (Fintype.card kappa : ℝ) +
            (Fintype.card kappa : ℝ) *
              ((Module.finrank ℚ F : ℝ) * Real.log C +
                (h : ℝ) * H +
                ((q0 + ∑ i, u0 i : ℕ) : ℝ) *
                  ((Module.finrank ℚ F : ℝ) * Real.log V))) ≤
        Real.log ‖φ (multipointMomentValue beta a r c h q0 u0)‖ := by
      exact (neg_le_neg hheight).trans hlocal
    have hnormPos : 0 < ‖φ (multipointMomentValue beta a r c h q0 u0)‖ :=
      norm_pos_iff.mpr ((map_ne_zero φ).2 hvalueNe)
    calc
      _ ≤ Real.exp (Real.log ‖φ (multipointMomentValue beta a r c h q0 u0)‖) :=
        Real.exp_le_exp.mpr hlog
      _ = _ := Real.exp_log hnormPos
  rw [← heval] at hlower
  linarith


/-- Uniform rectangular form of one extrapolation step.  The source
moment box has widths `A,T,S`; after reserving `k` derivative orders in
each moment direction, all values in the target box vanish. -/
theorem multipointMoments_extend_of_extrapolation
    {F kappa iota : Type*} [Field F] [NumberField F]
    [Fintype kappa] [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) (beta : kappa → F)
    (c : kappa → ℤ) (L : kappa → ℂ) (b0 Lambda : ℂ)
    (a : kappa → ℤ) (r : kappa → iota → ℤ) (ell : iota → ℂ)
    {A T S k A' T' S' : ℕ} {C H V U R Z : ℝ}
    (hb0 : b0 ≠ 0) (hC : 1 ≤ C) (hV : 1 ≤ V) (hU : 0 ≤ U)
    (hc : ∀ x, (c x).natAbs ≤ C)
    (hbeta : ∀ x, Height.logHeight₁ (beta x) ≤ H)
    (ha : ∀ x, ‖a x‖ ≤ V) (hr : ∀ x i, ‖r x i‖ ≤ V)
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (beta x))
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin A, ∀ q : Fin T, ∀ u : iota → Fin S,
      multipointMomentValue beta a r c node q (fun i ↦ u i) = 0)
    (hT : T' + k ≤ T) (hS : S' + k ≤ S)
    (hAR : (A : ℝ) < R) (hA'Z : (A' : ℝ) ≤ Z) (hZR : Z ≤ R)
    (hsmall : ∀ h < A', ∀ q < T', ∀ u : iota → ℕ,
      (∀ i, u i < S') →
      (Z + A) ^ (k * A) *
          (((Fintype.card kappa : ℝ) *
              (C * V ^ (q + ∑ i, u i)) *
              Real.exp (U * R)) /
            (R - A) ^ (k * A)) <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (Fintype.card kappa : ℝ) +
            (Fintype.card kappa : ℝ) *
              ((Module.finrank ℚ F : ℝ) * Real.log C +
                (h : ℝ) * H +
                ((q + ∑ i, u i : ℕ) : ℝ) *
                  ((Module.finrank ℚ F : ℝ) * Real.log V))))) :
    ∀ node : Fin A', ∀ q : Fin T', ∀ u : iota → Fin S',
      multipointMomentValue beta a r c node q (fun i ↦ u i) = 0 := by
  intro node q u
  apply multipointMomentValue_eq_zero_of_extrapolation
    (A := A) (T := T) (S := S) (k := k) (h := (node : ℕ))
    (q0 := (q : ℕ)) (C := C) (H := H) (V := V) (U := U) (R := R) (Z := Z)
    φ beta c L b0 Lambda a r ell (fun i ↦ (u i : ℕ))
    hb0 hC hV hU hc hbeta ha hr hL hexp hcoord hmoment
  · omega
  · intro i
    have hui : (u i : ℕ) < S' := (u i).isLt
    omega
  · exact hAR
  · exact (Nat.cast_le.mpr node.2.le).trans hA'Z
  · exact hZR
  · exact hsmall node node.2 q q.2 (fun i ↦ (u i : ℕ))
      (fun i ↦ (u i).isLt)

/-- Exact extrapolation for a full exponent box, with the structured
projective-height Liouville bound. -/
theorem boxMultipointMomentValue_eq_zero_of_extrapolation
    {F iota : Type*} [Field F] [NumberField F]
    [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) {n K : ℕ} (alpha : Fin n → F)
    (c : ExponentBox n K → ℤ) (L : ExponentBox n K → ℂ)
    (b0 Lambda : ℂ) (a : ExponentBox n K → ℤ)
    (r : ExponentBox n K → iota → ℤ) (ell : iota → ℂ)
    {A T S k h q0 : ℕ} (u0 : iota → ℕ)
    {C V : ℕ} {U R Z : ℝ}
    (hK : 0 < K) (hb0 : b0 ≠ 0) (hC : 1 ≤ C) (hV : 1 ≤ V)
    (hU : 0 ≤ U) (hc : ∀ x, (c x).natAbs ≤ C)
    (haV : ∀ x, ‖a x‖ ≤ (V : ℝ))
    (hrV : ∀ x i, ‖r x i‖ ≤ (V : ℝ))
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (boxMonomial alpha x))
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin A, ∀ q : Fin T, ∀ u : iota → Fin S,
      multipointMomentValue (boxMonomial alpha) a r c node q
        (fun i ↦ u i) = 0)
    (hq : q0 + k ≤ T) (hu : ∀ i, u0 i + k ≤ S)
    (hAR : (A : ℝ) < R) (hhZ : (h : ℝ) ≤ Z) (hZR : Z ≤ R)
    (hsmall :
      (Z + A) ^ (k * A) *
          (((K ^ n : ℕ) : ℝ) *
              (((C * V ^ (q0 + ∑ i, u0 i) : ℕ) : ℝ)) *
              Real.exp (U * R) /
            (R - A) ^ (k * A)) <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ n + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (C * V ^ (q0 + ∑ i, u0 i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i))))) :
    multipointMomentValue (boxMonomial alpha) a r c h q0 u0 = 0 := by
  let dZ : ExponentBox n K → ℤ := fun x ↦
    c x * a x ^ q0 * ∏ i, r x i ^ u0 i
  let d : ExponentBox n K → ℂ := fun x ↦ (dZ x : ℂ)
  have hd : ∀ x, ‖d x‖ ≤
      ((C * V ^ (q0 + ∑ i, u0 i) : ℕ) : ℝ) := by
    intro x
    have hcR : ‖(c x : ℂ)‖ ≤ (C : ℝ) := by
      rw [Complex.norm_intCast, ← Int.cast_abs, ← Nat.cast_natAbs]
      exact_mod_cast hc x
    dsimp [d, dZ]
    rw [Int.cast_mul, Int.cast_mul, Int.cast_pow, Int.cast_prod,
      norm_mul, norm_mul, norm_pow, Complex.norm_prod]
    simp_rw [Int.cast_pow]
    have hprod : ∏ i, ‖((r x i : ℂ) ^ u0 i)‖ ≤
        (V : ℝ) ^ (∑ i, u0 i) := by
      calc
        ∏ i, ‖((r x i : ℂ) ^ u0 i)‖ =
            ∏ i, ‖(r x i : ℂ)‖ ^ u0 i := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [norm_pow]
        _ ≤ ∏ i, (V : ℝ) ^ u0 i := by
          gcongr with i hi
          simpa [Int.norm_eq_abs] using hrV x i
        _ = (V : ℝ) ^ (∑ i, u0 i) := by
          rw [← Finset.prod_pow_eq_pow_sum]
    calc
      ‖(c x : ℂ)‖ * ‖(a x : ℂ)‖ ^ q0 *
          ∏ i, ‖((r x i : ℂ) ^ u0 i)‖ ≤
        (C : ℝ) * (V : ℝ) ^ q0 *
          (V : ℝ) ^ (∑ i, u0 i) := by
          have haR : ‖(a x : ℂ)‖ ≤ (V : ℝ) := by
            simpa [Int.norm_eq_abs] using haV x
          have hpowA : ‖(a x : ℂ)‖ ^ q0 ≤ (V : ℝ) ^ q0 :=
            pow_le_pow_left₀ (norm_nonneg _) haR q0
          exact mul_le_mul
            (mul_le_mul hcR hpowA (by positivity) (by positivity))
            hprod (by positivity) (by positivity)
      _ = ((C * V ^ (q0 + ∑ i, u0 i) : ℕ) : ℝ) := by
        push_cast
        rw [pow_add]
        ring
  have hdNat : ∀ x, (dZ x).natAbs ≤
      C * V ^ (q0 + ∑ i, u0 i) := by
    intro x
    have hx := hd x
    dsimp [d] at hx
    rw [Complex.norm_intCast, ← Int.cast_abs, ← Nat.cast_natAbs] at hx
    exact_mod_cast hx
  have hmomentC : ∀ node : Fin A, ∀ q : Fin T, ∀ u : iota → Fin S,
      ∑ x, (c x : ℂ) * φ (boxMonomial alpha x) ^ (node : ℕ) *
        (a x : ℂ) ^ (q : ℕ) * ∏ i, (r x i : ℂ) ^ (u i : ℕ) = 0 := by
    intro node q u
    rw [← multipointMomentValue_embedding φ (boxMonomial alpha)
      a r c node q (fun i ↦ u i)]
    rw [hmoment node q u, map_zero]
  have hzero : ∀ node < A, ∀ j < k,
      iteratedDeriv j (auxiliaryExponentialSum L d) (node : ℂ) = 0 := by
    intro node hnode j hj
    let nodeA : Fin A := ⟨node, hnode⟩
    have hq' : q0 + j < T := by omega
    have hu' : ∀ i, u0 i + j < S := by
      intro i
      exact (Nat.add_lt_add_left hj (u0 i)).trans_le (hu i)
    simpa [d, dZ] using
      iteratedDeriv_weightedAuxiliaryExponentialSum_eq_zero_of_multipoint_moments
        (fun x ↦ (c x : ℂ))
        (fun x ↦ φ (boxMonomial alpha x)) L b0 Lambda
        a r ell hb0 hexp hcoord hmomentC nodeA q0 u0 j hq' hu'
  have hzero' : ∀ node < A, ∀ j < k,
      iteratedDeriv (0 + j) (auxiliaryExponentialSum L d) (node : ℂ) = 0 := by
    simpa using hzero
  have hanalytic := auxiliaryExponentialSum_iteratedDeriv_norm_le_of_nat_nodes
    L d 0 k A (C := ((C * V ^ (q0 + ∑ i, u0 i) : ℕ) : ℝ))
      (by positivity) hU hAR hd hL hzero'
      (z := (h : ℂ)) (Z := Z) (R := R) (by simpa using hhZ) hZR
  simp only [iteratedDeriv_zero, pow_zero, mul_one] at hanalytic
  have hanalytic' : ‖auxiliaryExponentialSum L d (h : ℂ)‖ ≤
      (Z + A) ^ (k * A) *
        (((K ^ n : ℕ) : ℝ) *
            (((C * V ^ (q0 + ∑ i, u0 i) : ℕ) : ℝ)) *
            Real.exp (U * R) /
          (R - A) ^ (k * A)) := by
    simpa [ExponentBox] using hanalytic
  have heval : auxiliaryExponentialSum L d (h : ℂ) =
      φ (multipointMomentValue (boxMonomial alpha) a r c h q0 u0) := by
    rw [multipointMomentValue_embedding]
    unfold auxiliaryExponentialSum
    apply Finset.sum_congr rfl
    intro x hx
    have hp : Complex.exp (L x * (h : ℂ)) =
        φ (boxMonomial alpha x) ^ h := by
      calc
        Complex.exp (L x * (h : ℂ)) =
            Complex.exp ((h : ℂ) * L x) := by rw [mul_comm]
        _ = Complex.exp (L x) ^ h := Complex.exp_nat_mul _ _
        _ = φ (boxMonomial alpha x) ^ h := by rw [hexp]
    rw [hp]
    dsimp [d, dZ]
    push_cast
    ring
  have hvalue : multipointMomentValue (boxMonomial alpha) a r c h q0 u0 =
      boxAuxiliaryAlgebraicValue alpha dZ h := by
    unfold multipointMomentValue boxAuxiliaryAlgebraicValue
    apply Finset.sum_congr rfl
    intro x hx
    dsimp [dZ]
    push_cast
    ring
  by_contra hne
  have hneBox : boxAuxiliaryAlgebraicValue alpha dZ h ≠ 0 := by
    rwa [← hvalue]
  have hlocal := boxAuxiliaryAlgebraicValue_projective_log_norm_lower
    φ alpha dZ hK (Nat.mul_pos hC (pow_pos hV _)) hdNat hneBox
  have hlower : Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ n + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (C * V ^ (q0 + ∑ i, u0 i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i)))) ≤
      ‖φ (boxAuxiliaryAlgebraicValue alpha dZ h)‖ := by
    have hnormPos : 0 < ‖φ (boxAuxiliaryAlgebraicValue alpha dZ h)‖ :=
      norm_pos_iff.mpr ((map_ne_zero φ).2 hneBox)
    calc
      _ ≤ Real.exp (Real.log
          ‖φ (boxAuxiliaryAlgebraicValue alpha dZ h)‖) :=
        Real.exp_le_exp.mpr hlocal
      _ = _ := Real.exp_log hnormPos
  rw [← hvalue, ← heval] at hlower
  linarith

/-- Uniform rectangular form of exact exponent-box extrapolation. -/
theorem boxMultipointMoments_extend_of_extrapolation
    {F iota : Type*} [Field F] [NumberField F]
    [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) {n K : ℕ} (alpha : Fin n → F)
    (c : ExponentBox n K → ℤ) (L : ExponentBox n K → ℂ)
    (b0 Lambda : ℂ) (a : ExponentBox n K → ℤ)
    (r : ExponentBox n K → iota → ℤ) (ell : iota → ℂ)
    {A T S k A' T' S' : ℕ} {C V : ℕ} {U R Z : ℝ}
    (hK : 0 < K) (hb0 : b0 ≠ 0) (hC : 1 ≤ C) (hV : 1 ≤ V)
    (hU : 0 ≤ U) (hc : ∀ x, (c x).natAbs ≤ C)
    (haV : ∀ x, ‖a x‖ ≤ (V : ℝ))
    (hrV : ∀ x i, ‖r x i‖ ≤ (V : ℝ))
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (boxMonomial alpha x))
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin A, ∀ q : Fin T, ∀ u : iota → Fin S,
      multipointMomentValue (boxMonomial alpha) a r c node q
        (fun i ↦ u i) = 0)
    (hT : T' + k ≤ T) (hS : S' + k ≤ S)
    (hAR : (A : ℝ) < R) (hA'Z : (A' : ℝ) ≤ Z) (hZR : Z ≤ R)
    (hsmall : ∀ h < A', ∀ q < T', ∀ u : iota → ℕ,
      (∀ i, u i < S') →
      (Z + A) ^ (k * A) *
          (((K ^ n : ℕ) : ℝ) *
              (((C * V ^ (q + ∑ i, u i) : ℕ) : ℝ)) *
              Real.exp (U * R) /
            (R - A) ^ (k * A)) <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ n + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (C * V ^ (q + ∑ i, u i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i))))) :
    ∀ node : Fin A', ∀ q : Fin T', ∀ u : iota → Fin S',
      multipointMomentValue (boxMonomial alpha) a r c node q
        (fun i ↦ u i) = 0 := by
  intro node q u
  apply boxMultipointMomentValue_eq_zero_of_extrapolation
    (A := A) (T := T) (S := S) (k := k) (h := (node : ℕ))
    (q0 := (q : ℕ)) (C := C) (V := V) (U := U) (R := R) (Z := Z)
    φ alpha c L b0 Lambda a r ell (fun i ↦ (u i : ℕ))
    hK hb0 hC hV hU hc haV hrV hL hexp hcoord hmoment
  · omega
  · intro i
    have hui : (u i : ℕ) < S' := (u i).isLt
    omega
  · exact hAR
  · exact (Nat.cast_le.mpr node.2.le).trans hA'Z
  · exact hZR
  · exact hsmall node node.2 q q.2 (fun i ↦ (u i : ℕ))
      (fun i ↦ (u i).isLt)

/-- Iteration of the exact structured exponent-box extrapolation step along a
prescribed sequence of rectangular moment regions. -/
theorem boxMultipointMoments_iterate_extrapolation
    {F iota : Type*} [Field F] [NumberField F]
    [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) {n K : ℕ} (alpha : Fin n → F)
    (c : ExponentBox n K → ℤ) (L : ExponentBox n K → ℂ)
    (b0 Lambda : ℂ) (a : ExponentBox n K → ℤ)
    (r : ExponentBox n K → iota → ℤ) (ell : iota → ℂ)
    (A T S k : ℕ → ℕ) (R Z : ℕ → ℝ) (m : ℕ)
    {C V : ℕ} {U : ℝ}
    (hK : 0 < K) (hb0 : b0 ≠ 0) (hC : 1 ≤ C) (hV : 1 ≤ V)
    (hU : 0 ≤ U) (hc : ∀ x, (c x).natAbs ≤ C)
    (haV : ∀ x, ‖a x‖ ≤ (V : ℝ))
    (hrV : ∀ x i, ‖r x i‖ ≤ (V : ℝ))
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (boxMonomial alpha x))
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin (A 0), ∀ q : Fin (T 0),
      ∀ u : iota → Fin (S 0),
      multipointMomentValue (boxMonomial alpha) a r c node q
        (fun i ↦ u i) = 0)
    (hT : ∀ j, T (j + 1) + k j ≤ T j)
    (hS : ∀ j, S (j + 1) + k j ≤ S j)
    (hAR : ∀ j, (A j : ℝ) < R j)
    (hA'Z : ∀ j, (A (j + 1) : ℝ) ≤ Z j)
    (hZR : ∀ j, Z j ≤ R j)
    (hsmall : ∀ j, ∀ h < A (j + 1), ∀ q < T (j + 1),
      ∀ u : iota → ℕ, (∀ i, u i < S (j + 1)) →
      (Z j + A j) ^ (k j * A j) *
          (((K ^ n : ℕ) : ℝ) *
              (((C * V ^ (q + ∑ i, u i) : ℕ) : ℝ)) *
              Real.exp (U * R j) /
            (R j - A j) ^ (k j * A j)) <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ n + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (C * V ^ (q + ∑ i, u i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i))))) :
    ∀ node : Fin (A m), ∀ q : Fin (T m), ∀ u : iota → Fin (S m),
      multipointMomentValue (boxMonomial alpha) a r c node q
        (fun i ↦ u i) = 0 := by
  induction m with
  | zero => simpa using hmoment
  | succ m ih =>
      apply boxMultipointMoments_extend_of_extrapolation
        (A := A m) (T := T m) (S := S m) (k := k m)
        (A' := A (m + 1)) (T' := T (m + 1)) (S' := S (m + 1))
        (C := C) (V := V) (U := U) (R := R m) (Z := Z m)
        φ alpha c L b0 Lambda a r ell hK hb0 hC hV hU hc haV hrV
        hL hexp hcoord ih (hT m) (hS m) (hAR m) (hA'Z m) (hZR m)
        (hsmall m)

def hermiteJetMatrix (A k : ℕ) :
    Matrix (Fin (A * k)) (Fin (A * k)) ℤ := fun row m ↦
  let hj := finProdFinEquiv.symm row
  (m.1.choose hj.2.1 : ℤ) * (hj.1.1 : ℤ) ^ (m.1 - hj.2.1)

lemma hermiteJetMatrix_mulVec
    (A k : ℕ) (v : Fin (A * k) → ℂ) (h : Fin A) (j : Fin k) :
    ((Int.castRingHom ℂ).mapMatrix (hermiteJetMatrix A k)).mulVec v
        (finProdFinEquiv (h, j)) =
      (Polynomial.hasseDeriv (j : ℕ)
        (Polynomial.ofFn (A * k) v)).eval (h : ℂ) := by
  classical
  rw [Polynomial.ofFn_eq_sum_monomial, map_sum, Polynomial.eval_finset_sum]
  simp only [map_mul, Polynomial.hasseDeriv_monomial, Polynomial.eval_monomial,
    Matrix.mulVec, dotProduct, hermiteJetMatrix, Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hermiteJetMatrix,
    Equiv.symm_apply_apply]
  norm_num [map_mul, map_pow]
  push_cast
  ring

lemma hermiteJetMatrix_mulVec_eq_zero_imp
    (A k : ℕ) (v : Fin (A * k) → ℂ)
    (hv : ((Int.castRingHom ℂ).mapMatrix
      (hermiteJetMatrix A k)).mulVec v = 0) : v = 0 := by
  classical
  by_cases hN : A * k = 0
  · funext i
    exact Fin.elim0 (hN ▸ i)
  let p : Polynomial ℂ := Polynomial.ofFn (A * k) v
  have hjet : ∀ h : Fin A, ∀ j : Fin k,
      (Polynomial.hasseDeriv (j : ℕ) p).eval (h : ℂ) = 0 := by
    intro h j
    have hh := congrFun hv (finProdFinEquiv (h, j))
    rw [hermiteJetMatrix_mulVec] at hh
    exact hh
  have hdvd : ∀ h : Fin A,
      (Polynomial.X - Polynomial.C (h : ℂ)) ^ k ∣ p := by
    intro h
    rw [Polynomial.X_sub_C_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
    intro d hd
    change (Polynomial.taylor (h : ℂ) p).coeff d = 0
    rw [Polynomial.taylor_coeff]
    exact hjet h ⟨d, hd⟩
  have hinj : Function.Injective (fun h : Fin A ↦ (h : ℂ)) := by
    intro i j hij
    apply Fin.ext
    have hijR := congrArg Complex.re hij
    norm_num at hijR
    exact_mod_cast hijR
  have hpair : Pairwise (Function.onFun IsCoprime fun h : Fin A ↦
      (Polynomial.X - Polynomial.C (h : ℂ)) ^ k) := by
    intro i j hij
    exact ((Polynomial.pairwise_coprime_X_sub_C hinj) hij).pow
  have hprod : (∏ h : Fin A,
      (Polynomial.X - Polynomial.C (h : ℂ)) ^ k) ∣ p :=
    Fintype.prod_dvd_of_coprime hpair hdvd
  have hdegree : (∏ h : Fin A,
      (Polynomial.X - Polynomial.C (h : ℂ)) ^ k).natDegree = A * k := by
    rw [Polynomial.natDegree_prod_of_monic]
    · simp_rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
      simp
    · intro h hh
      exact (Polynomial.monic_X_sub_C _).pow _
  have hp : p = 0 := by
    by_contra hp0
    have hle := Polynomial.natDegree_le_of_dvd hprod hp0
    have hlt : p.natDegree < A * k := by
      simpa [p] using Polynomial.ofFn_natDegree_lt
        (Nat.one_le_iff_ne_zero.mpr hN) v
    rw [hdegree] at hle
    omega
  apply Polynomial.injective_ofFn (A * k)
  simpa [p] using hp

theorem hermiteJetMatrix_mulVec_injective (A k : ℕ) :
    Function.Injective
      ((Int.castRingHom ℂ).mapMatrix (hermiteJetMatrix A k)).mulVec := by
  intro v w hvw
  apply sub_eq_zero.mp
  apply hermiteJetMatrix_mulVec_eq_zero_imp A k
  rw [Matrix.mulVec_sub, hvw, sub_self]

lemma hermiteJetMatrix_det_ne_zero (A k : ℕ) :
    (hermiteJetMatrix A k).det ≠ 0 := by
  let M : Matrix (Fin (A * k)) (Fin (A * k)) ℂ :=
    (Int.castRingHom ℂ).mapMatrix (hermiteJetMatrix A k)
  have hunitM : IsUnit M :=
    Matrix.mulVec_injective_iff_isUnit.mp
      (hermiteJetMatrix_mulVec_injective A k)
  have hunitDet : IsUnit M.det :=
    (Matrix.isUnit_iff_isUnit_det M).mp hunitM
  have hdetC : M.det ≠ 0 := hunitDet.ne_zero
  intro hdet
  apply hdetC
  rw [← RingHom.map_det]
  simp [hdet, M]

lemma hermiteJetMatrix_entry_norm_le (A k : ℕ)
    (i j : Fin (A * k)) :
    ‖((Int.castRingHom ℂ).mapMatrix (hermiteJetMatrix A k)) i j‖ ≤
      (2 * (A + 1 : ℝ)) ^ (A * k) := by
  let hj := finProdFinEquiv.symm i
  have hchoose : j.1.choose hj.2.1 ≤ 2 ^ (A * k) :=
    (Nat.choose_le_two_pow _ _).trans
      (pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) j.2.le)
  have hnode : hj.1.1 ^ (j.1 - hj.2.1) ≤
      (A + 1) ^ (A * k) := by
    calc
      hj.1.1 ^ (j.1 - hj.2.1) ≤ (A + 1) ^ (j.1 - hj.2.1) := by
        apply pow_le_pow_left₀ (Nat.zero_le _) _ _
        omega
      _ ≤ (A + 1) ^ (A * k) := by
        apply pow_le_pow_right₀ (by omega)
        omega
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hermiteJetMatrix]
  change ‖((((j.1.choose hj.2.1 : ℕ) : ℤ) *
      (hj.1.1 : ℤ) ^ (j.1 - hj.2.1) : ℤ) : ℂ)‖ ≤ _
  rw [Complex.norm_intCast,
    abs_of_nonneg (show (0 : ℝ) ≤
      (((((j.1.choose hj.2.1 : ℕ) : ℤ) *
        (hj.1.1 : ℤ) ^ (j.1 - hj.2.1) : ℤ) : ℝ)) by positivity)]
  push_cast
  rw [mul_pow]
  have hchooseR : ((j.1.choose hj.2.1 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (A * k) := by exact_mod_cast hchoose
  have hnodeR : (hj.1.1 : ℝ) ^ (j.1 - hj.2.1) ≤
      (A + 1 : ℝ) ^ (A * k) := by exact_mod_cast hnode
  exact mul_le_mul hchooseR hnodeR
    (by positivity) (by positivity)

noncomputable def hermiteInterpolationBound (A k : ℕ) : ℝ :=
  ((A * k).factorial : ℝ) *
    ((2 * (A + 1 : ℝ)) ^ (A * k)) ^ (A * k)

lemma hermiteJetMatrix_adjugate_entry_norm_le (A k : ℕ)
    (i j : Fin (A * k)) :
    ‖(((Int.castRingHom ℂ).mapMatrix
      (hermiteJetMatrix A k)).adjugate i j)‖ ≤
      hermiteInterpolationBound A k := by
  let M : ℝ := (2 * (A + 1 : ℝ)) ^ (A * k)
  have hM : 1 ≤ M := by
    apply one_le_pow₀
    have hA : (0 : ℝ) ≤ A := by positivity
    nlinarith
  rw [Matrix.adjugate_apply]
  have hdet := Matrix.det_le
    (abv := IsAbsoluteValue.toAbsoluteValue (‖·‖ : ℂ → ℝ)) (x := M)
    (A := ((Int.castRingHom ℂ).mapMatrix
      (hermiteJetMatrix A k)).updateRow j (Pi.single i 1)) (by
      intro r c
      by_cases hr : r = j
      · subst r
        simp only [Matrix.updateRow_self]
        by_cases hc : c = i
        · subst c
          simp [hM]
        · simp [Pi.single_eq_of_ne hc, zero_le_one.trans hM]
      · rw [Matrix.updateRow_ne hr]
        exact hermiteJetMatrix_entry_norm_le A k r c)
  simpa [hermiteInterpolationBound, M, nsmul_eq_mul] using hdet

lemma one_le_hermiteJetMatrix_det_norm (A k : ℕ) :
    1 ≤ ‖((Int.castRingHom ℂ).mapMatrix
      (hermiteJetMatrix A k)).det‖ := by
  rw [← RingHom.map_det]
  change 1 ≤ ‖((hermiteJetMatrix A k).det : ℂ)‖
  rw [Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs (hermiteJetMatrix_det_ne_zero A k)

lemma exists_hermiteJetMatrix_solution
    (A k : ℕ) (y : Fin (A * k) → ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hy : ∀ i, ‖y i‖ ≤ δ) :
    ∃ v : Fin (A * k) → ℂ,
      ((Int.castRingHom ℂ).mapMatrix
          (hermiteJetMatrix A k)).mulVec v = y ∧
      ∀ i, ‖v i‖ ≤
        (A * k : ℝ) * hermiteInterpolationBound A k * δ := by
  classical
  let M : Matrix (Fin (A * k)) (Fin (A * k)) ℂ :=
    (Int.castRingHom ℂ).mapMatrix (hermiteJetMatrix A k)
  have hdet : M.det ≠ 0 := by
    have hdetZ := hermiteJetMatrix_det_ne_zero A k
    have hcast : ((hermiteJetMatrix A k).det : ℂ) ≠ 0 := by
      exact_mod_cast hdetZ
    change ((Int.castRingHom ℂ).mapMatrix
      (hermiteJetMatrix A k)).det ≠ 0
    rw [← RingHom.map_det]
    exact hcast
  have hunit : IsUnit M.det := hdet.isUnit
  refine ⟨M⁻¹.mulVec y, ?_, fun i ↦ ?_⟩
  · change M.mulVec (M⁻¹.mulVec y) = y
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hunit,
      Matrix.one_mulVec]
  · have hdetInv : ‖M.det⁻¹‖ ≤ (1 : ℝ) := by
      rw [norm_inv]
      apply (inv_le_one₀ (norm_pos_iff.mpr hdet)).2
      simpa [M] using one_le_hermiteJetMatrix_det_norm A k
    rw [Matrix.inv_def]
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply,
      smul_eq_mul, Ring.inverse_eq_inv]
    calc
      ‖∑ j, M.det⁻¹ * M.adjugate i j * y j‖ ≤
          ∑ j, ‖M.det⁻¹ * M.adjugate i j * y j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin (A * k),
          1 * hermiteInterpolationBound A k * δ := by
            gcongr with j hj
            simp only [norm_mul]
            have hB : 0 ≤ hermiteInterpolationBound A k := by
              unfold hermiteInterpolationBound
              positivity
            exact mul_le_mul
              (mul_le_mul hdetInv
                (by simpa [M] using
                  hermiteJetMatrix_adjugate_entry_norm_le A k i j)
                (norm_nonneg _) zero_le_one)
              (hy j) (norm_nonneg _) (mul_nonneg zero_le_one hB)
      _ = (A * k : ℝ) * hermiteInterpolationBound A k * δ := by
            simp [mul_assoc]

theorem exists_hermiteInterpolation
    (A k : ℕ) (hA : 0 < A) (hk : 0 < k)
    (y : Fin A → Fin k → ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hy : ∀ h j, ‖y h j‖ ≤ δ) :
    ∃ p : Polynomial ℂ,
      p.natDegree < A * k ∧
      (∀ (h : Fin A) (j : Fin k),
        (Polynomial.hasseDeriv (j : ℕ) p).eval (h : ℂ) = y h j) ∧
      ∀ m : Fin (A * k), ‖p.coeff m‖ ≤
        (A * k : ℝ) * hermiteInterpolationBound A k * δ := by
  classical
  let y' : Fin (A * k) → ℂ := fun row ↦
    y (finProdFinEquiv.symm row).1 (finProdFinEquiv.symm row).2
  obtain ⟨v, hv, hvbound⟩ := exists_hermiteJetMatrix_solution
    A k y' hδ (fun row ↦ hy _ _)
  refine ⟨Polynomial.ofFn (A * k) v,
    Polynomial.ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.ne_of_gt hA) (Nat.ne_of_gt hk))) v, ?_, ?_⟩
  · intro h j
    rw [← hermiteJetMatrix_mulVec]
    have hh := congrFun hv (finProdFinEquiv (h, j))
    change ((Int.castRingHom ℂ).mapMatrix
        (hermiteJetMatrix A k)).mulVec v (finProdFinEquiv (h, j)) =
      y (finProdFinEquiv.symm (finProdFinEquiv (h, j))).1
        (finProdFinEquiv.symm (finProdFinEquiv (h, j))).2 at hh
    rw [Equiv.symm_apply_apply] at hh
    exact hh
  · intro m
    rw [Polynomial.ofFn_coeff_eq_val_of_lt v m.isLt]
    exact hvbound m

lemma ofFn_eval_norm_le (N : ℕ) (v : Fin N → ℂ) {X : ℝ}
    (hX : 0 ≤ X) (hv : ∀ m, ‖v m‖ ≤ X) (z : ℂ) :
    ‖(Polynomial.ofFn N v).eval z‖ ≤
      (N : ℝ) * X * max 1 (‖z‖ ^ N) := by
  classical
  rw [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum]
  calc
    ‖∑ m : Fin N, (Polynomial.monomial (m : ℕ) (v m)).eval z‖ ≤
        ∑ m : Fin N, ‖(Polynomial.monomial (m : ℕ) (v m)).eval z‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m : Fin N, X * max 1 (‖z‖ ^ N) := by
      gcongr with m hm
      rw [Polynomial.eval_monomial, norm_mul, norm_pow]
      exact mul_le_mul (hv m)
        (pow_le_max_one_pow (norm_nonneg z) m.isLt.le)
        (pow_nonneg (norm_nonneg z) _) hX
    _ = (N : ℝ) * X * max 1 (‖z‖ ^ N) := by simp [mul_assoc]

lemma polynomial_eval_norm_le_of_natDegree_lt
    {p : Polynomial ℂ} {N : ℕ} (hdeg : p.natDegree < N) {X : ℝ}
    (hX : 0 ≤ X) (hcoeff : ∀ m : Fin N, ‖p.coeff m‖ ≤ X) (z : ℂ) :
    ‖p.eval z‖ ≤ (N : ℝ) * X * max 1 (‖z‖ ^ N) := by
  rw [← Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hdeg]
  apply ofFn_eval_norm_le N (Polynomial.toFn N p) hX
  intro m
  simpa [Polynomial.toFn] using hcoeff m

lemma iteratedDeriv_polynomial_eval (p : Polynomial ℂ) (j : ℕ) :
    iteratedDeriv j (fun z : ℂ ↦ p.eval z) =
      fun z ↦ ((Polynomial.derivative^[j]) p).eval z := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [show j + 1 = j + 1 by rfl, iteratedDeriv_succ, ih]
      funext z
      rw [Polynomial.deriv]
      simp [Function.iterate_succ_apply']

/-! ## Falling-factorial exponential polynomials -/

/-- The `v`-th derivative of the `m`-th descending Pochhammer polynomial,
evaluated at the natural node `h`, as a rational integer. -/
noncomputable def pochhammerJet (m v h : ℕ) : ℤ :=
  ((Polynomial.derivative^[v]) (descPochhammer ℤ m)).eval (h : ℤ)

lemma pochhammerJet_zero (m h : ℕ) :
    pochhammerJet m 0 h = (Nat.descFactorial h m : ℤ) := by
  simp [pochhammerJet, descPochhammer_eval_eq_descFactorial]

/-- Pochhammer jets commute with the distinguished embedding into `ℂ`. -/
lemma pochhammerJet_cast (m v h : ℕ) :
    (pochhammerJet m v h : ℂ) =
      ((Polynomial.derivative^[v])
        (descPochhammer ℂ m)).eval (h : ℂ) := by
  rw [pochhammerJet, ← descPochhammer_map (Int.castRingHom ℂ) m,
    Polynomial.iterate_derivative_map]
  change (Int.castRingHom ℂ)
      (((Polynomial.derivative^[v]) (descPochhammer ℤ m)).eval (h : ℤ)) =
    (((Polynomial.derivative^[v]) (descPochhammer ℤ m)).map
      (Int.castRingHom ℂ)).eval ((Int.castRingHom ℂ) (h : ℤ))
  rw [Polynomial.eval_map_apply]

/-- An auxiliary exponential polynomial in the falling-factorial basis.
The polynomial multiplicity supplies extra Siegel columns without changing
the exponential type. -/
noncomputable def pochhammerExponentialPolynomial
    {κ : Type*} [Fintype κ] (L : κ → ℂ) (P : ℕ)
    (c : κ → Fin P → ℂ) : ℂ → ℂ := fun z ↦
  ∑ x, ∑ m, c x m *
    (descPochhammer ℂ (m : ℕ)).eval z *
      Complex.exp (L x * z)

lemma iteratedDeriv_pochhammerExponentialTerm
    (L c z : ℂ) (m j : ℕ) :
    iteratedDeriv j (fun w : ℂ ↦
      c * (descPochhammer ℂ m).eval w * Complex.exp (L * w)) z =
      ∑ v ∈ Finset.range (j + 1),
        (j.choose v : ℂ) *
          (c * ((Polynomial.derivative^[v])
            (descPochhammer ℂ m)).eval z) *
          (L ^ (j - v) * Complex.exp (L * z)) := by
  have hp : ∀ w, AnalyticAt ℂ
      (fun z : ℂ ↦ (descPochhammer ℂ m).eval z) w := fun w ↦
    (AnalyticOnNhd.eval_polynomial (descPochhammer ℂ m)) w
      (Set.mem_univ w)
  have hcp : AnalyticAt ℂ
      (fun w : ℂ ↦ c * (descPochhammer ℂ m).eval w) z :=
    analyticAt_const.mul (hp z)
  rw [show (fun w : ℂ ↦
      c * (descPochhammer ℂ m).eval w * Complex.exp (L * w)) =
      (fun w : ℂ ↦ c * (descPochhammer ℂ m).eval w) *
        (fun w : ℂ ↦ Complex.exp (L * w)) by rfl]
  rw [iteratedDeriv_mul hcp.contDiffAt (by fun_prop)]
  apply Finset.sum_congr rfl
  intro v hv
  rw [iteratedDeriv_const_mul c (hp z).contDiffAt,
    congrFun (iteratedDeriv_polynomial_eval (descPochhammer ℂ m) v) z,
    congrFun (iteratedDeriv_cexp_const_mul (j - v) L) z]

/-- Leibniz expansion for a polynomial times one exponential.  This
slightly more general form is used after reserving an initial number of
polynomial derivatives in the falling-factorial auxiliary function. -/
lemma iteratedDeriv_polynomialExponentialTerm
    (L c z : ℂ) (p : Polynomial ℂ) (j : ℕ) :
    iteratedDeriv j (fun w : ℂ ↦
      c * p.eval w * Complex.exp (L * w)) z =
      ∑ t ∈ Finset.range (j + 1),
        (j.choose t : ℂ) *
          (c * ((Polynomial.derivative^[t]) p).eval z) *
          (L ^ (j - t) * Complex.exp (L * z)) := by
  have hp : ∀ w, AnalyticAt ℂ (fun z : ℂ ↦ p.eval z) w := fun w ↦
    (AnalyticOnNhd.eval_polynomial p) w (Set.mem_univ w)
  have hcp : AnalyticAt ℂ (fun w : ℂ ↦ c * p.eval w) z :=
    analyticAt_const.mul (hp z)
  rw [show (fun w : ℂ ↦ c * p.eval w * Complex.exp (L * w)) =
      (fun w : ℂ ↦ c * p.eval w) *
        (fun w : ℂ ↦ Complex.exp (L * w)) by rfl]
  rw [iteratedDeriv_mul hcp.contDiffAt (by fun_prop)]
  apply Finset.sum_congr rfl
  intro t ht
  rw [iteratedDeriv_const_mul c (hp z).contDiffAt,
    congrFun (iteratedDeriv_polynomial_eval p t) z,
    congrFun (iteratedDeriv_cexp_const_mul (j - t) L) z]

/-- Exact derivative expansion of a falling-factorial exponential
polynomial at an arbitrary complex point. -/
lemma iteratedDeriv_pochhammerExponentialPolynomial
    {κ : Type*} [Fintype κ] (L : κ → ℂ) (P : ℕ)
    (c : κ → Fin P → ℂ) (j : ℕ) (z : ℂ) :
    iteratedDeriv j (pochhammerExponentialPolynomial L P c) z =
      ∑ x, ∑ m, ∑ v ∈ Finset.range (j + 1),
        (j.choose v : ℂ) *
          (c x m * ((Polynomial.derivative^[v])
            (descPochhammer ℂ (m : ℕ))).eval z) *
          ((L x) ^ (j - v) * Complex.exp (L x * z)) := by
  unfold pochhammerExponentialPolynomial
  have houter : (fun w : ℂ ↦ ∑ x, ∑ m,
      c x m * (descPochhammer ℂ (m : ℕ)).eval w *
        Complex.exp (L x * w)) =
      ∑ x, (fun w : ℂ ↦ ∑ m,
        c x m * (descPochhammer ℂ (m : ℕ)).eval w *
          Complex.exp (L x * w)) := by
    funext w
    simp
  rw [houter]
  rw [iteratedDeriv_sum (I := Finset.univ) (by
    intro x hx
    apply ContDiffAt.sum
    intro m hm
    have hp : AnalyticAt ℂ
        (fun w : ℂ ↦ (descPochhammer ℂ (m : ℕ)).eval w) z :=
      (AnalyticOnNhd.eval_polynomial (descPochhammer ℂ (m : ℕ))) z
        (Set.mem_univ z)
    exact ((analyticAt_const.mul hp).mul (by fun_prop)).contDiffAt)]
  apply Finset.sum_congr rfl
  intro x hx
  have hinner : (fun w : ℂ ↦ ∑ m,
      c x m * (descPochhammer ℂ (m : ℕ)).eval w *
        Complex.exp (L x * w)) =
      ∑ m, (fun w : ℂ ↦
        c x m * (descPochhammer ℂ (m : ℕ)).eval w *
          Complex.exp (L x * w)) := by
    funext w
    simp
  rw [hinner]
  rw [iteratedDeriv_sum (I := Finset.univ) (by
    intro m hm
    have hp : AnalyticAt ℂ
        (fun w : ℂ ↦ (descPochhammer ℂ (m : ℕ)).eval w) z :=
      (AnalyticOnNhd.eval_polynomial (descPochhammer ℂ (m : ℕ))) z
        (Set.mem_univ z)
    exact ((analyticAt_const.mul hp).mul (by fun_prop)).contDiffAt)]
  apply Finset.sum_congr rfl
  intro m hm
  exact iteratedDeriv_pochhammerExponentialTerm
    (L x) (c x m) z (m : ℕ) j

/-- A falling-factorial auxiliary function with reserved polynomial jet and
logarithmic-moment indices.  Its value at a natural node is exactly the
corresponding algebraic Pochhammer moment. -/
noncomputable def pochhammerWeightedAuxiliary
    {κ iota : Type*} [Fintype κ] [Fintype iota]
    (L : κ → ℂ) (P : ℕ) (c : κ → Fin P → ℂ)
    (a : κ → ℂ) (r : κ → iota → ℂ)
    (v q : ℕ) (u : iota → ℕ) : ℂ → ℂ := fun z ↦
  ∑ x, ∑ m,
    (c x m * a x ^ q * ∏ i, r x i ^ u i) *
      ((Polynomial.derivative^[v])
        (descPochhammer ℂ (m : ℕ))).eval z *
      Complex.exp (L x * z)

/-- Exact derivative expansion of the weighted falling-factorial auxiliary
function.  Differentiation consumes polynomial-jet width and exponential
moment width independently. -/
lemma iteratedDeriv_pochhammerWeightedAuxiliary
    {κ iota : Type*} [Fintype κ] [Fintype iota]
    (L : κ → ℂ) (P : ℕ) (c : κ → Fin P → ℂ)
    (a : κ → ℂ) (r : κ → iota → ℂ)
    (v q j : ℕ) (u : iota → ℕ) (z : ℂ) :
    iteratedDeriv j
        (pochhammerWeightedAuxiliary L P c a r v q u) z =
      ∑ x, ∑ m, ∑ t ∈ Finset.range (j + 1),
        (j.choose t : ℂ) *
          ((c x m * a x ^ q * ∏ i, r x i ^ u i) *
            ((Polynomial.derivative^[v + t])
              (descPochhammer ℂ (m : ℕ))).eval z) *
          ((L x) ^ (j - t) * Complex.exp (L x * z)) := by
  unfold pochhammerWeightedAuxiliary
  have houter : (fun w : ℂ ↦ ∑ x, ∑ m,
      (c x m * a x ^ q * ∏ i, r x i ^ u i) *
        ((Polynomial.derivative^[v])
          (descPochhammer ℂ (m : ℕ))).eval w *
        Complex.exp (L x * w)) =
      ∑ x, (fun w : ℂ ↦ ∑ m,
        (c x m * a x ^ q * ∏ i, r x i ^ u i) *
          ((Polynomial.derivative^[v])
            (descPochhammer ℂ (m : ℕ))).eval w *
          Complex.exp (L x * w)) := by
    funext w
    simp
  rw [houter]
  rw [iteratedDeriv_sum (I := Finset.univ) (by
    intro x hx
    apply ContDiffAt.sum
    intro m hm
    have hp : AnalyticAt ℂ
        (fun w : ℂ ↦ ((Polynomial.derivative^[v])
          (descPochhammer ℂ (m : ℕ))).eval w) z :=
      (AnalyticOnNhd.eval_polynomial
        ((Polynomial.derivative^[v])
          (descPochhammer ℂ (m : ℕ)))) z (Set.mem_univ z)
    exact ((analyticAt_const.mul hp).mul (by fun_prop)).contDiffAt)]
  apply Finset.sum_congr rfl
  intro x hx
  have hinner : (fun w : ℂ ↦ ∑ m,
      (c x m * a x ^ q * ∏ i, r x i ^ u i) *
        ((Polynomial.derivative^[v])
          (descPochhammer ℂ (m : ℕ))).eval w *
        Complex.exp (L x * w)) =
      ∑ m, (fun w : ℂ ↦
        (c x m * a x ^ q * ∏ i, r x i ^ u i) *
          ((Polynomial.derivative^[v])
            (descPochhammer ℂ (m : ℕ))).eval w *
          Complex.exp (L x * w)) := by
    funext w
    simp
  rw [hinner]
  rw [iteratedDeriv_sum (I := Finset.univ) (by
    intro m hm
    have hp : AnalyticAt ℂ
        (fun w : ℂ ↦ ((Polynomial.derivative^[v])
          (descPochhammer ℂ (m : ℕ))).eval w) z :=
      (AnalyticOnNhd.eval_polynomial
        ((Polynomial.derivative^[v])
          (descPochhammer ℂ (m : ℕ)))) z (Set.mem_univ z)
    exact ((analyticAt_const.mul hp).mul (by fun_prop)).contDiffAt)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [iteratedDeriv_polynomialExponentialTerm]
  apply Finset.sum_congr rfl
  intro t ht
  congr 2
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- Uniform product bound for a descending Pochhammer polynomial on a
closed disk. -/
lemma norm_descPochhammer_eval_le
    {m P : ℕ} (hm : m < P) {z : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖(descPochhammer ℂ m).eval z‖ ≤ (R + P) ^ P := by
  rw [descPochhammer_eval_eq_prod_range, Complex.norm_prod]
  calc
    ∏ j ∈ Finset.range m, ‖z - (j : ℂ)‖ ≤
        ∏ _j ∈ Finset.range m, (R + P) := by
      apply Finset.prod_le_prod
      · intro j hj
        positivity
      · intro j hj
        have hjP : (j : ℝ) ≤ P := by
          exact_mod_cast (Finset.mem_range.mp hj).le.trans hm.le
        calc
          ‖z - (j : ℂ)‖ ≤ ‖z‖ + ‖(j : ℂ)‖ := norm_sub_le _ _
          _ = ‖z‖ + (j : ℝ) := by rw [Complex.norm_natCast]
          _ ≤ R + P := add_le_add hz hjP
    _ = (R + P) ^ m := by simp
    _ ≤ (R + P) ^ P := by
      apply pow_le_pow_right₀ _ hm.le
      have hP : (1 : ℝ) ≤ P := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : P ≠ 0))
      linarith

/-- Cauchy's estimate gives a uniform bound for every derivative of every
Pochhammer polynomial in the multiplicity block. -/
lemma norm_iterate_derivative_descPochhammer_eval_le
    {m P v : ℕ} (hm : m < P) {z : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖((Polynomial.derivative^[v]) (descPochhammer ℂ m)).eval z‖ ≤
      (v.factorial : ℝ) * (R + 1 + P) ^ P := by
  have hdiff : Differentiable ℂ
      (fun w : ℂ ↦ (descPochhammer ℂ m).eval w) := by
    fun_prop
  have hbound : ∀ w ∈ Metric.sphere z (1 : ℝ),
      ‖(descPochhammer ℂ m).eval w‖ ≤ (R + 1 + P) ^ P := by
    intro w hw
    have hdist : ‖w - z‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hw
    have hwR : ‖w‖ ≤ R + 1 := by
      calc
        ‖w‖ = ‖(w - z) + z‖ := by ring_nf
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ R + 1 := by rw [hdist]; linarith
    simpa [add_assoc] using
      norm_descPochhammer_eval_le hm (R := R + 1) (by linarith) hwR
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (f := fun w : ℂ ↦ (descPochhammer ℂ m).eval w)
    v (by norm_num : (0 : ℝ) < 1) hdiff.diffContOnCl hbound
  rw [congrFun (iteratedDeriv_polynomial_eval (descPochhammer ℂ m) v) z]
    at hcauchy
  simpa using hcauchy

/-- Boundary growth of a polynomially weighted auxiliary function.  The
Pochhammer dimension contributes only a polynomial factor and does not
increase the exponential type `U`. -/
theorem pochhammerWeightedAuxiliary_norm_le
    {κ iota : Type*} [Fintype κ] [Fintype iota]
    (L : κ → ℂ) (P : ℕ) (c : κ → Fin P → ℂ)
    (a : κ → ℂ) (r : κ → iota → ℂ)
    (v q : ℕ) (u : iota → ℕ) {z : ℂ} {C V U R : ℝ}
    (hC : 0 ≤ C) (hV : 1 ≤ V) (hU : 0 ≤ U) (hR : 0 ≤ R)
    (hc : ∀ x m, ‖c x m‖ ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ V) (hr : ∀ x i, ‖r x i‖ ≤ V)
    (hL : ∀ x, ‖L x‖ ≤ U) (hz : ‖z‖ ≤ R) :
    ‖pochhammerWeightedAuxiliary L P c a r v q u z‖ ≤
      (((Fintype.card κ * P : ℕ) : ℝ) *
        (C * V ^ (q + ∑ i, u i) *
          ((v.factorial : ℝ) * (R + 1 + P) ^ P) *
          Real.exp (U * R))) := by
  unfold pochhammerWeightedAuxiliary
  calc
    ‖∑ x, ∑ m,
        (c x m * a x ^ q * ∏ i, r x i ^ u i) *
          ((Polynomial.derivative^[v])
            (descPochhammer ℂ (m : ℕ))).eval z *
          Complex.exp (L x * z)‖ ≤
      ∑ x, ∑ m, ‖(c x m * a x ^ q * ∏ i, r x i ^ u i) *
          ((Polynomial.derivative^[v])
            (descPochhammer ℂ (m : ℕ))).eval z *
          Complex.exp (L x * z)‖ := by
        exact (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun x _ ↦ norm_sum_le _ _)
    _ ≤ ∑ _x : κ, ∑ _m : Fin P,
        C * V ^ (q + ∑ i, u i) *
          ((v.factorial : ℝ) * (R + 1 + P) ^ P) *
          Real.exp (U * R) := by
      gcongr with x hx m hm
      have hprod : ∏ i, ‖r x i ^ u i‖ ≤ V ^ (∑ i, u i) := by
        calc
          ∏ i, ‖r x i ^ u i‖ = ∏ i, ‖r x i‖ ^ u i := by
            apply Finset.prod_congr rfl
            intro i hi
            rw [norm_pow]
          _ ≤ ∏ i, V ^ u i := by
            gcongr with i hi
            exact hr x i
          _ = V ^ (∑ i, u i) := by
            rw [← Finset.prod_pow_eq_pow_sum]
      have hcoordinate : ‖c x m * a x ^ q * ∏ i, r x i ^ u i‖ ≤
          C * V ^ (q + ∑ i, u i) := by
        rw [norm_mul, norm_mul, norm_pow, Complex.norm_prod]
        calc
          ‖c x m‖ * ‖a x‖ ^ q * ∏ i, ‖r x i ^ u i‖ ≤
              C * V ^ q * V ^ (∑ i, u i) := by
            exact mul_le_mul
              (mul_le_mul (hc x m)
                (pow_le_pow_left₀ (norm_nonneg _) (ha x) q)
                (pow_nonneg (norm_nonneg _) _) hC)
              hprod (by positivity) (by positivity)
          _ = C * V ^ (q + ∑ i, u i) := by rw [pow_add]; ring
      have hpoly := norm_iterate_derivative_descPochhammer_eval_le
        m.isLt hR hz (v := v)
      have hexponential : ‖Complex.exp (L x * z)‖ ≤ Real.exp (U * R) := by
        rw [Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        calc
          (L x * z).re ≤ ‖L x * z‖ := Complex.re_le_norm _
          _ = ‖L x‖ * ‖z‖ := norm_mul _ _
          _ ≤ U * R := mul_le_mul (hL x) hz (norm_nonneg z) hU
      rw [norm_mul, norm_mul]
      exact mul_le_mul
        (mul_le_mul hcoordinate hpoly (norm_nonneg _) (by positivity))
        hexponential (norm_nonneg _) (by positivity)
    _ = (((Fintype.card κ * P : ℕ) : ℝ) *
        (C * V ^ (q + ∑ i, u i) *
          ((v.factorial : ℝ) * (R + 1 + P) ^ P) *
          Real.exp (U * R))) := by
      simp [Nat.cast_mul]
      ring

lemma pochhammerExponentialPolynomial_nat
    {κ : Type*} [Fintype κ] (L : κ → ℂ) (P : ℕ)
    (c : κ → Fin P → ℂ) (h : ℕ) :
    pochhammerExponentialPolynomial L P c (h : ℂ) =
      ∑ x, ∑ m, c x m * (Nat.descFactorial h (m : ℕ) : ℂ) *
        Complex.exp (L x * (h : ℂ)) := by
  unfold pochhammerExponentialPolynomial
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro m hm
  rw [descPochhammer_eval_eq_descFactorial]

/-- At a natural node the falling-factorial exponential polynomial is the
embedding of an explicit algebraic value. -/
lemma pochhammerExponentialPolynomial_nat_numberField
    {F κ : Type*} [Field F] [NumberField F] [Fintype κ]
    (φ : F →+* ℂ) (beta : κ → F) (L : κ → ℂ) (P : ℕ)
    (c : κ → Fin P → ℤ) (h : ℕ)
    (hexp : ∀ x, Complex.exp (L x) = φ (beta x)) :
    pochhammerExponentialPolynomial L P (fun x m ↦ (c x m : ℂ))
        (h : ℂ) =
      φ (∑ x, ∑ m, (c x m : F) *
        (Nat.descFactorial h (m : ℕ) : F) * beta x ^ h) := by
  rw [pochhammerExponentialPolynomial_nat, map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [map_mul, map_mul, map_intCast, map_natCast, map_pow]
  have hp : Complex.exp (L x * (h : ℂ)) = φ (beta x) ^ h := by
    calc
      Complex.exp (L x * (h : ℂ)) =
          Complex.exp ((h : ℂ) * L x) := by rw [mul_comm]
      _ = Complex.exp (L x) ^ h := Complex.exp_nat_mul _ _
      _ = φ (beta x) ^ h := by rw [hexp]
  rw [hp]

/-- An algebraic moment for a polynomially weighted auxiliary exponential
sum.  The extra index `v` records a derivative of the falling-factorial
polynomial, while `q,u` are the distinguished logarithmic coordinates. -/
noncomputable def pochhammerMultipointMomentValue
    {F κ iota : Type*} [CommRing F] [Fintype κ] [Fintype iota]
    (beta : κ → F) (a : κ → ℤ) (r : κ → iota → ℤ)
    (P : ℕ) (c : κ → Fin P → ℤ) (h v q : ℕ)
    (u : iota → ℕ) : F :=
  ∑ x, ∑ m, (c x m : F) * (pochhammerJet (m : ℕ) v h : F) *
    beta x ^ h * (a x : F) ^ q * ∏ i, (r x i : F) ^ u i

/-- The distinguished embedding turns an algebraic Pochhammer moment into
the corresponding complex weighted exponential value. -/
theorem pochhammerMultipointMomentValue_embedding
    {F κ iota : Type*} [Field F] [NumberField F]
    [Fintype κ] [Fintype iota]
    (φ : F →+* ℂ) (beta : κ → F)
    (a : κ → ℤ) (r : κ → iota → ℤ)
    (P : ℕ) (c : κ → Fin P → ℤ) (h v q : ℕ)
    (u : iota → ℕ) :
    φ (pochhammerMultipointMomentValue beta a r P c h v q u) =
      ∑ x, ∑ m, (c x m : ℂ) * (pochhammerJet (m : ℕ) v h : ℂ) *
        φ (beta x) ^ h * (a x : ℂ) ^ q *
          ∏ i, (r x i : ℂ) ^ u i := by
  simp [pochhammerMultipointMomentValue]

/-- Integral Pochhammer jets have an explicit factorial/product bound. -/
lemma natAbs_pochhammerJet_le
    {m P : ℕ} (hm : m < P) (v h : ℕ) :
    (pochhammerJet m v h).natAbs ≤
      v.factorial * (h + 1 + P) ^ P := by
  have hb := norm_iterate_derivative_descPochhammer_eval_le
    hm (v := v) (z := (h : ℂ)) (R := (h : ℝ))
      (by positivity) (by simp)
  rw [← pochhammerJet_cast, Complex.norm_intCast,
    ← Int.cast_abs, ← Nat.cast_natAbs] at hb
  exact_mod_cast hb

/-- At a natural node the weighted analytic auxiliary is the distinguished
embedding of its algebraic Pochhammer moment. -/
lemma pochhammerWeightedAuxiliary_nat_numberField
    {F κ iota : Type*} [Field F] [NumberField F]
    [Fintype κ] [Fintype iota]
    (φ : F →+* ℂ) (beta : κ → F) (L : κ → ℂ)
    (a : κ → ℤ) (r : κ → iota → ℤ)
    (P : ℕ) (c : κ → Fin P → ℤ) (h v q : ℕ)
    (u : iota → ℕ)
    (hexp : ∀ x, Complex.exp (L x) = φ (beta x)) :
    pochhammerWeightedAuxiliary L P (fun x m ↦ (c x m : ℂ))
        (fun x ↦ (a x : ℂ)) (fun x i ↦ (r x i : ℂ)) v q u
        (h : ℂ) =
      φ (pochhammerMultipointMomentValue beta a r P c h v q u) := by
  rw [pochhammerMultipointMomentValue_embedding]
  unfold pochhammerWeightedAuxiliary
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro m hm
  have hp : Complex.exp (L x * (h : ℂ)) = φ (beta x) ^ h := by
    calc
      Complex.exp (L x * (h : ℂ)) =
          Complex.exp ((h : ℂ) * L x) := by rw [mul_comm]
      _ = Complex.exp (L x) ^ h := Complex.exp_nat_mul _ _
      _ = φ (beta x) ^ h := by rw [hexp]
  rw [hp, ← pochhammerJet_cast]
  ring

/-- Coefficient bound after aggregating the polynomial multiplicity at one
node and one reserved moment index. -/
lemma pochhammerAggregatedCoefficient_natAbs_le
    {κ iota : Type*} [Fintype iota]
    (a : κ → ℤ) (r : κ → iota → ℤ)
    (P : ℕ) (c : κ → Fin P → ℤ) (x : κ) (h v q : ℕ)
    (u : iota → ℕ) (C V : ℕ)
    (hc : ∀ x m, (c x m).natAbs ≤ C)
    (ha : ∀ x, (a x).natAbs ≤ V)
    (hr : ∀ x i, (r x i).natAbs ≤ V) :
    (∑ m, c x m * pochhammerJet (m : ℕ) v h * a x ^ q *
      ∏ i, r x i ^ u i).natAbs ≤
        P * C * (v.factorial * (h + 1 + P) ^ P) *
          V ^ (q + ∑ i, u i) := by
  calc
    (∑ m, c x m * pochhammerJet (m : ℕ) v h * a x ^ q *
        ∏ i, r x i ^ u i).natAbs ≤
      ∑ m, (c x m * pochhammerJet (m : ℕ) v h * a x ^ q *
        ∏ i, r x i ^ u i).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _m : Fin P,
        C * (v.factorial * (h + 1 + P) ^ P) *
          V ^ q * V ^ (∑ i, u i) := by
      gcongr with m hm
      rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul,
        Int.natAbs_pow]
      rw [show (∏ i, r x i ^ u i).natAbs =
          ∏ i, (r x i).natAbs ^ u i by
        rw [show (∏ i, r x i ^ u i).natAbs =
          ∏ i, (r x i ^ u i).natAbs from
            map_prod Int.natAbsHom (fun i ↦ r x i ^ u i) Finset.univ]
        apply Finset.prod_congr rfl
        intro i hi
        rw [Int.natAbs_pow]]
      have hprod : ∏ i, (r x i).natAbs ^ u i ≤
          ∏ i, V ^ u i := by
        gcongr with i hi
        exact hr x i
      calc
        (c x m).natAbs * (pochhammerJet (m : ℕ) v h).natAbs *
            (a x).natAbs ^ q * ∏ i, (r x i).natAbs ^ u i ≤
          C * (v.factorial * (h + 1 + P) ^ P) *
            V ^ q * ∏ i, V ^ u i := by
          gcongr
          · exact hc x m
          · exact natAbs_pochhammerJet_le m.isLt v h
          · exact ha x
        _ = C * (v.factorial * (h + 1 + P) ^ P) *
            V ^ q * V ^ (∑ i, u i) := by
          rw [← Finset.prod_pow_eq_pow_sum]
    _ = P * C * (v.factorial * (h + 1 + P) ^ P) *
          V ^ (q + ∑ i, u i) := by
      simp [pow_add, mul_comm, mul_left_comm, mul_assoc]

/-- A rectangular block of Pochhammer moments forces the corresponding
polynomially weighted auxiliary function to vanish to the reserved order at
each known node.  The Leibniz index spends polynomial-jet width, while the
remaining exponential derivative spends logarithmic-moment width. -/
theorem iteratedDeriv_pochhammerWeightedAuxiliary_eq_zero_of_moments
    {F κ iota : Type*} [Field F] [NumberField F]
    [Fintype κ] [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) (beta : κ → F)
    (L : κ → ℂ) (b0 Lambda : ℂ)
    (a : κ → ℤ) (r : κ → iota → ℤ) (ell : iota → ℂ)
    (P : ℕ) (c : κ → Fin P → ℤ) {A V T S : ℕ}
    (hb0 : b0 ≠ 0)
    (hexp : ∀ x, Complex.exp (L x) = φ (beta x))
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin A, ∀ v : Fin V, ∀ q : Fin T,
      ∀ u : iota → Fin S,
        pochhammerMultipointMomentValue beta a r P c node v q
          (fun i ↦ u i) = 0)
    (node : Fin A) (v0 q0 : ℕ) (u0 : iota → ℕ) (j : ℕ)
    (hv : v0 + j < V) (hq : q0 + j < T)
    (hu : ∀ i, u0 i + j < S) :
    iteratedDeriv j
      (pochhammerWeightedAuxiliary L P (fun x m ↦ (c x m : ℂ))
        (fun x ↦ (a x : ℂ)) (fun x i ↦ (r x i : ℂ))
        v0 q0 u0) (node : ℂ) = 0 := by
  classical
  have hterm : ∀ t ∈ Finset.range (j + 1),
      ∑ x, ∑ m,
        ((c x m : ℂ) * (a x : ℂ) ^ q0 *
            ∏ i, (r x i : ℂ) ^ u0 i) *
          ((Polynomial.derivative^[v0 + t])
            (descPochhammer ℂ (m : ℕ))).eval (node : ℂ) *
          ((L x) ^ (j - t) * Complex.exp (L x * (node : ℂ))) = 0 := by
    intro t ht
    have htj : t ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp ht)
    have hvt : v0 + t < V := by omega
    let vt : Fin V := ⟨v0 + t, hvt⟩
    let s := j - t
    let d : κ → ℂ := fun x ↦
      (∑ m, (c x m : ℂ) *
        (pochhammerJet (m : ℕ) (v0 + t) node : ℂ)) *
        φ (beta x) ^ (node : ℕ) * (a x : ℂ) ^ q0 *
          ∏ i, (r x i : ℂ) ^ u0 i
    have hmomentC : ∀ q, q < s + 1 → ∀ p, p < s + 1 →
        ∀ w ∈ Finset.piAntidiag (Finset.univ : Finset iota) p,
          ∑ x, d x * (a x : ℂ) ^ q *
            ∏ i, (r x i : ℂ) ^ w i = 0 := by
      intro q hqs p hps w hw
      have hqT : q0 + q < T := by
        have hsle : s ≤ j := Nat.sub_le j t
        omega
      have hwle : ∀ i, w i ≤ p := by
        intro i
        exact Finset.single_le_sum (fun y _ ↦ Nat.zero_le (w y))
          (Finset.mem_univ i) |>.trans_eq (Finset.mem_piAntidiag.mp hw).1
      have huwS : ∀ i, u0 i + w i < S := by
        intro i
        have hsle : s ≤ j := Nat.sub_le j t
        have hwj : w i ≤ j := (hwle i).trans (by omega)
        exact (Nat.add_le_add_left hwj (u0 i)).trans_lt (hu i)
      let qT : Fin T := ⟨q0 + q, hqT⟩
      let uS : iota → Fin S := fun i ↦ ⟨u0 i + w i, huwS i⟩
      have hmapped := congrArg φ (hmoment node vt qT uS)
      rw [map_zero, pochhammerMultipointMomentValue_embedding] at hmapped
      rw [show (∑ x, d x * (a x : ℂ) ^ q *
          ∏ i, (r x i : ℂ) ^ w i) =
        ∑ x, ∑ m, (c x m : ℂ) *
          (pochhammerJet (m : ℕ) (v0 + t) node : ℂ) *
          φ (beta x) ^ (node : ℕ) *
          (a x : ℂ) ^ (q0 + q) *
          ∏ i, (r x i : ℂ) ^ (u0 i + w i) by
        apply Finset.sum_congr rfl
        intro x hx
        dsimp [d]
        simp_rw [pow_add, Finset.prod_mul_distrib]
        rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
          Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro m hm
        ring]
      simpa only [qT, uS] using hmapped
    have heq := auxiliaryDerivative_eq_pow_mul_binomialRemainder
      d L b0 Lambda (fun x ↦ (a x : ℂ))
        (fun x i ↦ (r x i : ℂ)) ell s (s + 1) (s + 1)
        (by omega) hcoord hmomentC
    have hrem : binomialRemainder d (fun x ↦ (a x : ℂ))
        (fun x ↦ ∑ i, (r x i : ℂ) * ell i) Lambda s (s + 1) = 0 := by
      rw [binomialRemainder]
      rw [show (Finset.range (s + 1)).filter (s + 1 ≤ ·) = ∅ by simp]
      simp
    rw [hrem, mul_zero] at heq
    have hzero : iteratedDeriv s (auxiliaryExponentialSum L d) 0 = 0 :=
      (mul_eq_zero.mp heq).resolve_left (pow_ne_zero _ hb0)
    rw [show (∑ x, ∑ m,
        ((c x m : ℂ) * (a x : ℂ) ^ q0 *
            ∏ i, (r x i : ℂ) ^ u0 i) *
          ((Polynomial.derivative^[v0 + t])
            (descPochhammer ℂ (m : ℕ))).eval (node : ℂ) *
          ((L x) ^ (j - t) * Complex.exp (L x * (node : ℂ)))) =
        iteratedDeriv s (auxiliaryExponentialSum L d) 0 by
      rw [iteratedDeriv_auxiliaryExponentialSum]
      simp only [mul_zero, Complex.exp_zero, mul_one]
      apply Finset.sum_congr rfl
      intro x hx
      have hp : Complex.exp (L x * (node : ℂ)) =
          φ (beta x) ^ (node : ℕ) := by
        calc
          Complex.exp (L x * (node : ℂ)) =
              Complex.exp ((node : ℂ) * L x) := by rw [mul_comm]
          _ = Complex.exp (L x) ^ (node : ℕ) := Complex.exp_nat_mul _ _
          _ = φ (beta x) ^ (node : ℕ) := by rw [hexp]
      rw [hp]
      dsimp [d]
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m hm
      rw [← pochhammerJet_cast]
      dsimp [s]
      ring]
    exact hzero
  rw [iteratedDeriv_pochhammerWeightedAuxiliary]
  rw [show (∑ x, ∑ m, ∑ t ∈ Finset.range (j + 1),
      (j.choose t : ℂ) *
        (((c x m : ℂ) * (a x : ℂ) ^ q0 *
            ∏ i, (r x i : ℂ) ^ u0 i) *
          ((Polynomial.derivative^[v0 + t])
            (descPochhammer ℂ (m : ℕ))).eval (node : ℂ)) *
        ((L x) ^ (j - t) * Complex.exp (L x * (node : ℂ)))) =
      ∑ t ∈ Finset.range (j + 1), (j.choose t : ℂ) *
        (∑ x, ∑ m,
          ((c x m : ℂ) * (a x : ℂ) ^ q0 *
              ∏ i, (r x i : ℂ) ^ u0 i) *
            ((Polynomial.derivative^[v0 + t])
              (descPochhammer ℂ (m : ℕ))).eval (node : ℂ) *
            ((L x) ^ (j - t) * Complex.exp (L x * (node : ℂ)))) by
    conv_lhs =>
      enter [2, x]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    ring]
  apply Finset.sum_eq_zero
  intro t ht
  rw [hterm t ht, mul_zero]

/-- Maximum-modulus extrapolation for a polynomially weighted auxiliary
function whose jets vanish at consecutive natural nodes. -/
theorem pochhammerWeightedAuxiliary_norm_le_of_nat_nodes
    {κ iota : Type*} [Fintype κ] [Fintype iota]
    (L : κ → ℂ) (P : ℕ) (c : κ → Fin P → ℂ)
    (a : κ → ℂ) (r : κ → iota → ℂ)
    (v q : ℕ) (u : iota → ℕ) (k A : ℕ)
    {z : ℂ} {C V U R Z : ℝ}
    (hC : 0 ≤ C) (hV : 1 ≤ V) (hU : 0 ≤ U)
    (hA : (A : ℝ) < R)
    (hc : ∀ x m, ‖c x m‖ ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ V) (hr : ∀ x i, ‖r x i‖ ≤ V)
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hzero : ∀ h < A, ∀ j < k,
      iteratedDeriv j (pochhammerWeightedAuxiliary L P c a r v q u)
        (h : ℂ) = 0)
    (hz : ‖z‖ ≤ Z) (hZR : Z ≤ R) :
    ‖pochhammerWeightedAuxiliary L P c a r v q u z‖ ≤
      (Z + A) ^ (k * A) *
        (((((Fintype.card κ * P : ℕ) : ℝ) *
            (C * V ^ (q + ∑ i, u i) *
              ((v.factorial : ℝ) * (R + 1 + P) ^ P) *
              Real.exp (U * R)))) /
          (R - A) ^ (k * A)) := by
  let s := natNodeFinset A
  have hR : 0 < R := lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ A) hA
  have hD : 0 < (R - A) ^ (k * A) := by positivity
  apply iteratedDeriv_norm_le_of_many_zeros
    (f := pochhammerWeightedAuxiliary L P c a r v q u)
    (s := s) (m := 0) (k := k) (R := R)
    (D := (R - A) ^ (k * A)) (E := (Z + A) ^ (k * A))
    (M := (((Fintype.card κ * P : ℕ) : ℝ) *
      (C * V ^ (q + ∑ i, u i) *
        ((v.factorial : ℝ) * (R + 1 + P) ^ P) *
        Real.exp (U * R))))
    hR hD
  · intro w
    unfold pochhammerWeightedAuxiliary
    have hinner : ∀ x : κ, AnalyticAt ℂ (fun z : ℂ ↦ ∑ m,
        (c x m * a x ^ q * ∏ i, r x i ^ u i) *
          ((Polynomial.derivative^[v])
            (descPochhammer ℂ (m : ℕ))).eval z *
          Complex.exp (L x * z)) w := by
      intro x
      have hs := Finset.analyticAt_fun_sum (𝕜 := ℂ)
        (Finset.univ : Finset (Fin P)) (fun m hm ↦ by
          have hp : AnalyticAt ℂ
              (fun z : ℂ ↦ ((Polynomial.derivative^[v])
                (descPochhammer ℂ (m : ℕ))).eval z) w :=
            (AnalyticOnNhd.eval_polynomial
              ((Polynomial.derivative^[v])
                (descPochhammer ℂ (m : ℕ)))) w (Set.mem_univ w)
          have hcst : AnalyticAt ℂ (fun _z : ℂ ↦
              c x m * a x ^ q * ∏ i, r x i ^ u i) w := analyticAt_const
          have he : AnalyticAt ℂ
              (fun z : ℂ ↦ Complex.exp (L x * z)) w := by fun_prop
          exact ((hcst.mul hp).mul he))
      simpa using hs
    have hs := Finset.analyticAt_fun_sum (𝕜 := ℂ)
      (Finset.univ : Finset κ) (fun x hx ↦ hinner x)
    simpa using hs
  · intro w hw j hj
    obtain ⟨h, hh, rfl⟩ := mem_natNodeFinset.mp hw
    simpa using hzero h hh j hj
  · intro w hw
    simp only [iteratedDeriv_zero]
    have hwNorm : ‖w‖ = R := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hw
    apply pochhammerWeightedAuxiliary_norm_le L P c a r v q u
      hC hV hU hR.le hc ha hr hL
    exact hwNorm.le
  · intro w hw
    simpa [s] using centeredPowerProduct_norm_lower
      (s := natNodeFinset A) (m := k) (A := (A : ℝ))
      (R := R) (by linarith)
      (fun x hx ↦ norm_le_of_mem_natNodeFinset hx) hw
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact hz.trans hZR
  · simpa [s] using centeredPowerProduct_norm_upper
      (s := natNodeFinset A) (m := k) (A := (A : ℝ)) (Z := Z)
      (fun x hx ↦ norm_le_of_mem_natNodeFinset hx) hz

/-- One exact extrapolation step for the structured Pochhammer moment
system.  Analytic smallness and the projective-height Liouville bound force
the target algebraic moment to vanish. -/
theorem boxPochhammerMomentValue_eq_zero_of_extrapolation
    {F iota : Type*} [Field F] [NumberField F]
    [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) {n K P : ℕ} (alpha : Fin n → F)
    (c : ExponentBox n K → Fin P → ℤ)
    (L : ExponentBox n K → ℂ) (b0 Lambda : ℂ)
    (a : ExponentBox n K → ℤ)
    (r : ExponentBox n K → iota → ℤ) (ell : iota → ℂ)
    {A W T S k h v0 q0 : ℕ} (u0 : iota → ℕ)
    {C V : ℕ} {U R Z : ℝ}
    (hK : 0 < K) (hP : 0 < P) (hb0 : b0 ≠ 0)
    (hC : 1 ≤ C) (hV : 1 ≤ V) (hU : 0 ≤ U)
    (hc : ∀ x m, (c x m).natAbs ≤ C)
    (haV : ∀ x, ‖a x‖ ≤ (V : ℝ))
    (hrV : ∀ x i, ‖r x i‖ ≤ (V : ℝ))
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (boxMonomial alpha x))
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin A, ∀ v : Fin W, ∀ q : Fin T,
      ∀ u : iota → Fin S,
        pochhammerMultipointMomentValue (boxMonomial alpha) a r P c
          node v q (fun i ↦ u i) = 0)
    (hv : v0 + k ≤ W) (hq : q0 + k ≤ T)
    (hu : ∀ i, u0 i + k ≤ S)
    (hAR : (A : ℝ) < R) (hhZ : (h : ℝ) ≤ Z) (hZR : Z ≤ R)
    (hsmall :
      (Z + A) ^ (k * A) *
          (((((K ^ n * P : ℕ) : ℝ) *
              ((C : ℝ) * (V : ℝ) ^ (q0 + ∑ i, u0 i) *
                ((v0.factorial : ℝ) * (R + 1 + P) ^ P) *
                Real.exp (U * R)))) /
            (R - A) ^ (k * A)) <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ n + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (P * C *
                (v0.factorial * (h + 1 + P) ^ P) *
                V ^ (q0 + ∑ i, u0 i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i))))) :
    pochhammerMultipointMomentValue (boxMonomial alpha) a r P c
      h v0 q0 u0 = 0 := by
  have hcComplex : ∀ x m, ‖(c x m : ℂ)‖ ≤ (C : ℝ) := by
    intro x m
    rw [Complex.norm_intCast, ← Int.cast_abs, ← Nat.cast_natAbs]
    exact_mod_cast hc x m
  have haComplex : ∀ x, ‖(a x : ℂ)‖ ≤ (V : ℝ) := by
    intro x
    simpa [Int.norm_eq_abs] using haV x
  have hrComplex : ∀ x i, ‖(r x i : ℂ)‖ ≤ (V : ℝ) := by
    intro x i
    simpa [Int.norm_eq_abs] using hrV x i
  have hzero : ∀ node < A, ∀ j < k,
      iteratedDeriv j
        (pochhammerWeightedAuxiliary L P (fun x m ↦ (c x m : ℂ))
          (fun x ↦ (a x : ℂ)) (fun x i ↦ (r x i : ℂ))
          v0 q0 u0) (node : ℂ) = 0 := by
    intro node hnode j hj
    apply iteratedDeriv_pochhammerWeightedAuxiliary_eq_zero_of_moments
      φ (boxMonomial alpha) L b0 Lambda a r ell P c hb0 hexp hcoord
      hmoment ⟨node, hnode⟩ v0 q0 u0 j
    · omega
    · omega
    · intro i
      exact (Nat.add_lt_add_left hj (u0 i)).trans_le (hu i)
  have hanalytic := pochhammerWeightedAuxiliary_norm_le_of_nat_nodes
    L P (fun x m ↦ (c x m : ℂ))
      (fun x ↦ (a x : ℂ)) (fun x i ↦ (r x i : ℂ))
      v0 q0 u0 k A (C := (C : ℝ)) (V := (V : ℝ))
      (U := U) (R := R) (Z := Z) (z := (h : ℂ))
      (by positivity) (by exact_mod_cast hV) hU hAR
      hcComplex haComplex hrComplex hL hzero (by simpa using hhZ) hZR
  have hanalytic' :
      ‖pochhammerWeightedAuxiliary L P (fun x m ↦ (c x m : ℂ))
          (fun x ↦ (a x : ℂ)) (fun x i ↦ (r x i : ℂ))
          v0 q0 u0 (h : ℂ)‖ ≤
        (Z + A) ^ (k * A) *
          (((((K ^ n * P : ℕ) : ℝ) *
              ((C : ℝ) * (V : ℝ) ^ (q0 + ∑ i, u0 i) *
                ((v0.factorial : ℝ) * (R + 1 + P) ^ P) *
                Real.exp (U * R)))) /
            (R - A) ^ (k * A)) := by
    simpa [ExponentBox] using hanalytic
  have heval := pochhammerWeightedAuxiliary_nat_numberField
    φ (boxMonomial alpha) L a r P c h v0 q0 u0 hexp
  let dZ : ExponentBox n K → ℤ := fun x ↦
    ∑ m, c x m * pochhammerJet (m : ℕ) v0 h * a x ^ q0 *
      ∏ i, r x i ^ u0 i
  have haNat : ∀ x, (a x).natAbs ≤ V := by
    intro x
    have hx := haComplex x
    rw [Complex.norm_intCast, ← Int.cast_abs, ← Nat.cast_natAbs] at hx
    exact_mod_cast hx
  have hrNat : ∀ x i, (r x i).natAbs ≤ V := by
    intro x i
    have hx := hrComplex x i
    rw [Complex.norm_intCast, ← Int.cast_abs, ← Nat.cast_natAbs] at hx
    exact_mod_cast hx
  have hd : ∀ x, (dZ x).natAbs ≤
      P * C * (v0.factorial * (h + 1 + P) ^ P) *
        V ^ (q0 + ∑ i, u0 i) := by
    intro x
    exact pochhammerAggregatedCoefficient_natAbs_le
      a r P c x h v0 q0 u0 C V hc haNat hrNat
  have hvalue :
      pochhammerMultipointMomentValue (boxMonomial alpha) a r P c
          h v0 q0 u0 = boxAuxiliaryAlgebraicValue alpha dZ h := by
    unfold pochhammerMultipointMomentValue boxAuxiliaryAlgebraicValue
    apply Finset.sum_congr rfl
    intro x hx
    dsimp [dZ]
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  by_contra hne
  have hneBox : boxAuxiliaryAlgebraicValue alpha dZ h ≠ 0 := by
    rwa [← hvalue]
  have hDbound : 1 ≤ P * C *
      (v0.factorial * (h + 1 + P) ^ P) *
        V ^ (q0 + ∑ i, u0 i) := by
    have hpos : 0 < P * C *
        (v0.factorial * (h + 1 + P) ^ P) *
          V ^ (q0 + ∑ i, u0 i) := by positivity
    omega
  have hlocal := boxAuxiliaryAlgebraicValue_projective_log_norm_lower
    φ alpha dZ hK hDbound hd hneBox
  have hlower :
      Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ n + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (P * C *
                (v0.factorial * (h + 1 + P) ^ P) *
                V ^ (q0 + ∑ i, u0 i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i)))) ≤
        ‖φ (boxAuxiliaryAlgebraicValue alpha dZ h)‖ := by
    have hnormPos : 0 < ‖φ (boxAuxiliaryAlgebraicValue alpha dZ h)‖ :=
      norm_pos_iff.mpr ((map_ne_zero φ).2 hneBox)
    calc
      _ ≤ Real.exp (Real.log
          ‖φ (boxAuxiliaryAlgebraicValue alpha dZ h)‖) :=
        Real.exp_le_exp.mpr hlocal
      _ = _ := Real.exp_log hnormPos
  rw [← hvalue, ← heval] at hlower
  linarith

/-- Uniform rectangular form of one exact Pochhammer extrapolation step. -/
theorem boxPochhammerMoments_extend_of_extrapolation
    {F iota : Type*} [Field F] [NumberField F]
    [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) {n K P : ℕ} (alpha : Fin n → F)
    (c : ExponentBox n K → Fin P → ℤ)
    (L : ExponentBox n K → ℂ) (b0 Lambda : ℂ)
    (a : ExponentBox n K → ℤ)
    (r : ExponentBox n K → iota → ℤ) (ell : iota → ℂ)
    {A W T S k A' W' T' S' : ℕ} {C V : ℕ} {U R Z : ℝ}
    (hK : 0 < K) (hP : 0 < P) (hb0 : b0 ≠ 0)
    (hC : 1 ≤ C) (hV : 1 ≤ V) (hU : 0 ≤ U)
    (hc : ∀ x m, (c x m).natAbs ≤ C)
    (haV : ∀ x, ‖a x‖ ≤ (V : ℝ))
    (hrV : ∀ x i, ‖r x i‖ ≤ (V : ℝ))
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (boxMonomial alpha x))
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin A, ∀ v : Fin W, ∀ q : Fin T,
      ∀ u : iota → Fin S,
        pochhammerMultipointMomentValue (boxMonomial alpha) a r P c
          node v q (fun i ↦ u i) = 0)
    (hW : W' + k ≤ W) (hT : T' + k ≤ T) (hS : S' + k ≤ S)
    (hAR : (A : ℝ) < R) (hA'Z : (A' : ℝ) ≤ Z) (hZR : Z ≤ R)
    (hsmall : ∀ h < A', ∀ v < W', ∀ q < T',
      ∀ u : iota → ℕ, (∀ i, u i < S') →
      (Z + A) ^ (k * A) *
          (((((K ^ n * P : ℕ) : ℝ) *
              ((C : ℝ) * (V : ℝ) ^ (q + ∑ i, u i) *
                ((v.factorial : ℝ) * (R + 1 + P) ^ P) *
                Real.exp (U * R)))) /
            (R - A) ^ (k * A)) <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ n + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (P * C *
                (v.factorial * (h + 1 + P) ^ P) *
                V ^ (q + ∑ i, u i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i))))) :
    ∀ node : Fin A', ∀ v : Fin W', ∀ q : Fin T',
      ∀ u : iota → Fin S',
        pochhammerMultipointMomentValue (boxMonomial alpha) a r P c
          node v q (fun i ↦ u i) = 0 := by
  intro node v q u
  apply boxPochhammerMomentValue_eq_zero_of_extrapolation
    (A := A) (W := W) (T := T) (S := S) (k := k)
    (h := (node : ℕ)) (v0 := (v : ℕ)) (q0 := (q : ℕ))
    (C := C) (V := V) (U := U) (R := R) (Z := Z)
    φ alpha c L b0 Lambda a r ell (fun i ↦ (u i : ℕ))
    hK hP hb0 hC hV hU hc haV hrV hL hexp hcoord hmoment
  · omega
  · omega
  · intro i
    have hui : (u i : ℕ) < S' := (u i).isLt
    omega
  · exact hAR
  · exact (Nat.cast_le.mpr node.isLt.le).trans hA'Z
  · exact hZR
  · exact hsmall node node.isLt v v.isLt q q.isLt
      (fun i ↦ (u i : ℕ)) (fun i ↦ (u i).isLt)

/-- Iteration of exact Pochhammer extrapolation through a prescribed
sequence of rectangular moment regions. -/
theorem boxPochhammerMoments_iterate_extrapolation
    {F iota : Type*} [Field F] [NumberField F]
    [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) {n K P : ℕ} (alpha : Fin n → F)
    (c : ExponentBox n K → Fin P → ℤ)
    (L : ExponentBox n K → ℂ) (b0 Lambda : ℂ)
    (a : ExponentBox n K → ℤ)
    (r : ExponentBox n K → iota → ℤ) (ell : iota → ℂ)
    (A W T S k : ℕ → ℕ) (R Z : ℕ → ℝ) (m : ℕ)
    {C V : ℕ} {U : ℝ}
    (hK : 0 < K) (hP : 0 < P) (hb0 : b0 ≠ 0)
    (hC : 1 ≤ C) (hV : 1 ≤ V) (hU : 0 ≤ U)
    (hc : ∀ x p, (c x p).natAbs ≤ C)
    (haV : ∀ x, ‖a x‖ ≤ (V : ℝ))
    (hrV : ∀ x i, ‖r x i‖ ≤ (V : ℝ))
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (boxMonomial alpha x))
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin (A 0), ∀ v : Fin (W 0),
      ∀ q : Fin (T 0), ∀ u : iota → Fin (S 0),
        pochhammerMultipointMomentValue (boxMonomial alpha) a r P c
          node v q (fun i ↦ u i) = 0)
    (hW : ∀ j, W (j + 1) + k j ≤ W j)
    (hT : ∀ j, T (j + 1) + k j ≤ T j)
    (hS : ∀ j, S (j + 1) + k j ≤ S j)
    (hAR : ∀ j, (A j : ℝ) < R j)
    (hA'Z : ∀ j, (A (j + 1) : ℝ) ≤ Z j)
    (hZR : ∀ j, Z j ≤ R j)
    (hsmall : ∀ j, ∀ h < A (j + 1), ∀ v < W (j + 1),
      ∀ q < T (j + 1), ∀ u : iota → ℕ,
      (∀ i, u i < S (j + 1)) →
      (Z j + A j) ^ (k j * A j) *
          (((((K ^ n * P : ℕ) : ℝ) *
              ((C : ℝ) * (V : ℝ) ^ (q + ∑ i, u i) *
                ((v.factorial : ℝ) * (R j + 1 + P) ^ P) *
                Real.exp (U * R j)))) /
            (R j - A j) ^ (k j * A j)) <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ n + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (P * C *
                (v.factorial * (h + 1 + P) ^ P) *
                V ^ (q + ∑ i, u i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i))))) :
    ∀ node : Fin (A m), ∀ v : Fin (W m),
      ∀ q : Fin (T m), ∀ u : iota → Fin (S m),
        pochhammerMultipointMomentValue (boxMonomial alpha) a r P c
          node v q (fun i ↦ u i) = 0 := by
  induction m with
  | zero => simpa using hmoment
  | succ m ih =>
      apply boxPochhammerMoments_extend_of_extrapolation
        (A := A m) (W := W m) (T := T m) (S := S m) (k := k m)
        (A' := A (m + 1)) (W' := W (m + 1))
        (T' := T (m + 1)) (S' := S (m + 1))
        (C := C) (V := V) (U := U) (R := R m) (Z := Z m)
        φ alpha c L b0 Lambda a r ell hK hP hb0 hC hV hU hc
        haV hrV hL hexp hcoord ih (hW m) (hT m) (hS m)
        (hAR m) (hA'Z m) (hZR m) (hsmall m)

/-- A nonzero falling-factorial coefficient table has a nonzero algebraic
sample before `card κ * P`.  This is the final confluent-Vandermonde
contradiction used after polynomial moment propagation. -/
theorem exists_pochhammerMultipointMomentValue_ne_zero
    {F κ iota : Type*} [Field F] [CharZero F]
    [Fintype κ] [Fintype iota]
    (beta : κ → F) (hbeta : Function.Injective beta)
    (hbeta0 : ∀ x, beta x ≠ 0)
    (a : κ → ℤ) (r : κ → iota → ℤ)
    (P : ℕ) (c : κ → Fin P → ℤ) (hc : c ≠ 0) :
    ∃ h : Fin (Fintype.card κ * P),
      pochhammerMultipointMomentValue beta a r P c h 0 0
        (fun _ ↦ 0) ≠ 0 := by
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let beta' : Fin (Fintype.card κ) → F := fun i ↦ beta (e.symm i)
  let c' : Fin (Fintype.card κ) → Fin P → F := fun i m ↦
    (c (e.symm i) m : F)
  have hbeta' : Function.Injective beta' := by
    intro i j hij
    apply e.symm.injective
    exact hbeta hij
  have hbeta0' : ∀ i, beta' i ≠ 0 := fun i ↦ hbeta0 (e.symm i)
  have hc' : c' ≠ 0 := by
    intro hz
    apply hc
    funext x m
    have hm := congrFun (congrFun hz (e x)) m
    dsimp [c'] at hm
    rw [Equiv.symm_apply_apply] at hm
    exact_mod_cast hm
  obtain ⟨h, hh⟩ :=
    exists_generalizedPochhammerExponentialSequence_ne_zero
      beta' hbeta' hbeta0' c' hc'
  refine ⟨h, ?_⟩
  change (∑ x, ∑ m, (c x m : F) *
      (pochhammerJet (m : ℕ) 0 (h : ℕ) : F) * beta x ^ (h : ℕ) *
      (a x : F) ^ 0 * ∏ i, (r x i : F) ^ 0) ≠ 0
  simp only [pochhammerJet_zero, Int.cast_natCast, pow_zero,
    mul_one, Finset.prod_const_one]
  change (∑ x, ∑ m, (c x m : F) *
      (Nat.descFactorial (h : ℕ) (m : ℕ) : F) *
      beta x ^ (h : ℕ)) ≠ 0
  rw [← e.symm.sum_comp (fun x ↦ ∑ m, (c x m : F) *
    (Nat.descFactorial (h : ℕ) (m : ℕ) : F) * beta x ^ (h : ℕ))]
  simpa [beta', c'] using hh

/-- Row indices for the integer moment system at the initial node.  The
first coordinate records the polynomial jet, followed by the usual
distinguished rectangular logarithmic moments. -/
abbrev PochhammerInitialMomentIndex (iota : Type*) (J T S : ℕ) :=
  Fin J × RectangularMomentIndex iota T S

/-- Integral initial-node moment matrix for the falling-factorial auxiliary
function.  Its columns are exponent-box points paired with polynomial
degrees. -/
noncomputable def pochhammerInitialMomentMatrix
    {κ iota : Type*} [Fintype κ] [Fintype iota]
    (a : κ → ℤ) (r : κ → iota → ℤ) (P J T S : ℕ) :
    Matrix (PochhammerInitialMomentIndex iota J T S) (κ × Fin P) ℤ :=
  fun vqu xm ↦
    pochhammerJet (xm.2 : ℕ) (vqu.1 : ℕ) 0 *
      a xm.1 ^ (vqu.2.1 : ℕ) *
        ∏ i, r xm.1 i ^ (vqu.2.2 i : ℕ)

/-- Siegel coefficients for the full initial polynomial-jet moment table.
The polynomial multiplicity `P` multiplies the available columns while the
number of rows is `J*T*S^rank`. -/
theorem exists_pochhammer_initial_moment_coefficients
    {κ iota : Type*} [Fintype κ] [Fintype iota]
    [DecidableEq iota]
    (a : κ → ℤ) (r : κ → iota → ℤ) (P J T S : ℕ)
    (_hP : 0 < P) (hJ : 0 < J) (hT : 0 < T) (hS : 0 < S)
    (hcard : J * T * S ^ Fintype.card iota < Fintype.card κ * P) :
    ∃ c : κ → Fin P → ℤ, c ≠ 0 ∧
      (∀ v : Fin J, ∀ q : Fin T, ∀ u : iota → Fin S,
        ∑ x, ∑ m, c x m * pochhammerJet (m : ℕ) (v : ℕ) 0 *
          a x ^ (q : ℕ) * ∏ i, r x i ^ (u i : ℕ) = 0) ∧
      ∀ x m, (c x m).natAbs ≤ Nat.ceil
        ((((Fintype.card κ * P : ℕ) : ℝ) *
            max 1 ‖pochhammerInitialMomentMatrix a r P J T S‖) ^
          ((((J * T * S ^ Fintype.card iota : ℕ) : ℝ)) /
            (((Fintype.card κ * P : ℕ) : ℝ) -
              ((J * T * S ^ Fintype.card iota : ℕ) : ℝ)))) := by
  let rows := PochhammerInitialMomentIndex iota J T S
  let cols := κ × Fin P
  let A : Matrix rows cols ℤ := pochhammerInitialMomentMatrix a r P J T S
  have hrowsCard : Fintype.card rows =
      J * T * S ^ Fintype.card iota := by
    simp [rows, PochhammerInitialMomentIndex, RectangularMomentIndex,
      Nat.mul_assoc]
  have hcolsCard : Fintype.card cols = Fintype.card κ * P := by
    simp [cols]
  have hrowsPos : 0 < Fintype.card rows := by
    rw [hrowsCard]
    positivity
  have hcard' : Fintype.card rows < Fintype.card cols := by
    simpa [hrowsCard, hcolsCard] using hcard
  obtain ⟨d, hd, hker, hbound⟩ :=
    exists_bounded_nonzero_integer_kernel A hcard' hrowsPos
  let c : κ → Fin P → ℤ := fun x m ↦ d (x, m)
  have hc : c ≠ 0 := by
    intro hz
    apply hd
    funext xm
    have hm := congrFun (congrFun hz xm.1) xm.2
    exact hm
  refine ⟨c, hc, ?_, ?_⟩
  · intro v q u
    have hrow := congrFun hker (v, q, u)
    dsimp [A, pochhammerInitialMomentMatrix, Matrix.mulVec,
      dotProduct] at hrow
    rw [Fintype.sum_prod_type] at hrow
    simpa [c, mul_assoc, mul_comm, mul_left_comm] using hrow
  · intro x m
    simpa [c, A, hrowsCard, hcolsCard] using hbound (x, m)

/-- Explicit sup-norm bound for the initial polynomial-jet moment matrix. -/
theorem pochhammerInitialMomentMatrix_norm_le
    {κ iota : Type*} [Fintype κ] [Fintype iota] [DecidableEq iota]
    (a : κ → ℤ) (r : κ → iota → ℤ) (P J T S : ℕ)
    {V : ℝ} (hV : 1 ≤ V)
    (ha : ∀ x, ‖a x‖ ≤ V) (hr : ∀ x i, ‖r x i‖ ≤ V) :
    ‖pochhammerInitialMomentMatrix a r P J T S‖ ≤
      (J.factorial : ℝ) * (1 + P) ^ P *
        V ^ (T + Fintype.card iota * S) := by
  have hRHS : 0 ≤ (J.factorial : ℝ) * (1 + P) ^ P *
      V ^ (T + Fintype.card iota * S) := by positivity
  rw [Matrix.norm_le_iff hRHS]
  intro vqu xm
  rw [pochhammerInitialMomentMatrix, norm_mul, norm_mul,
    norm_pow, norm_prod]
  have hjetNat := natAbs_pochhammerJet_le xm.2.isLt (vqu.1 : ℕ) 0
  have hjet : ‖pochhammerJet (xm.2 : ℕ) (vqu.1 : ℕ) 0‖ ≤
      (J.factorial : ℝ) * (1 + P) ^ P := by
    rw [Int.norm_eq_abs, ← Int.cast_abs, ← Nat.cast_natAbs]
    calc
      ((pochhammerJet (xm.2 : ℕ) (vqu.1 : ℕ) 0).natAbs : ℝ) ≤
          (((vqu.1 : ℕ).factorial * (0 + 1 + P) ^ P : ℕ) : ℝ) := by
        exact_mod_cast hjetNat
      _ ≤ ((J.factorial * (1 + P) ^ P : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_right _
          (Nat.factorial_le vqu.1.isLt.le)
      _ = (J.factorial : ℝ) * (1 + P) ^ P := by push_cast; ring
  have hprod : ∏ i, ‖r xm.1 i ^ (vqu.2.2 i : ℕ)‖ ≤
      V ^ (Fintype.card iota * S) := by
    calc
      ∏ i, ‖r xm.1 i ^ (vqu.2.2 i : ℕ)‖ =
          ∏ i, ‖r xm.1 i‖ ^ (vqu.2.2 i : ℕ) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [norm_pow]
      _ ≤ ∏ i, V ^ (vqu.2.2 i : ℕ) := by
        gcongr with i hi
        exact hr xm.1 i
      _ = V ^ (∑ i, (vqu.2.2 i : ℕ)) := by
        rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ V ^ (Fintype.card iota * S) := by
        apply pow_le_pow_right₀ hV
        calc
          ∑ i, (vqu.2.2 i : ℕ) ≤ ∑ _i : iota, S := by
            gcongr with i hi
            exact (vqu.2.2 i).isLt.le
          _ = Fintype.card iota * S := by simp
  have haPow : ‖a xm.1‖ ^ (vqu.2.1 : ℕ) ≤ V ^ T := by
    calc
      ‖a xm.1‖ ^ (vqu.2.1 : ℕ) ≤ V ^ (vqu.2.1 : ℕ) :=
        pow_le_pow_left₀ (norm_nonneg _) (ha xm.1) _
      _ ≤ V ^ T := pow_le_pow_right₀ hV vqu.2.1.isLt.le
  calc
    ‖pochhammerJet (xm.2 : ℕ) (vqu.1 : ℕ) 0‖ *
          ‖a xm.1‖ ^ (vqu.2.1 : ℕ) *
          ∏ i, ‖r xm.1 i ^ (vqu.2.2 i : ℕ)‖ ≤
      ((J.factorial : ℝ) * (1 + P) ^ P) * V ^ T *
        V ^ (Fintype.card iota * S) := by gcongr
    _ = (J.factorial : ℝ) * (1 + P) ^ P *
        V ^ (T + Fintype.card iota * S) := by rw [pow_add]; ring

theorem exists_bounded_polynomial_matching_jets
    (A k : ℕ) (hA : 0 < A) (hk : 0 < k)
    (f : ℂ → ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hjet : ∀ (h : Fin A) (j : Fin k),
      ‖iteratedDeriv (j : ℕ) f (h : ℂ) /
        (((j : ℕ).factorial : ℕ) : ℂ)‖ ≤ δ) :
    ∃ p : Polynomial ℂ,
      p.natDegree < A * k ∧
      (∀ (h : Fin A) (j : Fin k),
        iteratedDeriv (j : ℕ) (fun z : ℂ ↦ p.eval z) (h : ℂ) =
          iteratedDeriv (j : ℕ) f (h : ℂ)) ∧
      ∀ z : ℂ, ‖p.eval z‖ ≤
        (A * k : ℝ) *
          ((A * k : ℝ) * hermiteInterpolationBound A k * δ) *
          max 1 (‖z‖ ^ (A * k)) := by
  obtain ⟨p, hpdeg, hpjet, hpcoeff⟩ := exists_hermiteInterpolation
    A k hA hk
    (fun h j ↦ iteratedDeriv (j : ℕ) f (h : ℂ) /
      (((j : ℕ).factorial : ℕ) : ℂ))
    hδ hjet
  refine ⟨p, hpdeg, ?_, fun z ↦ ?_⟩
  · intro h j
    rw [iteratedDeriv_polynomial_eval]
    change ((Polynomial.derivative^[((j : ℕ))]) p).eval (h : ℂ) = _
    have hpoly := congrFun
      (Polynomial.factorial_smul_hasseDeriv (R := ℂ) (j : ℕ)) p
    have heval := congrArg (fun q : Polynomial ℂ ↦ q.eval (h : ℂ)) hpoly
    have heval' : (((j : ℕ).factorial : ℕ) : ℂ) *
        (Polynomial.hasseDeriv (j : ℕ) p).eval (h : ℂ) =
      ((Polynomial.derivative^[((j : ℕ))]) p).eval (h : ℂ) := by
      simpa [nsmul_eq_mul] using heval
    rw [← heval', hpjet]
    have hfac : ((((j : ℕ).factorial : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (j : ℕ)
    field_simp [hfac]
  · have hbound := polynomial_eval_norm_le_of_natDegree_lt hpdeg
      (X := ((A * k : ℕ) : ℝ) * hermiteInterpolationBound A k * δ)
      (by
        unfold hermiteInterpolationBound
        positivity)
      (fun m ↦ by simpa [Nat.cast_mul] using hpcoeff m) z
    simpa [Nat.cast_mul] using hbound

/-- Approximate Schwarz extrapolation from small normalized jets at the
consecutive integer nodes.  A bounded Hermite interpolation polynomial
absorbs the small jets, leaving a function with exact zeros. -/
theorem analytic_norm_le_of_approximate_nat_node_jets
    (f : ℂ → ℂ) (A k : ℕ) {z : ℂ} {δ M R Z : ℝ}
    (hA : 0 < A) (hk : 0 < k) (hδ : 0 ≤ δ)
    (hAR : (A : ℝ) < R) (hz : ‖z‖ ≤ Z) (hZR : Z ≤ R)
    (hf : ∀ w, AnalyticAt ℂ f w)
    (hjet : ∀ (h : Fin A) (j : Fin k),
      ‖iteratedDeriv (j : ℕ) f (h : ℂ) /
        (((j : ℕ).factorial : ℕ) : ℂ)‖ ≤ δ)
    (hboundary : ∀ w ∈ Metric.sphere (0 : ℂ) R, ‖f w‖ ≤ M) :
    ‖f z‖ ≤
      (Z + A) ^ (k * A) *
        ((M +
          (A * k : ℝ) *
            ((A * k : ℝ) * hermiteInterpolationBound A k * δ) *
            max 1 (R ^ (A * k))) /
          (R - A) ^ (k * A)) +
      (A * k : ℝ) *
        ((A * k : ℝ) * hermiteInterpolationBound A k * δ) *
        max 1 (Z ^ (A * k)) := by
  obtain ⟨p, hpdeg, hpjet, hpbound⟩ :=
    exists_bounded_polynomial_matching_jets A k hA hk f hδ hjet
  let g : ℂ → ℂ := fun w ↦ f w - p.eval w
  have hpAnalytic : ∀ w, AnalyticAt ℂ (fun x : ℂ ↦ p.eval x) w := by
    intro w
    exact (AnalyticOnNhd.eval_polynomial p) w (Set.mem_univ w)
  have hgAnalytic : ∀ w, AnalyticAt ℂ g w := by
    intro w
    exact (hf w).sub (hpAnalytic w)
  have hzero : ∀ a ∈ natNodeFinset A, ∀ j < k,
      iteratedDeriv (0 + j) g a = 0 := by
    intro a ha j hj
    obtain ⟨h, hh, rfl⟩ := mem_natNodeFinset.mp ha
    let h' : Fin A := ⟨h, hh⟩
    let j' : Fin k := ⟨j, hj⟩
    simp only [zero_add]
    change iteratedDeriv j
      (fun w : ℂ ↦ f w - p.eval w) (h : ℂ) = 0
    rw [show (fun w : ℂ ↦ f w - p.eval w) =
      f - (fun w : ℂ ↦ p.eval w) by rfl]
    rw [iteratedDeriv_sub (hf _).contDiffAt (hpAnalytic _).contDiffAt]
    exact sub_eq_zero.mpr (hpjet h' j').symm
  have hR : 0 < R := lt_trans (by positivity : (0 : ℝ) < A) hAR
  have hD : 0 < (R - A) ^ (k * A) := by positivity
  have hboundaryG : ∀ w ∈ Metric.sphere (0 : ℂ) R,
      ‖iteratedDeriv 0 g w‖ ≤
        M +
          (A * k : ℝ) *
            ((A * k : ℝ) * hermiteInterpolationBound A k * δ) *
            max 1 (R ^ (A * k)) := by
    intro w hw
    simp only [iteratedDeriv_zero]
    have hwNorm : ‖w‖ = R := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hw
    calc
      ‖g w‖ = ‖f w - p.eval w‖ := rfl
      _ ≤ ‖f w‖ + ‖p.eval w‖ := norm_sub_le _ _
      _ ≤ M +
          (A * k : ℝ) *
            ((A * k : ℝ) * hermiteInterpolationBound A k * δ) *
            max 1 (R ^ (A * k)) := by
        exact add_le_add (hboundary w hw)
          (by simpa [hwNorm] using hpbound w)
  have hgBound := iteratedDeriv_norm_le_of_many_zeros
    g (natNodeFinset A) 0 k hR hD hgAnalytic hzero hboundaryG
    (D := (R - A) ^ (k * A))
    (E := (Z + A) ^ (k * A))
    (M := M +
      (A * k : ℝ) *
        ((A * k : ℝ) * hermiteInterpolationBound A k * δ) *
        max 1 (R ^ (A * k)))
    (z := z)
    (fun w hw ↦ by
      simpa using centeredPowerProduct_norm_lower
        (s := natNodeFinset A) (m := k) (A := (A : ℝ))
        (R := R) (by linarith)
        (fun a ha ↦ norm_le_of_mem_natNodeFinset ha) hw)
    (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hz.trans hZR)
    (by
      simpa using centeredPowerProduct_norm_upper
        (s := natNodeFinset A) (m := k) (A := (A : ℝ)) (Z := Z)
        (fun a ha ↦ norm_le_of_mem_natNodeFinset ha) hz)
  simp only [iteratedDeriv_zero] at hgBound
  calc
    ‖f z‖ = ‖g z + p.eval z‖ := by simp [g]
    _ ≤ ‖g z‖ + ‖p.eval z‖ := norm_add_le _ _
    _ ≤ (Z + A) ^ (k * A) *
          ((M +
            (A * k : ℝ) *
              ((A * k : ℝ) * hermiteInterpolationBound A k * δ) *
              max 1 (R ^ (A * k))) /
            (R - A) ^ (k * A)) +
        (A * k : ℝ) *
          ((A * k : ℝ) * hermiteInterpolationBound A k * δ) *
          max 1 (Z ^ (A * k)) := by
      exact add_le_add hgBound (by
        have hpz := hpbound z
        have hpow : ‖z‖ ^ (A * k) ≤ Z ^ (A * k) :=
          pow_le_pow_left₀ (norm_nonneg z) hz (A * k)
        have hmax : max 1 (‖z‖ ^ (A * k)) ≤
            max 1 (Z ^ (A * k)) := max_le_max (le_refl 1) hpow
        exact hpz.trans (mul_le_mul_of_nonneg_left hmax (by
          unfold hermiteInterpolationBound
          positivity)))

theorem auxiliaryExponentialSum_normalized_jet_norm_le_of_multipoint_moments
    {kappa iota : Type*} [Fintype kappa] [Fintype iota]
    [DecidableEq iota]
    (c L : kappa → ℂ) (b0 Lambda : ℂ)
    (a : kappa → ℂ) (r : kappa → iota → ℂ)
    (ell : iota → ℂ) (A T S k : ℕ) {C M U : ℝ}
    (hC : 0 ≤ C) (hM : 1 ≤ M) (hU : 0 ≤ U)
    (hb0 : 1 ≤ ‖b0‖)
    (hc : ∀ x, ‖c x‖ ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ M)
    (hr : ∀ x, ‖∑ i, r x i * ell i‖ ≤ M)
    (hLambda : ‖Lambda‖ ≤ 1)
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hcoord : ∀ x, b0 * L x =
      a x * Lambda + ∑ i, r x i * ell i)
    (hmoment : ∀ node : Fin A, ∀ q, q < T → ∀ p, p < S →
      ∀ u ∈ Finset.piAntidiag (Finset.univ : Finset iota) p,
        ∑ x, (c x * Complex.exp (L x * (node : ℂ))) *
          a x ^ q * ∏ i, r x i ^ u i = 0)
    (hkS : k ≤ S) :
    ∀ (node : Fin A) (j : Fin k),
      ‖iteratedDeriv (j : ℕ) (auxiliaryExponentialSum L c) (node : ℂ) /
          (((j : ℕ).factorial : ℕ) : ℂ)‖ ≤
        ‖Lambda‖ ^ T *
          ((Fintype.card kappa : ℝ) *
            (C * Real.exp (U * A)) * M ^ k * (2 : ℝ) ^ k) := by
  intro node j
  let d : kappa → ℂ := fun x ↦ c x * Complex.exp (L x * (node : ℂ))
  have hd : ∀ x, ‖d x‖ ≤ C * Real.exp (U * A) := by
    intro x
    dsimp [d]
    rw [norm_mul, Complex.norm_exp]
    apply mul_le_mul (hc x)
    · apply Real.exp_le_exp.mpr
      calc
        (L x * (node : ℂ)).re ≤ ‖L x * (node : ℂ)‖ :=
          Complex.re_le_norm _
        _ = ‖L x‖ * (node : ℝ) := by
          rw [norm_mul, Complex.norm_natCast]
        _ ≤ U * A := by
          have hnode : (node : ℝ) ≤ (A : ℝ) := by
            exact_mod_cast node.isLt.le
          exact mul_le_mul (hL x) hnode (by positivity) hU
    · positivity
    · exact hC
  have hscaled := auxiliaryDerivative_norm_le_of_rectangular_moments
    d L b0 Lambda a r ell (j : ℕ) T S
    (C := C * Real.exp (U * A)) (M := M)
    (by omega) (by positivity) hM hd ha hr hLambda hcoord
    (fun q hq p hp u hu ↦ hmoment node q hq p hp u hu)
  have hderivEq :
      iteratedDeriv (j : ℕ) (auxiliaryExponentialSum L d) 0 =
        iteratedDeriv (j : ℕ) (auxiliaryExponentialSum L c) (node : ℂ) := by
    rw [iteratedDeriv_auxiliaryExponentialSum,
      iteratedDeriv_auxiliaryExponentialSum]
    simp only [mul_zero, Complex.exp_zero, mul_one]
    apply Finset.sum_congr rfl
    intro x hx
    dsimp [d]
    ring
  have hderiv :
      ‖iteratedDeriv (j : ℕ) (auxiliaryExponentialSum L c) (node : ℂ)‖ ≤
        ‖Lambda‖ ^ T *
          ((Fintype.card kappa : ℝ) *
            (C * Real.exp (U * A)) * M ^ (j : ℕ) * (2 : ℝ) ^ (j : ℕ)) := by
    rw [← hderivEq]
    calc
      ‖iteratedDeriv (j : ℕ) (auxiliaryExponentialSum L d) 0‖ ≤
          ‖b0‖ ^ (j : ℕ) *
            ‖iteratedDeriv (j : ℕ) (auxiliaryExponentialSum L d) 0‖ := by
        nth_rewrite 1 [← one_mul
          ‖iteratedDeriv (j : ℕ) (auxiliaryExponentialSum L d) 0‖]
        exact mul_le_mul_of_nonneg_right (one_le_pow₀ hb0) (norm_nonneg _)
      _ ≤ _ := hscaled
  rw [norm_div, norm_natCast]
  calc
    ‖iteratedDeriv (j : ℕ) (auxiliaryExponentialSum L c) (node : ℂ)‖ /
          ((j : ℕ).factorial : ℝ) ≤
        ‖iteratedDeriv (j : ℕ) (auxiliaryExponentialSum L c) (node : ℂ)‖ := by
      apply div_le_self (norm_nonneg _)
      exact_mod_cast Nat.factorial_pos (j : ℕ)
    _ ≤ ‖Lambda‖ ^ T *
          ((Fintype.card kappa : ℝ) *
            (C * Real.exp (U * A)) * M ^ (j : ℕ) * (2 : ℝ) ^ (j : ℕ)) :=
      hderiv
    _ ≤ ‖Lambda‖ ^ T *
          ((Fintype.card kappa : ℝ) *
            (C * Real.exp (U * A)) * M ^ k * (2 : ℝ) ^ k) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg Lambda) T)
      let P : ℝ := (Fintype.card kappa : ℝ) *
        (C * Real.exp (U * A))
      have hP : 0 ≤ P := by dsimp [P]; positivity
      have hMpow : M ^ (j : ℕ) ≤ M ^ k :=
        pow_le_pow_right₀ hM j.isLt.le
      have h2pow : (2 : ℝ) ^ (j : ℕ) ≤ 2 ^ k :=
        pow_le_pow_right₀ (by norm_num) j.isLt.le
      change P * M ^ (j : ℕ) * 2 ^ (j : ℕ) ≤ P * M ^ k * 2 ^ k
      calc
        P * M ^ (j : ℕ) * 2 ^ (j : ℕ) ≤
            P * M ^ k * 2 ^ (j : ℕ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hMpow hP) (by positivity)
        _ ≤ P * M ^ k * 2 ^ k :=
          mul_le_mul_of_nonneg_left h2pow (mul_nonneg hP (by positivity))

/-- Polynomial-multiplicity counterpart of the approximate jet estimate.
Exact rectangular Pochhammer moments absorb every derivative of the
falling-factorial coefficient, while the remaining exponential derivative
contributes the decisive factor `‖Lambda‖ ^ T`. -/
theorem pochhammerExponentialPolynomial_normalized_jet_norm_le_of_moments
    {F κ iota : Type*} [Field F] [NumberField F]
    [Fintype κ] [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) (beta : κ → F) (L : κ → ℂ)
    (b0 Lambda : ℂ) (a : κ → ℤ) (r : κ → iota → ℤ)
    (ell : iota → ℂ) (P : ℕ) (c : κ → Fin P → ℤ)
    (A W T S k : ℕ) {C M U : ℝ}
    (hC : 0 ≤ C) (hM : 1 ≤ M) (_hU : 0 ≤ U)
    (hb0 : 1 ≤ ‖b0‖) (hLambda : ‖Lambda‖ ≤ 1)
    (hc : ∀ x m, ‖(c x m : ℂ)‖ ≤ C)
    (ha : ∀ x, ‖(a x : ℂ)‖ ≤ M)
    (hr : ∀ x, ‖∑ i, (r x i : ℂ) * ell i‖ ≤ M)
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (beta x))
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin A, ∀ v : Fin W, ∀ q : Fin T,
      ∀ u : iota → Fin S,
        pochhammerMultipointMomentValue beta a r P c node v q
          (fun i ↦ u i) = 0)
    (hkW : k ≤ W) (hkS : k ≤ S) :
    ∀ (node : Fin A) (j : Fin k),
      ‖iteratedDeriv (j : ℕ)
          (pochhammerExponentialPolynomial L P
            (fun x m ↦ (c x m : ℂ))) (node : ℂ) /
          (((j : ℕ).factorial : ℕ) : ℂ)‖ ≤
        ‖Lambda‖ ^ T *
          (((Fintype.card κ * P : ℕ) : ℝ) * C *
            (k.factorial : ℝ) * (A + 1 + P) ^ P *
            Real.exp (U * A) * M ^ k * (2 : ℝ) ^ (2 * k)) := by
  intro node j
  have hterm : ∀ t ∈ Finset.range ((j : ℕ) + 1),
      ‖∑ x, ∑ m,
        ((c x m : ℂ) *
          ((Polynomial.derivative^[t])
            (descPochhammer ℂ (m : ℕ))).eval (node : ℂ)) *
          ((L x) ^ ((j : ℕ) - t) *
            Complex.exp (L x * (node : ℂ)))‖ ≤
        ‖Lambda‖ ^ T *
          ((Fintype.card κ : ℝ) *
            (((P : ℝ) * C * (k.factorial : ℝ) *
              (A + 1 + P) ^ P * Real.exp (U * A))) *
            M ^ k * (2 : ℝ) ^ k) := by
    intro t ht
    have htj : t ≤ (j : ℕ) := Nat.le_of_lt_succ (Finset.mem_range.mp ht)
    have htk : t < k := htj.trans_lt j.isLt
    let vt : Fin W := ⟨t, htk.trans_le hkW⟩
    let s := (j : ℕ) - t
    let d : κ → ℂ := fun x ↦
      (∑ m, (c x m : ℂ) *
        (pochhammerJet (m : ℕ) t node : ℂ)) *
        φ (beta x) ^ (node : ℕ)
    have hd : ∀ x, ‖d x‖ ≤
        (P : ℝ) * C * (k.factorial : ℝ) *
          (A + 1 + P) ^ P * Real.exp (U * A) := by
      intro x
      have hnode : ‖(node : ℂ)‖ ≤ (A : ℝ) := by
        rw [Complex.norm_natCast]
        exact_mod_cast node.isLt.le
      have hbeta : ‖φ (beta x) ^ (node : ℕ)‖ ≤ Real.exp (U * A) := by
        rw [← hexp, ← Complex.exp_nat_mul]
        rw [Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        calc
          (((node : ℂ) * L x).re) ≤ ‖(node : ℂ) * L x‖ :=
            Complex.re_le_norm _
          _ = (node : ℝ) * ‖L x‖ := by
            rw [norm_mul, Complex.norm_natCast]
          _ ≤ (A : ℝ) * U := by
            exact mul_le_mul (by exact_mod_cast node.isLt.le) (hL x)
              (norm_nonneg _) (by positivity)
          _ = U * A := by ring
      dsimp [d]
      rw [norm_mul]
      calc
        ‖∑ m, (c x m : ℂ) *
            (pochhammerJet (m : ℕ) t node : ℂ)‖ *
            ‖φ (beta x) ^ (node : ℕ)‖ ≤
          (∑ _m : Fin P, C *
            ((k.factorial : ℝ) * (A + 1 + P) ^ P)) *
              Real.exp (U * A) := by
            apply mul_le_mul _ hbeta (norm_nonneg _) (by positivity)
            calc
              ‖∑ m, (c x m : ℂ) *
                  (pochhammerJet (m : ℕ) t node : ℂ)‖ ≤
                ∑ m, ‖(c x m : ℂ) *
                  (pochhammerJet (m : ℕ) t node : ℂ)‖ := norm_sum_le _ _
              _ ≤ ∑ _m : Fin P, C *
                  ((k.factorial : ℝ) * (A + 1 + P) ^ P) := by
                gcongr with m hm
                rw [norm_mul]
                apply mul_le_mul (hc x m) _ (norm_nonneg _) hC
                have hp := norm_iterate_derivative_descPochhammer_eval_le
                  m.isLt (v := t) (z := (node : ℂ)) (R := (A : ℝ))
                    (by positivity) hnode
                calc
                  ‖(pochhammerJet (m : ℕ) t node : ℂ)‖ =
                      ‖((Polynomial.derivative^[t])
                        (descPochhammer ℂ (m : ℕ))).eval (node : ℂ)‖ := by
                    rw [pochhammerJet_cast]
                  _ ≤ (t.factorial : ℝ) * (A + 1 + P) ^ P := by
                    simpa using hp
                  _ ≤ (k.factorial : ℝ) * (A + 1 + P) ^ P := by
                    gcongr
        _ = (P : ℝ) * C * (k.factorial : ℝ) *
            (A + 1 + P) ^ P * Real.exp (U * A) := by
          simp
          ring
    have hmomentC : ∀ q, q < T → ∀ p, p < S →
        ∀ u ∈ Finset.piAntidiag (Finset.univ : Finset iota) p,
          ∑ x, d x * (a x : ℂ) ^ q *
            ∏ i, (r x i : ℂ) ^ u i = 0 := by
      intro q hq p hp u hu
      have hui : ∀ i, u i < S := by
        intro i
        have hi : u i ≤ p :=
          (Finset.single_le_sum (fun y _ ↦ Nat.zero_le (u y))
            (Finset.mem_univ i)).trans_eq (Finset.mem_piAntidiag.mp hu).1
        omega
      let qT : Fin T := ⟨q, hq⟩
      let uS : iota → Fin S := fun i ↦ ⟨u i, hui i⟩
      have hmapped := congrArg φ (hmoment node vt qT uS)
      rw [map_zero, pochhammerMultipointMomentValue_embedding] at hmapped
      rw [show (∑ x, d x * (a x : ℂ) ^ q *
          ∏ i, (r x i : ℂ) ^ u i) =
        ∑ x, ∑ m, (c x m : ℂ) *
          (pochhammerJet (m : ℕ) t node : ℂ) *
          φ (beta x) ^ (node : ℕ) * (a x : ℂ) ^ q *
          ∏ i, (r x i : ℂ) ^ u i by
        apply Finset.sum_congr rfl
        intro x hx
        dsimp [d]
        rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]]
      simpa only [qT, uS] using hmapped
    have hsS : s < S := by
      have hsk : s < k := (Nat.sub_le _ _).trans_lt j.isLt
      exact hsk.trans_le hkS
    have hscaled := auxiliaryDerivative_norm_le_of_rectangular_moments
      d L b0 Lambda (fun x ↦ (a x : ℂ))
        (fun x i ↦ (r x i : ℂ)) ell s T S
        (C := (P : ℝ) * C * (k.factorial : ℝ) *
          (A + 1 + P) ^ P * Real.exp (U * A)) (M := M)
        hsS (by positivity) hM hd ha hr hLambda hcoord hmomentC
    have hderiv : ‖iteratedDeriv s (auxiliaryExponentialSum L d) 0‖ ≤
        ‖Lambda‖ ^ T *
          ((Fintype.card κ : ℝ) *
            (((P : ℝ) * C * (k.factorial : ℝ) *
              (A + 1 + P) ^ P * Real.exp (U * A))) *
            M ^ s * (2 : ℝ) ^ s) := by
      calc
        ‖iteratedDeriv s (auxiliaryExponentialSum L d) 0‖ ≤
            ‖b0‖ ^ s * ‖iteratedDeriv s (auxiliaryExponentialSum L d) 0‖ := by
          nth_rewrite 1 [← one_mul ‖iteratedDeriv s
            (auxiliaryExponentialSum L d) 0‖]
          exact mul_le_mul_of_nonneg_right (one_le_pow₀ hb0) (norm_nonneg _)
        _ ≤ _ := hscaled
    have hderivK : ‖iteratedDeriv s (auxiliaryExponentialSum L d) 0‖ ≤
        ‖Lambda‖ ^ T *
          ((Fintype.card κ : ℝ) *
            (((P : ℝ) * C * (k.factorial : ℝ) *
              (A + 1 + P) ^ P * Real.exp (U * A))) *
            M ^ k * (2 : ℝ) ^ k) := by
      refine hderiv.trans ?_
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg _) _)
      have hsk : s ≤ k := (Nat.sub_le (j : ℕ) t).trans j.isLt.le
      calc
        (Fintype.card κ : ℝ) *
              ((P : ℝ) * C * (k.factorial : ℝ) *
                (A + 1 + P) ^ P * Real.exp (U * A)) *
            M ^ s * (2 : ℝ) ^ s ≤
            (Fintype.card κ : ℝ) *
              ((P : ℝ) * C * (k.factorial : ℝ) *
                (A + 1 + P) ^ P * Real.exp (U * A)) *
            M ^ k * (2 : ℝ) ^ s := by
          gcongr
        _ ≤ (Fintype.card κ : ℝ) *
              ((P : ℝ) * C * (k.factorial : ℝ) *
                (A + 1 + P) ^ P * Real.exp (U * A)) *
            M ^ k * (2 : ℝ) ^ k := by
          gcongr
          norm_num
    rw [show (∑ x, ∑ m,
        ((c x m : ℂ) *
          ((Polynomial.derivative^[t])
            (descPochhammer ℂ (m : ℕ))).eval (node : ℂ)) *
          ((L x) ^ ((j : ℕ) - t) *
            Complex.exp (L x * (node : ℂ)))) =
        iteratedDeriv s (auxiliaryExponentialSum L d) 0 by
      rw [iteratedDeriv_auxiliaryExponentialSum]
      simp only [mul_zero, Complex.exp_zero, mul_one]
      apply Finset.sum_congr rfl
      intro x hx
      have hp : Complex.exp (L x * (node : ℂ)) =
          φ (beta x) ^ (node : ℕ) := by
        calc
          Complex.exp (L x * (node : ℂ)) =
              Complex.exp ((node : ℂ) * L x) := by rw [mul_comm]
          _ = Complex.exp (L x) ^ (node : ℕ) := Complex.exp_nat_mul _ _
          _ = φ (beta x) ^ (node : ℕ) := by rw [hexp]
      rw [hp]
      dsimp [d, s]
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m hm
      rw [← pochhammerJet_cast]
      ring]
    exact hderivK
  rw [norm_div, norm_natCast]
  have hexpand := iteratedDeriv_pochhammerExponentialPolynomial
    L P (fun x m ↦ (c x m : ℂ)) (j : ℕ) (node : ℂ)
  rw [hexpand]
  calc
    ‖∑ x, ∑ m, ∑ t ∈ Finset.range ((j : ℕ) + 1),
        ((j : ℕ).choose t : ℂ) *
          ((c x m : ℂ) *
            ((Polynomial.derivative^[t])
              (descPochhammer ℂ (m : ℕ))).eval (node : ℂ)) *
          ((L x) ^ ((j : ℕ) - t) *
            Complex.exp (L x * (node : ℂ)))‖ /
        ((j : ℕ).factorial : ℝ) ≤
      ∑ t ∈ Finset.range ((j : ℕ) + 1),
        ((j : ℕ).choose t : ℝ) *
          (‖Lambda‖ ^ T *
            ((Fintype.card κ : ℝ) *
              (((P : ℝ) * C * (k.factorial : ℝ) *
                (A + 1 + P) ^ P * Real.exp (U * A))) *
              M ^ k * (2 : ℝ) ^ k)) := by
        have hsum : ‖∑ x, ∑ m, ∑ t ∈ Finset.range ((j : ℕ) + 1),
            ((j : ℕ).choose t : ℂ) *
              ((c x m : ℂ) *
                ((Polynomial.derivative^[t])
                  (descPochhammer ℂ (m : ℕ))).eval (node : ℂ)) *
              ((L x) ^ ((j : ℕ) - t) *
                Complex.exp (L x * (node : ℂ)))‖ ≤
          ∑ t ∈ Finset.range ((j : ℕ) + 1),
            ((j : ℕ).choose t : ℝ) *
              (‖Lambda‖ ^ T *
                ((Fintype.card κ : ℝ) *
                  (((P : ℝ) * C * (k.factorial : ℝ) *
                    (A + 1 + P) ^ P * Real.exp (U * A))) *
                  M ^ k * (2 : ℝ) ^ k)) := by
          rw [show (∑ x, ∑ m, ∑ t ∈ Finset.range ((j : ℕ) + 1),
              ((j : ℕ).choose t : ℂ) *
                ((c x m : ℂ) *
                  ((Polynomial.derivative^[t])
                    (descPochhammer ℂ (m : ℕ))).eval (node : ℂ)) *
                ((L x) ^ ((j : ℕ) - t) *
                  Complex.exp (L x * (node : ℂ)))) =
            ∑ t ∈ Finset.range ((j : ℕ) + 1),
              ((j : ℕ).choose t : ℂ) *
                (∑ x, ∑ m,
                  ((c x m : ℂ) *
                    ((Polynomial.derivative^[t])
                      (descPochhammer ℂ (m : ℕ))).eval (node : ℂ)) *
                  ((L x) ^ ((j : ℕ) - t) *
                    Complex.exp (L x * (node : ℂ)))) by
              conv_lhs =>
                enter [2, x]
                rw [Finset.sum_comm]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro t ht
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x hx
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro m hm
              ring]
          calc
            ‖∑ t ∈ Finset.range ((j : ℕ) + 1),
                ((j : ℕ).choose t : ℂ) *
                  (∑ x, ∑ m,
                    ((c x m : ℂ) *
                      ((Polynomial.derivative^[t])
                        (descPochhammer ℂ (m : ℕ))).eval (node : ℂ)) *
                    ((L x) ^ ((j : ℕ) - t) *
                      Complex.exp (L x * (node : ℂ))))‖ ≤
              ∑ t ∈ Finset.range ((j : ℕ) + 1),
                ‖((j : ℕ).choose t : ℂ) *
                  (∑ x, ∑ m,
                    ((c x m : ℂ) *
                      ((Polynomial.derivative^[t])
                        (descPochhammer ℂ (m : ℕ))).eval (node : ℂ)) *
                    ((L x) ^ ((j : ℕ) - t) *
                      Complex.exp (L x * (node : ℂ))))‖ := norm_sum_le _ _
            _ ≤ _ := by
              gcongr with t ht
              rw [norm_mul, Complex.norm_natCast]
              exact mul_le_mul_of_nonneg_left (hterm t ht) (by positivity)
        have hfac : (1 : ℝ) ≤ (j : ℕ).factorial := by
          exact_mod_cast Nat.factorial_pos (j : ℕ)
        exact (div_le_self (by positivity) hfac).trans hsum
    _ = ((2 : ℝ) ^ (j : ℕ)) *
          (‖Lambda‖ ^ T *
            ((Fintype.card κ : ℝ) *
              (((P : ℝ) * C * (k.factorial : ℝ) *
                (A + 1 + P) ^ P * Real.exp (U * A))) *
              M ^ k * (2 : ℝ) ^ k)) := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose (j : ℕ)
    _ ≤ ‖Lambda‖ ^ T *
          (((Fintype.card κ * P : ℕ) : ℝ) * C *
            (k.factorial : ℝ) * (A + 1 + P) ^ P *
            Real.exp (U * A) * M ^ k * (2 : ℝ) ^ (2 * k)) := by
      have h2 : (2 : ℝ) ^ (j : ℕ) ≤ 2 ^ k :=
        pow_le_pow_right₀ (by norm_num) j.isLt.le
      calc
        (2 : ℝ) ^ (j : ℕ) *
            (‖Lambda‖ ^ T *
              ((Fintype.card κ : ℝ) *
                (((P : ℝ) * C * (k.factorial : ℝ) *
                  (A + 1 + P) ^ P * Real.exp (U * A))) *
                M ^ k * (2 : ℝ) ^ k)) ≤
            (2 : ℝ) ^ k *
              (‖Lambda‖ ^ T *
                ((Fintype.card κ : ℝ) *
                  (((P : ℝ) * C * (k.factorial : ℝ) *
                    (A + 1 + P) ^ P * Real.exp (U * A))) *
                  M ^ k * (2 : ℝ) ^ k)) := by
              exact mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = _ := by
          push_cast
          rw [two_mul, pow_add]
          ring

theorem pochhammerWeightedAuxiliary_normalized_jet_norm_le_of_moments
    {F κ iota : Type*} [Field F] [NumberField F]
    [Fintype κ] [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) (beta : κ → F) (L : κ → ℂ)
    (b0 Lambda : ℂ) (a : κ → ℤ) (r : κ → iota → ℤ)
    (ell : iota → ℂ) (P : ℕ) (c : κ → Fin P → ℤ)
    (A W T S k Q v0 q0 : ℕ) (u0 : iota → ℕ) {C V U : ℝ}
    (hC : 0 ≤ C) (hV : 1 ≤ V) (_hU : 0 ≤ U)
    (hb0 : 1 ≤ ‖b0‖) (hLambda : ‖Lambda‖ ≤ 1)
    (hc : ∀ x m, ‖(c x m : ℂ)‖ ≤ C)
    (ha : ∀ x, ‖(a x : ℂ)‖ ≤ V)
    (hrV : ∀ x i, ‖(r x i : ℂ)‖ ≤ V)
    (hr : ∀ x, ‖∑ i, (r x i : ℂ) * ell i‖ ≤ V)
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (beta x))
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin A, ∀ v : Fin W, ∀ q : Fin T,
      ∀ u : iota → Fin S,
        pochhammerMultipointMomentValue beta a r P c node v q
          (fun i ↦ u i) = 0)
    (hvW : v0 + k ≤ W) (hqT : q0 + Q ≤ T)
    (huS : ∀ i, u0 i + k ≤ S) :
    ∀ (node : Fin A) (j : Fin k),
      ‖iteratedDeriv (j : ℕ)
          (pochhammerWeightedAuxiliary L P (fun x m ↦ (c x m : ℂ))
            (fun x ↦ (a x : ℂ)) (fun x i ↦ (r x i : ℂ))
            v0 q0 u0) (node : ℂ) /
          (((j : ℕ).factorial : ℕ) : ℂ)‖ ≤
        ‖Lambda‖ ^ Q *
          (((Fintype.card κ * P : ℕ) : ℝ) * C *
            V ^ (q0 + ∑ i, u0 i) * ((v0 + k).factorial : ℝ) *
            (A + 1 + P) ^ P * Real.exp (U * A) *
            V ^ k * (2 : ℝ) ^ (2 * k)) := by
  intro node j
  have hterm : ∀ t ∈ Finset.range ((j : ℕ) + 1),
      ‖∑ x, ∑ m,
        ((c x m : ℂ) * (a x : ℂ) ^ q0 *
            ∏ i, (r x i : ℂ) ^ u0 i) *
          ((Polynomial.derivative^[v0 + t])
            (descPochhammer ℂ (m : ℕ))).eval (node : ℂ) *
          ((L x) ^ ((j : ℕ) - t) *
            Complex.exp (L x * (node : ℂ)))‖ ≤
        ‖Lambda‖ ^ Q *
          ((Fintype.card κ : ℝ) *
            (((P : ℝ) * C * V ^ (q0 + ∑ i, u0 i) *
              ((v0 + k).factorial : ℝ) *
              (A + 1 + P) ^ P * Real.exp (U * A))) *
            V ^ k * (2 : ℝ) ^ k) := by
    intro t ht
    have htj : t ≤ (j : ℕ) := Nat.le_of_lt_succ (Finset.mem_range.mp ht)
    have htk : t < k := htj.trans_lt j.isLt
    have hvt : v0 + t < W := by omega
    let vt : Fin W := ⟨v0 + t, hvt⟩
    let s := (j : ℕ) - t
    let d : κ → ℂ := fun x ↦
      (∑ m, (c x m : ℂ) *
        (pochhammerJet (m : ℕ) (v0 + t) node : ℂ)) *
        φ (beta x) ^ (node : ℕ) * (a x : ℂ) ^ q0 *
          ∏ i, (r x i : ℂ) ^ u0 i
    have hd : ∀ x, ‖d x‖ ≤
        (P : ℝ) * C * V ^ (q0 + ∑ i, u0 i) *
          ((v0 + k).factorial : ℝ) *
          (A + 1 + P) ^ P * Real.exp (U * A) := by
      intro x
      have hnode : ‖(node : ℂ)‖ ≤ (A : ℝ) := by
        rw [Complex.norm_natCast]
        exact_mod_cast node.isLt.le
      have hbeta : ‖φ (beta x) ^ (node : ℕ)‖ ≤ Real.exp (U * A) := by
        rw [← hexp, ← Complex.exp_nat_mul]
        rw [Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        calc
          (((node : ℂ) * L x).re) ≤ ‖(node : ℂ) * L x‖ :=
            Complex.re_le_norm _
          _ = (node : ℝ) * ‖L x‖ := by
            rw [norm_mul, Complex.norm_natCast]
          _ ≤ (A : ℝ) * U := by
            exact mul_le_mul (by exact_mod_cast node.isLt.le) (hL x)
              (norm_nonneg _) (by positivity)
          _ = U * A := by ring
      have hprod : ∏ i, ‖(r x i : ℂ) ^ u0 i‖ ≤
          V ^ (∑ i, u0 i) := by
        calc
          ∏ i, ‖(r x i : ℂ) ^ u0 i‖ =
              ∏ i, ‖(r x i : ℂ)‖ ^ u0 i := by
            apply Finset.prod_congr rfl
            intro i hi
            rw [norm_pow]
          _ ≤ ∏ i, V ^ u0 i := by
            gcongr with i hi
            exact hrV x i
          _ = V ^ (∑ i, u0 i) := by
            rw [← Finset.prod_pow_eq_pow_sum]
      have hweight : ‖(a x : ℂ) ^ q0 *
          ∏ i, (r x i : ℂ) ^ u0 i‖ ≤
          V ^ (q0 + ∑ i, u0 i) := by
        rw [norm_mul, norm_pow, Complex.norm_prod, pow_add]
        exact mul_le_mul
          (pow_le_pow_left₀ (norm_nonneg _) (ha x) q0) hprod
          (by positivity) (by positivity)
      have hsum : ‖∑ m, (c x m : ℂ) *
          (pochhammerJet (m : ℕ) (v0 + t) node : ℂ)‖ ≤
          (P : ℝ) * C * ((v0 + k).factorial : ℝ) *
            (A + 1 + P) ^ P := by
        calc
          ‖∑ m, (c x m : ℂ) *
              (pochhammerJet (m : ℕ) (v0 + t) node : ℂ)‖ ≤
            ∑ m, ‖(c x m : ℂ) *
              (pochhammerJet (m : ℕ) (v0 + t) node : ℂ)‖ := norm_sum_le _ _
          _ ≤ ∑ _m : Fin P, C *
              (((v0 + k).factorial : ℝ) * (A + 1 + P) ^ P) := by
            gcongr with m hm
            rw [norm_mul]
            apply mul_le_mul (hc x m) _ (norm_nonneg _) hC
            have hp := norm_iterate_derivative_descPochhammer_eval_le
              m.isLt (v := v0 + t) (z := (node : ℂ)) (R := (A : ℝ))
                (by positivity) hnode
            calc
              ‖(pochhammerJet (m : ℕ) (v0 + t) node : ℂ)‖ =
                  ‖((Polynomial.derivative^[v0 + t])
                    (descPochhammer ℂ (m : ℕ))).eval (node : ℂ)‖ := by
                rw [pochhammerJet_cast]
              _ ≤ (((v0 + t).factorial : ℝ) *
                    (A + 1 + P) ^ P) := by simpa using hp
              _ ≤ ((v0 + k).factorial : ℝ) *
                    (A + 1 + P) ^ P := by
                gcongr
          _ = (P : ℝ) * C * ((v0 + k).factorial : ℝ) *
              (A + 1 + P) ^ P := by simp; ring
      dsimp [d]
      rw [norm_mul, norm_mul, norm_mul]
      calc
        ‖∑ m, (c x m : ℂ) *
              (pochhammerJet (m : ℕ) (v0 + t) node : ℂ)‖ *
            ‖φ (beta x) ^ (node : ℕ)‖ *
            ‖(a x : ℂ) ^ q0‖ *
            ‖∏ i, (r x i : ℂ) ^ u0 i‖ =
          ‖∑ m, (c x m : ℂ) *
              (pochhammerJet (m : ℕ) (v0 + t) node : ℂ)‖ *
            ‖φ (beta x) ^ (node : ℕ)‖ *
            ‖(a x : ℂ) ^ q0 * ∏ i, (r x i : ℂ) ^ u0 i‖ := by
              rw [norm_mul]
              ring
        _ ≤ ((P : ℝ) * C * ((v0 + k).factorial : ℝ) *
              (A + 1 + P) ^ P) * Real.exp (U * A) *
              V ^ (q0 + ∑ i, u0 i) := by gcongr
        _ = (P : ℝ) * C * V ^ (q0 + ∑ i, u0 i) *
              ((v0 + k).factorial : ℝ) *
              (A + 1 + P) ^ P * Real.exp (U * A) := by ring
    have hmomentC : ∀ q, q < Q → ∀ p, p < k →
        ∀ u ∈ Finset.piAntidiag (Finset.univ : Finset iota) p,
          ∑ x, d x * (a x : ℂ) ^ q *
            ∏ i, (r x i : ℂ) ^ u i = 0 := by
      intro q hq p hp u hu
      have hui : ∀ i, u0 i + u i < S := by
        intro i
        have hi : u i ≤ p :=
          (Finset.single_le_sum (fun y _ ↦ Nat.zero_le (u y))
            (Finset.mem_univ i)).trans_eq (Finset.mem_piAntidiag.mp hu).1
        have hik : u i < k := hi.trans_lt hp
        exact (Nat.add_lt_add_left hik (u0 i)).trans_le (huS i)
      let qT : Fin T := ⟨q0 + q, by omega⟩
      let uS : iota → Fin S := fun i ↦ ⟨u0 i + u i, hui i⟩
      have hmapped := congrArg φ (hmoment node vt qT uS)
      rw [map_zero, pochhammerMultipointMomentValue_embedding] at hmapped
      rw [show (∑ x, d x * (a x : ℂ) ^ q *
          ∏ i, (r x i : ℂ) ^ u i) =
        ∑ x, ∑ m, (c x m : ℂ) *
          (pochhammerJet (m : ℕ) (v0 + t) node : ℂ) *
          φ (beta x) ^ (node : ℕ) * (a x : ℂ) ^ (q0 + q) *
          ∏ i, (r x i : ℂ) ^ (u0 i + u i) by
        apply Finset.sum_congr rfl
        intro x hx
        dsimp [d]
        simp_rw [pow_add, Finset.prod_mul_distrib]
        rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
          Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro m hm
        ring]
      simpa only [qT, uS] using hmapped
    have hsK : s < k := (Nat.sub_le _ _).trans_lt j.isLt
    have hscaled := auxiliaryDerivative_norm_le_of_rectangular_moments
      d L b0 Lambda (fun x ↦ (a x : ℂ))
        (fun x i ↦ (r x i : ℂ)) ell s Q k
        (C := (P : ℝ) * C * V ^ (q0 + ∑ i, u0 i) *
          ((v0 + k).factorial : ℝ) *
          (A + 1 + P) ^ P * Real.exp (U * A)) (M := V)
        hsK (by positivity) hV hd ha hr hLambda hcoord hmomentC
    have hderiv : ‖iteratedDeriv s (auxiliaryExponentialSum L d) 0‖ ≤
        ‖Lambda‖ ^ Q *
          ((Fintype.card κ : ℝ) *
            (((P : ℝ) * C * V ^ (q0 + ∑ i, u0 i) *
              ((v0 + k).factorial : ℝ) *
              (A + 1 + P) ^ P * Real.exp (U * A))) *
            V ^ s * (2 : ℝ) ^ s) := by
      calc
        ‖iteratedDeriv s (auxiliaryExponentialSum L d) 0‖ ≤
            ‖b0‖ ^ s * ‖iteratedDeriv s (auxiliaryExponentialSum L d) 0‖ := by
          nth_rewrite 1 [← one_mul ‖iteratedDeriv s
            (auxiliaryExponentialSum L d) 0‖]
          exact mul_le_mul_of_nonneg_right (one_le_pow₀ hb0) (norm_nonneg _)
        _ ≤ _ := hscaled
    have hderivK : ‖iteratedDeriv s (auxiliaryExponentialSum L d) 0‖ ≤
        ‖Lambda‖ ^ Q *
          ((Fintype.card κ : ℝ) *
            (((P : ℝ) * C * V ^ (q0 + ∑ i, u0 i) *
              ((v0 + k).factorial : ℝ) *
              (A + 1 + P) ^ P * Real.exp (U * A))) *
            V ^ k * (2 : ℝ) ^ k) := by
      refine hderiv.trans ?_
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg _) _)
      have hsk : s ≤ k := (Nat.sub_le (j : ℕ) t).trans j.isLt.le
      gcongr
      norm_num
    rw [show (∑ x, ∑ m,
        ((c x m : ℂ) * (a x : ℂ) ^ q0 *
            ∏ i, (r x i : ℂ) ^ u0 i) *
          ((Polynomial.derivative^[v0 + t])
            (descPochhammer ℂ (m : ℕ))).eval (node : ℂ) *
          ((L x) ^ ((j : ℕ) - t) *
            Complex.exp (L x * (node : ℂ)))) =
        iteratedDeriv s (auxiliaryExponentialSum L d) 0 by
      rw [iteratedDeriv_auxiliaryExponentialSum]
      simp only [mul_zero, Complex.exp_zero, mul_one]
      apply Finset.sum_congr rfl
      intro x hx
      have hp : Complex.exp (L x * (node : ℂ)) =
          φ (beta x) ^ (node : ℕ) := by
        calc
          Complex.exp (L x * (node : ℂ)) =
              Complex.exp ((node : ℂ) * L x) := by rw [mul_comm]
          _ = Complex.exp (L x) ^ (node : ℕ) := Complex.exp_nat_mul _ _
          _ = φ (beta x) ^ (node : ℕ) := by rw [hexp]
      rw [hp]
      dsimp [d, s]
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m hm
      rw [← pochhammerJet_cast]
      ring]
    exact hderivK
  rw [norm_div, norm_natCast]
  rw [iteratedDeriv_pochhammerWeightedAuxiliary]
  calc
    ‖∑ x, ∑ m, ∑ t ∈ Finset.range ((j : ℕ) + 1),
        ((j : ℕ).choose t : ℂ) *
          (((c x m : ℂ) * (a x : ℂ) ^ q0 *
              ∏ i, (r x i : ℂ) ^ u0 i) *
            ((Polynomial.derivative^[v0 + t])
              (descPochhammer ℂ (m : ℕ))).eval (node : ℂ)) *
          ((L x) ^ ((j : ℕ) - t) *
            Complex.exp (L x * (node : ℂ)))‖ /
        ((j : ℕ).factorial : ℝ) ≤
      ∑ t ∈ Finset.range ((j : ℕ) + 1),
        ((j : ℕ).choose t : ℝ) *
          (‖Lambda‖ ^ Q *
            ((Fintype.card κ : ℝ) *
              (((P : ℝ) * C * V ^ (q0 + ∑ i, u0 i) *
                ((v0 + k).factorial : ℝ) *
                (A + 1 + P) ^ P * Real.exp (U * A))) *
              V ^ k * (2 : ℝ) ^ k)) := by
        have hsum : ‖∑ x, ∑ m, ∑ t ∈ Finset.range ((j : ℕ) + 1),
            ((j : ℕ).choose t : ℂ) *
              (((c x m : ℂ) * (a x : ℂ) ^ q0 *
                  ∏ i, (r x i : ℂ) ^ u0 i) *
                ((Polynomial.derivative^[v0 + t])
                  (descPochhammer ℂ (m : ℕ))).eval (node : ℂ)) *
              ((L x) ^ ((j : ℕ) - t) *
                Complex.exp (L x * (node : ℂ)))‖ ≤
          ∑ t ∈ Finset.range ((j : ℕ) + 1),
            ((j : ℕ).choose t : ℝ) *
              (‖Lambda‖ ^ Q *
                ((Fintype.card κ : ℝ) *
                  (((P : ℝ) * C * V ^ (q0 + ∑ i, u0 i) *
                    ((v0 + k).factorial : ℝ) *
                    (A + 1 + P) ^ P * Real.exp (U * A))) *
                  V ^ k * (2 : ℝ) ^ k)) := by
          rw [show (∑ x, ∑ m, ∑ t ∈ Finset.range ((j : ℕ) + 1),
              ((j : ℕ).choose t : ℂ) *
                (((c x m : ℂ) * (a x : ℂ) ^ q0 *
                    ∏ i, (r x i : ℂ) ^ u0 i) *
                  ((Polynomial.derivative^[v0 + t])
                    (descPochhammer ℂ (m : ℕ))).eval (node : ℂ)) *
                ((L x) ^ ((j : ℕ) - t) *
                  Complex.exp (L x * (node : ℂ)))) =
            ∑ t ∈ Finset.range ((j : ℕ) + 1),
              ((j : ℕ).choose t : ℂ) *
                (∑ x, ∑ m,
                  ((c x m : ℂ) * (a x : ℂ) ^ q0 *
                      ∏ i, (r x i : ℂ) ^ u0 i) *
                    ((Polynomial.derivative^[v0 + t])
                      (descPochhammer ℂ (m : ℕ))).eval (node : ℂ) *
                  ((L x) ^ ((j : ℕ) - t) *
                    Complex.exp (L x * (node : ℂ)))) by
              conv_lhs =>
                enter [2, x]
                rw [Finset.sum_comm]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro t ht
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x hx
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro m hm
              ring]
          calc
            ‖∑ t ∈ Finset.range ((j : ℕ) + 1),
                ((j : ℕ).choose t : ℂ) *
                  (∑ x, ∑ m,
                    ((c x m : ℂ) * (a x : ℂ) ^ q0 *
                        ∏ i, (r x i : ℂ) ^ u0 i) *
                      ((Polynomial.derivative^[v0 + t])
                        (descPochhammer ℂ (m : ℕ))).eval (node : ℂ) *
                    ((L x) ^ ((j : ℕ) - t) *
                      Complex.exp (L x * (node : ℂ))))‖ ≤
              ∑ t ∈ Finset.range ((j : ℕ) + 1),
                ‖((j : ℕ).choose t : ℂ) *
                  (∑ x, ∑ m,
                    ((c x m : ℂ) * (a x : ℂ) ^ q0 *
                        ∏ i, (r x i : ℂ) ^ u0 i) *
                      ((Polynomial.derivative^[v0 + t])
                        (descPochhammer ℂ (m : ℕ))).eval (node : ℂ) *
                    ((L x) ^ ((j : ℕ) - t) *
                      Complex.exp (L x * (node : ℂ))))‖ := norm_sum_le _ _
            _ ≤ _ := by
              gcongr with t ht
              rw [norm_mul, Complex.norm_natCast]
              exact mul_le_mul_of_nonneg_left (hterm t ht) (by positivity)
        have hfac : (1 : ℝ) ≤ (j : ℕ).factorial := by
          exact_mod_cast Nat.factorial_pos (j : ℕ)
        exact (div_le_self (by positivity) hfac).trans hsum
    _ = ((2 : ℝ) ^ (j : ℕ)) *
          (‖Lambda‖ ^ Q *
            ((Fintype.card κ : ℝ) *
              (((P : ℝ) * C * V ^ (q0 + ∑ i, u0 i) *
                ((v0 + k).factorial : ℝ) *
                (A + 1 + P) ^ P * Real.exp (U * A))) *
              V ^ k * (2 : ℝ) ^ k)) := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose (j : ℕ)
    _ ≤ ‖Lambda‖ ^ Q *
          (((Fintype.card κ * P : ℕ) : ℝ) * C *
            V ^ (q0 + ∑ i, u0 i) * ((v0 + k).factorial : ℝ) *
            (A + 1 + P) ^ P * Real.exp (U * A) *
            V ^ k * (2 : ℝ) ^ (2 * k)) := by
      have h2 : (2 : ℝ) ^ (j : ℕ) ≤ 2 ^ k :=
        pow_le_pow_right₀ (by norm_num) j.isLt.le
      calc
        (2 : ℝ) ^ (j : ℕ) *
            (‖Lambda‖ ^ Q *
              ((Fintype.card κ : ℝ) *
                (((P : ℝ) * C * V ^ (q0 + ∑ i, u0 i) *
                  ((v0 + k).factorial : ℝ) *
                  (A + 1 + P) ^ P * Real.exp (U * A))) *
                V ^ k * (2 : ℝ) ^ k)) ≤
            (2 : ℝ) ^ k *
              (‖Lambda‖ ^ Q *
                ((Fintype.card κ : ℝ) *
                  (((P : ℝ) * C * V ^ (q0 + ∑ i, u0 i) *
                    ((v0 + k).factorial : ℝ) *
                    (A + 1 + P) ^ P * Real.exp (U * A))) *
                  V ^ k * (2 : ℝ) ^ k)) := by
              exact mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = _ := by
          push_cast
          rw [two_mul, pow_add]
          ring

noncomputable def pochhammerWeightedApproximationBound
    (N P A k Q v q uTotal : ℕ)
    (C V U R Z lambdaNorm : ℝ) : ℝ :=
  let delta := lambdaNorm ^ Q *
    (((N * P : ℕ) : ℝ) * C * V ^ (q + uTotal) *
      ((v + k).factorial : ℝ) * (A + 1 + P) ^ P *
      Real.exp (U * A) * V ^ k * (2 : ℝ) ^ (2 * k))
  let boundary := ((N * P : ℕ) : ℝ) *
    (C * V ^ (q + uTotal) *
      (v.factorial : ℝ) * (R + 1 + P) ^ P * Real.exp (U * R))
  (Z + A) ^ (k * A) *
      ((boundary +
        (A * k : ℝ) *
          ((A * k : ℝ) * hermiteInterpolationBound A k * delta) *
          max 1 (R ^ (A * k))) /
        (R - A) ^ (k * A)) +
    (A * k : ℝ) *
      ((A * k : ℝ) * hermiteInterpolationBound A k * delta) *
      max 1 (Z ^ (A * k))

noncomputable def pochhammerWeightedPerturbationCoefficient
    (N P A k v q uTotal : ℕ) (C V U R Z : ℝ) : ℝ :=
  let core := (((N * P : ℕ) : ℝ) * C * V ^ (q + uTotal) *
    ((v + k).factorial : ℝ) * (A + 1 + P) ^ P *
    Real.exp (U * A) * V ^ k * (2 : ℝ) ^ (2 * k))
  (Z + A) ^ (k * A) *
      (((A * k : ℝ) *
        ((A * k : ℝ) * hermiteInterpolationBound A k * core) *
        max 1 (R ^ (A * k))) / (R - A) ^ (k * A)) +
    (A * k : ℝ) *
      ((A * k : ℝ) * hermiteInterpolationBound A k * core) *
      max 1 (Z ^ (A * k))

lemma pochhammerWeightedApproximationBound_one_eq
    (N P A k v q uTotal : ℕ) (C V U R Z lambdaNorm : ℝ) :
    pochhammerWeightedApproximationBound N P A k 1 v q uTotal
        C V U R Z lambdaNorm =
      pochhammerWeightedApproximationBound N P A k 1 v q uTotal
          C V U R Z 0 +
        lambdaNorm *
          pochhammerWeightedPerturbationCoefficient
            N P A k v q uTotal C V U R Z := by
  simp [pochhammerWeightedApproximationBound,
    pochhammerWeightedPerturbationCoefficient]
  ring

lemma pochhammerWeightedPerturbationCoefficient_nonneg
    (N P A k v q uTotal : ℕ) {C V U R Z : ℝ}
    (hC : 0 ≤ C) (hV : 0 ≤ V) (hZ : 0 ≤ Z) (hRA : 0 ≤ R - A) :
    0 ≤ pochhammerWeightedPerturbationCoefficient
      N P A k v q uTotal C V U R Z := by
  unfold pochhammerWeightedPerturbationCoefficient
  let core : ℝ := (((N * P : ℕ) : ℝ) * C * V ^ (q + uTotal) *
    ((v + k).factorial : ℝ) * (A + 1 + P) ^ P *
    Real.exp (U * A) * V ^ k * (2 : ℝ) ^ (2 * k))
  have hcore : 0 ≤ core := by dsimp [core]; positivity
  have hherm : 0 ≤ hermiteInterpolationBound A k := by
    unfold hermiteInterpolationBound
    positivity
  have hcommon : 0 ≤ (A * k : ℝ) *
      ((A * k : ℝ) * hermiteInterpolationBound A k * core) := by
    positivity
  have hden : 0 ≤ (R - A) ^ (k * A) := pow_nonneg hRA _
  apply add_nonneg
  · exact mul_nonneg (by positivity)
      (div_nonneg (mul_nonneg hcommon (zero_le_one.trans (le_max_left _ _))) hden)
  · exact mul_nonneg hcommon (zero_le_one.trans (le_max_left _ _))


lemma pochhammerWeightedPerturbationCoefficient_mono
    (N P A k v q uTotal W E : ℕ) {C V U R Z : ℝ}
    (hv : v ≤ W) (he : q + uTotal ≤ E)
    (hC : 0 ≤ C) (hV : 1 ≤ V) (hZ : 0 ≤ Z) (hRA : 0 ≤ R - A) :
    pochhammerWeightedPerturbationCoefficient
        N P A k v q uTotal C V U R Z ≤
      pochhammerWeightedPerturbationCoefficient
        N P A k W E 0 C V U R Z := by
  have hfac : (v + k).factorial ≤ (W + k).factorial :=
    Nat.factorial_le (Nat.add_le_add_right hv k)
  have hfacR : ((v + k).factorial : ℝ) ≤ ((W + k).factorial : ℝ) := by
    exact_mod_cast hfac
  have hpow : V ^ (q + uTotal) ≤ V ^ E :=
    pow_le_pow_right₀ hV he
  let core₁ : ℝ := (((N * P : ℕ) : ℝ) * C * V ^ (q + uTotal) *
    ((v + k).factorial : ℝ) * (A + 1 + P) ^ P *
    Real.exp (U * A) * V ^ k * (2 : ℝ) ^ (2 * k))
  let core₂ : ℝ := (((N * P : ℕ) : ℝ) * C * V ^ E *
    ((W + k).factorial : ℝ) * (A + 1 + P) ^ P *
    Real.exp (U * A) * V ^ k * (2 : ℝ) ^ (2 * k))
  have hcore : core₁ ≤ core₂ := by
    dsimp [core₁, core₂]
    gcongr
  have hcore0 : 0 ≤ core₁ := by dsimp [core₁]; positivity
  have hcore20 : 0 ≤ core₂ := hcore0.trans hcore
  have hherm : 0 ≤ hermiteInterpolationBound A k := by
    unfold hermiteInterpolationBound
    positivity
  have hden : 0 ≤ (R - A) ^ (k * A) := pow_nonneg hRA _
  unfold pochhammerWeightedPerturbationCoefficient
  dsimp only
  change
    (Z + A) ^ (k * A) *
        (((A * k : ℝ) *
          ((A * k : ℝ) * hermiteInterpolationBound A k * core₁) *
          max 1 (R ^ (A * k))) / (R - A) ^ (k * A)) +
      (A * k : ℝ) *
        ((A * k : ℝ) * hermiteInterpolationBound A k * core₁) *
        max 1 (Z ^ (A * k)) ≤
    (Z + A) ^ (k * A) *
        (((A * k : ℝ) *
          ((A * k : ℝ) * hermiteInterpolationBound A k * core₂) *
          max 1 (R ^ (A * k))) / (R - A) ^ (k * A)) +
      (A * k : ℝ) *
        ((A * k : ℝ) * hermiteInterpolationBound A k * core₂) *
        max 1 (Z ^ (A * k))
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply div_le_div_of_nonneg_right _ hden
    gcongr
  · gcongr


noncomputable def pochhammerWeightedPerturbationCore
    (N P A k v q uTotal : ℕ) (C V U : ℝ) : ℝ :=
  (((N * P : ℕ) : ℝ) * C * V ^ (q + uTotal) *
    ((v + k).factorial : ℝ) * (A + 1 + P) ^ P *
    Real.exp (U * A) * V ^ k * (2 : ℝ) ^ (2 * k))

noncomputable def pochhammerWeightedPerturbationCommon
    (N P A k v q uTotal : ℕ) (C V U : ℝ) : ℝ :=
  (A * k : ℝ) * ((A * k : ℝ) * hermiteInterpolationBound A k *
    pochhammerWeightedPerturbationCore N P A k v q uTotal C V U)

lemma pochhammerWeightedPerturbationCoefficient_le_simple
    (N P A k v q uTotal : ℕ) {C V U R Z : ℝ}
    (hA : 0 < A) (hC : 0 ≤ C) (hV : 0 ≤ V)
    (hZ : 0 ≤ Z) (hZR : Z ≤ R) (hden : 1 ≤ R - A) :
    pochhammerWeightedPerturbationCoefficient
        N P A k v q uTotal C V U R Z ≤
      2 * (Z + A) ^ (k * A) *
        pochhammerWeightedPerturbationCommon
          N P A k v q uTotal C V U *
        max 1 (R ^ (A * k)) := by
  let core := pochhammerWeightedPerturbationCore
    N P A k v q uTotal C V U
  let common := pochhammerWeightedPerturbationCommon
    N P A k v q uTotal C V U
  have hcore : 0 ≤ core := by
    dsimp [core, pochhammerWeightedPerturbationCore]
    positivity
  have hherm : 0 ≤ hermiteInterpolationBound A k := by
    unfold hermiteInterpolationBound
    positivity
  have hcommon : 0 ≤ common := by
    dsimp [common, pochhammerWeightedPerturbationCommon]
    positivity
  have hZA : 1 ≤ Z + (A : ℝ) := by
    have hAone : (1 : ℝ) ≤ A := by exact_mod_cast hA
    linarith
  have hpowZA : 1 ≤ (Z + A) ^ (k * A) := one_le_pow₀ hZA
  have hR0 : 0 ≤ R := hZ.trans hZR
  have hpowZR : Z ^ (A * k) ≤ R ^ (A * k) :=
    pow_le_pow_left₀ hZ hZR _
  have hmaxZR : max 1 (Z ^ (A * k)) ≤ max 1 (R ^ (A * k)) := by
    exact max_le_max le_rfl hpowZR
  have hmaxR0 : 0 ≤ max 1 (R ^ (A * k)) :=
    zero_le_one.trans (le_max_left _ _)
  have hdenpow : 1 ≤ (R - A) ^ (k * A) := one_le_pow₀ hden
  have hdiv : common * max 1 (R ^ (A * k)) / (R - A) ^ (k * A) ≤
      common * max 1 (R ^ (A * k)) := by
    exact div_le_self (mul_nonneg hcommon hmaxR0) hdenpow
  have hsecond : common * max 1 (Z ^ (A * k)) ≤
      (Z + A) ^ (k * A) * common * max 1 (R ^ (A * k)) := by
    calc
      common * max 1 (Z ^ (A * k)) ≤
          common * max 1 (R ^ (A * k)) := by gcongr
      _ ≤ (Z + A) ^ (k * A) *
          (common * max 1 (R ^ (A * k))) := by
        exact le_mul_of_one_le_left (mul_nonneg hcommon hmaxR0) hpowZA
      _ = _ := by ring
  unfold pochhammerWeightedPerturbationCoefficient
  change (Z + A) ^ (k * A) *
        (common * max 1 (R ^ (A * k)) / (R - A) ^ (k * A)) +
      common * max 1 (Z ^ (A * k)) ≤ _
  calc
    _ ≤ (Z + A) ^ (k * A) *
          (common * max 1 (R ^ (A * k))) +
        ((Z + A) ^ (k * A) * common * max 1 (R ^ (A * k))) :=
      add_le_add (mul_le_mul_of_nonneg_left hdiv (by positivity)) hsecond
    _ = _ := by ring


lemma log_pochhammerWeightedPerturbationCore
    (N P A k v q uTotal : ℕ) {C V U : ℝ}
    (hN : 0 < N) (hP : 0 < P) (hC : 0 < C) (hV : 0 < V) :
    Real.log (pochhammerWeightedPerturbationCore
        N P A k v q uTotal C V U) =
      Real.log (N * P : ℕ) + Real.log C +
        (q + uTotal : ℕ) * Real.log V +
        Real.log ((v + k).factorial : ℝ) +
        (P : ℝ) * Real.log ((A + 1 + P : ℕ) : ℝ) +
        U * A + (k : ℝ) * Real.log V +
        (2 * k : ℕ) * Real.log 2 := by
  unfold pochhammerWeightedPerturbationCore
  repeat' rw [Real.log_mul (by positivity) (by positivity)]
  repeat' rw [Real.log_pow]
  rw [Real.log_exp]
  push_cast
  ring

lemma log_hermiteInterpolationBound
    (A k : ℕ) (hA : 0 < A) (hk : 0 < k) :
    Real.log (hermiteInterpolationBound A k) =
      Real.log ((A * k).factorial : ℝ) +
        ((A * k : ℕ) : ℝ) ^ 2 * Real.log (2 * (A + 1 : ℝ)) := by
  have hfac : ((((A * k).factorial : ℕ) : ℝ)) ≠ 0 := by positivity
  have hbase : 2 * ((A : ℝ) + 1) ≠ 0 := by positivity
  unfold hermiteInterpolationBound
  rw [Real.log_mul hfac (pow_ne_zero _ (pow_ne_zero _ hbase)),
    Real.log_pow, Real.log_pow]
  push_cast
  ring

lemma log_pochhammerWeightedPerturbationCommon
    (N P A k v q uTotal : ℕ) {C V U : ℝ}
    (hN : 0 < N) (hP : 0 < P) (hA : 0 < A) (hk : 0 < k)
    (hC : 0 < C) (hV : 0 < V) :
    Real.log (pochhammerWeightedPerturbationCommon
        N P A k v q uTotal C V U) =
      2 * Real.log ((A * k : ℕ) : ℝ) +
        Real.log (hermiteInterpolationBound A k) +
        Real.log (pochhammerWeightedPerturbationCore
          N P A k v q uTotal C V U) := by
  unfold pochhammerWeightedPerturbationCommon
  push_cast
  have hA0 : (A : ℝ) ≠ 0 := by positivity
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hAk0 : (A : ℝ) * k ≠ 0 := mul_ne_zero hA0 hk0
  have hherm : hermiteInterpolationBound A k ≠ 0 := by
    unfold hermiteInterpolationBound
    positivity
  have hcore : pochhammerWeightedPerturbationCore
      N P A k v q uTotal C V U ≠ 0 := by
    unfold pochhammerWeightedPerturbationCore
    positivity
  rw [Real.log_mul hAk0 (mul_ne_zero (mul_ne_zero hAk0 hherm) hcore),
    Real.log_mul (mul_ne_zero hAk0 hherm) hcore,
    Real.log_mul hAk0 hherm, Real.log_mul hA0 hk0]
  ring

lemma hermiteInterpolationBound_log_le
    (A k : ℕ) {L : ℝ}
    (hA : 0 < A) (hk : 0 < k)
    (hfac : Real.log ((A * k).factorial : ℝ) ≤
      698 * L ^ 694 * Real.log L)
    (hsecond : ((A * k : ℕ) : ℝ) ^ 2 *
      Real.log (2 * (A + 1 : ℝ)) ≤
      1280 * L ^ 694 * Real.log L) :
    Real.log (hermiteInterpolationBound A k) ≤
      1978 * L ^ 694 * Real.log L := by
  rw [log_hermiteInterpolationBound A k hA hk]
  linarith

lemma pochhammerWeightedPerturbationCore_log_le
    (N P A k v q uTotal : ℕ) {C V U L cC cV cE s : ℝ}
    (hN : 0 < N) (hP : 0 < P) (hC : 0 < C) (hV : 0 < V)
    (hNP : Real.log (N * P : ℕ) ≤ 312 * L ^ 694 * Real.log L)
    (hClog : Real.log C ≤ cC * L ^ 694 * Real.log L)
    (hEV : (q + uTotal : ℕ) * Real.log V ≤
      cE * cV * L ^ 694 * Real.log L)
    (hfac : Real.log ((v + k).factorial : ℝ) ≤
      (315 * (315 + 34) : ℕ) * L ^ 694 * Real.log L)
    (hPterm : (P : ℝ) * Real.log ((A + 1 + P : ℕ) : ℝ) ≤
      318 * L ^ 694 * Real.log L)
    (hUA : U * A ≤ 2 * s * L ^ 694 * Real.log L)
    (hkV : (k : ℝ) * Real.log V ≤ cV * L ^ 694 * Real.log L)
    (htwo : (2 * k : ℕ) * Real.log 2 ≤ 4 * L ^ 694 * Real.log L) :
    Real.log (pochhammerWeightedPerturbationCore
        N P A k v q uTotal C V U) ≤
      (312 + cC + cE * cV + 315 * (315 + 34) +
        318 + 2 * s + cV + 4) * L ^ 694 * Real.log L := by
  rw [log_pochhammerWeightedPerturbationCore
    N P A k v q uTotal hN hP hC hV]
  calc
    _ ≤ 312 * L ^ 694 * Real.log L +
        cC * L ^ 694 * Real.log L +
        cE * cV * L ^ 694 * Real.log L +
        (315 * (315 + 34) : ℕ) * L ^ 694 * Real.log L +
        318 * L ^ 694 * Real.log L +
        2 * s * L ^ 694 * Real.log L +
        cV * L ^ 694 * Real.log L +
        4 * L ^ 694 * Real.log L := by linarith
    _ = _ := by push_cast; ring

lemma pochhammerWeightedPerturbationCommon_log_le
    (N P A k v q uTotal : ℕ) {C V U L cCore : ℝ}
    (hN : 0 < N) (hP : 0 < P) (hA : 0 < A) (hk : 0 < k)
    (hC : 0 < C) (hV : 0 < V)
    (hAk : 2 * Real.log ((A * k : ℕ) : ℝ) ≤
      698 * L ^ 694 * Real.log L)
    (hherm : Real.log (hermiteInterpolationBound A k) ≤
      1978 * L ^ 694 * Real.log L)
    (hcore : Real.log (pochhammerWeightedPerturbationCore
        N P A k v q uTotal C V U) ≤
      cCore * L ^ 694 * Real.log L) :
    Real.log (pochhammerWeightedPerturbationCommon
        N P A k v q uTotal C V U) ≤
      (2676 + cCore) * L ^ 694 * Real.log L := by
  rw [log_pochhammerWeightedPerturbationCommon
    N P A k v q uTotal hN hP hA hk hC hV]
  calc
    _ ≤ 698 * L ^ 694 * Real.log L +
        1978 * L ^ 694 * Real.log L +
        cCore * L ^ 694 * Real.log L := by linarith
    _ = _ := by ring

lemma pochhammerWeightedPerturbationCoefficient_log_le
    (N P A k v q uTotal L : ℕ) {C V U R Z LR cCore : ℝ}
    (hA : 0 < A) (hC : 0 < C) (hV : 0 < V)
    (hZ : 0 ≤ Z) (hZR : Z ≤ R) (hden : 1 ≤ R - A) (hR : 1 ≤ R)
    (hcoeff : 0 < pochhammerWeightedPerturbationCoefficient
      N P A k v q uTotal C V U R Z)
    (hcommonPos : 0 < pochhammerWeightedPerturbationCommon
      N P A k v q uTotal C V U)
    (hZAeq : Z + A = ((2 * A + A : ℕ) : ℝ))
    (hReq : R = ((L * (2 * A) : ℕ) : ℝ))
    (hlogTwo : Real.log 2 ≤ 2 * LR ^ 694 * Real.log LR)
    (hZAterm : ((A * k : ℕ) : ℝ) *
      Real.log ((2 * A + A : ℕ) : ℝ) ≤
      640 * LR ^ 694 * Real.log LR)
    (hcommon : Real.log (pochhammerWeightedPerturbationCommon
        N P A k v q uTotal C V U) ≤
      (2676 + cCore) * LR ^ 694 * Real.log LR)
    (hRterm : ((A * k : ℕ) : ℝ) *
      Real.log ((L * (2 * A) : ℕ) : ℝ) ≤
      638 * LR ^ 694 * Real.log LR) :
    Real.log (pochhammerWeightedPerturbationCoefficient
        N P A k v q uTotal C V U R Z) ≤
      (3956 + cCore) * LR ^ 694 * Real.log LR := by
  have hsimple := pochhammerWeightedPerturbationCoefficient_le_simple
    N P A k v q uTotal (C := C) (V := V) (U := U) (R := R) (Z := Z)
      hA hC.le hV.le hZ hZR hden
  have hmax : max 1 (R ^ (A * k)) = R ^ (A * k) :=
    max_eq_right (one_le_pow₀ hR)
  have hlogSimple := Real.log_le_log hcoeff hsimple
  have hlogRhs : Real.log (2 * (Z + A) ^ (k * A) *
      pochhammerWeightedPerturbationCommon N P A k v q uTotal C V U *
      max 1 (R ^ (A * k))) =
      Real.log 2 + ((A * k : ℕ) : ℝ) * Real.log ((2 * A + A : ℕ) : ℝ) +
        Real.log (pochhammerWeightedPerturbationCommon
          N P A k v q uTotal C V U) +
        ((A * k : ℕ) : ℝ) *
          Real.log ((L * (2 * A) : ℕ) : ℝ) := by
    have hZApos : (0 : ℝ) < ((2 * A + A : ℕ) : ℝ) := by positivity
    have hRnatPos : (0 : ℝ) < ((L * (2 * A) : ℕ) : ℝ) := by
      rw [← hReq]
      exact zero_lt_one.trans_le hR
    rw [hmax, hZAeq, hReq]
    repeat' rw [Real.log_mul (by positivity) (by positivity)]
    repeat' rw [Real.log_pow]
    push_cast
    ring
  rw [hlogRhs] at hlogSimple
  calc
    _ ≤ 2 * LR ^ 694 * Real.log LR +
        640 * LR ^ 694 * Real.log LR +
        (2676 + cCore) * LR ^ 694 * Real.log LR +
        638 * LR ^ 694 * Real.log LR := by linarith
    _ = _ := by ring

theorem pochhammerWeightedAuxiliary_norm_le_of_moments
    {F κ iota : Type*} [Field F] [NumberField F]
    [Fintype κ] [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) (beta : κ → F) (L : κ → ℂ)
    (b0 Lambda : ℂ) (a : κ → ℤ) (r : κ → iota → ℤ)
    (ell : iota → ℂ) (P : ℕ) (c : κ → Fin P → ℤ)
    (A W T S k Q v0 q0 : ℕ) (u0 : iota → ℕ)
    {C V U R Z : ℝ} {z : ℂ}
    (hA : 0 < A) (hk : 0 < k)
    (hC : 0 ≤ C) (hV : 1 ≤ V) (hU : 0 ≤ U)
    (hb0 : 1 ≤ ‖b0‖) (hLambda : ‖Lambda‖ ≤ 1)
    (hc : ∀ x m, ‖(c x m : ℂ)‖ ≤ C)
    (ha : ∀ x, ‖(a x : ℂ)‖ ≤ V)
    (hrV : ∀ x i, ‖(r x i : ℂ)‖ ≤ V)
    (hr : ∀ x, ‖∑ i, (r x i : ℂ) * ell i‖ ≤ V)
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (beta x))
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin A, ∀ v : Fin W, ∀ q : Fin T,
      ∀ u : iota → Fin S,
        pochhammerMultipointMomentValue beta a r P c node v q
          (fun i ↦ u i) = 0)
    (hvW : v0 + k ≤ W) (hqT : q0 + Q ≤ T)
    (huS : ∀ i, u0 i + k ≤ S)
    (hAR : (A : ℝ) < R) (hz : ‖z‖ ≤ Z) (hZR : Z ≤ R) :
    ‖pochhammerWeightedAuxiliary L P (fun x m ↦ (c x m : ℂ))
        (fun x ↦ (a x : ℂ)) (fun x i ↦ (r x i : ℂ))
        v0 q0 u0 z‖ ≤
      pochhammerWeightedApproximationBound
        (Fintype.card κ) P A k Q v0 q0 (∑ i, u0 i)
          C V U R Z ‖Lambda‖ := by
  unfold pochhammerWeightedApproximationBound
  dsimp only
  apply analytic_norm_le_of_approximate_nat_node_jets
    (pochhammerWeightedAuxiliary L P (fun x m ↦ (c x m : ℂ))
      (fun x ↦ (a x : ℂ)) (fun x i ↦ (r x i : ℂ)) v0 q0 u0)
    A k hA hk
    (δ := ‖Lambda‖ ^ Q *
      ((((Fintype.card κ) * P : ℕ) : ℝ) * C *
        V ^ (q0 + ∑ i, u0 i) * ((v0 + k).factorial : ℝ) *
        (A + 1 + P) ^ P * Real.exp (U * A) *
        V ^ k * (2 : ℝ) ^ (2 * k)))
    (M := ((((Fintype.card κ) * P : ℕ) : ℝ) *
      (C * V ^ (q0 + ∑ i, u0 i) *
        (v0.factorial : ℝ) * (R + 1 + P) ^ P * Real.exp (U * R))))
  · positivity
  · exact hAR
  · exact hz
  · exact hZR
  · intro w
    unfold pochhammerWeightedAuxiliary
    have houter : (fun z : ℂ ↦ ∑ x, ∑ m,
        ((c x m : ℂ) * (a x : ℂ) ^ q0 *
            ∏ i, (r x i : ℂ) ^ u0 i) *
          ((Polynomial.derivative^[v0])
            (descPochhammer ℂ (m : ℕ))).eval z *
          Complex.exp (L x * z)) =
        ∑ x, (fun z : ℂ ↦ ∑ m,
          ((c x m : ℂ) * (a x : ℂ) ^ q0 *
              ∏ i, (r x i : ℂ) ^ u0 i) *
            ((Polynomial.derivative^[v0])
              (descPochhammer ℂ (m : ℕ))).eval z *
            Complex.exp (L x * z)) := by
      funext z
      simp
    rw [houter]
    apply Finset.analyticAt_sum Finset.univ
    intro x hx
    have hinner : (fun z : ℂ ↦ ∑ m,
        ((c x m : ℂ) * (a x : ℂ) ^ q0 *
            ∏ i, (r x i : ℂ) ^ u0 i) *
          ((Polynomial.derivative^[v0])
            (descPochhammer ℂ (m : ℕ))).eval z *
          Complex.exp (L x * z)) =
        ∑ m, (fun z : ℂ ↦
          ((c x m : ℂ) * (a x : ℂ) ^ q0 *
              ∏ i, (r x i : ℂ) ^ u0 i) *
            ((Polynomial.derivative^[v0])
              (descPochhammer ℂ (m : ℕ))).eval z *
            Complex.exp (L x * z)) := by
      funext z
      simp
    rw [hinner]
    apply Finset.analyticAt_sum Finset.univ
    intro m hm
    have hp : AnalyticAt ℂ
        (fun z : ℂ ↦ ((Polynomial.derivative^[v0])
          (descPochhammer ℂ (m : ℕ))).eval z) w :=
      (AnalyticOnNhd.eval_polynomial
        ((Polynomial.derivative^[v0])
          (descPochhammer ℂ (m : ℕ)))) w (Set.mem_univ w)
    exact ((analyticAt_const.mul hp).mul (by fun_prop))
  · exact pochhammerWeightedAuxiliary_normalized_jet_norm_le_of_moments
      φ beta L b0 Lambda a r ell P c A W T S k Q v0 q0 u0
      hC hV hU hb0 hLambda hc ha hrV hr hL hexp hcoord hmoment
      hvW hqT huS
  · intro w hw
    have hwNorm : ‖w‖ = R := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hw
    have hb := pochhammerWeightedAuxiliary_norm_le
      L P (fun x m ↦ (c x m : ℂ))
      (fun x ↦ (a x : ℂ)) (fun x i ↦ (r x i : ℂ))
      v0 q0 u0 (C := C) (V := V) (U := U) (R := R) (z := w)
      hC hV hU (by exact le_of_lt ((Nat.cast_pos.mpr hA).trans hAR))
      hc ha hrV hL (by rw [hwNorm])
    simpa [mul_assoc] using hb


theorem boxPochhammerMomentValue_eq_zero_of_approximate_extrapolation
    {F iota : Type*} [Field F] [NumberField F]
    [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) {n K P : ℕ} (alpha : Fin n → F)
    (c : ExponentBox n K → Fin P → ℤ)
    (L : ExponentBox n K → ℂ) (b0 Lambda : ℂ)
    (a : ExponentBox n K → ℤ)
    (r : ExponentBox n K → iota → ℤ) (ell : iota → ℂ)
    {A W T S k Q h v0 q0 : ℕ} (u0 : iota → ℕ)
    {C V : ℕ} {U R Z : ℝ}
    (hK : 0 < K) (hP : 0 < P) (hA : 0 < A) (hk : 0 < k)
    (hb0 : 1 ≤ ‖b0‖) (hLambda : ‖Lambda‖ ≤ 1)
    (hC : 1 ≤ C) (hV : 1 ≤ V) (hU : 0 ≤ U)
    (hc : ∀ x m, (c x m).natAbs ≤ C)
    (haV : ∀ x, ‖a x‖ ≤ (V : ℝ))
    (hrV : ∀ x i, ‖r x i‖ ≤ (V : ℝ))
    (hrLinear : ∀ x, ‖∑ i, (r x i : ℂ) * ell i‖ ≤ (V : ℝ))
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (boxMonomial alpha x))
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin A, ∀ v : Fin W, ∀ q : Fin T,
      ∀ u : iota → Fin S,
        pochhammerMultipointMomentValue (boxMonomial alpha) a r P c
          node v q (fun i ↦ u i) = 0)
    (hvW : v0 + k ≤ W) (hqT : q0 + Q ≤ T)
    (huS : ∀ i, u0 i + k ≤ S)
    (hAR : (A : ℝ) < R) (hhZ : (h : ℝ) ≤ Z) (hZR : Z ≤ R)
    (hsmall :
      pochhammerWeightedApproximationBound (K ^ n) P A k Q v0 q0
          (∑ i, u0 i) (C : ℝ) (V : ℝ) U R Z ‖Lambda‖ <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ n + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (P * C *
                (v0.factorial * (h + 1 + P) ^ P) *
                V ^ (q0 + ∑ i, u0 i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i))))) :
    pochhammerMultipointMomentValue (boxMonomial alpha) a r P c
      h v0 q0 u0 = 0 := by
  have hcComplex : ∀ x m, ‖(c x m : ℂ)‖ ≤ (C : ℝ) := by
    intro x m
    rw [Complex.norm_intCast, ← Int.cast_abs, ← Nat.cast_natAbs]
    exact_mod_cast hc x m
  have haComplex : ∀ x, ‖(a x : ℂ)‖ ≤ (V : ℝ) := by
    intro x
    simpa [Int.norm_eq_abs] using haV x
  have hrComplex : ∀ x i, ‖(r x i : ℂ)‖ ≤ (V : ℝ) := by
    intro x i
    simpa [Int.norm_eq_abs] using hrV x i
  have hanalytic := pochhammerWeightedAuxiliary_norm_le_of_moments
    φ (boxMonomial alpha) L b0 Lambda a r ell P c
      A W T S k Q v0 q0 u0
      (C := (C : ℝ)) (V := (V : ℝ)) (U := U)
      (R := R) (Z := Z) (z := (h : ℂ))
      hA hk (by positivity)
      (by exact_mod_cast hV) hU hb0 hLambda hcComplex haComplex
      hrComplex hrLinear hL hexp hcoord hmoment hvW hqT huS hAR
      (by simpa using hhZ) hZR
  have hanalytic' :
      ‖pochhammerWeightedAuxiliary L P (fun x m ↦ (c x m : ℂ))
          (fun x ↦ (a x : ℂ)) (fun x i ↦ (r x i : ℂ))
          v0 q0 u0 (h : ℂ)‖ ≤
        pochhammerWeightedApproximationBound (K ^ n) P A k Q v0 q0
          (∑ i, u0 i) (C : ℝ) (V : ℝ) U R Z ‖Lambda‖ := by
    simpa [ExponentBox] using hanalytic
  have heval := pochhammerWeightedAuxiliary_nat_numberField
    φ (boxMonomial alpha) L a r P c h v0 q0 u0 hexp
  let dZ : ExponentBox n K → ℤ := fun x ↦
    ∑ m, c x m * pochhammerJet (m : ℕ) v0 h * a x ^ q0 *
      ∏ i, r x i ^ u0 i
  have haNat : ∀ x, (a x).natAbs ≤ V := by
    intro x
    have hx := haComplex x
    rw [Complex.norm_intCast, ← Int.cast_abs, ← Nat.cast_natAbs] at hx
    exact_mod_cast hx
  have hrNat : ∀ x i, (r x i).natAbs ≤ V := by
    intro x i
    have hx := hrComplex x i
    rw [Complex.norm_intCast, ← Int.cast_abs, ← Nat.cast_natAbs] at hx
    exact_mod_cast hx
  have hd : ∀ x, (dZ x).natAbs ≤
      P * C * (v0.factorial * (h + 1 + P) ^ P) *
        V ^ (q0 + ∑ i, u0 i) := by
    intro x
    exact pochhammerAggregatedCoefficient_natAbs_le
      a r P c x h v0 q0 u0 C V hc haNat hrNat
  have hvalue :
      pochhammerMultipointMomentValue (boxMonomial alpha) a r P c
          h v0 q0 u0 = boxAuxiliaryAlgebraicValue alpha dZ h := by
    unfold pochhammerMultipointMomentValue boxAuxiliaryAlgebraicValue
    apply Finset.sum_congr rfl
    intro x hx
    dsimp [dZ]
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  by_contra hne
  have hneBox : boxAuxiliaryAlgebraicValue alpha dZ h ≠ 0 := by
    rwa [← hvalue]
  have hDbound : 1 ≤ P * C *
      (v0.factorial * (h + 1 + P) ^ P) *
        V ^ (q0 + ∑ i, u0 i) := by
    have hpos : 0 < P * C *
        (v0.factorial * (h + 1 + P) ^ P) *
          V ^ (q0 + ∑ i, u0 i) := by positivity
    omega
  have hlocal := boxAuxiliaryAlgebraicValue_projective_log_norm_lower
    φ alpha dZ hK hDbound hd hneBox
  have hlower :
      Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ n + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (P * C *
                (v0.factorial * (h + 1 + P) ^ P) *
                V ^ (q0 + ∑ i, u0 i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i)))) ≤
        ‖φ (boxAuxiliaryAlgebraicValue alpha dZ h)‖ := by
    have hnormPos : 0 < ‖φ (boxAuxiliaryAlgebraicValue alpha dZ h)‖ :=
      norm_pos_iff.mpr ((map_ne_zero φ).2 hneBox)
    calc
      _ ≤ Real.exp (Real.log
          ‖φ (boxAuxiliaryAlgebraicValue alpha dZ h)‖) :=
        Real.exp_le_exp.mpr hlocal
      _ = _ := Real.exp_log hnormPos
  rw [← hvalue, ← heval] at hlower
  linarith [hanalytic']


theorem boxPochhammerMoments_extend_of_approximate_extrapolation
    {F iota : Type*} [Field F] [NumberField F]
    [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) {n K P : ℕ} (alpha : Fin n → F)
    (c : ExponentBox n K → Fin P → ℤ)
    (L : ExponentBox n K → ℂ) (b0 Lambda : ℂ)
    (a : ExponentBox n K → ℤ)
    (r : ExponentBox n K → iota → ℤ) (ell : iota → ℂ)
    {A W T S k Q A' W' T' S' : ℕ} {C V : ℕ} {U R Z : ℝ}
    (hK : 0 < K) (hP : 0 < P) (hA : 0 < A) (hk : 0 < k)
    (hb0 : 1 ≤ ‖b0‖) (hLambda : ‖Lambda‖ ≤ 1)
    (hC : 1 ≤ C) (hV : 1 ≤ V) (hU : 0 ≤ U)
    (hc : ∀ x m, (c x m).natAbs ≤ C)
    (haV : ∀ x, ‖a x‖ ≤ (V : ℝ))
    (hrV : ∀ x i, ‖r x i‖ ≤ (V : ℝ))
    (hrLinear : ∀ x, ‖∑ i, (r x i : ℂ) * ell i‖ ≤ (V : ℝ))
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (boxMonomial alpha x))
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin A, ∀ v : Fin W, ∀ q : Fin T,
      ∀ u : iota → Fin S,
        pochhammerMultipointMomentValue (boxMonomial alpha) a r P c
          node v q (fun i ↦ u i) = 0)
    (hW : W' + k ≤ W) (hT : T' + Q ≤ T) (hS : S' + k ≤ S)
    (hAR : (A : ℝ) < R) (hA'Z : (A' : ℝ) ≤ Z) (hZR : Z ≤ R)
    (hsmall : ∀ h < A', ∀ v < W', ∀ q < T',
      ∀ u : iota → ℕ, (∀ i, u i < S') →
      pochhammerWeightedApproximationBound (K ^ n) P A k Q v q
          (∑ i, u i) (C : ℝ) (V : ℝ) U R Z ‖Lambda‖ <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ n + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (P * C *
                (v.factorial * (h + 1 + P) ^ P) *
                V ^ (q + ∑ i, u i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i))))) :
    ∀ node : Fin A', ∀ v : Fin W', ∀ q : Fin T',
      ∀ u : iota → Fin S',
        pochhammerMultipointMomentValue (boxMonomial alpha) a r P c
          node v q (fun i ↦ u i) = 0 := by
  intro node v q u
  apply boxPochhammerMomentValue_eq_zero_of_approximate_extrapolation
    (A := A) (W := W) (T := T) (S := S) (k := k) (Q := Q)
    (h := (node : ℕ)) (v0 := (v : ℕ)) (q0 := (q : ℕ))
    (C := C) (V := V) (U := U) (R := R) (Z := Z)
    φ alpha c L b0 Lambda a r ell (fun i ↦ (u i : ℕ))
    hK hP hA hk hb0 hLambda hC hV hU hc haV hrV hrLinear
    hL hexp hcoord hmoment
  · omega
  · omega
  · intro i
    have hui : (u i : ℕ) < S' := (u i).isLt
    omega
  · exact hAR
  · exact (Nat.cast_le.mpr node.isLt.le).trans hA'Z
  · exact hZR
  · exact hsmall node node.isLt v v.isLt q q.isLt
      (fun i ↦ (u i : ℕ)) (fun i ↦ (u i).isLt)


theorem no_small_box_linear_form_of_pochhammer_approximate_then_iterated_moments
    {F iota : Type*} [Field F] [NumberField F]
    [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) {n K P : ℕ} (alpha : Fin n → F)
    (c : ExponentBox n K → Fin P → ℤ)
    (L : ExponentBox n K → ℂ) (b0 Lambda : ℂ)
    (a : ExponentBox n K → ℤ)
    (r : ExponentBox n K → iota → ℤ) (ell : iota → ℂ)
    {Ainit Wsrc Tsrc Ssrc kapprox Qaux : ℕ}
    (A W T S k : ℕ → ℕ) (R Z : ℕ → ℝ) (m : ℕ)
    {C V : ℕ} {U Rapprox Zapprox : ℝ}
    (hK : 0 < K) (hP : 0 < P) (hAinit : 0 < Ainit)
    (hkapprox : 0 < kapprox)
    (happroxW : W 0 + kapprox ≤ Wsrc)
    (happroxT : T 0 + Qaux ≤ Tsrc)
    (happroxS : S 0 + kapprox ≤ Ssrc)
    (hb0one : 1 ≤ ‖b0‖) (hLambda : ‖Lambda‖ ≤ 1)
    (hC : 1 ≤ C) (hV : 1 ≤ V) (hU : 0 ≤ U)
    (hc0 : c ≠ 0)
    (hinj : Function.Injective
      (fun x : ExponentBox n K ↦ boxMonomial alpha x))
    (hbeta0 : ∀ x : ExponentBox n K, boxMonomial alpha x ≠ 0)
    (hc : ∀ x p, (c x p).natAbs ≤ C)
    (haV : ∀ x, ‖a x‖ ≤ (V : ℝ))
    (hrV : ∀ x i, ‖r x i‖ ≤ (V : ℝ))
    (hrLinear : ∀ x, ‖∑ i, (r x i : ℂ) * ell i‖ ≤ (V : ℝ))
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (boxMonomial alpha x))
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin Ainit, ∀ v : Fin Wsrc,
      ∀ q : Fin Tsrc, ∀ u : iota → Fin Ssrc,
        pochhammerMultipointMomentValue (boxMonomial alpha) a r P c
          node v q (fun i ↦ u i) = 0)
    (happroxAR : (Ainit : ℝ) < Rapprox)
    (happroxA'Z : (A 0 : ℝ) ≤ Zapprox)
    (happroxZR : Zapprox ≤ Rapprox)
    (happroxSmall : ∀ h < A 0, ∀ v < W 0, ∀ q < T 0,
      ∀ u : iota → ℕ, (∀ i, u i < S 0) →
      pochhammerWeightedApproximationBound (K ^ n) P Ainit kapprox
          Qaux v q (∑ i, u i) (C : ℝ) (V : ℝ)
          U Rapprox Zapprox ‖Lambda‖ <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ n + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (P * C *
                (v.factorial * (h + 1 + P) ^ P) *
                V ^ (q + ∑ i, u i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i)))))
    (hstepW : ∀ j, W (j + 1) + k j ≤ W j)
    (hstepT : ∀ j, T (j + 1) + k j ≤ T j)
    (hstepS : ∀ j, S (j + 1) + k j ≤ S j)
    (hstepAR : ∀ j, (A j : ℝ) < R j)
    (hstepA'Z : ∀ j, (A (j + 1) : ℝ) ≤ Z j)
    (hstepZR : ∀ j, Z j ≤ R j)
    (hstepSmall : ∀ j, ∀ h < A (j + 1), ∀ v < W (j + 1),
      ∀ q < T (j + 1), ∀ u : iota → ℕ,
      (∀ i, u i < S (j + 1)) →
      (Z j + A j) ^ (k j * A j) *
          (((((K ^ n * P : ℕ) : ℝ) *
              ((C : ℝ) * (V : ℝ) ^ (q + ∑ i, u i) *
                ((v.factorial : ℝ) * (R j + 1 + P) ^ P) *
                Real.exp (U * R j)))) /
            (R j - A j) ^ (k j * A j)) <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ n + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (P * C *
                (v.factorial * (h + 1 + P) ^ P) *
                V ^ (q + ∑ i, u i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i)))))
    (hfinalA : K ^ n * P ≤ A m)
    (hfinalW : 0 < W m) (hfinalT : 0 < T m) (hfinalS : 0 < S m) :
    False := by
  have hmoment0 :=
    boxPochhammerMoments_extend_of_approximate_extrapolation
      (A := Ainit) (W := Wsrc) (T := Tsrc) (S := Ssrc)
      (k := kapprox) (Q := Qaux)
      (A' := A 0) (W' := W 0) (T' := T 0) (S' := S 0)
      (C := C) (V := V) (U := U)
      (R := Rapprox) (Z := Zapprox)
      φ alpha c L b0 Lambda a r ell hK hP hAinit hkapprox
      hb0one hLambda hC hV hU hc haV hrV hrLinear hL hexp
      hcoord hmoment happroxW happroxT happroxS happroxAR
      happroxA'Z happroxZR happroxSmall
  have hb0 : b0 ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hb0one)
  have hfinal := boxPochhammerMoments_iterate_extrapolation
    φ alpha c L b0 Lambda a r ell A W T S k R Z m
    hK hP hb0 hC hV hU hc haV hrV hL hexp hcoord hmoment0
    hstepW hstepT hstepS hstepAR hstepA'Z hstepZR hstepSmall
  obtain ⟨t, ht⟩ := exists_pochhammerMultipointMomentValue_ne_zero
    (boxMonomial alpha) hinj hbeta0 a r P c hc0
  have htN : (t : ℕ) < K ^ n * P := by
    simpa [ExponentBox] using t.isLt
  let node : Fin (A m) := ⟨t, htN.trans_le hfinalA⟩
  let v : Fin (W m) := ⟨0, hfinalW⟩
  let q : Fin (T m) := ⟨0, hfinalT⟩
  let u : iota → Fin (S m) := fun _ ↦ ⟨0, hfinalS⟩
  have hz := hfinal node v q u
  exact ht (by simpa [node, v, q, u] using hz)


theorem exists_box_initial_pochhammer_moment_coefficients
    {F : Type*} [Field F] [NumberField F]
    {r K B P J T S : ℕ} (alpha : Fin (r + 1) → F)
    (b : Fin (r + 1) → ℤ) (_hb : ∀ i, (b i).natAbs ≤ B)
    (hP : 0 < P) (hJ : 0 < J) (hT : 0 < T) (hS : 0 < S)
    (hcard : J * T * S ^ r < K ^ (r + 1) * P) :
    ∃ c : ExponentBox (r + 1) K → Fin P → ℤ, c ≠ 0 ∧
      (∀ node : Fin 1, ∀ v : Fin J, ∀ q : Fin T,
        ∀ u : Fin r → Fin S,
          pochhammerMultipointMomentValue (boxMonomial alpha)
            boxDistinguishedExponent (boxTransformedExponent b) P c
            node v q (fun i ↦ u i) = 0) ∧
      ∀ x m, (c x m).natAbs ≤ Nat.ceil
        ((((K ^ (r + 1) * P : ℕ) : ℝ) *
            max 1 ‖pochhammerInitialMomentMatrix
              (fun x : ExponentBox (r + 1) K ↦
                boxDistinguishedExponent x)
              (fun x i ↦ boxTransformedExponent b x i) P J T S‖) ^
          ((((J * T * S ^ r : ℕ) : ℝ)) /
            (((K ^ (r + 1) * P : ℕ) : ℝ) -
              ((J * T * S ^ r : ℕ) : ℝ)))) := by
  obtain ⟨c, hc0, hm, hc⟩ := exists_pochhammer_initial_moment_coefficients
    (fun x : ExponentBox (r + 1) K ↦ boxDistinguishedExponent x)
    (fun x i ↦ boxTransformedExponent b x i) P J T S
    hP hJ hT hS (by simpa [ExponentBox] using hcard)
  refine ⟨c, hc0, ?_, ?_⟩
  · intro node v q u
    have hz := hm v q u
    simpa [pochhammerMultipointMomentValue] using
      (show (∑ x, ∑ m,
        (c x m : F) * (pochhammerJet (m : ℕ) (v : ℕ) 0 : F) *
          (boxDistinguishedExponent x : F) ^ (q : ℕ) *
          ∏ i, (boxTransformedExponent b x i : F) ^ (u i : ℕ)) = 0 by
        exact_mod_cast hz)
  · intro x m
    simpa [ExponentBox] using hc x m


noncomputable def boxPochhammerInitialCoefficientBound
    (r K B P J T S : ℕ) : ℕ :=
  Nat.ceil
    ((((K ^ (r + 1) * P : ℕ) : ℝ) *
        max 1 ((J.factorial : ℝ) * (1 + P) ^ P *
          (boxMomentCoordinateBound B K : ℝ) ^ (T + r * S))) ^
      ((((J * T * S ^ r : ℕ) : ℝ)) /
        (((K ^ (r + 1) * P : ℕ) : ℝ) -
          ((J * T * S ^ r : ℕ) : ℝ))))

theorem exists_box_initial_pochhammer_moment_coefficients_explicit
    {F : Type*} [Field F] [NumberField F]
    {r K B P J T S : ℕ} (alpha : Fin (r + 1) → F)
    (b : Fin (r + 1) → ℤ) (hb : ∀ i, (b i).natAbs ≤ B)
    (hK : 0 < K) (hP : 0 < P) (hJ : 0 < J)
    (hT : 0 < T) (hS : 0 < S)
    (hcard : J * T * S ^ r < K ^ (r + 1) * P) :
    ∃ c : ExponentBox (r + 1) K → Fin P → ℤ, c ≠ 0 ∧
      (∀ node : Fin 1, ∀ v : Fin J, ∀ q : Fin T,
        ∀ u : Fin r → Fin S,
          pochhammerMultipointMomentValue (boxMonomial alpha)
            boxDistinguishedExponent (boxTransformedExponent b) P c
            node v q (fun i ↦ u i) = 0) ∧
      ∀ x m, (c x m).natAbs ≤
        boxPochhammerInitialCoefficientBound r K B P J T S := by
  obtain ⟨c, hc0, hm, hc⟩ :=
    exists_box_initial_pochhammer_moment_coefficients
      alpha b hb hP hJ hT hS hcard
  refine ⟨c, hc0, hm, fun x m ↦ (hc x m).trans ?_⟩
  apply Nat.ceil_mono
  apply Real.rpow_le_rpow
  · positivity
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply max_le_max_left
    have hmBound := pochhammerInitialMomentMatrix_norm_le
      (fun x : ExponentBox (r + 1) K ↦ boxDistinguishedExponent x)
      (fun x i ↦ boxTransformedExponent b x i) P J T S
      (V := (boxMomentCoordinateBound B K : ℝ))
      (by exact_mod_cast one_le_boxMomentCoordinateBound hK)
      (fun x ↦ (boxDistinguishedExponent_norm_le x).trans (by
        exact_mod_cast le_max_left K (2 * B * K)))
      (fun x i ↦ (boxTransformedExponent_norm_le b hb x i).trans (by
        exact_mod_cast le_max_right K (2 * B * K)))
    simpa using hmBound
  · have hden : (0 : ℝ) <
        ((K ^ (r + 1) * P : ℕ) : ℝ) -
          ((J * T * S ^ r : ℕ) : ℝ) := by
      exact sub_pos.mpr (by exact_mod_cast hcard)
    positivity


noncomputable def boxAnalyticCoordinateBound
    {r : ℕ} (B K : ℕ) (ell : Fin (r + 1) → ℂ) : ℕ :=
  Nat.ceil (max 1 (max (boxMomentCoordinateBound B K : ℝ)
    (((2 * B * K : ℕ) : ℝ) * ∑ i : Fin r, ‖ell i.succ‖)))

lemma one_le_boxAnalyticCoordinateBound
    {r B K : ℕ} (ell : Fin (r + 1) → ℂ) :
    1 ≤ boxAnalyticCoordinateBound B K ell := by
  have hreal : (1 : ℝ) ≤
      (boxAnalyticCoordinateBound B K ell : ℝ) := by
    calc
      (1 : ℝ) ≤ max 1 (max (boxMomentCoordinateBound B K : ℝ)
        (((2 * B * K : ℕ) : ℝ) * ∑ i : Fin r, ‖ell i.succ‖)) :=
        le_max_left _ _
      _ ≤ (boxAnalyticCoordinateBound B K ell : ℕ) :=
        Nat.le_ceil _
  exact_mod_cast hreal

lemma boxMomentCoordinateBound_le_boxAnalyticCoordinateBound
    {r B K : ℕ} (ell : Fin (r + 1) → ℂ) :
    boxMomentCoordinateBound B K ≤
      boxAnalyticCoordinateBound B K ell := by
  have hreal : (boxMomentCoordinateBound B K : ℝ) ≤
      (boxAnalyticCoordinateBound B K ell : ℝ) := by
    calc
      (boxMomentCoordinateBound B K : ℝ) ≤
        max 1 (max (boxMomentCoordinateBound B K : ℝ)
          (((2 * B * K : ℕ) : ℝ) * ∑ i : Fin r, ‖ell i.succ‖)) :=
        le_max_of_le_right (le_max_left _ _)
      _ ≤ (boxAnalyticCoordinateBound B K ell : ℕ) :=
        Nat.le_ceil _
  exact_mod_cast hreal

lemma boxTransformedLinearForm_norm_le_analyticBound
    {r K B : ℕ} (ell : Fin (r + 1) → ℂ)
    (b : Fin (r + 1) → ℤ) (hb : ∀ i, (b i).natAbs ≤ B)
    (x : ExponentBox (r + 1) K) :
    ‖∑ i : Fin r, (boxTransformedExponent b x i : ℂ) * ell i.succ‖ ≤
      (boxAnalyticCoordinateBound B K ell : ℝ) := by
  refine (boxTransformedLinearForm_norm_le
    (fun i : Fin r ↦ ell i.succ) b hb x).trans ?_
  calc
    (((2 * B * K : ℕ) : ℝ) * ∑ i : Fin r, ‖ell i.succ‖) ≤
        max 1 (max (boxMomentCoordinateBound B K : ℝ)
          (((2 * B * K : ℕ) : ℝ) * ∑ i : Fin r, ‖ell i.succ‖)) :=
      le_max_of_le_right (le_max_right _ _)
    _ ≤ (boxAnalyticCoordinateBound B K ell : ℕ) :=
      Nat.le_ceil _


noncomputable def boxPochhammerCoefficientMajorant
    (r K B P J T S : ℕ) : ℕ :=
  max 1 (boxPochhammerInitialCoefficientBound r K B P J T S)

lemma one_le_boxPochhammerCoefficientMajorant
    (r K B P J T S : ℕ) :
    1 ≤ boxPochhammerCoefficientMajorant r K B P J T S :=
  le_max_left _ _

theorem no_small_distinguished_linear_form_of_pochhammer_schedule
    {F : Type*} [Field F] [NumberField F]
    (φ : F →+* ℂ) {r B K P Wsrc Tsrc Ssrc kapprox Qaux : ℕ}
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ)
    (b : Fin (r + 1) → ℤ)
    (A W T S k : ℕ → ℕ) (R Z : ℕ → ℝ) (m : ℕ)
    {Rapprox Zapprox : ℝ}
    (hK : 0 < K) (hP : 0 < P)
    (hWsrc : 0 < Wsrc) (hTsrc : 0 < Tsrc) (hSsrc : 0 < Ssrc)
    (hcard : Wsrc * Tsrc * Ssrc ^ r < K ^ (r + 1) * P)
    (hb : ∀ i, (b i).natAbs ≤ B) (hb0 : b 0 ≠ 0)
    (halpha : ∀ i, alpha i ≠ 0)
    (hinj : Function.Injective
      (fun x : ExponentBox (r + 1) K ↦ boxMonomial alpha x))
    (hexp : ∀ x : ExponentBox (r + 1) K,
      Complex.exp (boxLinearForm ell x) =
      φ (boxMonomial alpha x))
    (hLambda : ‖∑ i, (b i : ℂ) * ell i‖ ≤ 1)
    (hkapprox : 0 < kapprox)
    (happroxW : W 0 + kapprox ≤ Wsrc)
    (happroxT : T 0 + Qaux ≤ Tsrc)
    (happroxS : S 0 + kapprox ≤ Ssrc)
    (happroxAR : (1 : ℝ) < Rapprox)
    (happroxA'Z : (A 0 : ℝ) ≤ Zapprox)
    (happroxZR : Zapprox ≤ Rapprox)
    (happroxSmall : ∀ h < A 0, ∀ v < W 0, ∀ q < T 0,
      ∀ u : Fin r → ℕ, (∀ i, u i < S 0) →
      pochhammerWeightedApproximationBound (K ^ (r + 1)) P 1 kapprox
          Qaux v q (∑ i, u i)
          (boxPochhammerCoefficientMajorant
            r K B P Wsrc Tsrc Ssrc : ℝ)
          (boxAnalyticCoordinateBound B K ell : ℝ)
          ((K : ℝ) * ∑ i, ‖ell i‖) Rapprox Zapprox
          ‖∑ i, (b i : ℂ) * ell i‖ <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ (r + 1) + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (P * boxPochhammerCoefficientMajorant
                  r K B P Wsrc Tsrc Ssrc *
                (v.factorial * (h + 1 + P) ^ P) *
                (boxAnalyticCoordinateBound B K ell) ^
                  (q + ∑ i, u i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i)))))
    (hstepW : ∀ j, W (j + 1) + k j ≤ W j)
    (hstepT : ∀ j, T (j + 1) + k j ≤ T j)
    (hstepS : ∀ j, S (j + 1) + k j ≤ S j)
    (hstepAR : ∀ j, (A j : ℝ) < R j)
    (hstepA'Z : ∀ j, (A (j + 1) : ℝ) ≤ Z j)
    (hstepZR : ∀ j, Z j ≤ R j)
    (hstepSmall : ∀ j, ∀ h < A (j + 1), ∀ v < W (j + 1),
      ∀ q < T (j + 1), ∀ u : Fin r → ℕ,
      (∀ i, u i < S (j + 1)) →
      (Z j + A j) ^ (k j * A j) *
          (((((K ^ (r + 1) * P : ℕ) : ℝ) *
              ((boxPochhammerCoefficientMajorant
                    r K B P Wsrc Tsrc Ssrc : ℝ) *
                (boxAnalyticCoordinateBound B K ell : ℝ) ^
                  (q + ∑ i, u i) *
                ((v.factorial : ℝ) * (R j + 1 + P) ^ P) *
                Real.exp (((K : ℝ) * ∑ i, ‖ell i‖) * R j)))) /
            (R j - A j) ^ (k j * A j)) <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ (r + 1) + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (P * boxPochhammerCoefficientMajorant
                  r K B P Wsrc Tsrc Ssrc *
                (v.factorial * (h + 1 + P) ^ P) *
                (boxAnalyticCoordinateBound B K ell) ^
                  (q + ∑ i, u i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i)))))
    (hfinalA : K ^ (r + 1) * P ≤ A m)
    (hfinalW : 0 < W m) (hfinalT : 0 < T m) (hfinalS : 0 < S m) :
    False := by
  obtain ⟨c, hc0, hmoment, hc⟩ :=
    exists_box_initial_pochhammer_moment_coefficients_explicit
      alpha b hb hK hP hWsrc hTsrc hSsrc hcard
  let C := boxPochhammerCoefficientMajorant
    r K B P Wsrc Tsrc Ssrc
  let V := boxAnalyticCoordinateBound B K ell
  have hCone : 1 ≤ C := one_le_boxPochhammerCoefficientMajorant _ _ _ _ _ _ _
  have hVone : 1 ≤ V := one_le_boxAnalyticCoordinateBound ell
  have hcC : ∀ x p, (c x p).natAbs ≤ C := by
    intro x p
    exact (hc x p).trans (le_max_right _ _)
  have haV : ∀ x : ExponentBox (r + 1) K,
      ‖boxDistinguishedExponent x‖ ≤ (V : ℝ) := by
    intro x
    refine (boxDistinguishedExponent_norm_le x).trans ?_
    exact_mod_cast (le_max_left K (2 * B * K)).trans
      (boxMomentCoordinateBound_le_boxAnalyticCoordinateBound ell)
  have hrV : ∀ x : ExponentBox (r + 1) K, ∀ i : Fin r,
      ‖boxTransformedExponent b x i‖ ≤ (V : ℝ) := by
    intro x i
    refine (boxTransformedExponent_norm_le b hb x i).trans ?_
    exact_mod_cast (le_max_right K (2 * B * K)).trans
      (boxMomentCoordinateBound_le_boxAnalyticCoordinateBound ell)
  apply no_small_box_linear_form_of_pochhammer_approximate_then_iterated_moments
    φ alpha c (fun x ↦ boxLinearForm ell x)
      (b 0 : ℂ) (∑ i, (b i : ℂ) * ell i)
      boxDistinguishedExponent (boxTransformedExponent b)
      (fun i : Fin r ↦ ell i.succ)
      (Ainit := 1) (Wsrc := Wsrc) (Tsrc := Tsrc) (Ssrc := Ssrc)
      (kapprox := kapprox) (Qaux := Qaux) A W T S k R Z m
      (C := C) (V := V) (U := (K : ℝ) * ∑ i, ‖ell i‖)
      (Rapprox := Rapprox) (Zapprox := Zapprox)
  · exact hK
  · exact hP
  · norm_num
  · exact hkapprox
  · exact happroxW
  · exact happroxT
  · exact happroxS
  · rw [Complex.norm_intCast, ← Int.cast_abs, ← Nat.cast_natAbs]
    exact_mod_cast Int.natAbs_pos.mpr hb0
  · exact hLambda
  · exact hCone
  · exact hVone
  · positivity
  · exact hc0
  · exact hinj
  · exact fun x ↦ boxMonomial_ne_zero alpha halpha x
  · exact hcC
  · exact haV
  · exact hrV
  · exact fun x ↦ boxTransformedLinearForm_norm_le_analyticBound ell b hb x
  · exact fun x ↦ boxLinearForm_norm_le ell x
  · exact hexp
  · exact fun x ↦ box_distinguished_linearForm_identity ell b x
  · exact hmoment
  · simpa only [Nat.cast_one] using happroxAR
  · exact happroxA'Z
  · exact happroxZR
  · simpa [C, V] using happroxSmall
  · exact hstepW
  · exact hstepT
  · exact hstepS
  · exact hstepAR
  · exact hstepA'Z
  · exact hstepZR
  · simpa [C, V] using hstepSmall
  · exact hfinalA
  · exact hfinalW
  · exact hfinalT
  · exact hfinalS


theorem boxPochhammerMoments_iterate_approximate_extrapolation
    {F iota : Type*} [Field F] [NumberField F]
    [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) {n K P : ℕ} (alpha : Fin n → F)
    (c : ExponentBox n K → Fin P → ℤ)
    (L : ExponentBox n K → ℂ) (b0 Lambda : ℂ)
    (a : ExponentBox n K → ℤ)
    (r : ExponentBox n K → iota → ℤ) (ell : iota → ℂ)
    (A W T S k Q : ℕ → ℕ) (R Z : ℕ → ℝ) (m : ℕ)
    {C V : ℕ} {U : ℝ}
    (hK : 0 < K) (hP : 0 < P)
    (hA : ∀ j, j < m → 0 < A j) (hk : ∀ j, j < m → 0 < k j)
    (hb0 : 1 ≤ ‖b0‖) (hLambda : ‖Lambda‖ ≤ 1)
    (hC : 1 ≤ C) (hV : 1 ≤ V) (hU : 0 ≤ U)
    (hc : ∀ x p, (c x p).natAbs ≤ C)
    (haV : ∀ x, ‖a x‖ ≤ (V : ℝ))
    (hrV : ∀ x i, ‖r x i‖ ≤ (V : ℝ))
    (hrLinear : ∀ x, ‖∑ i, (r x i : ℂ) * ell i‖ ≤ (V : ℝ))
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (boxMonomial alpha x))
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin (A 0), ∀ v : Fin (W 0),
      ∀ q : Fin (T 0), ∀ u : iota → Fin (S 0),
        pochhammerMultipointMomentValue (boxMonomial alpha) a r P c
          node v q (fun i ↦ u i) = 0)
    (hW : ∀ j, j < m → W (j + 1) + k j ≤ W j)
    (hT : ∀ j, j < m → T (j + 1) + Q j ≤ T j)
    (hS : ∀ j, j < m → S (j + 1) + k j ≤ S j)
    (hAR : ∀ j, j < m → (A j : ℝ) < R j)
    (hA'Z : ∀ j, j < m → (A (j + 1) : ℝ) ≤ Z j)
    (hZR : ∀ j, j < m → Z j ≤ R j)
    (hsmall : ∀ j, j < m → ∀ h < A (j + 1), ∀ v < W (j + 1),
      ∀ q < T (j + 1), ∀ u : iota → ℕ,
      (∀ i, u i < S (j + 1)) →
      pochhammerWeightedApproximationBound (K ^ n) P (A j) (k j)
          (Q j) v q (∑ i, u i) (C : ℝ) (V : ℝ)
          U (R j) (Z j) ‖Lambda‖ <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ n + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (P * C *
                (v.factorial * (h + 1 + P) ^ P) *
                V ^ (q + ∑ i, u i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i))))) :
    ∀ node : Fin (A m), ∀ v : Fin (W m),
      ∀ q : Fin (T m), ∀ u : iota → Fin (S m),
        pochhammerMultipointMomentValue (boxMonomial alpha) a r P c
          node v q (fun i ↦ u i) = 0 := by
  induction m with
  | zero => simpa using hmoment
  | succ m ih =>
      have ih' := ih
        (fun j hj ↦ hA j (hj.trans (Nat.lt_succ_self m)))
        (fun j hj ↦ hk j (hj.trans (Nat.lt_succ_self m)))
        (fun j hj ↦ hW j (hj.trans (Nat.lt_succ_self m)))
        (fun j hj ↦ hT j (hj.trans (Nat.lt_succ_self m)))
        (fun j hj ↦ hS j (hj.trans (Nat.lt_succ_self m)))
        (fun j hj ↦ hAR j (hj.trans (Nat.lt_succ_self m)))
        (fun j hj ↦ hA'Z j (hj.trans (Nat.lt_succ_self m)))
        (fun j hj ↦ hZR j (hj.trans (Nat.lt_succ_self m)))
        (fun j hj ↦ hsmall j (hj.trans (Nat.lt_succ_self m)))
      apply boxPochhammerMoments_extend_of_approximate_extrapolation
        (A := A m) (W := W m) (T := T m) (S := S m)
        (k := k m) (Q := Q m)
        (A' := A (m + 1)) (W' := W (m + 1))
        (T' := T (m + 1)) (S' := S (m + 1))
        (C := C) (V := V) (U := U) (R := R m) (Z := Z m)
        φ alpha c L b0 Lambda a r ell hK hP (hA m (Nat.lt_succ_self m))
        (hk m (Nat.lt_succ_self m))
        hb0 hLambda hC hV hU hc haV hrV hrLinear hL hexp hcoord ih'
        (hW m (Nat.lt_succ_self m)) (hT m (Nat.lt_succ_self m))
        (hS m (Nat.lt_succ_self m)) (hAR m (Nat.lt_succ_self m))
        (hA'Z m (Nat.lt_succ_self m)) (hZR m (Nat.lt_succ_self m))
        (hsmall m (Nat.lt_succ_self m))


theorem no_small_box_linear_form_of_pochhammer_iterated_approximate_moments
    {F iota : Type*} [Field F] [NumberField F]
    [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) {n K P : ℕ} (alpha : Fin n → F)
    (c : ExponentBox n K → Fin P → ℤ)
    (L : ExponentBox n K → ℂ) (b0 Lambda : ℂ)
    (a : ExponentBox n K → ℤ)
    (r : ExponentBox n K → iota → ℤ) (ell : iota → ℂ)
    (A W T S k Q : ℕ → ℕ) (R Z : ℕ → ℝ) (m : ℕ)
    {C V : ℕ} {U : ℝ}
    (hK : 0 < K) (hP : 0 < P)
    (hA : ∀ j, j < m → 0 < A j) (hk : ∀ j, j < m → 0 < k j)
    (hb0 : 1 ≤ ‖b0‖) (hLambda : ‖Lambda‖ ≤ 1)
    (hC : 1 ≤ C) (hV : 1 ≤ V) (hU : 0 ≤ U)
    (hc0 : c ≠ 0)
    (hinj : Function.Injective
      (fun x : ExponentBox n K ↦ boxMonomial alpha x))
    (hbeta0 : ∀ x : ExponentBox n K, boxMonomial alpha x ≠ 0)
    (hc : ∀ x p, (c x p).natAbs ≤ C)
    (haV : ∀ x, ‖a x‖ ≤ (V : ℝ))
    (hrV : ∀ x i, ‖r x i‖ ≤ (V : ℝ))
    (hrLinear : ∀ x, ‖∑ i, (r x i : ℂ) * ell i‖ ≤ (V : ℝ))
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (boxMonomial alpha x))
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin (A 0), ∀ v : Fin (W 0),
      ∀ q : Fin (T 0), ∀ u : iota → Fin (S 0),
        pochhammerMultipointMomentValue (boxMonomial alpha) a r P c
          node v q (fun i ↦ u i) = 0)
    (hW : ∀ j, j < m → W (j + 1) + k j ≤ W j)
    (hT : ∀ j, j < m → T (j + 1) + Q j ≤ T j)
    (hS : ∀ j, j < m → S (j + 1) + k j ≤ S j)
    (hAR : ∀ j, j < m → (A j : ℝ) < R j)
    (hA'Z : ∀ j, j < m → (A (j + 1) : ℝ) ≤ Z j)
    (hZR : ∀ j, j < m → Z j ≤ R j)
    (hsmall : ∀ j, j < m → ∀ h < A (j + 1), ∀ v < W (j + 1),
      ∀ q < T (j + 1), ∀ u : iota → ℕ,
      (∀ i, u i < S (j + 1)) →
      pochhammerWeightedApproximationBound (K ^ n) P (A j) (k j)
          (Q j) v q (∑ i, u i) (C : ℝ) (V : ℝ)
          U (R j) (Z j) ‖Lambda‖ <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ n + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (P * C *
                (v.factorial * (h + 1 + P) ^ P) *
                V ^ (q + ∑ i, u i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i)))))
    (hfinalA : K ^ n * P ≤ A m)
    (hfinalW : 0 < W m) (hfinalT : 0 < T m) (hfinalS : 0 < S m) :
    False := by
  have hfinal := boxPochhammerMoments_iterate_approximate_extrapolation
    φ alpha c L b0 Lambda a r ell A W T S k Q R Z m
    hK hP hA hk hb0 hLambda hC hV hU hc haV hrV hrLinear
    hL hexp hcoord hmoment hW hT hS hAR hA'Z hZR hsmall
  obtain ⟨t, ht⟩ := exists_pochhammerMultipointMomentValue_ne_zero
    (boxMonomial alpha) hinj hbeta0 a r P c hc0
  have htN : (t : ℕ) < K ^ n * P := by
    simpa [ExponentBox] using t.isLt
  let node : Fin (A m) := ⟨t, htN.trans_le hfinalA⟩
  let v : Fin (W m) := ⟨0, hfinalW⟩
  let q : Fin (T m) := ⟨0, hfinalT⟩
  let u : iota → Fin (S m) := fun _ ↦ ⟨0, hfinalS⟩
  have hz := hfinal node v q u
  exact ht (by simpa [node, v, q, u] using hz)


theorem no_small_distinguished_linear_form_of_pochhammer_approximate_schedule
    {F : Type*} [Field F] [NumberField F]
    (φ : F →+* ℂ) {r B K P Wsrc Tsrc Ssrc : ℕ}
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ)
    (b : Fin (r + 1) → ℤ)
    (A W T S k Q : ℕ → ℕ) (R Z : ℕ → ℝ) (m : ℕ)
    (hK : 0 < K) (hP : 0 < P)
    (hWsrc : 0 < Wsrc) (hTsrc : 0 < Tsrc) (hSsrc : 0 < Ssrc)
    (hcard : Wsrc * Tsrc * Ssrc ^ r < K ^ (r + 1) * P)
    (hb : ∀ i, (b i).natAbs ≤ B) (hb0 : b 0 ≠ 0)
    (halpha : ∀ i, alpha i ≠ 0)
    (hinj : Function.Injective
      (fun x : ExponentBox (r + 1) K ↦ boxMonomial alpha x))
    (hexp : ∀ x : ExponentBox (r + 1) K,
      Complex.exp (boxLinearForm ell x) =
      φ (boxMonomial alpha x))
    (hLambda : ‖∑ i, (b i : ℂ) * ell i‖ ≤ 1)
    (hA0 : A 0 = 1) (hW0 : W 0 = Wsrc)
    (hT0 : T 0 = Tsrc) (hS0 : S 0 = Ssrc)
    (hA : ∀ j, j < m → 0 < A j) (hk : ∀ j, j < m → 0 < k j)
    (hstepW : ∀ j, j < m → W (j + 1) + k j ≤ W j)
    (hstepT : ∀ j, j < m → T (j + 1) + Q j ≤ T j)
    (hstepS : ∀ j, j < m → S (j + 1) + k j ≤ S j)
    (hstepAR : ∀ j, j < m → (A j : ℝ) < R j)
    (hstepA'Z : ∀ j, j < m → (A (j + 1) : ℝ) ≤ Z j)
    (hstepZR : ∀ j, j < m → Z j ≤ R j)
    (hstepSmall : ∀ j, j < m → ∀ h < A (j + 1), ∀ v < W (j + 1),
      ∀ q < T (j + 1), ∀ u : Fin r → ℕ,
      (∀ i, u i < S (j + 1)) →
      pochhammerWeightedApproximationBound (K ^ (r + 1)) P
          (A j) (k j) (Q j) v q (∑ i, u i)
          (boxPochhammerCoefficientMajorant
            r K B P Wsrc Tsrc Ssrc : ℝ)
          (boxAnalyticCoordinateBound B K ell : ℝ)
          ((K : ℝ) * ∑ i, ‖ell i‖) (R j) (Z j)
          ‖∑ i, (b i : ℂ) * ell i‖ <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ (r + 1) + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (P * boxPochhammerCoefficientMajorant
                  r K B P Wsrc Tsrc Ssrc *
                (v.factorial * (h + 1 + P) ^ P) *
                (boxAnalyticCoordinateBound B K ell) ^
                  (q + ∑ i, u i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i)))))
    (hfinalA : K ^ (r + 1) * P ≤ A m)
    (hfinalW : 0 < W m) (hfinalT : 0 < T m) (hfinalS : 0 < S m) :
    False := by
  obtain ⟨c, hc0, hmoment, hc⟩ :=
    exists_box_initial_pochhammer_moment_coefficients_explicit
      alpha b hb hK hP hWsrc hTsrc hSsrc hcard
  let C := boxPochhammerCoefficientMajorant
    r K B P Wsrc Tsrc Ssrc
  let V := boxAnalyticCoordinateBound B K ell
  have hCone : 1 ≤ C := one_le_boxPochhammerCoefficientMajorant _ _ _ _ _ _ _
  have hVone : 1 ≤ V := one_le_boxAnalyticCoordinateBound ell
  have hcC : ∀ x p, (c x p).natAbs ≤ C := by
    intro x p
    exact (hc x p).trans (le_max_right _ _)
  have haV : ∀ x : ExponentBox (r + 1) K,
      ‖boxDistinguishedExponent x‖ ≤ (V : ℝ) := by
    intro x
    refine (boxDistinguishedExponent_norm_le x).trans ?_
    exact_mod_cast (le_max_left K (2 * B * K)).trans
      (boxMomentCoordinateBound_le_boxAnalyticCoordinateBound ell)
  have hrV : ∀ x : ExponentBox (r + 1) K, ∀ i : Fin r,
      ‖boxTransformedExponent b x i‖ ≤ (V : ℝ) := by
    intro x i
    refine (boxTransformedExponent_norm_le b hb x i).trans ?_
    exact_mod_cast (le_max_right K (2 * B * K)).trans
      (boxMomentCoordinateBound_le_boxAnalyticCoordinateBound ell)
  apply no_small_box_linear_form_of_pochhammer_iterated_approximate_moments
    φ alpha c (fun x ↦ boxLinearForm ell x)
      (b 0 : ℂ) (∑ i, (b i : ℂ) * ell i)
      boxDistinguishedExponent (boxTransformedExponent b)
      (fun i : Fin r ↦ ell i.succ)
      A W T S k Q R Z m
      (C := C) (V := V) (U := (K : ℝ) * ∑ i, ‖ell i‖)
  · exact hK
  · exact hP
  · exact hA
  · exact hk
  · rw [Complex.norm_intCast, ← Int.cast_abs, ← Nat.cast_natAbs]
    exact_mod_cast Int.natAbs_pos.mpr hb0
  · exact hLambda
  · exact hCone
  · exact hVone
  · positivity
  · exact hc0
  · exact hinj
  · exact fun x ↦ boxMonomial_ne_zero alpha halpha x
  · exact hcC
  · exact haV
  · exact hrV
  · exact fun x ↦ boxTransformedLinearForm_norm_le_analyticBound ell b hb x
  · exact fun x ↦ boxLinearForm_norm_le ell x
  · exact hexp
  · exact fun x ↦ box_distinguished_linearForm_identity ell b x
  · rw [hA0, hW0, hT0, hS0]
    intro node v q u
    simpa using hmoment node v q u
  · exact hstepW
  · exact hstepT
  · exact hstepS
  · exact hstepAR
  · exact hstepA'Z
  · exact hstepZR
  · simpa [C, V] using hstepSmall
  · exact hfinalA
  · exact hfinalW
  · exact hfinalT
  · exact hfinalS


def dyadicStageCount (N : ℕ) : ℕ := (Nat.log 2 N).succ

def dyadicStageA (j : ℕ) : ℕ := 2 ^ j

def stageSpendBudget (m spend j : ℕ) : ℕ := (m - j) * spend + 1

def stageUnitBudget (m j : ℕ) : ℕ := (m - j) + 1

lemma stageSpendBudget_step {m spend j : ℕ} (hj : j < m) :
    stageSpendBudget m spend (j + 1) + spend =
      stageSpendBudget m spend j := by
  unfold stageSpendBudget
  have hsub : m - j = (m - (j + 1)) + 1 := by omega
  rw [hsub, Nat.add_mul]
  omega

lemma stageUnitBudget_step {m j : ℕ} (hj : j < m) :
    stageUnitBudget m (j + 1) + 1 =
      stageUnitBudget m j := by
  unfold stageUnitBudget
  omega

lemma stageSpendBudget_zero (m spend : ℕ) :
    stageSpendBudget m spend 0 = m * spend + 1 := by
  simp [stageSpendBudget]

lemma stageUnitBudget_zero (m : ℕ) :
    stageUnitBudget m 0 = m + 1 := by
  simp [stageUnitBudget]

lemma stageSpendBudget_self (m spend : ℕ) :
    stageSpendBudget m spend m = 1 := by
  simp [stageSpendBudget]

lemma stageUnitBudget_self (m : ℕ) :
    stageUnitBudget m m = 1 := by
  simp [stageUnitBudget]

lemma le_dyadicStageA_stageCount (N : ℕ) :
    N ≤ dyadicStageA (dyadicStageCount N) := by
  exact (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N).le

theorem no_small_distinguished_linear_form_of_dyadic_schedule
    {F : Type*} [Field F] [NumberField F]
    (φ : F →+* ℂ) {r B K P spend : ℕ}
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ)
    (b : Fin (r + 1) → ℤ) (D : ℝ)
    (hK : 0 < K) (hP : 0 < P) (hspend : 0 < spend)
    (hD : 1 ≤ D)
    (hcard :
      (dyadicStageCount (K ^ (r + 1) * P) * spend + 1) *
          (dyadicStageCount (K ^ (r + 1) * P) + 1) *
          (dyadicStageCount (K ^ (r + 1) * P) * spend + 1) ^ r <
        K ^ (r + 1) * P)
    (hb : ∀ i, (b i).natAbs ≤ B) (hb0 : b 0 ≠ 0)
    (halpha : ∀ i, alpha i ≠ 0)
    (hinj : Function.Injective
      (fun x : ExponentBox (r + 1) K ↦ boxMonomial alpha x))
    (hexp : ∀ x : ExponentBox (r + 1) K,
      Complex.exp (boxLinearForm ell x) =
      φ (boxMonomial alpha x))
    (hLambda : ‖∑ i, (b i : ℂ) * ell i‖ ≤ 1)
    (hsmall :
      let m := dyadicStageCount (K ^ (r + 1) * P)
      ∀ j, j < m → ∀ h < dyadicStageA (j + 1),
        ∀ v < stageSpendBudget m spend (j + 1),
        ∀ q < stageUnitBudget m (j + 1),
        ∀ u : Fin r → ℕ,
        (∀ i, u i < stageSpendBudget m spend (j + 1)) →
        pochhammerWeightedApproximationBound (K ^ (r + 1)) P
            (dyadicStageA j) spend 1 v q (∑ i, u i)
            (boxPochhammerCoefficientMajorant r K B P
              (m * spend + 1) (m + 1) (m * spend + 1) : ℝ)
            (boxAnalyticCoordinateBound B K ell : ℝ)
            ((K : ℝ) * ∑ i, ‖ell i‖)
            (D * (dyadicStageA (j + 1) : ℝ))
            (dyadicStageA (j + 1) : ℝ)
            ‖∑ i, (b i : ℂ) * ell i‖ <
          Real.exp (-((Module.finrank ℚ F : ℝ) *
                Real.log (K ^ (r + 1) + 1 : ℕ) +
              (Module.finrank ℚ F : ℝ) *
                Real.log (P * boxPochhammerCoefficientMajorant r K B P
                    (m * spend + 1) (m + 1) (m * spend + 1) *
                  (v.factorial * (h + 1 + P) ^ P) *
                  (boxAnalyticCoordinateBound B K ell) ^
                    (q + ∑ i, u i) : ℕ) +
              (h : ℝ) * ((K : ℝ) *
                ∑ i, Height.logHeight₁ (alpha i))))) :
    False := by
  let N := K ^ (r + 1) * P
  let m := dyadicStageCount N
  let A : ℕ → ℕ := dyadicStageA
  let W : ℕ → ℕ := stageSpendBudget m spend
  let T : ℕ → ℕ := stageUnitBudget m
  let S : ℕ → ℕ := stageSpendBudget m spend
  let k : ℕ → ℕ := fun _ ↦ spend
  let Q : ℕ → ℕ := fun _ ↦ 1
  let R : ℕ → ℝ := fun j ↦ D * (A (j + 1) : ℝ)
  let Z : ℕ → ℝ := fun j ↦ (A (j + 1) : ℝ)
  apply no_small_distinguished_linear_form_of_pochhammer_approximate_schedule
    φ alpha ell b A W T S k Q R Z m
      (Wsrc := m * spend + 1) (Tsrc := m + 1)
      (Ssrc := m * spend + 1)
  · exact hK
  · exact hP
  · positivity
  · positivity
  · positivity
  · simpa [N, m] using hcard
  · exact hb
  · exact hb0
  · exact halpha
  · exact hinj
  · exact hexp
  · exact hLambda
  · simp [A, dyadicStageA]
  · simp [W, stageSpendBudget]
  · simp [T, stageUnitBudget]
  · simp [S, stageSpendBudget]
  · intro j hj
    simp [A, dyadicStageA]
  · intro j hj
    simpa [k] using hspend
  · intro j hj
    exact (stageSpendBudget_step hj).le
  · intro j hj
    exact (stageUnitBudget_step hj).le
  · intro j hj
    exact (stageSpendBudget_step hj).le
  · intro j hj
    dsimp [A, R, dyadicStageA]
    have hpow : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
    calc
      ((2 ^ j : ℕ) : ℝ) < 2 * ((2 ^ j : ℕ) : ℝ) := by nlinarith
      _ ≤ D * (2 * ((2 ^ j : ℕ) : ℝ)) := by
        have hm := mul_le_mul_of_nonneg_right hD
          (show 0 ≤ 2 * ((2 ^ j : ℕ) : ℝ) by positivity)
        simpa using hm
      _ = D * ((2 ^ (j + 1) : ℕ) : ℝ) := by
        rw [pow_succ]
        push_cast
        ring
  · intro j hj
    simp [A, Z, dyadicStageA]
  · intro j hj
    dsimp [R, Z]
    exact le_mul_of_one_le_left (by positivity) hD
  · dsimp [N, m, A, W, T, S, k, Q, R, Z] at hsmall ⊢
    exact hsmall
  · dsimp [N, A, m]
    exact le_dyadicStageA_stageCount N
  · simp [W, stageSpendBudget]
  · simp [T, stageUnitBudget]
  · simp [S, stageSpendBudget]


lemma pochhammerWeightedApproximationBound_continuous
    (N P A k Q v q u : ℕ) (C V U R Z : ℝ) :
    Continuous (fun x : ℝ ↦
      pochhammerWeightedApproximationBound N P A k Q v q u C V U R Z x) := by
  unfold pochhammerWeightedApproximationBound
  fun_prop

theorem exists_uniform_lambda_radius_of_boundary_small
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (N P : ℕ) (A W T S k Q : ℕ → ℕ)
    (C V U : ℝ) (R Z : ℕ → ℝ) (m : ℕ)
    (target : (j : ℕ) → ℕ → ℕ → ℕ → (iota → ℕ) → ℝ)
    (hboundary : ∀ j, j < m → ∀ h < A (j + 1),
      ∀ v < W (j + 1), ∀ q < T (j + 1), ∀ u : iota → ℕ,
      (∀ i, u i < S (j + 1)) →
      pochhammerWeightedApproximationBound N P (A j) (k j) (Q j)
          v q (∑ i, u i) C V U (R j) (Z j) 0 <
        target j h v q u) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ lambdaNorm : ℝ, |lambdaNorm| < ε →
      ∀ j, j < m → ∀ h < A (j + 1),
      ∀ v < W (j + 1), ∀ q < T (j + 1), ∀ u : iota → ℕ,
      (∀ i, u i < S (j + 1)) →
      pochhammerWeightedApproximationBound N P (A j) (k j) (Q j)
          v q (∑ i, u i) C V U (R j) (Z j) lambdaNorm <
        target j h v q u := by
  have hlocal (j : Fin m) (h : Fin (A (j + 1)))
      (v : Fin (W (j + 1))) (q : Fin (T (j + 1)))
      (u : iota → Fin (S (j + 1))) :
      ∀ᶠ lambdaNorm : ℝ in nhds 0,
        pochhammerWeightedApproximationBound N P (A j) (k j) (Q j)
            v q (∑ i, (u i : ℕ)) C V U (R j) (Z j) lambdaNorm <
          target j h v q (fun i ↦ u i) := by
    apply (pochhammerWeightedApproximationBound_continuous
      N P (A j) (k j) (Q j) v q (∑ i, (u i : ℕ))
        C V U (R j) (Z j)).continuousAt.eventually_lt continuousAt_const
    exact hboundary j j.isLt h h.isLt v v.isLt q q.isLt
      (fun i ↦ u i) (fun i ↦ (u i).isLt)
  have hall : ∀ᶠ lambdaNorm : ℝ in nhds 0,
      ∀ j : Fin m, ∀ h : Fin (A (j + 1)),
      ∀ v : Fin (W (j + 1)), ∀ q : Fin (T (j + 1)),
      ∀ u : iota → Fin (S (j + 1)),
        pochhammerWeightedApproximationBound N P (A j) (k j) (Q j)
            v q (∑ i, (u i : ℕ)) C V U (R j) (Z j) lambdaNorm <
          target j h v q (fun i ↦ u i) := by
    exact Filter.eventually_all.2 fun j ↦
      Filter.eventually_all.2 fun h ↦
      Filter.eventually_all.2 fun v ↦
      Filter.eventually_all.2 fun q ↦
      Filter.eventually_all.2 fun u ↦ hlocal j h v q u
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hall
  refine ⟨ε, hε, fun lambdaNorm hlambda j hj h hh v hv q hq u hu ↦ ?_⟩
  let jf : Fin m := ⟨j, hj⟩
  let hf : Fin (A (j + 1)) := ⟨h, hh⟩
  let vf : Fin (W (j + 1)) := ⟨v, hv⟩
  let qf : Fin (T (j + 1)) := ⟨q, hq⟩
  let uf : iota → Fin (S (j + 1)) := fun i ↦ ⟨u i, hu i⟩
  have hmem : lambdaNorm ∈ Metric.ball (0 : ℝ) ε := by
    simpa [Real.dist_eq] using hlambda
  have hout := hball lambdaNorm hmem jf hf vf qf uf
  simpa [jf, hf, vf, qf, uf] using hout


lemma pochhammerWeightedApproximationBound_zero
    (N P A k v q u : ℕ) (C V U R Z : ℝ) :
    pochhammerWeightedApproximationBound N P A k 1 v q u C V U R Z 0 =
      (Z + A) ^ (k * A) *
        (((N * P : ℕ) : ℝ) *
          (C * V ^ (q + u) * (v.factorial : ℝ) *
            (R + 1 + P) ^ P * Real.exp (U * R)) /
          (R - A) ^ (k * A)) := by
  simp [pochhammerWeightedApproximationBound]


/-- The elementary one-place Liouville inequality supplied by the product
formula: at any complex embedding, the logarithm of a nonzero algebraic
number cannot lie below minus its unnormalised logarithmic height.  This is
the local lower-bound input for the auxiliary determinants in the
Baker--Wüstholz argument. -/
lemma numberField_neg_logHeight_le_log_norm_embedding
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) {x : K} (_hx : x ≠ 0) :
    -Height.logHeight₁ x ≤ Real.log ‖φ x‖ := by
  let w : NumberField.InfinitePlace K :=
    NumberField.InfinitePlace.mk φ
  have harchTerm :
      (w.mult : ℝ) * Real.posLog (w (x⁻¹)) ≤
        ∑ v : NumberField.InfinitePlace K,
          (v.mult : ℝ) * Real.posLog (v (x⁻¹)) := by
    exact Finset.single_le_sum
      (fun (v : NumberField.InfinitePlace K) _ ↦
        mul_nonneg (Nat.cast_nonneg v.mult)
          (show 0 ≤ Real.posLog (v (x⁻¹)) from Real.posLog_nonneg))
      (Finset.mem_univ w)
  have hnonarch : 0 ≤
      ∑ᶠ v : NumberField.FinitePlace K, Real.posLog (v (x⁻¹)) :=
    finsum_nonneg fun v : NumberField.FinitePlace K ↦
      (show 0 ≤ Real.posLog (v (x⁻¹)) from Real.posLog_nonneg)
  have htermHeight :
      (w.mult : ℝ) * Real.posLog (w (x⁻¹)) ≤
        Height.logHeight₁ x := by
    calc
      _ ≤ ∑ v : NumberField.InfinitePlace K,
          (v.mult : ℝ) * Real.posLog (v (x⁻¹)) := harchTerm
      _ ≤ (∑ v : NumberField.InfinitePlace K,
          (v.mult : ℝ) * Real.posLog (v (x⁻¹))) +
          ∑ᶠ v : NumberField.FinitePlace K,
            Real.posLog (v (x⁻¹)) := le_add_of_nonneg_right hnonarch
      _ = Height.logHeight₁ (x⁻¹) :=
        (NumberField.logHeight₁_eq (x⁻¹)).symm
      _ = Height.logHeight₁ x := Height.logHeight₁_inv x
  have hwInv : w (x⁻¹) = ‖φ x‖⁻¹ := by
    simp [w]
  have hneglog : -Real.log ‖φ x‖ ≤ Real.posLog (w (x⁻¹)) := by
    rw [hwInv]
    change -Real.log ‖φ x‖ ≤ max 0 (Real.log ‖φ x‖⁻¹)
    rw [Real.log_inv]
    exact le_max_right _ _
  have hmult : Real.posLog (w (x⁻¹)) ≤
      (w.mult : ℝ) * Real.posLog (w (x⁻¹)) := by
    nth_rewrite 1 [← one_mul (Real.posLog (w (x⁻¹)))]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr w.mult_ne_zero)
      Real.posLog_nonneg
  linarith

/-- The complementary one-place upper inequality: the logarithmic norm at
one complex embedding is at most the global unnormalised height. -/
lemma numberField_log_norm_embedding_le_logHeight
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (x : K) :
    Real.log ‖φ x‖ ≤ Height.logHeight₁ x := by
  let w : NumberField.InfinitePlace K := NumberField.InfinitePlace.mk φ
  have harchTerm :
      (w.mult : ℝ) * Real.posLog (w x) ≤
        ∑ v : NumberField.InfinitePlace K,
          (v.mult : ℝ) * Real.posLog (v x) := by
    exact Finset.single_le_sum
      (fun (v : NumberField.InfinitePlace K) _ ↦
        mul_nonneg (Nat.cast_nonneg v.mult)
          (show 0 ≤ Real.posLog (v x) from Real.posLog_nonneg))
      (Finset.mem_univ w)
  have hnonarch : 0 ≤
      ∑ᶠ v : NumberField.FinitePlace K, Real.posLog (v x) :=
    finsum_nonneg fun _ ↦ Real.posLog_nonneg
  have htermHeight :
      (w.mult : ℝ) * Real.posLog (w x) ≤ Height.logHeight₁ x := by
    calc
      _ ≤ ∑ v : NumberField.InfinitePlace K,
          (v.mult : ℝ) * Real.posLog (v x) := harchTerm
      _ ≤ (∑ v : NumberField.InfinitePlace K,
          (v.mult : ℝ) * Real.posLog (v x)) +
          ∑ᶠ v : NumberField.FinitePlace K, Real.posLog (v x) :=
        le_add_of_nonneg_right hnonarch
      _ = Height.logHeight₁ x := (NumberField.logHeight₁_eq x).symm
  have hw : w x = ‖φ x‖ := by simp [w]
  have hlog : Real.log ‖φ x‖ ≤ Real.posLog (w x) := by
    rw [hw]
    exact le_max_right _ _
  have hmult : Real.posLog (w x) ≤
      (w.mult : ℝ) * Real.posLog (w x) := by
    nth_rewrite 1 [← one_mul (Real.posLog (w x))]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr w.mult_ne_zero)
      Real.posLog_nonneg
  exact hlog.trans (hmult.trans htermHeight)

/-- At a nonzero algebraic number, the absolute logarithmic norm at any
complex embedding is bounded by its global unnormalised height. -/
lemma numberField_abs_log_norm_embedding_le_logHeight
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) {x : K} (hx : x ≠ 0) :
    |Real.log ‖φ x‖| ≤ Height.logHeight₁ x := by
  rw [abs_le]
  exact ⟨numberField_neg_logHeight_le_log_norm_embedding φ hx,
    numberField_log_norm_embedding_le_logHeight φ x⟩

attribute [local instance] Matrix.seminormedAddCommGroup

/-- Quantitative control of the integral trace-coordinate matrix obtained
from a common integral denominator.  The estimate is deliberately coarse:
each trace is bounded by the sum of all complex embeddings. -/
lemma traceConstraintMatrix_norm_le
    {K rows cols ι : Type*} [Field K] [NumberField K]
    [Fintype rows] [Fintype cols] [Fintype ι]
    (b : Module.Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i))
    (A : Matrix rows cols K) (Q : ℕ)
    (hQA : ∀ r j, IsIntegral ℤ ((Q : K) * A r j))
    {H M S : ℝ} (hS : 0 ≤ S) (hM0 : 0 ≤ M)
    (hH : ∀ r j, Height.logHeight₁ (A r j) ≤ H)
    (hM : ∀ i (φ : K →ₐ[ℚ] ℂ), ‖φ (b i)‖ ≤ M)
    (hQ : (Q : ℝ) ≤ S) :
    ‖traceConstraintMatrix b hb A Q hQA‖ ≤
      (Module.finrank ℚ K : ℝ) * S * Real.exp H * M := by
  have hRHS : 0 ≤ (Module.finrank ℚ K : ℝ) * S * Real.exp H * M :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hS)
      (Real.exp_pos H).le) hM0
  rw [Matrix.norm_le_iff hRHS]
  intro ri j
  let u : NumberField.RingOfIntegers K :=
    ⟨(Q : K) * A ri.1 j, hQA ri.1 j⟩
  let v : NumberField.RingOfIntegers K := ⟨b ri.2, hb ri.2⟩
  have htrace :
      ((Algebra.trace ℤ (NumberField.RingOfIntegers K) (u * v) : ℤ) : ℂ) =
        ∑ φ : K →ₐ[ℚ] ℂ, φ (((u * v : NumberField.RingOfIntegers K) : K)) := by
    calc
      ((Algebra.trace ℤ (NumberField.RingOfIntegers K) (u * v) : ℤ) : ℂ) =
          algebraMap ℚ ℂ
            ((Algebra.trace ℤ (NumberField.RingOfIntegers K) (u * v) : ℤ) : ℚ) := by
        norm_num
      _ = algebraMap ℚ ℂ
          (Algebra.trace ℚ K (((u * v : NumberField.RingOfIntegers K) : K))) := by
        rw [Algebra.coe_trace_int]
      _ = ∑ φ : K →ₐ[ℚ] ℂ,
          φ (((u * v : NumberField.RingOfIntegers K) : K)) :=
        trace_eq_sum_embeddings ℂ
  have hAemb : ∀ φ : K →ₐ[ℚ] ℂ, ‖φ (A ri.1 j)‖ ≤ Real.exp H := by
    intro φ
    by_cases hz : A ri.1 j = 0
    · simp [hz, (Real.exp_pos H).le]
    · have hp : 0 < ‖φ (A ri.1 j)‖ := norm_pos_iff.mpr
          ((map_ne_zero_iff φ.toRingHom φ.injective).mpr hz)
      calc
        ‖φ (A ri.1 j)‖ = Real.exp (Real.log ‖φ (A ri.1 j)‖) := by
          rw [Real.exp_log hp]
        _ ≤ Real.exp H := Real.exp_le_exp.mpr
          ((numberField_log_norm_embedding_le_logHeight φ.toRingHom _).trans
            (hH ri.1 j))
  have hterm : ∀ φ : K →ₐ[ℚ] ℂ,
      ‖φ (((u * v : NumberField.RingOfIntegers K) : K))‖ ≤
        S * Real.exp H * M := by
    intro φ
    change ‖φ ((Q : K) * A ri.1 j * b ri.2)‖ ≤ _
    rw [map_mul, map_mul, norm_mul, norm_mul]
    have hQnorm : ‖φ (Q : K)‖ ≤ S := by
      simpa using hQ
    exact mul_le_mul
      (mul_le_mul hQnorm (hAemb φ) (by positivity) hS)
      (hM ri.2 φ) (norm_nonneg _) (mul_nonneg hS (Real.exp_pos H).le)
  change ‖Algebra.trace ℤ (NumberField.RingOfIntegers K) (u * v)‖ ≤ _
  have hcastNorm :
      ‖Algebra.trace ℤ (NumberField.RingOfIntegers K) (u * v)‖ =
        ‖((Algebra.trace ℤ (NumberField.RingOfIntegers K) (u * v) : ℤ) : ℂ)‖ := by
    norm_num [Int.norm_eq_abs]
  rw [hcastNorm, htrace]
  calc
    ‖∑ φ : K →ₐ[ℚ] ℂ, φ (((u * v : NumberField.RingOfIntegers K) : K))‖ ≤
        ∑ φ : K →ₐ[ℚ] ℂ,
          ‖φ (((u * v : NumberField.RingOfIntegers K) : K))‖ := norm_sum_le _ _
    _ ≤ ∑ _φ : K →ₐ[ℚ] ℂ, (S * Real.exp H * M) := by
      gcongr with φ hφ
      exact hterm φ
    _ = (Module.finrank ℚ K : ℝ) * S * Real.exp H * M := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        AlgHom.card ℚ K ℂ]
      ring

/-- A number-field form of Siegel's lemma.  Taking traces against an
integral rational basis turns each algebraic row into `deg K` integral
rows.  Nondegeneracy of the trace pairing recovers the original kernel. -/
theorem exists_bounded_nonzero_integer_kernel_numberField
    {K rows cols ι : Type*} [Field K] [NumberField K]
    [Fintype rows] [Fintype cols] [Fintype ι]
    [Nonempty rows]
    (b : Module.Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i))
    (A : Matrix rows cols K) {H M : ℝ}
    (hM0 : 0 ≤ M)
    (hH : ∀ r j, Height.logHeight₁ (A r j) ≤ H)
    (hM : ∀ i (φ : K →ₐ[ℚ] ℂ), ‖φ (b i)‖ ≤ M)
    (hcard : Fintype.card rows * Fintype.card ι < Fintype.card cols) :
    ∃ (Q : ℕ) (_hQ0 : Q ≠ 0)
        (hQA : ∀ r j, IsIntegral ℤ ((Q : K) * A r j))
        (c : cols → ℤ),
      (Q : ℝ) ≤ Real.exp H ^ (Fintype.card rows * Fintype.card cols) ∧
      c ≠ 0 ∧ A.mulVec (fun j ↦ (c j : K)) = 0 ∧
      (∀ j, (c j).natAbs ≤ Nat.ceil
        (((Fintype.card cols : ℝ) *
            max 1 ‖traceConstraintMatrix b hb A Q hQA‖) ^
          (((Fintype.card rows * Fintype.card ι : ℕ) : ℝ) /
            ((Fintype.card cols : ℝ) -
              (Fintype.card rows * Fintype.card ι : ℕ))))) ∧
      ‖traceConstraintMatrix b hb A Q hQA‖ ≤
        (Module.finrank ℚ K : ℝ) *
          (Real.exp H ^ (Fintype.card rows * Fintype.card cols)) *
          Real.exp H * M := by
  classical
  obtain ⟨Q, hQ0, hQbound, hQAflat⟩ :=
    exists_common_integral_scale
      (fun rc : rows × cols ↦ A rc.1 rc.2)
      (fun rc ↦ hH rc.1 rc.2)
  have hQA : ∀ r j, IsIntegral ℤ ((Q : K) * A r j) :=
    fun r j ↦ hQAflat (r, j)
  let T := traceConstraintMatrix b hb A Q hQA
  have hcard' : Fintype.card (rows × ι) < Fintype.card cols := by
    simpa [Fintype.card_prod] using hcard
  let : Nonempty ι := Fintype.card_pos_iff.mp <| by
    rw [← Module.finrank_eq_card_basis b]
    exact Module.finrank_pos
  have hrows' : 0 < Fintype.card (rows × ι) := Fintype.card_pos
  obtain ⟨c, hc0, hkernel, hcbound⟩ :=
    exists_bounded_nonzero_integer_kernel T hcard' hrows'
  have hAker : A.mulVec (fun j ↦ (c j : K)) = 0 :=
    traceConstraintMatrix_kernel b hb A Q hQ0 hQA c hkernel
  have hQbound' :
      (Q : ℝ) ≤ Real.exp H ^ (Fintype.card rows * Fintype.card cols) := by
    simpa [Fintype.card_prod] using hQbound
  have hTnorm : ‖T‖ ≤
      (Module.finrank ℚ K : ℝ) *
        (Real.exp H ^ (Fintype.card rows * Fintype.card cols)) *
        Real.exp H * M := by
    apply traceConstraintMatrix_norm_le b hb A Q hQA
      (by positivity) hM0 hH hM hQbound'
  refine ⟨Q, hQ0, hQA, c, hQbound', hc0, hAker, ?_, hTnorm⟩
  simpa [T, Fintype.card_prod] using hcbound

/-- Siegel's lemma for the algebraic multipoint moment system used in the
fixed-rank logarithmic-form argument.  It returns the exact moments together
with the coefficient and trace-matrix bounds needed by extrapolation. -/
theorem exists_bounded_nonzero_multipoint_moment_coefficients_numberField
    {F kappa iota ι : Type*} [Field F] [NumberField F]
    [Fintype kappa] [Fintype iota] [DecidableEq iota] [Fintype ι]
    (basis : Module.Basis ι ℚ F)
    (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (beta : kappa → F) (a : kappa → ℤ) (r : kappa → iota → ℤ)
    (A T S : ℕ) {H V M : ℝ}
    (hA : 0 < A) (hT : 0 < T) (hS : 0 < S)
    (hV : 1 ≤ V) (hM0 : 0 ≤ M)
    (hbeta : ∀ k, Height.logHeight₁ (beta k) ≤ H)
    (ha : ∀ k, ‖a k‖ ≤ V) (hr : ∀ k i, ‖r k i‖ ≤ V)
    (hM : ∀ i (φ : F →ₐ[ℚ] ℂ), ‖φ (basis i)‖ ≤ M)
    (hcard :
      (A * T * S ^ Fintype.card iota) * Fintype.card ι <
        Fintype.card kappa) :
    let Hentry : ℝ := (A : ℝ) * H +
      ((T + Fintype.card iota * S : ℕ) : ℝ) *
        ((Module.finrank ℚ F : ℝ) * Real.log V)
    ∃ (Q : ℕ) (_hQ0 : Q ≠ 0)
        (hQint : ∀ row k, IsIntegral ℤ
          ((Q : F) * multipointRectangularMomentMatrix
            beta a r A T S row k))
        (c : kappa → ℤ),
      (Q : ℝ) ≤ Real.exp Hentry ^
          ((A * T * S ^ Fintype.card iota) * Fintype.card kappa) ∧
      c ≠ 0 ∧
      (∀ h : Fin A, ∀ q : Fin T, ∀ u : iota → Fin S,
        ∑ k, (c k : F) * beta k ^ (h : ℕ) * (a k : F) ^ (q : ℕ) *
          ∏ i, (r k i : F) ^ (u i : ℕ) = 0) ∧
      (∀ k, (c k).natAbs ≤ Nat.ceil
        (((Fintype.card kappa : ℝ) *
            max 1 ‖traceConstraintMatrix basis hbasis
              (multipointRectangularMomentMatrix beta a r A T S)
              Q hQint‖) ^
          ((((A * T * S ^ Fintype.card iota) * Fintype.card ι : ℕ) : ℝ) /
            ((Fintype.card kappa : ℝ) -
              ((A * T * S ^ Fintype.card iota) * Fintype.card ι : ℕ))))) ∧
      ‖traceConstraintMatrix basis hbasis
          (multipointRectangularMomentMatrix beta a r A T S)
          Q hQint‖ ≤
        (Module.finrank ℚ F : ℝ) *
          (Real.exp Hentry ^
            ((A * T * S ^ Fintype.card iota) * Fintype.card kappa)) *
          Real.exp Hentry * M := by
  dsimp only
  let rows := MultipointRectangularMomentIndex iota A T S
  let : Fintype rows := by
    dsimp [rows, MultipointRectangularMomentIndex,
      RectangularMomentIndex]
    infer_instance
  let matrix : Matrix rows kappa F :=
    multipointRectangularMomentMatrix beta a r A T S
  have hrowsCard : Fintype.card rows =
      A * T * S ^ Fintype.card iota := by
    simp [rows, MultipointRectangularMomentIndex,
      RectangularMomentIndex, Nat.mul_assoc]
  let Hentry : ℝ := (A : ℝ) * H +
      ((T + Fintype.card iota * S : ℕ) : ℝ) *
        ((Module.finrank ℚ F : ℝ) * Real.log V)
  have hheight : ∀ row k, Height.logHeight₁ (matrix row k) ≤ Hentry := by
    intro row k
    exact logHeight₁_multipointRectangularMomentMatrix_le
      beta a r A T S hV hbeta ha hr row k
  have : Nonempty rows := Fintype.card_pos_iff.mp <| by
    rw [hrowsCard]
    positivity
  have hcard' : Fintype.card rows * Fintype.card ι <
      Fintype.card kappa := by
    simpa [hrowsCard] using hcard
  obtain ⟨Q, hQ0, hQint, c, hQ, hc0, hker, hc, hnorm⟩ :=
    exists_bounded_nonzero_integer_kernel_numberField
      basis hbasis matrix hM0 hheight hM hcard'
  have hmom :=
    (multipointRectangularMomentMatrix_kernel_iff
      beta a r A T S c).mp hker
  refine ⟨Q, hQ0, hQint, c, ?_, hc0, hmom, ?_, ?_⟩
  · simpa [Hentry, hrowsCard] using hQ
  · simpa [matrix, Hentry, hrowsCard] using hc
  · simpa [matrix, Hentry, hrowsCard] using hnorm


attribute [local instance] Matrix.seminormedAddCommGroup

abbrev PochhammerMultipointInitialMomentIndex
    (iota : Type*) (A W T S : ℕ) :=
  Fin A × Fin W × RectangularMomentIndex iota T S

noncomputable def pochhammerMultipointInitialMomentMatrix
    {F κ iota : Type*} [CommRing F] [Fintype κ] [Fintype iota]
    (beta : κ → F) (a : κ → ℤ) (r : κ → iota → ℤ)
    (P A W T S : ℕ) :
    Matrix (PochhammerMultipointInitialMomentIndex iota A W T S)
      (κ × Fin P) F :=
  fun hvqu xm ↦
    (pochhammerJet (xm.2 : ℕ) (hvqu.2.1 : ℕ) (hvqu.1 : ℕ) : F) *
      beta xm.1 ^ (hvqu.1 : ℕ) *
      (a xm.1 : F) ^ (hvqu.2.2.1 : ℕ) *
      ∏ i, (r xm.1 i : F) ^ (hvqu.2.2.2 i : ℕ)

lemma pochhammerMultipointInitialMomentMatrix_kernel_iff
    {F κ iota : Type*} [CommRing F] [Fintype κ] [Fintype iota]
    (beta : κ → F) (a : κ → ℤ) (r : κ → iota → ℤ)
    (P A W T S : ℕ) (c : κ → Fin P → ℤ) :
    (pochhammerMultipointInitialMomentMatrix beta a r P A W T S).mulVec
        (fun xm ↦ (c xm.1 xm.2 : F)) = 0 ↔
      ∀ node : Fin A, ∀ v : Fin W, ∀ q : Fin T,
        ∀ u : iota → Fin S,
          pochhammerMultipointMomentValue beta a r P c node v q
            (fun i ↦ u i) = 0 := by
  constructor
  · intro hker node v q u
    have hz := congrFun hker (node, v, q, u)
    rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type] at hz
    simpa [pochhammerMultipointInitialMomentMatrix,
      pochhammerMultipointMomentValue, mul_assoc, mul_comm, mul_left_comm]
      using hz
  · intro h
    funext hvqu
    rcases hvqu with ⟨node, v, q, u⟩
    have hz := h node v q u
    rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
    simpa [pochhammerMultipointInitialMomentMatrix,
      pochhammerMultipointMomentValue, mul_assoc, mul_comm, mul_left_comm]
      using hz

theorem logHeight₁_pochhammerMultipointInitialMomentMatrix_le
    {F κ iota : Type*} [Field F] [NumberField F]
    [Fintype κ] [Fintype iota]
    (beta : κ → F) (a : κ → ℤ) (r : κ → iota → ℤ)
    (P A W T S : ℕ) {H V : ℝ}
    (hA : 0 < A) (hW : 0 < W) (hP : 0 < P) (hV : 1 ≤ V)
    (hbeta : ∀ x, Height.logHeight₁ (beta x) ≤ H)
    (ha : ∀ x, ‖a x‖ ≤ V) (hr : ∀ x i, ‖r x i‖ ≤ V) :
    ∀ row xm,
      Height.logHeight₁
          (pochhammerMultipointInitialMomentMatrix
            beta a r P A W T S row xm) ≤
        (Module.finrank ℚ F : ℝ) *
            Real.log ((W.factorial * (A + P) ^ P : ℕ) : ℝ) +
          (A : ℝ) * H +
          ((T + Fintype.card iota * S : ℕ) : ℝ) *
            ((Module.finrank ℚ F : ℝ) * Real.log V) := by
  intro row xm
  rcases row with ⟨node, v, q, u⟩
  let J : ℕ := W.factorial * (A + P) ^ P
  have hJ : 1 ≤ J := by
    dsimp [J]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (Nat.factorial_ne_zero W) (pow_ne_zero _ (by omega)))
  have hjetNat :
      (pochhammerJet (xm.2 : ℕ) (v : ℕ) (node : ℕ)).natAbs ≤ J := by
    refine (natAbs_pochhammerJet_le xm.2.isLt (v : ℕ) (node : ℕ)).trans ?_
    dsimp [J]
    gcongr
    · exact v.isLt.le
    · omega
  have hjet : Height.logHeight₁
      (pochhammerJet (xm.2 : ℕ) (v : ℕ) (node : ℕ) : F) ≤
      (Module.finrank ℚ F : ℝ) * Real.log (J : ℝ) := by
    refine (logHeight₁_intCast_le
      (K := F) (pochhammerJet (xm.2 : ℕ) (v : ℕ) (node : ℕ))).trans ?_
    gcongr
    exact_mod_cast max_le hJ hjetNat
  have hrest := logHeight₁_multipointRectangularMomentMatrix_le
    beta a r A T S hV hbeta ha hr (node, q, u) xm.1
  rw [pochhammerMultipointInitialMomentMatrix]
  calc
    Height.logHeight₁
        ((pochhammerJet (xm.2 : ℕ) (v : ℕ) (node : ℕ) : F) *
          beta xm.1 ^ (node : ℕ) * (a xm.1 : F) ^ (q : ℕ) *
          ∏ i, (r xm.1 i : F) ^ (u i : ℕ)) ≤
      Height.logHeight₁
          (pochhammerJet (xm.2 : ℕ) (v : ℕ) (node : ℕ) : F) +
        Height.logHeight₁
          (beta xm.1 ^ (node : ℕ) * (a xm.1 : F) ^ (q : ℕ) *
            ∏ i, (r xm.1 i : F) ^ (u i : ℕ)) := by
      simpa [mul_assoc] using Height.logHeight₁_mul_le
        (pochhammerJet (xm.2 : ℕ) (v : ℕ) (node : ℕ) : F)
        (beta xm.1 ^ (node : ℕ) * (a xm.1 : F) ^ (q : ℕ) *
          ∏ i, (r xm.1 i : F) ^ (u i : ℕ))
    _ ≤ (Module.finrank ℚ F : ℝ) * Real.log (J : ℝ) +
        ((A : ℝ) * H +
          ((T + Fintype.card iota * S : ℕ) : ℝ) *
            ((Module.finrank ℚ F : ℝ) * Real.log V)) :=
      add_le_add hjet hrest
    _ = _ := by simp [J, add_assoc]

theorem exists_bounded_nonzero_pochhammerMultipoint_coefficients_numberField
    {F κ iota ι : Type*} [Field F] [NumberField F]
    [Fintype κ] [Fintype iota] [DecidableEq iota] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (beta : κ → F) (a : κ → ℤ) (r : κ → iota → ℤ)
    (P A W T S : ℕ) {H V M : ℝ}
    (hP : 0 < P) (hA : 0 < A) (hW : 0 < W)
    (hT : 0 < T) (hS : 0 < S)
    (hV : 1 ≤ V) (hM0 : 0 ≤ M)
    (hbeta : ∀ x, Height.logHeight₁ (beta x) ≤ H)
    (ha : ∀ x, ‖a x‖ ≤ V) (hr : ∀ x i, ‖r x i‖ ≤ V)
    (hM : ∀ i (φ : F →ₐ[ℚ] ℂ), ‖φ (basis i)‖ ≤ M)
    (hcard :
      (A * W * T * S ^ Fintype.card iota) * Fintype.card ι <
        Fintype.card κ * P) :
    let Hentry : ℝ :=
      (Module.finrank ℚ F : ℝ) *
          Real.log ((W.factorial * (A + P) ^ P : ℕ) : ℝ) +
        (A : ℝ) * H +
        ((T + Fintype.card iota * S : ℕ) : ℝ) *
          ((Module.finrank ℚ F : ℝ) * Real.log V)
    ∃ (Q : ℕ) (_hQ0 : Q ≠ 0)
        (hQint : ∀ row xm, IsIntegral ℤ
          ((Q : F) * pochhammerMultipointInitialMomentMatrix
            beta a r P A W T S row xm))
        (c : κ → Fin P → ℤ),
      (Q : ℝ) ≤ Real.exp Hentry ^
          ((A * W * T * S ^ Fintype.card iota) *
            (Fintype.card κ * P)) ∧
      c ≠ 0 ∧
      (∀ node : Fin A, ∀ v : Fin W, ∀ q : Fin T,
        ∀ u : iota → Fin S,
          pochhammerMultipointMomentValue beta a r P c node v q
            (fun i ↦ u i) = 0) ∧
      (∀ x p, (c x p).natAbs ≤ Nat.ceil
        ((((Fintype.card κ * P : ℕ) : ℝ) *
          max 1 ‖traceConstraintMatrix basis hbasis
            (pochhammerMultipointInitialMomentMatrix
              beta a r P A W T S) Q hQint‖) ^
          ((((A * W * T * S ^ Fintype.card iota) * Fintype.card ι : ℕ) : ℝ) /
            (((Fintype.card κ * P : ℕ) : ℝ) -
              ((A * W * T * S ^ Fintype.card iota) * Fintype.card ι : ℕ))))) ∧
      ‖traceConstraintMatrix basis hbasis
          (pochhammerMultipointInitialMomentMatrix
            beta a r P A W T S) Q hQint‖ ≤
        (Module.finrank ℚ F : ℝ) *
          (Real.exp Hentry ^
            ((A * W * T * S ^ Fintype.card iota) *
              (Fintype.card κ * P))) *
          Real.exp Hentry * M := by
  dsimp only
  let rows := PochhammerMultipointInitialMomentIndex iota A W T S
  let cols := κ × Fin P
  let matrix : Matrix rows cols F :=
    pochhammerMultipointInitialMomentMatrix beta a r P A W T S
  have hrowsCard : Fintype.card rows =
      A * W * T * S ^ Fintype.card iota := by
    simp [rows, PochhammerMultipointInitialMomentIndex,
      RectangularMomentIndex, Nat.mul_assoc]
  have hcolsCard : Fintype.card cols = Fintype.card κ * P := by
    simp [cols]
  let Hentry : ℝ :=
      (Module.finrank ℚ F : ℝ) *
          Real.log ((W.factorial * (A + P) ^ P : ℕ) : ℝ) +
        (A : ℝ) * H +
        ((T + Fintype.card iota * S : ℕ) : ℝ) *
          ((Module.finrank ℚ F : ℝ) * Real.log V)
  have hheight : ∀ row xm, Height.logHeight₁ (matrix row xm) ≤ Hentry := by
    exact logHeight₁_pochhammerMultipointInitialMomentMatrix_le
      beta a r P A W T S hA hW hP hV hbeta ha hr
  have : Nonempty rows := Fintype.card_pos_iff.mp <| by
    rw [hrowsCard]
    positivity
  have hcard' : Fintype.card rows * Fintype.card ι <
      Fintype.card cols := by
    simpa [hrowsCard, hcolsCard] using hcard
  obtain ⟨Q, hQ0, hQint, cflat, hQ, hc0, hker, hc, hnorm⟩ :=
    exists_bounded_nonzero_integer_kernel_numberField
      basis hbasis matrix hM0 hheight hM hcard'
  let c : κ → Fin P → ℤ := fun x p ↦ cflat (x, p)
  have hc0' : c ≠ 0 := by
    intro hz
    apply hc0
    funext xp
    exact congrFun (congrFun hz xp.1) xp.2
  have hmom :=
    (pochhammerMultipointInitialMomentMatrix_kernel_iff
      beta a r P A W T S c).mp (by simpa [matrix, c] using hker)
  refine ⟨Q, hQ0, hQint, c, ?_, hc0', hmom, ?_, ?_⟩
  · simpa [Hentry, hrowsCard, hcolsCard] using hQ
  · intro x p
    simpa [c, hrowsCard, hcolsCard] using hc (x, p)
  · simpa [matrix, Hentry, hrowsCard, hcolsCard] using hnorm


noncomputable def numberFieldKernelCoefficientMajorant
    (rows cols d : ℕ) (H M : ℝ) : ℕ :=
  max 1 (Nat.ceil
    (((cols : ℝ) *
        max 1 ((d : ℝ) * (Real.exp H ^ (rows * cols)) *
          Real.exp H * M)) ^
      (((rows * d : ℕ) : ℝ) /
        ((cols : ℝ) - ((rows * d : ℕ) : ℝ)))))

lemma one_le_numberFieldKernelCoefficientMajorant
    (rows cols d : ℕ) (H M : ℝ) :
    1 ≤ numberFieldKernelCoefficientMajorant rows cols d H M :=
  le_max_left _ _

theorem exists_pochhammerMultipoint_coefficients_with_majorant
    {F κ iota ι : Type*} [Field F] [NumberField F]
    [Fintype κ] [Fintype iota] [DecidableEq iota] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (beta : κ → F) (a : κ → ℤ) (r : κ → iota → ℤ)
    (P A W T S : ℕ) {H V M : ℝ}
    (hP : 0 < P) (hA : 0 < A) (hW : 0 < W)
    (hT : 0 < T) (hS : 0 < S)
    (hV : 1 ≤ V) (hM0 : 0 ≤ M)
    (hbeta : ∀ x, Height.logHeight₁ (beta x) ≤ H)
    (ha : ∀ x, ‖a x‖ ≤ V) (hr : ∀ x i, ‖r x i‖ ≤ V)
    (hM : ∀ i (φ : F →ₐ[ℚ] ℂ), ‖φ (basis i)‖ ≤ M)
    (hcard :
      (A * W * T * S ^ Fintype.card iota) * Fintype.card ι <
        Fintype.card κ * P) :
    let rows := A * W * T * S ^ Fintype.card iota
    let cols := Fintype.card κ * P
    let Hentry : ℝ :=
      (Module.finrank ℚ F : ℝ) *
          Real.log ((W.factorial * (A + P) ^ P : ℕ) : ℝ) +
        (A : ℝ) * H +
        ((T + Fintype.card iota * S : ℕ) : ℝ) *
          ((Module.finrank ℚ F : ℝ) * Real.log V)
    ∃ c : κ → Fin P → ℤ, c ≠ 0 ∧
      (∀ node : Fin A, ∀ v : Fin W, ∀ q : Fin T,
        ∀ u : iota → Fin S,
          pochhammerMultipointMomentValue beta a r P c node v q
            (fun i ↦ u i) = 0) ∧
      ∀ x p, (c x p).natAbs ≤
        numberFieldKernelCoefficientMajorant
          rows cols (Fintype.card ι) Hentry M := by
  dsimp only
  let rows := A * W * T * S ^ Fintype.card iota
  let cols := Fintype.card κ * P
  let Hentry : ℝ :=
      (Module.finrank ℚ F : ℝ) *
          Real.log ((W.factorial * (A + P) ^ P : ℕ) : ℝ) +
        (A : ℝ) * H +
        ((T + Fintype.card iota * S : ℕ) : ℝ) *
          ((Module.finrank ℚ F : ℝ) * Real.log V)
  obtain ⟨Q, hQ0, hQint, c, hQ, hc0, hmom, hc, hnorm⟩ :=
    exists_bounded_nonzero_pochhammerMultipoint_coefficients_numberField
      basis hbasis beta a r P A W T S hP hA hW hT hS hV hM0
      hbeta ha hr hM hcard
  refine ⟨c, hc0, hmom, fun x p ↦ (hc x p).trans ?_⟩
  unfold numberFieldKernelCoefficientMajorant
  apply le_max_of_le_right
  apply Nat.ceil_mono
  apply Real.rpow_le_rpow
  · positivity
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply max_le_max_left
    have hd : Fintype.card ι = Module.finrank ℚ F := by
      rw [← Module.finrank_eq_card_basis basis]
    simpa [rows, cols, Hentry, hd] using hnorm
  · have hden : (0 : ℝ) < (Fintype.card κ * P : ℕ) -
        ((A * W * T * S ^ Fintype.card iota) * Fintype.card ι : ℕ) := by
      exact sub_pos.mpr (by exact_mod_cast hcard)
    positivity


noncomputable def boxPochhammerMultipointCoefficientMajorant
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (M : ℝ)
    (r B K P A W T S : ℕ) (alpha : Fin (r + 1) → F) : ℕ :=
  let rows := A * W * T * S ^ r
  let cols := K ^ (r + 1) * P
  let Hbox := (K : ℝ) * ∑ i, Height.logHeight₁ (alpha i)
  let V := boxMomentCoordinateBound B K
  let Hentry :=
    (Module.finrank ℚ F : ℝ) *
        Real.log ((W.factorial * (A + P) ^ P : ℕ) : ℝ) +
      (A : ℝ) * Hbox +
      ((T + r * S : ℕ) : ℝ) *
        ((Module.finrank ℚ F : ℝ) * Real.log (V : ℝ))
  numberFieldKernelCoefficientMajorant
    rows cols (Fintype.card ι) Hentry M

lemma one_le_boxPochhammerMultipointCoefficientMajorant
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (M : ℝ)
    (r B K P A W T S : ℕ) (alpha : Fin (r + 1) → F) :
    1 ≤ boxPochhammerMultipointCoefficientMajorant
      basis M r B K P A W T S alpha :=
  one_le_numberFieldKernelCoefficientMajorant _ _ _ _ _

theorem exists_box_pochhammerMultipoint_coefficients_with_majorant
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    {r B K P A W T S : ℕ} (alpha : Fin (r + 1) → F)
    (b : Fin (r + 1) → ℤ) (M : ℝ)
    (hK : 0 < K) (hP : 0 < P) (hA : 0 < A)
    (hW : 0 < W) (hT : 0 < T) (hS : 0 < S)
    (hb : ∀ i, (b i).natAbs ≤ B) (hM0 : 0 ≤ M)
    (hM : ∀ i (φ : F →ₐ[ℚ] ℂ), ‖φ (basis i)‖ ≤ M)
    (hcard : (A * W * T * S ^ r) * Fintype.card ι <
      K ^ (r + 1) * P) :
    ∃ c : ExponentBox (r + 1) K → Fin P → ℤ, c ≠ 0 ∧
      (∀ node : Fin A, ∀ v : Fin W, ∀ q : Fin T,
        ∀ u : Fin r → Fin S,
          pochhammerMultipointMomentValue (boxMonomial alpha)
            boxDistinguishedExponent (boxTransformedExponent b) P c
            node v q (fun i ↦ u i) = 0) ∧
      ∀ x p, (c x p).natAbs ≤
        boxPochhammerMultipointCoefficientMajorant
          basis M r B K P A W T S alpha := by
  let Hbox : ℝ := (K : ℝ) * ∑ i, Height.logHeight₁ (alpha i)
  let V := boxMomentCoordinateBound B K
  simpa [boxPochhammerMultipointCoefficientMajorant, Hbox, V,
    ExponentBox] using
    (exists_pochhammerMultipoint_coefficients_with_majorant
      basis hbasis (boxMonomial alpha) boxDistinguishedExponent
      (boxTransformedExponent b) P A W T S hP hA hW hT hS
      (V := (V : ℝ)) (H := Hbox) (M := M)
      (by exact_mod_cast one_le_boxMomentCoordinateBound hK) hM0
      (fun x ↦ logHeight₁_boxMonomial_le alpha x)
      (fun x ↦ (boxDistinguishedExponent_norm_le x).trans (by
        exact_mod_cast le_max_left K (2 * B * K)))
      (fun x i ↦ (boxTransformedExponent_norm_le b hb x i).trans (by
        exact_mod_cast le_max_right K (2 * B * K)))
      hM (by simpa [ExponentBox] using hcard))

theorem no_small_distinguished_linear_form_of_algebraic_initial_schedule
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (φ : F →+* ℂ) {r B K P Ainit Wsrc Tsrc Ssrc : ℕ}
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ)
    (b : Fin (r + 1) → ℤ) (M : ℝ)
    (A W T S k Q : ℕ → ℕ) (R Z : ℕ → ℝ) (m : ℕ)
    (hK : 0 < K) (hP : 0 < P) (hAinit : 0 < Ainit)
    (hWsrc : 0 < Wsrc) (hTsrc : 0 < Tsrc) (hSsrc : 0 < Ssrc)
    (hM0 : 0 ≤ M) (hM : ∀ i (ψ : F →ₐ[ℚ] ℂ), ‖ψ (basis i)‖ ≤ M)
    (hcard : (Ainit * Wsrc * Tsrc * Ssrc ^ r) * Fintype.card ι <
      K ^ (r + 1) * P)
    (hb : ∀ i, (b i).natAbs ≤ B) (hb0 : b 0 ≠ 0)
    (halpha : ∀ i, alpha i ≠ 0)
    (hinj : Function.Injective
      (fun x : ExponentBox (r + 1) K ↦ boxMonomial alpha x))
    (hexp : ∀ x : ExponentBox (r + 1) K,
      Complex.exp (boxLinearForm ell x) = φ (boxMonomial alpha x))
    (hLambda : ‖∑ i, (b i : ℂ) * ell i‖ ≤ 1)
    (hA0 : A 0 = Ainit) (hW0 : W 0 = Wsrc)
    (hT0 : T 0 = Tsrc) (hS0 : S 0 = Ssrc)
    (hA : ∀ j, j < m → 0 < A j) (hk : ∀ j, j < m → 0 < k j)
    (hstepW : ∀ j, j < m → W (j + 1) + k j ≤ W j)
    (hstepT : ∀ j, j < m → T (j + 1) + Q j ≤ T j)
    (hstepS : ∀ j, j < m → S (j + 1) + k j ≤ S j)
    (hstepAR : ∀ j, j < m → (A j : ℝ) < R j)
    (hstepA'Z : ∀ j, j < m → (A (j + 1) : ℝ) ≤ Z j)
    (hstepZR : ∀ j, j < m → Z j ≤ R j)
    (hstepSmall : ∀ j, j < m → ∀ h < A (j + 1),
      ∀ v < W (j + 1), ∀ q < T (j + 1), ∀ u : Fin r → ℕ,
      (∀ i, u i < S (j + 1)) →
      pochhammerWeightedApproximationBound (K ^ (r + 1)) P
          (A j) (k j) (Q j) v q (∑ i, u i)
          (boxPochhammerMultipointCoefficientMajorant
            basis M r B K P Ainit Wsrc Tsrc Ssrc alpha : ℝ)
          (boxAnalyticCoordinateBound B K ell : ℝ)
          ((K : ℝ) * ∑ i, ‖ell i‖) (R j) (Z j)
          ‖∑ i, (b i : ℂ) * ell i‖ <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ (r + 1) + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (P * boxPochhammerMultipointCoefficientMajorant
                  basis M r B K P Ainit Wsrc Tsrc Ssrc alpha *
                (v.factorial * (h + 1 + P) ^ P) *
                (boxAnalyticCoordinateBound B K ell) ^
                  (q + ∑ i, u i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i)))))
    (hfinalA : K ^ (r + 1) * P ≤ A m)
    (hfinalW : 0 < W m) (hfinalT : 0 < T m) (hfinalS : 0 < S m) :
    False := by
  obtain ⟨c, hc0, hmoment, hc⟩ :=
    exists_box_pochhammerMultipoint_coefficients_with_majorant
      basis hbasis alpha b M hK hP hAinit hWsrc hTsrc hSsrc hb hM0 hM hcard
  let C := boxPochhammerMultipointCoefficientMajorant
    basis M r B K P Ainit Wsrc Tsrc Ssrc alpha
  let V := boxAnalyticCoordinateBound B K ell
  have hCone : 1 ≤ C :=
    one_le_boxPochhammerMultipointCoefficientMajorant
      basis M r B K P Ainit Wsrc Tsrc Ssrc alpha
  have hVone : 1 ≤ V := one_le_boxAnalyticCoordinateBound ell
  have haV : ∀ x : ExponentBox (r + 1) K,
      ‖boxDistinguishedExponent x‖ ≤ (V : ℝ) := by
    intro x
    refine (boxDistinguishedExponent_norm_le x).trans ?_
    exact_mod_cast (le_max_left K (2 * B * K)).trans
      (boxMomentCoordinateBound_le_boxAnalyticCoordinateBound ell)
  have hrV : ∀ x : ExponentBox (r + 1) K, ∀ i : Fin r,
      ‖boxTransformedExponent b x i‖ ≤ (V : ℝ) := by
    intro x i
    refine (boxTransformedExponent_norm_le b hb x i).trans ?_
    exact_mod_cast (le_max_right K (2 * B * K)).trans
      (boxMomentCoordinateBound_le_boxAnalyticCoordinateBound ell)
  apply no_small_box_linear_form_of_pochhammer_iterated_approximate_moments
    φ alpha c (fun x ↦ boxLinearForm ell x)
      (b 0 : ℂ) (∑ i, (b i : ℂ) * ell i)
      boxDistinguishedExponent (boxTransformedExponent b)
      (fun i : Fin r ↦ ell i.succ)
      A W T S k Q R Z m (C := C) (V := V)
      (U := (K : ℝ) * ∑ i, ‖ell i‖)
  · exact hK
  · exact hP
  · exact hA
  · exact hk
  · rw [Complex.norm_intCast, ← Int.cast_abs, ← Nat.cast_natAbs]
    exact_mod_cast Int.natAbs_pos.mpr hb0
  · exact hLambda
  · exact hCone
  · exact hVone
  · positivity
  · exact hc0
  · exact hinj
  · exact fun x ↦ boxMonomial_ne_zero alpha halpha x
  · exact hc
  · exact haV
  · exact hrV
  · exact fun x ↦ boxTransformedLinearForm_norm_le_analyticBound ell b hb x
  · exact fun x ↦ boxLinearForm_norm_le ell x
  · exact hexp
  · exact fun x ↦ box_distinguished_linearForm_identity ell b x
  · rw [hA0, hW0, hT0, hS0]
    exact hmoment
  · exact hstepW
  · exact hstepT
  · exact hstepS
  · exact hstepAR
  · exact hstepA'Z
  · exact hstepZR
  · simpa [C, V] using hstepSmall
  · exact hfinalA
  · exact hfinalW
  · exact hfinalT
  · exact hfinalS


def scaledDyadicStageA (Ainit j : ℕ) : ℕ := Ainit * 2 ^ j

lemma scaledDyadicStageA_pos {Ainit : ℕ} (hAinit : 0 < Ainit) (j : ℕ) :
    0 < scaledDyadicStageA Ainit j := by
  simp [scaledDyadicStageA, hAinit]

lemma le_scaledDyadicStageA_stageCount {Ainit N : ℕ}
    (hAinit : 0 < Ainit) :
    N ≤ scaledDyadicStageA Ainit (dyadicStageCount N) := by
  refine (le_dyadicStageA_stageCount N).trans ?_
  unfold scaledDyadicStageA dyadicStageA
  exact Nat.le_mul_of_pos_left _ hAinit

theorem no_small_distinguished_linear_form_of_scaled_dyadic_schedule
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (φ : F →+* ℂ) {r B K P Ainit spend : ℕ}
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ)
    (b : Fin (r + 1) → ℤ) (M D : ℝ)
    (hK : 0 < K) (hP : 0 < P) (hAinit : 0 < Ainit)
    (hspend : 0 < spend) (hM0 : 0 ≤ M)
    (hM : ∀ i (ψ : F →ₐ[ℚ] ℂ), ‖ψ (basis i)‖ ≤ M)
    (hD : 1 ≤ D)
    (hcard :
      (Ainit *
        (dyadicStageCount (K ^ (r + 1) * P) * spend + 1) *
        (dyadicStageCount (K ^ (r + 1) * P) + 1) *
        (dyadicStageCount (K ^ (r + 1) * P) * spend + 1) ^ r) *
          Fintype.card ι < K ^ (r + 1) * P)
    (hb : ∀ i, (b i).natAbs ≤ B) (hb0 : b 0 ≠ 0)
    (halpha : ∀ i, alpha i ≠ 0)
    (hinj : Function.Injective
      (fun x : ExponentBox (r + 1) K ↦ boxMonomial alpha x))
    (hexp : ∀ x : ExponentBox (r + 1) K,
      Complex.exp (boxLinearForm ell x) = φ (boxMonomial alpha x))
    (hLambda : ‖∑ i, (b i : ℂ) * ell i‖ ≤ 1)
    (hsmall :
      let m := dyadicStageCount (K ^ (r + 1) * P)
      ∀ j, j < m → ∀ h < scaledDyadicStageA Ainit (j + 1),
        ∀ v < stageSpendBudget m spend (j + 1),
        ∀ q < stageUnitBudget m (j + 1),
        ∀ u : Fin r → ℕ,
        (∀ i, u i < stageSpendBudget m spend (j + 1)) →
        pochhammerWeightedApproximationBound (K ^ (r + 1)) P
            (scaledDyadicStageA Ainit j) spend 1 v q (∑ i, u i)
            (boxPochhammerMultipointCoefficientMajorant basis M r B K P
              Ainit (m * spend + 1) (m + 1) (m * spend + 1) alpha : ℝ)
            (boxAnalyticCoordinateBound B K ell : ℝ)
            ((K : ℝ) * ∑ i, ‖ell i‖)
            (D * (scaledDyadicStageA Ainit (j + 1) : ℝ))
            (scaledDyadicStageA Ainit (j + 1) : ℝ)
            ‖∑ i, (b i : ℂ) * ell i‖ <
          Real.exp (-((Module.finrank ℚ F : ℝ) *
                Real.log (K ^ (r + 1) + 1 : ℕ) +
              (Module.finrank ℚ F : ℝ) *
                Real.log (P * boxPochhammerMultipointCoefficientMajorant
                    basis M r B K P Ainit
                      (m * spend + 1) (m + 1) (m * spend + 1) alpha *
                  (v.factorial * (h + 1 + P) ^ P) *
                  (boxAnalyticCoordinateBound B K ell) ^
                    (q + ∑ i, u i) : ℕ) +
              (h : ℝ) * ((K : ℝ) *
                ∑ i, Height.logHeight₁ (alpha i))))) :
    False := by
  let N := K ^ (r + 1) * P
  let m := dyadicStageCount N
  let A : ℕ → ℕ := scaledDyadicStageA Ainit
  let W : ℕ → ℕ := stageSpendBudget m spend
  let T : ℕ → ℕ := stageUnitBudget m
  let S : ℕ → ℕ := stageSpendBudget m spend
  let k : ℕ → ℕ := fun _ ↦ spend
  let Q : ℕ → ℕ := fun _ ↦ 1
  let R : ℕ → ℝ := fun j ↦ D * (A (j + 1) : ℝ)
  let Z : ℕ → ℝ := fun j ↦ (A (j + 1) : ℝ)
  apply no_small_distinguished_linear_form_of_algebraic_initial_schedule
    basis hbasis φ alpha ell b M A W T S k Q R Z m
      (Ainit := Ainit) (Wsrc := m * spend + 1)
      (Tsrc := m + 1) (Ssrc := m * spend + 1)
  · exact hK
  · exact hP
  · exact hAinit
  · positivity
  · positivity
  · positivity
  · exact hM0
  · exact hM
  · simpa [N, m, Nat.mul_assoc] using hcard
  · exact hb
  · exact hb0
  · exact halpha
  · exact hinj
  · exact hexp
  · exact hLambda
  · simp [A, scaledDyadicStageA]
  · simp [W, stageSpendBudget]
  · simp [T, stageUnitBudget]
  · simp [S, stageSpendBudget]
  · intro j hj
    exact scaledDyadicStageA_pos hAinit j
  · intro j hj
    simpa [k] using hspend
  · intro j hj
    exact (stageSpendBudget_step hj).le
  · intro j hj
    exact (stageUnitBudget_step hj).le
  · intro j hj
    exact (stageSpendBudget_step hj).le
  · intro j hj
    dsimp [A, R, scaledDyadicStageA]
    have hpow : (0 : ℝ) < ((Ainit * 2 ^ j : ℕ) : ℝ) := by positivity
    calc
      ((Ainit * 2 ^ j : ℕ) : ℝ) <
          2 * ((Ainit * 2 ^ j : ℕ) : ℝ) := by nlinarith
      _ ≤ D * (2 * ((Ainit * 2 ^ j : ℕ) : ℝ)) := by
        have hm := mul_le_mul_of_nonneg_right hD
          (show 0 ≤ 2 * ((Ainit * 2 ^ j : ℕ) : ℝ) by positivity)
        simpa using hm
      _ = D * ((Ainit * 2 ^ (j + 1) : ℕ) : ℝ) := by
        rw [pow_succ]
        push_cast
        ring
  · intro j hj
    simp [A, Z, scaledDyadicStageA]
  · intro j hj
    dsimp [R, Z]
    exact le_mul_of_one_le_left (by positivity) hD
  · dsimp [N, m, A, W, T, S, k, Q, R, Z] at hsmall ⊢
    exact hsmall
  · dsimp [N, A, m]
    exact le_scaledDyadicStageA_stageCount hAinit
  · simp [W, stageSpendBudget]
  · simp [T, stageUnitBudget]
  · simp [S, stageSpendBudget]


theorem exists_positive_lower_bound_of_scaled_dyadic_boundary
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (φ : F →+* ℂ) {r B K P Ainit spend : ℕ}
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ)
    (b : Fin (r + 1) → ℤ) (M D : ℝ)
    (hK : 0 < K) (hP : 0 < P) (hAinit : 0 < Ainit)
    (hspend : 0 < spend) (hM0 : 0 ≤ M)
    (hM : ∀ i (ψ : F →ₐ[ℚ] ℂ), ‖ψ (basis i)‖ ≤ M)
    (hD : 1 ≤ D)
    (hcard :
      (Ainit *
        (dyadicStageCount (K ^ (r + 1) * P) * spend + 1) *
        (dyadicStageCount (K ^ (r + 1) * P) + 1) *
        (dyadicStageCount (K ^ (r + 1) * P) * spend + 1) ^ r) *
          Fintype.card ι < K ^ (r + 1) * P)
    (hb : ∀ i, (b i).natAbs ≤ B) (hb0 : b 0 ≠ 0)
    (halpha : ∀ i, alpha i ≠ 0)
    (hinj : Function.Injective
      (fun x : ExponentBox (r + 1) K ↦ boxMonomial alpha x))
    (hexp : ∀ x : ExponentBox (r + 1) K,
      Complex.exp (boxLinearForm ell x) = φ (boxMonomial alpha x))
    (hboundary :
      let m := dyadicStageCount (K ^ (r + 1) * P)
      ∀ j, j < m → ∀ h < scaledDyadicStageA Ainit (j + 1),
        ∀ v < stageSpendBudget m spend (j + 1),
        ∀ q < stageUnitBudget m (j + 1),
        ∀ u : Fin r → ℕ,
        (∀ i, u i < stageSpendBudget m spend (j + 1)) →
        pochhammerWeightedApproximationBound (K ^ (r + 1)) P
            (scaledDyadicStageA Ainit j) spend 1 v q (∑ i, u i)
            (boxPochhammerMultipointCoefficientMajorant basis M r B K P
              Ainit (m * spend + 1) (m + 1) (m * spend + 1) alpha : ℝ)
            (boxAnalyticCoordinateBound B K ell : ℝ)
            ((K : ℝ) * ∑ i, ‖ell i‖)
            (D * (scaledDyadicStageA Ainit (j + 1) : ℝ))
            (scaledDyadicStageA Ainit (j + 1) : ℝ) 0 <
          Real.exp (-((Module.finrank ℚ F : ℝ) *
                Real.log (K ^ (r + 1) + 1 : ℕ) +
              (Module.finrank ℚ F : ℝ) *
                Real.log (P * boxPochhammerMultipointCoefficientMajorant
                    basis M r B K P Ainit
                      (m * spend + 1) (m + 1) (m * spend + 1) alpha *
                  (v.factorial * (h + 1 + P) ^ P) *
                  (boxAnalyticCoordinateBound B K ell) ^
                    (q + ∑ i, u i) : ℕ) +
              (h : ℝ) * ((K : ℝ) *
                ∑ i, Height.logHeight₁ (alpha i))))) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ ‖∑ i, (b i : ℂ) * ell i‖ := by
  let Nbox := K ^ (r + 1)
  let N := Nbox * P
  let m := dyadicStageCount N
  let A : ℕ → ℕ := scaledDyadicStageA Ainit
  let W : ℕ → ℕ := stageSpendBudget m spend
  let T : ℕ → ℕ := stageUnitBudget m
  let S : ℕ → ℕ := stageSpendBudget m spend
  let k : ℕ → ℕ := fun _ ↦ spend
  let Q : ℕ → ℕ := fun _ ↦ 1
  let C : ℝ := boxPochhammerMultipointCoefficientMajorant basis M r B K P
    Ainit (m * spend + 1) (m + 1) (m * spend + 1) alpha
  let V : ℝ := boxAnalyticCoordinateBound B K ell
  let U : ℝ := (K : ℝ) * ∑ i, ‖ell i‖
  let R : ℕ → ℝ := fun j ↦ D * (A (j + 1) : ℝ)
  let Z : ℕ → ℝ := fun j ↦ (A (j + 1) : ℝ)
  let target : (j : ℕ) → ℕ → ℕ → ℕ → (Fin r → ℕ) → ℝ :=
    fun j h v q u ↦
      Real.exp (-((Module.finrank ℚ F : ℝ) *
            Real.log (K ^ (r + 1) + 1 : ℕ) +
          (Module.finrank ℚ F : ℝ) *
            Real.log (P * boxPochhammerMultipointCoefficientMajorant
                basis M r B K P Ainit
                  (m * spend + 1) (m + 1) (m * spend + 1) alpha *
              (v.factorial * (h + 1 + P) ^ P) *
              (boxAnalyticCoordinateBound B K ell) ^
                (q + ∑ i, u i) : ℕ) +
          (h : ℝ) * ((K : ℝ) *
            ∑ i, Height.logHeight₁ (alpha i))))
  have hboundary' : ∀ j, j < m → ∀ h < A (j + 1),
      ∀ v < W (j + 1), ∀ q < T (j + 1), ∀ u : Fin r → ℕ,
      (∀ i, u i < S (j + 1)) →
      pochhammerWeightedApproximationBound Nbox P (A j) (k j) (Q j)
          v q (∑ i, u i) C V U (R j) (Z j) 0 < target j h v q u := by
    dsimp [Nbox, N, m, A, W, T, S, k, Q, C, V, U, R, Z, target]
    simpa using hboundary
  obtain ⟨ε, hε, hεsmall⟩ :=
    exists_uniform_lambda_radius_of_boundary_small
      Nbox P A W T S k Q C V U R Z m target hboundary'
  let ε' := min ε 1
  have hε' : 0 < ε' := lt_min hε zero_lt_one
  refine ⟨ε', hε', ?_⟩
  by_contra hnot
  have hnormlt : ‖∑ i, (b i : ℂ) * ell i‖ < ε' := lt_of_not_ge hnot
  have hsmallAbs :
      |(‖∑ i, (b i : ℂ) * ell i‖ : ℝ)| < ε := by
    rw [abs_of_nonneg (norm_nonneg _)]
    exact hnormlt.trans_le (min_le_left _ _)
  have hsmall' := hεsmall _ hsmallAbs
  apply no_small_distinguished_linear_form_of_scaled_dyadic_schedule
    basis hbasis φ alpha ell b M D hK hP hAinit hspend hM0 hM hD
      hcard hb hb0 halpha hinj hexp
  · exact hnormlt.le.trans (min_le_right _ _)
  · dsimp [Nbox, N, m, A, W, T, S, k, Q, C, V, U, R, Z, target] at hsmall'
    simpa using hsmall'


attribute [local instance] Matrix.seminormedAddCommGroup

noncomputable def rowTraceConstraintMatrix
    {K rows cols ι : Type*} [Field K] [NumberField K] [Fintype cols]
    (b : Module.Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i))
    (A : Matrix rows cols K) (Q : rows → ℕ)
    (hQA : ∀ r j, IsIntegral ℤ ((Q r : K) * A r j)) :
    Matrix (rows × ι) cols ℤ :=
  fun ri j ↦ Algebra.trace ℤ (NumberField.RingOfIntegers K)
    (⟨(Q ri.1 : K) * A ri.1 j, hQA ri.1 j⟩ * ⟨b ri.2, hb ri.2⟩)

lemma rowTraceConstraintMatrix_kernel
    {K rows cols ι : Type*} [Field K] [NumberField K]
    [Fintype cols] [Fintype ι]
    (b : Module.Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i))
    (A : Matrix rows cols K) (Q : rows → ℕ) (hQ : ∀ r, Q r ≠ 0)
    (hQA : ∀ r j, IsIntegral ℤ ((Q r : K) * A r j))
    (c : cols → ℤ)
    (hc : (rowTraceConstraintMatrix b hb A Q hQA).mulVec c = 0) :
    A.mulVec (fun j ↦ (c j : K)) = 0 := by
  funext r
  let y : K := ∑ j, (c j : K) * A r j
  have htrace : ∀ i, Algebra.trace ℚ K ((Q r : K) * y * b i) = 0 := by
    intro i
    have hi := congrFun hc (r, i)
    change ∑ j, rowTraceConstraintMatrix b hb A Q hQA (r, i) j * c j = 0 at hi
    have hiQ := congrArg (fun z : ℤ ↦ (z : ℚ)) hi
    rw [Int.cast_sum] at hiQ
    simp only [Int.cast_mul, Int.cast_zero] at hiQ
    have hterm : ∀ j,
        ((rowTraceConstraintMatrix b hb A Q hQA (r, i) j : ℤ) : ℚ) =
          Algebra.trace ℚ K (((Q r : K) * A r j) * b i) := by
      intro j
      exact Algebra.coe_trace_int
        (⟨(Q r : K) * A r j, hQA r j⟩ * ⟨b i, hb i⟩)
    simp_rw [hterm] at hiQ
    have heq : (Q r : K) * y * b i =
        ∑ j, (c j : ℚ) • (((Q r : K) * A r j) * b i) := by
      dsimp [y]
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Algebra.smul_def]
      norm_num
      ring
    rw [heq, map_sum]
    simpa [map_smul, mul_comm] using hiQ
  have hzero : (Q r : K) * y = 0 := by
    apply (traceForm_nondegenerate ℚ K).1
    intro z
    rw [← b.sum_repr z]
    simp only [map_sum, Algebra.traceForm_apply, Algebra.smul_def, mul_assoc]
    apply Finset.sum_eq_zero
    intro i hi
    have heq : (Q r : K) *
        (y * ((algebraMap ℚ K) ((b.repr z) i) * b i)) =
        ((b.repr z) i) • ((Q r : K) * y * b i) := by
      simp only [Algebra.smul_def]
      ring
    rw [heq, map_smul]
    simp [htrace i]
  have hy : y = 0 := by
    exact (mul_eq_zero.mp hzero).resolve_left (Nat.cast_ne_zero.mpr (hQ r))
  simpa [Matrix.mulVec, dotProduct, mul_comm, y] using hy

lemma rowTraceConstraintMatrix_norm_le
    {K rows cols ι : Type*} [Field K] [NumberField K]
    [Fintype rows] [Fintype cols] [Fintype ι]
    (b : Module.Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i))
    (A : Matrix rows cols K) (Q : rows → ℕ)
    (hQA : ∀ r j, IsIntegral ℤ ((Q r : K) * A r j))
    {H M Scale : ℝ} (hScale : 0 ≤ Scale) (hM0 : 0 ≤ M)
    (hH : ∀ r j, Height.logHeight₁ (A r j) ≤ H)
    (hM : ∀ i (φ : K →ₐ[ℚ] ℂ), ‖φ (b i)‖ ≤ M)
    (hQ : ∀ r, (Q r : ℝ) ≤ Scale) :
    ‖rowTraceConstraintMatrix b hb A Q hQA‖ ≤
      (Module.finrank ℚ K : ℝ) * Scale * Real.exp H * M := by
  have hRHS : 0 ≤ (Module.finrank ℚ K : ℝ) * Scale * Real.exp H * M :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hScale)
      (Real.exp_pos H).le) hM0
  rw [Matrix.norm_le_iff hRHS]
  intro ri j
  let u : NumberField.RingOfIntegers K :=
    ⟨(Q ri.1 : K) * A ri.1 j, hQA ri.1 j⟩
  let v : NumberField.RingOfIntegers K := ⟨b ri.2, hb ri.2⟩
  have htrace :
      ((Algebra.trace ℤ (NumberField.RingOfIntegers K) (u * v) : ℤ) : ℂ) =
        ∑ φ : K →ₐ[ℚ] ℂ, φ (((u * v : NumberField.RingOfIntegers K) : K)) := by
    calc
      ((Algebra.trace ℤ (NumberField.RingOfIntegers K) (u * v) : ℤ) : ℂ) =
          algebraMap ℚ ℂ
            ((Algebra.trace ℤ (NumberField.RingOfIntegers K) (u * v) : ℤ) : ℚ) := by
        norm_num
      _ = algebraMap ℚ ℂ
          (Algebra.trace ℚ K (((u * v : NumberField.RingOfIntegers K) : K))) := by
        rw [Algebra.coe_trace_int]
      _ = ∑ φ : K →ₐ[ℚ] ℂ,
          φ (((u * v : NumberField.RingOfIntegers K) : K)) :=
        trace_eq_sum_embeddings ℂ
  have hAemb : ∀ φ : K →ₐ[ℚ] ℂ, ‖φ (A ri.1 j)‖ ≤ Real.exp H := by
    intro φ
    by_cases hz : A ri.1 j = 0
    · simp [hz, (Real.exp_pos H).le]
    · have hp : 0 < ‖φ (A ri.1 j)‖ := norm_pos_iff.mpr
          ((map_ne_zero_iff φ.toRingHom φ.injective).mpr hz)
      calc
        ‖φ (A ri.1 j)‖ = Real.exp (Real.log ‖φ (A ri.1 j)‖) := by
          rw [Real.exp_log hp]
        _ ≤ Real.exp H := Real.exp_le_exp.mpr
          ((numberField_log_norm_embedding_le_logHeight φ.toRingHom _).trans
            (hH ri.1 j))
  have hterm : ∀ φ : K →ₐ[ℚ] ℂ,
      ‖φ (((u * v : NumberField.RingOfIntegers K) : K))‖ ≤
        Scale * Real.exp H * M := by
    intro φ
    change ‖φ ((Q ri.1 : K) * A ri.1 j * b ri.2)‖ ≤ _
    rw [map_mul, map_mul, norm_mul, norm_mul]
    have hQnorm : ‖φ (Q ri.1 : K)‖ ≤ Scale := by simpa using hQ ri.1
    exact mul_le_mul
      (mul_le_mul hQnorm (hAemb φ) (by positivity) hScale)
      (hM ri.2 φ) (norm_nonneg _) (mul_nonneg hScale (Real.exp_pos H).le)
  change ‖Algebra.trace ℤ (NumberField.RingOfIntegers K) (u * v)‖ ≤ _
  have hcastNorm :
      ‖Algebra.trace ℤ (NumberField.RingOfIntegers K) (u * v)‖ =
        ‖((Algebra.trace ℤ (NumberField.RingOfIntegers K) (u * v) : ℤ) : ℂ)‖ := by
    norm_num [Int.norm_eq_abs]
  rw [hcastNorm, htrace]
  calc
    ‖∑ φ : K →ₐ[ℚ] ℂ, φ (((u * v : NumberField.RingOfIntegers K) : K))‖ ≤
        ∑ φ : K →ₐ[ℚ] ℂ,
          ‖φ (((u * v : NumberField.RingOfIntegers K) : K))‖ := norm_sum_le _ _
    _ ≤ ∑ _φ : K →ₐ[ℚ] ℂ, (Scale * Real.exp H * M) := by
      gcongr with φ hφ
      exact hterm φ
    _ = (Module.finrank ℚ K : ℝ) * Scale * Real.exp H * M := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, AlgHom.card ℚ K ℂ]
      ring

theorem exists_bounded_nonzero_integer_kernel_numberField_rowScaled
    {K rows cols ι : Type*} [Field K] [NumberField K]
    [Fintype rows] [Fintype cols] [Fintype ι] [Nonempty rows]
    (b : Module.Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i))
    (A : Matrix rows cols K) {H M : ℝ} (hM0 : 0 ≤ M)
    (hH : ∀ r j, Height.logHeight₁ (A r j) ≤ H)
    (hM : ∀ i (φ : K →ₐ[ℚ] ℂ), ‖φ (b i)‖ ≤ M)
    (hcard : Fintype.card rows * Fintype.card ι < Fintype.card cols) :
    ∃ (Q : rows → ℕ) (_hQ0 : ∀ r, Q r ≠ 0)
        (hQA : ∀ r j, IsIntegral ℤ ((Q r : K) * A r j))
        (c : cols → ℤ),
      (∀ r, (Q r : ℝ) ≤ Real.exp H ^ Fintype.card cols) ∧
      c ≠ 0 ∧ A.mulVec (fun j ↦ (c j : K)) = 0 ∧
      (∀ j, (c j).natAbs ≤ Nat.ceil
        (((Fintype.card cols : ℝ) *
            max 1 ‖rowTraceConstraintMatrix b hb A Q hQA‖) ^
          (((Fintype.card rows * Fintype.card ι : ℕ) : ℝ) /
            ((Fintype.card cols : ℝ) -
              (Fintype.card rows * Fintype.card ι : ℕ))))) ∧
      ‖rowTraceConstraintMatrix b hb A Q hQA‖ ≤
        (Module.finrank ℚ K : ℝ) *
          (Real.exp H ^ Fintype.card cols) * Real.exp H * M := by
  classical
  choose Q hQ0 hQbound hQA using fun r ↦
    exists_common_integral_scale (fun j ↦ A r j) (fun j ↦ hH r j)
  let T := rowTraceConstraintMatrix b hb A Q hQA
  have hcard' : Fintype.card (rows × ι) < Fintype.card cols := by
    simpa [Fintype.card_prod] using hcard
  let : Nonempty ι := Fintype.card_pos_iff.mp <| by
    rw [← Module.finrank_eq_card_basis b]
    exact Module.finrank_pos
  have hrows' : 0 < Fintype.card (rows × ι) := Fintype.card_pos
  obtain ⟨c, hc0, hkernel, hcbound⟩ :=
    exists_bounded_nonzero_integer_kernel T hcard' hrows'
  have hAker : A.mulVec (fun j ↦ (c j : K)) = 0 :=
    rowTraceConstraintMatrix_kernel b hb A Q hQ0 hQA c hkernel
  have hQbound' : ∀ r, (Q r : ℝ) ≤ Real.exp H ^ Fintype.card cols := by
    intro r
    simpa using hQbound r
  have hTnorm : ‖T‖ ≤ (Module.finrank ℚ K : ℝ) *
      (Real.exp H ^ Fintype.card cols) * Real.exp H * M := by
    apply rowTraceConstraintMatrix_norm_le b hb A Q hQA
      (by positivity) hM0 hH hM hQbound'
  refine ⟨Q, hQ0, hQA, c, hQbound', hc0, hAker, ?_, hTnorm⟩
  simpa [T, Fintype.card_prod] using hcbound


noncomputable def numberFieldRowKernelCoefficientMajorant
    (rows cols d : ℕ) (H M : ℝ) : ℕ :=
  max 1 (Nat.ceil
    (((cols : ℝ) *
        max 1 ((d : ℝ) * (Real.exp H ^ cols) * Real.exp H * M)) ^
      (((rows * d : ℕ) : ℝ) /
        ((cols : ℝ) - ((rows * d : ℕ) : ℝ)))))

lemma one_le_numberFieldRowKernelCoefficientMajorant
    (rows cols d : ℕ) (H M : ℝ) :
    1 ≤ numberFieldRowKernelCoefficientMajorant rows cols d H M :=
  le_max_left _ _

theorem exists_pochhammerMultipoint_coefficients_with_rowMajorant
    {F κ iota ι : Type*} [Field F] [NumberField F]
    [Fintype κ] [Fintype iota] [DecidableEq iota] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (beta : κ → F) (a : κ → ℤ) (r : κ → iota → ℤ)
    (P A W T S : ℕ) {H V M : ℝ}
    (hP : 0 < P) (hA : 0 < A) (hW : 0 < W)
    (hT : 0 < T) (hS : 0 < S)
    (hV : 1 ≤ V) (hM0 : 0 ≤ M)
    (hbeta : ∀ x, Height.logHeight₁ (beta x) ≤ H)
    (ha : ∀ x, ‖a x‖ ≤ V) (hr : ∀ x i, ‖r x i‖ ≤ V)
    (hM : ∀ i (φ : F →ₐ[ℚ] ℂ), ‖φ (basis i)‖ ≤ M)
    (hcard :
      (A * W * T * S ^ Fintype.card iota) * Fintype.card ι <
        Fintype.card κ * P) :
    let rows := A * W * T * S ^ Fintype.card iota
    let cols := Fintype.card κ * P
    let Hentry : ℝ :=
      (Module.finrank ℚ F : ℝ) *
          Real.log ((W.factorial * (A + P) ^ P : ℕ) : ℝ) +
        (A : ℝ) * H +
        ((T + Fintype.card iota * S : ℕ) : ℝ) *
          ((Module.finrank ℚ F : ℝ) * Real.log V)
    ∃ c : κ → Fin P → ℤ, c ≠ 0 ∧
      (∀ node : Fin A, ∀ v : Fin W, ∀ q : Fin T,
        ∀ u : iota → Fin S,
          pochhammerMultipointMomentValue beta a r P c node v q
            (fun i ↦ u i) = 0) ∧
      ∀ x p, (c x p).natAbs ≤
        numberFieldRowKernelCoefficientMajorant
          rows cols (Fintype.card ι) Hentry M := by
  dsimp only
  let rowsType := PochhammerMultipointInitialMomentIndex iota A W T S
  let colsType := κ × Fin P
  let matrix : Matrix rowsType colsType F :=
    pochhammerMultipointInitialMomentMatrix beta a r P A W T S
  have hrowsCard : Fintype.card rowsType =
      A * W * T * S ^ Fintype.card iota := by
    simp [rowsType, PochhammerMultipointInitialMomentIndex,
      RectangularMomentIndex, Nat.mul_assoc]
  have hcolsCard : Fintype.card colsType = Fintype.card κ * P := by
    simp [colsType]
  let Hentry : ℝ :=
      (Module.finrank ℚ F : ℝ) *
          Real.log ((W.factorial * (A + P) ^ P : ℕ) : ℝ) +
        (A : ℝ) * H +
        ((T + Fintype.card iota * S : ℕ) : ℝ) *
          ((Module.finrank ℚ F : ℝ) * Real.log V)
  have hheight : ∀ row xm, Height.logHeight₁ (matrix row xm) ≤ Hentry := by
    exact logHeight₁_pochhammerMultipointInitialMomentMatrix_le
      beta a r P A W T S hA hW hP hV hbeta ha hr
  have : Nonempty rowsType := Fintype.card_pos_iff.mp <| by
    rw [hrowsCard]
    positivity
  have hcard' : Fintype.card rowsType * Fintype.card ι <
      Fintype.card colsType := by
    simpa [hrowsCard, hcolsCard] using hcard
  obtain ⟨Q, hQ0, hQint, cflat, hQ, hc0, hker, hc, hnorm⟩ :=
    exists_bounded_nonzero_integer_kernel_numberField_rowScaled
      basis hbasis matrix hM0 hheight hM hcard'
  let c : κ → Fin P → ℤ := fun x p ↦ cflat (x, p)
  have hc0' : c ≠ 0 := by
    intro hz
    apply hc0
    funext xp
    exact congrFun (congrFun hz xp.1) xp.2
  have hmom :=
    (pochhammerMultipointInitialMomentMatrix_kernel_iff
      beta a r P A W T S c).mp (by simpa [matrix, c] using hker)
  refine ⟨c, hc0', hmom, fun x p ↦ (hc (x, p)).trans ?_⟩
  unfold numberFieldRowKernelCoefficientMajorant
  apply le_max_of_le_right
  apply Nat.ceil_mono
  rw [hrowsCard, hcolsCard]
  apply Real.rpow_le_rpow
  · positivity
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply max_le_max_left
    have hd : Fintype.card ι = Module.finrank ℚ F := by
      rw [← Module.finrank_eq_card_basis basis]
    simpa [Hentry, hcolsCard, hd] using hnorm
  · have hden : (0 : ℝ) < (Fintype.card κ * P : ℕ) -
        ((A * W * T * S ^ Fintype.card iota) * Fintype.card ι : ℕ) := by
      exact sub_pos.mpr (by exact_mod_cast hcard)
    positivity


noncomputable def boxPochhammerMultipointRowCoefficientMajorant
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (M : ℝ)
    (r B K P A W T S : ℕ) (alpha : Fin (r + 1) → F) : ℕ :=
  let rows := A * W * T * S ^ r
  let cols := K ^ (r + 1) * P
  let Hbox := (K : ℝ) * ∑ i, Height.logHeight₁ (alpha i)
  let V := boxMomentCoordinateBound B K
  let Hentry :=
    (Module.finrank ℚ F : ℝ) *
        Real.log ((W.factorial * (A + P) ^ P : ℕ) : ℝ) +
      (A : ℝ) * Hbox +
      ((T + r * S : ℕ) : ℝ) *
        ((Module.finrank ℚ F : ℝ) * Real.log (V : ℝ))
  numberFieldRowKernelCoefficientMajorant
    rows cols (Fintype.card ι) Hentry M

lemma one_le_boxPochhammerMultipointRowCoefficientMajorant
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (M : ℝ)
    (r B K P A W T S : ℕ) (alpha : Fin (r + 1) → F) :
    1 ≤ boxPochhammerMultipointRowCoefficientMajorant
      basis M r B K P A W T S alpha :=
  one_le_numberFieldRowKernelCoefficientMajorant _ _ _ _ _

theorem exists_box_pochhammerMultipoint_coefficients_with_rowMajorant
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    {r B K P A W T S : ℕ} (alpha : Fin (r + 1) → F)
    (b : Fin (r + 1) → ℤ) (M : ℝ)
    (hK : 0 < K) (hP : 0 < P) (hA : 0 < A)
    (hW : 0 < W) (hT : 0 < T) (hS : 0 < S)
    (hb : ∀ i, (b i).natAbs ≤ B) (hM0 : 0 ≤ M)
    (hM : ∀ i (φ : F →ₐ[ℚ] ℂ), ‖φ (basis i)‖ ≤ M)
    (hcard : (A * W * T * S ^ r) * Fintype.card ι <
      K ^ (r + 1) * P) :
    ∃ c : ExponentBox (r + 1) K → Fin P → ℤ, c ≠ 0 ∧
      (∀ node : Fin A, ∀ v : Fin W, ∀ q : Fin T,
        ∀ u : Fin r → Fin S,
          pochhammerMultipointMomentValue (boxMonomial alpha)
            boxDistinguishedExponent (boxTransformedExponent b) P c
            node v q (fun i ↦ u i) = 0) ∧
      ∀ x p, (c x p).natAbs ≤
        boxPochhammerMultipointRowCoefficientMajorant
          basis M r B K P A W T S alpha := by
  let Hbox : ℝ := (K : ℝ) * ∑ i, Height.logHeight₁ (alpha i)
  let V := boxMomentCoordinateBound B K
  simpa [boxPochhammerMultipointRowCoefficientMajorant, Hbox, V,
    ExponentBox] using
    (exists_pochhammerMultipoint_coefficients_with_rowMajorant
      basis hbasis (boxMonomial alpha) boxDistinguishedExponent
      (boxTransformedExponent b) P A W T S hP hA hW hT hS
      (V := (V : ℝ)) (H := Hbox) (M := M)
      (by exact_mod_cast one_le_boxMomentCoordinateBound hK) hM0
      (fun x ↦ logHeight₁_boxMonomial_le alpha x)
      (fun x ↦ (boxDistinguishedExponent_norm_le x).trans (by
        exact_mod_cast le_max_left K (2 * B * K)))
      (fun x i ↦ (boxTransformedExponent_norm_le b hb x i).trans (by
        exact_mod_cast le_max_right K (2 * B * K)))
      hM (by simpa [ExponentBox] using hcard))

theorem no_small_distinguished_linear_form_of_algebraic_initial_schedule_rowMajorant
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (φ : F →+* ℂ) {r B K P Ainit Wsrc Tsrc Ssrc : ℕ}
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ)
    (b : Fin (r + 1) → ℤ) (M : ℝ)
    (A W T S k Q : ℕ → ℕ) (R Z : ℕ → ℝ) (m : ℕ)
    (hK : 0 < K) (hP : 0 < P) (hAinit : 0 < Ainit)
    (hWsrc : 0 < Wsrc) (hTsrc : 0 < Tsrc) (hSsrc : 0 < Ssrc)
    (hM0 : 0 ≤ M) (hM : ∀ i (ψ : F →ₐ[ℚ] ℂ), ‖ψ (basis i)‖ ≤ M)
    (hcard : (Ainit * Wsrc * Tsrc * Ssrc ^ r) * Fintype.card ι <
      K ^ (r + 1) * P)
    (hb : ∀ i, (b i).natAbs ≤ B) (hb0 : b 0 ≠ 0)
    (halpha : ∀ i, alpha i ≠ 0)
    (hinj : Function.Injective
      (fun x : ExponentBox (r + 1) K ↦ boxMonomial alpha x))
    (hexp : ∀ x : ExponentBox (r + 1) K,
      Complex.exp (boxLinearForm ell x) = φ (boxMonomial alpha x))
    (hLambda : ‖∑ i, (b i : ℂ) * ell i‖ ≤ 1)
    (hA0 : A 0 = Ainit) (hW0 : W 0 = Wsrc)
    (hT0 : T 0 = Tsrc) (hS0 : S 0 = Ssrc)
    (hA : ∀ j, j < m → 0 < A j) (hk : ∀ j, j < m → 0 < k j)
    (hstepW : ∀ j, j < m → W (j + 1) + k j ≤ W j)
    (hstepT : ∀ j, j < m → T (j + 1) + Q j ≤ T j)
    (hstepS : ∀ j, j < m → S (j + 1) + k j ≤ S j)
    (hstepAR : ∀ j, j < m → (A j : ℝ) < R j)
    (hstepA'Z : ∀ j, j < m → (A (j + 1) : ℝ) ≤ Z j)
    (hstepZR : ∀ j, j < m → Z j ≤ R j)
    (hstepSmall : ∀ j, j < m → ∀ h < A (j + 1),
      ∀ v < W (j + 1), ∀ q < T (j + 1), ∀ u : Fin r → ℕ,
      (∀ i, u i < S (j + 1)) →
      pochhammerWeightedApproximationBound (K ^ (r + 1)) P
          (A j) (k j) (Q j) v q (∑ i, u i)
          (boxPochhammerMultipointRowCoefficientMajorant
            basis M r B K P Ainit Wsrc Tsrc Ssrc alpha : ℝ)
          (boxAnalyticCoordinateBound B K ell : ℝ)
          ((K : ℝ) * ∑ i, ‖ell i‖) (R j) (Z j)
          ‖∑ i, (b i : ℂ) * ell i‖ <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ (r + 1) + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (P * boxPochhammerMultipointRowCoefficientMajorant
                  basis M r B K P Ainit Wsrc Tsrc Ssrc alpha *
                (v.factorial * (h + 1 + P) ^ P) *
                (boxAnalyticCoordinateBound B K ell) ^
                  (q + ∑ i, u i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i)))))
    (hfinalA : K ^ (r + 1) * P ≤ A m)
    (hfinalW : 0 < W m) (hfinalT : 0 < T m) (hfinalS : 0 < S m) :
    False := by
  obtain ⟨c, hc0, hmoment, hc⟩ :=
    exists_box_pochhammerMultipoint_coefficients_with_rowMajorant
      basis hbasis alpha b M hK hP hAinit hWsrc hTsrc hSsrc hb hM0 hM hcard
  let C := boxPochhammerMultipointRowCoefficientMajorant
    basis M r B K P Ainit Wsrc Tsrc Ssrc alpha
  let V := boxAnalyticCoordinateBound B K ell
  have hCone : 1 ≤ C :=
    one_le_boxPochhammerMultipointRowCoefficientMajorant
      basis M r B K P Ainit Wsrc Tsrc Ssrc alpha
  have hVone : 1 ≤ V := one_le_boxAnalyticCoordinateBound ell
  have haV : ∀ x : ExponentBox (r + 1) K,
      ‖boxDistinguishedExponent x‖ ≤ (V : ℝ) := by
    intro x
    refine (boxDistinguishedExponent_norm_le x).trans ?_
    exact_mod_cast (le_max_left K (2 * B * K)).trans
      (boxMomentCoordinateBound_le_boxAnalyticCoordinateBound ell)
  have hrV : ∀ x : ExponentBox (r + 1) K, ∀ i : Fin r,
      ‖boxTransformedExponent b x i‖ ≤ (V : ℝ) := by
    intro x i
    refine (boxTransformedExponent_norm_le b hb x i).trans ?_
    exact_mod_cast (le_max_right K (2 * B * K)).trans
      (boxMomentCoordinateBound_le_boxAnalyticCoordinateBound ell)
  apply no_small_box_linear_form_of_pochhammer_iterated_approximate_moments
    φ alpha c (fun x ↦ boxLinearForm ell x)
      (b 0 : ℂ) (∑ i, (b i : ℂ) * ell i)
      boxDistinguishedExponent (boxTransformedExponent b)
      (fun i : Fin r ↦ ell i.succ)
      A W T S k Q R Z m (C := C) (V := V)
      (U := (K : ℝ) * ∑ i, ‖ell i‖)
  · exact hK
  · exact hP
  · exact hA
  · exact hk
  · rw [Complex.norm_intCast, ← Int.cast_abs, ← Nat.cast_natAbs]
    exact_mod_cast Int.natAbs_pos.mpr hb0
  · exact hLambda
  · exact hCone
  · exact hVone
  · positivity
  · exact hc0
  · exact hinj
  · exact fun x ↦ boxMonomial_ne_zero alpha halpha x
  · exact hc
  · exact haV
  · exact hrV
  · exact fun x ↦ boxTransformedLinearForm_norm_le_analyticBound ell b hb x
  · exact fun x ↦ boxLinearForm_norm_le ell x
  · exact hexp
  · exact fun x ↦ box_distinguished_linearForm_identity ell b x
  · rw [hA0, hW0, hT0, hS0]
    exact hmoment
  · exact hstepW
  · exact hstepT
  · exact hstepS
  · exact hstepAR
  · exact hstepA'Z
  · exact hstepZR
  · simpa [C, V] using hstepSmall
  · exact hfinalA
  · exact hfinalW
  · exact hfinalT
  · exact hfinalS

theorem no_small_distinguished_linear_form_of_scaled_dyadic_schedule_rowMajorant
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (φ : F →+* ℂ) {r B K P Ainit spend : ℕ}
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ)
    (b : Fin (r + 1) → ℤ) (M D : ℝ)
    (hK : 0 < K) (hP : 0 < P) (hAinit : 0 < Ainit)
    (hspend : 0 < spend) (hM0 : 0 ≤ M)
    (hM : ∀ i (ψ : F →ₐ[ℚ] ℂ), ‖ψ (basis i)‖ ≤ M)
    (hD : 1 ≤ D)
    (hcard :
      (Ainit *
        (dyadicStageCount (K ^ (r + 1) * P) * spend + 1) *
        (dyadicStageCount (K ^ (r + 1) * P) + 1) *
        (dyadicStageCount (K ^ (r + 1) * P) * spend + 1) ^ r) *
          Fintype.card ι < K ^ (r + 1) * P)
    (hb : ∀ i, (b i).natAbs ≤ B) (hb0 : b 0 ≠ 0)
    (halpha : ∀ i, alpha i ≠ 0)
    (hinj : Function.Injective
      (fun x : ExponentBox (r + 1) K ↦ boxMonomial alpha x))
    (hexp : ∀ x : ExponentBox (r + 1) K,
      Complex.exp (boxLinearForm ell x) = φ (boxMonomial alpha x))
    (hLambda : ‖∑ i, (b i : ℂ) * ell i‖ ≤ 1)
    (hsmall :
      let m := dyadicStageCount (K ^ (r + 1) * P)
      ∀ j, j < m → ∀ h < scaledDyadicStageA Ainit (j + 1),
        ∀ v < stageSpendBudget m spend (j + 1),
        ∀ q < stageUnitBudget m (j + 1),
        ∀ u : Fin r → ℕ,
        (∀ i, u i < stageSpendBudget m spend (j + 1)) →
        pochhammerWeightedApproximationBound (K ^ (r + 1)) P
            (scaledDyadicStageA Ainit j) spend 1 v q (∑ i, u i)
            (boxPochhammerMultipointRowCoefficientMajorant basis M r B K P
              Ainit (m * spend + 1) (m + 1) (m * spend + 1) alpha : ℝ)
            (boxAnalyticCoordinateBound B K ell : ℝ)
            ((K : ℝ) * ∑ i, ‖ell i‖)
            (D * (scaledDyadicStageA Ainit (j + 1) : ℝ))
            (scaledDyadicStageA Ainit (j + 1) : ℝ)
            ‖∑ i, (b i : ℂ) * ell i‖ <
          Real.exp (-((Module.finrank ℚ F : ℝ) *
                Real.log (K ^ (r + 1) + 1 : ℕ) +
              (Module.finrank ℚ F : ℝ) *
                Real.log (P * boxPochhammerMultipointRowCoefficientMajorant
                    basis M r B K P Ainit
                      (m * spend + 1) (m + 1) (m * spend + 1) alpha *
                  (v.factorial * (h + 1 + P) ^ P) *
                  (boxAnalyticCoordinateBound B K ell) ^
                    (q + ∑ i, u i) : ℕ) +
              (h : ℝ) * ((K : ℝ) *
                ∑ i, Height.logHeight₁ (alpha i))))) :
    False := by
  let N := K ^ (r + 1) * P
  let m := dyadicStageCount N
  let A : ℕ → ℕ := scaledDyadicStageA Ainit
  let W : ℕ → ℕ := stageSpendBudget m spend
  let T : ℕ → ℕ := stageUnitBudget m
  let S : ℕ → ℕ := stageSpendBudget m spend
  let k : ℕ → ℕ := fun _ ↦ spend
  let Q : ℕ → ℕ := fun _ ↦ 1
  let R : ℕ → ℝ := fun j ↦ D * (A (j + 1) : ℝ)
  let Z : ℕ → ℝ := fun j ↦ (A (j + 1) : ℝ)
  apply no_small_distinguished_linear_form_of_algebraic_initial_schedule_rowMajorant
    basis hbasis φ alpha ell b M A W T S k Q R Z m
      (Ainit := Ainit) (Wsrc := m * spend + 1)
      (Tsrc := m + 1) (Ssrc := m * spend + 1)
  · exact hK
  · exact hP
  · exact hAinit
  · positivity
  · positivity
  · positivity
  · exact hM0
  · exact hM
  · simpa [N, m, Nat.mul_assoc] using hcard
  · exact hb
  · exact hb0
  · exact halpha
  · exact hinj
  · exact hexp
  · exact hLambda
  · simp [A, scaledDyadicStageA]
  · simp [W, stageSpendBudget]
  · simp [T, stageUnitBudget]
  · simp [S, stageSpendBudget]
  · intro j hj
    exact scaledDyadicStageA_pos hAinit j
  · intro j hj
    simpa [k] using hspend
  · intro j hj
    exact (stageSpendBudget_step hj).le
  · intro j hj
    exact (stageUnitBudget_step hj).le
  · intro j hj
    exact (stageSpendBudget_step hj).le
  · intro j hj
    dsimp [A, R, scaledDyadicStageA]
    have hpow : (0 : ℝ) < ((Ainit * 2 ^ j : ℕ) : ℝ) := by positivity
    calc
      ((Ainit * 2 ^ j : ℕ) : ℝ) <
          2 * ((Ainit * 2 ^ j : ℕ) : ℝ) := by nlinarith
      _ ≤ D * (2 * ((Ainit * 2 ^ j : ℕ) : ℝ)) := by
        have hm := mul_le_mul_of_nonneg_right hD
          (show 0 ≤ 2 * ((Ainit * 2 ^ j : ℕ) : ℝ) by positivity)
        simpa using hm
      _ = D * ((Ainit * 2 ^ (j + 1) : ℕ) : ℝ) := by
        rw [pow_succ]
        push_cast
        ring
  · intro j hj
    simp [A, Z, scaledDyadicStageA]
  · intro j hj
    dsimp [R, Z]
    exact le_mul_of_one_le_left (by positivity) hD
  · dsimp [N, m, A, W, T, S, k, Q, R, Z] at hsmall ⊢
    exact hsmall
  · dsimp [N, A, m]
    exact le_scaledDyadicStageA_stageCount hAinit
  · simp [W, stageSpendBudget]
  · simp [T, stageUnitBudget]
  · simp [S, stageSpendBudget]


theorem exists_positive_lower_bound_of_scaled_dyadic_boundary_rowMajorant
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (φ : F →+* ℂ) {r B K P Ainit spend : ℕ}
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ)
    (b : Fin (r + 1) → ℤ) (M D : ℝ)
    (hK : 0 < K) (hP : 0 < P) (hAinit : 0 < Ainit)
    (hspend : 0 < spend) (hM0 : 0 ≤ M)
    (hM : ∀ i (ψ : F →ₐ[ℚ] ℂ), ‖ψ (basis i)‖ ≤ M)
    (hD : 1 ≤ D)
    (hcard :
      (Ainit *
        (dyadicStageCount (K ^ (r + 1) * P) * spend + 1) *
        (dyadicStageCount (K ^ (r + 1) * P) + 1) *
        (dyadicStageCount (K ^ (r + 1) * P) * spend + 1) ^ r) *
          Fintype.card ι < K ^ (r + 1) * P)
    (hb : ∀ i, (b i).natAbs ≤ B) (hb0 : b 0 ≠ 0)
    (halpha : ∀ i, alpha i ≠ 0)
    (hinj : Function.Injective
      (fun x : ExponentBox (r + 1) K ↦ boxMonomial alpha x))
    (hexp : ∀ x : ExponentBox (r + 1) K,
      Complex.exp (boxLinearForm ell x) = φ (boxMonomial alpha x))
    (hboundary :
      let m := dyadicStageCount (K ^ (r + 1) * P)
      ∀ j, j < m → ∀ h < scaledDyadicStageA Ainit (j + 1),
        ∀ v < stageSpendBudget m spend (j + 1),
        ∀ q < stageUnitBudget m (j + 1),
        ∀ u : Fin r → ℕ,
        (∀ i, u i < stageSpendBudget m spend (j + 1)) →
        pochhammerWeightedApproximationBound (K ^ (r + 1)) P
            (scaledDyadicStageA Ainit j) spend 1 v q (∑ i, u i)
            (boxPochhammerMultipointRowCoefficientMajorant basis M r B K P
              Ainit (m * spend + 1) (m + 1) (m * spend + 1) alpha : ℝ)
            (boxAnalyticCoordinateBound B K ell : ℝ)
            ((K : ℝ) * ∑ i, ‖ell i‖)
            (D * (scaledDyadicStageA Ainit (j + 1) : ℝ))
            (scaledDyadicStageA Ainit (j + 1) : ℝ) 0 <
          Real.exp (-((Module.finrank ℚ F : ℝ) *
                Real.log (K ^ (r + 1) + 1 : ℕ) +
              (Module.finrank ℚ F : ℝ) *
                Real.log (P * boxPochhammerMultipointRowCoefficientMajorant
                    basis M r B K P Ainit
                      (m * spend + 1) (m + 1) (m * spend + 1) alpha *
                  (v.factorial * (h + 1 + P) ^ P) *
                  (boxAnalyticCoordinateBound B K ell) ^
                    (q + ∑ i, u i) : ℕ) +
              (h : ℝ) * ((K : ℝ) *
                ∑ i, Height.logHeight₁ (alpha i))))) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ ‖∑ i, (b i : ℂ) * ell i‖ := by
  let Nbox := K ^ (r + 1)
  let N := Nbox * P
  let m := dyadicStageCount N
  let A : ℕ → ℕ := scaledDyadicStageA Ainit
  let W : ℕ → ℕ := stageSpendBudget m spend
  let T : ℕ → ℕ := stageUnitBudget m
  let S : ℕ → ℕ := stageSpendBudget m spend
  let k : ℕ → ℕ := fun _ ↦ spend
  let Q : ℕ → ℕ := fun _ ↦ 1
  let C : ℝ := boxPochhammerMultipointRowCoefficientMajorant basis M r B K P
    Ainit (m * spend + 1) (m + 1) (m * spend + 1) alpha
  let V : ℝ := boxAnalyticCoordinateBound B K ell
  let U : ℝ := (K : ℝ) * ∑ i, ‖ell i‖
  let R : ℕ → ℝ := fun j ↦ D * (A (j + 1) : ℝ)
  let Z : ℕ → ℝ := fun j ↦ (A (j + 1) : ℝ)
  let target : (j : ℕ) → ℕ → ℕ → ℕ → (Fin r → ℕ) → ℝ :=
    fun j h v q u ↦
      Real.exp (-((Module.finrank ℚ F : ℝ) *
            Real.log (K ^ (r + 1) + 1 : ℕ) +
          (Module.finrank ℚ F : ℝ) *
            Real.log (P * boxPochhammerMultipointRowCoefficientMajorant
                basis M r B K P Ainit
                  (m * spend + 1) (m + 1) (m * spend + 1) alpha *
              (v.factorial * (h + 1 + P) ^ P) *
              (boxAnalyticCoordinateBound B K ell) ^
                (q + ∑ i, u i) : ℕ) +
          (h : ℝ) * ((K : ℝ) *
            ∑ i, Height.logHeight₁ (alpha i))))
  have hboundary' : ∀ j, j < m → ∀ h < A (j + 1),
      ∀ v < W (j + 1), ∀ q < T (j + 1), ∀ u : Fin r → ℕ,
      (∀ i, u i < S (j + 1)) →
      pochhammerWeightedApproximationBound Nbox P (A j) (k j) (Q j)
          v q (∑ i, u i) C V U (R j) (Z j) 0 < target j h v q u := by
    dsimp [Nbox, N, m, A, W, T, S, k, Q, C, V, U, R, Z, target]
    simpa using hboundary
  obtain ⟨ε, hε, hεsmall⟩ :=
    exists_uniform_lambda_radius_of_boundary_small
      Nbox P A W T S k Q C V U R Z m target hboundary'
  let ε' := min ε 1
  have hε' : 0 < ε' := lt_min hε zero_lt_one
  refine ⟨ε', hε', ?_⟩
  by_contra hnot
  have hnormlt : ‖∑ i, (b i : ℂ) * ell i‖ < ε' := lt_of_not_ge hnot
  have hsmallAbs :
      |(‖∑ i, (b i : ℂ) * ell i‖ : ℝ)| < ε := by
    rw [abs_of_nonneg (norm_nonneg _)]
    exact hnormlt.trans_le (min_le_left _ _)
  have hsmall' := hεsmall _ hsmallAbs
  apply no_small_distinguished_linear_form_of_scaled_dyadic_schedule_rowMajorant
    basis hbasis φ alpha ell b M D hK hP hAinit hspend hM0 hM hD
      hcard hb hb0 halpha hinj hexp
  · exact hnormlt.le.trans (min_le_right _ _)
  · dsimp [Nbox, N, m, A, W, T, S, k, Q, C, V, U, R, Z, target] at hsmall'
    simpa using hsmall'

lemma isIntegral_scaled_pow_of_isIntegral_mul
    {F : Type*} [Field F] {Q K x : ℕ} {alpha : F}
    (hQa : IsIntegral ℤ ((Q : F) * alpha)) (hx : x ≤ K) :
    IsIntegral ℤ ((Q : F) ^ K * alpha ^ x) := by
  have hq : IsIntegral ℤ ((Q : F) ^ (K - x)) :=
    (isIntegral_natCast (R := ℤ) (B := F) Q).pow (K - x)
  have hp := hQa.pow x
  rw [mul_pow] at hp
  have hm := hq.mul hp
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hx] at hm
  exact hm

lemma isIntegral_scaled_boxMonomial
    {F : Type*} [Field F] {n K Q : ℕ}
    (alpha : Fin n → F)
    (hQa : ∀ i, IsIntegral ℤ ((Q : F) * alpha i))
    (x : ExponentBox n K) :
    IsIntegral ℤ ((Q : F) ^ (n * K) * boxMonomial alpha x) := by
  have hp : IsIntegral ℤ
      (∏ i : Fin n, ((Q : F) ^ K * alpha i ^ (x i : ℕ))) :=
    IsIntegral.prod _ fun i _ ↦
      isIntegral_scaled_pow_of_isIntegral_mul (hQa i) (x i).isLt.le
  simpa [boxMonomial, Finset.prod_mul_distrib, ← pow_mul, Nat.mul_comm] using hp

lemma isIntegral_scaled_boxMonomial_pow
    {F : Type*} [Field F] {n K A Q h : ℕ}
    (alpha : Fin n → F)
    (hQa : ∀ i, IsIntegral ℤ ((Q : F) * alpha i))
    (x : ExponentBox n K) (hh : h ≤ A) :
    IsIntegral ℤ ((Q : F) ^ (n * K * A) * boxMonomial alpha x ^ h) := by
  have hb := isIntegral_scaled_boxMonomial alpha hQa x
  have hb' : IsIntegral ℤ
      (((Q ^ (n * K) : ℕ) : F) * boxMonomial alpha x) := by
    simpa using hb
  have hp := isIntegral_scaled_pow_of_isIntegral_mul
    (Q := Q ^ (n * K)) (K := A) (x := h) hb' hh
  simpa [Nat.cast_pow, pow_mul, Nat.mul_assoc] using hp

lemma isIntegral_scaled_pochhammerMultipointInitialMomentMatrix
    {F : Type*} [Field F] {r K P A W T S Q : ℕ}
    (alpha : Fin (r + 1) → F)
    (hQa : ∀ i, IsIntegral ℤ ((Q : F) * alpha i))
    (a : ExponentBox (r + 1) K → ℤ)
    (rho : ExponentBox (r + 1) K → Fin r → ℤ) :
    ∀ row xm, IsIntegral ℤ
      (((Q ^ ((r + 1) * K * A) : ℕ) : F) *
        pochhammerMultipointInitialMomentMatrix
          (boxMonomial alpha) a rho P A W T S row xm) := by
  rintro ⟨node, v, q, u⟩ ⟨x, p⟩
  have hbeta := isIntegral_scaled_boxMonomial_pow alpha hQa x node.isLt.le
  have hjet : IsIntegral ℤ
      (pochhammerJet (p : ℕ) (v : ℕ) (node : ℕ) : F) :=
    isIntegral_intCast _
  have ha : IsIntegral ℤ ((a x : F) ^ (q : ℕ)) :=
    (isIntegral_intCast _).pow _
  have hrho : IsIntegral ℤ (∏ i, (rho x i : F) ^ (u i : ℕ)) :=
    IsIntegral.prod _ fun i _ ↦ (isIntegral_intCast _).pow _
  have hall := ((hbeta.mul hjet).mul ha).mul hrho
  simpa [pochhammerMultipointInitialMomentMatrix,
    mul_assoc, mul_comm, mul_left_comm] using hall

theorem exists_bounded_nonzero_integer_kernel_numberField_of_scale
    {K rows cols ι : Type*} [Field K] [NumberField K]
    [Fintype rows] [Fintype cols] [Fintype ι] [Nonempty rows]
    (b : Module.Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i))
    (A : Matrix rows cols K) (Q : ℕ) (hQ0 : Q ≠ 0)
    (hQA : ∀ r j, IsIntegral ℤ ((Q : K) * A r j))
    {H M S : ℝ} (hS0 : 0 ≤ S) (hM0 : 0 ≤ M)
    (hH : ∀ r j, Height.logHeight₁ (A r j) ≤ H)
    (hM : ∀ i (φ : K →ₐ[ℚ] ℂ), ‖φ (b i)‖ ≤ M)
    (hQ : (Q : ℝ) ≤ S)
    (hcard : Fintype.card rows * Fintype.card ι < Fintype.card cols) :
    ∃ c : cols → ℤ,
      c ≠ 0 ∧ A.mulVec (fun j ↦ (c j : K)) = 0 ∧
      (∀ j, (c j).natAbs ≤ Nat.ceil
        (((Fintype.card cols : ℝ) *
            max 1 ((Module.finrank ℚ K : ℝ) * S * Real.exp H * M)) ^
          (((Fintype.card rows * Fintype.card ι : ℕ) : ℝ) /
            ((Fintype.card cols : ℝ) -
              (Fintype.card rows * Fintype.card ι : ℕ))))) := by
  let T := traceConstraintMatrix b hb A Q hQA
  have hcard' : Fintype.card (rows × ι) < Fintype.card cols := by
    simpa [Fintype.card_prod] using hcard
  let : Nonempty ι := Fintype.card_pos_iff.mp <| by
    rw [← Module.finrank_eq_card_basis b]
    exact Module.finrank_pos
  have hrows' : 0 < Fintype.card (rows × ι) := Fintype.card_pos
  obtain ⟨c, hc0, hkernel, hcbound⟩ :=
    exists_bounded_nonzero_integer_kernel T hcard' hrows'
  have hAker : A.mulVec (fun j ↦ (c j : K)) = 0 :=
    traceConstraintMatrix_kernel b hb A Q hQ0 hQA c hkernel
  have hTnorm : ‖T‖ ≤
      (Module.finrank ℚ K : ℝ) * S * Real.exp H * M := by
    apply traceConstraintMatrix_norm_le b hb A Q hQA hS0 hM0 hH hM hQ
  refine ⟨c, hc0, hAker, fun j ↦ (hcbound j).trans ?_⟩
  apply Nat.ceil_mono
  rw [Fintype.card_prod]
  apply Real.rpow_le_rpow
  · positivity
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact max_le_max (le_refl 1) hTnorm
  · have hden : (0 : ℝ) <
        Fintype.card cols -
          (Fintype.card rows * Fintype.card ι : ℕ) := by
      exact sub_pos.mpr (by exact_mod_cast hcard)
    positivity

theorem exists_box_pochhammerMultipoint_coefficients_structured
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    {r B K P A W T S : ℕ} (alpha : Fin (r + 1) → F)
    (b : Fin (r + 1) → ℤ) (M : ℝ)
    (hK : 0 < K) (hP : 0 < P) (hA : 0 < A)
    (hW : 0 < W) (hT : 0 < T) (hS : 0 < S)
    (hb : ∀ i, (b i).natAbs ≤ B) (hM0 : 0 ≤ M)
    (hM : ∀ i (phi : F →ₐ[ℚ] ℂ), ‖phi (basis i)‖ ≤ M)
    (hcard : (A * W * T * S ^ r) * Fintype.card ι <
      K ^ (r + 1) * P) :
    let rows := A * W * T * S ^ r
    let cols := K ^ (r + 1) * P
    let Halpha := ∑ i, Height.logHeight₁ (alpha i)
    let V := boxMomentCoordinateBound B K
    let Hentry : ℝ :=
      (Module.finrank ℚ F : ℝ) *
          Real.log ((W.factorial * (A + P) ^ P : ℕ) : ℝ) +
        (A : ℝ) * ((K : ℝ) * Halpha) +
        ((T + r * S : ℕ) : ℝ) *
          ((Module.finrank ℚ F : ℝ) * Real.log (V : ℝ))
    let Qbound : ℝ :=
      (Real.exp Halpha ^ (r + 1)) ^ ((r + 1) * K * A)
    ∃ c : ExponentBox (r + 1) K → Fin P → ℤ, c ≠ 0 ∧
      (∀ node : Fin A, ∀ v : Fin W, ∀ q : Fin T,
        ∀ u : Fin r → Fin S,
          pochhammerMultipointMomentValue (boxMonomial alpha)
            boxDistinguishedExponent (boxTransformedExponent b) P c
            node v q (fun i ↦ u i) = 0) ∧
      ∀ x p, (c x p).natAbs ≤ Nat.ceil
        (((cols : ℝ) *
            max 1 ((Module.finrank ℚ F : ℝ) * Qbound *
              Real.exp Hentry * M)) ^
          (((rows * Fintype.card ι : ℕ) : ℝ) /
            ((cols : ℝ) - ((rows * Fintype.card ι : ℕ) : ℝ)))) := by
  dsimp only
  let rowsType := PochhammerMultipointInitialMomentIndex (Fin r) A W T S
  let colsType := ExponentBox (r + 1) K × Fin P
  let matrix : Matrix rowsType colsType F :=
    pochhammerMultipointInitialMomentMatrix (boxMonomial alpha)
      boxDistinguishedExponent (boxTransformedExponent b) P A W T S
  have hrowsCard : Fintype.card rowsType = A * W * T * S ^ r := by
    simp [rowsType, PochhammerMultipointInitialMomentIndex,
      RectangularMomentIndex, Nat.mul_assoc]
  have hcolsCard : Fintype.card colsType = K ^ (r + 1) * P := by
    simp [colsType, ExponentBox]
  let Halpha : ℝ := ∑ i, Height.logHeight₁ (alpha i)
  let V := boxMomentCoordinateBound B K
  let Hentry : ℝ :=
      (Module.finrank ℚ F : ℝ) *
          Real.log ((W.factorial * (A + P) ^ P : ℕ) : ℝ) +
        (A : ℝ) * ((K : ℝ) * Halpha) +
        ((T + r * S : ℕ) : ℝ) *
          ((Module.finrank ℚ F : ℝ) * Real.log (V : ℝ))
  have hheight : ∀ row xm, Height.logHeight₁ (matrix row xm) ≤ Hentry := by
    intro row xm
    simpa [matrix, Hentry, V] using
      (logHeight₁_pochhammerMultipointInitialMomentMatrix_le
        (boxMonomial alpha) boxDistinguishedExponent
        (boxTransformedExponent b) P A W T S hA hW hP
        (H := (K : ℝ) * Halpha) (V := (V : ℝ))
        (by exact_mod_cast one_le_boxMomentCoordinateBound hK)
        (fun x ↦ logHeight₁_boxMonomial_le alpha x)
        (fun x ↦ (boxDistinguishedExponent_norm_le x).trans (by
          exact_mod_cast le_max_left K (2 * B * K)))
        (fun x i ↦ (boxTransformedExponent_norm_le b hb x i).trans (by
          exact_mod_cast le_max_right K (2 * B * K))) row xm)
  have halphaHeight : ∀ i, Height.logHeight₁ (alpha i) ≤ Halpha := by
    intro i
    dsimp [Halpha]
    exact Finset.single_le_sum
      (fun j _ ↦ Height.zero_le_logHeight₁ (alpha j))
      (Finset.mem_univ i)
  obtain ⟨Q0, hQ00, hQ0bound, hQalpha⟩ :=
    exists_common_integral_scale alpha halphaHeight
  let Q : ℕ := Q0 ^ ((r + 1) * K * A)
  let Qbound : ℝ :=
    (Real.exp Halpha ^ (r + 1)) ^ ((r + 1) * K * A)
  have hQ0 : Q ≠ 0 := pow_ne_zero _ hQ00
  have hQint : ∀ row xm, IsIntegral ℤ ((Q : F) * matrix row xm) := by
    intro row xm
    simpa [Q, matrix] using
      (isIntegral_scaled_pochhammerMultipointInitialMomentMatrix
        alpha hQalpha boxDistinguishedExponent (boxTransformedExponent b)
        row xm)
  have hQbound : (Q : ℝ) ≤ Qbound := by
    dsimp [Q, Qbound]
    push_cast
    have hQ0bound' : (Q0 : ℝ) ≤ Real.exp Halpha ^ (r + 1) := by
      simpa using hQ0bound
    exact pow_le_pow_left₀ (by positivity) hQ0bound' _
  have : Nonempty rowsType := Fintype.card_pos_iff.mp <| by
    rw [hrowsCard]
    positivity
  have hcard' : Fintype.card rowsType * Fintype.card ι <
      Fintype.card colsType := by
    simpa [hrowsCard, hcolsCard] using hcard
  obtain ⟨cflat, hc0, hker, hc⟩ :=
    exists_bounded_nonzero_integer_kernel_numberField_of_scale
      basis hbasis matrix Q hQ0 hQint (H := Hentry) (M := M)
      (S := Qbound) (by positivity) hM0 hheight hM hQbound hcard'
  let c : ExponentBox (r + 1) K → Fin P → ℤ := fun x p ↦ cflat (x, p)
  have hc0' : c ≠ 0 := by
    intro hz
    apply hc0
    funext xp
    exact congrFun (congrFun hz xp.1) xp.2
  have hmom :=
    (pochhammerMultipointInitialMomentMatrix_kernel_iff
      (boxMonomial alpha) boxDistinguishedExponent
      (boxTransformedExponent b) P A W T S c).mp
        (by simpa [matrix, c] using hker)
  refine ⟨c, hc0', hmom, fun x p ↦ ?_⟩
  simpa [hrowsCard, hcolsCard, Hentry, Qbound] using hc (x, p)

noncomputable def structuredKernelCoefficientMajorant
    (rows cols d : ℕ) (Qbound H M : ℝ) : ℕ :=
  max 1 (Nat.ceil
    (Real.exp
      (Real.log ((cols : ℝ) *
          max 1 ((d : ℝ) * Qbound * Real.exp H * M)) *
        (((rows * d : ℕ) : ℝ) /
          ((cols : ℝ) - ((rows * d : ℕ) : ℝ))))))

lemma structuredKernelCoefficientMajorant_cast_le
    {rows cols d : ℕ} {Q H M : ℝ}
    (hcols : 0 < cols) (hd : 1 ≤ d) (hQ : 1 ≤ Q)
    (hH : 0 ≤ H) (hM : 1 ≤ M)
    (hhalf : 2 * (rows * d) ≤ cols) :
    (structuredKernelCoefficientMajorant rows cols d Q H M : ℝ) ≤
      2 * (cols : ℝ) * ((d : ℝ) * Q * Real.exp H * M) := by
  unfold structuredKernelCoefficientMajorant
  let E : ℝ := (d : ℝ) * Q * Real.exp H * M
  let expo : ℝ :=
    ((rows * d : ℕ) : ℝ) /
      ((cols : ℝ) - ((rows * d : ℕ) : ℝ))
  have hE : 1 ≤ E := by
    dsimp [E]
    have hexp : 1 ≤ Real.exp H := by
      simpa using Real.exp_le_exp.mpr hH
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by exact_mod_cast hd) hQ) hexp) hM
  have hden : (0 : ℝ) < (cols : ℝ) - ((rows * d : ℕ) : ℝ) := by
    have hlt : rows * d < cols := by omega
    exact sub_pos.mpr (by exact_mod_cast hlt)
  have hexpo1 : expo ≤ 1 := by
    dsimp [expo]
    rw [div_le_one hden]
    have hc : (2 : ℝ) * ((rows * d : ℕ) : ℝ) ≤ cols := by
      exact_mod_cast hhalf
    linarith
  have hbase : 1 ≤ (cols : ℝ) * E :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast hcols) hE
  have hbasepos : 0 < (cols : ℝ) * E := lt_of_lt_of_le zero_lt_one hbase
  have hlog : 0 ≤ Real.log ((cols : ℝ) * E) := Real.log_nonneg hbase
  have hexpBound :
      Real.exp (Real.log ((cols : ℝ) * E) * expo) ≤
        (cols : ℝ) * E := by
    calc
      Real.exp (Real.log ((cols : ℝ) * E) * expo) ≤
          Real.exp (Real.log ((cols : ℝ) * E) * 1) := by
        exact Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hexpo1 hlog)
      _ = (cols : ℝ) * E := by
        rw [mul_one, Real.exp_log hbasepos]
  have hceil :
      ((Nat.ceil
        (Real.exp (Real.log ((cols : ℝ) * E) * expo)) : ℕ) : ℝ) ≤
          (cols : ℝ) * E + 1 := by
    calc
      ((Nat.ceil
        (Real.exp (Real.log ((cols : ℝ) * E) * expo)) : ℕ) : ℝ) ≤
          Real.exp (Real.log ((cols : ℝ) * E) * expo) + 1 :=
        (Nat.ceil_lt_add_one (Real.exp_pos _).le).le
      _ ≤ (cols : ℝ) * E + 1 := by linarith
  change ((max 1 (Nat.ceil
      (Real.exp (Real.log ((cols : ℝ) * max 1 E) * expo))) : ℕ) : ℝ) ≤
        2 * (cols : ℝ) * E
  rw [max_eq_right hE, Nat.cast_max]
  simp only [Nat.cast_one]
  apply max_le
  · calc
      (1 : ℝ) ≤ (cols : ℝ) * E := hbase
      _ ≤ 2 * (cols : ℝ) * E := by
        nlinarith [show 0 ≤ (cols : ℝ) * E from zero_le_one.trans hbase]
  · calc
      ((Nat.ceil
        (Real.exp (Real.log ((cols : ℝ) * E) * expo)) : ℕ) : ℝ) ≤
          (cols : ℝ) * E + 1 := hceil
      _ ≤ 2 * (cols : ℝ) * E := by
        nlinarith [hbase]

lemma one_le_structuredKernelCoefficientMajorant
    (rows cols d : ℕ) (Qbound H M : ℝ) :
    1 ≤ structuredKernelCoefficientMajorant rows cols d Qbound H M :=
  le_max_left _ _

noncomputable def boxPochhammerStructuredCoefficientMajorant
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (M : ℝ)
    (r B K P A W T S : ℕ) (alpha : Fin (r + 1) → F) : ℕ :=
  let rows := A * W * T * S ^ r
  let cols := K ^ (r + 1) * P
  let Halpha := ∑ i, Height.logHeight₁ (alpha i)
  let V := boxMomentCoordinateBound B K
  let Hentry : ℝ :=
    (Module.finrank ℚ F : ℝ) *
        Real.log ((W.factorial * (A + P) ^ P : ℕ) : ℝ) +
      (A : ℝ) * ((K : ℝ) * Halpha) +
      ((T + r * S : ℕ) : ℝ) *
        ((Module.finrank ℚ F : ℝ) * Real.log (V : ℝ))
  let Qbound : ℝ :=
    (Real.exp Halpha ^ (r + 1)) ^ ((r + 1) * K * A)
  structuredKernelCoefficientMajorant
    rows cols (Fintype.card ι) Qbound Hentry M

lemma one_le_boxPochhammerStructuredCoefficientMajorant
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (M : ℝ)
    (r B K P A W T S : ℕ) (alpha : Fin (r + 1) → F) :
    1 ≤ boxPochhammerStructuredCoefficientMajorant
      basis M r B K P A W T S alpha :=
  one_le_structuredKernelCoefficientMajorant _ _ _ _ _ _

theorem exists_box_pochhammerMultipoint_coefficients_structured_majorant
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    {r B K P A W T S : ℕ} (alpha : Fin (r + 1) → F)
    (b : Fin (r + 1) → ℤ) (M : ℝ)
    (hK : 0 < K) (hP : 0 < P) (hA : 0 < A)
    (hW : 0 < W) (hT : 0 < T) (hS : 0 < S)
    (hb : ∀ i, (b i).natAbs ≤ B) (hM0 : 0 ≤ M)
    (hM : ∀ i (phi : F →ₐ[ℚ] ℂ), ‖phi (basis i)‖ ≤ M)
    (hcard : (A * W * T * S ^ r) * Fintype.card ι <
      K ^ (r + 1) * P) :
    ∃ c : ExponentBox (r + 1) K → Fin P → ℤ, c ≠ 0 ∧
      (∀ node : Fin A, ∀ v : Fin W, ∀ q : Fin T,
        ∀ u : Fin r → Fin S,
          pochhammerMultipointMomentValue (boxMonomial alpha)
            boxDistinguishedExponent (boxTransformedExponent b) P c
            node v q (fun i ↦ u i) = 0) ∧
      ∀ x p, (c x p).natAbs ≤
        boxPochhammerStructuredCoefficientMajorant
          basis M r B K P A W T S alpha := by
  obtain ⟨c, hc0, hmom, hc⟩ :=
    exists_box_pochhammerMultipoint_coefficients_structured
      basis hbasis alpha b M hK hP hA hW hT hS hb hM0 hM hcard
  refine ⟨c, hc0, hmom, fun x p ↦ (hc x p).trans ?_⟩
  have hd : Fintype.card ι = Module.finrank ℚ F := by
    rw [← Module.finrank_eq_card_basis basis]
  have hbase : 0 < ((K ^ (r + 1) * P : ℕ) : ℝ) *
      max 1 ((Module.finrank ℚ F : ℝ) *
        (Real.exp (∑ i, Height.logHeight₁ (alpha i)) ^ (r + 1)) ^
          ((r + 1) * K * A) *
        Real.exp ((Module.finrank ℚ F : ℝ) *
            Real.log ((W.factorial * (A + P) ^ P : ℕ) : ℝ) +
          (A : ℝ) * ((K : ℝ) * ∑ i, Height.logHeight₁ (alpha i)) +
          ((T + r * S : ℕ) : ℝ) *
            ((Module.finrank ℚ F : ℝ) *
              Real.log (boxMomentCoordinateBound B K : ℝ))) * M) := by
    positivity
  unfold boxPochhammerStructuredCoefficientMajorant
    structuredKernelCoefficientMajorant
  apply le_max_of_le_right
  apply Nat.ceil_mono
  rw [Real.rpow_def_of_pos hbase]
  rw [← hd]

theorem no_small_distinguished_linear_form_of_algebraic_initial_schedule_structured
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (φ : F →+* ℂ) {r B K P Ainit Wsrc Tsrc Ssrc : ℕ}
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ)
    (b : Fin (r + 1) → ℤ) (M : ℝ)
    (A W T S k Q : ℕ → ℕ) (R Z : ℕ → ℝ) (m : ℕ)
    (hK : 0 < K) (hP : 0 < P) (hAinit : 0 < Ainit)
    (hWsrc : 0 < Wsrc) (hTsrc : 0 < Tsrc) (hSsrc : 0 < Ssrc)
    (hM0 : 0 ≤ M) (hM : ∀ i (ψ : F →ₐ[ℚ] ℂ), ‖ψ (basis i)‖ ≤ M)
    (hcard : (Ainit * Wsrc * Tsrc * Ssrc ^ r) * Fintype.card ι <
      K ^ (r + 1) * P)
    (hb : ∀ i, (b i).natAbs ≤ B) (hb0 : b 0 ≠ 0)
    (halpha : ∀ i, alpha i ≠ 0)
    (hinj : Function.Injective
      (fun x : ExponentBox (r + 1) K ↦ boxMonomial alpha x))
    (hexp : ∀ x : ExponentBox (r + 1) K,
      Complex.exp (boxLinearForm ell x) = φ (boxMonomial alpha x))
    (hLambda : ‖∑ i, (b i : ℂ) * ell i‖ ≤ 1)
    (hA0 : A 0 = Ainit) (hW0 : W 0 = Wsrc)
    (hT0 : T 0 = Tsrc) (hS0 : S 0 = Ssrc)
    (hA : ∀ j, j < m → 0 < A j) (hk : ∀ j, j < m → 0 < k j)
    (hstepW : ∀ j, j < m → W (j + 1) + k j ≤ W j)
    (hstepT : ∀ j, j < m → T (j + 1) + Q j ≤ T j)
    (hstepS : ∀ j, j < m → S (j + 1) + k j ≤ S j)
    (hstepAR : ∀ j, j < m → (A j : ℝ) < R j)
    (hstepA'Z : ∀ j, j < m → (A (j + 1) : ℝ) ≤ Z j)
    (hstepZR : ∀ j, j < m → Z j ≤ R j)
    (hstepSmall : ∀ j, j < m → ∀ h < A (j + 1),
      ∀ v < W (j + 1), ∀ q < T (j + 1), ∀ u : Fin r → ℕ,
      (∀ i, u i < S (j + 1)) →
      pochhammerWeightedApproximationBound (K ^ (r + 1)) P
          (A j) (k j) (Q j) v q (∑ i, u i)
          (boxPochhammerStructuredCoefficientMajorant
            basis M r B K P Ainit Wsrc Tsrc Ssrc alpha : ℝ)
          (boxAnalyticCoordinateBound B K ell : ℝ)
          ((K : ℝ) * ∑ i, ‖ell i‖) (R j) (Z j)
          ‖∑ i, (b i : ℂ) * ell i‖ <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ (r + 1) + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (P * boxPochhammerStructuredCoefficientMajorant
                  basis M r B K P Ainit Wsrc Tsrc Ssrc alpha *
                (v.factorial * (h + 1 + P) ^ P) *
                (boxAnalyticCoordinateBound B K ell) ^
                  (q + ∑ i, u i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i)))))
    (hfinalA : K ^ (r + 1) * P ≤ A m)
    (hfinalW : 0 < W m) (hfinalT : 0 < T m) (hfinalS : 0 < S m) :
    False := by
  obtain ⟨c, hc0, hmoment, hc⟩ :=
    exists_box_pochhammerMultipoint_coefficients_structured_majorant
      basis hbasis alpha b M hK hP hAinit hWsrc hTsrc hSsrc hb hM0 hM hcard
  let C := boxPochhammerStructuredCoefficientMajorant
    basis M r B K P Ainit Wsrc Tsrc Ssrc alpha
  let V := boxAnalyticCoordinateBound B K ell
  have hCone : 1 ≤ C :=
    one_le_boxPochhammerStructuredCoefficientMajorant
      basis M r B K P Ainit Wsrc Tsrc Ssrc alpha
  have hVone : 1 ≤ V := one_le_boxAnalyticCoordinateBound ell
  have haV : ∀ x : ExponentBox (r + 1) K,
      ‖boxDistinguishedExponent x‖ ≤ (V : ℝ) := by
    intro x
    refine (boxDistinguishedExponent_norm_le x).trans ?_
    exact_mod_cast (le_max_left K (2 * B * K)).trans
      (boxMomentCoordinateBound_le_boxAnalyticCoordinateBound ell)
  have hrV : ∀ x : ExponentBox (r + 1) K, ∀ i : Fin r,
      ‖boxTransformedExponent b x i‖ ≤ (V : ℝ) := by
    intro x i
    refine (boxTransformedExponent_norm_le b hb x i).trans ?_
    exact_mod_cast (le_max_right K (2 * B * K)).trans
      (boxMomentCoordinateBound_le_boxAnalyticCoordinateBound ell)
  apply no_small_box_linear_form_of_pochhammer_iterated_approximate_moments
    φ alpha c (fun x ↦ boxLinearForm ell x)
      (b 0 : ℂ) (∑ i, (b i : ℂ) * ell i)
      boxDistinguishedExponent (boxTransformedExponent b)
      (fun i : Fin r ↦ ell i.succ)
      A W T S k Q R Z m (C := C) (V := V)
      (U := (K : ℝ) * ∑ i, ‖ell i‖)
  · exact hK
  · exact hP
  · exact hA
  · exact hk
  · rw [Complex.norm_intCast, ← Int.cast_abs, ← Nat.cast_natAbs]
    exact_mod_cast Int.natAbs_pos.mpr hb0
  · exact hLambda
  · exact hCone
  · exact hVone
  · positivity
  · exact hc0
  · exact hinj
  · exact fun x ↦ boxMonomial_ne_zero alpha halpha x
  · exact hc
  · exact haV
  · exact hrV
  · exact fun x ↦ boxTransformedLinearForm_norm_le_analyticBound ell b hb x
  · exact fun x ↦ boxLinearForm_norm_le ell x
  · exact hexp
  · exact fun x ↦ box_distinguished_linearForm_identity ell b x
  · rw [hA0, hW0, hT0, hS0]
    exact hmoment
  · exact hstepW
  · exact hstepT
  · exact hstepS
  · exact hstepAR
  · exact hstepA'Z
  · exact hstepZR
  · simpa [C, V] using hstepSmall
  · exact hfinalA
  · exact hfinalW
  · exact hfinalT
  · exact hfinalS

theorem no_small_distinguished_linear_form_of_scaled_dyadic_schedule_structured
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (φ : F →+* ℂ) {r B K P Ainit spend : ℕ}
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ)
    (b : Fin (r + 1) → ℤ) (M D : ℝ)
    (hK : 0 < K) (hP : 0 < P) (hAinit : 0 < Ainit)
    (hspend : 0 < spend) (hM0 : 0 ≤ M)
    (hM : ∀ i (ψ : F →ₐ[ℚ] ℂ), ‖ψ (basis i)‖ ≤ M)
    (hD : 1 ≤ D)
    (hcard :
      (Ainit *
        (dyadicStageCount (K ^ (r + 1) * P) * spend + 1) *
        (dyadicStageCount (K ^ (r + 1) * P) + 1) *
        (dyadicStageCount (K ^ (r + 1) * P) * spend + 1) ^ r) *
          Fintype.card ι < K ^ (r + 1) * P)
    (hb : ∀ i, (b i).natAbs ≤ B) (hb0 : b 0 ≠ 0)
    (halpha : ∀ i, alpha i ≠ 0)
    (hinj : Function.Injective
      (fun x : ExponentBox (r + 1) K ↦ boxMonomial alpha x))
    (hexp : ∀ x : ExponentBox (r + 1) K,
      Complex.exp (boxLinearForm ell x) = φ (boxMonomial alpha x))
    (hLambda : ‖∑ i, (b i : ℂ) * ell i‖ ≤ 1)
    (hsmall :
      let m := dyadicStageCount (K ^ (r + 1) * P)
      ∀ j, j < m → ∀ h < scaledDyadicStageA Ainit (j + 1),
        ∀ v < stageSpendBudget m spend (j + 1),
        ∀ q < stageUnitBudget m (j + 1),
        ∀ u : Fin r → ℕ,
        (∀ i, u i < stageSpendBudget m spend (j + 1)) →
        pochhammerWeightedApproximationBound (K ^ (r + 1)) P
            (scaledDyadicStageA Ainit j) spend 1 v q (∑ i, u i)
            (boxPochhammerStructuredCoefficientMajorant basis M r B K P
              Ainit (m * spend + 1) (m + 1) (m * spend + 1) alpha : ℝ)
            (boxAnalyticCoordinateBound B K ell : ℝ)
            ((K : ℝ) * ∑ i, ‖ell i‖)
            (D * (scaledDyadicStageA Ainit (j + 1) : ℝ))
            (scaledDyadicStageA Ainit (j + 1) : ℝ)
            ‖∑ i, (b i : ℂ) * ell i‖ <
          Real.exp (-((Module.finrank ℚ F : ℝ) *
                Real.log (K ^ (r + 1) + 1 : ℕ) +
              (Module.finrank ℚ F : ℝ) *
                Real.log (P * boxPochhammerStructuredCoefficientMajorant
                    basis M r B K P Ainit
                      (m * spend + 1) (m + 1) (m * spend + 1) alpha *
                  (v.factorial * (h + 1 + P) ^ P) *
                  (boxAnalyticCoordinateBound B K ell) ^
                    (q + ∑ i, u i) : ℕ) +
              (h : ℝ) * ((K : ℝ) *
                ∑ i, Height.logHeight₁ (alpha i))))) :
    False := by
  let N := K ^ (r + 1) * P
  let m := dyadicStageCount N
  let A : ℕ → ℕ := scaledDyadicStageA Ainit
  let W : ℕ → ℕ := stageSpendBudget m spend
  let T : ℕ → ℕ := stageUnitBudget m
  let S : ℕ → ℕ := stageSpendBudget m spend
  let k : ℕ → ℕ := fun _ ↦ spend
  let Q : ℕ → ℕ := fun _ ↦ 1
  let R : ℕ → ℝ := fun j ↦ D * (A (j + 1) : ℝ)
  let Z : ℕ → ℝ := fun j ↦ (A (j + 1) : ℝ)
  apply no_small_distinguished_linear_form_of_algebraic_initial_schedule_structured
    basis hbasis φ alpha ell b M A W T S k Q R Z m
      (Ainit := Ainit) (Wsrc := m * spend + 1)
      (Tsrc := m + 1) (Ssrc := m * spend + 1)
  · exact hK
  · exact hP
  · exact hAinit
  · positivity
  · positivity
  · positivity
  · exact hM0
  · exact hM
  · simpa [N, m, Nat.mul_assoc] using hcard
  · exact hb
  · exact hb0
  · exact halpha
  · exact hinj
  · exact hexp
  · exact hLambda
  · simp [A, scaledDyadicStageA]
  · simp [W, stageSpendBudget]
  · simp [T, stageUnitBudget]
  · simp [S, stageSpendBudget]
  · intro j hj
    exact scaledDyadicStageA_pos hAinit j
  · intro j hj
    simpa [k] using hspend
  · intro j hj
    exact (stageSpendBudget_step hj).le
  · intro j hj
    exact (stageUnitBudget_step hj).le
  · intro j hj
    exact (stageSpendBudget_step hj).le
  · intro j hj
    dsimp [A, R, scaledDyadicStageA]
    have hpow : (0 : ℝ) < ((Ainit * 2 ^ j : ℕ) : ℝ) := by positivity
    calc
      ((Ainit * 2 ^ j : ℕ) : ℝ) <
          2 * ((Ainit * 2 ^ j : ℕ) : ℝ) := by nlinarith
      _ ≤ D * (2 * ((Ainit * 2 ^ j : ℕ) : ℝ)) := by
        have hm := mul_le_mul_of_nonneg_right hD
          (show 0 ≤ 2 * ((Ainit * 2 ^ j : ℕ) : ℝ) by positivity)
        simpa using hm
      _ = D * ((Ainit * 2 ^ (j + 1) : ℕ) : ℝ) := by
        rw [pow_succ]
        push_cast
        ring
  · intro j hj
    simp [A, Z, scaledDyadicStageA]
  · intro j hj
    dsimp [R, Z]
    exact le_mul_of_one_le_left (by positivity) hD
  · dsimp [N, m, A, W, T, S, k, Q, R, Z] at hsmall ⊢
    exact hsmall
  · dsimp [N, A, m]
    exact le_scaledDyadicStageA_stageCount hAinit
  · simp [W, stageSpendBudget]
  · simp [T, stageUnitBudget]
  · simp [S, stageSpendBudget]


theorem exists_positive_lower_bound_of_scaled_dyadic_boundary_structured
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (φ : F →+* ℂ) {r B K P Ainit spend : ℕ}
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ)
    (b : Fin (r + 1) → ℤ) (M D : ℝ)
    (hK : 0 < K) (hP : 0 < P) (hAinit : 0 < Ainit)
    (hspend : 0 < spend) (hM0 : 0 ≤ M)
    (hM : ∀ i (ψ : F →ₐ[ℚ] ℂ), ‖ψ (basis i)‖ ≤ M)
    (hD : 1 ≤ D)
    (hcard :
      (Ainit *
        (dyadicStageCount (K ^ (r + 1) * P) * spend + 1) *
        (dyadicStageCount (K ^ (r + 1) * P) + 1) *
        (dyadicStageCount (K ^ (r + 1) * P) * spend + 1) ^ r) *
          Fintype.card ι < K ^ (r + 1) * P)
    (hb : ∀ i, (b i).natAbs ≤ B) (hb0 : b 0 ≠ 0)
    (halpha : ∀ i, alpha i ≠ 0)
    (hinj : Function.Injective
      (fun x : ExponentBox (r + 1) K ↦ boxMonomial alpha x))
    (hexp : ∀ x : ExponentBox (r + 1) K,
      Complex.exp (boxLinearForm ell x) = φ (boxMonomial alpha x))
    (hboundary :
      let m := dyadicStageCount (K ^ (r + 1) * P)
      ∀ j, j < m → ∀ h < scaledDyadicStageA Ainit (j + 1),
        ∀ v < stageSpendBudget m spend (j + 1),
        ∀ q < stageUnitBudget m (j + 1),
        ∀ u : Fin r → ℕ,
        (∀ i, u i < stageSpendBudget m spend (j + 1)) →
        pochhammerWeightedApproximationBound (K ^ (r + 1)) P
            (scaledDyadicStageA Ainit j) spend 1 v q (∑ i, u i)
            (boxPochhammerStructuredCoefficientMajorant basis M r B K P
              Ainit (m * spend + 1) (m + 1) (m * spend + 1) alpha : ℝ)
            (boxAnalyticCoordinateBound B K ell : ℝ)
            ((K : ℝ) * ∑ i, ‖ell i‖)
            (D * (scaledDyadicStageA Ainit (j + 1) : ℝ))
            (scaledDyadicStageA Ainit (j + 1) : ℝ) 0 <
          Real.exp (-((Module.finrank ℚ F : ℝ) *
                Real.log (K ^ (r + 1) + 1 : ℕ) +
              (Module.finrank ℚ F : ℝ) *
                Real.log (P * boxPochhammerStructuredCoefficientMajorant
                    basis M r B K P Ainit
                      (m * spend + 1) (m + 1) (m * spend + 1) alpha *
                  (v.factorial * (h + 1 + P) ^ P) *
                  (boxAnalyticCoordinateBound B K ell) ^
                    (q + ∑ i, u i) : ℕ) +
              (h : ℝ) * ((K : ℝ) *
                ∑ i, Height.logHeight₁ (alpha i))))) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ ‖∑ i, (b i : ℂ) * ell i‖ := by
  let Nbox := K ^ (r + 1)
  let N := Nbox * P
  let m := dyadicStageCount N
  let A : ℕ → ℕ := scaledDyadicStageA Ainit
  let W : ℕ → ℕ := stageSpendBudget m spend
  let T : ℕ → ℕ := stageUnitBudget m
  let S : ℕ → ℕ := stageSpendBudget m spend
  let k : ℕ → ℕ := fun _ ↦ spend
  let Q : ℕ → ℕ := fun _ ↦ 1
  let C : ℝ := boxPochhammerStructuredCoefficientMajorant basis M r B K P
    Ainit (m * spend + 1) (m + 1) (m * spend + 1) alpha
  let V : ℝ := boxAnalyticCoordinateBound B K ell
  let U : ℝ := (K : ℝ) * ∑ i, ‖ell i‖
  let R : ℕ → ℝ := fun j ↦ D * (A (j + 1) : ℝ)
  let Z : ℕ → ℝ := fun j ↦ (A (j + 1) : ℝ)
  let target : (j : ℕ) → ℕ → ℕ → ℕ → (Fin r → ℕ) → ℝ :=
    fun j h v q u ↦
      Real.exp (-((Module.finrank ℚ F : ℝ) *
            Real.log (K ^ (r + 1) + 1 : ℕ) +
          (Module.finrank ℚ F : ℝ) *
            Real.log (P * boxPochhammerStructuredCoefficientMajorant
                basis M r B K P Ainit
                  (m * spend + 1) (m + 1) (m * spend + 1) alpha *
              (v.factorial * (h + 1 + P) ^ P) *
              (boxAnalyticCoordinateBound B K ell) ^
                (q + ∑ i, u i) : ℕ) +
          (h : ℝ) * ((K : ℝ) *
            ∑ i, Height.logHeight₁ (alpha i))))
  have hboundary' : ∀ j, j < m → ∀ h < A (j + 1),
      ∀ v < W (j + 1), ∀ q < T (j + 1), ∀ u : Fin r → ℕ,
      (∀ i, u i < S (j + 1)) →
      pochhammerWeightedApproximationBound Nbox P (A j) (k j) (Q j)
          v q (∑ i, u i) C V U (R j) (Z j) 0 < target j h v q u := by
    dsimp [Nbox, N, m, A, W, T, S, k, Q, C, V, U, R, Z, target]
    simpa using hboundary
  obtain ⟨ε, hε, hεsmall⟩ :=
    exists_uniform_lambda_radius_of_boundary_small
      Nbox P A W T S k Q C V U R Z m target hboundary'
  let ε' := min ε 1
  have hε' : 0 < ε' := lt_min hε zero_lt_one
  refine ⟨ε', hε', ?_⟩
  by_contra hnot
  have hnormlt : ‖∑ i, (b i : ℂ) * ell i‖ < ε' := lt_of_not_ge hnot
  have hsmallAbs :
      |(‖∑ i, (b i : ℂ) * ell i‖ : ℝ)| < ε := by
    rw [abs_of_nonneg (norm_nonneg _)]
    exact hnormlt.trans_le (min_le_left _ _)
  have hsmall' := hεsmall _ hsmallAbs
  apply no_small_distinguished_linear_form_of_scaled_dyadic_schedule_structured
    basis hbasis φ alpha ell b M D hK hP hAinit hspend hM0 hM hD
      hcard hb hb0 halpha hinj hexp
  · exact hnormlt.le.trans (min_le_right _ _)
  · dsimp [Nbox, N, m, A, W, T, S, k, Q, C, V, U, R, Z, target] at hsmall'
    simpa using hsmall'

lemma self_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by omega)
      omega

lemma dyadicStageCount_box_parameter_bound
    {r L : ℕ} (hr : r ≤ 8) (hL : 2 ≤ L) :
    dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24) ≤ 313 * L := by
  let e := 32 * (r + 1) + 24
  have he : e ≤ 312 := by
    dsimp [e]
    omega
  have hL0 : L ≠ 0 := by omega
  have hN0 : (L ^ 32) ^ (r + 1) * L ^ 24 ≠ 0 := by positivity
  have hrewrite : (L ^ 32) ^ (r + 1) * L ^ 24 = L ^ e := by
    simp [e, ← pow_mul, ← pow_add, Nat.mul_comm]
  have hpowbase : L ^ e ≤ (2 ^ L) ^ e :=
    Nat.pow_le_pow_left (self_le_two_pow L) e
  have hpowrewrite : (2 ^ L) ^ e = 2 ^ (L * e) := by
    rw [pow_mul]
  have hexp : L * e < 313 * L := by
    nlinarith
  have htwo : 2 ^ (L * e) < 2 ^ (313 * L) :=
    Nat.pow_lt_pow_right (by omega) hexp
  have hNlt : (L ^ 32) ^ (r + 1) * L ^ 24 < 2 ^ (313 * L) := by
    rw [hrewrite]
    exact hpowbase.trans_lt (hpowrewrite ▸ htwo)
  unfold dyadicStageCount
  exact Nat.succ_le_iff.mpr (Nat.log_lt_of_lt_pow hN0 hNlt)

lemma stageSpendBudget_le_zero (m spend j : ℕ) :
    stageSpendBudget m spend j ≤ m * spend + 1 := by
  unfold stageSpendBudget
  gcongr
  omega

lemma stageUnitBudget_le_zero (m j : ℕ) :
    stageUnitBudget m j ≤ m + 1 := by
  unfold stageUnitBudget
  omega

lemma box_parameter_budget_bounds
    {r L : ℕ} (hr : r ≤ 8) (hL : 2 ≤ L) :
    let K := L ^ 32
    let P := L ^ 24
    let spend := L ^ 33
    let m := dyadicStageCount (K ^ (r + 1) * P)
    m ≤ 313 * L ∧
      m * spend + 1 ≤ 314 * L ^ 34 ∧
      m + 1 ≤ 314 * L := by
  dsimp only
  let m := dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24)
  have hm : m ≤ 313 * L :=
    dyadicStageCount_box_parameter_bound hr hL
  have hLone : 1 ≤ L ^ 34 := Nat.one_le_pow _ _ (by omega)
  have hbudget : m * L ^ 33 + 1 ≤ 314 * L ^ 34 := by
    calc
      m * L ^ 33 + 1 ≤ (313 * L) * L ^ 33 + L ^ 34 :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hm) hLone
      _ = 314 * L ^ 34 := by ring
  have hstage : m + 1 ≤ 314 * L := by
    calc
      m + 1 ≤ 313 * L + L := Nat.add_le_add hm (by omega)
      _ = 314 * L := by ring
  exact ⟨hm, hbudget, hstage⟩

lemma scaledDyadicStageA_parameter_upper
    {r L j : ℕ} (hL : 2 ≤ L)
    (hj : j < dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24)) :
    scaledDyadicStageA (L ^ 2) (j + 1) ≤
      2 * L ^ 2 * ((L ^ 32) ^ (r + 1) * L ^ 24) := by
  let N := (L ^ 32) ^ (r + 1) * L ^ 24
  let m := dyadicStageCount N
  have hN0 : N ≠ 0 := by dsimp [N]; positivity
  have hjm : j + 1 ≤ m := by simpa [m] using hj
  have hpowjm : 2 ^ (j + 1) ≤ 2 ^ m :=
    Nat.pow_le_pow_right (by omega) hjm
  have hm : m = (Nat.log 2 N) + 1 := rfl
  have hpown : 2 ^ m ≤ 2 * N := by
    rw [hm, pow_succ]
    simpa [Nat.mul_comm] using
      Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 hN0)
  dsimp [scaledDyadicStageA]
  calc
    L ^ 2 * 2 ^ (j + 1) ≤ L ^ 2 * 2 ^ m := Nat.mul_le_mul_left _ hpowjm
    _ ≤ L ^ 2 * (2 * N) := Nat.mul_le_mul_left _ hpown
    _ = 2 * L ^ 2 * ((L ^ 32) ^ (r + 1) * L ^ 24) := by
      dsimp [N]
      ring


lemma log_nat_factorial_le {n : ℕ} (hn : 0 < n) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
  have hfacPos : (0 : ℝ) < n.factorial := by positivity
  have hpowPos : (0 : ℝ) < (n ^ n : ℕ) := by positivity
  calc
    Real.log (n.factorial : ℝ) ≤ Real.log ((n ^ n : ℕ) : ℝ) := by
      exact Real.log_le_log hfacPos (by exact_mod_cast Nat.factorial_le_pow n)
    _ = (n : ℝ) * Real.log (n : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]

lemma log_nat_le_poly
    {n c e L : ℕ} (hn : 0 < n) (hc : 0 < c) (hL : 0 < L)
    (hlogL : 1 ≤ Real.log (L : ℝ)) (hnle : n ≤ c * L ^ e) :
    Real.log (n : ℝ) ≤ (c + e : ℕ) * Real.log (L : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hprodR : (0 : ℝ) < (c * L ^ e : ℕ) := by positivity
  have hlogc : Real.log (c : ℝ) ≤ (c : ℝ) := by
    calc
      Real.log (c : ℝ) ≤ (c : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos hcR
      _ ≤ (c : ℝ) := by linarith
  calc
    Real.log (n : ℝ) ≤ Real.log ((c * L ^ e : ℕ) : ℝ) := by
      exact Real.log_le_log hnR (by exact_mod_cast hnle)
    _ = Real.log (c : ℝ) + (e : ℝ) * Real.log (L : ℝ) := by
      push_cast
      rw [Real.log_mul hcR.ne' (pow_ne_zero _ hLR.ne'), Real.log_pow]
    _ ≤ (c : ℝ) * Real.log (L : ℝ) +
          (e : ℝ) * Real.log (L : ℝ) := by
      gcongr
      exact hlogc.trans (le_mul_of_one_le_right (by positivity) hlogL)
    _ = (c + e : ℕ) * Real.log (L : ℝ) := by push_cast; ring

lemma log_nat_le_log_coefficient_add
    {n c e L : ℕ} (hn : 0 < n) (hc : 0 < c) (hL : 0 < L)
    (hlogL : 1 ≤ Real.log (L : ℝ)) (hnle : n ≤ c * L ^ e) :
    Real.log (n : ℝ) ≤
      (Real.log (c : ℝ) + (e : ℝ)) * Real.log (L : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hlogc : 0 ≤ Real.log (c : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ c by omega))
  calc
    Real.log (n : ℝ) ≤ Real.log ((c * L ^ e : ℕ) : ℝ) := by
      exact Real.log_le_log hnR (by exact_mod_cast hnle)
    _ = Real.log (c : ℝ) + (e : ℝ) * Real.log (L : ℝ) := by
      push_cast
      rw [Real.log_mul hcR.ne' (pow_ne_zero _ hLR.ne'), Real.log_pow]
    _ ≤ (Real.log (c : ℝ) + (e : ℝ)) * Real.log (L : ℝ) := by
      nlinarith [mul_nonneg hlogc (sub_nonneg.mpr hlogL)]


lemma log_nat_factorial_le_poly
    {n c e L : ℕ} (hn : 0 < n) (hc : 0 < c) (hL : 0 < L)
    (hlogL : 1 ≤ Real.log (L : ℝ)) (hnle : n ≤ c * L ^ e) :
    Real.log (n.factorial : ℝ) ≤
      (c * (c + e) : ℕ) * (L : ℝ) ^ e * Real.log (L : ℝ) := by
  have hncast : (n : ℝ) ≤ (c : ℝ) * (L : ℝ) ^ e := by
    exact_mod_cast hnle
  have hlogn := log_nat_le_poly hn hc hL hlogL hnle
  calc
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) :=
      log_nat_factorial_le hn
    _ ≤ ((c : ℝ) * (L : ℝ) ^ e) *
          ((c + e : ℕ) * Real.log (L : ℝ)) := by
      apply mul_le_mul hncast hlogn
      · exact Real.log_nonneg (by exact_mod_cast hn)
      · positivity
    _ = (c * (c + e) : ℕ) * (L : ℝ) ^ e * Real.log (L : ℝ) := by
      push_cast
      ring


noncomputable def boxAnalyticSlope
    {r : ℕ} (B : ℕ) (ell : Fin (r + 1) → ℂ) : ℕ :=
  Nat.ceil (3 + 2 * (B : ℝ) +
    2 * (B : ℝ) * ∑ i : Fin r, ‖ell i.succ‖) + 1

lemma boxAnalyticSlope_pos
    {r : ℕ} (B : ℕ) (ell : Fin (r + 1) → ℂ) :
    0 < boxAnalyticSlope B ell := by
  unfold boxAnalyticSlope
  omega

lemma boxAnalyticCoordinateBound_le_slope
    {r B K : ℕ} (ell : Fin (r + 1) → ℂ) (hK : 0 < K) :
    boxAnalyticCoordinateBound B K ell ≤
      boxAnalyticSlope B ell * K := by
  let E : ℝ := ∑ i : Fin r, ‖ell i.succ‖
  let s : ℝ := 3 + 2 * (B : ℝ) + 2 * (B : ℝ) * E
  have hKone : 1 ≤ K := hK
  have hmoment : (boxMomentCoordinateBound B K : ℝ) ≤
      (1 + 2 * (B : ℝ)) * K := by
    rw [boxMomentCoordinateBound, Nat.cast_max, Nat.cast_mul,
      Nat.cast_mul]
    apply max_le
    · apply le_mul_of_one_le_left (by positivity)
      nlinarith [show (0 : ℝ) ≤ B by positivity]
    · apply mul_le_mul_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ K)
      norm_num
  have hthird : (((2 * B * K : ℕ) : ℝ) * E) ≤
      (2 * (B : ℝ) * E) * K := by
    push_cast
    ring_nf
    exact le_rfl
  have hinner :
      max 1 (max (boxMomentCoordinateBound B K : ℝ)
        (((2 * B * K : ℕ) : ℝ) * E)) ≤ (s - 1) * K := by
    apply max_le
    · dsimp [s]
      have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hKone
      nlinarith [show 0 ≤ E by dsimp [E]; positivity,
        show (0 : ℝ) ≤ B by positivity]
    · apply max_le
      · exact hmoment.trans (by
          dsimp [s]
          have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hKone
          have hE : 0 ≤ E := by dsimp [E]; positivity
          nlinarith [mul_nonneg hE (show (0 : ℝ) ≤ B by positivity)])
      · exact hthird.trans (by
          dsimp [s]
          have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hKone
          have hE : 0 ≤ E := by dsimp [E]; positivity
          nlinarith [mul_nonneg hE (show (0 : ℝ) ≤ B by positivity)])
  have hceil : (boxAnalyticCoordinateBound B K ell : ℝ) ≤
      max 1 (max (boxMomentCoordinateBound B K : ℝ)
        (((2 * B * K : ℕ) : ℝ) * E)) + 1 := by
    unfold boxAnalyticCoordinateBound
    exact (Nat.ceil_lt_add_one (by positivity : 0 ≤
      max 1 (max (boxMomentCoordinateBound B K : ℝ)
        (((2 * B * K : ℕ) : ℝ) * E)))).le
  have hsceil : s ≤ (boxAnalyticSlope B ell : ℝ) := by
    unfold boxAnalyticSlope
    push_cast
    exact (Nat.le_ceil s).trans (by linarith)
  have hfinal : (boxAnalyticCoordinateBound B K ell : ℝ) ≤
      (boxAnalyticSlope B ell : ℝ) * K := by
    calc
      (boxAnalyticCoordinateBound B K ell : ℝ) ≤
          max 1 (max (boxMomentCoordinateBound B K : ℝ)
            (((2 * B * K : ℕ) : ℝ) * E)) + 1 := hceil
      _ ≤ (s - 1) * K + 1 := by linarith
      _ ≤ s * K := by
        have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hKone
        linarith
      _ ≤ (boxAnalyticSlope B ell : ℝ) * K := by
        gcongr
  exact_mod_cast hfinal


lemma boxMomentCoordinateBound_le_poly
    {B K : ℕ} :
    boxMomentCoordinateBound B K ≤ (2 * B + 1) * K := by
  rw [boxMomentCoordinateBound, max_le_iff]
  constructor <;> nlinarith

lemma structured_initial_entry_height_le
    {r d B L : ℕ} (Halpha cMoment : ℝ)
    (hr : r ≤ 8) (hd : d ≤ 8) (hHalpha : 0 ≤ Halpha)
    (hcMoment : 0 ≤ cMoment)
    (hL : 2 ≤ L) (hlogL : 1 ≤ Real.log (L : ℝ)) :
    Real.log (boxMomentCoordinateBound B (L ^ 32) : ℝ) ≤
      cMoment * Real.log (L : ℝ) →
    let K := L ^ 32
    let P := L ^ 24
    let A := L ^ 2
    let spend := L ^ 33
    let m := dyadicStageCount (K ^ (r + 1) * P)
    let W := m * spend + 1
    let T := m + 1
    let S := W
    let V := boxMomentCoordinateBound B K
    (d : ℝ) * Real.log ((W.factorial * (A + P) ^ P : ℕ) : ℝ) +
        (A : ℝ) * ((K : ℝ) * Halpha) +
        ((T + r * S : ℕ) : ℝ) * ((d : ℝ) * Real.log (V : ℝ)) ≤
      (8 * (314 * (314 + 34) + 26) + Halpha +
          (314 * 9) * 8 * cMoment : ℝ) *
        (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
  intro hlogMoment
  dsimp only
  let m := dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24)
  let W := m * L ^ 33 + 1
  let T := m + 1
  have hb := box_parameter_budget_bounds hr hL
  dsimp only at hb
  have hW : W ≤ 314 * L ^ 34 := by simpa [W, m] using hb.2.1
  have hT : T ≤ 314 * L := by simpa [T, m] using hb.2.2
  have hWpos : 0 < W := by dsimp [W]; omega
  have hLpos : 0 < L := by omega
  have hLone : 1 ≤ L := by omega
  have hlogPos : 0 < Real.log (L : ℝ) := lt_of_lt_of_le zero_lt_one hlogL
  have hfac := log_nat_factorial_le_poly hWpos (by norm_num : 0 < 314)
    hLpos hlogL hW
  have hsum : L ^ 2 + L ^ 24 ≤ 2 * L ^ 24 := by
    have hp : L ^ 2 ≤ L ^ 24 :=
      Nat.pow_le_pow_right hLone (by omega)
    omega
  have hlogsum := log_nat_le_poly
    (n := L ^ 2 + L ^ 24) (c := 2) (e := 24)
    (by positivity) (by norm_num) hLpos hlogL hsum
  have hfacprod :
      Real.log (((W.factorial * (L ^ 2 + L ^ 24) ^ L ^ 24 : ℕ) : ℝ)) ≤
        (314 * (314 + 34) + 26 : ℕ) *
          (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
    have hfacR : (0 : ℝ) < W.factorial := by positivity
    have hsumR : (0 : ℝ) < ((L ^ 2 + L ^ 24 : ℕ) : ℝ) := by positivity
    have hsumCast : (((L ^ 2 + L ^ 24 : ℕ) : ℝ)) =
        (L : ℝ) ^ 2 + (L : ℝ) ^ 24 := by
      simp only [Nat.cast_add, Nat.cast_pow]
    rw [Nat.cast_mul, Nat.cast_pow,
      Real.log_mul hfacR.ne' (pow_ne_zero _ hsumR.ne'), Real.log_pow]
    rw [hsumCast]
    push_cast
    have hpowterm :
        (L : ℝ) ^ 24 * Real.log ((L : ℝ) ^ 2 + (L : ℝ) ^ 24) ≤
          26 * (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
      have hLpow : (L : ℝ) ^ 24 ≤ (L : ℝ) ^ 34 := by
        exact pow_le_pow_right₀ (by exact_mod_cast hLone) (by omega)
      calc
        (L : ℝ) ^ 24 * Real.log ((L : ℝ) ^ 2 + (L : ℝ) ^ 24) ≤
            (L : ℝ) ^ 24 * (26 * Real.log (L : ℝ)) := by
          push_cast
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hlogsum' := hlogsum
          norm_num [Nat.cast_add, Nat.cast_pow] at hlogsum' ⊢
          exact hlogsum'
        _ ≤ (L : ℝ) ^ 34 * (26 * Real.log (L : ℝ)) := by
          gcongr
        _ = 26 * (L : ℝ) ^ 34 * Real.log (L : ℝ) := by ring
    calc
      Real.log (W.factorial : ℝ) +
          (L : ℝ) ^ 24 * Real.log ((L : ℝ) ^ 2 + (L : ℝ) ^ 24) ≤
        (314 * (314 + 34) : ℕ) * (L : ℝ) ^ 34 * Real.log (L : ℝ) +
          26 * (L : ℝ) ^ 34 * Real.log (L : ℝ) :=
        add_le_add hfac hpowterm
      _ = (314 * (314 + 34) + 26 : ℕ) *
          (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
        push_cast
        ring
  have hAK : ((L ^ 2 : ℕ) : ℝ) * (((L ^ 32 : ℕ) : ℝ) * Halpha) =
      Halpha * (L : ℝ) ^ 34 := by
    push_cast
    ring
  have hTLS : T + r * W ≤ 314 * 9 * L ^ 34 := by
    have hL34 : L ≤ L ^ 34 := by
      simpa using Nat.pow_le_pow_right hLone (show 1 ≤ 34 by omega)
    calc
      T + r * W ≤ 314 * L + 8 * (314 * L ^ 34) := by gcongr
      _ ≤ 314 * L ^ 34 + 8 * (314 * L ^ 34) := by gcongr
      _ = 314 * 9 * L ^ 34 := by ring
  have hTLSterm :
      ((T + r * W : ℕ) : ℝ) *
          ((d : ℝ) * Real.log (boxMomentCoordinateBound B (L ^ 32) : ℝ)) ≤
        ((314 * 9 : ℕ) : ℝ) * (L : ℝ) ^ 34 *
          (8 * cMoment * Real.log (L : ℝ)) := by
    apply mul_le_mul (by exact_mod_cast hTLS) ?_ (by positivity) (by positivity)
    have hVone := one_le_boxMomentCoordinateBound
      (B := B) (show 0 < L ^ 32 by positivity)
    have hlogV0 : 0 ≤
        Real.log (boxMomentCoordinateBound B (L ^ 32) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hVone)
    have hdR : (d : ℝ) ≤ 8 := by exact_mod_cast hd
    calc
      (d : ℝ) * Real.log (boxMomentCoordinateBound B (L ^ 32) : ℝ) ≤
          8 * Real.log (boxMomentCoordinateBound B (L ^ 32) : ℝ) :=
        mul_le_mul_of_nonneg_right hdR hlogV0
      _ ≤ 8 * (cMoment * Real.log (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogMoment (by norm_num)
      _ = 8 * cMoment * Real.log (L : ℝ) := by ring
  rw [hAK]
  have hfirst := mul_le_mul_of_nonneg_left hfacprod
    (by positivity : (0 : ℝ) ≤ d)
  have hfirst' :
      (d : ℝ) *
          Real.log (((W.factorial * (L ^ 2 + L ^ 24) ^ L ^ 24 : ℕ) : ℝ)) ≤
        8 * (314 * (314 + 34) + 26 : ℕ) *
          (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
    have hdR : (d : ℝ) ≤ 8 := by exact_mod_cast hd
    calc
      _ ≤ (d : ℝ) * ((314 * (314 + 34) + 26 : ℕ) *
          (L : ℝ) ^ 34 * Real.log (L : ℝ)) := hfirst
      _ ≤ 8 * ((314 * (314 + 34) + 26 : ℕ) *
          (L : ℝ) ^ 34 * Real.log (L : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hdR (by positivity)
      _ = _ := by ring
  calc
    (d : ℝ) *
          Real.log (((W.factorial * (L ^ 2 + L ^ 24) ^ L ^ 24 : ℕ) : ℝ)) +
        Halpha * (L : ℝ) ^ 34 +
        ((T + r * W : ℕ) : ℝ) *
          ((d : ℝ) * Real.log (boxMomentCoordinateBound B (L ^ 32) : ℝ)) ≤
      8 * (314 * (314 + 34) + 26 : ℕ) *
          (L : ℝ) ^ 34 * Real.log (L : ℝ) +
        Halpha * (L : ℝ) ^ 34 * Real.log (L : ℝ) +
        ((314 * 9 : ℕ) : ℝ) * (L : ℝ) ^ 34 *
          (8 * cMoment * Real.log (L : ℝ)) := by
      apply add_le_add
      · apply add_le_add hfirst'
        exact le_mul_of_one_le_right (mul_nonneg hHalpha (by positivity)) hlogL
      · exact hTLSterm
    _ = _ := by
      push_cast
      ring


lemma boxMomentCoordinateBound_le_poly_duplicate
    {B K : ℕ} :
    boxMomentCoordinateBound B K ≤ (2 * B + 1) * K := by
  rw [boxMomentCoordinateBound, max_le_iff]
  constructor <;> nlinarith

lemma structured_initial_entry_height_le_duplicate
    {r d B L : ℕ} (Halpha : ℝ)
    (hr : r ≤ 8) (hd : d ≤ 8) (hHalpha : 0 ≤ Halpha)
    (hL : 2 ≤ L) (hlogL : 1 ≤ Real.log (L : ℝ)) :
    let K := L ^ 32
    let P := L ^ 24
    let A := L ^ 2
    let spend := L ^ 33
    let m := dyadicStageCount (K ^ (r + 1) * P)
    let W := m * spend + 1
    let T := m + 1
    let S := W
    let V := boxMomentCoordinateBound B K
    (d : ℝ) * Real.log ((W.factorial * (A + P) ^ P : ℕ) : ℝ) +
        (A : ℝ) * ((K : ℝ) * Halpha) +
        ((T + r * S : ℕ) : ℝ) * ((d : ℝ) * Real.log (V : ℝ)) ≤
      (8 * (314 * (314 + 34) + 26) + Halpha +
          (314 * 9) * 8 * ((2 * B + 1 : ℕ) + 32) : ℝ) *
        (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
  dsimp only
  let m := dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24)
  let W := m * L ^ 33 + 1
  let T := m + 1
  have hb := box_parameter_budget_bounds hr hL
  dsimp only at hb
  have hW : W ≤ 314 * L ^ 34 := by simpa [W, m] using hb.2.1
  have hT : T ≤ 314 * L := by simpa [T, m] using hb.2.2
  have hWpos : 0 < W := by dsimp [W]; omega
  have hLpos : 0 < L := by omega
  have hLone : 1 ≤ L := by omega
  have hlogPos : 0 < Real.log (L : ℝ) := lt_of_lt_of_le zero_lt_one hlogL
  have hfac := log_nat_factorial_le_poly hWpos (by norm_num : 0 < 314)
    hLpos hlogL hW
  have hsum : L ^ 2 + L ^ 24 ≤ 2 * L ^ 24 := by
    have hp : L ^ 2 ≤ L ^ 24 :=
      Nat.pow_le_pow_right hLone (by omega)
    omega
  have hlogsum := log_nat_le_poly
    (n := L ^ 2 + L ^ 24) (c := 2) (e := 24)
    (by positivity) (by norm_num) hLpos hlogL hsum
  have hfacprod :
      Real.log (((W.factorial * (L ^ 2 + L ^ 24) ^ L ^ 24 : ℕ) : ℝ)) ≤
        (314 * (314 + 34) + 26 : ℕ) *
          (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
    have hfacR : (0 : ℝ) < W.factorial := by positivity
    have hsumR : (0 : ℝ) < ((L ^ 2 + L ^ 24 : ℕ) : ℝ) := by positivity
    have hsumCast : (((L ^ 2 + L ^ 24 : ℕ) : ℝ)) =
        (L : ℝ) ^ 2 + (L : ℝ) ^ 24 := by
      simp only [Nat.cast_add, Nat.cast_pow]
    rw [Nat.cast_mul, Nat.cast_pow,
      Real.log_mul hfacR.ne' (pow_ne_zero _ hsumR.ne'), Real.log_pow]
    rw [hsumCast]
    push_cast
    have hpowterm :
        (L : ℝ) ^ 24 * Real.log ((L : ℝ) ^ 2 + (L : ℝ) ^ 24) ≤
          26 * (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
      have hLpow : (L : ℝ) ^ 24 ≤ (L : ℝ) ^ 34 := by
        exact pow_le_pow_right₀ (by exact_mod_cast hLone) (by omega)
      calc
        (L : ℝ) ^ 24 * Real.log ((L : ℝ) ^ 2 + (L : ℝ) ^ 24) ≤
            (L : ℝ) ^ 24 * (26 * Real.log (L : ℝ)) := by
          push_cast
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hlogsum' := hlogsum
          norm_num [Nat.cast_add, Nat.cast_pow] at hlogsum' ⊢
          exact hlogsum'
        _ ≤ (L : ℝ) ^ 34 * (26 * Real.log (L : ℝ)) := by
          gcongr
        _ = 26 * (L : ℝ) ^ 34 * Real.log (L : ℝ) := by ring
    calc
      Real.log (W.factorial : ℝ) +
          (L : ℝ) ^ 24 * Real.log ((L : ℝ) ^ 2 + (L : ℝ) ^ 24) ≤
        (314 * (314 + 34) : ℕ) * (L : ℝ) ^ 34 * Real.log (L : ℝ) +
          26 * (L : ℝ) ^ 34 * Real.log (L : ℝ) :=
        add_le_add hfac hpowterm
      _ = (314 * (314 + 34) + 26 : ℕ) *
          (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
        push_cast
        ring
  have hAK : ((L ^ 2 : ℕ) : ℝ) * (((L ^ 32 : ℕ) : ℝ) * Halpha) =
      Halpha * (L : ℝ) ^ 34 := by
    push_cast
    ring
  have hTLS : T + r * W ≤ 314 * 9 * L ^ 34 := by
    have hL34 : L ≤ L ^ 34 := by
      simpa using Nat.pow_le_pow_right hLone (show 1 ≤ 34 by omega)
    calc
      T + r * W ≤ 314 * L + 8 * (314 * L ^ 34) := by gcongr
      _ ≤ 314 * L ^ 34 + 8 * (314 * L ^ 34) := by gcongr
      _ = 314 * 9 * L ^ 34 := by ring
  have hV : boxMomentCoordinateBound B (L ^ 32) ≤
      (2 * B + 1) * L ^ 32 := boxMomentCoordinateBound_le_poly
  have hVpos : 0 < boxMomentCoordinateBound B (L ^ 32) := by
    exact lt_of_lt_of_le (by positivity : 0 < L ^ 32)
      (le_max_left _ _)
  have hlogV := log_nat_le_poly hVpos (by omega : 0 < 2 * B + 1)
    hLpos hlogL hV
  have hTLSterm :
      ((T + r * W : ℕ) : ℝ) *
          ((d : ℝ) * Real.log (boxMomentCoordinateBound B (L ^ 32) : ℝ)) ≤
        ((314 * 9 : ℕ) : ℝ) * (L : ℝ) ^ 34 *
          (8 * (((2 * B + 1 : ℕ) + 32 : ℕ) : ℝ) *
            Real.log (L : ℝ)) := by
    apply mul_le_mul (by exact_mod_cast hTLS) ?_ (by positivity) (by positivity)
    have hVone := one_le_boxMomentCoordinateBound
      (B := B) (show 0 < L ^ 32 by positivity)
    have hlogV0 : 0 ≤
        Real.log (boxMomentCoordinateBound B (L ^ 32) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hVone)
    have hdR : (d : ℝ) ≤ 8 := by exact_mod_cast hd
    calc
      (d : ℝ) * Real.log (boxMomentCoordinateBound B (L ^ 32) : ℝ) ≤
          8 * Real.log (boxMomentCoordinateBound B (L ^ 32) : ℝ) :=
        mul_le_mul_of_nonneg_right hdR hlogV0
      _ ≤ 8 * (((2 * B + 1 : ℕ) + 32 : ℕ) * Real.log (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogV (by norm_num)
      _ = 8 * (((2 * B + 1 : ℕ) + 32 : ℕ) : ℝ) *
          Real.log (L : ℝ) := by ring
  rw [hAK]
  have hfirst := mul_le_mul_of_nonneg_left hfacprod
    (by positivity : (0 : ℝ) ≤ d)
  have hfirst' :
      (d : ℝ) *
          Real.log (((W.factorial * (L ^ 2 + L ^ 24) ^ L ^ 24 : ℕ) : ℝ)) ≤
        8 * (314 * (314 + 34) + 26 : ℕ) *
          (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
    have hdR : (d : ℝ) ≤ 8 := by exact_mod_cast hd
    calc
      _ ≤ (d : ℝ) * ((314 * (314 + 34) + 26 : ℕ) *
          (L : ℝ) ^ 34 * Real.log (L : ℝ)) := hfirst
      _ ≤ 8 * ((314 * (314 + 34) + 26 : ℕ) *
          (L : ℝ) ^ 34 * Real.log (L : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hdR (by positivity)
      _ = _ := by ring
  calc
    (d : ℝ) *
          Real.log (((W.factorial * (L ^ 2 + L ^ 24) ^ L ^ 24 : ℕ) : ℝ)) +
        Halpha * (L : ℝ) ^ 34 +
        ((T + r * W : ℕ) : ℝ) *
          ((d : ℝ) * Real.log (boxMomentCoordinateBound B (L ^ 32) : ℝ)) ≤
      8 * (314 * (314 + 34) + 26 : ℕ) *
          (L : ℝ) ^ 34 * Real.log (L : ℝ) +
        Halpha * (L : ℝ) ^ 34 * Real.log (L : ℝ) +
        ((314 * 9 : ℕ) : ℝ) * (L : ℝ) ^ 34 *
          (8 * (((2 * B + 1 : ℕ) + 32 : ℕ) : ℝ) *
            Real.log (L : ℝ)) := by
      apply add_le_add
      · apply add_le_add hfirst'
        exact le_mul_of_one_le_right (mul_nonneg hHalpha (by positivity)) hlogL
      · exact hTLSterm
    _ = _ := by
      push_cast
      ring


lemma boxPochhammerStructuredCoefficientMajorant_cast_le
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) {M : ℝ}
    {r B K P A W T S : ℕ} (alpha : Fin (r + 1) → F)
    (hK : 0 < K) (hP : 0 < P) (hA : 0 < A) (hW : 0 < W)
    (hM : 1 ≤ M)
    (hhalf : 2 * ((A * W * T * S ^ r) * Fintype.card ι) ≤
      K ^ (r + 1) * P) :
    let Halpha := ∑ i, Height.logHeight₁ (alpha i)
    let V := boxMomentCoordinateBound B K
    let Hentry : ℝ :=
      (Module.finrank ℚ F : ℝ) *
          Real.log ((W.factorial * (A + P) ^ P : ℕ) : ℝ) +
        (A : ℝ) * ((K : ℝ) * Halpha) +
        ((T + r * S : ℕ) : ℝ) *
          ((Module.finrank ℚ F : ℝ) * Real.log (V : ℝ))
    let Qbound : ℝ :=
      (Real.exp Halpha ^ (r + 1)) ^ ((r + 1) * K * A)
    (boxPochhammerStructuredCoefficientMajorant
      basis M r B K P A W T S alpha : ℝ) ≤
      2 * (K ^ (r + 1) * P : ℕ) *
        ((Module.finrank ℚ F : ℝ) * Qbound * Real.exp Hentry * M) := by
  dsimp only
  let Halpha : ℝ := ∑ i, Height.logHeight₁ (alpha i)
  let V := boxMomentCoordinateBound B K
  let Hentry : ℝ :=
      (Module.finrank ℚ F : ℝ) *
          Real.log ((W.factorial * (A + P) ^ P : ℕ) : ℝ) +
        (A : ℝ) * ((K : ℝ) * Halpha) +
        ((T + r * S : ℕ) : ℝ) *
          ((Module.finrank ℚ F : ℝ) * Real.log (V : ℝ))
  let Qbound : ℝ :=
    (Real.exp Halpha ^ (r + 1)) ^ ((r + 1) * K * A)
  have hHalpha : 0 ≤ Halpha := by
    dsimp [Halpha]
    positivity
  have hV : 1 ≤ V := one_le_boxMomentCoordinateBound hK
  have hfac : 1 ≤ W.factorial * (A + P) ^ P :=
    one_le_mul_of_one_le_of_one_le
      (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero W))
      (Nat.one_le_pow _ _ (by omega))
  have hHentry : 0 ≤ Hentry := by
    dsimp [Hentry]
    have hlogfac : 0 ≤
        Real.log ((W.factorial * (A + P) ^ P : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hfac)
    have hlogV : 0 ≤ Real.log (V : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hV)
    positivity
  have hQbound : 1 ≤ Qbound := by
    dsimp [Qbound]
    have he : 1 ≤ Real.exp Halpha := by
      simpa using Real.exp_le_exp.mpr hHalpha
    exact one_le_pow₀ (one_le_pow₀ he)
  have hd : Fintype.card ι = Module.finrank ℚ F := by
    rw [← Module.finrank_eq_card_basis basis]
  have hgeneric :=
    structuredKernelCoefficientMajorant_cast_le
      (rows := A * W * T * S ^ r) (cols := K ^ (r + 1) * P)
      (d := Fintype.card ι) (Q := Qbound) (H := Hentry) (M := M)
      (by positivity)
      (by
        rw [hd]
        exact_mod_cast Module.finrank_pos (R := ℚ) (M := F))
      hQbound hHentry hM hhalf
  simpa [boxPochhammerStructuredCoefficientMajorant,
    Halpha, V, Hentry, Qbound, hd] using hgeneric

lemma structured_initial_coefficient_log_le
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (M cM cMoment : ℝ)
    {r B L : ℕ} (alpha : Fin (r + 1) → F)
    (hr : r ≤ 8) (hd : Module.finrank ℚ F ≤ 8)
    (hL : 2 ≤ L) (hlogL : 1 ≤ Real.log (L : ℝ)) (hM : 1 ≤ M)
    (hcM : 0 ≤ cM) (hlogM : Real.log M ≤ cM * Real.log (L : ℝ))
    (hcMoment : 0 ≤ cMoment)
    (hlogMoment : Real.log (boxMomentCoordinateBound B (L ^ 32) : ℝ) ≤
      cMoment * Real.log (L : ℝ))
    (hhalf :
      let K := L ^ 32
      let P := L ^ 24
      let A := L ^ 2
      let spend := L ^ 33
      let m := dyadicStageCount (K ^ (r + 1) * P)
      2 * ((A * (m * spend + 1) * (m + 1) *
          (m * spend + 1) ^ r) * Fintype.card ι) ≤
        K ^ (r + 1) * P) :
    let K := L ^ 32
    let P := L ^ 24
    let A := L ^ 2
    let spend := L ^ 33
    let m := dyadicStageCount (K ^ (r + 1) * P)
    let W := m * spend + 1
    let T := m + 1
    let S := W
    let Halpha := ∑ i, Height.logHeight₁ (alpha i)
    let cH : ℝ := 8 * (314 * (314 + 34) + 26) + Halpha +
      (314 * 9) * 8 * cMoment
    Real.log (boxPochhammerStructuredCoefficientMajorant
        basis M r B K P A W T S alpha : ℝ) ≤
      (2 + 312 + 8 + cM + 81 * Halpha + cH) *
        (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
  dsimp only
  let K := L ^ 32
  let P := L ^ 24
  let A := L ^ 2
  let spend := L ^ 33
  let m := dyadicStageCount (K ^ (r + 1) * P)
  let W := m * spend + 1
  let T := m + 1
  let S := W
  let Halpha : ℝ := ∑ i, Height.logHeight₁ (alpha i)
  let V := boxMomentCoordinateBound B K
  let Hentry : ℝ :=
    (Module.finrank ℚ F : ℝ) *
        Real.log ((W.factorial * (A + P) ^ P : ℕ) : ℝ) +
      (A : ℝ) * ((K : ℝ) * Halpha) +
      ((T + r * S : ℕ) : ℝ) *
        ((Module.finrank ℚ F : ℝ) * Real.log (V : ℝ))
  let Qbound : ℝ :=
    (Real.exp Halpha ^ (r + 1)) ^ ((r + 1) * K * A)
  let cH : ℝ := 8 * (314 * (314 + 34) + 26) + Halpha +
    (314 * 9) * 8 * cMoment
  have hHalpha : 0 ≤ Halpha := by dsimp [Halpha]; positivity
  have hLpos : 0 < L := by omega
  have hLone : 1 ≤ L := by omega
  have hlogPos : 0 < Real.log (L : ℝ) := lt_of_lt_of_le zero_lt_one hlogL
  have hHentry : Hentry ≤ cH * (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
    dsimp [Hentry, cH, Halpha, K, P, A, W, T, S, m, spend, V]
    exact structured_initial_entry_height_le
      (∑ i, Height.logHeight₁ (alpha i)) cMoment hr hd hHalpha hcMoment
      hL hlogL hlogMoment
  have hhalf' : 2 * ((A * W * T * S ^ r) * Fintype.card ι) ≤
      K ^ (r + 1) * P := by
    simpa [A, W, T, S, K, P, m, spend] using hhalf
  have hK : 0 < K := by dsimp [K]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hW : 0 < W := by dsimp [W]; omega
  have hCcast := boxPochhammerStructuredCoefficientMajorant_cast_le
    (B := B) basis alpha hK hP hA hW hM hhalf'
  dsimp only at hCcast
  change
    (boxPochhammerStructuredCoefficientMajorant
      basis M r B K P A W T S alpha : ℝ) ≤
        2 * (K ^ (r + 1) * P : ℕ) *
          ((Module.finrank ℚ F : ℝ) * Qbound * Real.exp Hentry * M)
    at hCcast
  let C := boxPochhammerStructuredCoefficientMajorant
    basis M r B K P A W T S alpha
  have hCpos : (0 : ℝ) < C := by
    exact_mod_cast one_le_boxPochhammerStructuredCoefficientMajorant
      basis M r B K P A W T S alpha
  have hdpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hQpos : 0 < Qbound := by dsimp [Qbound]; positivity
  have hRpos : 0 < 2 * (K ^ (r + 1) * P : ℕ) *
      ((Module.finrank ℚ F : ℝ) * Qbound * Real.exp Hentry * M) := by
    positivity
  have hlogC : Real.log (C : ℝ) ≤
      Real.log (2 * (K ^ (r + 1) * P : ℕ) *
        ((Module.finrank ℚ F : ℝ) * Qbound * Real.exp Hentry * M)) :=
    Real.log_le_log hCpos (by simpa [C] using hCcast)
  have hcolslog :
      Real.log ((K ^ (r + 1) * P : ℕ) : ℝ) =
        (32 * (r + 1) + 24 : ℕ) * Real.log (L : ℝ) := by
    dsimp [K, P]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_pow, Real.log_pow]
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  have hexpBound : 32 * (r + 1) + 24 ≤ 312 := by omega
  have hcolslogBound :
      Real.log ((K ^ (r + 1) * P : ℕ) : ℝ) ≤
        312 * Real.log (L : ℝ) := by
    rw [hcolslog]
    gcongr
    exact_mod_cast hexpBound
  have hdlog : Real.log (Module.finrank ℚ F : ℝ) ≤
      8 * Real.log (L : ℝ) := by
    calc
      Real.log (Module.finrank ℚ F : ℝ) ≤ (Module.finrank ℚ F : ℝ) := by
        exact (Real.log_le_sub_one_of_pos (by exact_mod_cast hdpos)).trans (by linarith)
      _ ≤ 8 := by exact_mod_cast hd
      _ ≤ 8 * Real.log (L : ℝ) := by nlinarith
  have hQlog : Real.log Qbound ≤
      81 * Halpha * (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
    have hbase : 0 < Real.exp Halpha := Real.exp_pos _
    dsimp [Qbound]
    rw [Real.log_pow, Real.log_pow, Real.log_exp]
    have hr1 : r + 1 ≤ 9 := by omega
    have hcastR : ((r + 1 : ℕ) : ℝ) ≤ 9 := by exact_mod_cast hr1
    have hcastR' : (r : ℝ) + 1 ≤ 9 := by exact_mod_cast hr1
    have hKA : (K : ℝ) * (A : ℝ) = (L : ℝ) ^ 34 := by
      dsimp [K, A]
      push_cast
      ring
    rw [show ((r + 1) * K * A : ℕ) = (r + 1) * (K * A) by ring]
    push_cast
    rw [hKA]
    calc
      ((r : ℝ) + 1) * (L : ℝ) ^ 34 *
          (((r : ℝ) + 1) * Halpha) =
        (((r : ℝ) + 1) * ((r : ℝ) + 1)) *
          Halpha * (L : ℝ) ^ 34 := by ring
      _ ≤ 81 * Halpha * (L : ℝ) ^ 34 := by
        gcongr
        nlinarith [hcastR']
      _ ≤ 81 * Halpha * (L : ℝ) ^ 34 * Real.log (L : ℝ) :=
        le_mul_of_one_le_right (by positivity) hlogL
  have hlogTwo : Real.log 2 ≤ 2 * Real.log (L : ℝ) := by
    have hlog2 : Real.log 2 ≤ 2 :=
      (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans (by norm_num)
    exact hlog2.trans (by nlinarith)
  have hlogExpand :
      Real.log (2 * (K ^ (r + 1) * P : ℕ) *
        ((Module.finrank ℚ F : ℝ) * Qbound * Real.exp Hentry * M)) =
      Real.log 2 + Real.log ((K ^ (r + 1) * P : ℕ) : ℝ) +
      Real.log (Module.finrank ℚ F : ℝ) + Real.log Qbound + Hentry +
        Real.log M := by
    have hcols0 : (((K ^ (r + 1) * P : ℕ) : ℝ)) ≠ 0 := by positivity
    have hd0 : ((Module.finrank ℚ F : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast hdpos.ne'
    have hM0 : M ≠ 0 := (lt_of_lt_of_le zero_lt_one hM).ne'
    calc
      Real.log (2 * (K ^ (r + 1) * P : ℕ) *
          ((Module.finrank ℚ F : ℝ) * Qbound * Real.exp Hentry * M)) =
        Real.log (2 * (K ^ (r + 1) * P : ℕ)) +
          Real.log ((Module.finrank ℚ F : ℝ) * Qbound *
            Real.exp Hentry * M) := by
              rw [Real.log_mul (mul_ne_zero (by norm_num) hcols0)
                (mul_ne_zero (mul_ne_zero (mul_ne_zero hd0 hQpos.ne')
                  (Real.exp_ne_zero _)) hM0)]
      _ = (Real.log 2 + Real.log ((K ^ (r + 1) * P : ℕ) : ℝ)) +
          (Real.log ((Module.finrank ℚ F : ℝ) * Qbound *
            Real.exp Hentry) + Real.log M) := by
              rw [Real.log_mul (by norm_num) hcols0,
                Real.log_mul (mul_ne_zero (mul_ne_zero hd0 hQpos.ne')
                  (Real.exp_ne_zero _)) hM0]
      _ = _ := by
        rw [Real.log_mul (mul_ne_zero hd0 hQpos.ne') (Real.exp_ne_zero _),
          Real.log_mul hd0 hQpos.ne', Real.log_exp]
        ring
  have hsmall :
      Real.log 2 + Real.log ((K ^ (r + 1) * P : ℕ) : ℝ) +
          Real.log (Module.finrank ℚ F : ℝ) + Real.log Qbound + Hentry +
          Real.log M ≤
        (2 + 312 + 8 + cM + 81 * Halpha + cH) *
          (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
    have hpowOne : (1 : ℝ) ≤ (L : ℝ) ^ 34 := one_le_pow₀ (by exact_mod_cast hLone)
    have hsmallCoeff : (0 : ℝ) ≤ 2 + 312 + 8 + cM := by positivity
    calc
      _ ≤ (2 + 312 + 8 + cM) * Real.log (L : ℝ) +
          (81 * Halpha + cH) * (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
        nlinarith
      _ ≤ (2 + 312 + 8 + cM) * (L : ℝ) ^ 34 * Real.log (L : ℝ) +
          (81 * Halpha + cH) * (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_right _ hlogPos.le
          simpa using mul_le_mul_of_nonneg_left hpowOne hsmallCoeff
        · exact le_rfl
      _ = _ := by ring
  exact hlogC.trans (hlogExpand.trans_le hsmall)


lemma degree_log_term_le
    {d n A L : ℕ} (hd : d ≤ 8) (hn : 1 ≤ n)
    (hbase : (1 : ℝ) ≤ (A : ℝ) * (L : ℝ) ^ 32)
    (hlogL0 : 0 ≤ Real.log (L : ℝ))
    (hlogn : Real.log (n : ℝ) ≤ 290 * Real.log (L : ℝ)) :
    (d : ℝ) * Real.log (n : ℝ) ≤
      2320 * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
  have hdR : (d : ℝ) ≤ 8 := by exact_mod_cast hd
  have hlogn0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  calc
    _ ≤ 8 * Real.log (n : ℝ) := mul_le_mul_of_nonneg_right hdR hlogn0
    _ ≤ 8 * (290 * Real.log (L : ℝ)) := by gcongr
    _ ≤ 2320 * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hbase) hlogL0]

lemma degree_bounded_log_term_le
    {d q : ℕ} {c base : ℝ} (hd : d ≤ 8) (hq : 1 ≤ q)
    (hlog : Real.log (q : ℝ) ≤ c * base) :
    (d : ℝ) * Real.log (q : ℝ) ≤ (8 * c) * base := by
  have hdR : (d : ℝ) ≤ 8 := by exact_mod_cast hd
  have hlog0 : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hq)
  calc
    _ ≤ 8 * Real.log (q : ℝ) := mul_le_mul_of_nonneg_right hdR hlog0
    _ ≤ 8 * (c * base) := by gcongr
    _ = _ := by ring

lemma height_term_le
    {A L : ℕ} {H : ℝ} (hH : 0 ≤ H) (hlogL : 1 ≤ Real.log (L : ℝ)) :
    2 * H * ((A : ℝ) * (L : ℝ) ^ 32) ≤
      2 * H * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
  calc
    _ ≤ 2 * H * ((A : ℝ) * (L : ℝ) ^ 32) * Real.log (L : ℝ) :=
      le_mul_of_one_le_right (by positivity) hlogL
    _ = _ := by ring

lemma sum_three_weighted_le
    {x y z a b c base : ℝ}
    (hx : x ≤ a * base) (hy : y ≤ b * base) (hz : z ≤ c * base) :
    x + y + z ≤ (a + b + c) * base := by
  linarith

lemma master_recombine
    {a c s x y : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    c * (a * x) + s * (a * y) ≤
      a * ((c + s) * x + (c + s) * y) := by
  nlinarith [mul_nonneg (mul_nonneg ha hc) hy,
    mul_nonneg (mul_nonneg ha hs) hx]

lemma combine_outer_inner
    {x y c p q r base tail : ℝ}
    (hx : x ≤ c * base + tail) (hy : y ≤ (p + q + r) * base) :
    x + y ≤ (c + p + q + r) * base + tail := by
  linarith

lemma coefficient_nonneg_of_log_bound
    {C L : ℕ} {c : ℝ} (hC : 0 < C) (hL : 0 < L)
    (hlogL : 0 < Real.log (L : ℝ))
    (hlog : Real.log (C : ℝ) ≤ c * (L : ℝ) ^ 34 * Real.log (L : ℝ)) :
    0 ≤ c := by
  by_contra hc
  have hneg : c < 0 := lt_of_not_ge hc
  have hlogC0 : 0 ≤ Real.log (C : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ C by omega))
  have hp : c * (L : ℝ) ^ 34 * Real.log (L : ℝ) < 0 := by
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg (by positivity)) hlogL
  linarith

lemma outer_log_expansion
    {cols C V E W Y P : ℕ} {R U : ℝ}
    (hcols : 0 < cols) (hC : 0 < C) (hV : 0 < V) (hY : 0 < Y)
    (hRY : R + 1 + P = (Y : ℝ)) :
    Real.log
        ((cols : ℝ) *
          ((C : ℝ) * (V : ℝ) ^ E * (W.factorial : ℝ) *
            (R + 1 + P) ^ P * Real.exp (U * R))) =
      Real.log (cols : ℝ) + Real.log (C : ℝ) +
        (E : ℝ) * Real.log (V : ℝ) + Real.log (W.factorial : ℝ) +
        (P : ℝ) * Real.log (Y : ℝ) + U * R := by
  have hcols0 : (cols : ℝ) ≠ 0 := by exact_mod_cast hcols.ne'
  have hC0 : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hV0 : (V : ℝ) ≠ 0 := by exact_mod_cast hV.ne'
  have hW0 : (W.factorial : ℝ) ≠ 0 := by positivity
  have hY0 : (Y : ℝ) ≠ 0 := by exact_mod_cast hY.ne'
  rw [hRY]
  rw [Real.log_mul hcols0 (by positivity),
    Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hC0 (pow_ne_zero _ hV0)) hW0)
      (pow_ne_zero _ hY0)) (Real.exp_ne_zero _),
    Real.log_mul (mul_ne_zero (mul_ne_zero hC0 (pow_ne_zero _ hV0)) hW0)
      (pow_ne_zero _ hY0),
    Real.log_mul (mul_ne_zero hC0 (pow_ne_zero _ hV0)) hW0,
    Real.log_mul hC0 (pow_ne_zero _ hV0),
    Real.log_pow, Real.log_pow, Real.log_exp]
  ring

lemma inner_log_expansion
    {P C W Z V E : ℕ}
    (hP : 0 < P) (hC : 0 < C) (hZ : 0 < Z) (hV : 0 < V) :
    Real.log (P * C * W.factorial * Z ^ P * V ^ E : ℕ) =
      Real.log (P : ℝ) + Real.log (C : ℝ) +
        Real.log (W.factorial : ℝ) + (P : ℝ) * Real.log (Z : ℝ) +
        (E : ℝ) * Real.log (V : ℝ) := by
  have hP0 : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  have hC0 : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hW0 : (W.factorial : ℝ) ≠ 0 := by positivity
  have hZ0 : (Z : ℝ) ≠ 0 := by exact_mod_cast hZ.ne'
  have hV0 : (V : ℝ) ≠ 0 := by exact_mod_cast hV.ne'
  push_cast
  rw [Real.log_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hP0 hC0) hW0)
      (pow_ne_zero _ hZ0)) (pow_ne_zero _ hV0),
    Real.log_mul (mul_ne_zero (mul_ne_zero hP0 hC0) hW0) (pow_ne_zero _ hZ0),
    Real.log_mul (mul_ne_zero hP0 hC0) hW0,
    Real.log_mul hP0 hC0, Real.log_pow, Real.log_pow]

lemma structured_stage_log_growth_le
    {r L j C V d : ℕ} (ell : Fin (r + 1) → ℂ)
    (Halpha cC cV : ℝ)
    (hr : r ≤ 8) (hd : d ≤ 8) (hHalpha : 0 ≤ Halpha) (hcV : 0 ≤ cV)
    (hL : 2 ≤ L) (hlogL : 1 ≤ Real.log (L : ℝ))
    (hC : 0 < C) (hV : 0 < V)
    (hj : j < dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24))
    (hlogC : Real.log (C : ℝ) ≤
      cC * (L : ℝ) ^ 34 * Real.log (L : ℝ))
    (hlogV : Real.log (V : ℝ) ≤ cV * Real.log (L : ℝ)) :
    let N := (L ^ 32) ^ (r + 1)
    let P := L ^ 24
    let A := scaledDyadicStageA (L ^ 2) j
    let spend := L ^ 33
    let m := dyadicStageCount (N * P)
    let W := stageSpendBudget m spend (j + 1)
    let T := stageUnitBudget m (j + 1)
    let S := W
    let E := T + r * S
    let R : ℝ := (L : ℝ) * (2 * A : ℕ)
    let U : ℝ := (L ^ 32 : ℕ) * ∑ i, ‖ell i‖
    let X : ℝ :=
      d * Real.log (N + 1 : ℕ) +
        d * Real.log
          (P * C * W.factorial * (2 * A + P) ^ P * V ^ E : ℕ) +
        (2 * A : ℕ) * ((L ^ 32 : ℕ) * Halpha)
    let cFac : ℝ := 314 * (314 + 34)
    let cE : ℝ := 314 * 9
    let cLog : ℝ := 312 + cC + cE * cV + cFac + 321
    let cInner : ℝ := 24 + cC + cFac + 319 + cE * cV
    let cTotal : ℝ := cLog + 2320 + 8 * cInner + 2 * Halpha +
      2 * ∑ i, ‖ell i‖
    Real.log
        (((N * P : ℕ) : ℝ) *
          ((C : ℝ) * (V : ℝ) ^ E * (W.factorial : ℝ) *
            (R + 1 + P) ^ P * Real.exp (U * R))) + X ≤
      (A : ℝ) *
        (cTotal * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
          cTotal * (L : ℝ) ^ 33) := by
  dsimp only
  let N := (L ^ 32) ^ (r + 1)
  let P := L ^ 24
  let A := scaledDyadicStageA (L ^ 2) j
  let spend := L ^ 33
  let m := dyadicStageCount (N * P)
  let W := stageSpendBudget m spend (j + 1)
  let T := stageUnitBudget m (j + 1)
  let S := W
  let E := T + r * S
  let R : ℝ := (L : ℝ) * (2 * A : ℕ)
  let U : ℝ := (L ^ 32 : ℕ) * ∑ i, ‖ell i‖
  let cFac : ℝ := 314 * (314 + 34)
  let cE : ℝ := 314 * 9
  let cLog : ℝ := 312 + cC + cE * cV + cFac + 321
  let cInner : ℝ := 24 + cC + cFac + 319 + cE * cV
  let cTotal : ℝ := cLog + 2320 + 8 * cInner + 2 * Halpha +
    2 * ∑ i, ‖ell i‖
  have hLpos : 0 < L := by omega
  have hLone : 1 ≤ L := by omega
  have hlogPos : 0 < Real.log (L : ℝ) := lt_of_lt_of_le zero_lt_one hlogL
  have hN : 0 < N := by dsimp [N]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hA : 0 < A := by
    dsimp [A]
    exact scaledDyadicStageA_pos (by positivity) j
  have hAinit : L ^ 2 ≤ A := by
    dsimp [A, scaledDyadicStageA]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hAL32 : (L : ℝ) ^ 34 ≤ (A : ℝ) * (L : ℝ) ^ 32 := by
    have hcast : ((L ^ 2 : ℕ) : ℝ) ≤ (A : ℝ) := by exact_mod_cast hAinit
    have hcast' : (L : ℝ) ^ 2 ≤ (A : ℝ) := by
      simpa only [Nat.cast_pow] using hcast
    calc
      (L : ℝ) ^ 34 = (L : ℝ) ^ 2 * (L : ℝ) ^ 32 := by ring
      _ ≤ (A : ℝ) * (L : ℝ) ^ 32 := by
        exact mul_le_mul_of_nonneg_right hcast' (by positivity)
  have hb := box_parameter_budget_bounds hr hL
  dsimp only at hb
  have hWsrc : m * spend + 1 ≤ 314 * L ^ 34 := by
    simpa [m, N, P, spend] using hb.2.1
  have hTsrc : m + 1 ≤ 314 * L := by
    simpa [m, N, P] using hb.2.2
  have hWbd : W ≤ 314 * L ^ 34 :=
    (stageSpendBudget_le_zero m spend (j + 1)).trans hWsrc
  have hTbd : T ≤ 314 * L :=
    (stageUnitBudget_le_zero m (j + 1)).trans hTsrc
  have hWpos : 0 < W := by dsimp [W, stageSpendBudget]; omega
  have hTpos : 0 < T := by dsimp [T, stageUnitBudget]; omega
  have hEbd : E ≤ 314 * 9 * L ^ 34 := by
    have hL34 : L ≤ L ^ 34 := by
      simpa using Nat.pow_le_pow_right hLone (show 1 ≤ 34 by omega)
    dsimp [E, S]
    calc
      T + r * W ≤ 314 * L + 8 * (314 * L ^ 34) := by gcongr
      _ ≤ 314 * L ^ 34 + 8 * (314 * L ^ 34) := by gcongr
      _ = 314 * 9 * L ^ 34 := by ring
  have hlogV0 : 0 ≤ Real.log (V : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ V by omega))
  have hElogV : (E : ℝ) * Real.log (V : ℝ) ≤
      cE * cV * (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
    calc
      (E : ℝ) * Real.log (V : ℝ) ≤
          ((314 * 9 : ℕ) : ℝ) * (L : ℝ) ^ 34 *
            (cV * Real.log (L : ℝ)) := by
        apply mul_le_mul (by exact_mod_cast hEbd) hlogV hlogV0 (by positivity)
      _ = cE * cV * (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
        dsimp [cE]
        ring
  have hfac := log_nat_factorial_le_poly hWpos (by norm_num : 0 < 314)
    hLpos hlogL hWbd
  have hfac' : Real.log (W.factorial : ℝ) ≤
      cFac * (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
    dsimp [cFac]
    norm_num at hfac ⊢
    exact hfac
  have hAupper := scaledDyadicStageA_parameter_upper hL hj
  have hNpow : N * P ≤ L ^ 312 := by
    have he : 32 * (r + 1) + 24 ≤ 312 := by omega
    have heq : N * P = L ^ (32 * (r + 1) + 24) := by
      dsimp [N, P]
      rw [← pow_mul, ← pow_add]
    rw [heq]
    exact Nat.pow_le_pow_right hLone he
  have hApoly : A ≤ 2 * L ^ 314 := by
    have hAstep : A ≤ scaledDyadicStageA (L ^ 2) (j + 1) := by
      dsimp [A, scaledDyadicStageA]
      exact Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by omega) (Nat.le_succ j))
    calc
      A ≤ scaledDyadicStageA (L ^ 2) (j + 1) := hAstep
      _ ≤ 2 * L ^ 2 * (N * P) := by simpa [N, P] using hAupper
      _ ≤ 2 * L ^ 2 * L ^ 312 := by gcongr
      _ = 2 * L ^ 314 := by ring
  let Y : ℕ := L * (2 * A) + 1 + P
  have hYpos : 0 < Y := by dsimp [Y]; positivity
  have hYpoly : Y ≤ 6 * L ^ 315 := by
    have hPpoly : P ≤ L ^ 315 := by
      dsimp [P]
      exact Nat.pow_le_pow_right hLone (by omega)
    have hOne : 1 ≤ L ^ 315 := Nat.one_le_pow _ _ hLone
    dsimp [Y]
    calc
      L * (2 * A) + 1 + P ≤ L * (2 * (2 * L ^ 314)) + L ^ 315 + L ^ 315 := by
        gcongr
      _ = 6 * L ^ 315 := by ring
  have hlogY := log_nat_le_poly hYpos (by norm_num : 0 < 6)
    hLpos hlogL hYpoly
  have hPltAL32 : (P : ℝ) ≤ (A : ℝ) * (L : ℝ) ^ 32 := by
    have hp34 : (L : ℝ) ^ 24 ≤ (L : ℝ) ^ 34 :=
      pow_le_pow_right₀ (by exact_mod_cast hLone) (by omega)
    exact (by simpa [P] using hp34.trans hAL32)
  have hPlogY : (P : ℝ) * Real.log (Y : ℝ) ≤
      321 * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    calc
      (P : ℝ) * Real.log (Y : ℝ) ≤
          (P : ℝ) * (321 * Real.log (L : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        norm_num at hlogY ⊢
        exact hlogY
      _ ≤ ((A : ℝ) * (L : ℝ) ^ 32) *
          (321 * Real.log (L : ℝ)) := by gcongr
      _ = 321 * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by ring
  have hlogCols : Real.log ((N * P : ℕ) : ℝ) ≤
      312 * Real.log (L : ℝ) := by
    have hcolsPos : (0 : ℝ) < ((N * P : ℕ) : ℝ) := by positivity
    have hLpowPos : (0 : ℝ) < ((L ^ 312 : ℕ) : ℝ) := by positivity
    calc
      Real.log ((N * P : ℕ) : ℝ) ≤ Real.log ((L ^ 312 : ℕ) : ℝ) :=
        Real.log_le_log hcolsPos (by exact_mod_cast hNpow)
      _ = 312 * Real.log (L : ℝ) := by
        push_cast
        rw [Real.log_pow]
        norm_num
  have hsmallToA (c : ℝ) (hc : 0 ≤ c) :
      c * (L : ℝ) ^ 34 * Real.log (L : ℝ) ≤
        c * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    calc
      c * (L : ℝ) ^ 34 * Real.log (L : ℝ) ≤
          c * ((A : ℝ) * (L : ℝ) ^ 32) * Real.log (L : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hAL32 hc) hlogPos.le
      _ = _ := by ring
  have hcC : 0 ≤ cC :=
    coefficient_nonneg_of_log_bound hC hLpos hlogPos hlogC
  have hlogCstage : Real.log (C : ℝ) ≤
      cC * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    exact hlogC.trans (hsmallToA cC hcC)
  have hElogVstage : (E : ℝ) * Real.log (V : ℝ) ≤
      (cE * cV) * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    exact hElogV.trans (hsmallToA (cE * cV) (by positivity))
  have hfacstage : Real.log (W.factorial : ℝ) ≤
      cFac * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    exact hfac'.trans (hsmallToA cFac (by positivity))
  have hcolsstage : Real.log ((N * P : ℕ) : ℝ) ≤
      312 * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    have hone : (1 : ℝ) ≤ (A : ℝ) * (L : ℝ) ^ 32 := by
      exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hA)
        (one_le_pow₀ (by exact_mod_cast hLone))
    calc
      _ ≤ 312 * Real.log (L : ℝ) := hlogCols
      _ ≤ 312 * ((A : ℝ) * (L : ℝ) ^ 32) * Real.log (L : ℝ) := by
        have h312 : (0 : ℝ) ≤ 312 := by norm_num
        exact mul_le_mul_of_nonneg_right
          (by simpa using mul_le_mul_of_nonneg_left hone h312) hlogPos.le
      _ = _ := by ring
  have hUR : U * R =
      2 * (∑ i, ‖ell i‖) * ((A : ℝ) * (L : ℝ) ^ 33) := by
    dsimp [U, R]
    push_cast
    ring
  have hRcast : R + 1 + P = (Y : ℝ) := by
    dsimp [R, Y, P]
    push_cast
    ring
  have houterLog :
      Real.log
        (((N * P : ℕ) : ℝ) *
          ((C : ℝ) * (V : ℝ) ^ E * (W.factorial : ℝ) *
            (R + 1 + P) ^ P * Real.exp (U * R))) =
      Real.log ((N * P : ℕ) : ℝ) + Real.log (C : ℝ) +
        (E : ℝ) * Real.log (V : ℝ) + Real.log (W.factorial : ℝ) +
        (P : ℝ) * Real.log (Y : ℝ) + U * R :=
    outer_log_expansion (by positivity) hC hV hYpos hRcast
  have houter :
      Real.log
        (((N * P : ℕ) : ℝ) *
          ((C : ℝ) * (V : ℝ) ^ E * (W.factorial : ℝ) *
            (R + 1 + P) ^ P * Real.exp (U * R))) ≤
      cLog * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) +
        2 * (∑ i, ‖ell i‖) * ((A : ℝ) * (L : ℝ) ^ 33) := by
    rw [houterLog, hUR]
    dsimp [cLog]
    linarith
  -- The right-hand Liouville exponent has the same components, with a
  -- harmless factor `d ≤ 8` and the height term `2 A K Halpha`.
  let Z : ℕ := 2 * A + P
  have hZpos : 0 < Z := by dsimp [Z]; positivity
  have hZpoly : Z ≤ 5 * L ^ 314 := by
    have hPpoly : P ≤ L ^ 314 := by
      dsimp [P]
      exact Nat.pow_le_pow_right hLone (by omega)
    dsimp [Z]
    calc
      2 * A + P ≤ 2 * (2 * L ^ 314) + L ^ 314 := by gcongr
      _ = 5 * L ^ 314 := by ring
  have hlogZ := log_nat_le_poly hZpos (by norm_num : 0 < 5)
    hLpos hlogL hZpoly
  have hPlogZ : (P : ℝ) * Real.log (Z : ℝ) ≤
      319 * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    calc
      (P : ℝ) * Real.log (Z : ℝ) ≤
          (P : ℝ) * (319 * Real.log (L : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        norm_num at hlogZ ⊢
        exact hlogZ
      _ ≤ ((A : ℝ) * (L : ℝ) ^ 32) *
          (319 * Real.log (L : ℝ)) := by gcongr
      _ = _ := by ring
  have hlogP : Real.log (P : ℝ) = 24 * Real.log (L : ℝ) := by
    dsimp [P]
    push_cast
    rw [Real.log_pow]
    norm_num
  have hinnerNat :
      Real.log (P * C * W.factorial * Z ^ P * V ^ E : ℕ) =
        Real.log (P : ℝ) + Real.log (C : ℝ) +
          Real.log (W.factorial : ℝ) + (P : ℝ) * Real.log (Z : ℝ) +
          (E : ℝ) * Real.log (V : ℝ) :=
    inner_log_expansion hP hC hZpos hV
  have hInner : Real.log (P * C * W.factorial * Z ^ P * V ^ E : ℕ) ≤
      cInner * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    rw [hinnerNat, hlogP]
    dsimp [cInner]
    have h24 : 24 * Real.log (L : ℝ) ≤
        24 * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
      have hone : (1 : ℝ) ≤ (A : ℝ) * (L : ℝ) ^ 32 := by
        exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hA)
          (one_le_pow₀ (by exact_mod_cast hLone))
      nlinarith [mul_nonneg (sub_nonneg.mpr hone) hlogPos.le]
    linarith
  have hNplus : N + 1 ≤ 2 * L ^ 288 := by
    have he : 32 * (r + 1) ≤ 288 := by omega
    have hNle : N ≤ L ^ 288 := by
      have heq : N = L ^ (32 * (r + 1)) := by
        dsimp [N]
        rw [← pow_mul]
      rw [heq]
      exact Nat.pow_le_pow_right hLone he
    have hone : 1 ≤ L ^ 288 := Nat.one_le_pow _ _ hLone
    omega
  have hlogNplus := log_nat_le_poly (n := N + 1) (c := 2) (e := 288)
    (by positivity) (by norm_num) hLpos hlogL hNplus
  have hNterm : (d : ℝ) * Real.log (N + 1 : ℕ) ≤
      2320 * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    have hone : (1 : ℝ) ≤ (A : ℝ) * (L : ℝ) ^ 32 := by
      exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hA)
        (one_le_pow₀ (by exact_mod_cast hLone))
    have hlogNplus' : Real.log (N + 1 : ℕ) ≤
        290 * Real.log (L : ℝ) := by
      change Real.log (N + 1 : ℕ) ≤ ((290 : ℕ) : ℝ) * Real.log (L : ℝ)
      simpa only [Nat.reduceAdd] using hlogNplus
    exact degree_log_term_le (d := d) (n := N + 1) (A := A) (L := L)
      hd (by omega) hone hlogPos.le hlogNplus'
  have hInnerD : (d : ℝ) *
      Real.log (P * C * W.factorial * Z ^ P * V ^ E : ℕ) ≤
      (8 * cInner) *
        ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    exact degree_bounded_log_term_le
      (d := d) (q := P * C * W.factorial * Z ^ P * V ^ E)
      (c := cInner)
      (base := (A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ))
      hd (by
        have hqpos : 0 < P * C * W.factorial * Z ^ P * V ^ E := by positivity
        omega) hInner
  have hHeight : ((2 * A : ℕ) : ℝ) * (((L ^ 32 : ℕ) : ℝ) * Halpha) =
      2 * Halpha * ((A : ℝ) * (L : ℝ) ^ 32) := by
    push_cast
    ring
  have hX :
      (d : ℝ) * Real.log (N + 1 : ℕ) +
          (d : ℝ) * Real.log
            (P * C * W.factorial * Z ^ P * V ^ E : ℕ) +
          ((2 * A : ℕ) : ℝ) * (((L ^ 32 : ℕ) : ℝ) * Halpha) ≤
        (2320 + 8 * cInner + 2 * Halpha) *
          ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    rw [hHeight]
    have hh := height_term_le (A := A) (L := L) hHalpha hlogL
    exact sum_three_weighted_le hNterm hInnerD hh
  have hTotalLog :
      Real.log
          (((N * P : ℕ) : ℝ) *
            ((C : ℝ) * (V : ℝ) ^ E * (W.factorial : ℝ) *
              (R + 1 + P) ^ P * Real.exp (U * R))) +
        ((d : ℝ) * Real.log (N + 1 : ℕ) +
          (d : ℝ) * Real.log
            (P * C * W.factorial * (2 * A + P) ^ P * V ^ E : ℕ) +
          ((2 * A : ℕ) : ℝ) * (((L ^ 32 : ℕ) : ℝ) * Halpha)) ≤
      (cLog + 2320 + 8 * cInner + 2 * Halpha) *
          ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) +
        2 * (∑ i, ‖ell i‖) * ((A : ℝ) * (L : ℝ) ^ 33) :=
    combine_outer_inner houter hX
  calc
    _ ≤ (cLog + 2320 + 8 * cInner + 2 * Halpha) *
          ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) +
        2 * (∑ i, ‖ell i‖) * ((A : ℝ) * (L : ℝ) ^ 33) := hTotalLog
    _ ≤ (A : ℝ) *
        ((cLog + 2320 + 8 * cInner + 2 * Halpha +
            2 * ∑ i, ‖ell i‖) *
              ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
          (cLog + 2320 + 8 * cInner + 2 * Halpha +
            2 * ∑ i, ‖ell i‖) * (L : ℝ) ^ 33) := by
      have hcbase : 0 ≤ cLog + 2320 + 8 * cInner + 2 * Halpha := by
        dsimp [cLog, cInner, cFac, cE]
        positivity
      have hell : 0 ≤ 2 * ∑ i, ‖ell i‖ := by positivity
      convert master_recombine
        (a := (A : ℝ))
        (c := cLog + 2320 + 8 * cInner + 2 * Halpha)
        (s := 2 * ∑ i, ‖ell i‖)
        (x := (L : ℝ) ^ 32 * Real.log (L : ℝ))
        (y := (L : ℝ) ^ 33)
        (by positivity) hcbase hell (by positivity) (by positivity) using 1 <;> ring



lemma structured_stage_log_growth_le_fixed_radius
    {r L j C V d D : ℕ} (ell : Fin (r + 1) → ℂ)
    (Halpha cC cV : ℝ)
    (hr : r ≤ 8) (hd : d ≤ 8) (hHalpha : 0 ≤ Halpha) (hcV : 0 ≤ cV)
    (hL : 2 ≤ L) (hDlow : 2 ≤ D) (hDhigh : D ≤ L)
    (hlogL : 1 ≤ Real.log (L : ℝ))
    (hC : 0 < C) (hV : 0 < V)
    (hj : j < dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24))
    (hlogC : Real.log (C : ℝ) ≤
      cC * (L : ℝ) ^ 34 * Real.log (L : ℝ))
    (hlogV : Real.log (V : ℝ) ≤ cV * Real.log (L : ℝ)) :
    let N := (L ^ 32) ^ (r + 1)
    let P := L ^ 24
    let A := scaledDyadicStageA (L ^ 2) j
    let spend := L ^ 33
    let m := dyadicStageCount (N * P)
    let W := stageSpendBudget m spend (j + 1)
    let T := stageUnitBudget m (j + 1)
    let S := W
    let E := T + r * S
    let R : ℝ := (D : ℝ) * (2 * A : ℕ)
    let U : ℝ := (L ^ 32 : ℕ) * ∑ i, ‖ell i‖
    let X : ℝ :=
      d * Real.log (N + 1 : ℕ) +
        d * Real.log
          (P * C * W.factorial * (2 * A + P) ^ P * V ^ E : ℕ) +
        (2 * A : ℕ) * ((L ^ 32 : ℕ) * Halpha)
    let cFac : ℝ := 314 * (314 + 34)
    let cE : ℝ := 314 * 9
    let cLog : ℝ := 312 + cC + cE * cV + cFac + 321
    let cInner : ℝ := 24 + cC + cFac + 319 + cE * cV
    let cBase : ℝ := cLog + 2320 + 8 * cInner + 2 * Halpha
    Real.log
        (((N * P : ℕ) : ℝ) *
          ((C : ℝ) * (V : ℝ) ^ E * (W.factorial : ℝ) *
            (R + 1 + P) ^ P * Real.exp (U * R))) + X ≤
      (A : ℝ) *
        (cBase * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
          2 * (D : ℝ) * (∑ i, ‖ell i‖) * (L : ℝ) ^ 32) := by
  dsimp only
  let N := (L ^ 32) ^ (r + 1)
  let P := L ^ 24
  let A := scaledDyadicStageA (L ^ 2) j
  let spend := L ^ 33
  let m := dyadicStageCount (N * P)
  let W := stageSpendBudget m spend (j + 1)
  let T := stageUnitBudget m (j + 1)
  let S := W
  let E := T + r * S
  let R : ℝ := (D : ℝ) * (2 * A : ℕ)
  let U : ℝ := (L ^ 32 : ℕ) * ∑ i, ‖ell i‖
  let cFac : ℝ := 314 * (314 + 34)
  let cE : ℝ := 314 * 9
  let cLog : ℝ := 312 + cC + cE * cV + cFac + 321
  let cInner : ℝ := 24 + cC + cFac + 319 + cE * cV
  let cBase : ℝ := cLog + 2320 + 8 * cInner + 2 * Halpha
  have hLpos : 0 < L := by omega
  have hLone : 1 ≤ L := by omega
  have hlogPos : 0 < Real.log (L : ℝ) := lt_of_lt_of_le zero_lt_one hlogL
  have hN : 0 < N := by dsimp [N]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hA : 0 < A := by
    dsimp [A]
    exact scaledDyadicStageA_pos (by positivity) j
  have hAinit : L ^ 2 ≤ A := by
    dsimp [A, scaledDyadicStageA]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  have hAL32 : (L : ℝ) ^ 34 ≤ (A : ℝ) * (L : ℝ) ^ 32 := by
    have hcast : ((L ^ 2 : ℕ) : ℝ) ≤ (A : ℝ) := by exact_mod_cast hAinit
    have hcast' : (L : ℝ) ^ 2 ≤ (A : ℝ) := by
      simpa only [Nat.cast_pow] using hcast
    calc
      (L : ℝ) ^ 34 = (L : ℝ) ^ 2 * (L : ℝ) ^ 32 := by ring
      _ ≤ (A : ℝ) * (L : ℝ) ^ 32 := by
        exact mul_le_mul_of_nonneg_right hcast' (by positivity)
  have hb := box_parameter_budget_bounds hr hL
  dsimp only at hb
  have hWsrc : m * spend + 1 ≤ 314 * L ^ 34 := by
    simpa [m, N, P, spend] using hb.2.1
  have hTsrc : m + 1 ≤ 314 * L := by
    simpa [m, N, P] using hb.2.2
  have hWbd : W ≤ 314 * L ^ 34 :=
    (stageSpendBudget_le_zero m spend (j + 1)).trans hWsrc
  have hTbd : T ≤ 314 * L :=
    (stageUnitBudget_le_zero m (j + 1)).trans hTsrc
  have hWpos : 0 < W := by dsimp [W, stageSpendBudget]; omega
  have hTpos : 0 < T := by dsimp [T, stageUnitBudget]; omega
  have hEbd : E ≤ 314 * 9 * L ^ 34 := by
    have hL34 : L ≤ L ^ 34 := by
      simpa using Nat.pow_le_pow_right hLone (show 1 ≤ 34 by omega)
    dsimp [E, S]
    calc
      T + r * W ≤ 314 * L + 8 * (314 * L ^ 34) := by gcongr
      _ ≤ 314 * L ^ 34 + 8 * (314 * L ^ 34) := by gcongr
      _ = 314 * 9 * L ^ 34 := by ring
  have hlogV0 : 0 ≤ Real.log (V : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ V by omega))
  have hElogV : (E : ℝ) * Real.log (V : ℝ) ≤
      cE * cV * (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
    calc
      (E : ℝ) * Real.log (V : ℝ) ≤
          ((314 * 9 : ℕ) : ℝ) * (L : ℝ) ^ 34 *
            (cV * Real.log (L : ℝ)) := by
        apply mul_le_mul (by exact_mod_cast hEbd) hlogV hlogV0 (by positivity)
      _ = cE * cV * (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
        dsimp [cE]
        ring
  have hfac := log_nat_factorial_le_poly hWpos (by norm_num : 0 < 314)
    hLpos hlogL hWbd
  have hfac' : Real.log (W.factorial : ℝ) ≤
      cFac * (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
    dsimp [cFac]
    norm_num at hfac ⊢
    exact hfac
  have hAupper := scaledDyadicStageA_parameter_upper hL hj
  have hNpow : N * P ≤ L ^ 312 := by
    have he : 32 * (r + 1) + 24 ≤ 312 := by omega
    have heq : N * P = L ^ (32 * (r + 1) + 24) := by
      dsimp [N, P]
      rw [← pow_mul, ← pow_add]
    rw [heq]
    exact Nat.pow_le_pow_right hLone he
  have hApoly : A ≤ 2 * L ^ 314 := by
    have hAstep : A ≤ scaledDyadicStageA (L ^ 2) (j + 1) := by
      dsimp [A, scaledDyadicStageA]
      exact Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by omega) (Nat.le_succ j))
    calc
      A ≤ scaledDyadicStageA (L ^ 2) (j + 1) := hAstep
      _ ≤ 2 * L ^ 2 * (N * P) := by simpa [N, P] using hAupper
      _ ≤ 2 * L ^ 2 * L ^ 312 := by gcongr
      _ = 2 * L ^ 314 := by ring
  let Y : ℕ := D * (2 * A) + 1 + P
  have hYpos : 0 < Y := by dsimp [Y]; positivity
  have hYpoly : Y ≤ 6 * L ^ 315 := by
    have hPpoly : P ≤ L ^ 315 := by
      dsimp [P]
      exact Nat.pow_le_pow_right hLone (by omega)
    have hOne : 1 ≤ L ^ 315 := Nat.one_le_pow _ _ hLone
    dsimp [Y]
    calc
      D * (2 * A) + 1 + P ≤ L * (2 * (2 * L ^ 314)) + L ^ 315 + L ^ 315 := by
        gcongr
      _ = 6 * L ^ 315 := by ring
  have hlogY := log_nat_le_poly hYpos (by norm_num : 0 < 6)
    hLpos hlogL hYpoly
  have hPltAL32 : (P : ℝ) ≤ (A : ℝ) * (L : ℝ) ^ 32 := by
    have hp34 : (L : ℝ) ^ 24 ≤ (L : ℝ) ^ 34 :=
      pow_le_pow_right₀ (by exact_mod_cast hLone) (by omega)
    exact (by simpa [P] using hp34.trans hAL32)
  have hPlogY : (P : ℝ) * Real.log (Y : ℝ) ≤
      321 * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    calc
      (P : ℝ) * Real.log (Y : ℝ) ≤
          (P : ℝ) * (321 * Real.log (L : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        norm_num at hlogY ⊢
        exact hlogY
      _ ≤ ((A : ℝ) * (L : ℝ) ^ 32) *
          (321 * Real.log (L : ℝ)) := by gcongr
      _ = 321 * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by ring
  have hlogCols : Real.log ((N * P : ℕ) : ℝ) ≤
      312 * Real.log (L : ℝ) := by
    have hcolsPos : (0 : ℝ) < ((N * P : ℕ) : ℝ) := by positivity
    have hLpowPos : (0 : ℝ) < ((L ^ 312 : ℕ) : ℝ) := by positivity
    calc
      Real.log ((N * P : ℕ) : ℝ) ≤ Real.log ((L ^ 312 : ℕ) : ℝ) :=
        Real.log_le_log hcolsPos (by exact_mod_cast hNpow)
      _ = 312 * Real.log (L : ℝ) := by
        push_cast
        rw [Real.log_pow]
        norm_num
  have hsmallToA (c : ℝ) (hc : 0 ≤ c) :
      c * (L : ℝ) ^ 34 * Real.log (L : ℝ) ≤
        c * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    calc
      c * (L : ℝ) ^ 34 * Real.log (L : ℝ) ≤
          c * ((A : ℝ) * (L : ℝ) ^ 32) * Real.log (L : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hAL32 hc) hlogPos.le
      _ = _ := by ring
  have hcC : 0 ≤ cC :=
    coefficient_nonneg_of_log_bound hC hLpos hlogPos hlogC
  have hlogCstage : Real.log (C : ℝ) ≤
      cC * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    exact hlogC.trans (hsmallToA cC hcC)
  have hElogVstage : (E : ℝ) * Real.log (V : ℝ) ≤
      (cE * cV) * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    exact hElogV.trans (hsmallToA (cE * cV) (by positivity))
  have hfacstage : Real.log (W.factorial : ℝ) ≤
      cFac * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    exact hfac'.trans (hsmallToA cFac (by positivity))
  have hcolsstage : Real.log ((N * P : ℕ) : ℝ) ≤
      312 * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    have hone : (1 : ℝ) ≤ (A : ℝ) * (L : ℝ) ^ 32 := by
      exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hA)
        (one_le_pow₀ (by exact_mod_cast hLone))
    calc
      _ ≤ 312 * Real.log (L : ℝ) := hlogCols
      _ ≤ 312 * ((A : ℝ) * (L : ℝ) ^ 32) * Real.log (L : ℝ) := by
        have h312 : (0 : ℝ) ≤ 312 := by norm_num
        exact mul_le_mul_of_nonneg_right
          (by simpa using mul_le_mul_of_nonneg_left hone h312) hlogPos.le
      _ = _ := by ring
  have hUR : U * R =
      2 * (D : ℝ) * (∑ i, ‖ell i‖) *
          ((A : ℝ) * (L : ℝ) ^ 32) := by
    dsimp [U, R]
    push_cast
    ring
  have hRcast : R + 1 + P = (Y : ℝ) := by
    dsimp [R, Y, P]
    push_cast
    ring
  have houterLog :
      Real.log
        (((N * P : ℕ) : ℝ) *
          ((C : ℝ) * (V : ℝ) ^ E * (W.factorial : ℝ) *
            (R + 1 + P) ^ P * Real.exp (U * R))) =
      Real.log ((N * P : ℕ) : ℝ) + Real.log (C : ℝ) +
        (E : ℝ) * Real.log (V : ℝ) + Real.log (W.factorial : ℝ) +
        (P : ℝ) * Real.log (Y : ℝ) + U * R :=
    outer_log_expansion (by positivity) hC hV hYpos hRcast
  have houter :
      Real.log
        (((N * P : ℕ) : ℝ) *
          ((C : ℝ) * (V : ℝ) ^ E * (W.factorial : ℝ) *
            (R + 1 + P) ^ P * Real.exp (U * R))) ≤
      cLog * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) +
        2 * (D : ℝ) * (∑ i, ‖ell i‖) *
          ((A : ℝ) * (L : ℝ) ^ 32) := by
    rw [houterLog, hUR]
    dsimp [cLog]
    linarith
  -- The right-hand Liouville exponent has the same components, with a
  -- harmless factor `d ≤ 8` and the height term `2 A K Halpha`.
  let Z : ℕ := 2 * A + P
  have hZpos : 0 < Z := by dsimp [Z]; positivity
  have hZpoly : Z ≤ 5 * L ^ 314 := by
    have hPpoly : P ≤ L ^ 314 := by
      dsimp [P]
      exact Nat.pow_le_pow_right hLone (by omega)
    dsimp [Z]
    calc
      2 * A + P ≤ 2 * (2 * L ^ 314) + L ^ 314 := by gcongr
      _ = 5 * L ^ 314 := by ring
  have hlogZ := log_nat_le_poly hZpos (by norm_num : 0 < 5)
    hLpos hlogL hZpoly
  have hPlogZ : (P : ℝ) * Real.log (Z : ℝ) ≤
      319 * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    calc
      (P : ℝ) * Real.log (Z : ℝ) ≤
          (P : ℝ) * (319 * Real.log (L : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        norm_num at hlogZ ⊢
        exact hlogZ
      _ ≤ ((A : ℝ) * (L : ℝ) ^ 32) *
          (319 * Real.log (L : ℝ)) := by gcongr
      _ = _ := by ring
  have hlogP : Real.log (P : ℝ) = 24 * Real.log (L : ℝ) := by
    dsimp [P]
    push_cast
    rw [Real.log_pow]
    norm_num
  have hinnerNat :
      Real.log (P * C * W.factorial * Z ^ P * V ^ E : ℕ) =
        Real.log (P : ℝ) + Real.log (C : ℝ) +
          Real.log (W.factorial : ℝ) + (P : ℝ) * Real.log (Z : ℝ) +
          (E : ℝ) * Real.log (V : ℝ) :=
    inner_log_expansion hP hC hZpos hV
  have hInner : Real.log (P * C * W.factorial * Z ^ P * V ^ E : ℕ) ≤
      cInner * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    rw [hinnerNat, hlogP]
    dsimp [cInner]
    have h24 : 24 * Real.log (L : ℝ) ≤
        24 * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
      have hone : (1 : ℝ) ≤ (A : ℝ) * (L : ℝ) ^ 32 := by
        exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hA)
          (one_le_pow₀ (by exact_mod_cast hLone))
      nlinarith [mul_nonneg (sub_nonneg.mpr hone) hlogPos.le]
    linarith
  have hNplus : N + 1 ≤ 2 * L ^ 288 := by
    have he : 32 * (r + 1) ≤ 288 := by omega
    have hNle : N ≤ L ^ 288 := by
      have heq : N = L ^ (32 * (r + 1)) := by
        dsimp [N]
        rw [← pow_mul]
      rw [heq]
      exact Nat.pow_le_pow_right hLone he
    have hone : 1 ≤ L ^ 288 := Nat.one_le_pow _ _ hLone
    omega
  have hlogNplus := log_nat_le_poly (n := N + 1) (c := 2) (e := 288)
    (by positivity) (by norm_num) hLpos hlogL hNplus
  have hNterm : (d : ℝ) * Real.log (N + 1 : ℕ) ≤
      2320 * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    have hone : (1 : ℝ) ≤ (A : ℝ) * (L : ℝ) ^ 32 := by
      exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hA)
        (one_le_pow₀ (by exact_mod_cast hLone))
    have hlogNplus' : Real.log (N + 1 : ℕ) ≤
        290 * Real.log (L : ℝ) := by
      change Real.log (N + 1 : ℕ) ≤ ((290 : ℕ) : ℝ) * Real.log (L : ℝ)
      simpa only [Nat.reduceAdd] using hlogNplus
    exact degree_log_term_le (d := d) (n := N + 1) (A := A) (L := L)
      hd (by omega) hone hlogPos.le hlogNplus'
  have hInnerD : (d : ℝ) *
      Real.log (P * C * W.factorial * Z ^ P * V ^ E : ℕ) ≤
      (8 * cInner) *
        ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    exact degree_bounded_log_term_le
      (d := d) (q := P * C * W.factorial * Z ^ P * V ^ E)
      (c := cInner)
      (base := (A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ))
      hd (by
        have hqpos : 0 < P * C * W.factorial * Z ^ P * V ^ E := by positivity
        omega) hInner
  have hHeight : ((2 * A : ℕ) : ℝ) * (((L ^ 32 : ℕ) : ℝ) * Halpha) =
      2 * Halpha * ((A : ℝ) * (L : ℝ) ^ 32) := by
    push_cast
    ring
  have hX :
      (d : ℝ) * Real.log (N + 1 : ℕ) +
          (d : ℝ) * Real.log
            (P * C * W.factorial * Z ^ P * V ^ E : ℕ) +
          ((2 * A : ℕ) : ℝ) * (((L ^ 32 : ℕ) : ℝ) * Halpha) ≤
        (2320 + 8 * cInner + 2 * Halpha) *
          ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    rw [hHeight]
    have hh := height_term_le (A := A) (L := L) hHalpha hlogL
    exact sum_three_weighted_le hNterm hInnerD hh
  have hTotalLog :
      Real.log
          (((N * P : ℕ) : ℝ) *
            ((C : ℝ) * (V : ℝ) ^ E * (W.factorial : ℝ) *
              (R + 1 + P) ^ P * Real.exp (U * R))) +
        ((d : ℝ) * Real.log (N + 1 : ℕ) +
          (d : ℝ) * Real.log
            (P * C * W.factorial * (2 * A + P) ^ P * V ^ E : ℕ) +
          ((2 * A : ℕ) : ℝ) * (((L ^ 32 : ℕ) : ℝ) * Halpha)) ≤
      (cLog + 2320 + 8 * cInner + 2 * Halpha) *
          ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) +
        2 * (D : ℝ) * (∑ i, ‖ell i‖) *
          ((A : ℝ) * (L : ℝ) ^ 32) :=
    combine_outer_inner houter hX
  calc
    _ ≤ cBase * ((A : ℝ) * (L : ℝ) ^ 32 * Real.log (L : ℝ)) +
        2 * (D : ℝ) * (∑ i, ‖ell i‖) *
          ((A : ℝ) * (L : ℝ) ^ 32) := hTotalLog
    _ = (A : ℝ) *
        (cBase * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
          2 * (D : ℝ) * (∑ i, ‖ell i‖) * (L : ℝ) ^ 32) := by ring


lemma structured_stage_perturbation_log_le
    {r L j C V : ℕ} (ell : Fin (r + 1) → ℂ)
    (cC cV : ℝ)
    (hr : r ≤ 8) (hcV : 0 ≤ cV)
    (hL : 2 ≤ L) (hlogL : 1 ≤ Real.log (L : ℝ))
    (hC : 0 < C) (hV : 0 < V)
    (hj : j < dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24))
    (hlogC : Real.log (C : ℝ) ≤
      cC * (L : ℝ) ^ 34 * Real.log (L : ℝ))
    (hlogV : Real.log (V : ℝ) ≤ cV * Real.log (L : ℝ)) :
    let N := (L ^ 32) ^ (r + 1)
    let P := L ^ 24
    let A := scaledDyadicStageA (L ^ 2) j
    let k := L ^ 33
    let m := dyadicStageCount (N * P)
    let W := stageSpendBudget m k (j + 1)
    let T := stageUnitBudget m (j + 1)
    let S := W
    let E := T + r * S
    let U : ℝ := (L ^ 32 : ℕ) * ∑ i, ‖ell i‖
    let R : ℝ := (L : ℝ) * (2 * A : ℕ)
    let Z : ℝ := (2 * A : ℕ)
    let cE : ℝ := 314 * 9
    let cCore : ℝ := 312 + cC + cE * cV + 315 * (315 + 34) +
      318 + 2 * (∑ i, ‖ell i‖) + cV + 4
    let cPerturb : ℝ := 3956 + cCore
    Real.log (pochhammerWeightedPerturbationCoefficient
        N P A k W E 0 (C : ℝ) (V : ℝ) U R Z) ≤
      cPerturb * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
  dsimp only
  let N := (L ^ 32) ^ (r + 1)
  let P := L ^ 24
  let A := scaledDyadicStageA (L ^ 2) j
  let k := L ^ 33
  let m := dyadicStageCount (N * P)
  let W := stageSpendBudget m k (j + 1)
  let T := stageUnitBudget m (j + 1)
  let S := W
  let E := T + r * S
  let U : ℝ := (L ^ 32 : ℕ) * ∑ i, ‖ell i‖
  let R : ℝ := (L : ℝ) * (2 * A : ℕ)
  let Z : ℝ := (2 * A : ℕ)
  let cE : ℝ := 314 * 9
  let cCore : ℝ := 312 + cC + cE * cV + 315 * (315 + 34) +
    318 + 2 * (∑ i, ‖ell i‖) + cV + 4
  let cPerturb : ℝ := 3956 + cCore
  have hLpos : 0 < L := by omega
  have hLone : 1 ≤ L := by omega
  have hLoneR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLone
  have hpow694one : (1 : ℝ) ≤ (L : ℝ) ^ 694 := one_le_pow₀ hLoneR
  have hlogPos : 0 < Real.log (L : ℝ) := lt_of_lt_of_le zero_lt_one hlogL
  have hN : 0 < N := by dsimp [N]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hA : 0 < A := by dsimp [A]; exact scaledDyadicStageA_pos (by positivity) j
  have hk : 0 < k := by dsimp [k]; positivity
  have hb := box_parameter_budget_bounds hr hL
  dsimp only at hb
  have hWsrc : m * k + 1 ≤ 314 * L ^ 34 := by
    simpa [m, N, P, k] using hb.2.1
  have hTsrc : m + 1 ≤ 314 * L := by
    simpa [m, N, P] using hb.2.2
  have hWbd : W ≤ 314 * L ^ 34 :=
    (stageSpendBudget_le_zero m k (j + 1)).trans hWsrc
  have hTbd : T ≤ 314 * L :=
    (stageUnitBudget_le_zero m (j + 1)).trans hTsrc
  have hWpos : 0 < W := by dsimp [W, stageSpendBudget]; omega
  have hEbd : E ≤ 314 * 9 * L ^ 34 := by
    have hL34 : L ≤ L ^ 34 := by
      simpa using Nat.pow_le_pow_right hLone (show 1 ≤ 34 by omega)
    dsimp [E, S]
    calc
      T + r * W ≤ 314 * L + 8 * (314 * L ^ 34) := by gcongr
      _ ≤ 314 * L ^ 34 + 8 * (314 * L ^ 34) := by gcongr
      _ = 314 * 9 * L ^ 34 := by ring
  have hAupper0 := scaledDyadicStageA_parameter_upper (by omega) hj
  have hNpow : N * P ≤ L ^ 312 := by
    have he : 32 * (r + 1) + 24 ≤ 312 := by omega
    have heq : N * P = L ^ (32 * (r + 1) + 24) := by
      dsimp [N, P]
      rw [← pow_mul, ← pow_add]
    rw [heq]
    exact Nat.pow_le_pow_right hLone he
  have hApoly : A ≤ 2 * L ^ 314 := by
    have hAstep : A ≤ scaledDyadicStageA (L ^ 2) (j + 1) := by
      dsimp [A, scaledDyadicStageA]
      exact Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by omega) (Nat.le_succ j))
    calc
      A ≤ scaledDyadicStageA (L ^ 2) (j + 1) := hAstep
      _ ≤ 2 * L ^ 2 * (N * P) := by simpa [N, P] using hAupper0
      _ ≤ 2 * L ^ 2 * L ^ 312 := by gcongr
      _ = 2 * L ^ 314 := by ring
  have hkL34 : k ≤ L ^ 34 := by
    dsimp [k]
    exact Nat.pow_le_pow_right hLone (by omega)
  have hWk : W + k ≤ 315 * L ^ 34 := by omega
  have hAk : A * k ≤ 2 * L ^ 347 := by
    calc
      A * k ≤ (2 * L ^ 314) * L ^ 33 := by gcongr
      _ = 2 * L ^ 347 := by ring
  have hAPA : A + 1 + P ≤ 4 * L ^ 314 := by
    have hP314 : P ≤ L ^ 314 := by
      dsimp [P]
      exact Nat.pow_le_pow_right hLone (by omega)
    have hOne314 : 1 ≤ L ^ 314 := Nat.one_le_pow _ _ hLone
    omega
  have hZA : 2 * A + A ≤ 6 * L ^ 314 := by omega
  have hRnat : L * (2 * A) ≤ 4 * L ^ 315 := by
    calc
      L * (2 * A) ≤ L * (2 * (2 * L ^ 314)) := by gcongr
      _ = 4 * L ^ 315 := by ring
  have hHermBase : 2 * (A + 1) ≤ 6 * L ^ 314 := by
    have hOne314 : 1 ≤ L ^ 314 := Nat.one_le_pow _ _ hLone
    omega
  have hlogAk := log_nat_le_poly (n := A * k) (c := 2) (e := 347)
    (by positivity) (by norm_num) hLpos hlogL hAk
  have hlogZA := log_nat_le_poly (n := 2 * A + A) (c := 6) (e := 314)
    (by positivity) (by norm_num) hLpos hlogL hZA
  have hlogR := log_nat_le_poly (n := L * (2 * A)) (c := 4) (e := 315)
    (by positivity) (by norm_num) hLpos hlogL hRnat
  have hlogAPA := log_nat_le_poly (n := A + 1 + P) (c := 4) (e := 314)
    (by positivity) (by norm_num) hLpos hlogL hAPA
  have hlogHermBase := log_nat_le_poly (n := 2 * (A + 1))
    (c := 6) (e := 314) (by positivity) (by norm_num) hLpos hlogL hHermBase
  have hfacWk := log_nat_factorial_le_poly (n := W + k)
    (c := 315) (e := 34) (by positivity) (by norm_num) hLpos hlogL hWk
  have hfacAk := log_nat_factorial_le_poly (n := A * k)
    (c := 2) (e := 347) (by positivity) (by norm_num) hLpos hlogL hAk
  have hcC : 0 ≤ cC :=
    coefficient_nonneg_of_log_bound hC hLpos hlogPos hlogC
  have hlogV0 : 0 ≤ Real.log (V : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ V by omega))
  have hElogV : (E : ℝ) * Real.log (V : ℝ) ≤
      cE * cV * (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
    calc
      (E : ℝ) * Real.log (V : ℝ) ≤
          ((314 * 9 : ℕ) : ℝ) * (L : ℝ) ^ 34 *
            (cV * Real.log (L : ℝ)) := by
        apply mul_le_mul (by exact_mod_cast hEbd) hlogV hlogV0 (by positivity)
      _ = cE * cV * (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
        dsimp [cE]
        ring
  have hlogNP : Real.log (N * P : ℕ) ≤ 312 * Real.log (L : ℝ) := by
    have hp : (0 : ℝ) < ((N * P : ℕ) : ℝ) := by positivity
    calc
      Real.log (N * P : ℕ) ≤ Real.log ((L ^ 312 : ℕ) : ℝ) :=
        Real.log_le_log hp (by exact_mod_cast hNpow)
      _ = 312 * Real.log (L : ℝ) := by
        push_cast
        rw [Real.log_pow]
        norm_num
  have hlogTwo : Real.log 2 ≤ 2 * Real.log (L : ℝ) := by
    have h2 : Real.log 2 ≤ 2 :=
      (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans (by norm_num)
    exact h2.trans (by nlinarith)
  have hpow34 : (L : ℝ) ^ 34 ≤ (L : ℝ) ^ 694 :=
    pow_le_pow_right₀ (by exact_mod_cast hLone) (by omega)
  have hpow24 : (L : ℝ) ^ 24 ≤ (L : ℝ) ^ 694 :=
    pow_le_pow_right₀ (by exact_mod_cast hLone) (by omega)
  have hpow33 : (L : ℝ) ^ 33 ≤ (L : ℝ) ^ 694 :=
    pow_le_pow_right₀ (by exact_mod_cast hLone) (by omega)
  have hpow346 : (L : ℝ) ^ 346 ≤ (L : ℝ) ^ 694 :=
    pow_le_pow_right₀ (by exact_mod_cast hLone) (by omega)
  have hpow347 : (L : ℝ) ^ 347 ≤ (L : ℝ) ^ 694 :=
    pow_le_pow_right₀ (by exact_mod_cast hLone) (by omega)
  have hAkR : (A * k : ℕ) ≤ 2 * L ^ 347 := hAk
  have hAkCast : ((A * k : ℕ) : ℝ) ≤ 2 * (L : ℝ) ^ 347 := by
    exact_mod_cast hAkR
  have hAkSq : ((A * k : ℕ) : ℝ) ^ 2 ≤ 4 * (L : ℝ) ^ 694 := by
    calc
      ((A * k : ℕ) : ℝ) ^ 2 ≤ (2 * (L : ℝ) ^ 347) ^ 2 := by gcongr
      _ = 4 * (L : ℝ) ^ 694 := by ring
  have hlogHermite : Real.log (hermiteInterpolationBound A k) ≤
      1978 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
    have hsecond : ((A * k : ℕ) : ℝ) ^ 2 *
        Real.log (2 * (A + 1 : ℝ)) ≤
        1280 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
      have hbaseEq : 2 * (A + 1 : ℝ) = ((2 * (A + 1) : ℕ) : ℝ) := by
        push_cast
        ring
      rw [hbaseEq]
      calc
        _ ≤ (4 * (L : ℝ) ^ 694) * (320 * Real.log (L : ℝ)) := by
          apply mul_le_mul hAkSq (by simpa using hlogHermBase)
            (Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * (A + 1) by omega)))
            (by positivity)
        _ = _ := by ring
    have hfirst : Real.log ((A * k).factorial : ℝ) ≤
        698 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
      calc
        _ ≤ 698 * (L : ℝ) ^ 347 * Real.log (L : ℝ) := by
          norm_num at hfacAk ⊢
          exact hfacAk
        _ ≤ 698 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by gcongr
    exact hermiteInterpolationBound_log_le A k hA hk hfirst hsecond
  have hcore : Real.log (pochhammerWeightedPerturbationCore
      N P A k W E 0 (C : ℝ) (V : ℝ) U) ≤
      cCore * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
    have hfacWk' : Real.log ((W + k).factorial : ℝ) ≤
        (315 * (315 + 34) : ℕ) * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
      calc
        _ ≤ (315 * (315 + 34) : ℕ) * (L : ℝ) ^ 34 * Real.log (L : ℝ) := hfacWk
        _ ≤ _ := by gcongr
    have hPterm : (P : ℝ) * Real.log ((A + 1 + P : ℕ) : ℝ) ≤
        318 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
      have hPcast : (P : ℝ) = (L : ℝ) ^ 24 := by simp [P]
      have hlogAPA' : Real.log ((A + 1 + P : ℕ) : ℝ) ≤
          318 * Real.log (L : ℝ) := by
        norm_num at hlogAPA ⊢
        exact hlogAPA
      rw [hPcast]
      calc
        _ ≤ (L : ℝ) ^ 24 * (318 * Real.log (L : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hlogAPA' (by positivity)
        _ ≤ (L : ℝ) ^ 694 * (318 * Real.log (L : ℝ)) := by gcongr
        _ = _ := by ring
    have hUA : U * (A : ℝ) ≤
        (2 * ∑ i, ‖ell i‖) * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
      have hAcast : (A : ℝ) ≤ 2 * (L : ℝ) ^ 314 := by exact_mod_cast hApoly
      have hraw : U * (A : ℝ) ≤
          (2 * ∑ i, ‖ell i‖) * (L : ℝ) ^ 346 := by
        dsimp [U]
        push_cast
        calc
          (L : ℝ) ^ 32 * (∑ i, ‖ell i‖) * (A : ℝ) ≤
              (L : ℝ) ^ 32 * (∑ i, ‖ell i‖) *
                (2 * (L : ℝ) ^ 314) := by gcongr
          _ = _ := by ring
      calc
        _ ≤ (2 * ∑ i, ‖ell i‖) * (L : ℝ) ^ 346 := hraw
        _ ≤ (2 * ∑ i, ‖ell i‖) * (L : ℝ) ^ 694 := by
          exact mul_le_mul_of_nonneg_left hpow346 (by positivity)
        _ ≤ (2 * ∑ i, ‖ell i‖) * (L : ℝ) ^ 694 *
            Real.log (L : ℝ) := by
          apply le_mul_of_one_le_right
          · exact mul_nonneg
              (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))
              (pow_nonneg (by positivity) _)
          · exact hlogL
    have hkV : (k : ℝ) * Real.log (V : ℝ) ≤
        cV * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
      have hkcast : (k : ℝ) = (L : ℝ) ^ 33 := by simp [k]
      rw [hkcast]
      calc
        _ ≤ (L : ℝ) ^ 33 * (cV * Real.log (L : ℝ)) := by gcongr
        _ ≤ (L : ℝ) ^ 694 * (cV * Real.log (L : ℝ)) := by
          gcongr
        _ = _ := by ring
    have htwoK : ((2 * k : ℕ) : ℝ) * Real.log 2 ≤
        4 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
      have hkcast : (k : ℝ) = (L : ℝ) ^ 33 := by simp [k]
      push_cast
      rw [hkcast]
      calc
        2 * (L : ℝ) ^ 33 * Real.log 2 ≤
            2 * (L : ℝ) ^ 33 * (2 * Real.log (L : ℝ)) := by gcongr
        _ ≤ 2 * (L : ℝ) ^ 694 * (2 * Real.log (L : ℝ)) := by gcongr
        _ = _ := by ring
    have hNP' : Real.log (N * P : ℕ) ≤
        312 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
      calc
        _ ≤ 312 * Real.log (L : ℝ) := hlogNP
        _ ≤ 312 * ((L : ℝ) ^ 694 * Real.log (L : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right hpow694one hlogPos.le)
        _ = 312 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by ring
    have hC' : Real.log (C : ℝ) ≤
        cC * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
      apply hlogC.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow34 hcC) hlogPos.le
    have hEV' : (E : ℝ) * Real.log (V : ℝ) ≤
        cE * cV * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
      apply hElogV.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow34 (by dsimp [cE]; positivity)) hlogPos.le
    exact pochhammerWeightedPerturbationCore_log_le
      N P A k W E 0 hN hP (by exact_mod_cast hC) (by exact_mod_cast hV)
        hNP' hC' hEV' hfacWk' hPterm hUA hkV htwoK
  have hcommon : Real.log (pochhammerWeightedPerturbationCommon
      N P A k W E 0 (C : ℝ) (V : ℝ) U) ≤
      (2676 + cCore) * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
    have hlogAk' : 2 * Real.log ((A * k : ℕ) : ℝ) ≤
        698 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
      have hlogAkNum : Real.log ((A * k : ℕ) : ℝ) ≤
          349 * Real.log (L : ℝ) := by
        norm_num at hlogAk ⊢
        exact hlogAk
      calc
        _ ≤ 2 * (349 * Real.log (L : ℝ)) := by linarith
        _ = 698 * Real.log (L : ℝ) := by ring
        _ ≤ 698 * ((L : ℝ) ^ 694 * Real.log (L : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right hpow694one hlogPos.le)
        _ = 698 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by ring
    exact pochhammerWeightedPerturbationCommon_log_le
      N P A k W E 0 hN hP hA hk (by exact_mod_cast hC) (by exact_mod_cast hV)
        hlogAk' hlogHermite hcore
  have hRone : 1 ≤ R := by
    dsimp [R]
    push_cast
    nlinarith [show (1 : ℝ) ≤ L by exact_mod_cast hLone,
      show (1 : ℝ) ≤ A by exact_mod_cast (show 1 ≤ A by omega)]
  have hden : 1 ≤ R - A := by
    have hfactor : (1 : ℝ) ≤ 2 * (L : ℝ) - 1 := by
      have hLR : (2 : ℝ) ≤ L := by exact_mod_cast hL
      linarith
    have hAR : (1 : ℝ) ≤ A := by exact_mod_cast (show 1 ≤ A by omega)
    calc
      1 ≤ (2 * (L : ℝ) - 1) * (A : ℝ) :=
        one_le_mul_of_one_le_of_one_le hfactor hAR
      _ = R - A := by
        dsimp [R]
        push_cast
        ring
  have hcommonPos : 0 < pochhammerWeightedPerturbationCommon
      N P A k W E 0 (C : ℝ) (V : ℝ) U := by
    unfold pochhammerWeightedPerturbationCommon
      pochhammerWeightedPerturbationCore hermiteInterpolationBound
    positivity
  have hcoeffPos : 0 < pochhammerWeightedPerturbationCoefficient
      N P A k W E 0 (C : ℝ) (V : ℝ) U R Z := by
    have hden0 : 0 < (R - (A : ℝ)) ^ (k * A) := by
      exact pow_pos (zero_lt_one.trans_le hden) _
    unfold pochhammerWeightedPerturbationCoefficient
    change 0 < (Z + A) ^ (k * A) *
        (pochhammerWeightedPerturbationCommon
          N P A k W E 0 (C : ℝ) (V : ℝ) U *
          max 1 (R ^ (A * k)) / (R - A) ^ (k * A)) +
      pochhammerWeightedPerturbationCommon
          N P A k W E 0 (C : ℝ) (V : ℝ) U *
        max 1 (Z ^ (A * k))
    apply add_pos_of_nonneg_of_pos
    · exact mul_nonneg (by positivity)
        (div_nonneg
          (mul_nonneg hcommonPos.le (zero_le_one.trans (le_max_left _ _)))
          hden0.le)
    · exact mul_pos hcommonPos
        (zero_lt_one.trans_le (le_max_left _ _))
  have hZ0 : 0 ≤ Z := by dsimp [Z]; positivity
  have hZR : Z ≤ R := by
    dsimp [Z, R]
    push_cast
    exact le_mul_of_one_le_left (by positivity) hLoneR
  have hZAeq : Z + A = ((2 * A + A : ℕ) : ℝ) := by
    dsimp [Z]
    push_cast
    ring
  have hReq : R = ((L * (2 * A) : ℕ) : ℝ) := by
    dsimp [R]
    push_cast
    ring
  have hZAterm : ((A * k : ℕ) : ℝ) * Real.log ((2 * A + A : ℕ) : ℝ) ≤
      640 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
    have hlogZA' : Real.log ((2 * A + A : ℕ) : ℝ) ≤
        320 * Real.log (L : ℝ) := by
      norm_num at hlogZA ⊢
      exact hlogZA
    calc
      _ ≤ (2 * (L : ℝ) ^ 347) * (320 * Real.log (L : ℝ)) := by
        apply mul_le_mul hAkCast hlogZA'
        · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * A + A by omega))
        · positivity
      _ ≤ (2 * (L : ℝ) ^ 694) * (320 * Real.log (L : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow347 (by norm_num)) (by positivity)
      _ = _ := by ring
  have hRterm : ((A * k : ℕ) : ℝ) * Real.log ((L * (2 * A) : ℕ) : ℝ) ≤
      638 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
    have hlogR' : Real.log ((L * (2 * A) : ℕ) : ℝ) ≤
        319 * Real.log (L : ℝ) := by
      norm_num at hlogR ⊢
      exact hlogR
    calc
      _ ≤ (2 * (L : ℝ) ^ 347) * (319 * Real.log (L : ℝ)) := by
        apply mul_le_mul hAkCast hlogR'
        · have hpos : 0 < L * (2 * A) := by positivity
          exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ L * (2 * A) by omega))
        · positivity
      _ ≤ (2 * (L : ℝ) ^ 694) * (319 * Real.log (L : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow347 (by norm_num)) (by positivity)
      _ = _ := by ring
  have hlogTwo' : Real.log 2 ≤
      2 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
    calc
      _ ≤ 2 * Real.log (L : ℝ) := hlogTwo
      _ ≤ 2 * ((L : ℝ) ^ 694 * Real.log (L : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right hpow694one hlogPos.le)) (by norm_num)
      _ = _ := by ring
  change Real.log (pochhammerWeightedPerturbationCoefficient
      N P A k W E 0 (C : ℝ) (V : ℝ) U R Z) ≤
    cPerturb * (L : ℝ) ^ 694 * Real.log (L : ℝ)
  exact pochhammerWeightedPerturbationCoefficient_log_le
      N P A k W E 0 L hA (by exact_mod_cast hC) (by exact_mod_cast hV)
      hZ0 hZR hden hRone hcoeffPos hcommonPos hZAeq hReq hlogTwo'
      hZAterm hcommon hRterm




lemma structured_stage_perturbation_log_le_fixed_radius
    {r L j C V D : ℕ} (ell : Fin (r + 1) → ℂ)
    (cC cV : ℝ)
    (hr : r ≤ 8) (hcV : 0 ≤ cV)
    (hL : 2 ≤ L) (hDlow : 2 ≤ D) (hDhigh : D ≤ L)
    (hlogL : 1 ≤ Real.log (L : ℝ))
    (hC : 0 < C) (hV : 0 < V)
    (hj : j < dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24))
    (hlogC : Real.log (C : ℝ) ≤
      cC * (L : ℝ) ^ 34 * Real.log (L : ℝ))
    (hlogV : Real.log (V : ℝ) ≤ cV * Real.log (L : ℝ)) :
    let N := (L ^ 32) ^ (r + 1)
    let P := L ^ 24
    let A := scaledDyadicStageA (L ^ 2) j
    let k := L ^ 33
    let m := dyadicStageCount (N * P)
    let W := stageSpendBudget m k (j + 1)
    let T := stageUnitBudget m (j + 1)
    let S := W
    let E := T + r * S
    let U : ℝ := (L ^ 32 : ℕ) * ∑ i, ‖ell i‖
    let R : ℝ := (D : ℝ) * (2 * A : ℕ)
    let Z : ℝ := (2 * A : ℕ)
    let cE : ℝ := 314 * 9
    let cCore : ℝ := 312 + cC + cE * cV + 315 * (315 + 34) +
      318 + 2 * (∑ i, ‖ell i‖) + cV + 4
    let cPerturb : ℝ := 3956 + cCore
    Real.log (pochhammerWeightedPerturbationCoefficient
        N P A k W E 0 (C : ℝ) (V : ℝ) U R Z) ≤
      cPerturb * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
  dsimp only
  let N := (L ^ 32) ^ (r + 1)
  let P := L ^ 24
  let A := scaledDyadicStageA (L ^ 2) j
  let k := L ^ 33
  let m := dyadicStageCount (N * P)
  let W := stageSpendBudget m k (j + 1)
  let T := stageUnitBudget m (j + 1)
  let S := W
  let E := T + r * S
  let U : ℝ := (L ^ 32 : ℕ) * ∑ i, ‖ell i‖
  let R : ℝ := (D : ℝ) * (2 * A : ℕ)
  let Z : ℝ := (2 * A : ℕ)
  let cE : ℝ := 314 * 9
  let cCore : ℝ := 312 + cC + cE * cV + 315 * (315 + 34) +
    318 + 2 * (∑ i, ‖ell i‖) + cV + 4
  let cPerturb : ℝ := 3956 + cCore
  have hLpos : 0 < L := by omega
  have hLone : 1 ≤ L := by omega
  have hLoneR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLone
  have hDoneR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (show 1 ≤ D by omega)
  have hpow694one : (1 : ℝ) ≤ (L : ℝ) ^ 694 := one_le_pow₀ hLoneR
  have hlogPos : 0 < Real.log (L : ℝ) := lt_of_lt_of_le zero_lt_one hlogL
  have hN : 0 < N := by dsimp [N]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hA : 0 < A := by dsimp [A]; exact scaledDyadicStageA_pos (by positivity) j
  have hk : 0 < k := by dsimp [k]; positivity
  have hb := box_parameter_budget_bounds hr hL
  dsimp only at hb
  have hWsrc : m * k + 1 ≤ 314 * L ^ 34 := by
    simpa [m, N, P, k] using hb.2.1
  have hTsrc : m + 1 ≤ 314 * L := by
    simpa [m, N, P] using hb.2.2
  have hWbd : W ≤ 314 * L ^ 34 :=
    (stageSpendBudget_le_zero m k (j + 1)).trans hWsrc
  have hTbd : T ≤ 314 * L :=
    (stageUnitBudget_le_zero m (j + 1)).trans hTsrc
  have hWpos : 0 < W := by dsimp [W, stageSpendBudget]; omega
  have hEbd : E ≤ 314 * 9 * L ^ 34 := by
    have hL34 : L ≤ L ^ 34 := by
      simpa using Nat.pow_le_pow_right hLone (show 1 ≤ 34 by omega)
    dsimp [E, S]
    calc
      T + r * W ≤ 314 * L + 8 * (314 * L ^ 34) := by gcongr
      _ ≤ 314 * L ^ 34 + 8 * (314 * L ^ 34) := by gcongr
      _ = 314 * 9 * L ^ 34 := by ring
  have hAupper0 := scaledDyadicStageA_parameter_upper hL hj
  have hNpow : N * P ≤ L ^ 312 := by
    have he : 32 * (r + 1) + 24 ≤ 312 := by omega
    have heq : N * P = L ^ (32 * (r + 1) + 24) := by
      dsimp [N, P]
      rw [← pow_mul, ← pow_add]
    rw [heq]
    exact Nat.pow_le_pow_right hLone he
  have hApoly : A ≤ 2 * L ^ 314 := by
    have hAstep : A ≤ scaledDyadicStageA (L ^ 2) (j + 1) := by
      dsimp [A, scaledDyadicStageA]
      exact Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by omega) (Nat.le_succ j))
    calc
      A ≤ scaledDyadicStageA (L ^ 2) (j + 1) := hAstep
      _ ≤ 2 * L ^ 2 * (N * P) := by simpa [N, P] using hAupper0
      _ ≤ 2 * L ^ 2 * L ^ 312 := by gcongr
      _ = 2 * L ^ 314 := by ring
  have hkL34 : k ≤ L ^ 34 := by
    dsimp [k]
    exact Nat.pow_le_pow_right hLone (by omega)
  have hWk : W + k ≤ 315 * L ^ 34 := by omega
  have hAk : A * k ≤ 2 * L ^ 347 := by
    calc
      A * k ≤ (2 * L ^ 314) * L ^ 33 := by gcongr
      _ = 2 * L ^ 347 := by ring
  have hAPA : A + 1 + P ≤ 4 * L ^ 314 := by
    have hP314 : P ≤ L ^ 314 := by
      dsimp [P]
      exact Nat.pow_le_pow_right hLone (by omega)
    have hOne314 : 1 ≤ L ^ 314 := Nat.one_le_pow _ _ hLone
    omega
  have hZA : 2 * A + A ≤ 6 * L ^ 314 := by omega
  have hRnat : D * (2 * A) ≤ 4 * L ^ 315 := by
    calc
      D * (2 * A) ≤ L * (2 * (2 * L ^ 314)) := by gcongr
      _ = 4 * L ^ 315 := by ring
  have hHermBase : 2 * (A + 1) ≤ 6 * L ^ 314 := by
    have hOne314 : 1 ≤ L ^ 314 := Nat.one_le_pow _ _ hLone
    omega
  have hlogAk := log_nat_le_poly (n := A * k) (c := 2) (e := 347)
    (by positivity) (by norm_num) hLpos hlogL hAk
  have hlogZA := log_nat_le_poly (n := 2 * A + A) (c := 6) (e := 314)
    (by positivity) (by norm_num) hLpos hlogL hZA
  have hlogR := log_nat_le_poly (n := D * (2 * A)) (c := 4) (e := 315)
    (by positivity) (by norm_num) hLpos hlogL hRnat
  have hlogAPA := log_nat_le_poly (n := A + 1 + P) (c := 4) (e := 314)
    (by positivity) (by norm_num) hLpos hlogL hAPA
  have hlogHermBase := log_nat_le_poly (n := 2 * (A + 1))
    (c := 6) (e := 314) (by positivity) (by norm_num) hLpos hlogL hHermBase
  have hfacWk := log_nat_factorial_le_poly (n := W + k)
    (c := 315) (e := 34) (by positivity) (by norm_num) hLpos hlogL hWk
  have hfacAk := log_nat_factorial_le_poly (n := A * k)
    (c := 2) (e := 347) (by positivity) (by norm_num) hLpos hlogL hAk
  have hcC : 0 ≤ cC :=
    coefficient_nonneg_of_log_bound hC hLpos hlogPos hlogC
  have hlogV0 : 0 ≤ Real.log (V : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ V by omega))
  have hElogV : (E : ℝ) * Real.log (V : ℝ) ≤
      cE * cV * (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
    calc
      (E : ℝ) * Real.log (V : ℝ) ≤
          ((314 * 9 : ℕ) : ℝ) * (L : ℝ) ^ 34 *
            (cV * Real.log (L : ℝ)) := by
        apply mul_le_mul (by exact_mod_cast hEbd) hlogV hlogV0 (by positivity)
      _ = cE * cV * (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
        dsimp [cE]
        ring
  have hlogNP : Real.log (N * P : ℕ) ≤ 312 * Real.log (L : ℝ) := by
    have hp : (0 : ℝ) < ((N * P : ℕ) : ℝ) := by positivity
    calc
      Real.log (N * P : ℕ) ≤ Real.log ((L ^ 312 : ℕ) : ℝ) :=
        Real.log_le_log hp (by exact_mod_cast hNpow)
      _ = 312 * Real.log (L : ℝ) := by
        push_cast
        rw [Real.log_pow]
        norm_num
  have hlogTwo : Real.log 2 ≤ 2 * Real.log (L : ℝ) := by
    have h2 : Real.log 2 ≤ 2 :=
      (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans (by norm_num)
    exact h2.trans (by nlinarith)
  have hpow34 : (L : ℝ) ^ 34 ≤ (L : ℝ) ^ 694 :=
    pow_le_pow_right₀ (by exact_mod_cast hLone) (by omega)
  have hpow24 : (L : ℝ) ^ 24 ≤ (L : ℝ) ^ 694 :=
    pow_le_pow_right₀ (by exact_mod_cast hLone) (by omega)
  have hpow33 : (L : ℝ) ^ 33 ≤ (L : ℝ) ^ 694 :=
    pow_le_pow_right₀ (by exact_mod_cast hLone) (by omega)
  have hpow346 : (L : ℝ) ^ 346 ≤ (L : ℝ) ^ 694 :=
    pow_le_pow_right₀ (by exact_mod_cast hLone) (by omega)
  have hpow347 : (L : ℝ) ^ 347 ≤ (L : ℝ) ^ 694 :=
    pow_le_pow_right₀ (by exact_mod_cast hLone) (by omega)
  have hAkR : (A * k : ℕ) ≤ 2 * L ^ 347 := hAk
  have hAkCast : ((A * k : ℕ) : ℝ) ≤ 2 * (L : ℝ) ^ 347 := by
    exact_mod_cast hAkR
  have hAkSq : ((A * k : ℕ) : ℝ) ^ 2 ≤ 4 * (L : ℝ) ^ 694 := by
    calc
      ((A * k : ℕ) : ℝ) ^ 2 ≤ (2 * (L : ℝ) ^ 347) ^ 2 := by gcongr
      _ = 4 * (L : ℝ) ^ 694 := by ring
  have hlogHermite : Real.log (hermiteInterpolationBound A k) ≤
      1978 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
    have hsecond : ((A * k : ℕ) : ℝ) ^ 2 *
        Real.log (2 * (A + 1 : ℝ)) ≤
        1280 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
      have hbaseEq : 2 * (A + 1 : ℝ) = ((2 * (A + 1) : ℕ) : ℝ) := by
        push_cast
        ring
      rw [hbaseEq]
      calc
        _ ≤ (4 * (L : ℝ) ^ 694) * (320 * Real.log (L : ℝ)) := by
          apply mul_le_mul hAkSq (by simpa using hlogHermBase)
            (Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * (A + 1) by omega)))
            (by positivity)
        _ = _ := by ring
    have hfirst : Real.log ((A * k).factorial : ℝ) ≤
        698 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
      calc
        _ ≤ 698 * (L : ℝ) ^ 347 * Real.log (L : ℝ) := by
          norm_num at hfacAk ⊢
          exact hfacAk
        _ ≤ 698 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by gcongr
    exact hermiteInterpolationBound_log_le A k hA hk hfirst hsecond
  have hcore : Real.log (pochhammerWeightedPerturbationCore
      N P A k W E 0 (C : ℝ) (V : ℝ) U) ≤
      cCore * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
    have hfacWk' : Real.log ((W + k).factorial : ℝ) ≤
        (315 * (315 + 34) : ℕ) * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
      calc
        _ ≤ (315 * (315 + 34) : ℕ) * (L : ℝ) ^ 34 * Real.log (L : ℝ) := hfacWk
        _ ≤ _ := by gcongr
    have hPterm : (P : ℝ) * Real.log ((A + 1 + P : ℕ) : ℝ) ≤
        318 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
      have hPcast : (P : ℝ) = (L : ℝ) ^ 24 := by simp [P]
      have hlogAPA' : Real.log ((A + 1 + P : ℕ) : ℝ) ≤
          318 * Real.log (L : ℝ) := by
        norm_num at hlogAPA ⊢
        exact hlogAPA
      rw [hPcast]
      calc
        _ ≤ (L : ℝ) ^ 24 * (318 * Real.log (L : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hlogAPA' (by positivity)
        _ ≤ (L : ℝ) ^ 694 * (318 * Real.log (L : ℝ)) := by gcongr
        _ = _ := by ring
    have hUA : U * (A : ℝ) ≤
        (2 * ∑ i, ‖ell i‖) * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
      have hAcast : (A : ℝ) ≤ 2 * (L : ℝ) ^ 314 := by exact_mod_cast hApoly
      have hraw : U * (A : ℝ) ≤
          (2 * ∑ i, ‖ell i‖) * (L : ℝ) ^ 346 := by
        dsimp [U]
        push_cast
        calc
          (L : ℝ) ^ 32 * (∑ i, ‖ell i‖) * (A : ℝ) ≤
              (L : ℝ) ^ 32 * (∑ i, ‖ell i‖) *
                (2 * (L : ℝ) ^ 314) := by gcongr
          _ = _ := by ring
      calc
        _ ≤ (2 * ∑ i, ‖ell i‖) * (L : ℝ) ^ 346 := hraw
        _ ≤ (2 * ∑ i, ‖ell i‖) * (L : ℝ) ^ 694 := by
          exact mul_le_mul_of_nonneg_left hpow346 (by positivity)
        _ ≤ (2 * ∑ i, ‖ell i‖) * (L : ℝ) ^ 694 *
            Real.log (L : ℝ) := by
          apply le_mul_of_one_le_right
          · exact mul_nonneg
              (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))
              (pow_nonneg (by positivity) _)
          · exact hlogL
    have hkV : (k : ℝ) * Real.log (V : ℝ) ≤
        cV * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
      have hkcast : (k : ℝ) = (L : ℝ) ^ 33 := by simp [k]
      rw [hkcast]
      calc
        _ ≤ (L : ℝ) ^ 33 * (cV * Real.log (L : ℝ)) := by gcongr
        _ ≤ (L : ℝ) ^ 694 * (cV * Real.log (L : ℝ)) := by
          gcongr
        _ = _ := by ring
    have htwoK : ((2 * k : ℕ) : ℝ) * Real.log 2 ≤
        4 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
      have hkcast : (k : ℝ) = (L : ℝ) ^ 33 := by simp [k]
      push_cast
      rw [hkcast]
      calc
        2 * (L : ℝ) ^ 33 * Real.log 2 ≤
            2 * (L : ℝ) ^ 33 * (2 * Real.log (L : ℝ)) := by gcongr
        _ ≤ 2 * (L : ℝ) ^ 694 * (2 * Real.log (L : ℝ)) := by gcongr
        _ = _ := by ring
    have hNP' : Real.log (N * P : ℕ) ≤
        312 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
      calc
        _ ≤ 312 * Real.log (L : ℝ) := hlogNP
        _ ≤ 312 * ((L : ℝ) ^ 694 * Real.log (L : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right hpow694one hlogPos.le)
        _ = 312 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by ring
    have hC' : Real.log (C : ℝ) ≤
        cC * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
      apply hlogC.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow34 hcC) hlogPos.le
    have hEV' : (E : ℝ) * Real.log (V : ℝ) ≤
        cE * cV * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
      apply hElogV.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow34 (by dsimp [cE]; positivity)) hlogPos.le
    exact pochhammerWeightedPerturbationCore_log_le
      N P A k W E 0 hN hP (by exact_mod_cast hC) (by exact_mod_cast hV)
        hNP' hC' hEV' hfacWk' hPterm hUA hkV htwoK
  have hcommon : Real.log (pochhammerWeightedPerturbationCommon
      N P A k W E 0 (C : ℝ) (V : ℝ) U) ≤
      (2676 + cCore) * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
    have hlogAk' : 2 * Real.log ((A * k : ℕ) : ℝ) ≤
        698 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
      have hlogAkNum : Real.log ((A * k : ℕ) : ℝ) ≤
          349 * Real.log (L : ℝ) := by
        norm_num at hlogAk ⊢
        exact hlogAk
      calc
        _ ≤ 2 * (349 * Real.log (L : ℝ)) := by linarith
        _ = 698 * Real.log (L : ℝ) := by ring
        _ ≤ 698 * ((L : ℝ) ^ 694 * Real.log (L : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right hpow694one hlogPos.le)
        _ = 698 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by ring
    exact pochhammerWeightedPerturbationCommon_log_le
      N P A k W E 0 hN hP hA hk (by exact_mod_cast hC) (by exact_mod_cast hV)
        hlogAk' hlogHermite hcore
  have hRone : 1 ≤ R := by
    dsimp [R]
    push_cast
    exact one_le_mul_of_one_le_of_one_le hDoneR
      (by exact_mod_cast (show 1 ≤ 2 * A by omega))
  have hden : 1 ≤ R - A := by
    have hfactor : (1 : ℝ) ≤ 2 * (D : ℝ) - 1 := by
      have hDR : (2 : ℝ) ≤ D := by exact_mod_cast hDlow
      linarith
    have hAR : (1 : ℝ) ≤ A := by exact_mod_cast (show 1 ≤ A by omega)
    calc
      1 ≤ (2 * (D : ℝ) - 1) * (A : ℝ) :=
        one_le_mul_of_one_le_of_one_le hfactor hAR
      _ = R - A := by
        dsimp [R]
        push_cast
        ring
  have hcommonPos : 0 < pochhammerWeightedPerturbationCommon
      N P A k W E 0 (C : ℝ) (V : ℝ) U := by
    unfold pochhammerWeightedPerturbationCommon
      pochhammerWeightedPerturbationCore hermiteInterpolationBound
    positivity
  have hcoeffPos : 0 < pochhammerWeightedPerturbationCoefficient
      N P A k W E 0 (C : ℝ) (V : ℝ) U R Z := by
    have hden0 : 0 < (R - (A : ℝ)) ^ (k * A) := by
      exact pow_pos (zero_lt_one.trans_le hden) _
    unfold pochhammerWeightedPerturbationCoefficient
    change 0 < (Z + A) ^ (k * A) *
        (pochhammerWeightedPerturbationCommon
          N P A k W E 0 (C : ℝ) (V : ℝ) U *
          max 1 (R ^ (A * k)) / (R - A) ^ (k * A)) +
      pochhammerWeightedPerturbationCommon
          N P A k W E 0 (C : ℝ) (V : ℝ) U *
        max 1 (Z ^ (A * k))
    apply add_pos_of_nonneg_of_pos
    · exact mul_nonneg (by positivity)
        (div_nonneg
          (mul_nonneg hcommonPos.le (zero_le_one.trans (le_max_left _ _)))
          hden0.le)
    · exact mul_pos hcommonPos
        (zero_lt_one.trans_le (le_max_left _ _))
  have hZ0 : 0 ≤ Z := by dsimp [Z]; positivity
  have hZR : Z ≤ R := by
    dsimp [Z, R]
    push_cast
    exact le_mul_of_one_le_left (by positivity) hDoneR
  have hZAeq : Z + A = ((2 * A + A : ℕ) : ℝ) := by
    dsimp [Z]
    push_cast
    ring
  have hReq : R = ((D * (2 * A) : ℕ) : ℝ) := by
    dsimp [R]
    push_cast
    ring
  have hZAterm : ((A * k : ℕ) : ℝ) * Real.log ((2 * A + A : ℕ) : ℝ) ≤
      640 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
    have hlogZA' : Real.log ((2 * A + A : ℕ) : ℝ) ≤
        320 * Real.log (L : ℝ) := by
      norm_num at hlogZA ⊢
      exact hlogZA
    calc
      _ ≤ (2 * (L : ℝ) ^ 347) * (320 * Real.log (L : ℝ)) := by
        apply mul_le_mul hAkCast hlogZA'
        · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * A + A by omega))
        · positivity
      _ ≤ (2 * (L : ℝ) ^ 694) * (320 * Real.log (L : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow347 (by norm_num)) (by positivity)
      _ = _ := by ring
  have hRterm : ((A * k : ℕ) : ℝ) * Real.log ((D * (2 * A) : ℕ) : ℝ) ≤
      638 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
    have hlogR' : Real.log ((D * (2 * A) : ℕ) : ℝ) ≤
        319 * Real.log (L : ℝ) := by
      norm_num at hlogR ⊢
      exact hlogR
    calc
      _ ≤ (2 * (L : ℝ) ^ 347) * (319 * Real.log (L : ℝ)) := by
        apply mul_le_mul hAkCast hlogR'
        · have hpos : 0 < D * (2 * A) := by positivity
          exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ D * (2 * A) by omega))
        · positivity
      _ ≤ (2 * (L : ℝ) ^ 694) * (319 * Real.log (L : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow347 (by norm_num)) (by positivity)
      _ = _ := by ring
  have hlogTwo' : Real.log 2 ≤
      2 * (L : ℝ) ^ 694 * Real.log (L : ℝ) := by
    calc
      _ ≤ 2 * Real.log (L : ℝ) := hlogTwo
      _ ≤ 2 * ((L : ℝ) ^ 694 * Real.log (L : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right hpow694one hlogPos.le)) (by norm_num)
      _ = _ := by ring
  change Real.log (pochhammerWeightedPerturbationCoefficient
      N P A k W E 0 (C : ℝ) (V : ℝ) U R Z) ≤
    cPerturb * (L : ℝ) ^ 694 * Real.log (L : ℝ)
  exact pochhammerWeightedPerturbationCoefficient_log_le
      N P A k W E 0 D hA (by exact_mod_cast hC) (by exact_mod_cast hV)
      hZ0 hZR hden hRone hcoeffPos hcommonPos hZAeq hReq hlogTwo'
      hZAterm hcommon hRterm





lemma perturbation_product_le_half_target
    {lambda coeff coeffWorst X Xmax Q : ℝ}
    (hlambda : 0 ≤ lambda)
    (hcoeff : 0 ≤ coeff) (hcoeffWorst : 0 < coeffWorst)
    (hcoeffle : coeff ≤ coeffWorst)
    (hlogCoeff : Real.log coeffWorst ≤ Q)
    (hX : X ≤ Xmax)
    (hlambdaSmall : lambda ≤ Real.exp (-(Xmax + Q + Real.log 2))) :
    lambda * coeff ≤ Real.exp (-X) / 2 := by
  have hcoeffExp : coeffWorst ≤ Real.exp Q := by
    exact (Real.log_le_iff_le_exp hcoeffWorst).mp hlogCoeff
  have hmul : lambda * coeff ≤
      Real.exp (-(Xmax + Q + Real.log 2)) * Real.exp Q := by
    calc
      lambda * coeff ≤ lambda * coeffWorst := by gcongr
      _ ≤ Real.exp (-(Xmax + Q + Real.log 2)) * coeffWorst := by gcongr
      _ ≤ Real.exp (-(Xmax + Q + Real.log 2)) * Real.exp Q := by gcongr
  have hexpEq : Real.exp (-(Xmax + Q + Real.log 2)) * Real.exp Q =
      Real.exp (-Xmax) / 2 := by
    rw [← Real.exp_add]
    have htwo : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
    rw [show -(Xmax + Q + Real.log 2) + Q = -Xmax - Real.log 2 by ring,
      Real.exp_sub, htwo]
  have htarget : Real.exp (-Xmax) / 2 ≤ Real.exp (-X) / 2 := by
    gcongr
  exact hmul.trans (hexpEq ▸ htarget)

lemma pochhammer_liouville_exponent_le_worst_case
    {iota : Type*} [Fintype iota]
    (N P A W T S C V h v q : ℕ) (u : iota → ℕ) (Hbox d : ℝ)
    (hP : 0 < P) (hA : 0 < A) (hC : 0 < C) (hV : 1 ≤ V)
    (hd : 0 ≤ d) (hHbox : 0 ≤ Hbox)
    (hh : h < 2 * A) (hv : v < W) (hq : q < T)
    (hu : ∀ i, u i < S) :
    d * Real.log (N + 1 : ℕ) +
        d * Real.log
          (P * C * (v.factorial * (h + 1 + P) ^ P) *
            V ^ (q + ∑ i, u i) : ℕ) +
        (h : ℝ) * Hbox ≤
      d * Real.log (N + 1 : ℕ) +
        d * Real.log
          (P * C * W.factorial * (2 * A + P) ^ P *
            V ^ (T + Fintype.card iota * S) : ℕ) +
        (2 * A : ℕ) * Hbox := by
  have husum : ∑ i, u i ≤ Fintype.card iota * S := by
    calc
      ∑ i, u i ≤ ∑ _i : iota, S := by
        gcongr with i
        exact (hu i).le
      _ = Fintype.card iota * S := by simp
  have hexp : q + ∑ i, u i ≤ T + Fintype.card iota * S := by omega
  have hVpowN : V ^ (q + ∑ i, u i) ≤
      V ^ (T + Fintype.card iota * S) :=
    Nat.pow_le_pow_right hV hexp
  have hfacN : v.factorial ≤ W.factorial :=
    Nat.factorial_le (by omega)
  have hhbase : h + 1 + P ≤ 2 * A + P := by omega
  have hhpowN : (h + 1 + P) ^ P ≤ (2 * A + P) ^ P :=
    Nat.pow_le_pow_left hhbase P
  have hinside :
      P * C * (v.factorial * (h + 1 + P) ^ P) *
          V ^ (q + ∑ i, u i) ≤
        P * C * W.factorial * (2 * A + P) ^ P *
          V ^ (T + Fintype.card iota * S) := by
    calc
      P * C * (v.factorial * (h + 1 + P) ^ P) *
          V ^ (q + ∑ i, u i) ≤
        P * C * (W.factorial * (2 * A + P) ^ P) *
          V ^ (q + ∑ i, u i) := by gcongr
      _ ≤ P * C * (W.factorial * (2 * A + P) ^ P) *
          V ^ (T + Fintype.card iota * S) := by gcongr
      _ = P * C * W.factorial * (2 * A + P) ^ P *
          V ^ (T + Fintype.card iota * S) := by ring
  have hinsidePos :
      0 < P * C * (v.factorial * (h + 1 + P) ^ P) *
          V ^ (q + ∑ i, u i) := by positivity
  have hinsidePosR : (0 : ℝ) <
      (P * C * (v.factorial * (h + 1 + P) ^ P) *
        V ^ (q + ∑ i, u i) : ℕ) := by exact_mod_cast hinsidePos
  have hinsideR :
      ((P * C * (v.factorial * (h + 1 + P) ^ P) *
        V ^ (q + ∑ i, u i) : ℕ) : ℝ) ≤
      (P * C * W.factorial * (2 * A + P) ^ P *
        V ^ (T + Fintype.card iota * S) : ℕ) := by exact_mod_cast hinside
  have hlogInside := Real.log_le_log hinsidePosR hinsideR
  apply add_le_add
  · apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_left hlogInside hd
  · have hhR : (h : ℝ) ≤ (2 * A : ℕ) := by exact_mod_cast hh.le
    exact mul_le_mul_of_nonneg_right hhR hHbox

lemma log_boundary_nonneg
    (N P W E C V : ℕ) (R U : ℝ)
    (hN : 0 < N) (hP : 0 < P) (hC : 0 < C) (hV : 1 ≤ V)
    (hR : 0 ≤ R) (hU : 0 ≤ U) :
    0 ≤ Real.log
      (((N * P : ℕ) : ℝ) *
        ((C : ℝ) * (V : ℝ) ^ E * (W.factorial : ℝ) *
          (R + 1 + P) ^ P * Real.exp (U * R))) := by
  apply Real.log_nonneg
  have hNP : (1 : ℝ) ≤ (N * P : ℕ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (Nat.ne_of_gt hN) (Nat.ne_of_gt hP)))
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast (show 1 ≤ C by omega)
  have hV1 : (1 : ℝ) ≤ V := by exact_mod_cast hV
  have hfac : (1 : ℝ) ≤ W.factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero W)
  have hRP : (1 : ℝ) ≤ R + 1 + P := by
    have hP0 : (0 : ℝ) ≤ P := by positivity
    linarith
  have hexp : 1 ≤ Real.exp (U * R) := by
    simpa using Real.exp_le_exp.mpr (mul_nonneg hU hR)
  have hCV : 1 ≤ (C : ℝ) * (V : ℝ) ^ E :=
    one_le_mul_of_one_le_of_one_le hC1 (one_le_pow₀ hV1)
  have hCVF : 1 ≤ (C : ℝ) * (V : ℝ) ^ E * W.factorial :=
    one_le_mul_of_one_le_of_one_le hCV hfac
  have hCVFP : 1 ≤ (C : ℝ) * (V : ℝ) ^ E * W.factorial *
      (R + 1 + P) ^ P :=
    one_le_mul_of_one_le_of_one_le hCVF (one_le_pow₀ hRP)
  have hinner : 1 ≤ (C : ℝ) * (V : ℝ) ^ E * W.factorial *
      (R + 1 + P) ^ P * Real.exp (U * R) :=
    one_le_mul_of_one_le_of_one_le hCVFP hexp
  exact one_le_mul_of_one_le_of_one_le hNP hinner


lemma box_parameter_cardinality
    {r d L : ℕ} (hr : r ≤ 8) (hd : d ≤ 8)
    (hL : 2 ≤ L) (hbig : 314 ^ 9 * 314 * 8 < L ^ 5) :
    let K := L ^ 32
    let P := L ^ 24
    let spend := L ^ 33
    let m := dyadicStageCount (K ^ (r + 1) * P)
    (1 * (m * spend + 1) * (m + 1) * (m * spend + 1) ^ r) * d <
      K ^ (r + 1) * P := by
  dsimp only
  let m := dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24)
  have hm : m ≤ 313 * L :=
    dyadicStageCount_box_parameter_bound hr hL
  have hLone : 1 ≤ L ^ 34 := Nat.one_le_pow _ _ (by omega)
  have hbudget : m * L ^ 33 + 1 ≤ 314 * L ^ 34 := by
    calc
      m * L ^ 33 + 1 ≤ (313 * L) * L ^ 33 + L ^ 34 :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hm) hLone
      _ = 314 * L ^ 34 := by ring
  have hstage : m + 1 ≤ 314 * L := by
    calc
      m + 1 ≤ 313 * L + L := Nat.add_le_add hm (by omega)
      _ = 314 * L := by ring
  have hpowConst : 314 ^ (r + 1) ≤ 314 ^ 9 := by
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hrow :
      (m * L ^ 33 + 1) * (m + 1) *
          (m * L ^ 33 + 1) ^ r * d ≤
        (314 ^ 9 * 314 * 8) * L ^ (34 * (r + 1) + 1) := by
    calc
      (m * L ^ 33 + 1) * (m + 1) *
          (m * L ^ 33 + 1) ^ r * d =
          (m * L ^ 33 + 1) ^ (r + 1) * (m + 1) * d := by
            rw [pow_succ']
            ring
      _ ≤ (314 * L ^ 34) ^ (r + 1) * (314 * L) * 8 := by
        gcongr
      _ = (314 ^ (r + 1) * 314 * 8) *
          L ^ (34 * (r + 1) + 1) := by
        rw [mul_pow, ← pow_mul]
        ring
      _ ≤ (314 ^ 9 * 314 * 8) * L ^ (34 * (r + 1) + 1) := by
        gcongr
  have hexp : 34 * (r + 1) + 1 + 5 ≤ 32 * (r + 1) + 24 := by
    omega
  calc
    (1 * (m * L ^ 33 + 1) * (m + 1) *
        (m * L ^ 33 + 1) ^ r) * d ≤
        (314 ^ 9 * 314 * 8) * L ^ (34 * (r + 1) + 1) := by
      simpa [m] using hrow
    _ < L ^ 5 * L ^ (34 * (r + 1) + 1) :=
      Nat.mul_lt_mul_of_pos_right hbig (by positivity)
    _ = L ^ (34 * (r + 1) + 1 + 5) := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ L ^ (32 * (r + 1) + 24) :=
      Nat.pow_le_pow_right (by omega) hexp
    _ = (L ^ 32) ^ (r + 1) * L ^ 24 := by
      symm
      rw [← pow_mul, ← pow_add]

lemma boxPochhammerStructuredCoefficientMajorant_cast_le_duplicate
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) {M : ℝ}
    {r B K P A W T S : ℕ} (alpha : Fin (r + 1) → F)
    (hK : 0 < K) (hP : 0 < P) (hA : 0 < A) (hW : 0 < W)
    (hM : 1 ≤ M)
    (hhalf : 2 * ((A * W * T * S ^ r) * Fintype.card ι) ≤
      K ^ (r + 1) * P) :
    let Halpha := ∑ i, Height.logHeight₁ (alpha i)
    let V := boxMomentCoordinateBound B K
    let Hentry : ℝ :=
      (Module.finrank ℚ F : ℝ) *
          Real.log ((W.factorial * (A + P) ^ P : ℕ) : ℝ) +
        (A : ℝ) * ((K : ℝ) * Halpha) +
        ((T + r * S : ℕ) : ℝ) *
          ((Module.finrank ℚ F : ℝ) * Real.log (V : ℝ))
    let Qbound : ℝ :=
      (Real.exp Halpha ^ (r + 1)) ^ ((r + 1) * K * A)
    (boxPochhammerStructuredCoefficientMajorant
      basis M r B K P A W T S alpha : ℝ) ≤
      2 * (K ^ (r + 1) * P : ℕ) *
        ((Module.finrank ℚ F : ℝ) * Qbound * Real.exp Hentry * M) := by
  dsimp only
  let Halpha : ℝ := ∑ i, Height.logHeight₁ (alpha i)
  let V := boxMomentCoordinateBound B K
  let Hentry : ℝ :=
      (Module.finrank ℚ F : ℝ) *
          Real.log ((W.factorial * (A + P) ^ P : ℕ) : ℝ) +
        (A : ℝ) * ((K : ℝ) * Halpha) +
        ((T + r * S : ℕ) : ℝ) *
          ((Module.finrank ℚ F : ℝ) * Real.log (V : ℝ))
  let Qbound : ℝ :=
    (Real.exp Halpha ^ (r + 1)) ^ ((r + 1) * K * A)
  have hHalpha : 0 ≤ Halpha := by
    dsimp [Halpha]
    positivity
  have hV : 1 ≤ V := one_le_boxMomentCoordinateBound hK
  have hfac : 1 ≤ W.factorial * (A + P) ^ P :=
    one_le_mul_of_one_le_of_one_le
      (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero W))
      (Nat.one_le_pow _ _ (by omega))
  have hHentry : 0 ≤ Hentry := by
    dsimp [Hentry]
    have hlogfac : 0 ≤
        Real.log ((W.factorial * (A + P) ^ P : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hfac)
    have hlogV : 0 ≤ Real.log (V : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hV)
    positivity
  have hQbound : 1 ≤ Qbound := by
    dsimp [Qbound]
    have he : 1 ≤ Real.exp Halpha := by
      simpa using Real.exp_le_exp.mpr hHalpha
    exact one_le_pow₀ (one_le_pow₀ he)
  have hd : Fintype.card ι = Module.finrank ℚ F := by
    rw [← Module.finrank_eq_card_basis basis]
  have hgeneric :=
    structuredKernelCoefficientMajorant_cast_le
      (rows := A * W * T * S ^ r) (cols := K ^ (r + 1) * P)
      (d := Fintype.card ι) (Q := Qbound) (H := Hentry) (M := M)
      (by positivity)
      (by
        rw [hd]
        exact_mod_cast Module.finrank_pos (R := ℚ) (M := F))
      hQbound hHentry hM hhalf
  simpa [boxPochhammerStructuredCoefficientMajorant,
    Halpha, V, Hentry, Qbound, hd] using hgeneric

lemma box_parameter_cardinality_general
    {r d D L : ℕ} (hr : r ≤ 8) (hd : d ≤ D)
    (hL : 2 ≤ L) (hbig : 314 ^ 9 * 314 * D < L ^ 5) :
    let K := L ^ 32
    let P := L ^ 24
    let spend := L ^ 33
    let m := dyadicStageCount (K ^ (r + 1) * P)
    (1 * (m * spend + 1) * (m + 1) * (m * spend + 1) ^ r) * d <
      K ^ (r + 1) * P := by
  dsimp only
  let m := dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24)
  have hm : m ≤ 313 * L :=
    dyadicStageCount_box_parameter_bound hr hL
  have hLone : 1 ≤ L ^ 34 := Nat.one_le_pow _ _ (by omega)
  have hbudget : m * L ^ 33 + 1 ≤ 314 * L ^ 34 := by
    calc
      m * L ^ 33 + 1 ≤ (313 * L) * L ^ 33 + L ^ 34 :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hm) hLone
      _ = 314 * L ^ 34 := by ring
  have hstage : m + 1 ≤ 314 * L := by
    calc
      m + 1 ≤ 313 * L + L := Nat.add_le_add hm (by omega)
      _ = 314 * L := by ring
  have hpowConst : 314 ^ (r + 1) ≤ 314 ^ 9 := by
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hrow :
      (m * L ^ 33 + 1) * (m + 1) *
          (m * L ^ 33 + 1) ^ r * d ≤
        (314 ^ 9 * 314 * D) * L ^ (34 * (r + 1) + 1) := by
    calc
      (m * L ^ 33 + 1) * (m + 1) *
          (m * L ^ 33 + 1) ^ r * d =
          (m * L ^ 33 + 1) ^ (r + 1) * (m + 1) * d := by
            rw [pow_succ']
            ring
      _ ≤ (314 * L ^ 34) ^ (r + 1) * (314 * L) * D := by
        gcongr
      _ = (314 ^ (r + 1) * 314 * D) *
          L ^ (34 * (r + 1) + 1) := by
        rw [mul_pow, ← pow_mul]
        ring
      _ ≤ (314 ^ 9 * 314 * D) * L ^ (34 * (r + 1) + 1) := by
        gcongr
  have hexp : 34 * (r + 1) + 1 + 5 ≤ 32 * (r + 1) + 24 := by
    omega
  calc
    (1 * (m * L ^ 33 + 1) * (m + 1) *
        (m * L ^ 33 + 1) ^ r) * d ≤
        (314 ^ 9 * 314 * D) * L ^ (34 * (r + 1) + 1) := by
      simpa [m] using hrow
    _ < L ^ 5 * L ^ (34 * (r + 1) + 1) :=
      Nat.mul_lt_mul_of_pos_right hbig (by positivity)
    _ = L ^ (34 * (r + 1) + 1 + 5) := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ L ^ (32 * (r + 1) + 24) :=
      Nat.pow_le_pow_right (by omega) hexp
    _ = (L ^ 32) ^ (r + 1) * L ^ 24 := by
      symm
      rw [← pow_mul, ← pow_add]

lemma box_parameter_half_cardinality
    {r d L : ℕ} (hr : r ≤ 8) (hd : d ≤ 8)
    (hL : 2 ≤ L) (hbig : 314 ^ 9 * 314 * 16 < L ^ 5) :
    let K := L ^ 32
    let P := L ^ 24
    let spend := L ^ 33
    let m := dyadicStageCount (K ^ (r + 1) * P)
    2 * ((1 * (m * spend + 1) * (m + 1) *
      (m * spend + 1) ^ r) * d) ≤ K ^ (r + 1) * P := by
  dsimp only
  have h := box_parameter_cardinality_general
    (r := r) (d := 2 * d) (D := 16) hr (by omega) hL hbig
  dsimp only at h
  calc
    2 * ((1 *
        (dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24) * L ^ 33 + 1) *
        (dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24) + 1) *
        (dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24) * L ^ 33 + 1) ^ r) * d) =
      (1 *
        (dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24) * L ^ 33 + 1) *
        (dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24) + 1) *
        (dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24) * L ^ 33 + 1) ^ r) *
          (2 * d) := by ring
    _ ≤ (L ^ 32) ^ (r + 1) * L ^ 24 := h.le

lemma box_parameter_cardinality_initial_sq
    {r d L : ℕ} (hr : r ≤ 8) (hd : d ≤ 8)
    (hL : 2 ≤ L) (hbig : 314 ^ 9 * 314 * 8 < L ^ 3) :
    let K := L ^ 32
    let P := L ^ 24
    let Ainit := L ^ 2
    let spend := L ^ 33
    let m := dyadicStageCount (K ^ (r + 1) * P)
    (Ainit * (m * spend + 1) * (m + 1) *
      (m * spend + 1) ^ r) * d < K ^ (r + 1) * P := by
  dsimp only
  have hd' : L ^ 2 * d ≤ 8 * L ^ 2 := by
    nlinarith [Nat.mul_le_mul_left (L ^ 2) hd]
  have hbig' : 314 ^ 9 * 314 * (8 * L ^ 2) < L ^ 5 := by
    calc
      314 ^ 9 * 314 * (8 * L ^ 2) =
          (314 ^ 9 * 314 * 8) * L ^ 2 := by ring
      _ < L ^ 3 * L ^ 2 := Nat.mul_lt_mul_of_pos_right hbig (by positivity)
      _ = L ^ 5 := by ring
  have h := box_parameter_cardinality_general
    (r := r) (d := L ^ 2 * d) (D := 8 * L ^ 2)
    hr hd' hL hbig'
  dsimp only at h
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

lemma box_parameter_half_cardinality_initial_sq
    {r d L : ℕ} (hr : r ≤ 8) (hd : d ≤ 8)
    (hL : 2 ≤ L) (hbig : 314 ^ 9 * 314 * 16 < L ^ 3) :
    let K := L ^ 32
    let P := L ^ 24
    let Ainit := L ^ 2
    let spend := L ^ 33
    let m := dyadicStageCount (K ^ (r + 1) * P)
    2 * ((Ainit * (m * spend + 1) * (m + 1) *
      (m * spend + 1) ^ r) * d) ≤ K ^ (r + 1) * P := by
  dsimp only
  have hd' : 2 * L ^ 2 * d ≤ 16 * L ^ 2 := by
    nlinarith [Nat.mul_le_mul_left (2 * L ^ 2) hd]
  have hbig' : 314 ^ 9 * 314 * (16 * L ^ 2) < L ^ 5 := by
    calc
      314 ^ 9 * 314 * (16 * L ^ 2) =
          (314 ^ 9 * 314 * 16) * L ^ 2 := by ring
      _ < L ^ 3 * L ^ 2 := Nat.mul_lt_mul_of_pos_right hbig (by positivity)
      _ = L ^ 5 := by ring
  have h := box_parameter_cardinality_general
    (r := r) (d := 2 * L ^ 2 * d) (D := 16 * L ^ 2)
    hr hd' hL hbig'
  dsimp only at h
  have heq :
      2 * ((L ^ 2 *
        (dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24) * L ^ 33 + 1) *
        (dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24) + 1) *
        (dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24) * L ^ 33 + 1) ^ r) * d) =
      (1 *
        (dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24) * L ^ 33 + 1) *
        (dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24) + 1) *
        (dyadicStageCount ((L ^ 32) ^ (r + 1) * L ^ 24) * L ^ 33 + 1) ^ r) *
          (2 * L ^ 2 * d) := by ring
  rw [heq]
  exact h.le


lemma pochhammerWeightedApproximationBound_zero_scaled
    (N P A k v q u : ℕ) (C V U D : ℝ)
    (hA : 0 < A) (hD : 1 < D) :
    pochhammerWeightedApproximationBound N P A k 1 v q u C V U
        (D * (2 * A : ℕ)) (2 * A : ℕ) 0 =
      (3 / (2 * D - 1)) ^ (k * A) *
        (((N * P : ℕ) : ℝ) *
          (C * V ^ (q + u) * (v.factorial : ℝ) *
            (D * (2 * A : ℕ) + 1 + P) ^ P *
            Real.exp (U * (D * (2 * A : ℕ))))) := by
  rw [pochhammerWeightedApproximationBound_zero]
  have hAR : ((A : ℝ) : ℝ) ≠ 0 := by positivity
  have hDR : 2 * D - 1 ≠ 0 := by linarith
  have hZA : ((2 * A : ℕ) : ℝ) + A = 3 * (A : ℝ) := by
    push_cast
    ring
  have hRA : D * ((2 * A : ℕ) : ℝ) - A =
      (2 * D - 1) * (A : ℝ) := by
    push_cast
    ring
  rw [hZA, hRA, mul_pow, mul_pow]
  field_simp
  <;> ring

lemma boundary_log_dominates_of_explicit_bounds
    (c : ℝ) {L : ℕ}
    (hL : max 1 (2 * max c 0) < (L : ℝ))
    (hlog : 2 * (max c 0 + Real.log 3) < Real.log (L : ℝ)) :
    c * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
        c * (L : ℝ) ^ 33 <
      (L : ℝ) ^ 33 * Real.log ((2 * (L : ℝ) - 1) / 3) := by
  let c' := max c 0
  have hcc' : c ≤ c' := le_max_left _ _
  have hc' : 0 ≤ c' := le_max_right _ _
  have hOneL : (1 : ℝ) < L := (le_max_left _ _).trans_lt hL
  have hLR : (0 : ℝ) < L := zero_lt_one.trans hOneL
  have hlogPos : 0 < Real.log (L : ℝ) := Real.log_pos hOneL
  have hcTerm :
      c * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) ≤
        c' * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    gcongr
  have hcPow : c * (L : ℝ) ^ 33 ≤ c' * (L : ℝ) ^ 33 := by
    gcongr
  have htwoC : 2 * c' < (L : ℝ) :=
    (le_max_right (1 : ℝ) (2 * c')).trans_lt hL
  have hfirst :
      c' * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) <
        (1 / 2 : ℝ) * ((L : ℝ) ^ 33 * Real.log (L : ℝ)) := by
    have hmul := mul_lt_mul_of_pos_right htwoC
      (show 0 < (L : ℝ) ^ 32 * Real.log (L : ℝ) by positivity)
    rw [pow_succ']
    nlinarith
  have hsecond :
      c' * (L : ℝ) ^ 33 + Real.log 3 * (L : ℝ) ^ 33 <
        (1 / 2 : ℝ) * ((L : ℝ) ^ 33 * Real.log (L : ℝ)) := by
    have hmul := mul_lt_mul_of_pos_right hlog
      (show 0 < (L : ℝ) ^ 33 by positivity)
    nlinarith
  have hratio :
      Real.log (L : ℝ) - Real.log 3 ≤
        Real.log ((2 * (L : ℝ) - 1) / 3) := by
    have hthree : (0 : ℝ) < 3 := by norm_num
    have hdivPos : 0 < (L : ℝ) / 3 := div_pos hLR hthree
    have hcomp : (L : ℝ) / 3 ≤ (2 * (L : ℝ) - 1) / 3 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      linarith
    rw [← Real.log_div hLR.ne' hthree.ne']
    exact Real.log_le_log hdivPos hcomp
  calc
    c * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) + c * (L : ℝ) ^ 33 ≤
        c' * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) + c' * (L : ℝ) ^ 33 :=
      add_le_add hcTerm hcPow
    _ < (L : ℝ) ^ 33 * (Real.log (L : ℝ) - Real.log 3) := by
      nlinarith
    _ ≤ (L : ℝ) ^ 33 * Real.log ((2 * (L : ℝ) - 1) / 3) := by
      gcongr


lemma eventually_boundary_log_dominates (c : ℝ) :
    ∀ᶠ L : ℕ in Filter.atTop,
      c * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
          c * (L : ℝ) ^ 33 <
        (L : ℝ) ^ 33 * Real.log ((2 * (L : ℝ) - 1) / 3) := by
  have hcastTop : Filter.Tendsto (fun L : ℕ ↦ (L : ℝ))
      Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have hlogTop : Filter.Tendsto (fun L : ℕ ↦ Real.log (L : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hcastTop
  have hLlarge := hcastTop.eventually
    (Filter.eventually_gt_atTop (max 1 (2 * max c 0)))
  have hlogLarge := hlogTop.eventually
    (Filter.eventually_gt_atTop (2 * (max c 0 + Real.log 3)))
  filter_upwards [hLlarge, hlogLarge] with L hL hlog
  let c' := max c 0
  have hcc' : c ≤ c' := le_max_left _ _
  have hc' : 0 ≤ c' := le_max_right _ _
  have hOneL : (1 : ℝ) < L := (le_max_left _ _).trans_lt hL
  have hLR : (0 : ℝ) < L := zero_lt_one.trans hOneL
  have hlogPos : 0 < Real.log (L : ℝ) := Real.log_pos hOneL
  have hcTerm :
      c * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) ≤
        c' * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) := by
    gcongr
  have hcPow : c * (L : ℝ) ^ 33 ≤ c' * (L : ℝ) ^ 33 := by
    gcongr
  have htwoC : 2 * c' < (L : ℝ) :=
    (le_max_right (1 : ℝ) (2 * c')).trans_lt hL
  have hfirst :
      c' * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) <
        (1 / 2 : ℝ) * ((L : ℝ) ^ 33 * Real.log (L : ℝ)) := by
    have hmul := mul_lt_mul_of_pos_right htwoC
      (show 0 < (L : ℝ) ^ 32 * Real.log (L : ℝ) by positivity)
    rw [pow_succ']
    nlinarith
  have hsecond :
      c' * (L : ℝ) ^ 33 + Real.log 3 * (L : ℝ) ^ 33 <
        (1 / 2 : ℝ) * ((L : ℝ) ^ 33 * Real.log (L : ℝ)) := by
    have hmul := mul_lt_mul_of_pos_right hlog
      (show 0 < (L : ℝ) ^ 33 by positivity)
    nlinarith
  have hratio :
      Real.log (L : ℝ) - Real.log 3 ≤
        Real.log ((2 * (L : ℝ) - 1) / 3) := by
    have hthree : (0 : ℝ) < 3 := by norm_num
    have hdivPos : 0 < (L : ℝ) / 3 := div_pos hLR hthree
    have hcomp : (L : ℝ) / 3 ≤ (2 * (L : ℝ) - 1) / 3 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      linarith
    rw [← Real.log_div hLR.ne' hthree.ne']
    exact Real.log_le_log hdivPos hcomp
  calc
    c * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) + c * (L : ℝ) ^ 33 ≤
        c' * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) + c' * (L : ℝ) ^ 33 :=
      add_le_add hcTerm hcPow
    _ < (L : ℝ) ^ 33 * (Real.log (L : ℝ) - Real.log 3) := by
      nlinarith
    _ ≤ (L : ℝ) ^ 33 * Real.log ((2 * (L : ℝ) - 1) / 3) := by
      gcongr


lemma boundary_master_of_log_inequality
    (N P A k W E C V : ℕ) (U D R X : ℝ)
    (hN : 0 < N) (hP : 0 < P) (hA : 0 < A) (hC : 0 < C)
    (hV : 0 < V) (hD : 1 < D) (hR : 0 ≤ R)
    (hlog :
      Real.log
          (((N * P : ℕ) : ℝ) *
            ((C : ℝ) * (V : ℝ) ^ E * (W.factorial : ℝ) *
              (R + 1 + P) ^ P * Real.exp (U * R))) + X <
        ((k * A : ℕ) : ℝ) * Real.log ((2 * D - 1) / 3)) :
    (3 / (2 * D - 1)) ^ (k * A) *
          (((N * P : ℕ) : ℝ) *
            ((C : ℝ) * (V : ℝ) ^ E * (W.factorial : ℝ) *
              (R + 1 + P) ^ P * Real.exp (U * R))) <
        Real.exp (-X) := by
  have hden : 0 < 2 * D - 1 := by linarith
  have hratio : 0 < 3 / (2 * D - 1) := div_pos (by norm_num) hden
  have hRP : 0 < R + 1 + (P : ℝ) := by positivity
  have hprod : 0 <
      (((N * P : ℕ) : ℝ) *
        ((C : ℝ) * (V : ℝ) ^ E * (W.factorial : ℝ) *
          (R + 1 + P) ^ P * Real.exp (U * R))) := by
    positivity
  have hleft : 0 <
      (3 / (2 * D - 1)) ^ (k * A) *
        (((N * P : ℕ) : ℝ) *
          ((C : ℝ) * (V : ℝ) ^ E * (W.factorial : ℝ) *
            (R + 1 + P) ^ P * Real.exp (U * R))) := by
    positivity
  apply (Real.log_lt_iff_lt_exp hleft).mp
  rw [Real.log_mul (pow_ne_zero _ hratio.ne') hprod.ne', Real.log_pow]
  have hratioEq : 3 / (2 * D - 1) = ((2 * D - 1) / 3)⁻¹ := by
    field_simp
  rw [hratioEq, Real.log_inv]
  nlinarith


lemma boundary_master_half_of_log_inequality
    (N P A k W E C V : ℕ) (U D R X : ℝ)
    (hN : 0 < N) (hP : 0 < P) (hA : 0 < A) (hC : 0 < C)
    (hV : 0 < V) (hD : 1 < D) (hR : 0 ≤ R)
    (hlog :
      Real.log
          (((N * P : ℕ) : ℝ) *
            ((C : ℝ) * (V : ℝ) ^ E * (W.factorial : ℝ) *
              (R + 1 + P) ^ P * Real.exp (U * R))) + X + Real.log 2 <
        ((k * A : ℕ) : ℝ) * Real.log ((2 * D - 1) / 3)) :
    (3 / (2 * D - 1)) ^ (k * A) *
          (((N * P : ℕ) : ℝ) *
            ((C : ℝ) * (V : ℝ) ^ E * (W.factorial : ℝ) *
              (R + 1 + P) ^ P * Real.exp (U * R))) <
        Real.exp (-X) / 2 := by
  have hmain := boundary_master_of_log_inequality
    N P A k W E C V U D R (X + Real.log 2)
    hN hP hA hC hV hD hR (by linarith)
  have hexp : Real.exp (-(X + Real.log 2)) = Real.exp (-X) / 2 := by
    rw [neg_add_rev, Real.exp_add, Real.exp_neg, Real.exp_log (by norm_num)]
    ring
  rw [← hexp]
  exact hmain

lemma approximation_lt_of_half_bounds
    (N P A k v q uTotal : ℕ) (C V U R Z lambdaNorm target : ℝ)
    (hzero : pochhammerWeightedApproximationBound N P A k 1 v q uTotal
        C V U R Z 0 < target / 2)
    (hperturb : lambdaNorm *
        pochhammerWeightedPerturbationCoefficient
          N P A k v q uTotal C V U R Z ≤ target / 2) :
    pochhammerWeightedApproximationBound N P A k 1 v q uTotal
        C V U R Z lambdaNorm < target := by
  rw [pochhammerWeightedApproximationBound_one_eq]
  linarith


theorem pochhammer_boundary_lt_of_worst_case
    {iota : Type*} [Fintype iota]
    (N P A k W T S C V : ℕ) (U D Hbox d : ℝ)
    (hP : 0 < P) (hA : 0 < A) (hD : 1 < D) (hC : 0 < C) (hV : 1 ≤ V)
    (hd : 0 ≤ d) (hHbox : 0 ≤ Hbox)
    (hmaster :
      (3 / (2 * D - 1)) ^ (k * A) *
          (((N * P : ℕ) : ℝ) *
            ((C : ℝ) * (V : ℝ) ^ (T + Fintype.card iota * S) *
              (W.factorial : ℝ) *
              (D * (2 * A : ℕ) + 1 + P) ^ P *
              Real.exp (U * (D * (2 * A : ℕ))))) <
        Real.exp (-(d * Real.log (N + 1 : ℕ) +
          d * Real.log
            (P * C * W.factorial * (2 * A + P) ^ P *
              V ^ (T + Fintype.card iota * S) : ℕ) +
          (2 * A : ℕ) * Hbox))) :
    ∀ h < 2 * A, ∀ v < W, ∀ q < T, ∀ u : iota → ℕ,
      (∀ i, u i < S) →
      pochhammerWeightedApproximationBound N P A k 1
          v q (∑ i, u i) C V U
          (D * (2 * A : ℕ)) (2 * A : ℕ) 0 <
        Real.exp (-(d * Real.log (N + 1 : ℕ) +
          d * Real.log
            (P * C * (v.factorial * (h + 1 + P) ^ P) *
              V ^ (q + ∑ i, u i) : ℕ) +
          (h : ℝ) * Hbox)) := by
  intro h hh v hv q hq u hu
  have husum : ∑ i, u i ≤ Fintype.card iota * S := by
    calc
      ∑ i, u i ≤ ∑ _i : iota, S := by
        gcongr with i
        exact (hu i).le
      _ = Fintype.card iota * S := by simp
  have hexp : q + ∑ i, u i ≤ T + Fintype.card iota * S := by omega
  have hVpowR : (V : ℝ) ^ (q + ∑ i, u i) ≤
      (V : ℝ) ^ (T + Fintype.card iota * S) := by
    exact pow_le_pow_right₀ (by exact_mod_cast hV) hexp
  have hVpowN : V ^ (q + ∑ i, u i) ≤
      V ^ (T + Fintype.card iota * S) :=
    Nat.pow_le_pow_right hV hexp
  have hfacN : v.factorial ≤ W.factorial :=
    Nat.factorial_le (by omega)
  have hfacR : (v.factorial : ℝ) ≤ W.factorial := by
    exact_mod_cast hfacN
  have hhbase : h + 1 + P ≤ 2 * A + P := by omega
  have hhpowN : (h + 1 + P) ^ P ≤ (2 * A + P) ^ P :=
    Nat.pow_le_pow_left hhbase P
  have hhpowR : ((h + 1 + P : ℕ) : ℝ) ^ P ≤
      ((2 * A + P : ℕ) : ℝ) ^ P := by
    exact_mod_cast hhpowN
  have hratioPow0 : 0 ≤ (3 / (2 * D - 1)) ^ (k * A) := by
    apply pow_nonneg
    apply div_nonneg (by norm_num)
    linarith
  have hleft :
      (3 / (2 * D - 1)) ^ (k * A) *
          (((N * P : ℕ) : ℝ) *
            ((C : ℝ) * (V : ℝ) ^ (q + ∑ i, u i) *
              (v.factorial : ℝ) *
              (D * (2 * A : ℕ) + 1 + P) ^ P *
              Real.exp (U * (D * (2 * A : ℕ))))) ≤
        (3 / (2 * D - 1)) ^ (k * A) *
          (((N * P : ℕ) : ℝ) *
            ((C : ℝ) * (V : ℝ) ^ (T + Fintype.card iota * S) *
              (W.factorial : ℝ) *
              (D * (2 * A : ℕ) + 1 + P) ^ P *
              Real.exp (U * (D * (2 * A : ℕ))))) := by
    apply mul_le_mul_of_nonneg_left _ hratioPow0
    gcongr
  have hinside :
      P * C * (v.factorial * (h + 1 + P) ^ P) *
          V ^ (q + ∑ i, u i) ≤
        P * C * W.factorial * (2 * A + P) ^ P *
          V ^ (T + Fintype.card iota * S) := by
    have hmiddle :
        v.factorial * (h + 1 + P) ^ P ≤
          W.factorial * (2 * A + P) ^ P :=
      Nat.mul_le_mul hfacN hhpowN
    calc
      P * C * (v.factorial * (h + 1 + P) ^ P) *
          V ^ (q + ∑ i, u i) ≤
        P * C * (W.factorial * (2 * A + P) ^ P) *
          V ^ (q + ∑ i, u i) := by gcongr
      _ ≤ P * C * (W.factorial * (2 * A + P) ^ P) *
          V ^ (T + Fintype.card iota * S) := by gcongr
      _ = P * C * W.factorial * (2 * A + P) ^ P *
          V ^ (T + Fintype.card iota * S) := by ring
  have hinsidePos :
      0 < P * C * (v.factorial * (h + 1 + P) ^ P) *
          V ^ (q + ∑ i, u i) := by
    positivity
  have hlogInside :
      Real.log
          (P * C * (v.factorial * (h + 1 + P) ^ P) *
            V ^ (q + ∑ i, u i) : ℕ) ≤
        Real.log
          (P * C * W.factorial * (2 * A + P) ^ P *
            V ^ (T + Fintype.card iota * S) : ℕ) := by
    exact Real.log_le_log (by exact_mod_cast hinsidePos) (by exact_mod_cast hinside)
  have hX :
      d * Real.log (N + 1 : ℕ) +
          d * Real.log
            (P * C * (v.factorial * (h + 1 + P) ^ P) *
              V ^ (q + ∑ i, u i) : ℕ) +
          (h : ℝ) * Hbox ≤
        d * Real.log (N + 1 : ℕ) +
          d * Real.log
            (P * C * W.factorial * (2 * A + P) ^ P *
              V ^ (T + Fintype.card iota * S) : ℕ) +
          (2 * A : ℕ) * Hbox := by
    gcongr
  rw [pochhammerWeightedApproximationBound_zero_scaled
    N P A k v q (∑ i, u i) C V U D hA hD]
  exact hleft.trans_lt (hmaster.trans_le (Real.exp_le_exp.mpr (neg_le_neg hX)))


theorem pochhammer_boundary_half_lt_of_worst_case
    {iota : Type*} [Fintype iota]
    (N P A k W T S C V : ℕ) (U D Hbox d : ℝ)
    (hP : 0 < P) (hA : 0 < A) (hD : 1 < D) (hC : 0 < C) (hV : 1 ≤ V)
    (hd : 0 ≤ d) (hHbox : 0 ≤ Hbox)
    (hmaster :
      (3 / (2 * D - 1)) ^ (k * A) *
          (((N * P : ℕ) : ℝ) *
            ((C : ℝ) * (V : ℝ) ^ (T + Fintype.card iota * S) *
              (W.factorial : ℝ) *
              (D * (2 * A : ℕ) + 1 + P) ^ P *
              Real.exp (U * (D * (2 * A : ℕ))))) <
        Real.exp (-(d * Real.log (N + 1 : ℕ) +
          d * Real.log
            (P * C * W.factorial * (2 * A + P) ^ P *
              V ^ (T + Fintype.card iota * S) : ℕ) +
          (2 * A : ℕ) * Hbox)) / 2) :
    ∀ h < 2 * A, ∀ v < W, ∀ q < T, ∀ u : iota → ℕ,
      (∀ i, u i < S) →
      pochhammerWeightedApproximationBound N P A k 1
          v q (∑ i, u i) C V U
          (D * (2 * A : ℕ)) (2 * A : ℕ) 0 <
        Real.exp (-(d * Real.log (N + 1 : ℕ) +
          d * Real.log
            (P * C * (v.factorial * (h + 1 + P) ^ P) *
              V ^ (q + ∑ i, u i) : ℕ) +
          (h : ℝ) * Hbox)) / 2 := by
  intro h hh v hv q hq u hu
  have husum : ∑ i, u i ≤ Fintype.card iota * S := by
    calc
      ∑ i, u i ≤ ∑ _i : iota, S := by
        gcongr with i
        exact (hu i).le
      _ = Fintype.card iota * S := by simp
  have hexp : q + ∑ i, u i ≤ T + Fintype.card iota * S := by omega
  have hVpowR : (V : ℝ) ^ (q + ∑ i, u i) ≤
      (V : ℝ) ^ (T + Fintype.card iota * S) := by
    exact pow_le_pow_right₀ (by exact_mod_cast hV) hexp
  have hVpowN : V ^ (q + ∑ i, u i) ≤
      V ^ (T + Fintype.card iota * S) :=
    Nat.pow_le_pow_right hV hexp
  have hfacN : v.factorial ≤ W.factorial :=
    Nat.factorial_le (by omega)
  have hfacR : (v.factorial : ℝ) ≤ W.factorial := by
    exact_mod_cast hfacN
  have hhbase : h + 1 + P ≤ 2 * A + P := by omega
  have hhpowN : (h + 1 + P) ^ P ≤ (2 * A + P) ^ P :=
    Nat.pow_le_pow_left hhbase P
  have hhpowR : ((h + 1 + P : ℕ) : ℝ) ^ P ≤
      ((2 * A + P : ℕ) : ℝ) ^ P := by
    exact_mod_cast hhpowN
  have hratioPow0 : 0 ≤ (3 / (2 * D - 1)) ^ (k * A) := by
    apply pow_nonneg
    apply div_nonneg (by norm_num)
    linarith
  have hleft :
      (3 / (2 * D - 1)) ^ (k * A) *
          (((N * P : ℕ) : ℝ) *
            ((C : ℝ) * (V : ℝ) ^ (q + ∑ i, u i) *
              (v.factorial : ℝ) *
              (D * (2 * A : ℕ) + 1 + P) ^ P *
              Real.exp (U * (D * (2 * A : ℕ))))) ≤
        (3 / (2 * D - 1)) ^ (k * A) *
          (((N * P : ℕ) : ℝ) *
            ((C : ℝ) * (V : ℝ) ^ (T + Fintype.card iota * S) *
              (W.factorial : ℝ) *
              (D * (2 * A : ℕ) + 1 + P) ^ P *
              Real.exp (U * (D * (2 * A : ℕ))))) := by
    apply mul_le_mul_of_nonneg_left _ hratioPow0
    gcongr
  have hinside :
      P * C * (v.factorial * (h + 1 + P) ^ P) *
          V ^ (q + ∑ i, u i) ≤
        P * C * W.factorial * (2 * A + P) ^ P *
          V ^ (T + Fintype.card iota * S) := by
    have hmiddle :
        v.factorial * (h + 1 + P) ^ P ≤
          W.factorial * (2 * A + P) ^ P :=
      Nat.mul_le_mul hfacN hhpowN
    calc
      P * C * (v.factorial * (h + 1 + P) ^ P) *
          V ^ (q + ∑ i, u i) ≤
        P * C * (W.factorial * (2 * A + P) ^ P) *
          V ^ (q + ∑ i, u i) := by gcongr
      _ ≤ P * C * (W.factorial * (2 * A + P) ^ P) *
          V ^ (T + Fintype.card iota * S) := by gcongr
      _ = P * C * W.factorial * (2 * A + P) ^ P *
          V ^ (T + Fintype.card iota * S) := by ring
  have hinsidePos :
      0 < P * C * (v.factorial * (h + 1 + P) ^ P) *
          V ^ (q + ∑ i, u i) := by
    positivity
  have hlogInside :
      Real.log
          (P * C * (v.factorial * (h + 1 + P) ^ P) *
            V ^ (q + ∑ i, u i) : ℕ) ≤
        Real.log
          (P * C * W.factorial * (2 * A + P) ^ P *
            V ^ (T + Fintype.card iota * S) : ℕ) := by
    exact Real.log_le_log (by exact_mod_cast hinsidePos) (by exact_mod_cast hinside)
  have hX :
      d * Real.log (N + 1 : ℕ) +
          d * Real.log
            (P * C * (v.factorial * (h + 1 + P) ^ P) *
              V ^ (q + ∑ i, u i) : ℕ) +
          (h : ℝ) * Hbox ≤
        d * Real.log (N + 1 : ℕ) +
          d * Real.log
            (P * C * W.factorial * (2 * A + P) ^ P *
              V ^ (T + Fintype.card iota * S) : ℕ) +
          (2 * A : ℕ) * Hbox := by
    gcongr
  rw [pochhammerWeightedApproximationBound_zero_scaled
    N P A k v q (∑ i, u i) C V U D hA hD]
  exact hleft.trans_lt (hmaster.trans_le
    (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hX))
      (by norm_num)))



theorem structured_box_small_of_norm_bound
    {r L C V d : ℕ} (ell : Fin (r + 1) → ℂ)
    (Halpha cC cV lambdaNorm : ℝ)
    (hr : r ≤ 8) (hd : d ≤ 8) (hHalpha : 0 ≤ Halpha)
    (hcV : 0 ≤ cV) (hlambda : 0 ≤ lambdaNorm)
    (hL : 4 ≤ L) (hlogL : 1 ≤ Real.log (L : ℝ))
    (hC : 0 < C) (hV : 1 ≤ V)
    (hlogC : Real.log (C : ℝ) ≤
      cC * (L : ℝ) ^ 34 * Real.log (L : ℝ))
    (hlogV : Real.log (V : ℝ) ≤ cV * Real.log (L : ℝ))
    (hzero :
      let K := L ^ 32
      let P := L ^ 24
      let Ainit := L ^ 2
      let spend := L ^ 33
      let m := dyadicStageCount (K ^ (r + 1) * P)
      ∀ j, j < m → ∀ h < scaledDyadicStageA Ainit (j + 1),
        ∀ v < stageSpendBudget m spend (j + 1),
        ∀ q < stageUnitBudget m (j + 1),
        ∀ u : Fin r → ℕ,
        (∀ i, u i < stageSpendBudget m spend (j + 1)) →
        pochhammerWeightedApproximationBound (K ^ (r + 1)) P
            (scaledDyadicStageA Ainit j) spend 1 v q (∑ i, u i)
            (C : ℝ) (V : ℝ) ((K : ℝ) * ∑ i, ‖ell i‖)
            (4 * (scaledDyadicStageA Ainit (j + 1) : ℝ))
            (scaledDyadicStageA Ainit (j + 1) : ℝ) 0 <
          Real.exp (-(
            (d : ℝ) * Real.log (K ^ (r + 1) + 1 : ℕ) +
            (d : ℝ) * Real.log
              (P * C * (v.factorial * (h + 1 + P) ^ P) *
                V ^ (q + ∑ i, u i) : ℕ) +
            (h : ℝ) * ((K : ℝ) * Halpha))) / 2) :
    let K := L ^ 32
    let P := L ^ 24
    let Ainit := L ^ 2
    let spend := L ^ 33
    let m := dyadicStageCount (K ^ (r + 1) * P)
    let cFac : ℝ := 314 * (314 + 34)
    let cE : ℝ := 314 * 9
    let cLog : ℝ := 312 + cC + cE * cV + cFac + 321
    let cInner : ℝ := 24 + cC + cFac + 319 + cE * cV
    let cTotal : ℝ := cLog + 2320 + 8 * cInner + 2 * Halpha +
      2 * ∑ i, ‖ell i‖
    let cCore : ℝ := 312 + cC + cE * cV + 315 * (315 + 34) +
      318 + 2 * (∑ i, ‖ell i‖) + cV + 4
    let cPerturb : ℝ := 3956 + cCore
    let Xmax : ℝ := 2 * cTotal *
      ((L : ℝ) ^ 346 * Real.log (L : ℝ) + (L : ℝ) ^ 347)
    let Qperturb : ℝ := cPerturb * (L : ℝ) ^ 694 * Real.log (L : ℝ)
    lambdaNorm ≤ Real.exp (-(Xmax + Qperturb + Real.log 2)) →
    ∀ j, j < m → ∀ h < scaledDyadicStageA Ainit (j + 1),
      ∀ v < stageSpendBudget m spend (j + 1),
      ∀ q < stageUnitBudget m (j + 1),
      ∀ u : Fin r → ℕ,
      (∀ i, u i < stageSpendBudget m spend (j + 1)) →
      pochhammerWeightedApproximationBound (K ^ (r + 1)) P
          (scaledDyadicStageA Ainit j) spend 1 v q (∑ i, u i)
          (C : ℝ) (V : ℝ) ((K : ℝ) * ∑ i, ‖ell i‖)
          (4 * (scaledDyadicStageA Ainit (j + 1) : ℝ))
          (scaledDyadicStageA Ainit (j + 1) : ℝ) lambdaNorm <
        Real.exp (-(
          (d : ℝ) * Real.log (K ^ (r + 1) + 1 : ℕ) +
          (d : ℝ) * Real.log
            (P * C * (v.factorial * (h + 1 + P) ^ P) *
              V ^ (q + ∑ i, u i) : ℕ) +
          (h : ℝ) * ((K : ℝ) * Halpha))) := by
  dsimp only
  let K := L ^ 32
  let P := L ^ 24
  let Ainit := L ^ 2
  let spend := L ^ 33
  let m := dyadicStageCount (K ^ (r + 1) * P)
  let cFac : ℝ := 314 * (314 + 34)
  let cE : ℝ := 314 * 9
  let cLog : ℝ := 312 + cC + cE * cV + cFac + 321
  let cInner : ℝ := 24 + cC + cFac + 319 + cE * cV
  let cTotal : ℝ := cLog + 2320 + 8 * cInner + 2 * Halpha +
    2 * ∑ i, ‖ell i‖
  let cCore : ℝ := 312 + cC + cE * cV + 315 * (315 + 34) +
    318 + 2 * (∑ i, ‖ell i‖) + cV + 4
  let cPerturb : ℝ := 3956 + cCore
  let Xmax : ℝ := 2 * cTotal *
    ((L : ℝ) ^ 346 * Real.log (L : ℝ) + (L : ℝ) ^ 347)
  let Qperturb : ℝ := cPerturb * (L : ℝ) ^ 694 * Real.log (L : ℝ)
  intro hlambdaSmall j hj h hh v hv q hq u hu
  let A := scaledDyadicStageA Ainit j
  let W := stageSpendBudget m spend (j + 1)
  let T := stageUnitBudget m (j + 1)
  let S := W
  let E := T + r * S
  let U : ℝ := (K : ℝ) * ∑ i, ‖ell i‖
  let R : ℝ := 4 * (scaledDyadicStageA Ainit (j + 1) : ℝ)
  let Z : ℝ := (scaledDyadicStageA Ainit (j + 1) : ℝ)
  let X : ℝ := (d : ℝ) * Real.log (K ^ (r + 1) + 1 : ℕ) +
    (d : ℝ) * Real.log
      (P * C * (v.factorial * (h + 1 + P) ^ P) *
        V ^ (q + ∑ i, u i) : ℕ) +
    (h : ℝ) * ((K : ℝ) * Halpha)
  let Xworst : ℝ := (d : ℝ) * Real.log (K ^ (r + 1) + 1 : ℕ) +
    (d : ℝ) * Real.log
      (P * C * W.factorial * (2 * A + P) ^ P * V ^ E : ℕ) +
    (2 * A : ℕ) * ((K : ℝ) * Halpha)
  have hA : 0 < A := scaledDyadicStageA_pos (by dsimp [Ainit]; positivity) j
  have hAstep : scaledDyadicStageA Ainit (j + 1) = 2 * A := by
    dsimp [A, scaledDyadicStageA]
    rw [pow_succ]
    ring
  have hzero' : pochhammerWeightedApproximationBound (K ^ (r + 1)) P
        A spend 1 v q (∑ i, u i) (C : ℝ) (V : ℝ) U R Z 0 <
      Real.exp (-X) / 2 := by
    simpa [K, P, Ainit, spend, m, A, W, T, S, U, R, Z, X, hAstep] using
      hzero j hj h hh v hv q hq u hu
  have hq' : q < T := by
    simpa [T, m, K, P] using hq
  have hu' : ∀ i, u i < S := by
    simpa [S, W, m, spend, K, P] using hu
  have husum : ∑ i, u i ≤ r * S := by
    calc
      ∑ i, u i ≤ ∑ _i : Fin r, S := by
        gcongr with i
        exact (hu' i).le
      _ = r * S := by simp
  have hexp : q + ∑ i, u i ≤ E := by
    dsimp [E]
    omega
  have hXworst : X ≤ Xworst := by
    dsimp [X, Xworst, E]
    simpa using pochhammer_liouville_exponent_le_worst_case
      (iota := Fin r) (K ^ (r + 1)) P A W T S C V h v q u
      ((K : ℝ) * Halpha) d (by dsimp [P]; positivity) hA hC hV
      (by positivity) (by positivity) (hAstep ▸ hh) hv hq' hu'
  have hVpos : 0 < V := lt_of_lt_of_le zero_lt_one hV
  have hstage := structured_stage_log_growth_le_fixed_radius
    ell Halpha cC cV hr hd hHalpha hcV (by omega)
    (by norm_num : 2 ≤ 4) hL hlogL hC hVpos hj hlogC hlogV
  have hstage' :
      Real.log
          ((((K ^ (r + 1)) * P : ℕ) : ℝ) *
            ((C : ℝ) * (V : ℝ) ^ E * (W.factorial : ℝ) *
              (4 * (2 * A : ℕ) + 1 + P) ^ P *
              Real.exp (U * (4 * (2 * A : ℕ))))) + Xworst ≤
        (A : ℝ) *
          (cTotal * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
            cTotal * (L : ℝ) ^ 33) := by
    have hraw :
        Real.log
            ((((K ^ (r + 1)) * P : ℕ) : ℝ) *
              ((C : ℝ) * (V : ℝ) ^ E * (W.factorial : ℝ) *
                (4 * (2 * A : ℕ) + 1 + P) ^ P *
                Real.exp (U * (4 * (2 * A : ℕ))))) + Xworst ≤
          (A : ℝ) *
            ((cLog + 2320 + 8 * cInner + 2 * Halpha) *
                ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
              2 * (4 : ℝ) * (∑ i, ‖ell i‖) * (L : ℝ) ^ 32) := by
      simpa [K, P, Ainit, spend, m, A, W, T, S, E, U, Xworst,
        cFac, cE, cLog, cInner] using hstage
    apply hraw.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hlog0 : 0 ≤ Real.log (L : ℝ) := (zero_le_one.trans hlogL)
    have hLone : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
    have hL32le33 : (L : ℝ) ^ 32 ≤ (L : ℝ) ^ 33 := by
      exact pow_le_pow_right₀ hLone (by omega)
    have hL32quad : 4 * (L : ℝ) ^ 32 ≤ (L : ℝ) ^ 33 := by
      have hLR : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
      rw [show (L : ℝ) ^ 33 = (L : ℝ) ^ 32 * L by ring]
      nlinarith [mul_nonneg (sub_nonneg.mpr hLR) (pow_nonneg (by positivity) 32)]
    have hcC0 : 0 ≤ cC := coefficient_nonneg_of_log_bound hC (by omega)
      (lt_of_lt_of_le zero_lt_one hlogL) hlogC
    have hbase : 0 ≤ cLog + 2320 + 8 * cInner + 2 * Halpha := by
      dsimp [cLog, cInner, cFac, cE]
      positivity
    have hell : 0 ≤ ∑ i, ‖ell i‖ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    have hEllRaw : 2 * (4 : ℝ) * (∑ i, ‖ell i‖) * (L : ℝ) ^ 32 ≤
        2 * (∑ i, ‖ell i‖) * (L : ℝ) ^ 33 := by
      nlinarith [mul_le_mul_of_nonneg_left hL32quad hell]
    dsimp [cTotal]
    calc
      (cLog + 2320 + 8 * cInner + 2 * Halpha) *
              ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
            2 * (4 : ℝ) * (∑ i, ‖ell i‖) * (L : ℝ) ^ 32 ≤
          (cLog + 2320 + 8 * cInner + 2 * Halpha) *
              ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
            2 * (∑ i, ‖ell i‖) * (L : ℝ) ^ 33 :=
        add_le_add le_rfl hEllRaw
      _ ≤ (cLog + 2320 + 8 * cInner + 2 * Halpha +
              2 * ∑ i, ‖ell i‖) *
              ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
            (cLog + 2320 + 8 * cInner + 2 * Halpha +
              2 * ∑ i, ‖ell i‖) * (L : ℝ) ^ 33 := by
        have hExtraLog : 0 ≤ 2 * (∑ i, ‖ell i‖) *
            ((L : ℝ) ^ 32 * Real.log (L : ℝ)) := by positivity
        have hExtraBase : 0 ≤ (cLog + 2320 + 8 * cInner + 2 * Halpha) *
            (L : ℝ) ^ 33 := mul_nonneg hbase (by positivity)
        nlinarith
  have hlogBoundary : 0 ≤ Real.log
      ((((K ^ (r + 1)) * P : ℕ) : ℝ) *
        ((C : ℝ) * (V : ℝ) ^ E * (W.factorial : ℝ) *
          (4 * (2 * A : ℕ) + 1 + P) ^ P *
          Real.exp (U * (4 * (2 * A : ℕ))))) := by
    apply log_boundary_nonneg (K ^ (r + 1)) P W E C V
    · positivity
    · dsimp [P]
      positivity
    · exact hC
    · exact hV
    · positivity
    · dsimp [U, K]
      positivity
  have hXstage : Xworst ≤ (A : ℝ) *
      (cTotal * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
        cTotal * (L : ℝ) ^ 33) := by linarith
  have hAupper0 := scaledDyadicStageA_parameter_upper (by omega) hj
  have hLone : 1 ≤ L := by omega
  have hNpow : K ^ (r + 1) * P ≤ L ^ 312 := by
    have he : 32 * (r + 1) + 24 ≤ 312 := by omega
    have heq : K ^ (r + 1) * P = L ^ (32 * (r + 1) + 24) := by
      dsimp [K, P]
      rw [← pow_mul, ← pow_add]
    rw [heq]
    exact Nat.pow_le_pow_right hLone he
  have hApoly : A ≤ 2 * L ^ 314 := by
    have hAstepLe : A ≤ scaledDyadicStageA (L ^ 2) (j + 1) := by
      dsimp [A, Ainit, scaledDyadicStageA]
      exact Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by omega) (Nat.le_succ j))
    calc
      A ≤ scaledDyadicStageA (L ^ 2) (j + 1) := hAstepLe
      _ ≤ 2 * L ^ 2 * (K ^ (r + 1) * P) := by
        simpa [K, P] using hAupper0
      _ ≤ 2 * L ^ 2 * L ^ 312 := by gcongr
      _ = 2 * L ^ 314 := by ring
  have hcC : 0 ≤ cC := coefficient_nonneg_of_log_bound hC (by omega)
    (lt_of_lt_of_le zero_lt_one hlogL) hlogC
  have hcTotal : 0 ≤ cTotal := by
    dsimp [cTotal, cLog, cInner, cFac, cE]
    positivity
  have hAcast : (A : ℝ) ≤ 2 * (L : ℝ) ^ 314 := by exact_mod_cast hApoly
  have hXmax : X ≤ Xmax := hXworst.trans (hXstage.trans (by
    dsimp [Xmax]
    calc
      (A : ℝ) *
          (cTotal * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
            cTotal * (L : ℝ) ^ 33) ≤
        (2 * (L : ℝ) ^ 314) *
          (cTotal * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
            cTotal * (L : ℝ) ^ 33) := by
          apply mul_le_mul_of_nonneg_right hAcast
          positivity
      _ = 2 * cTotal *
          ((L : ℝ) ^ 346 * Real.log (L : ℝ) + (L : ℝ) ^ 347) := by ring))
  have hcoeffMono := pochhammerWeightedPerturbationCoefficient_mono
    (K ^ (r + 1)) P A spend v q (∑ i, u i) W E
    (C := (C : ℝ)) (V := (V : ℝ)) (U := U) (R := R) (Z := Z)
    hv.le hexp (by positivity) (by exact_mod_cast hV)
    (by dsimp [Z]; positivity) (by
      dsimp [R]
      rw [hAstep]
      push_cast
      rw [show 4 * (2 * (A : ℝ)) - (A : ℝ) = 7 * (A : ℝ) by ring]
      positivity)
  have hcoeffNonneg := pochhammerWeightedPerturbationCoefficient_nonneg
    (K ^ (r + 1)) P A spend v q (∑ i, u i)
    (C := (C : ℝ)) (V := (V : ℝ)) (U := U) (R := R) (Z := Z)
    (by positivity) (by positivity) (by dsimp [Z]; positivity) (by
      dsimp [R]
      rw [hAstep]
      push_cast
      rw [show 4 * (2 * (A : ℝ)) - (A : ℝ) = 7 * (A : ℝ) by ring]
      positivity)
  have hperturbLog := structured_stage_perturbation_log_le_fixed_radius
    ell cC cV hr hcV (by omega) (by norm_num : 2 ≤ 4) hL
      hlogL hC hVpos hj hlogC hlogV
  have hperturbLog' : Real.log
      (pochhammerWeightedPerturbationCoefficient
        (K ^ (r + 1)) P A spend W E 0 (C : ℝ) (V : ℝ) U R Z) ≤
      Qperturb := by
    simpa [K, P, Ainit, spend, m, A, W, T, S, E, U, R, Z,
      cE, cCore, cPerturb, Qperturb, hAstep] using hperturbLog
  have hcoeffWorstPos : 0 < pochhammerWeightedPerturbationCoefficient
      (K ^ (r + 1)) P A spend W E 0 (C : ℝ) (V : ℝ) U R Z := by
    have hcommon : 0 < pochhammerWeightedPerturbationCommon
        (K ^ (r + 1)) P A spend W E 0 (C : ℝ) (V : ℝ) U := by
      unfold pochhammerWeightedPerturbationCommon
        pochhammerWeightedPerturbationCore hermiteInterpolationBound
      positivity
    have hRA : 0 < R - (A : ℝ) := by
      dsimp [R]
      rw [hAstep]
      push_cast
      rw [show 4 * (2 * (A : ℝ)) - (A : ℝ) = 7 * (A : ℝ) by ring]
      positivity
    unfold pochhammerWeightedPerturbationCoefficient
    change 0 < (Z + A) ^ (spend * A) *
        (pochhammerWeightedPerturbationCommon
          (K ^ (r + 1)) P A spend W E 0 (C : ℝ) (V : ℝ) U *
          max 1 (R ^ (A * spend)) / (R - A) ^ (spend * A)) +
      pochhammerWeightedPerturbationCommon
          (K ^ (r + 1)) P A spend W E 0 (C : ℝ) (V : ℝ) U *
        max 1 (Z ^ (A * spend))
    apply add_pos_of_nonneg_of_pos
    · positivity
    · exact mul_pos hcommon (zero_lt_one.trans_le (le_max_left _ _))
  have hperturbHalf := perturbation_product_le_half_target
    hlambda hcoeffNonneg hcoeffWorstPos hcoeffMono hperturbLog'
      hXmax hlambdaSmall
  change pochhammerWeightedApproximationBound (K ^ (r + 1)) P
      A spend 1 v q (∑ i, u i) (C : ℝ) (V : ℝ) U R Z lambdaNorm <
    Real.exp (-X)
  exact approximation_lt_of_half_bounds
    (K ^ (r + 1)) P A spend v q (∑ i, u i)
      (C : ℝ) (V : ℝ) U R Z lambdaNorm (Real.exp (-X))
      hzero' hperturbHalf


theorem structured_box_boundary_half
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (M : ℝ)
    {r B L : ℕ} (alpha : Fin (r + 1) → F)
    (ell : Fin (r + 1) → ℂ)
    (hr : r ≤ 8) (hd : Module.finrank ℚ F ≤ 8)
    (hL : 4 ≤ L) (hlogL : 1 ≤ Real.log (L : ℝ)) (hM : 1 ≤ M)
    (hbig : 314 ^ 9 * 314 * 16 < L ^ 3)
    (hdom :
      let Halpha : ℝ := ∑ i, Height.logHeight₁ (alpha i)
      let cH : ℝ := 8 * (314 * (314 + 34) + 26) + Halpha +
        (314 * 9) * 8 * (Real.log ((2 * B + 1 : ℕ) : ℝ) + 32)
      let cC : ℝ := 2 + 312 + 8 + Real.log M + 81 * Halpha + cH
      let cV : ℝ := Real.log (boxAnalyticSlope B ell : ℝ) + 32
      let cFac : ℝ := 314 * (314 + 34)
      let cE : ℝ := 314 * 9
      let cLog : ℝ := 312 + cC + cE * cV + cFac + 321
      let cInner : ℝ := 24 + cC + cFac + 319 + cE * cV
      let cBase : ℝ := cLog + 2320 + 8 * cInner + 2 * Halpha
      cBase * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
          2 * (4 : ℝ) * (∑ i, ‖ell i‖) * (L : ℝ) ^ 32 + Real.log 2 <
        (L : ℝ) ^ 33 * Real.log ((2 * (4 : ℝ) - 1) / 3)) :
    let K := L ^ 32
    let P := L ^ 24
    let Ainit := L ^ 2
    let spend := L ^ 33
    let m := dyadicStageCount (K ^ (r + 1) * P)
    ∀ j, j < m → ∀ h < scaledDyadicStageA Ainit (j + 1),
      ∀ v < stageSpendBudget m spend (j + 1),
      ∀ q < stageUnitBudget m (j + 1),
      ∀ u : Fin r → ℕ,
      (∀ i, u i < stageSpendBudget m spend (j + 1)) →
      pochhammerWeightedApproximationBound (K ^ (r + 1)) P
          (scaledDyadicStageA Ainit j) spend 1 v q (∑ i, u i)
          (boxPochhammerStructuredCoefficientMajorant basis M r B K P
            Ainit (m * spend + 1) (m + 1) (m * spend + 1) alpha : ℝ)
          (boxAnalyticCoordinateBound B K ell : ℝ)
          ((K : ℝ) * ∑ i, ‖ell i‖)
          (4 * (scaledDyadicStageA Ainit (j + 1) : ℝ))
          (scaledDyadicStageA Ainit (j + 1) : ℝ) 0 <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ (r + 1) + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (P * boxPochhammerStructuredCoefficientMajorant
                  basis M r B K P Ainit
                    (m * spend + 1) (m + 1) (m * spend + 1) alpha *
                (v.factorial * (h + 1 + P) ^ P) *
                (boxAnalyticCoordinateBound B K ell) ^
                  (q + ∑ i, u i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i)))) / 2 := by
  dsimp only
  let K := L ^ 32
  let P := L ^ 24
  let Ainit := L ^ 2
  let spend := L ^ 33
  let m := dyadicStageCount (K ^ (r + 1) * P)
  let Wsrc := m * spend + 1
  let Tsrc := m + 1
  let Ssrc := Wsrc
  let C := boxPochhammerStructuredCoefficientMajorant basis M r B K P
    Ainit Wsrc Tsrc Ssrc alpha
  let V := boxAnalyticCoordinateBound B K ell
  let Halpha : ℝ := ∑ i, Height.logHeight₁ (alpha i)
  let cMoment : ℝ := Real.log ((2 * B + 1 : ℕ) : ℝ) + 32
  let cH : ℝ := 8 * (314 * (314 + 34) + 26) + Halpha +
    (314 * 9) * 8 * cMoment
  let cC : ℝ := 2 + 312 + 8 + Real.log M + 81 * Halpha + cH
  let cV : ℝ := Real.log (boxAnalyticSlope B ell : ℝ) + 32
  let cFac : ℝ := 314 * (314 + 34)
  let cE : ℝ := 314 * 9
  let cLog : ℝ := 312 + cC + cE * cV + cFac + 321
  let cInner : ℝ := 24 + cC + cFac + 319 + cE * cV
  let cBase : ℝ := cLog + 2320 + 8 * cInner + 2 * Halpha
  have hdegCard : Fintype.card ι ≤ 8 := by
    rw [← Module.finrank_eq_card_basis basis]
    exact hd
  have hhalf := box_parameter_half_cardinality_initial_sq
    (r := r) (d := Fintype.card ι) hr hdegCard (by omega) hbig
  have hcM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hlogM : Real.log M ≤ Real.log M * Real.log (L : ℝ) :=
    le_mul_of_one_le_right hcM hlogL
  have hMomentPoly : boxMomentCoordinateBound B (L ^ 32) ≤
      (2 * B + 1) * L ^ 32 := boxMomentCoordinateBound_le_poly
  have hMomentPos : 0 < boxMomentCoordinateBound B (L ^ 32) := by
    exact lt_of_lt_of_le (by positivity : 0 < L ^ 32) (le_max_left _ _)
  have hlogMoment :
      Real.log (boxMomentCoordinateBound B (L ^ 32) : ℝ) ≤
        cMoment * Real.log (L : ℝ) := by
    have h := log_nat_le_log_coefficient_add hMomentPos
      (by omega : 0 < 2 * B + 1) (by omega : 0 < L) hlogL hMomentPoly
    simpa [cMoment] using h
  have hlogC : Real.log (C : ℝ) ≤
      cC * (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
    dsimp [C, cC, cH, cMoment, Halpha, K, P, Ainit, Wsrc, Tsrc, Ssrc,
      m, spend]
    exact structured_initial_coefficient_log_le basis M (Real.log M)
      (Real.log ((2 * B + 1 : ℕ) : ℝ) + 32) alpha hr hd (by omega) hlogL
      hM hcM hlogM (by positivity) (by simpa [cMoment] using hlogMoment) hhalf
  have hK : 0 < K := by dsimp [K]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hAinit : 0 < Ainit := by dsimp [Ainit]; positivity
  have hspend : 0 < spend := by dsimp [spend]; positivity
  have hC : 0 < C := by
    exact lt_of_lt_of_le zero_lt_one
      (one_le_boxPochhammerStructuredCoefficientMajorant
        basis M r B K P Ainit Wsrc Tsrc Ssrc alpha)
  have hV : 1 ≤ V := one_le_boxAnalyticCoordinateBound ell
  have hVpoly : V ≤ boxAnalyticSlope B ell * L ^ 32 := by
    simpa [V, K] using boxAnalyticCoordinateBound_le_slope ell hK
  have hlogV : Real.log (V : ℝ) ≤ cV * Real.log (L : ℝ) := by
    have h := log_nat_le_log_coefficient_add
      (n := V) (c := boxAnalyticSlope B ell) (e := 32) (L := L)
      (lt_of_lt_of_le zero_lt_one hV) (boxAnalyticSlope_pos B ell)
      (by omega) hlogL hVpoly
    simpa [cV] using h
  have hHalpha : 0 ≤ Halpha := by dsimp [Halpha]; positivity
  have hdom' :
      cBase * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
          2 * (4 : ℝ) * (∑ i, ‖ell i‖) * (L : ℝ) ^ 32 + Real.log 2 <
        (L : ℝ) ^ 33 * Real.log ((2 * (4 : ℝ) - 1) / 3) := by
    simpa [Halpha, cMoment, cH, cC, cV, cFac, cE, cLog, cInner, cBase] using hdom
  intro j hj h hh v hv q hq u hu
  let A := scaledDyadicStageA Ainit j
  let W := stageSpendBudget m spend (j + 1)
  let T := stageUnitBudget m (j + 1)
  let S := W
  have hA : 0 < A := scaledDyadicStageA_pos hAinit j
  have hAstep : scaledDyadicStageA Ainit (j + 1) = 2 * A := by
    dsimp [A, scaledDyadicStageA]
    rw [pow_succ]
    ring
  have hstage := structured_stage_log_growth_le_fixed_radius
    ell Halpha cC cV hr hd hHalpha
    (by dsimp [cV]; positivity) (by omega) (by norm_num : 2 ≤ 4)
    hL hlogL hC
    (lt_of_lt_of_le zero_lt_one hV) hj hlogC hlogV
  have hstage' :
      Real.log
          ((((K ^ (r + 1)) * P : ℕ) : ℝ) *
            ((C : ℝ) * (V : ℝ) ^ (T + r * S) * (W.factorial : ℝ) *
              (4 * (2 * A : ℕ) + 1 + P) ^ P *
              Real.exp (((K : ℝ) * ∑ i, ‖ell i‖) *
                (4 * (2 * A : ℕ))))) +
        ((Module.finrank ℚ F : ℝ) *
            Real.log (K ^ (r + 1) + 1 : ℕ) +
          (Module.finrank ℚ F : ℝ) *
            Real.log
              (P * C * W.factorial * (2 * A + P) ^ P * V ^ (T + r * S) : ℕ) +
          (2 * A : ℕ) * ((K : ℝ) * Halpha)) ≤
        (A : ℝ) *
          (cBase * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
            2 * (4 : ℝ) * (∑ i, ‖ell i‖) * (L : ℝ) ^ 32) := by
    simpa [K, P, Ainit, spend, m, C, V, Halpha, cMoment, cC, cV, cFac, cE,
      cLog, cInner, cBase, A, W, T, S, Wsrc, Tsrc, Ssrc] using hstage
  have hlogmaster :
      Real.log
          ((((K ^ (r + 1)) * P : ℕ) : ℝ) *
            ((C : ℝ) * (V : ℝ) ^ (T + r * S) * (W.factorial : ℝ) *
              (4 * (2 * A : ℕ) + 1 + P) ^ P *
              Real.exp (((K : ℝ) * ∑ i, ‖ell i‖) *
                (4 * (2 * A : ℕ))))) +
        ((Module.finrank ℚ F : ℝ) *
            Real.log (K ^ (r + 1) + 1 : ℕ) +
          (Module.finrank ℚ F : ℝ) *
            Real.log
              (P * C * W.factorial * (2 * A + P) ^ P * V ^ (T + r * S) : ℕ) +
          (2 * A : ℕ) * ((K : ℝ) * Halpha)) + Real.log 2 <
        ((spend * A : ℕ) : ℝ) *
          Real.log ((2 * (4 : ℝ) - 1) / 3) := by
    calc
      _ ≤ (A : ℝ) *
              (cBase * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
                2 * (4 : ℝ) * (∑ i, ‖ell i‖) * (L : ℝ) ^ 32) + Real.log 2 :=
        add_le_add hstage' le_rfl
      _ ≤ (A : ℝ) *
          (cBase * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
            2 * (4 : ℝ) * (∑ i, ‖ell i‖) * (L : ℝ) ^ 32 + Real.log 2) := by
        have hAone : (1 : ℝ) ≤ A := by exact_mod_cast (show 1 ≤ A by omega)
        have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        nlinarith [mul_nonneg (sub_nonneg.mpr hAone) hlogTwo]
      _ < (A : ℝ) *
          ((L : ℝ) ^ 33 * Real.log ((2 * (4 : ℝ) - 1) / 3)) := by
        exact mul_lt_mul_of_pos_left hdom' (by positivity)
      _ = ((spend * A : ℕ) : ℝ) *
          Real.log ((2 * (4 : ℝ) - 1) / 3) := by
        dsimp [spend]
        push_cast
        ring
  have hmaster := boundary_master_half_of_log_inequality
    (K ^ (r + 1)) P A spend W (T + r * S) C V
    ((K : ℝ) * ∑ i, ‖ell i‖) 4
    (4 * (2 * A : ℕ))
    ((Module.finrank ℚ F : ℝ) * Real.log (K ^ (r + 1) + 1 : ℕ) +
      (Module.finrank ℚ F : ℝ) *
        Real.log (P * C * W.factorial * (2 * A + P) ^ P *
          V ^ (T + r * S) : ℕ) +
      (2 * A : ℕ) * ((K : ℝ) * Halpha))
    (by positivity) hP hA hC (lt_of_lt_of_le zero_lt_one hV)
    (by norm_num) (by positivity) hlogmaster
  have hworst := pochhammer_boundary_half_lt_of_worst_case
    (iota := Fin r) (K ^ (r + 1)) P A spend W T S C V
    ((K : ℝ) * ∑ i, ‖ell i‖) 4 ((K : ℝ) * Halpha)
    (Module.finrank ℚ F : ℝ) hP hA (by norm_num) hC hV
    (by positivity) (by positivity) (by simpa using hmaster)
  have hbound := hworst h (hAstep ▸ hh) v hv q hq u hu
  simpa [K, P, Ainit, spend, m, C, V, Halpha, A, W, T, S,
    Wsrc, Tsrc, Ssrc, hAstep] using hbound





theorem structured_box_boundary
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (M : ℝ)
    {r B L : ℕ} (alpha : Fin (r + 1) → F)
    (ell : Fin (r + 1) → ℂ)
    (hr : r ≤ 8) (hd : Module.finrank ℚ F ≤ 8)
    (hL : 2 ≤ L) (hlogL : 1 ≤ Real.log (L : ℝ)) (hM : 1 ≤ M)
    (hbig : 314 ^ 9 * 314 * 16 < L ^ 3)
    (hdom :
      let Halpha : ℝ := ∑ i, Height.logHeight₁ (alpha i)
      let cH : ℝ := 8 * (314 * (314 + 34) + 26) + Halpha +
        (314 * 9) * 8 * ((2 * B + 1 : ℕ) + 32)
      let cC : ℝ := 2 + 312 + 8 + M + 81 * Halpha + cH
      let cV : ℝ := (boxAnalyticSlope B ell + 32 : ℕ)
      let cFac : ℝ := 314 * (314 + 34)
      let cE : ℝ := 314 * 9
      let cLog : ℝ := 312 + cC + cE * cV + cFac + 321
      let cInner : ℝ := 24 + cC + cFac + 319 + cE * cV
      let cTotal : ℝ := cLog + 2320 + 8 * cInner + 2 * Halpha +
        2 * ∑ i, ‖ell i‖
      cTotal * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
          cTotal * (L : ℝ) ^ 33 <
        (L : ℝ) ^ 33 * Real.log ((2 * (L : ℝ) - 1) / 3)) :
    let K := L ^ 32
    let P := L ^ 24
    let Ainit := L ^ 2
    let spend := L ^ 33
    let m := dyadicStageCount (K ^ (r + 1) * P)
    ∀ j, j < m → ∀ h < scaledDyadicStageA Ainit (j + 1),
      ∀ v < stageSpendBudget m spend (j + 1),
      ∀ q < stageUnitBudget m (j + 1),
      ∀ u : Fin r → ℕ,
      (∀ i, u i < stageSpendBudget m spend (j + 1)) →
      pochhammerWeightedApproximationBound (K ^ (r + 1)) P
          (scaledDyadicStageA Ainit j) spend 1 v q (∑ i, u i)
          (boxPochhammerStructuredCoefficientMajorant basis M r B K P
            Ainit (m * spend + 1) (m + 1) (m * spend + 1) alpha : ℝ)
          (boxAnalyticCoordinateBound B K ell : ℝ)
          ((K : ℝ) * ∑ i, ‖ell i‖)
          ((L : ℝ) * (scaledDyadicStageA Ainit (j + 1) : ℝ))
          (scaledDyadicStageA Ainit (j + 1) : ℝ) 0 <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ (r + 1) + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (P * boxPochhammerStructuredCoefficientMajorant
                  basis M r B K P Ainit
                    (m * spend + 1) (m + 1) (m * spend + 1) alpha *
                (v.factorial * (h + 1 + P) ^ P) *
                (boxAnalyticCoordinateBound B K ell) ^
                  (q + ∑ i, u i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i)))) := by
  dsimp only
  let K := L ^ 32
  let P := L ^ 24
  let Ainit := L ^ 2
  let spend := L ^ 33
  let m := dyadicStageCount (K ^ (r + 1) * P)
  let Wsrc := m * spend + 1
  let Tsrc := m + 1
  let Ssrc := Wsrc
  let C := boxPochhammerStructuredCoefficientMajorant basis M r B K P
    Ainit Wsrc Tsrc Ssrc alpha
  let V := boxAnalyticCoordinateBound B K ell
  let Halpha : ℝ := ∑ i, Height.logHeight₁ (alpha i)
  let cMoment : ℝ := (((2 * B + 1 : ℕ) + 32 : ℕ) : ℝ)
  let cH : ℝ := 8 * (314 * (314 + 34) + 26) + Halpha +
    (314 * 9) * 8 * cMoment
  let cC : ℝ := 2 + 312 + 8 + M + 81 * Halpha + cH
  let cV : ℝ := (boxAnalyticSlope B ell + 32 : ℕ)
  let cFac : ℝ := 314 * (314 + 34)
  let cE : ℝ := 314 * 9
  let cLog : ℝ := 312 + cC + cE * cV + cFac + 321
  let cInner : ℝ := 24 + cC + cFac + 319 + cE * cV
  let cTotal : ℝ := cLog + 2320 + 8 * cInner + 2 * Halpha +
    2 * ∑ i, ‖ell i‖
  have hdegCard : Fintype.card ι ≤ 8 := by
    rw [← Module.finrank_eq_card_basis basis]
    exact hd
  have hhalf := box_parameter_half_cardinality_initial_sq
    (r := r) (d := Fintype.card ι) hr hdegCard hL hbig
  have hcM : 0 ≤ M := zero_le_one.trans hM
  have hlogM : Real.log M ≤ M * Real.log (L : ℝ) := by
    calc
      Real.log M ≤ M - 1 :=
        Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hM)
      _ ≤ M := by linarith
      _ ≤ M * Real.log (L : ℝ) := le_mul_of_one_le_right hcM hlogL
  have hMomentPoly : boxMomentCoordinateBound B (L ^ 32) ≤
      (2 * B + 1) * L ^ 32 := boxMomentCoordinateBound_le_poly
  have hMomentPos : 0 < boxMomentCoordinateBound B (L ^ 32) := by
    exact lt_of_lt_of_le (by positivity : 0 < L ^ 32) (le_max_left _ _)
  have hlogMoment :
      Real.log (boxMomentCoordinateBound B (L ^ 32) : ℝ) ≤
        cMoment * Real.log (L : ℝ) := by
    have h := log_nat_le_poly hMomentPos (by omega : 0 < 2 * B + 1)
      (by omega : 0 < L) hlogL hMomentPoly
    simpa [cMoment] using h
  have hlogC : Real.log (C : ℝ) ≤
      cC * (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
    dsimp [C, cC, cH, cMoment, Halpha, K, P, Ainit, Wsrc, Tsrc, Ssrc,
      m, spend]
    exact structured_initial_coefficient_log_le basis M M
      ((((2 * B + 1 : ℕ) + 32 : ℕ) : ℝ)) alpha hr hd hL hlogL
      hM hcM hlogM (by positivity) (by simpa [cMoment] using hlogMoment) hhalf
  have hK : 0 < K := by dsimp [K]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hAinit : 0 < Ainit := by dsimp [Ainit]; positivity
  have hspend : 0 < spend := by dsimp [spend]; positivity
  have hC : 0 < C := by
    exact lt_of_lt_of_le zero_lt_one
      (one_le_boxPochhammerStructuredCoefficientMajorant
        basis M r B K P Ainit Wsrc Tsrc Ssrc alpha)
  have hV : 1 ≤ V := one_le_boxAnalyticCoordinateBound ell
  have hVpoly : V ≤ boxAnalyticSlope B ell * L ^ 32 := by
    simpa [V, K] using boxAnalyticCoordinateBound_le_slope ell hK
  have hlogV : Real.log (V : ℝ) ≤ cV * Real.log (L : ℝ) := by
    have h := log_nat_le_poly
      (n := V) (c := boxAnalyticSlope B ell) (e := 32) (L := L)
      (lt_of_lt_of_le zero_lt_one hV) (boxAnalyticSlope_pos B ell)
      (by omega) hlogL hVpoly
    simpa [cV] using h
  have hHalpha : 0 ≤ Halpha := by dsimp [Halpha]; positivity
  have hdom' :
      cTotal * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
          cTotal * (L : ℝ) ^ 33 <
        (L : ℝ) ^ 33 * Real.log ((2 * (L : ℝ) - 1) / 3) := by
    simpa [Halpha, cMoment, cH, cC, cV, cFac, cE, cLog, cInner, cTotal] using hdom
  intro j hj h hh v hv q hq u hu
  let A := scaledDyadicStageA Ainit j
  let W := stageSpendBudget m spend (j + 1)
  let T := stageUnitBudget m (j + 1)
  let S := W
  have hA : 0 < A := scaledDyadicStageA_pos hAinit j
  have hAstep : scaledDyadicStageA Ainit (j + 1) = 2 * A := by
    dsimp [A, scaledDyadicStageA]
    rw [pow_succ]
    ring
  have hstage := structured_stage_log_growth_le ell Halpha cC cV hr hd hHalpha
    (by dsimp [cV]; positivity) hL hlogL hC
    (lt_of_lt_of_le zero_lt_one hV) hj hlogC hlogV
  have hstage' :
      Real.log
          ((((K ^ (r + 1)) * P : ℕ) : ℝ) *
            ((C : ℝ) * (V : ℝ) ^ (T + r * S) * (W.factorial : ℝ) *
              ((L : ℝ) * (2 * A : ℕ) + 1 + P) ^ P *
              Real.exp (((K : ℝ) * ∑ i, ‖ell i‖) *
                ((L : ℝ) * (2 * A : ℕ))))) +
        ((Module.finrank ℚ F : ℝ) *
            Real.log (K ^ (r + 1) + 1 : ℕ) +
          (Module.finrank ℚ F : ℝ) *
            Real.log
              (P * C * W.factorial * (2 * A + P) ^ P * V ^ (T + r * S) : ℕ) +
          (2 * A : ℕ) * ((K : ℝ) * Halpha)) ≤
        (A : ℝ) *
          (cTotal * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
            cTotal * (L : ℝ) ^ 33) := by
    simpa [K, P, Ainit, spend, m, C, V, Halpha, cMoment, cC, cV, cFac, cE,
      cLog, cInner, cTotal, A, W, T, S, Wsrc, Tsrc, Ssrc] using hstage
  have hlogmaster :
      Real.log
          ((((K ^ (r + 1)) * P : ℕ) : ℝ) *
            ((C : ℝ) * (V : ℝ) ^ (T + r * S) * (W.factorial : ℝ) *
              ((L : ℝ) * (2 * A : ℕ) + 1 + P) ^ P *
              Real.exp (((K : ℝ) * ∑ i, ‖ell i‖) *
                ((L : ℝ) * (2 * A : ℕ))))) +
        ((Module.finrank ℚ F : ℝ) *
            Real.log (K ^ (r + 1) + 1 : ℕ) +
          (Module.finrank ℚ F : ℝ) *
            Real.log
              (P * C * W.factorial * (2 * A + P) ^ P * V ^ (T + r * S) : ℕ) +
          (2 * A : ℕ) * ((K : ℝ) * Halpha)) <
        ((spend * A : ℕ) : ℝ) *
          Real.log ((2 * (L : ℝ) - 1) / 3) := by
    calc
      _ ≤ (A : ℝ) *
          (cTotal * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
            cTotal * (L : ℝ) ^ 33) := hstage'
      _ < (A : ℝ) *
          ((L : ℝ) ^ 33 * Real.log ((2 * (L : ℝ) - 1) / 3)) := by
        exact mul_lt_mul_of_pos_left hdom' (by positivity)
      _ = ((spend * A : ℕ) : ℝ) *
          Real.log ((2 * (L : ℝ) - 1) / 3) := by
        dsimp [spend]
        push_cast
        ring
  have hmaster := boundary_master_of_log_inequality
    (K ^ (r + 1)) P A spend W (T + r * S) C V
    ((K : ℝ) * ∑ i, ‖ell i‖) (L : ℝ)
    ((L : ℝ) * (2 * A : ℕ))
    ((Module.finrank ℚ F : ℝ) * Real.log (K ^ (r + 1) + 1 : ℕ) +
      (Module.finrank ℚ F : ℝ) *
        Real.log (P * C * W.factorial * (2 * A + P) ^ P *
          V ^ (T + r * S) : ℕ) +
      (2 * A : ℕ) * ((K : ℝ) * Halpha))
    (by positivity) hP hA hC (lt_of_lt_of_le zero_lt_one hV)
    (by exact_mod_cast hL) (by positivity) hlogmaster
  have hworst := pochhammer_boundary_lt_of_worst_case
    (iota := Fin r) (K ^ (r + 1)) P A spend W T S C V
    ((K : ℝ) * ∑ i, ‖ell i‖) (L : ℝ) ((K : ℝ) * Halpha)
    (Module.finrank ℚ F : ℝ) hP hA (by exact_mod_cast hL) hC hV
    (by positivity) (by positivity) (by simpa using hmaster)
  have hbound := hworst h (hAstep ▸ hh) v hv q hq u hu
  simpa [K, P, Ainit, spend, m, C, V, Halpha, A, W, T, S,
    Wsrc, Tsrc, Ssrc, hAstep] using hbound


theorem exists_positive_lower_bound_box_logarithmic_form
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (φ : F →+* ℂ) {r B : ℕ}
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ)
    (b : Fin (r + 1) → ℤ) (M : ℝ)
    (hr : r ≤ 8) (hd : Module.finrank ℚ F ≤ 8) (hM : 1 ≤ M)
    (hMbasis : ∀ i (ψ : F →ₐ[ℚ] ℂ), ‖ψ (basis i)‖ ≤ M)
    (hb : ∀ i, (b i).natAbs ≤ B) (hb0 : b 0 ≠ 0)
    (halpha : ∀ i, alpha i ≠ 0)
    (hinj : ∀ K, 0 < K → Function.Injective
      (fun x : ExponentBox (r + 1) K ↦ boxMonomial alpha x))
    (hexp : ∀ K (x : ExponentBox (r + 1) K),
      Complex.exp (boxLinearForm ell x) = φ (boxMonomial alpha x)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ ‖∑ i, (b i : ℂ) * ell i‖ := by
  let Halpha : ℝ := ∑ i, Height.logHeight₁ (alpha i)
  let cH : ℝ := 8 * (314 * (314 + 34) + 26) + Halpha +
    (314 * 9) * 8 * ((2 * B + 1 : ℕ) + 32)
  let cC : ℝ := 2 + 312 + 8 + M + 81 * Halpha + cH
  let cV : ℝ := (boxAnalyticSlope B ell + 32 : ℕ)
  let cFac : ℝ := 314 * (314 + 34)
  let cE : ℝ := 314 * 9
  let cLog : ℝ := 312 + cC + cE * cV + cFac + 321
  let cInner : ℝ := 24 + cC + cFac + 319 + cE * cV
  let cTotal : ℝ := cLog + 2320 + 8 * cInner + 2 * Halpha +
    2 * ∑ i, ‖ell i‖
  have hcastTop : Filter.Tendsto (fun L : ℕ ↦ (L : ℝ))
      Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have hlogTop : Filter.Tendsto (fun L : ℕ ↦ Real.log (L : ℝ))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hcastTop
  have hdomEv := eventually_boundary_log_dominates cTotal
  have hL2 : ∀ᶠ L : ℕ in Filter.atTop, 2 ≤ L :=
    Filter.eventually_ge_atTop 2
  have hlog1 : ∀ᶠ L : ℕ in Filter.atTop, 1 ≤ Real.log (L : ℝ) :=
    hlogTop.eventually (Filter.eventually_ge_atTop 1)
  have hconst : ∀ᶠ L : ℕ in Filter.atTop,
      314 ^ 9 * 314 * 16 < L :=
    Filter.eventually_gt_atTop (314 ^ 9 * 314 * 16)
  have hall : ∀ᶠ L : ℕ in Filter.atTop,
      2 ≤ L ∧ 1 ≤ Real.log (L : ℝ) ∧
        314 ^ 9 * 314 * 16 < L ∧
        cTotal * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
            cTotal * (L : ℝ) ^ 33 <
          (L : ℝ) ^ 33 * Real.log ((2 * (L : ℝ) - 1) / 3) := by
    filter_upwards [hL2, hlog1, hconst, hdomEv] with L hL hlogL hconstL hdom
    exact ⟨hL, hlogL, hconstL, hdom⟩
  rcases hall.exists with ⟨L, hL, hlogL, hconstL, hdom⟩
  have hLone : 1 ≤ L := by omega
  have hLcube : L ≤ L ^ 3 := by
    simpa using Nat.pow_le_pow_right hLone (show 1 ≤ 3 by omega)
  have hbig : 314 ^ 9 * 314 * 16 < L ^ 3 := hconstL.trans_le hLcube
  let K := L ^ 32
  let P := L ^ 24
  let Ainit := L ^ 2
  let spend := L ^ 33
  let m := dyadicStageCount (K ^ (r + 1) * P)
  have hdegCard : Fintype.card ι ≤ 8 := by
    rw [← Module.finrank_eq_card_basis basis]
    exact hd
  have hbig8 : 314 ^ 9 * 314 * 8 < L ^ 3 := by
    have hconst8 : 314 ^ 9 * 314 * 8 < 314 ^ 9 * 314 * 16 := by
      nlinarith [show 0 < 314 ^ 9 * 314 by positivity]
    exact hconst8.trans hbig
  have hcard := box_parameter_cardinality_initial_sq
    (r := r) (d := Fintype.card ι) hr hdegCard (by omega) hbig8
  have hboundary := structured_box_boundary basis M alpha ell hr hd hL hlogL hM hbig hdom
  apply exists_positive_lower_bound_of_scaled_dyadic_boundary_structured
    basis hbasis φ alpha ell b M (L : ℝ)
      (K := K) (P := P) (Ainit := Ainit) (spend := spend)
  · dsimp [K]
    positivity
  · dsimp [P]
    positivity
  · dsimp [Ainit]
    positivity
  · dsimp [spend]
    positivity
  · linarith
  · exact hMbasis
  · exact_mod_cast hLone
  · simpa [K, P, Ainit, spend, m] using hcard
  · exact hb
  · exact hb0
  · exact halpha
  · exact hinj K (by dsimp [K]; positivity)
  · exact hexp K
  · simpa [K, P, Ainit, spend, m] using hboundary


noncomputable def structuredBoxHalfBoundaryCondition
    {F : Type*} [Field F] [NumberField F] {r : ℕ} (B L : ℕ) (M : ℝ)
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ) : Prop :=
  let Halpha : ℝ := ∑ i, Height.logHeight₁ (alpha i)
  let cH : ℝ := 8 * (314 * (314 + 34) + 26) + Halpha +
    (314 * 9) * 8 * (Real.log ((2 * B + 1 : ℕ) : ℝ) + 32)
  let cC : ℝ := 2 + 312 + 8 + Real.log M + 81 * Halpha + cH
  let cV : ℝ := Real.log (boxAnalyticSlope B ell : ℝ) + 32
  let cFac : ℝ := 314 * (314 + 34)
  let cE : ℝ := 314 * 9
  let cLog : ℝ := 312 + cC + cE * cV + cFac + 321
  let cInner : ℝ := 24 + cC + cFac + 319 + cE * cV
  let cBase : ℝ := cLog + 2320 + 8 * cInner + 2 * Halpha
  cBase * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
      2 * (4 : ℝ) * (∑ i, ‖ell i‖) * (L : ℝ) ^ 32 + Real.log 2 <
    (L : ℝ) ^ 33 * Real.log ((2 * (4 : ℝ) - 1) / 3)

lemma fixed_radius_boundary_dominates_of_square
    (c s : ℝ) {N : ℕ} (hc : 0 ≤ c) (_hs : 0 ≤ s) (hN : 2 ≤ N)
    (hcN : 16 * c ≤ N) (hsN : 64 * s ≤ (N : ℝ) ^ 2) :
    c * ((((N ^ 2 : ℕ) : ℝ)) ^ 32 * Real.log ((N ^ 2 : ℕ) : ℝ)) +
          2 * (4 : ℝ) * s * (((N ^ 2 : ℕ) : ℝ)) ^ 32 + Real.log 2 <
        (((N ^ 2 : ℕ) : ℝ)) ^ 33 *
          Real.log ((2 * (4 : ℝ) - 1) / 3) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by positivity
  have hNone : (1 : ℝ) ≤ N := by linarith
  have hlogN : Real.log (N : ℝ) ≤ (N : ℝ) := by
    calc
      Real.log (N : ℝ) ≤ (N : ℝ) - 1 := Real.log_le_sub_one_of_pos hNpos
      _ ≤ (N : ℝ) := by linarith
  have hlogSq : Real.log ((N ^ 2 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
    linarith
  have hcTerm : c * Real.log ((N ^ 2 : ℕ) : ℝ) ≤
      (1 / 8 : ℝ) * (N : ℝ) ^ 2 := by
    have hNsqN : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hNsqR : (1 : ℝ) ≤ ((N ^ 2 : ℕ) : ℝ) := by exact_mod_cast hNsqN
    have h := mul_le_mul hcN hlogSq (Real.log_nonneg hNsqR) (by positivity)
    nlinarith
  have hsTerm : 2 * (4 : ℝ) * s ≤
      (1 / 8 : ℝ) * (N : ℝ) ^ 2 := by
    nlinarith
  have hlogTwo : Real.log 2 ≤ (1 / 4 : ℝ) * (N : ℝ) ^ 2 := by
    have hlt : Real.log 2 < 1 := (Real.log_two_lt_d9).trans (by norm_num)
    nlinarith [sq_nonneg ((N : ℝ) - 2)]
  have hinner : c * Real.log ((N ^ 2 : ℕ) : ℝ) +
      2 * (4 : ℝ) * s + Real.log 2 ≤
      (1 / 2 : ℝ) * (N : ℝ) ^ 2 := by linarith
  have hratio : (2 / 3 : ℝ) < Real.log ((2 * (4 : ℝ) - 1) / 3) := by
    have htwoLt : (2 : ℝ) < (2 * (4 : ℝ) - 1) / 3 := by norm_num
    have hlogMono : Real.log 2 < Real.log ((2 * (4 : ℝ) - 1) / 3) :=
      Real.strictMonoOn_log (by norm_num) (by norm_num) htwoLt
    have h23 : (2 / 3 : ℝ) < Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    exact h23.trans hlogMono
  have hinner' : c * Real.log ((N ^ 2 : ℕ) : ℝ) +
      2 * (4 : ℝ) * s + Real.log 2 <
      ((N ^ 2 : ℕ) : ℝ) * Real.log ((2 * (4 : ℝ) - 1) / 3) := by
    norm_num [Nat.cast_pow]
    nlinarith [sq_pos_of_pos hNpos]
  let X : ℝ := (((N ^ 2 : ℕ) : ℝ)) ^ 32
  have hX : 1 ≤ X := by
    dsimp [X]
    have hNsq : (1 : ℝ) ≤ ((N ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.one_le_pow 2 N (by omega : 1 ≤ N))
    exact one_le_pow₀ hNsq
  have hlogTwo0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc
    c * ((((N ^ 2 : ℕ) : ℝ)) ^ 32 * Real.log ((N ^ 2 : ℕ) : ℝ)) +
          2 * (4 : ℝ) * s * (((N ^ 2 : ℕ) : ℝ)) ^ 32 + Real.log 2 ≤
        X * (c * Real.log ((N ^ 2 : ℕ) : ℝ) +
          2 * (4 : ℝ) * s + Real.log 2) := by
      dsimp [X]
      nlinarith [mul_nonneg (sub_nonneg.mpr hX) hlogTwo0]
    _ < X * (((N ^ 2 : ℕ) : ℝ) *
          Real.log ((2 * (4 : ℝ) - 1) / 3)) :=
      mul_lt_mul_of_pos_left hinner' (by dsimp [X]; positivity)
    _ = (((N ^ 2 : ℕ) : ℝ)) ^ 33 *
          Real.log ((2 * (4 : ℝ) - 1) / 3) := by
      dsimp [X]
      ring

noncomputable def structuredBoxBoundaryBase
    {F : Type*} [Field F] [NumberField F] {r : ℕ} (B : ℕ) (M : ℝ)
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ) : ℝ :=
  let Halpha : ℝ := ∑ i, Height.logHeight₁ (alpha i)
  let cH : ℝ := 8 * (314 * (314 + 34) + 26) + Halpha +
    (314 * 9) * 8 * (Real.log ((2 * B + 1 : ℕ) : ℝ) + 32)
  let cC : ℝ := 2 + 312 + 8 + Real.log M + 81 * Halpha + cH
  let cV : ℝ := Real.log (boxAnalyticSlope B ell : ℝ) + 32
  let cFac : ℝ := 314 * (314 + 34)
  let cE : ℝ := 314 * 9
  let cLog : ℝ := 312 + cC + cE * cV + cFac + 321
  let cInner : ℝ := 24 + cC + cFac + 319 + cE * cV
  cLog + 2320 + 8 * cInner + 2 * Halpha

noncomputable def structuredBoxMasterScale
    {F : Type*} [Field F] [NumberField F] {r : ℕ} (B : ℕ) (M : ℝ)
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ) : ℝ :=
  max 2 (max ((314 ^ 9 * 314 * 16 : ℕ) + 1 : ℕ)
    (max (16 * structuredBoxBoundaryBase B M alpha ell)
      (64 * ∑ i, ‖ell i‖)))

noncomputable def structuredBoxMasterN
    {F : Type*} [Field F] [NumberField F] {r : ℕ} (B : ℕ) (M : ℝ)
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ) : ℕ :=
  Nat.ceil (structuredBoxMasterScale B M alpha ell)

noncomputable def structuredBoxMasterL
    {F : Type*} [Field F] [NumberField F] {r : ℕ} (B : ℕ) (M : ℝ)
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ) : ℕ :=
  (structuredBoxMasterN B M alpha ell) ^ 2

theorem structured_box_master_parameter
    {F : Type*} [Field F] [NumberField F] {r : ℕ} (B : ℕ) (M : ℝ)
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ) (hM : 1 ≤ M) :
    let L := structuredBoxMasterL B M alpha ell
    4 ≤ L ∧ 1 ≤ Real.log (L : ℝ) ∧
      314 ^ 9 * 314 * 16 < L ^ 3 ∧
      structuredBoxHalfBoundaryCondition B L M alpha ell ∧
      (structuredBoxMasterN B M alpha ell : ℝ) <
        structuredBoxMasterScale B M alpha ell + 1 := by
  dsimp only
  let c := structuredBoxBoundaryBase B M alpha ell
  let s : ℝ := ∑ i, ‖ell i‖
  let X := structuredBoxMasterScale B M alpha ell
  let N := structuredBoxMasterN B M alpha ell
  let L := N ^ 2
  have hH : 0 ≤ ∑ i, Height.logHeight₁ (alpha i) := by positivity
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hlogB : 0 ≤ Real.log ((2 * B + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * B + 1 by omega))
  have hlogSlope : 0 ≤ Real.log (boxAnalyticSlope B ell : ℝ) :=
    Real.log_nonneg (by exact_mod_cast boxAnalyticSlope_pos B ell)
  have hc : 0 ≤ c := by
    dsimp [c, structuredBoxBoundaryBase]
    positivity
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hX : 0 ≤ X := by
    dsimp [X, structuredBoxMasterScale]
    exact le_max_of_le_left (by norm_num)
  have hXN : X ≤ (N : ℝ) := by
    dsimp [N, structuredBoxMasterN]
    exact Nat.le_ceil X
  have hXtwo : (2 : ℝ) ≤ X := by
    dsimp [X, structuredBoxMasterScale]
    exact le_max_left _ _
  have hN : 2 ≤ N := by exact_mod_cast hXtwo.trans hXN
  have hNpos : 0 < N := by omega
  have hNc : 16 * c ≤ (N : ℝ) := by
    apply (show 16 * c ≤ X from ?_).trans hXN
    dsimp [X, structuredBoxMasterScale]
    exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hNs : 64 * s ≤ (N : ℝ) := by
    apply (show 64 * s ≤ X from ?_).trans hXN
    dsimp [X, structuredBoxMasterScale]
    exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  have hNleSq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
    nlinarith [show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega)]
  have hNsSq : 64 * s ≤ (N : ℝ) ^ 2 := hNs.trans hNleSq
  have hL4 : 4 ≤ L := by dsimp [L]; nlinarith
  have hlogL : 1 ≤ Real.log (L : ℝ) := by
    have hlogN : Real.log 2 ≤ Real.log (N : ℝ) := by
      exact Real.log_le_log (by norm_num) (by exact_mod_cast hN)
    have hhalf : (1 / 2 : ℝ) < Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    have hlogN' : (1 / 2 : ℝ) < Real.log (N : ℝ) := hhalf.trans_le hlogN
    dsimp [L]
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
    linarith
  have hconstX : (((314 ^ 9 * 314 * 16 : ℕ) + 1 : ℕ) : ℝ) ≤ X := by
    dsimp [X, structuredBoxMasterScale]
    exact le_max_of_le_right (le_max_left _ _)
  have hconstN : 314 ^ 9 * 314 * 16 < N := by
    have : (((314 ^ 9 * 314 * 16 : ℕ) + 1 : ℕ) : ℝ) ≤ (N : ℝ) :=
      hconstX.trans hXN
    exact_mod_cast this
  have hNleSix : N ≤ N ^ 6 := by
    simpa using Nat.pow_le_pow_right (show 1 ≤ N by omega) (show 1 ≤ 6 by omega)
  have hbig : 314 ^ 9 * 314 * 16 < L ^ 3 := by
    dsimp [L]
    rw [← pow_mul]
    exact hconstN.trans_le hNleSix
  have hdomRaw := fixed_radius_boundary_dominates_of_square
    c s hc hs hN hNc hNsSq
  have hdom : structuredBoxHalfBoundaryCondition B L M alpha ell := by
    simpa [structuredBoxHalfBoundaryCondition, structuredBoxBoundaryBase,
      c, s, L] using hdomRaw
  have hNupper : (N : ℝ) < X + 1 := by
    dsimp [N, structuredBoxMasterN]
    exact_mod_cast Nat.ceil_lt_add_one hX
  simpa [structuredBoxMasterL, N, L, X] using
    And.intro hL4 (And.intro hlogL (And.intro hbig (And.intro hdom hNupper)))

noncomputable def structuredBoxLogarithmicFormThreshold
    {F : Type*} [Field F] [NumberField F] {r : ℕ} (B L : ℕ) (M : ℝ)
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ) : ℝ :=
  let Halpha : ℝ := ∑ i, Height.logHeight₁ (alpha i)
  let cH : ℝ := 8 * (314 * (314 + 34) + 26) + Halpha +
    (314 * 9) * 8 * (Real.log ((2 * B + 1 : ℕ) : ℝ) + 32)
  let cC : ℝ := 2 + 312 + 8 + Real.log M + 81 * Halpha + cH
  let cV : ℝ := Real.log (boxAnalyticSlope B ell : ℝ) + 32
  let cFac : ℝ := 314 * (314 + 34)
  let cE : ℝ := 314 * 9
  let cLog : ℝ := 312 + cC + cE * cV + cFac + 321
  let cInner : ℝ := 24 + cC + cFac + 319 + cE * cV
  let cTotal : ℝ := cLog + 2320 + 8 * cInner + 2 * Halpha +
    2 * ∑ i, ‖ell i‖
  let cCore : ℝ := 312 + cC + cE * cV + 315 * (315 + 34) +
    318 + 2 * (∑ i, ‖ell i‖) + cV + 4
  let cPerturb : ℝ := 3956 + cCore
  let Xmax : ℝ := 2 * cTotal *
    ((L : ℝ) ^ 346 * Real.log (L : ℝ) + (L : ℝ) ^ 347)
  let Qperturb : ℝ := cPerturb * (L : ℝ) ^ 694 * Real.log (L : ℝ)
  min 1 (Real.exp (-(Xmax + Qperturb + Real.log 2)))

noncomputable def structuredBoxSmallSchedule
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (M : ℝ) {r B L : ℕ}
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ)
    (lambdaNorm : ℝ) : Prop :=
  let K := L ^ 32
  let P := L ^ 24
  let Ainit := L ^ 2
  let spend := L ^ 33
  let m := dyadicStageCount (K ^ (r + 1) * P)
  ∀ j, j < m → ∀ h < scaledDyadicStageA Ainit (j + 1),
    ∀ v < stageSpendBudget m spend (j + 1),
    ∀ q < stageUnitBudget m (j + 1),
    ∀ u : Fin r → ℕ,
    (∀ i, u i < stageSpendBudget m spend (j + 1)) →
    pochhammerWeightedApproximationBound (K ^ (r + 1)) P
        (scaledDyadicStageA Ainit j) spend 1 v q (∑ i, u i)
        (boxPochhammerStructuredCoefficientMajorant basis M r B K P
          Ainit (m * spend + 1) (m + 1) (m * spend + 1) alpha : ℝ)
        (boxAnalyticCoordinateBound B K ell : ℝ)
        ((K : ℝ) * ∑ i, ‖ell i‖)
        (4 * (scaledDyadicStageA Ainit (j + 1) : ℝ))
        (scaledDyadicStageA Ainit (j + 1) : ℝ) lambdaNorm <
      Real.exp (-((Module.finrank ℚ F : ℝ) *
            Real.log (K ^ (r + 1) + 1 : ℕ) +
          (Module.finrank ℚ F : ℝ) *
            Real.log (P * boxPochhammerStructuredCoefficientMajorant
                basis M r B K P Ainit
                  (m * spend + 1) (m + 1) (m * spend + 1) alpha *
              (v.factorial * (h + 1 + P) ^ P) *
              (boxAnalyticCoordinateBound B K ell) ^
                (q + ∑ i, u i) : ℕ) +
          (h : ℝ) * ((K : ℝ) *
            ∑ i, Height.logHeight₁ (alpha i))))

noncomputable def structuredBoxHalfBoundarySchedule
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (M : ℝ) {r B L : ℕ}
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ) : Prop :=
  let K := L ^ 32
  let P := L ^ 24
  let Ainit := L ^ 2
  let spend := L ^ 33
  let m := dyadicStageCount (K ^ (r + 1) * P)
  ∀ j, j < m → ∀ h < scaledDyadicStageA Ainit (j + 1),
    ∀ v < stageSpendBudget m spend (j + 1),
    ∀ q < stageUnitBudget m (j + 1),
    ∀ u : Fin r → ℕ,
    (∀ i, u i < stageSpendBudget m spend (j + 1)) →
    pochhammerWeightedApproximationBound (K ^ (r + 1)) P
        (scaledDyadicStageA Ainit j) spend 1 v q (∑ i, u i)
        (boxPochhammerStructuredCoefficientMajorant basis M r B K P
          Ainit (m * spend + 1) (m + 1) (m * spend + 1) alpha : ℝ)
        (boxAnalyticCoordinateBound B K ell : ℝ)
        ((K : ℝ) * ∑ i, ‖ell i‖)
        (4 * (scaledDyadicStageA Ainit (j + 1) : ℝ))
        (scaledDyadicStageA Ainit (j + 1) : ℝ) 0 <
      Real.exp (-((Module.finrank ℚ F : ℝ) *
            Real.log (K ^ (r + 1) + 1 : ℕ) +
          (Module.finrank ℚ F : ℝ) *
            Real.log (P * boxPochhammerStructuredCoefficientMajorant
                basis M r B K P Ainit
                  (m * spend + 1) (m + 1) (m * spend + 1) alpha *
              (v.factorial * (h + 1 + P) ^ P) *
              (boxAnalyticCoordinateBound B K ell) ^
                (q + ∑ i, u i) : ℕ) +
          (h : ℝ) * ((K : ℝ) *
            ∑ i, Height.logHeight₁ (alpha i)))) / 2

theorem structured_box_half_boundary_schedule
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (M : ℝ) {r B L : ℕ}
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ)
    (hr : r ≤ 8) (hd : Module.finrank ℚ F ≤ 8)
    (hL : 4 ≤ L) (hlogL : 1 ≤ Real.log (L : ℝ)) (hM : 1 ≤ M)
    (hbig : 314 ^ 9 * 314 * 16 < L ^ 3)
    (hdom : structuredBoxHalfBoundaryCondition B L M alpha ell) :
    structuredBoxHalfBoundarySchedule (B := B) (L := L)
      basis M alpha ell := by
  have hdom' :
      let Halpha : ℝ := ∑ i, Height.logHeight₁ (alpha i)
      let cH : ℝ := 8 * (314 * (314 + 34) + 26) + Halpha +
        (314 * 9) * 8 * (Real.log ((2 * B + 1 : ℕ) : ℝ) + 32)
      let cC : ℝ := 2 + 312 + 8 + Real.log M + 81 * Halpha + cH
      let cV : ℝ := Real.log (boxAnalyticSlope B ell : ℝ) + 32
      let cFac : ℝ := 314 * (314 + 34)
      let cE : ℝ := 314 * 9
      let cLog : ℝ := 312 + cC + cE * cV + cFac + 321
      let cInner : ℝ := 24 + cC + cFac + 319 + cE * cV
      let cBase : ℝ := cLog + 2320 + 8 * cInner + 2 * Halpha
      cBase * ((L : ℝ) ^ 32 * Real.log (L : ℝ)) +
          2 * (4 : ℝ) * (∑ i, ‖ell i‖) * (L : ℝ) ^ 32 + Real.log 2 <
        (L : ℝ) ^ 33 * Real.log ((2 * (4 : ℝ) - 1) / 3) := by
    simpa [structuredBoxHalfBoundaryCondition] using hdom
  have h := structured_box_boundary_half basis M alpha ell hr hd hL hlogL
    hM hbig hdom'
  simpa [structuredBoxHalfBoundarySchedule] using h

noncomputable def structuredBoxParameterEstimates
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (M : ℝ) {r B L : ℕ}
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ) : Prop :=
  let K := L ^ 32
  let P := L ^ 24
  let Ainit := L ^ 2
  let spend := L ^ 33
  let m := dyadicStageCount (K ^ (r + 1) * P)
  let C := boxPochhammerStructuredCoefficientMajorant basis M r B K P
    Ainit (m * spend + 1) (m + 1) (m * spend + 1) alpha
  let V := boxAnalyticCoordinateBound B K ell
  let Halpha : ℝ := ∑ i, Height.logHeight₁ (alpha i)
  let cH : ℝ := 8 * (314 * (314 + 34) + 26) + Halpha +
    (314 * 9) * 8 * (Real.log ((2 * B + 1 : ℕ) : ℝ) + 32)
  let cC : ℝ := 2 + 312 + 8 + Real.log M + 81 * Halpha + cH
  let cV : ℝ := Real.log (boxAnalyticSlope B ell : ℝ) + 32
  0 < C ∧ 1 ≤ V ∧ 0 ≤ Halpha ∧ 0 ≤ cV ∧
    Real.log (C : ℝ) ≤ cC * (L : ℝ) ^ 34 * Real.log (L : ℝ) ∧
    Real.log (V : ℝ) ≤ cV * Real.log (L : ℝ)

theorem structured_box_parameter_estimates
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (M : ℝ) {r B L : ℕ}
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ)
    (hr : r ≤ 8) (hd : Module.finrank ℚ F ≤ 8)
    (hL : 4 ≤ L) (hlogL : 1 ≤ Real.log (L : ℝ)) (hM : 1 ≤ M)
    (hbig : 314 ^ 9 * 314 * 16 < L ^ 3) :
    structuredBoxParameterEstimates (B := B) (L := L)
      basis M alpha ell := by
  let K := L ^ 32
  let P := L ^ 24
  let Ainit := L ^ 2
  let spend := L ^ 33
  let m := dyadicStageCount (K ^ (r + 1) * P)
  let Wsrc := m * spend + 1
  let Tsrc := m + 1
  let Ssrc := Wsrc
  let C := boxPochhammerStructuredCoefficientMajorant basis M r B K P
    Ainit Wsrc Tsrc Ssrc alpha
  let V := boxAnalyticCoordinateBound B K ell
  let Halpha : ℝ := ∑ i, Height.logHeight₁ (alpha i)
  let cMoment : ℝ := Real.log ((2 * B + 1 : ℕ) : ℝ) + 32
  let cH : ℝ := 8 * (314 * (314 + 34) + 26) + Halpha +
    (314 * 9) * 8 * cMoment
  let cC : ℝ := 2 + 312 + 8 + Real.log M + 81 * Halpha + cH
  let cV : ℝ := Real.log (boxAnalyticSlope B ell : ℝ) + 32
  have hdegCard : Fintype.card ι ≤ 8 := by
    rw [← Module.finrank_eq_card_basis basis]
    exact hd
  have hhalf := box_parameter_half_cardinality_initial_sq
    (r := r) (d := Fintype.card ι) hr hdegCard (by omega) hbig
  have hcM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hlogM : Real.log M ≤ Real.log M * Real.log (L : ℝ) :=
    le_mul_of_one_le_right hcM hlogL
  have hMomentPoly : boxMomentCoordinateBound B (L ^ 32) ≤
      (2 * B + 1) * L ^ 32 := boxMomentCoordinateBound_le_poly
  have hMomentPos : 0 < boxMomentCoordinateBound B (L ^ 32) := by
    exact lt_of_lt_of_le (by positivity : 0 < L ^ 32) (le_max_left _ _)
  have hlogMoment :
      Real.log (boxMomentCoordinateBound B (L ^ 32) : ℝ) ≤
        cMoment * Real.log (L : ℝ) := by
    have h := log_nat_le_log_coefficient_add hMomentPos
      (by omega : 0 < 2 * B + 1) (by omega : 0 < L) hlogL hMomentPoly
    simpa [cMoment] using h
  have hlogC : Real.log (C : ℝ) ≤
      cC * (L : ℝ) ^ 34 * Real.log (L : ℝ) := by
    dsimp [C, cC, cH, cMoment, Halpha, K, P, Ainit, Wsrc, Tsrc, Ssrc,
      m, spend]
    exact structured_initial_coefficient_log_le basis M (Real.log M)
      (Real.log ((2 * B + 1 : ℕ) : ℝ) + 32) alpha hr hd (by omega) hlogL
      hM hcM hlogM (by positivity) (by simpa [cMoment] using hlogMoment) hhalf
  have hC : 0 < C := by
    exact lt_of_lt_of_le zero_lt_one
      (one_le_boxPochhammerStructuredCoefficientMajorant
        basis M r B K P Ainit Wsrc Tsrc Ssrc alpha)
  have hV : 1 ≤ V := one_le_boxAnalyticCoordinateBound ell
  have hVpoly : V ≤ boxAnalyticSlope B ell * L ^ 32 := by
    simpa [V, K] using boxAnalyticCoordinateBound_le_slope ell (by positivity)
  have hlogV : Real.log (V : ℝ) ≤ cV * Real.log (L : ℝ) := by
    have h := log_nat_le_log_coefficient_add
      (n := V) (c := boxAnalyticSlope B ell) (e := 32) (L := L)
      (lt_of_lt_of_le zero_lt_one hV) (boxAnalyticSlope_pos B ell)
      (by omega) hlogL hVpoly
    simpa [cV] using h
  have hHalpha : 0 ≤ Halpha := by dsimp [Halpha]; positivity
  have hcV : 0 ≤ cV := by dsimp [cV]; positivity
  simpa [structuredBoxParameterEstimates, K, P, Ainit, spend, m, C, V,
    Halpha, cMoment, cH, cC, cV, Wsrc, Tsrc, Ssrc] using
    And.intro hC (And.intro hV (And.intro hHalpha
      (And.intro hcV (And.intro hlogC hlogV))))

theorem structured_box_small_schedule_of_prepared_data
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (M : ℝ) {r B L : ℕ}
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ)
    (lambdaNorm : ℝ)
    (hr : r ≤ 8) (hd : Module.finrank ℚ F ≤ 8)
    (hL : 4 ≤ L) (hlogL : 1 ≤ Real.log (L : ℝ))
    (hparams : structuredBoxParameterEstimates (B := B) (L := L)
      basis M alpha ell)
    (hboundary : structuredBoxHalfBoundarySchedule (B := B) (L := L)
      basis M alpha ell)
    (hlambda0 : 0 ≤ lambdaNorm)
    (hlambda : lambdaNorm ≤
      structuredBoxLogarithmicFormThreshold B L M alpha ell) :
    structuredBoxSmallSchedule (B := B) (L := L)
      basis M alpha ell lambdaNorm := by
  let K := L ^ 32
  let P := L ^ 24
  let Ainit := L ^ 2
  let spend := L ^ 33
  let m := dyadicStageCount (K ^ (r + 1) * P)
  let Wsrc := m * spend + 1
  let Tsrc := m + 1
  let Ssrc := Wsrc
  let C := boxPochhammerStructuredCoefficientMajorant basis M r B K P
    Ainit Wsrc Tsrc Ssrc alpha
  let V := boxAnalyticCoordinateBound B K ell
  let Halpha : ℝ := ∑ i, Height.logHeight₁ (alpha i)
  let cMoment : ℝ := Real.log ((2 * B + 1 : ℕ) : ℝ) + 32
  let cH : ℝ := 8 * (314 * (314 + 34) + 26) + Halpha +
    (314 * 9) * 8 * cMoment
  let cC : ℝ := 2 + 312 + 8 + Real.log M + 81 * Halpha + cH
  let cV : ℝ := Real.log (boxAnalyticSlope B ell : ℝ) + 32
  let cFac : ℝ := 314 * (314 + 34)
  let cE : ℝ := 314 * 9
  let cLog : ℝ := 312 + cC + cE * cV + cFac + 321
  let cInner : ℝ := 24 + cC + cFac + 319 + cE * cV
  let cTotal : ℝ := cLog + 2320 + 8 * cInner + 2 * Halpha +
    2 * ∑ i, ‖ell i‖
  let cCore : ℝ := 312 + cC + cE * cV + 315 * (315 + 34) +
    318 + 2 * (∑ i, ‖ell i‖) + cV + 4
  let cPerturb : ℝ := 3956 + cCore
  let Xmax : ℝ := 2 * cTotal *
    ((L : ℝ) ^ 346 * Real.log (L : ℝ) + (L : ℝ) ^ 347)
  let Qperturb : ℝ := cPerturb * (L : ℝ) ^ 694 * Real.log (L : ℝ)
  have hparams' : 0 < C ∧ 1 ≤ V ∧ 0 ≤ Halpha ∧ 0 ≤ cV ∧
      Real.log (C : ℝ) ≤ cC * (L : ℝ) ^ 34 * Real.log (L : ℝ) ∧
      Real.log (V : ℝ) ≤ cV * Real.log (L : ℝ) := by
    simpa [structuredBoxParameterEstimates, K, P, Ainit, spend, m, C, V,
      Halpha, cMoment, cH, cC, cV, Wsrc, Tsrc, Ssrc] using hparams
  rcases hparams' with ⟨hC, hV, hHalpha, hcV, hlogC, hlogV⟩
  have hzero :
      let K := L ^ 32
      let P := L ^ 24
      let Ainit := L ^ 2
      let spend := L ^ 33
      let m := dyadicStageCount (K ^ (r + 1) * P)
      ∀ j, j < m → ∀ h < scaledDyadicStageA Ainit (j + 1),
        ∀ v < stageSpendBudget m spend (j + 1),
        ∀ q < stageUnitBudget m (j + 1),
        ∀ u : Fin r → ℕ,
        (∀ i, u i < stageSpendBudget m spend (j + 1)) →
        pochhammerWeightedApproximationBound (K ^ (r + 1)) P
            (scaledDyadicStageA Ainit j) spend 1 v q (∑ i, u i)
            (C : ℝ) (V : ℝ) ((K : ℝ) * ∑ i, ‖ell i‖)
            (4 * (scaledDyadicStageA Ainit (j + 1) : ℝ))
            (scaledDyadicStageA Ainit (j + 1) : ℝ) 0 <
          Real.exp (-((Module.finrank ℚ F : ℝ) *
                Real.log (K ^ (r + 1) + 1 : ℕ) +
              (Module.finrank ℚ F : ℝ) *
                Real.log (P * C * (v.factorial * (h + 1 + P) ^ P) *
                  V ^ (q + ∑ i, u i) : ℕ) +
              (h : ℝ) * ((K : ℝ) * Halpha))) / 2 := by
    simpa [structuredBoxHalfBoundarySchedule, K, P, Ainit, spend, m,
      C, V, Halpha, Wsrc, Tsrc, Ssrc] using hboundary
  have hsmallBound := structured_box_small_of_norm_bound
    (C := C) (V := V) (d := Module.finrank ℚ F)
    ell Halpha cC cV lambdaNorm hr hd hHalpha hcV hlambda0
    hL hlogL hC hV hlogC hlogV hzero
  have hlambdaExp : lambdaNorm ≤
      Real.exp (-(Xmax + Qperturb + Real.log 2)) := by
    have hthreshold :
        structuredBoxLogarithmicFormThreshold B L M alpha ell =
          min 1 (Real.exp (-(Xmax + Qperturb + Real.log 2))) := by
      simp [structuredBoxLogarithmicFormThreshold, Halpha, cMoment, cH, cC,
        cV, cFac, cE, cLog, cInner, cTotal, cCore, cPerturb, Xmax, Qperturb]
    rw [hthreshold] at hlambda
    exact hlambda.trans (min_le_right _ _)
  have hsmall := hsmallBound (by
    simpa [Xmax, Qperturb, cPerturb, cCore, cTotal, cLog, cInner, cFac, cE]
      using hlambdaExp)
  simpa [structuredBoxSmallSchedule, K, P, Ainit, spend, m, C, V,
    Wsrc, Tsrc, Ssrc] using hsmall

theorem structured_box_small_schedule_of_norm_bound
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (M : ℝ) {r B L : ℕ}
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ)
    (lambdaNorm : ℝ)
    (hr : r ≤ 8) (hd : Module.finrank ℚ F ≤ 8)
    (hL : 4 ≤ L) (hlogL : 1 ≤ Real.log (L : ℝ)) (hM : 1 ≤ M)
    (hbig : 314 ^ 9 * 314 * 16 < L ^ 3)
    (hdom : structuredBoxHalfBoundaryCondition B L M alpha ell)
    (hlambda0 : 0 ≤ lambdaNorm)
    (hlambda : lambdaNorm ≤
      structuredBoxLogarithmicFormThreshold B L M alpha ell) :
    structuredBoxSmallSchedule (B := B) (L := L)
      basis M alpha ell lambdaNorm := by
  have hparams := structured_box_parameter_estimates
    (B := B) (L := L) basis M alpha ell hr hd hL hlogL hM hbig
  have hboundary := structured_box_half_boundary_schedule
    (B := B) (L := L) basis M alpha ell hr hd hL hlogL hM hbig hdom
  exact structured_box_small_schedule_of_prepared_data
    (B := B) (L := L) basis M alpha ell lambdaNorm hr hd hL hlogL
      hparams hboundary hlambda0 hlambda
theorem structured_box_logarithmic_form_lower_bound
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (φ : F →+* ℂ) {r B L : ℕ}
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ)
    (b : Fin (r + 1) → ℤ) (M : ℝ)
    (hr : r ≤ 8) (hd : Module.finrank ℚ F ≤ 8)
    (hL : 4 ≤ L) (hlogL : 1 ≤ Real.log (L : ℝ)) (hM : 1 ≤ M)
    (hMbasis : ∀ i (ψ : F →ₐ[ℚ] ℂ), ‖ψ (basis i)‖ ≤ M)
    (hbig : 314 ^ 9 * 314 * 16 < L ^ 3)
    (hdom : structuredBoxHalfBoundaryCondition B L M alpha ell)
    (hb : ∀ i, (b i).natAbs ≤ B) (hb0 : b 0 ≠ 0)
    (halpha : ∀ i, alpha i ≠ 0)
    (hinj : ∀ K, 0 < K → Function.Injective
      (fun x : ExponentBox (r + 1) K ↦ boxMonomial alpha x))
    (hexp : ∀ K (x : ExponentBox (r + 1) K),
      Complex.exp (boxLinearForm ell x) = φ (boxMonomial alpha x)) :
    structuredBoxLogarithmicFormThreshold B L M alpha ell ≤
      ‖∑ i, (b i : ℂ) * ell i‖ := by
  let K := L ^ 32
  let P := L ^ 24
  let Ainit := L ^ 2
  let spend := L ^ 33
  let m := dyadicStageCount (K ^ (r + 1) * P)
  let lambdaNorm : ℝ := ‖∑ i, (b i : ℂ) * ell i‖
  have hdegCard : Fintype.card ι ≤ 8 := by
    rw [← Module.finrank_eq_card_basis basis]
    exact hd
  have hcM : 0 ≤ M := zero_le_one.trans hM
  have hLone : 1 ≤ L := by omega
  have hbig8 : 314 ^ 9 * 314 * 8 < L ^ 3 := by
    have hconst8 : 314 ^ 9 * 314 * 8 < 314 ^ 9 * 314 * 16 := by
      nlinarith [show 0 < 314 ^ 9 * 314 by positivity]
    exact hconst8.trans hbig
  have hcard := box_parameter_cardinality_initial_sq
    (r := r) (d := Fintype.card ι) hr hdegCard (by omega) hbig8
  change structuredBoxLogarithmicFormThreshold B L M alpha ell ≤ lambdaNorm
  by_contra hnot
  have hlambdaLt : lambdaNorm <
      structuredBoxLogarithmicFormThreshold B L M alpha ell :=
    lt_of_not_ge hnot
  have hlambdaOne : lambdaNorm ≤ 1 := by
    apply hlambdaLt.le.trans
    unfold structuredBoxLogarithmicFormThreshold
    exact min_le_left _ _
  have hsmall := structured_box_small_schedule_of_norm_bound
    (B := B) (L := L)
    basis M alpha ell lambdaNorm hr hd hL hlogL hM hbig hdom
    (by dsimp [lambdaNorm]; positivity) hlambdaLt.le
  exact no_small_distinguished_linear_form_of_scaled_dyadic_schedule_structured
    basis hbasis φ alpha ell b M 4
      (K := K) (P := P) (Ainit := Ainit) (spend := spend)
      (by positivity) (by positivity)
      (by positivity) (by positivity)
      hcM hMbasis (by norm_num)
      (by simpa [K, P, Ainit, spend, m] using hcard) hb hb0 halpha
      (hinj K (by positivity)) (hexp K)
      (by simpa [lambdaNorm] using hlambdaOne)
      (by simpa [structuredBoxSmallSchedule, K, P, Ainit, spend, m,
          lambdaNorm] using hsmall)

theorem structured_box_logarithmic_form_lower_bound_at_master
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (φ : F →+* ℂ) {r B : ℕ}
    (alpha : Fin (r + 1) → F) (ell : Fin (r + 1) → ℂ)
    (b : Fin (r + 1) → ℤ) (M : ℝ)
    (hr : r ≤ 8) (hd : Module.finrank ℚ F ≤ 8) (hM : 1 ≤ M)
    (hMbasis : ∀ i (ψ : F →ₐ[ℚ] ℂ), ‖ψ (basis i)‖ ≤ M)
    (hb : ∀ i, (b i).natAbs ≤ B) (hb0 : b 0 ≠ 0)
    (halpha : ∀ i, alpha i ≠ 0)
    (hinj : ∀ K, 0 < K → Function.Injective
      (fun x : ExponentBox (r + 1) K ↦ boxMonomial alpha x))
    (hexp : ∀ K (x : ExponentBox (r + 1) K),
      Complex.exp (boxLinearForm ell x) = φ (boxMonomial alpha x)) :
    structuredBoxLogarithmicFormThreshold B
        (structuredBoxMasterL B M alpha ell) M alpha ell ≤
      ‖∑ i, (b i : ℂ) * ell i‖ := by
  obtain ⟨hL, hlogL, hbig, hdom, _hupper⟩ :=
    structured_box_master_parameter B M alpha ell hM
  exact structured_box_logarithmic_form_lower_bound
    basis hbasis φ alpha ell b M hr hd hL hlogL hM hMbasis hbig hdom
      hb hb0 halpha hinj hexp

/-- The master-parameter lower bound is invariant under a finite
reindexing of the logarithms.  Besides making the symmetry explicit, this
wrapper lets an application move any nonzero coefficient into the
distinguished zeroth coordinate required by the auxiliary construction. -/
theorem structured_box_logarithmic_form_lower_bound_at_master_reindex
    {F ι : Type*} [Field F] [NumberField F] [Fintype ι]
    (basis : Module.Basis ι ℚ F) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (φ : F →+* ℂ) {r n B : ℕ}
    (e : Fin (r + 1) ≃ Fin n)
    (alpha : Fin n → F) (ell : Fin n → ℂ)
    (b : Fin n → ℤ) (M : ℝ)
    (hr : r ≤ 8) (hd : Module.finrank ℚ F ≤ 8) (hM : 1 ≤ M)
    (hMbasis : ∀ i (ψ : F →ₐ[ℚ] ℂ), ‖ψ (basis i)‖ ≤ M)
    (hb : ∀ i, (b i).natAbs ≤ B) (hb0 : b (e 0) ≠ 0)
    (halpha : ∀ i, alpha i ≠ 0)
    (hinj : ∀ K, 0 < K → Function.Injective
      (fun x : ExponentBox n K ↦ boxMonomial alpha x))
    (hexp : ∀ K (x : ExponentBox n K),
      Complex.exp (boxLinearForm ell x) = φ (boxMonomial alpha x)) :
    structuredBoxLogarithmicFormThreshold B
        (structuredBoxMasterL B M (fun i ↦ alpha (e i))
          (fun i ↦ ell (e i))) M
        (fun i ↦ alpha (e i)) (fun i ↦ ell (e i)) ≤
      ‖∑ i, (b i : ℂ) * ell i‖ := by
  let alpha' : Fin (r + 1) → F := fun i ↦ alpha (e i)
  let ell' : Fin (r + 1) → ℂ := fun i ↦ ell (e i)
  let b' : Fin (r + 1) → ℤ := fun i ↦ b (e i)
  have hinj' : ∀ K, 0 < K → Function.Injective
      (fun x : ExponentBox (r + 1) K ↦ boxMonomial alpha' x) := by
    intro K hK x y hxy
    let ex : ExponentBox n K := fun j ↦ x (e.symm j)
    let ey : ExponentBox n K := fun j ↦ y (e.symm j)
    have hmonox : boxMonomial alpha' x = boxMonomial alpha ex := by
      rw [boxMonomial, boxMonomial]
      simpa [alpha', ex] using
        (e.prod_comp (fun j ↦ alpha j ^ (x (e.symm j) : ℕ)))
    have hmonoy : boxMonomial alpha' y = boxMonomial alpha ey := by
      rw [boxMonomial, boxMonomial]
      simpa [alpha', ey] using
        (e.prod_comp (fun j ↦ alpha j ^ (y (e.symm j) : ℕ)))
    have hexy : ex = ey := hinj K hK
      (hmonox.symm.trans (hxy.trans hmonoy))
    funext i
    have hi := congrFun hexy (e i)
    simpa [ex, ey] using hi
  have hexp' : ∀ K (x : ExponentBox (r + 1) K),
      Complex.exp (boxLinearForm ell' x) = φ (boxMonomial alpha' x) := by
    intro K x
    let ex : ExponentBox n K := fun j ↦ x (e.symm j)
    have hlin : boxLinearForm ell' x = boxLinearForm ell ex := by
      rw [boxLinearForm, boxLinearForm]
      simpa [ell', ex] using
        (e.sum_comp (fun j ↦ ((x (e.symm j) : ℕ) : ℂ) * ell j))
    have hmono : boxMonomial alpha' x = boxMonomial alpha ex := by
      rw [boxMonomial, boxMonomial]
      simpa [alpha', ex] using
        (e.prod_comp (fun j ↦ alpha j ^ (x (e.symm j) : ℕ)))
    rw [hlin, hmono]
    exact hexp K ex
  have hmain := structured_box_logarithmic_form_lower_bound_at_master
    basis hbasis φ alpha' ell' b' M hr hd hM hMbasis
      (fun i ↦ hb (e i)) hb0 (fun i ↦ halpha (e i)) hinj' hexp'
  have hsum : (∑ i, (b' i : ℂ) * ell' i) =
      ∑ i, (b i : ℂ) * ell i := by
    simpa [b', ell'] using
      (e.sum_comp (fun i ↦ (b i : ℂ) * ell i))
  simpa [alpha', ell', hsum] using hmain

theorem auxiliaryExponentialSum_norm_le_of_multipoint_moments
    {kappa iota : Type*} [Fintype kappa] [Fintype iota]
    [DecidableEq iota]
    (c L : kappa → ℂ) (b0 Lambda : ℂ)
    (a : kappa → ℂ) (r : kappa → iota → ℂ)
    (ell : iota → ℂ) (A T S k : ℕ) {C M U R Z : ℝ} {z : ℂ}
    (hA : 0 < A) (hk : 0 < k) (hkS : k ≤ S)
    (hC : 0 ≤ C) (hM : 1 ≤ M) (hU : 0 ≤ U)
    (hb0 : 1 ≤ ‖b0‖)
    (hc : ∀ x, ‖c x‖ ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ M)
    (hr : ∀ x, ‖∑ i, r x i * ell i‖ ≤ M)
    (hLambda : ‖Lambda‖ ≤ 1)
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hcoord : ∀ x, b0 * L x =
      a x * Lambda + ∑ i, r x i * ell i)
    (hmoment : ∀ node : Fin A, ∀ q, q < T → ∀ p, p < S →
      ∀ u ∈ Finset.piAntidiag (Finset.univ : Finset iota) p,
        ∑ x, (c x * Complex.exp (L x * (node : ℂ))) *
          a x ^ q * ∏ i, r x i ^ u i = 0)
    (hAR : (A : ℝ) < R) (hz : ‖z‖ ≤ Z) (hZR : Z ≤ R) :
    ‖auxiliaryExponentialSum L c z‖ ≤
      (Z + A) ^ (k * A) *
        (((Fintype.card kappa : ℝ) * C * Real.exp (U * R) +
          (A * k : ℝ) *
            ((A * k : ℝ) * hermiteInterpolationBound A k *
              (‖Lambda‖ ^ T *
                ((Fintype.card kappa : ℝ) *
                  (C * Real.exp (U * A)) * M ^ k * (2 : ℝ) ^ k))) *
            max 1 (R ^ (A * k))) /
          (R - A) ^ (k * A)) +
      (A * k : ℝ) *
        ((A * k : ℝ) * hermiteInterpolationBound A k *
          (‖Lambda‖ ^ T *
            ((Fintype.card kappa : ℝ) *
              (C * Real.exp (U * A)) * M ^ k * (2 : ℝ) ^ k))) *
        max 1 (Z ^ (A * k)) := by
  apply analytic_norm_le_of_approximate_nat_node_jets
    (auxiliaryExponentialSum L c) A k hA hk
    (δ := ‖Lambda‖ ^ T *
      ((Fintype.card kappa : ℝ) *
        (C * Real.exp (U * A)) * M ^ k * (2 : ℝ) ^ k))
    (M := (Fintype.card kappa : ℝ) * C * Real.exp (U * R))
  · positivity
  · exact hAR
  · exact hz
  · exact hZR
  · intro w
    unfold auxiliaryExponentialSum
    fun_prop
  · exact auxiliaryExponentialSum_normalized_jet_norm_le_of_multipoint_moments
      c L b0 Lambda a r ell A T S k hC hM hU hb0 hc ha hr
      hLambda hL hcoord hmoment hkS
  · intro w hw
    have hwNorm : ‖w‖ = R := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hw
    have hbound := iteratedDeriv_auxiliaryExponentialSum_norm_le
      L c 0 hC hU hc hL (by rw [hwNorm])
    simpa using hbound

noncomputable def multipointApproximationBound
    (N A k T : ℕ) (C M U R Z lambdaNorm : ℝ) : ℝ :=
  (Z + A) ^ (k * A) *
      ((N * C * Real.exp (U * R) +
        (A * k) *
          ((A * k) * hermiteInterpolationBound A k *
            (lambdaNorm ^ T *
              (N * (C * Real.exp (U * A)) * M ^ k * 2 ^ k))) *
          max 1 (R ^ (A * k))) /
        (R - A) ^ (k * A)) +
    (A * k) *
      ((A * k) * hermiteInterpolationBound A k *
        (lambdaNorm ^ T *
          (N * (C * Real.exp (U * A)) * M ^ k * 2 ^ k))) *
      max 1 (Z ^ (A * k))

theorem auxiliaryExponentialSum_norm_le_multipointApproximationBound
    {kappa iota : Type*} [Fintype kappa] [Fintype iota]
    [DecidableEq iota]
    (c L : kappa → ℂ) (b0 Lambda : ℂ)
    (a : kappa → ℂ) (r : kappa → iota → ℂ)
    (ell : iota → ℂ) (A T S k : ℕ) {C M U R Z : ℝ} {z : ℂ}
    (hA : 0 < A) (hk : 0 < k) (hkS : k ≤ S)
    (hC : 0 ≤ C) (hM : 1 ≤ M) (hU : 0 ≤ U)
    (hb0 : 1 ≤ ‖b0‖)
    (hc : ∀ x, ‖c x‖ ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ M)
    (hr : ∀ x, ‖∑ i, r x i * ell i‖ ≤ M)
    (hLambda : ‖Lambda‖ ≤ 1)
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hcoord : ∀ x, b0 * L x =
      a x * Lambda + ∑ i, r x i * ell i)
    (hmoment : ∀ node : Fin A, ∀ q, q < T → ∀ p, p < S →
      ∀ u ∈ Finset.piAntidiag (Finset.univ : Finset iota) p,
        ∑ x, (c x * Complex.exp (L x * (node : ℂ))) *
          a x ^ q * ∏ i, r x i ^ u i = 0)
    (hAR : (A : ℝ) < R) (hz : ‖z‖ ≤ Z) (hZR : Z ≤ R) :
    ‖auxiliaryExponentialSum L c z‖ ≤
      multipointApproximationBound (Fintype.card kappa) A k T
        C M U R Z ‖Lambda‖ := by
  simpa [multipointApproximationBound, Nat.cast_mul] using
    auxiliaryExponentialSum_norm_le_of_multipoint_moments
      c L b0 Lambda a r ell A T S k hA hk hkS hC hM hU hb0
      hc ha hr hLambda hL hcoord hmoment hAR hz hZR

theorem multipointMomentValue_eq_zero_of_approximate_extrapolation
    {F kappa iota : Type*} [Field F] [NumberField F]
    [Fintype kappa] [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) (beta : kappa → F)
    (c : kappa → ℤ) (L : kappa → ℂ) (b0 Lambda : ℂ)
    (a : kappa → ℤ) (r : kappa → iota → ℤ) (ell : iota → ℂ)
    {A T S k h : ℕ} {C H V M U R Z : ℝ}
    (hA : 0 < A) (hk : 0 < k) (hkS : k ≤ S)
    (hb0 : 1 ≤ ‖b0‖) (hC : 1 ≤ C) (hV : 1 ≤ V)
    (hM : 1 ≤ M) (hU : 0 ≤ U)
    (hc : ∀ x, (c x).natAbs ≤ C)
    (hbeta : ∀ x, Height.logHeight₁ (beta x) ≤ H)
    (haV : ∀ x, ‖a x‖ ≤ V) (hrV : ∀ x i, ‖r x i‖ ≤ V)
    (haM : ∀ x, ‖a x‖ ≤ M)
    (hrM : ∀ x, ‖∑ i, (r x i : ℂ) * ell i‖ ≤ M)
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (beta x))
    (hLambda : ‖Lambda‖ ≤ 1)
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin A, ∀ q : Fin T, ∀ u : iota → Fin S,
      multipointMomentValue beta a r c node q (fun i ↦ u i) = 0)
    (hAR : (A : ℝ) < R) (hhZ : (h : ℝ) ≤ Z) (hZR : Z ≤ R)
    (hsmall :
      multipointApproximationBound (Fintype.card kappa) A k T
          C M U R Z ‖Lambda‖ <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
            Real.log (Fintype.card kappa : ℝ) +
          (Fintype.card kappa : ℝ) *
            ((Module.finrank ℚ F : ℝ) * Real.log C + (h : ℝ) * H)))) :
    multipointMomentValue beta a r c h 0 (fun _ ↦ 0) = 0 := by
  have hcComplex : ∀ x, ‖(c x : ℂ)‖ ≤ C := by
    intro x
    simpa [Complex.norm_intCast, Int.cast_abs, Int.natCast_natAbs] using hc x
  have hmomentC : ∀ node : Fin A, ∀ q, q < T → ∀ p, p < S →
      ∀ u ∈ Finset.piAntidiag (Finset.univ : Finset iota) p,
        ∑ x, ((c x : ℂ) * Complex.exp (L x * (node : ℂ))) *
          (a x : ℂ) ^ q * ∏ i, (r x i : ℂ) ^ u i = 0 := by
    intro node q hq p hp u hu
    let q' : Fin T := ⟨q, hq⟩
    have hui : ∀ i, u i < S := by
      intro i
      have hle : u i ≤ p := by
        have hsum := (Finset.mem_piAntidiag.mp hu).1
        rw [← hsum]
        exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le (u j))
          (Finset.mem_univ i)
      omega
    let u' : iota → Fin S := fun i ↦ ⟨u i, hui i⟩
    have hmapped := congrArg φ (hmoment node q' u')
    rw [map_zero, multipointMomentValue_embedding] at hmapped
    calc
      ∑ x, ((c x : ℂ) * Complex.exp (L x * (node : ℂ))) *
          (a x : ℂ) ^ q * ∏ i, (r x i : ℂ) ^ u i =
          ∑ x, (c x : ℂ) * φ (beta x) ^ (node : ℕ) *
            (a x : ℂ) ^ q * ∏ i, (r x i : ℂ) ^ u i := by
        apply Finset.sum_congr rfl
        intro x hx
        have hpow : Complex.exp (L x * (node : ℂ)) =
            φ (beta x) ^ (node : ℕ) := by
          calc
            Complex.exp (L x * (node : ℂ)) =
                Complex.exp ((node : ℂ) * L x) := by rw [mul_comm]
            _ = Complex.exp (L x) ^ (node : ℕ) := Complex.exp_nat_mul _ _
            _ = φ (beta x) ^ (node : ℕ) := by rw [hexp]
        rw [hpow]
      _ = 0 := by simpa [q', u'] using hmapped
  have hanalytic := auxiliaryExponentialSum_norm_le_multipointApproximationBound
    (fun x ↦ (c x : ℂ)) L b0 Lambda
    (fun x ↦ (a x : ℂ)) (fun x i ↦ (r x i : ℂ)) ell
    A T S k hA hk hkS (zero_le_one.trans hC) hM hU hb0 hcComplex
    (fun x ↦ by simpa [Int.norm_eq_abs] using haM x) hrM hLambda hL
    hcoord hmomentC hAR (z := (h : ℂ)) (by simpa using hhZ) hZR
  have heval : auxiliaryExponentialSum L (fun x ↦ (c x : ℂ)) (h : ℂ) =
      φ (multipointMomentValue beta a r c h 0 (fun _ ↦ 0)) := by
    rw [multipointMomentValue_embedding]
    unfold auxiliaryExponentialSum
    apply Finset.sum_congr rfl
    intro x hx
    have hp : Complex.exp (L x * (h : ℂ)) = φ (beta x) ^ h := by
      calc
        Complex.exp (L x * (h : ℂ)) =
            Complex.exp ((h : ℂ) * L x) := by rw [mul_comm]
        _ = Complex.exp (L x) ^ h := Complex.exp_nat_mul _ _
        _ = φ (beta x) ^ h := by rw [hexp]
    rw [hp]
    simp
  by_contra hne
  have hheight := logHeight₁_multipointMomentValue_le
    beta a r c h 0 (fun _ ↦ 0) hC hV hc hbeta haV hrV
  have hlocal := neg_logHeight₁_le_log_norm_embedding φ hne
  have hlower : Real.exp (-((Module.finrank ℚ F : ℝ) *
            Real.log (Fintype.card kappa : ℝ) +
          (Fintype.card kappa : ℝ) *
            ((Module.finrank ℚ F : ℝ) * Real.log C + (h : ℝ) * H))) ≤
      ‖φ (multipointMomentValue beta a r c h 0 (fun _ ↦ 0))‖ := by
    have hlog : -((Module.finrank ℚ F : ℝ) *
            Real.log (Fintype.card kappa : ℝ) +
          (Fintype.card kappa : ℝ) *
            ((Module.finrank ℚ F : ℝ) * Real.log C + (h : ℝ) * H)) ≤
        Real.log ‖φ (multipointMomentValue beta a r c h 0 (fun _ ↦ 0))‖ := by
      have hsimp : ((0 + ∑ _i : iota, 0 : ℕ) : ℝ) *
          ((Module.finrank ℚ F : ℝ) * Real.log V) = 0 := by simp
      rw [hsimp, add_zero] at hheight
      exact (neg_le_neg hheight).trans hlocal
    have hnormPos : 0 <
        ‖φ (multipointMomentValue beta a r c h 0 (fun _ ↦ 0))‖ :=
      norm_pos_iff.mpr ((map_ne_zero φ).2 hne)
    calc
      _ ≤ Real.exp (Real.log
          ‖φ (multipointMomentValue beta a r c h 0 (fun _ ↦ 0))‖) :=
        Real.exp_le_exp.mpr hlog
      _ = _ := Real.exp_log hnormPos
  rw [← heval] at hlower
  linarith

theorem multipointMomentValue_eq_zero_of_shifted_approximate_extrapolation
    {F kappa iota : Type*} [Field F] [NumberField F]
    [Fintype kappa] [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) (beta : kappa → F)
    (c : kappa → ℤ) (L : kappa → ℂ) (b0 Lambda : ℂ)
    (a : kappa → ℤ) (r : kappa → iota → ℤ) (ell : iota → ℂ)
    {A Tsrc Ssrc T0 S0 k h q0 : ℕ} (u0 : iota → ℕ)
    {C H V M U R Z : ℝ}
    (hA : 0 < A) (hk : 0 < k) (hkS : k ≤ S0)
    (hT : q0 + T0 ≤ Tsrc) (hS : ∀ i, u0 i + S0 ≤ Ssrc)
    (hb0 : 1 ≤ ‖b0‖) (hC : 1 ≤ C) (hV : 1 ≤ V)
    (hM : 1 ≤ M) (hU : 0 ≤ U)
    (hc : ∀ x, (c x).natAbs ≤ C)
    (hbeta : ∀ x, Height.logHeight₁ (beta x) ≤ H)
    (haV : ∀ x, ‖a x‖ ≤ V) (hrV : ∀ x i, ‖r x i‖ ≤ V)
    (haM : ∀ x, ‖a x‖ ≤ M)
    (hrM : ∀ x, ‖∑ i, (r x i : ℂ) * ell i‖ ≤ M)
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (beta x))
    (hLambda : ‖Lambda‖ ≤ 1)
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin A, ∀ q : Fin Tsrc, ∀ u : iota → Fin Ssrc,
      multipointMomentValue beta a r c node q (fun i ↦ u i) = 0)
    (hAR : (A : ℝ) < R) (hhZ : (h : ℝ) ≤ Z) (hZR : Z ≤ R)
    (hsmall :
      multipointApproximationBound (Fintype.card kappa) A k T0
          (C * V ^ (q0 + ∑ i, u0 i)) M U R Z ‖Lambda‖ <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (Fintype.card kappa : ℝ) +
            (Fintype.card kappa : ℝ) *
              ((Module.finrank ℚ F : ℝ) * Real.log C +
                (h : ℝ) * H +
                ((q0 + ∑ i, u0 i : ℕ) : ℝ) *
                  ((Module.finrank ℚ F : ℝ) * Real.log V))))) :
    multipointMomentValue beta a r c h q0 u0 = 0 := by
  let d : kappa → ℂ := fun x ↦
    (c x : ℂ) * (a x : ℂ) ^ q0 * ∏ i, (r x i : ℂ) ^ u0 i
  have hd : ∀ x, ‖d x‖ ≤ C * V ^ (q0 + ∑ i, u0 i) := by
    intro x
    have hcR : ‖(c x : ℂ)‖ ≤ C := by
      simpa [Complex.norm_intCast, Int.cast_abs, Int.natCast_natAbs] using hc x
    dsimp [d]
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_prod]
    have hprod : ∏ i, ‖((r x i : ℂ) ^ u0 i)‖ ≤
        V ^ (∑ i, u0 i) := by
      calc
        ∏ i, ‖((r x i : ℂ) ^ u0 i)‖ =
            ∏ i, ‖(r x i : ℂ)‖ ^ u0 i := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [norm_pow]
        _ ≤ ∏ i, V ^ u0 i := by
          gcongr with i hi
          simpa [Int.norm_eq_abs] using hrV x i
        _ = V ^ (∑ i, u0 i) := by rw [← Finset.prod_pow_eq_pow_sum]
    calc
      ‖(c x : ℂ)‖ * ‖(a x : ℂ)‖ ^ q0 *
          ∏ i, ‖((r x i : ℂ) ^ u0 i)‖ ≤
        C * V ^ q0 * V ^ (∑ i, u0 i) := by
          have haR : ‖(a x : ℂ)‖ ≤ V := by
            simpa [Int.norm_eq_abs] using haV x
          have hpowA : ‖(a x : ℂ)‖ ^ q0 ≤ V ^ q0 :=
            pow_le_pow_left₀ (norm_nonneg _) haR q0
          exact mul_le_mul
            (mul_le_mul hcR hpowA (by positivity) (zero_le_one.trans hC))
            hprod (by positivity) (by positivity)
      _ = C * V ^ (q0 + ∑ i, u0 i) := by rw [pow_add]; ring
  have hmomentC : ∀ node : Fin A, ∀ q, q < T0 → ∀ p, p < S0 →
      ∀ u ∈ Finset.piAntidiag (Finset.univ : Finset iota) p,
        ∑ x, (d x * Complex.exp (L x * (node : ℂ))) *
          (a x : ℂ) ^ q * ∏ i, (r x i : ℂ) ^ u i = 0 := by
    intro node q hq p hp u hu
    have hqsrc : q0 + q < Tsrc := by omega
    let q' : Fin Tsrc := ⟨q0 + q, hqsrc⟩
    have hui : ∀ i, u0 i + u i < Ssrc := by
      intro i
      have hle : u i ≤ p := by
        have hsum := (Finset.mem_piAntidiag.mp hu).1
        rw [← hsum]
        exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le (u j))
          (Finset.mem_univ i)
      have hs := hS i
      omega
    let u' : iota → Fin Ssrc := fun i ↦ ⟨u0 i + u i, hui i⟩
    have hmapped := congrArg φ (hmoment node q' u')
    rw [map_zero, multipointMomentValue_embedding] at hmapped
    calc
      ∑ x, (d x * Complex.exp (L x * (node : ℂ))) *
          (a x : ℂ) ^ q * ∏ i, (r x i : ℂ) ^ u i =
          ∑ x, (c x : ℂ) * φ (beta x) ^ (node : ℕ) *
            (a x : ℂ) ^ (q0 + q) *
              ∏ i, (r x i : ℂ) ^ (u0 i + u i) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hpow : Complex.exp (L x * (node : ℂ)) =
            φ (beta x) ^ (node : ℕ) := by
          calc
            Complex.exp (L x * (node : ℂ)) =
                Complex.exp ((node : ℂ) * L x) := by rw [mul_comm]
            _ = Complex.exp (L x) ^ (node : ℕ) := Complex.exp_nat_mul _ _
            _ = φ (beta x) ^ (node : ℕ) := by rw [hexp]
        rw [hpow]
        dsimp [d]
        simp_rw [pow_add]
        rw [Finset.prod_mul_distrib]
        ring
      _ = 0 := by simpa [q', u'] using hmapped
  have hanalytic := auxiliaryExponentialSum_norm_le_multipointApproximationBound
    d L b0 Lambda (fun x ↦ (a x : ℂ)) (fun x i ↦ (r x i : ℂ)) ell
    A T0 S0 k hA hk hkS (by positivity) hM hU hb0 hd
    (fun x ↦ by simpa [Int.norm_eq_abs] using haM x) hrM hLambda hL
    hcoord hmomentC hAR (z := (h : ℂ)) (by simpa using hhZ) hZR
  have heval : auxiliaryExponentialSum L d (h : ℂ) =
      φ (multipointMomentValue beta a r c h q0 u0) := by
    rw [multipointMomentValue_embedding]
    unfold auxiliaryExponentialSum
    apply Finset.sum_congr rfl
    intro x hx
    have hp : Complex.exp (L x * (h : ℂ)) = φ (beta x) ^ h := by
      calc
        Complex.exp (L x * (h : ℂ)) =
            Complex.exp ((h : ℂ) * L x) := by rw [mul_comm]
        _ = Complex.exp (L x) ^ h := Complex.exp_nat_mul _ _
        _ = φ (beta x) ^ h := by rw [hexp]
    rw [hp]
    dsimp [d]
    ring
  by_contra hne
  have hheight := logHeight₁_multipointMomentValue_le
    beta a r c h q0 u0 hC hV hc hbeta haV hrV
  have hlocal := neg_logHeight₁_le_log_norm_embedding φ hne
  have hlower : Real.exp (-
          ((Module.finrank ℚ F : ℝ) *
              Real.log (Fintype.card kappa : ℝ) +
            (Fintype.card kappa : ℝ) *
              ((Module.finrank ℚ F : ℝ) * Real.log C +
                (h : ℝ) * H +
                ((q0 + ∑ i, u0 i : ℕ) : ℝ) *
                  ((Module.finrank ℚ F : ℝ) * Real.log V)))) ≤
      ‖φ (multipointMomentValue beta a r c h q0 u0)‖ := by
    have hlog : -
          ((Module.finrank ℚ F : ℝ) *
              Real.log (Fintype.card kappa : ℝ) +
            (Fintype.card kappa : ℝ) *
              ((Module.finrank ℚ F : ℝ) * Real.log C +
                (h : ℝ) * H +
                ((q0 + ∑ i, u0 i : ℕ) : ℝ) *
                  ((Module.finrank ℚ F : ℝ) * Real.log V))) ≤
        Real.log ‖φ (multipointMomentValue beta a r c h q0 u0)‖ :=
      (neg_le_neg hheight).trans hlocal
    have hnormPos : 0 < ‖φ (multipointMomentValue beta a r c h q0 u0)‖ :=
      norm_pos_iff.mpr ((map_ne_zero φ).2 hne)
    calc
      _ ≤ Real.exp (Real.log
          ‖φ (multipointMomentValue beta a r c h q0 u0)‖) :=
        Real.exp_le_exp.mpr hlog
      _ = _ := Real.exp_log hnormPos
  rw [← heval] at hlower
  linarith

/-- Shifted approximate extrapolation for a full exponent box, using the
structured projective-height bound rather than charging each monomial
separately. -/
theorem boxMultipointMomentValue_eq_zero_of_shifted_approximate_extrapolation
    {F iota : Type*} [Field F] [NumberField F]
    [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) {n K : ℕ} (alpha : Fin n → F)
    (c : ExponentBox n K → ℤ) (L : ExponentBox n K → ℂ)
    (b0 Lambda : ℂ) (a : ExponentBox n K → ℤ)
    (r : ExponentBox n K → iota → ℤ) (ell : iota → ℂ)
    {A Tsrc Ssrc T0 S0 k h q0 : ℕ} (u0 : iota → ℕ)
    {C V : ℕ} {M U R Z : ℝ}
    (hK : 0 < K) (hA : 0 < A) (hk : 0 < k) (hkS : k ≤ S0)
    (hT : q0 + T0 ≤ Tsrc) (hS : ∀ i, u0 i + S0 ≤ Ssrc)
    (hb0 : 1 ≤ ‖b0‖) (hC : 1 ≤ C) (hV : 1 ≤ V)
    (hM : 1 ≤ M) (hU : 0 ≤ U)
    (hc : ∀ x, (c x).natAbs ≤ C)
    (haV : ∀ x, ‖a x‖ ≤ (V : ℝ))
    (hrV : ∀ x i, ‖r x i‖ ≤ (V : ℝ))
    (haM : ∀ x, ‖a x‖ ≤ M)
    (hrM : ∀ x, ‖∑ i, (r x i : ℂ) * ell i‖ ≤ M)
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (boxMonomial alpha x))
    (hLambda : ‖Lambda‖ ≤ 1)
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin A, ∀ q : Fin Tsrc, ∀ u : iota → Fin Ssrc,
      multipointMomentValue (boxMonomial alpha) a r c node q
        (fun i ↦ u i) = 0)
    (hAR : (A : ℝ) < R) (hhZ : (h : ℝ) ≤ Z) (hZR : Z ≤ R)
    (hsmall :
      multipointApproximationBound (K ^ n) A k T0
          ((C * V ^ (q0 + ∑ i, u0 i) : ℕ) : ℝ) M U R Z ‖Lambda‖ <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ n + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (C * V ^ (q0 + ∑ i, u0 i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i))))) :
    multipointMomentValue (boxMonomial alpha) a r c h q0 u0 = 0 := by
  let dZ : ExponentBox n K → ℤ := fun x ↦
    c x * a x ^ q0 * ∏ i, r x i ^ u0 i
  let d : ExponentBox n K → ℂ := fun x ↦ (dZ x : ℂ)
  have hd : ∀ x, ‖d x‖ ≤
      ((C * V ^ (q0 + ∑ i, u0 i) : ℕ) : ℝ) := by
    intro x
    have hcR : ‖(c x : ℂ)‖ ≤ (C : ℝ) := by
      rw [Complex.norm_intCast, ← Int.cast_abs, ← Nat.cast_natAbs]
      exact_mod_cast hc x
    dsimp [d, dZ]
    rw [Int.cast_mul, Int.cast_mul, Int.cast_pow, Int.cast_prod,
      norm_mul, norm_mul, norm_pow, Complex.norm_prod]
    simp_rw [Int.cast_pow]
    have hprod : ∏ i, ‖((r x i : ℂ) ^ u0 i)‖ ≤
        (V : ℝ) ^ (∑ i, u0 i) := by
      calc
        ∏ i, ‖((r x i : ℂ) ^ u0 i)‖ =
            ∏ i, ‖(r x i : ℂ)‖ ^ u0 i := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [norm_pow]
        _ ≤ ∏ i, (V : ℝ) ^ u0 i := by
          gcongr with i hi
          simpa [Int.norm_eq_abs] using hrV x i
        _ = (V : ℝ) ^ (∑ i, u0 i) := by
          rw [← Finset.prod_pow_eq_pow_sum]
    calc
      ‖(c x : ℂ)‖ * ‖(a x : ℂ)‖ ^ q0 *
          ∏ i, ‖((r x i : ℂ) ^ u0 i)‖ ≤
        (C : ℝ) * (V : ℝ) ^ q0 *
          (V : ℝ) ^ (∑ i, u0 i) := by
          have haR : ‖(a x : ℂ)‖ ≤ (V : ℝ) := by
            simpa [Int.norm_eq_abs] using haV x
          have hpowA : ‖(a x : ℂ)‖ ^ q0 ≤ (V : ℝ) ^ q0 :=
            pow_le_pow_left₀ (norm_nonneg _) haR q0
          exact mul_le_mul
            (mul_le_mul hcR hpowA (by positivity) (by positivity))
            hprod (by positivity) (by positivity)
      _ = ((C * V ^ (q0 + ∑ i, u0 i) : ℕ) : ℝ) := by
        push_cast
        rw [pow_add]
        ring
  have hdNat : ∀ x, (dZ x).natAbs ≤
      C * V ^ (q0 + ∑ i, u0 i) := by
    intro x
    have hx := hd x
    dsimp [d] at hx
    rw [Complex.norm_intCast, ← Int.cast_abs, ← Nat.cast_natAbs] at hx
    exact_mod_cast hx
  have hmomentC : ∀ node : Fin A, ∀ q, q < T0 → ∀ p, p < S0 →
      ∀ u ∈ Finset.piAntidiag (Finset.univ : Finset iota) p,
        ∑ x, (d x * Complex.exp (L x * (node : ℂ))) *
          (a x : ℂ) ^ q * ∏ i, (r x i : ℂ) ^ u i = 0 := by
    intro node q hq p hp u hu
    have hqsrc : q0 + q < Tsrc := by omega
    let q' : Fin Tsrc := ⟨q0 + q, hqsrc⟩
    have hui : ∀ i, u0 i + u i < Ssrc := by
      intro i
      have hle : u i ≤ p := by
        have hsum := (Finset.mem_piAntidiag.mp hu).1
        rw [← hsum]
        exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le (u j))
          (Finset.mem_univ i)
      have hs := hS i
      omega
    let u' : iota → Fin Ssrc := fun i ↦ ⟨u0 i + u i, hui i⟩
    have hmapped := congrArg φ (hmoment node q' u')
    rw [map_zero, multipointMomentValue_embedding] at hmapped
    calc
      ∑ x, (d x * Complex.exp (L x * (node : ℂ))) *
          (a x : ℂ) ^ q * ∏ i, (r x i : ℂ) ^ u i =
          ∑ x, (c x : ℂ) * φ (boxMonomial alpha x) ^ (node : ℕ) *
            (a x : ℂ) ^ (q0 + q) *
              ∏ i, (r x i : ℂ) ^ (u0 i + u i) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hpow : Complex.exp (L x * (node : ℂ)) =
            φ (boxMonomial alpha x) ^ (node : ℕ) := by
          calc
            Complex.exp (L x * (node : ℂ)) =
                Complex.exp ((node : ℂ) * L x) := by rw [mul_comm]
            _ = Complex.exp (L x) ^ (node : ℕ) := Complex.exp_nat_mul _ _
            _ = φ (boxMonomial alpha x) ^ (node : ℕ) := by rw [hexp]
        rw [hpow]
        dsimp [d, dZ]
        push_cast
        simp_rw [pow_add]
        rw [Finset.prod_mul_distrib]
        ring
      _ = 0 := by simpa [q', u'] using hmapped
  have hanalytic := auxiliaryExponentialSum_norm_le_multipointApproximationBound
    d L b0 Lambda (fun x ↦ (a x : ℂ)) (fun x i ↦ (r x i : ℂ)) ell
    A T0 S0 k hA hk hkS (by positivity) hM hU hb0 hd
    (fun x ↦ by simpa [Int.norm_eq_abs] using haM x) hrM hLambda hL
    hcoord hmomentC hAR (z := (h : ℂ)) (by simpa using hhZ) hZR
  have hanalytic' : ‖auxiliaryExponentialSum L d (h : ℂ)‖ ≤
      multipointApproximationBound (K ^ n) A k T0
        ((C * V ^ (q0 + ∑ i, u0 i) : ℕ) : ℝ) M U R Z ‖Lambda‖ := by
    simpa [ExponentBox] using hanalytic
  have heval : auxiliaryExponentialSum L d (h : ℂ) =
      φ (multipointMomentValue (boxMonomial alpha) a r c h q0 u0) := by
    rw [multipointMomentValue_embedding]
    unfold auxiliaryExponentialSum
    apply Finset.sum_congr rfl
    intro x hx
    have hp : Complex.exp (L x * (h : ℂ)) =
        φ (boxMonomial alpha x) ^ h := by
      calc
        Complex.exp (L x * (h : ℂ)) =
            Complex.exp ((h : ℂ) * L x) := by rw [mul_comm]
        _ = Complex.exp (L x) ^ h := Complex.exp_nat_mul _ _
        _ = φ (boxMonomial alpha x) ^ h := by rw [hexp]
    rw [hp]
    dsimp [d, dZ]
    push_cast
    ring
  have hvalue : multipointMomentValue (boxMonomial alpha) a r c h q0 u0 =
      boxAuxiliaryAlgebraicValue alpha dZ h := by
    unfold multipointMomentValue boxAuxiliaryAlgebraicValue
    apply Finset.sum_congr rfl
    intro x hx
    dsimp [dZ]
    push_cast
    ring
  by_contra hne
  have hneBox : boxAuxiliaryAlgebraicValue alpha dZ h ≠ 0 := by
    rwa [← hvalue]
  have hlocal := boxAuxiliaryAlgebraicValue_projective_log_norm_lower
    φ alpha dZ hK (Nat.mul_pos hC (pow_pos hV _)) hdNat hneBox
  have hlower : Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ n + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (C * V ^ (q0 + ∑ i, u0 i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i)))) ≤
      ‖φ (boxAuxiliaryAlgebraicValue alpha dZ h)‖ := by
    have hnormPos : 0 < ‖φ (boxAuxiliaryAlgebraicValue alpha dZ h)‖ :=
      norm_pos_iff.mpr ((map_ne_zero φ).2 hneBox)
    calc
      _ ≤ Real.exp (Real.log
          ‖φ (boxAuxiliaryAlgebraicValue alpha dZ h)‖) :=
        Real.exp_le_exp.mpr hlocal
      _ = _ := Real.exp_log hnormPos
  rw [← hvalue, ← heval] at hlower
  linarith

/-- Uniform rectangular form of the structured exponent-box approximate
extrapolation step. -/
theorem boxMultipointMoments_extend_of_shifted_approximate_extrapolation
    {F iota : Type*} [Field F] [NumberField F]
    [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) {n K : ℕ} (alpha : Fin n → F)
    (c : ExponentBox n K → ℤ) (L : ExponentBox n K → ℂ)
    (b0 Lambda : ℂ) (a : ExponentBox n K → ℤ)
    (r : ExponentBox n K → iota → ℤ) (ell : iota → ℂ)
    {A Tsrc Ssrc T0 S0 k A' T' S' : ℕ}
    {C V : ℕ} {M U R Z : ℝ}
    (hK : 0 < K) (hA : 0 < A) (hk : 0 < k) (hkS : k ≤ S0)
    (hT : T' + T0 ≤ Tsrc) (hS : S' + S0 ≤ Ssrc)
    (hb0 : 1 ≤ ‖b0‖) (hC : 1 ≤ C) (hV : 1 ≤ V)
    (hM : 1 ≤ M) (hU : 0 ≤ U)
    (hc : ∀ x, (c x).natAbs ≤ C)
    (haV : ∀ x, ‖a x‖ ≤ (V : ℝ))
    (hrV : ∀ x i, ‖r x i‖ ≤ (V : ℝ))
    (haM : ∀ x, ‖a x‖ ≤ M)
    (hrM : ∀ x, ‖∑ i, (r x i : ℂ) * ell i‖ ≤ M)
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (boxMonomial alpha x))
    (hLambda : ‖Lambda‖ ≤ 1)
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin A, ∀ q : Fin Tsrc, ∀ u : iota → Fin Ssrc,
      multipointMomentValue (boxMonomial alpha) a r c node q
        (fun i ↦ u i) = 0)
    (hAR : (A : ℝ) < R) (hA'Z : (A' : ℝ) ≤ Z) (hZR : Z ≤ R)
    (hsmall : ∀ h < A', ∀ q < T', ∀ u : iota → ℕ,
      (∀ i, u i < S') →
      multipointApproximationBound (K ^ n) A k T0
          ((C * V ^ (q + ∑ i, u i) : ℕ) : ℝ) M U R Z ‖Lambda‖ <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ n + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (C * V ^ (q + ∑ i, u i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i))))) :
    ∀ node : Fin A', ∀ q : Fin T', ∀ u : iota → Fin S',
      multipointMomentValue (boxMonomial alpha) a r c node q
        (fun i ↦ u i) = 0 := by
  intro node q u
  apply boxMultipointMomentValue_eq_zero_of_shifted_approximate_extrapolation
    (A := A) (Tsrc := Tsrc) (Ssrc := Ssrc) (T0 := T0) (S0 := S0)
    (k := k) (h := (node : ℕ)) (q0 := (q : ℕ))
    (C := C) (V := V) (M := M) (U := U) (R := R) (Z := Z)
    φ alpha c L b0 Lambda a r ell (fun i ↦ (u i : ℕ))
    hK hA hk hkS
  · omega
  · intro i
    have hui : (u i : ℕ) < S' := (u i).isLt
    omega
  · exact hb0
  · exact hC
  · exact hV
  · exact hM
  · exact hU
  · exact hc
  · exact haV
  · exact hrV
  · exact haM
  · exact hrM
  · exact hL
  · exact hexp
  · exact hLambda
  · exact hcoord
  · exact hmoment
  · exact hAR
  · exact (Nat.cast_le.mpr node.2.le).trans hA'Z
  · exact hZR
  · exact hsmall node node.2 q q.2 (fun i ↦ (u i : ℕ))
      (fun i ↦ (u i).isLt)

/-- The structured exponent-box contradiction: approximate extrapolation
forces all samples below the box cardinality to vanish, while ordinary
Vandermonde nonvanishing supplies one nonzero sample. -/
theorem no_small_box_linear_form_of_multipoint_moments
    {F iota : Type*} [Field F] [NumberField F]
    [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) {n K : ℕ} (alpha : Fin n → F)
    (c : ExponentBox n K → ℤ) (L : ExponentBox n K → ℂ)
    (b0 Lambda : ℂ) (a : ExponentBox n K → ℤ)
    (r : ExponentBox n K → iota → ℤ) (ell : iota → ℂ)
    {A Tsrc Ssrc T0 S0 k : ℕ}
    {C V : ℕ} {M U R Z : ℝ}
    (hK : 0 < K) (hA : 0 < A) (hk : 0 < k) (hkS : k ≤ S0)
    (hT : T0 ≤ Tsrc) (hS : S0 ≤ Ssrc)
    (hb0 : 1 ≤ ‖b0‖) (hC : 1 ≤ C) (hV : 1 ≤ V)
    (hM : 1 ≤ M) (hU : 0 ≤ U)
    (hc0 : c ≠ 0)
    (hinj : Function.Injective
      (fun x : ExponentBox n K ↦ boxMonomial alpha x))
    (hc : ∀ x, (c x).natAbs ≤ C)
    (haV : ∀ x, ‖a x‖ ≤ (V : ℝ))
    (hrV : ∀ x i, ‖r x i‖ ≤ (V : ℝ))
    (haM : ∀ x, ‖a x‖ ≤ M)
    (hrM : ∀ x, ‖∑ i, (r x i : ℂ) * ell i‖ ≤ M)
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (boxMonomial alpha x))
    (hLambda : ‖Lambda‖ ≤ 1)
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin A, ∀ q : Fin Tsrc, ∀ u : iota → Fin Ssrc,
      multipointMomentValue (boxMonomial alpha) a r c node q
        (fun i ↦ u i) = 0)
    (hAR : (A : ℝ) < R) (hcardZ : ((K ^ n : ℕ) : ℝ) ≤ Z)
    (hZR : Z ≤ R)
    (hsmall : ∀ h < K ^ n,
      multipointApproximationBound (K ^ n) A k T0
          (C : ℝ) M U R Z ‖Lambda‖ <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ n + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) * Real.log C +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i))))) :
    False := by
  obtain ⟨t, ht⟩ :=
    exists_boxAuxiliaryAlgebraicValue_ne_zero alpha c hinj hc0
  have hvalueNe :
      multipointMomentValue (boxMonomial alpha) a r c (t : ℕ)
          0 (fun _ ↦ 0) ≠ 0 := by
    simpa [multipointMomentValue, boxAuxiliaryAlgebraicValue] using ht
  have hzero :=
    boxMultipointMomentValue_eq_zero_of_shifted_approximate_extrapolation
      (A := A) (Tsrc := Tsrc) (Ssrc := Ssrc) (T0 := T0) (S0 := S0)
      (k := k) (h := (t : ℕ)) (q0 := 0)
      (C := C) (V := V) (M := M) (U := U) (R := R) (Z := Z)
      φ alpha c L b0 Lambda a r ell (fun _ ↦ 0)
      hK hA hk hkS (by simpa using hT) (fun _ ↦ by simpa using hS)
      hb0 hC hV hM hU hc haV hrV haM hrM hL hexp hLambda hcoord
      hmoment hAR
      (by
        have htK : (t : ℕ) < K ^ n := by
          simpa [ExponentBox] using t.isLt
        exact (Nat.cast_le.mpr htK.le).trans hcardZ) hZR
      (by simpa using hsmall t (by simpa [ExponentBox] using t.isLt))
  exact hvalueNe hzero

/-- Complete logical pipeline from one approximate propagation step through
an arbitrary exact extrapolation schedule.  Once the final node interval
contains the cardinality of the exponent box, Vandermonde nonvanishing
contradicts the propagated moment table. -/
theorem no_small_box_linear_form_of_approximate_then_iterated_moments
    {F iota : Type*} [Field F] [NumberField F]
    [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) {n K : ℕ} (alpha : Fin n → F)
    (c : ExponentBox n K → ℤ) (L : ExponentBox n K → ℂ)
    (b0 Lambda : ℂ) (a : ExponentBox n K → ℤ)
    (r : ExponentBox n K → iota → ℤ) (ell : iota → ℂ)
    {Ainit Tsrc Ssrc Taux Saux kapprox : ℕ}
    (A T S k : ℕ → ℕ) (R Z : ℕ → ℝ) (m : ℕ)
    {C V : ℕ} {M U Rapprox Zapprox : ℝ}
    (hK : 0 < K) (hAinit : 0 < Ainit) (hkapprox : 0 < kapprox)
    (hkapproxS : kapprox ≤ Saux)
    (happroxT : T 0 + Taux ≤ Tsrc)
    (happroxS : S 0 + Saux ≤ Ssrc)
    (hb0one : 1 ≤ ‖b0‖) (hC : 1 ≤ C) (hV : 1 ≤ V)
    (hM : 1 ≤ M) (hU : 0 ≤ U)
    (hc0 : c ≠ 0)
    (hinj : Function.Injective
      (fun x : ExponentBox n K ↦ boxMonomial alpha x))
    (hc : ∀ x, (c x).natAbs ≤ C)
    (haV : ∀ x, ‖a x‖ ≤ (V : ℝ))
    (hrV : ∀ x i, ‖r x i‖ ≤ (V : ℝ))
    (haM : ∀ x, ‖a x‖ ≤ M)
    (hrM : ∀ x, ‖∑ i, (r x i : ℂ) * ell i‖ ≤ M)
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (boxMonomial alpha x))
    (hLambda : ‖Lambda‖ ≤ 1)
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin Ainit, ∀ q : Fin Tsrc,
      ∀ u : iota → Fin Ssrc,
      multipointMomentValue (boxMonomial alpha) a r c node q
        (fun i ↦ u i) = 0)
    (happroxAR : (Ainit : ℝ) < Rapprox)
    (happroxA'Z : (A 0 : ℝ) ≤ Zapprox)
    (happroxZR : Zapprox ≤ Rapprox)
    (happroxSmall : ∀ h < A 0, ∀ q < T 0, ∀ u : iota → ℕ,
      (∀ i, u i < S 0) →
      multipointApproximationBound (K ^ n) Ainit kapprox Taux
          ((C * V ^ (q + ∑ i, u i) : ℕ) : ℝ)
          M U Rapprox Zapprox ‖Lambda‖ <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ n + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (C * V ^ (q + ∑ i, u i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i)))))
    (hstepT : ∀ j, T (j + 1) + k j ≤ T j)
    (hstepS : ∀ j, S (j + 1) + k j ≤ S j)
    (hstepAR : ∀ j, (A j : ℝ) < R j)
    (hstepA'Z : ∀ j, (A (j + 1) : ℝ) ≤ Z j)
    (hstepZR : ∀ j, Z j ≤ R j)
    (hstepSmall : ∀ j, ∀ h < A (j + 1), ∀ q < T (j + 1),
      ∀ u : iota → ℕ, (∀ i, u i < S (j + 1)) →
      (Z j + A j) ^ (k j * A j) *
          (((K ^ n : ℕ) : ℝ) *
              (((C * V ^ (q + ∑ i, u i) : ℕ) : ℝ)) *
              Real.exp (U * R j) /
            (R j - A j) ^ (k j * A j)) <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (K ^ n + 1 : ℕ) +
            (Module.finrank ℚ F : ℝ) *
              Real.log (C * V ^ (q + ∑ i, u i) : ℕ) +
            (h : ℝ) * ((K : ℝ) *
              ∑ i, Height.logHeight₁ (alpha i)))))
    (hfinalA : K ^ n ≤ A m) (hfinalT : 0 < T m)
    (hfinalS : 0 < S m) : False := by
  have hmoment0 :=
    boxMultipointMoments_extend_of_shifted_approximate_extrapolation
      (A := Ainit) (Tsrc := Tsrc) (Ssrc := Ssrc)
      (T0 := Taux) (S0 := Saux) (k := kapprox)
      (A' := A 0) (T' := T 0) (S' := S 0)
      (C := C) (V := V) (M := M) (U := U)
      (R := Rapprox) (Z := Zapprox)
      φ alpha c L b0 Lambda a r ell hK hAinit hkapprox hkapproxS
      happroxT happroxS hb0one hC hV hM hU hc haV hrV haM hrM
      hL hexp hLambda hcoord hmoment happroxAR happroxA'Z happroxZR
      happroxSmall
  have hb0 : b0 ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hb0one)
  have hfinal := boxMultipointMoments_iterate_extrapolation
    φ alpha c L b0 Lambda a r ell A T S k R Z m hK
    hb0 hC hV hU hc haV hrV hL hexp hcoord hmoment0 hstepT hstepS
    hstepAR hstepA'Z hstepZR hstepSmall
  obtain ⟨t, ht⟩ :=
    exists_boxAuxiliaryAlgebraicValue_ne_zero alpha c hinj hc0
  have htN : (t : ℕ) < K ^ n := by
    simpa [ExponentBox] using t.isLt
  let node : Fin (A m) := ⟨t, htN.trans_le hfinalA⟩
  let q : Fin (T m) := ⟨0, hfinalT⟩
  let u : iota → Fin (S m) := fun _ ↦ ⟨0, hfinalS⟩
  have hz := hfinal node q u
  apply ht
  simpa [node, q, u, multipointMomentValue,
    boxAuxiliaryAlgebraicValue] using hz

/-- Uniform rectangular form of one approximate extrapolation step. -/
theorem multipointMoments_extend_of_shifted_approximate_extrapolation
    {F kappa iota : Type*} [Field F] [NumberField F]
    [Fintype kappa] [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) (beta : kappa → F)
    (c : kappa → ℤ) (L : kappa → ℂ) (b0 Lambda : ℂ)
    (a : kappa → ℤ) (r : kappa → iota → ℤ) (ell : iota → ℂ)
    {A Tsrc Ssrc T0 S0 k A' T' S' : ℕ} {C H V M U R Z : ℝ}
    (hA : 0 < A) (hk : 0 < k) (hkS : k ≤ S0)
    (hT : T' + T0 ≤ Tsrc) (hS : S' + S0 ≤ Ssrc)
    (hb0 : 1 ≤ ‖b0‖) (hC : 1 ≤ C) (hV : 1 ≤ V)
    (hM : 1 ≤ M) (hU : 0 ≤ U)
    (hc : ∀ x, (c x).natAbs ≤ C)
    (hbeta : ∀ x, Height.logHeight₁ (beta x) ≤ H)
    (haV : ∀ x, ‖a x‖ ≤ V) (hrV : ∀ x i, ‖r x i‖ ≤ V)
    (haM : ∀ x, ‖a x‖ ≤ M)
    (hrM : ∀ x, ‖∑ i, (r x i : ℂ) * ell i‖ ≤ M)
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (beta x))
    (hLambda : ‖Lambda‖ ≤ 1)
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin A, ∀ q : Fin Tsrc, ∀ u : iota → Fin Ssrc,
      multipointMomentValue beta a r c node q (fun i ↦ u i) = 0)
    (hAR : (A : ℝ) < R) (hA'Z : (A' : ℝ) ≤ Z) (hZR : Z ≤ R)
    (hsmall : ∀ h < A', ∀ q < T', ∀ u : iota → ℕ,
      (∀ i, u i < S') →
      multipointApproximationBound (Fintype.card kappa) A k T0
          (C * V ^ (q + ∑ i, u i)) M U R Z ‖Lambda‖ <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
              Real.log (Fintype.card kappa : ℝ) +
            (Fintype.card kappa : ℝ) *
              ((Module.finrank ℚ F : ℝ) * Real.log C +
                (h : ℝ) * H +
                ((q + ∑ i, u i : ℕ) : ℝ) *
                  ((Module.finrank ℚ F : ℝ) * Real.log V))))) :
    ∀ node : Fin A', ∀ q : Fin T', ∀ u : iota → Fin S',
      multipointMomentValue beta a r c node q (fun i ↦ u i) = 0 := by
  intro node q u
  apply multipointMomentValue_eq_zero_of_shifted_approximate_extrapolation
    (A := A) (Tsrc := Tsrc) (Ssrc := Ssrc) (T0 := T0) (S0 := S0)
    (k := k) (h := (node : ℕ)) (q0 := (q : ℕ))
    (C := C) (H := H) (V := V) (M := M) (U := U) (R := R) (Z := Z)
    φ beta c L b0 Lambda a r ell (fun i ↦ (u i : ℕ))
    hA hk hkS
  · omega
  · intro i
    have hui : (u i : ℕ) < S' := (u i).isLt
    omega
  · exact hb0
  · exact hC
  · exact hV
  · exact hM
  · exact hU
  · exact hc
  · exact hbeta
  · exact haV
  · exact hrV
  · exact haM
  · exact hrM
  · exact hL
  · exact hexp
  · exact hLambda
  · exact hcoord
  · exact hmoment
  · exact hAR
  · exact (Nat.cast_le.mpr node.2.le).trans hA'Z
  · exact hZR
  · exact hsmall node node.2 q q.2 (fun i ↦ (u i : ℕ))
      (fun i ↦ (u i).isLt)

theorem no_small_linear_form_of_multipoint_moments
    {F kappa iota : Type*} [Field F] [NumberField F]
    [Fintype kappa] [DecidableEq kappa] [Fintype iota] [DecidableEq iota]
    (φ : F →+* ℂ) (beta : kappa → F)
    (c : kappa → ℤ) (L : kappa → ℂ) (b0 Lambda : ℂ)
    (a : kappa → ℤ) (r : kappa → iota → ℤ) (ell : iota → ℂ)
    {A T S k : ℕ} {C H V M U R Z : ℝ}
    (hA : 0 < A) (hk : 0 < k) (hkS : k ≤ S)
    (hb0 : 1 ≤ ‖b0‖) (hC : 1 ≤ C) (hV : 1 ≤ V)
    (hM : 1 ≤ M) (hU : 0 ≤ U)
    (hc0 : c ≠ 0) (hbetaInj : Function.Injective beta)
    (hc : ∀ x, (c x).natAbs ≤ C)
    (hbeta : ∀ x, Height.logHeight₁ (beta x) ≤ H)
    (haV : ∀ x, ‖a x‖ ≤ V) (hrV : ∀ x i, ‖r x i‖ ≤ V)
    (haM : ∀ x, ‖a x‖ ≤ M)
    (hrM : ∀ x, ‖∑ i, (r x i : ℂ) * ell i‖ ≤ M)
    (hL : ∀ x, ‖L x‖ ≤ U)
    (hexp : ∀ x, Complex.exp (L x) = φ (beta x))
    (hLambda : ‖Lambda‖ ≤ 1)
    (hcoord : ∀ x, b0 * L x = (a x : ℂ) * Lambda +
      ∑ i, (r x i : ℂ) * ell i)
    (hmoment : ∀ node : Fin A, ∀ q : Fin T, ∀ u : iota → Fin S,
      multipointMomentValue beta a r c node q (fun i ↦ u i) = 0)
    (hAR : (A : ℝ) < R)
    (hcardZ : (Fintype.card kappa : ℝ) ≤ Z) (hZR : Z ≤ R)
    (hsmall : ∀ h < Fintype.card kappa,
      multipointApproximationBound (Fintype.card kappa) A k T
          C M U R Z ‖Lambda‖ <
        Real.exp (-((Module.finrank ℚ F : ℝ) *
            Real.log (Fintype.card kappa : ℝ) +
          (Fintype.card kappa : ℝ) *
            ((Module.finrank ℚ F : ℝ) * Real.log C + (h : ℝ) * H)))) :
    False := by
  have hcF : (fun x ↦ (c x : F)) ≠ 0 := by
    intro hz
    apply hc0
    funext x
    have hx := congrFun hz x
    apply (Int.cast_eq_zero (α := F)).mp
    simpa using hx
  obtain ⟨t, ht⟩ := exists_finite_exponentialSum_ne_zero
    beta (fun x ↦ (c x : F)) hbetaInj hcF
  have hvalueNe :
      multipointMomentValue beta a r c (t : ℕ) 0 (fun _ ↦ 0) ≠ 0 := by
    simpa [multipointMomentValue] using ht
  have hzero := multipointMomentValue_eq_zero_of_approximate_extrapolation
    φ beta c L b0 Lambda a r ell hA hk hkS hb0 hC hV hM hU
    hc hbeta haV hrV haM hrM hL hexp hLambda hcoord hmoment hAR
    (h := (t : ℕ))
    (by exact (Nat.cast_le.mpr t.isLt.le).trans hcardZ) hZR
    (hsmall t t.isLt)
  exact hvalueNe hzero

end

end Erdos841.LinearForms
