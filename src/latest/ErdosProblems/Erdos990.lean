import Mathlib

open BigOperators Polynomial

namespace Erdos990

/-- `θ` is an argument of `z`.

This is deliberately not `Complex.arg z = θ`, since `Complex.arg` uses a fixed branch; the
problem statement allows arguments chosen in `[0, 2π]`. -/
def IsArgument (z : ℂ) (θ : ℝ) : Prop :=
  z = (‖z‖ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

/-- The standard argument, moved into the interval `[0, 2π]`. -/
noncomputable def argumentRepresentative (z : ℂ) : ℝ :=
  if Complex.arg z < 0 then Complex.arg z + 2 * Real.pi else Complex.arg z

/-- The representative argument really is an argument. -/
theorem isArgument_argumentRepresentative (z : ℂ) :
    IsArgument z (argumentRepresentative z) := by
  rw [IsArgument, argumentRepresentative]
  by_cases harg : Complex.arg z < 0
  · rw [if_pos harg]
    have hexp :
        Complex.exp (((Complex.arg z + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
          Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by
      rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨1, ?_⟩
      norm_num [sub_eq_add_neg]
      ring
    rw [hexp]
    exact (Complex.norm_mul_exp_arg_mul_I z).symm
  · rw [if_neg harg]
    exact (Complex.norm_mul_exp_arg_mul_I z).symm

/-- The representative argument lies in the problem's interval. -/
theorem argumentRepresentative_mem_Ico (z : ℂ) :
    argumentRepresentative z ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
  have harg_lower := Complex.neg_pi_lt_arg z
  have harg_upper := Complex.arg_le_pi z
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  rw [argumentRepresentative]
  by_cases harg : Complex.arg z < 0
  · rw [if_pos harg]
    constructor <;> linarith
  · rw [if_neg harg]
    constructor <;> linarith

/-- A positive real uses the representative argument `0`. -/
theorem argumentRepresentative_ofReal_pos {x : ℝ} (hx : 0 < x) :
    argumentRepresentative (x : ℂ) = 0 := by
  rw [argumentRepresentative, Complex.arg_ofReal_of_nonneg hx.le]
  simp

/-- The number `n` of non-zero coefficients among `a₀, ..., a_d`. -/
noncomputable def coeffSupportCardUpTo (f : Polynomial ℂ) (d : ℕ) : ℕ :=
  ((Finset.range (d + 1)).filter fun k => f.coeff k ≠ 0).card

/-- The coefficient ratio
`(|a₀| + ... + |a_d|) / (|a₀| |a_d|)^{1/2}` appearing in the conjecture. -/
noncomputable def coefficientRatio (f : Polynomial ℂ) (d : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (d + 1), ‖f.coeff k‖) /
    Real.sqrt (‖f.coeff 0‖ * ‖f.coeff d‖)

/-- If the endpoint coefficients are nonzero, the coefficient ratio is positive. -/
theorem coefficientRatio_pos_of_endpoint_ne_zero {f : Polynomial ℂ} {d : ℕ}
    (h0 : f.coeff 0 ≠ 0) (hd : f.coeff d ≠ 0) :
    0 < coefficientRatio f d := by
  unfold coefficientRatio
  refine div_pos ?_ ?_
  · refine lt_of_lt_of_le (norm_pos_iff.mpr h0) ?_
    refine Finset.single_le_sum
      (s := Finset.range (d + 1)) (f := fun k : ℕ => ‖f.coeff k‖) ?_ ?_
    · intro k _hk
      exact norm_nonneg _
    · simp
  · refine Real.sqrt_pos.mpr ?_
    exact mul_pos (norm_pos_iff.mpr h0) (norm_pos_iff.mpr hd)

/-- The number of listed root-arguments lying in the closed interval `[α, β]`. -/
noncomputable def argumentCount {d : ℕ} (θ : Fin d → ℝ) (α β : ℝ) : ℕ :=
  (Finset.univ.filter fun i => α ≤ θ i ∧ θ i ≤ β).card

/-- A polynomial together with the data used in the problem statement.

The factorisation hypothesis lists all roots with multiplicity. -/
def HasRootsWithArguments (f : Polynomial ℂ) (d : ℕ) (z : Fin d → ℂ)
    (θ : Fin d → ℝ) : Prop :=
  f.natDegree = d ∧
    f.coeff d ≠ 0 ∧
    f.coeff 0 ≠ 0 ∧
    f = Polynomial.C (f.coeff d) * ∏ i : Fin d, (Polynomial.X - Polynomial.C (z i)) ∧
    ∀ i : Fin d, IsArgument (z i) (θ i) ∧ θ i ∈ Set.Ico (0 : ℝ) (2 * Real.pi)

/-- The proposed sparse Erdős--Turán estimate, with the Vinogradov symbol `≪`
formalized as an absolute constant.

For every complex degree-`d` polynomial with `n` non-zero coefficients and coefficient ratio
`M`, the angular discrepancy of its roots on any interval in `[0, 2π]` is bounded by
`C * sqrt (n * log M)`. -/
def SparseErdosTuranEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (d : ℕ) (f : Polynomial ℂ) (z : Fin d → ℂ) (θ : Fin d → ℝ),
      HasRootsWithArguments f d z θ →
        ∀ α β : ℝ,
          0 ≤ α → α ≤ β → β ≤ 2 * Real.pi →
            |(argumentCount θ α β : ℝ) - ((β - α) / (2 * Real.pi)) * d| ≤
              C * Real.sqrt
                ((coeffSupportCardUpTo f d : ℝ) * Real.log (coefficientRatio f d))

/-! ## The counterexample from `Erdos990.tex` -/

/-- The exponent sequence `0, 1, K, ..., K ^ N`. -/
def counterexampleExponent (N K : ℕ) (j : Fin (N + 2)) : ℕ :=
  if j.val = 0 then 0 else K ^ (j.val - 1)

/-- The degree `d = K ^ N` of the lacunary counterexample. -/
def counterexampleDegree (N K : ℕ) : ℕ :=
  K ^ N

/-- The normalized exponents `λ_j = m_j / d`. -/
noncomputable def counterexampleLambda (N K : ℕ) (j : Fin (N + 2)) : ℝ :=
  (counterexampleExponent N K j : ℝ) / (counterexampleDegree N K : ℝ)

/-- The Vandermonde denominator `Δ_j = ∏_{ℓ ≠ j} |λ_j - λ_ℓ|`. -/
noncomputable def counterexampleDelta (N K : ℕ) (j : Fin (N + 2)) : ℝ :=
  ∏ l : Fin (N + 2), if l = j then 1 else |counterexampleLambda N K j -
    counterexampleLambda N K l|

/-- The quantity called `A_1` in the tex solution. -/
noncomputable def counterexampleA₁ (N K : ℕ) : ℝ :=
  Real.sqrt
    (counterexampleDelta N K (Fin.last (N + 1)) / counterexampleDelta N K ⟨0, by omega⟩)

/-- The tilt `T = 1 / (sqrt 2 * A_1)`. -/
noncomputable def counterexampleTilt (N K : ℕ) : ℝ :=
  1 / (Real.sqrt 2 * counterexampleA₁ N K)

/-- The point `τ = 2 log T` where the exponential polynomial has its high-order zero. -/
noncomputable def counterexampleTau (N K : ℕ) : ℝ :=
  2 * Real.log (counterexampleTilt N K)

/-- The coefficient
`c_j = (-1)^(s-j) exp (-λ_j τ) / Δ_j`, indexed from `j = 0`.

This is real-valued; it is cast to `ℂ` when building the algebraic polynomial. -/
noncomputable def counterexampleRealCoeff (N K : ℕ) (j : Fin (N + 2)) : ℝ :=
  (-1 : ℝ) ^ (N + 1 - j.val) *
    Real.exp (-(counterexampleLambda N K j * counterexampleTau N K)) /
      counterexampleDelta N K j

/-- The lacunary algebraic polynomial `f_{N,K}` from the tex solution. -/
noncomputable def counterexamplePolynomial (N K : ℕ) : Polynomial ℂ :=
  ∑ j : Fin (N + 2),
    Polynomial.C ((counterexampleRealCoeff N K j : ℂ)) *
      Polynomial.X ^ counterexampleExponent N K j

/-- The positive real root obtained from the high-order zero of the exponential polynomial. -/
noncomputable def counterexamplePositiveRoot (N K : ℕ) : ℝ :=
  Real.exp (counterexampleTau N K / counterexampleDegree N K)

/-- The Lagrange-coefficient identity for an arbitrary polynomial of degree smaller than the
number of interpolation nodes. -/
theorem lagrange_top_coeff_sum {s : ℕ} (α : Fin s → ℝ) (hα : StrictMono α)
    (P : Polynomial ℝ) (hdegree : P.degree < (s : WithBot ℕ)) :
    (∑ j : Fin s, P.eval (α j) / ∏ l ∈ (Finset.univ.erase j), (α j - α l)) =
      P.coeff (s - 1) := by
  have hvs : Set.InjOn α (Finset.univ : Finset (Fin s)) := hα.injective.injOn
  have hdegree' :
      P.degree < (Finset.univ : Finset (Fin s)).card := by
    simpa [Finset.card_univ, Fintype.card_fin, Nat.cast_withBot] using hdegree
  have hcoeff := Lagrange.coeff_eq_sum
    (s := (Finset.univ : Finset (Fin s))) (v := α) hvs (P := P) hdegree'
  rw [Finset.card_univ, Fintype.card_fin] at hcoeff
  simpa [eq_comm] using hcoeff.symm

/-- For an increasing list of interpolation nodes, the signed Lagrange denominator is
`(-1)^(number of nodes to the right)` times the product of the absolute distances. -/
theorem lagrange_denominator_eq_signed_abs_product {s : ℕ} (α : Fin s → ℝ)
    (hα : StrictMono α) (j : Fin s) :
    (∏ l ∈ (Finset.univ.erase j), (α j - α l)) =
      (-1 : ℝ) ^ (s - 1 - j.val) * ∏ l ∈ (Finset.univ.erase j), |α j - α l| := by
  rw [show (Finset.univ.erase j : Finset (Fin s)) = Finset.Iio j ∪ Finset.Ioi j by
    ext l
    simp]
  rw [Finset.prod_union (by simpa [disjoint_comm] using Finset.disjoint_Ioi_Iio j)]
  rw [Finset.prod_union (by simpa [disjoint_comm] using Finset.disjoint_Ioi_Iio j)]
  rw [show ∏ x ∈ Finset.Iio j, (α j - α x) =
      ∏ x ∈ Finset.Iio j, |α j - α x| by
    refine Finset.prod_congr rfl ?_
    intro x hx
    rw [abs_of_pos]
    exact sub_pos.mpr (hα (by simpa using hx))]
  rw [show ∏ x ∈ Finset.Ioi j, (α j - α x) =
      (-1 : ℝ) ^ (Finset.Ioi j).card * ∏ x ∈ Finset.Ioi j, |α j - α x| by
    rw [← Finset.prod_neg]
    refine Finset.prod_congr rfl ?_
    intro x hx
    rw [abs_of_neg]
    · ring
    · exact sub_neg.mpr (hα (by simpa using hx))]
  rw [Fin.card_Ioi]
  ring

/-- The point `x₀ = exp (τ / d)` from the tex proof is positive. -/
theorem counterexamplePositiveRoot_pos (N K : ℕ) :
    0 < counterexamplePositiveRoot N K := by
  rw [counterexamplePositiveRoot]
  positivity

/-- The `k`th Taylor coefficient of the algebraic counterexample at `x₀`, expanded directly
from the lacunary definition. -/
theorem counterexamplePolynomial_taylor_coeff_positiveRoot (N K k : ℕ) :
    (((counterexamplePolynomial N K).comp
      (Polynomial.X + Polynomial.C (counterexamplePositiveRoot N K : ℂ))).coeff k) =
      ∑ j : Fin (N + 2),
        (counterexampleRealCoeff N K j : ℂ) *
          (counterexamplePositiveRoot N K : ℂ) ^ (counterexampleExponent N K j - k) *
            ((counterexampleExponent N K j).choose k : ℂ) := by
  unfold counterexamplePolynomial
  rw [Polynomial.sum_comp]
  rw [Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [Polynomial.mul_comp, Polynomial.X_pow_comp, Polynomial.C_comp]
  rw [Polynomial.coeff_C_mul]
  rw [Polynomial.coeff_X_add_C_pow]
  ring

/-- The first exponent in the lacunary support is `0`. -/
theorem counterexampleExponent_zero (N K : ℕ) :
    counterexampleExponent N K ⟨0, by omega⟩ = 0 := by
  simp [counterexampleExponent]

/-- The last exponent in the lacunary support is the degree `d = K ^ N`. -/
theorem counterexampleExponent_last (N K : ℕ) :
    counterexampleExponent N K (Fin.last (N + 1)) = counterexampleDegree N K := by
  simp [counterexampleExponent, counterexampleDegree, Fin.val_last]

/-- The first normalized exponent is `0`. -/
theorem counterexampleLambda_zero (N K : ℕ) :
    counterexampleLambda N K ⟨0, by omega⟩ = 0 := by
  simp [counterexampleLambda, counterexampleExponent]

/-- The last normalized exponent is `1`, under the construction's hypothesis `K ≥ 1`. -/
theorem counterexampleLambda_last (N K : ℕ) (hK : 0 < K) :
    counterexampleLambda N K (Fin.last (N + 1)) = 1 := by
  rw [counterexampleLambda, counterexampleExponent_last, counterexampleDegree]
  rw [div_self]
  exact_mod_cast pow_ne_zero N (Nat.ne_of_gt hK)

/-- The lacunary exponent list has no repetitions. -/
theorem counterexampleExponent_injective (N K : ℕ) (hK : 2 ≤ K) :
    Function.Injective (counterexampleExponent N K) := by
  intro i j hij
  unfold counterexampleExponent at hij
  split_ifs at hij with hi hj
  · exact Fin.ext (by omega)
  · have hpow_pos : 0 < K ^ (j.val - 1) := Nat.pow_pos (by omega)
    omega
  · have hpow_pos : 0 < K ^ (i.val - 1) := Nat.pow_pos (by omega)
    omega
  · have hsub : i.val - 1 = j.val - 1 := Nat.pow_right_injective hK hij
    exact Fin.ext (by omega)

/-- The lacunary exponent list is strictly increasing. -/
theorem counterexampleExponent_strictMono (N K : ℕ) (hK : 2 ≤ K) :
    StrictMono (counterexampleExponent N K) := by
  intro i j hij
  unfold counterexampleExponent
  split_ifs with hi hj
  · omega
  · exact Nat.pow_pos (by omega)
  · omega
  · have hsub : i.val - 1 < j.val - 1 := by omega
    exact Nat.pow_lt_pow_right (by omega) hsub

/-- The normalized exponent list has no repetitions. -/
theorem counterexampleLambda_injective (N K : ℕ) (hK : 2 ≤ K) :
    Function.Injective (counterexampleLambda N K) := by
  intro i j hij
  rw [counterexampleLambda, counterexampleLambda] at hij
  have hdeg : (counterexampleDegree N K : ℝ) ≠ 0 := by
    unfold counterexampleDegree
    exact_mod_cast (pow_ne_zero N (ne_of_gt (lt_of_lt_of_le (by norm_num) hK)))
  have hm :
      (counterexampleExponent N K i : ℝ) =
        (counterexampleExponent N K j : ℝ) := by
    have hm := congr_arg (fun x : ℝ => x * (counterexampleDegree N K : ℝ)) hij
    field_simp [hdeg] at hm
    exact hm
  exact counterexampleExponent_injective N K hK (Nat.cast_injective hm)

/-- The normalized exponent list is strictly increasing. -/
theorem counterexampleLambda_strictMono (N K : ℕ) (hK : 2 ≤ K) :
    StrictMono (counterexampleLambda N K) := by
  intro i j hij
  rw [counterexampleLambda, counterexampleLambda]
  have hdeg_pos : 0 < (counterexampleDegree N K : ℝ) := by
    unfold counterexampleDegree
    positivity
  have hm_nat :
      counterexampleExponent N K i < counterexampleExponent N K j :=
    counterexampleExponent_strictMono N K hK hij
  have hm_real :
      (counterexampleExponent N K i : ℝ) < (counterexampleExponent N K j : ℝ) := by
    exact_mod_cast hm_nat
  exact div_lt_div_of_pos_right hm_real hdeg_pos

/-- The positive Vandermonde denominator can be written as the product over all other indices. -/
theorem counterexampleDelta_eq_prod_erase (N K : ℕ) (j : Fin (N + 2)) :
    counterexampleDelta N K j =
      ∏ l ∈ (Finset.univ.erase j),
        |counterexampleLambda N K j - counterexampleLambda N K l| := by
  unfold counterexampleDelta
  rw [← Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin (N + 2))))
    (f := fun l => if l = j then 1 else |counterexampleLambda N K j -
      counterexampleLambda N K l|) (a := j) (Finset.mem_univ j)]
  simp only [↓reduceIte, one_mul]
  refine Finset.prod_congr rfl ?_
  intro l hl
  rw [if_neg]
  exact (Finset.mem_erase.mp hl).1

/-- The Vandermonde denominator for the counterexample support is nonzero. -/
theorem counterexampleDelta_ne_zero (N K : ℕ) (hK : 2 ≤ K) (j : Fin (N + 2)) :
    counterexampleDelta N K j ≠ 0 := by
  unfold counterexampleDelta
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro l _hl
  split_ifs with hlj
  · exact one_ne_zero
  · have hneq :
        counterexampleLambda N K j ≠ counterexampleLambda N K l := by
      intro hlambda
      exact hlj ((counterexampleLambda_injective N K hK hlambda).symm)
    exact abs_ne_zero.mpr (sub_ne_zero.mpr hneq)

/-- The positive Vandermonde denominators are strictly positive. -/
theorem counterexampleDelta_pos (N K : ℕ) (hK : 2 ≤ K) (j : Fin (N + 2)) :
    0 < counterexampleDelta N K j := by
  unfold counterexampleDelta
  refine Finset.prod_pos ?_
  intro l _hl
  split_ifs with hlj
  · positivity
  · rw [abs_pos]
    exact sub_ne_zero.mpr (by
      intro h
      exact hlj ((counterexampleLambda_injective N K hK h).symm))

/-- Lagrange's top-coefficient functional in the signed/positive-denominator normalization used
by the counterexample coefficients. -/
theorem counterexample_signed_lagrange_top_coeff_sum
    (N K : ℕ) (hK : 2 ≤ K) (P : Polynomial ℝ)
    (hdegree : P.degree < ((N + 2 : ℕ) : WithBot ℕ)) :
    (∑ j : Fin (N + 2),
        (-1 : ℝ) ^ (N + 1 - j.val) * P.eval (counterexampleLambda N K j) /
          counterexampleDelta N K j) =
      P.coeff (N + 1) := by
  have hordinary := lagrange_top_coeff_sum (counterexampleLambda N K)
    (counterexampleLambda_strictMono N K hK) P hdegree
  have hsub : N + 2 - 1 = N + 1 := by omega
  rw [hsub] at hordinary
  rw [← hordinary]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [counterexampleDelta_eq_prod_erase]
  rw [lagrange_denominator_eq_signed_abs_product (counterexampleLambda N K)
    (counterexampleLambda_strictMono N K hK) j]
  let A : ℝ := P.eval (counterexampleLambda N K j)
  let B : ℝ :=
    ∏ l ∈ Finset.univ.erase j, |counterexampleLambda N K j - counterexampleLambda N K l|
  let S : ℝ := (-1) ^ (N + 1 - j.val)
  have hS : S ≠ 0 := by
    exact pow_ne_zero _ (by norm_num)
  have hB : B ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro l hl
    have hneq :
        counterexampleLambda N K j ≠ counterexampleLambda N K l := by
      intro h
      have hlj := (counterexampleLambda_injective N K hK h)
      exact (Finset.mem_erase.mp hl).1 hlj.symm
    exact abs_ne_zero.mpr (sub_ne_zero.mpr hneq)
  change S * A / B = A / (S * B)
  field_simp [hS, hB]
  have hS_sq : S ^ 2 = 1 := by
    dsimp [S]
    rw [← pow_mul]
    norm_num
  rw [hS_sq, one_mul]

/-- The polynomial in the normalized exponent `λ` whose value is
`choose (d * λ) k` at the counterexample nodes. -/
noncomputable def scaledChoosePolynomial (d k : ℕ) : Polynomial ℝ :=
  Polynomial.C (((Nat.factorial k : ℕ) : ℝ)⁻¹) *
    (descPochhammer ℝ k).comp (Polynomial.C (d : ℝ) * Polynomial.X)

/-- Evaluating `scaledChoosePolynomial` at an exponent divided by `d` recovers the binomial
coefficient. -/
theorem scaledChoosePolynomial_eval_div (d m k : ℕ) (hd : d ≠ 0) :
    (scaledChoosePolynomial d k).eval ((m : ℝ) / (d : ℝ)) =
      (m.choose k : ℝ) := by
  unfold scaledChoosePolynomial
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  have hd_real : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  rw [mul_div_cancel₀ _ hd_real]
  rw [Nat.cast_choose_eq_descPochhammer_div]
  rw [div_eq_mul_inv]
  ring

/-- The scaled choose polynomial takes the expected values on the normalized counterexample
support. -/
theorem scaledChoosePolynomial_eval_counterexampleLambda
    (N K k : ℕ) (hK : 2 ≤ K) (j : Fin (N + 2)) :
    (scaledChoosePolynomial (counterexampleDegree N K) k).eval
        (counterexampleLambda N K j) =
      ((counterexampleExponent N K j).choose k : ℝ) := by
  rw [counterexampleLambda]
  exact scaledChoosePolynomial_eval_div (counterexampleDegree N K)
    (counterexampleExponent N K j) k (by
      unfold counterexampleDegree
      exact pow_ne_zero N (ne_of_gt (by omega)))

/-- The scaled choose polynomial has degree at most the lower index. -/
theorem scaledChoosePolynomial_natDegree_le (d k : ℕ) :
    (scaledChoosePolynomial d k).natDegree ≤ k := by
  unfold scaledChoosePolynomial
  refine Polynomial.natDegree_mul_le.trans ?_
  have hcomp :
      ((descPochhammer ℝ k).comp (Polynomial.C (d : ℝ) * Polynomial.X)).natDegree ≤ k := by
    calc
      ((descPochhammer ℝ k).comp (Polynomial.C (d : ℝ) * Polynomial.X)).natDegree ≤
          (descPochhammer ℝ k).natDegree *
            (Polynomial.C (d : ℝ) * Polynomial.X).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ k * 1 := by
        rw [descPochhammer_natDegree]
        exact Nat.mul_le_mul_left k (by
          simpa using Polynomial.natDegree_C_mul_X_pow_le (d : ℝ) 1)
      _ = k := by simp
  have hconstant :
      (Polynomial.C (((Nat.factorial k : ℕ) : ℝ)⁻¹)).natDegree ≤ 0 := by
    rw [Polynomial.natDegree_C]
  nlinarith

/-- The top coefficient of the scaled choose polynomial. -/
theorem scaledChoosePolynomial_coeff_self (d k : ℕ) :
    (scaledChoosePolynomial d k).coeff k =
      (d : ℝ) ^ k / (Nat.factorial k : ℝ) := by
  unfold scaledChoosePolynomial
  rw [Polynomial.coeff_C_mul]
  rw [Polynomial.comp_C_mul_X_coeff]
  rw [show (descPochhammer ℝ k).coeff k = 1 by
    simpa [Polynomial.leadingCoeff, descPochhammer_natDegree] using
      (monic_descPochhammer ℝ k).leadingCoeff]
  rw [one_mul]
  ring

/-- The signed Vandermonde functional applied to binomial coefficients of the lacunary exponents. -/
theorem counterexample_signed_choose_sum_eq_scaledChoose_coeff
    (N K k : ℕ) (hK : 2 ≤ K) (hk : k ≤ N + 1) :
    (∑ j : Fin (N + 2),
        (-1 : ℝ) ^ (N + 1 - j.val) *
          ((counterexampleExponent N K j).choose k : ℝ) /
            counterexampleDelta N K j) =
      (scaledChoosePolynomial (counterexampleDegree N K) k).coeff (N + 1) := by
  have hdegree :
      (scaledChoosePolynomial (counterexampleDegree N K) k).degree <
        ((N + 2 : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    exact WithBot.coe_lt_coe.mpr ((scaledChoosePolynomial_natDegree_le
      (counterexampleDegree N K) k).trans_lt (show k < N + 2 by omega))
  have hlagrange := counterexample_signed_lagrange_top_coeff_sum N K hK
    (scaledChoosePolynomial (counterexampleDegree N K) k) hdegree
  rw [← hlagrange]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [scaledChoosePolynomial_eval_counterexampleLambda N K k hK j]

/-- After Taylor-expanding at `x₀ = exp (τ / d)`, the `k`th coefficient is a nonzero
common exponential factor times the signed Vandermonde functional applied to `m ↦ choose m k`. -/
theorem counterexamplePolynomial_taylor_coeff_eq_signed_choose_sum
    (N K k : ℕ) (hK : 2 ≤ K) :
    (((counterexamplePolynomial N K).comp
      (Polynomial.X + Polynomial.C (counterexamplePositiveRoot N K : ℂ))).coeff k) =
      (Real.exp (-(k : ℝ) * counterexampleTau N K / (counterexampleDegree N K : ℝ)) : ℂ) *
        ((∑ j : Fin (N + 2),
            (-1 : ℝ) ^ (N + 1 - j.val) *
              ((counterexampleExponent N K j).choose k : ℝ) /
                counterexampleDelta N K j) : ℂ) := by
  rw [counterexamplePolynomial_taylor_coeff_positiveRoot]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases hmk : counterexampleExponent N K j < k
  · rw [Nat.choose_eq_zero_of_lt hmk]
    norm_num
  · have hkm : k ≤ counterexampleExponent N K j := Nat.le_of_not_gt hmk
    have hdeg_real : (counterexampleDegree N K : ℝ) ≠ 0 := by
      unfold counterexampleDegree
      positivity
    have hpow :
        counterexamplePositiveRoot N K ^ (counterexampleExponent N K j - k) =
          Real.exp (((counterexampleExponent N K j - k : ℕ) : ℝ) *
            (counterexampleTau N K / (counterexampleDegree N K : ℝ))) := by
      rw [counterexamplePositiveRoot]
      rw [Real.exp_nat_mul]
    have hcast_sub :
        ((counterexampleExponent N K j - k : ℕ) : ℝ) =
          (counterexampleExponent N K j : ℝ) - (k : ℝ) := by
      rw [Nat.cast_sub hkm]
    have hexp :
        Real.exp (-(counterexampleLambda N K j * counterexampleTau N K)) *
            counterexamplePositiveRoot N K ^ (counterexampleExponent N K j - k) =
          Real.exp (-(k : ℝ) * counterexampleTau N K /
            (counterexampleDegree N K : ℝ)) := by
      rw [hpow, ← Real.exp_add]
      rw [counterexampleLambda]
      rw [hcast_sub]
      apply congrArg Real.exp
      field_simp [hdeg_real]
      ring
    norm_cast
    norm_num
    rw [counterexampleRealCoeff]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc
      (((-1 : ℝ) ^ (N + 1 - j.val) *
            Real.exp (-(counterexampleLambda N K j * counterexampleTau N K)) *
          (counterexampleDelta N K j)⁻¹) *
          counterexamplePositiveRoot N K ^ (counterexampleExponent N K j - k) *
        ↑((counterexampleExponent N K j).choose k)) =
          (Real.exp (-(counterexampleLambda N K j * counterexampleTau N K)) *
              counterexamplePositiveRoot N K ^ (counterexampleExponent N K j - k)) *
            ((-1 : ℝ) ^ (N + 1 - j.val) *
              ↑((counterexampleExponent N K j).choose k) *
                (counterexampleDelta N K j)⁻¹) := by
        ring
      _ = Real.exp (-(k : ℝ) * counterexampleTau N K /
            (counterexampleDegree N K : ℝ)) *
            ((-1 : ℝ) ^ (N + 1 - j.val) *
              ↑((counterexampleExponent N K j).choose k) *
                (counterexampleDelta N K j)⁻¹) := by
        rw [hexp]
      _ = Real.exp ((- (k : ℝ)) * counterexampleTau N K /
            (counterexampleDegree N K : ℝ)) *
            (((-1 : ℝ) ^ (N + 1 - j.val) *
              ↑((counterexampleExponent N K j).choose k)) *
                (counterexampleDelta N K j)⁻¹) := by
        ring
      _ = Real.exp (-(↑k * counterexampleTau N K) *
            (↑(counterexampleDegree N K))⁻¹) *
            ((-1 : ℝ) ^ (N + 1 - ↑j) *
              ↑((counterexampleExponent N K j).choose k) /
                counterexampleDelta N K j) := by
        rw [div_eq_mul_inv]
        ring_nf

/-- Taylor-expanded at the special positive point, the algebraic polynomial starts in exactly
degree `N + 1`.

This is the polynomial/Taylor version of the tex proof's multiplicity-transfer paragraph: the
Vandermonde identity makes the first `N + 1` Taylor coefficients vanish and the next one nonzero. -/
theorem counterexamplePolynomial_taylor_initial_coefficients_positiveRoot
    (N K : ℕ) (_hN : 1 ≤ N) (hK : 2 ≤ K) :
    (∀ k < N + 1,
      (((counterexamplePolynomial N K).comp
        (Polynomial.X + Polynomial.C (counterexamplePositiveRoot N K : ℂ))).coeff k = 0)) ∧
      (((counterexamplePolynomial N K).comp
        (Polynomial.X + Polynomial.C (counterexamplePositiveRoot N K : ℂ))).coeff (N + 1) ≠
          0) := by
  constructor
  · intro k hk
    rw [counterexamplePolynomial_taylor_coeff_eq_signed_choose_sum N K k hK]
    have hsigned_complex :
        (∑ j : Fin (N + 2),
          (↑(-1 : ℝ) ^ (N + 1 - ↑j) *
            ↑↑((counterexampleExponent N K j).choose k) /
              ↑(counterexampleDelta N K j) : ℂ)) =
          ((scaledChoosePolynomial (counterexampleDegree N K) k).coeff (N + 1) : ℂ) := by
      exact_mod_cast counterexample_signed_choose_sum_eq_scaledChoose_coeff N K k hK
        (by omega)
    norm_num
    rw [show
      (∑ x : Fin (N + 2),
        (-1 : ℂ) ^ (N + 1 - ↑x) *
          ↑((counterexampleExponent N K x).choose k) /
            ↑(counterexampleDelta N K x)) =
          ((scaledChoosePolynomial (counterexampleDegree N K) k).coeff (N + 1) : ℂ) by
        simpa using hsigned_complex]
    have htop_zero :
        (scaledChoosePolynomial (counterexampleDegree N K) k).coeff (N + 1) = 0 := by
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        ((scaledChoosePolynomial_natDegree_le (counterexampleDegree N K) k).trans_lt hk)
    rw [htop_zero]
    simp
  · rw [counterexamplePolynomial_taylor_coeff_eq_signed_choose_sum N K (N + 1) hK]
    have hsigned_complex :
        (∑ j : Fin (N + 2),
          (↑(-1 : ℝ) ^ (N + 1 - ↑j) *
            ↑↑((counterexampleExponent N K j).choose (N + 1)) /
              ↑(counterexampleDelta N K j) : ℂ)) =
          ((scaledChoosePolynomial (counterexampleDegree N K) (N + 1)).coeff (N + 1) : ℂ) := by
      exact_mod_cast counterexample_signed_choose_sum_eq_scaledChoose_coeff N K (N + 1) hK
        le_rfl
    norm_num
    rw [show
      (∑ x : Fin (N + 2),
        (-1 : ℂ) ^ (N + 1 - ↑x) *
          ↑((counterexampleExponent N K x).choose (N + 1)) /
            ↑(counterexampleDelta N K x)) =
          ((scaledChoosePolynomial (counterexampleDegree N K) (N + 1)).coeff (N + 1) : ℂ) by
        simpa using hsigned_complex]
    rw [scaledChoosePolynomial_coeff_self]
    have hd_nat : counterexampleDegree N K ≠ 0 := by
      unfold counterexampleDegree
      exact pow_ne_zero N (ne_of_gt (by omega : 0 < K))
    have hnum : ((counterexampleDegree N K : ℝ) ^ (N + 1)) ≠ 0 := by
      exact_mod_cast pow_ne_zero (N + 1) hd_nat
    have hden : (((N + 1).factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (N + 1)
    exact_mod_cast div_ne_zero hnum hden

/-- Taylor-expanded at the special positive point, the algebraic polynomial starts in exactly
degree `N + 1`.

This is the polynomial/Taylor version of the tex proof's multiplicity-transfer paragraph: the
Vandermonde identity makes the first `N + 1` Taylor coefficients vanish and the next one nonzero. -/
theorem counterexamplePolynomial_taylor_natTrailingDegree_positiveRoot
    (N K : ℕ) (hN : 1 ≤ N) (hK : 2 ≤ K) :
    ((counterexamplePolynomial N K).comp
      (Polynomial.X + Polynomial.C (counterexamplePositiveRoot N K : ℂ))).natTrailingDegree =
        N + 1 := by
  let q :=
    (counterexamplePolynomial N K).comp
      (Polynomial.X + Polynomial.C (counterexamplePositiveRoot N K : ℂ))
  have hcoeff := counterexamplePolynomial_taylor_initial_coefficients_positiveRoot N K hN hK
  have hq_ne_zero : q ≠ 0 := by
    intro hq
    exact hcoeff.2 (by simp [q, hq])
  refine le_antisymm ?_ ?_
  · exact Polynomial.natTrailingDegree_le_of_ne_zero hcoeff.2
  · exact Polynomial.le_natTrailingDegree hq_ne_zero hcoeff.1

/-- The positive root has the multiplicity promised by the Vandermonde construction. -/
theorem counterexamplePolynomial_rootMultiplicity_positiveRoot
    (N K : ℕ) (hN : 1 ≤ N) (hK : 2 ≤ K) :
    (counterexamplePolynomial N K).rootMultiplicity (counterexamplePositiveRoot N K : ℂ) =
      N + 1 := by
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
  exact counterexamplePolynomial_taylor_natTrailingDegree_positiveRoot N K hN hK

/-- Every coefficient in the displayed lacunary sum is nonzero. -/
theorem counterexampleRealCoeff_ne_zero (N K : ℕ) (hK : 2 ≤ K) (j : Fin (N + 2)) :
    counterexampleRealCoeff N K j ≠ 0 := by
  rw [counterexampleRealCoeff]
  refine div_ne_zero ?_ (counterexampleDelta_ne_zero N K hK j)
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (Real.exp_ne_zero _)

/-- At a listed lacunary exponent, the algebraic counterexample has the listed coefficient. -/
theorem counterexamplePolynomial_coeff_exponent
    (N K : ℕ) (hK : 2 ≤ K) (j : Fin (N + 2)) :
    (counterexamplePolynomial N K).coeff (counterexampleExponent N K j) =
      (counterexampleRealCoeff N K j : ℂ) := by
  unfold counterexamplePolynomial
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single j]
  · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
  · intro i _hi hij
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]
    exact fun h => hij (counterexampleExponent_injective N K hK h.symm)
  · simp

/-- The support of the algebraic counterexample is exactly the image of the lacunary exponent
list. -/
theorem counterexamplePolynomial_support_eq_image
    (N K : ℕ) (hK : 2 ≤ K) :
    (counterexamplePolynomial N K).support =
      (Finset.univ : Finset (Fin (N + 2))).image (counterexampleExponent N K) := by
  ext m
  rw [Polynomial.mem_support_iff, Finset.mem_image]
  constructor
  · intro hcoeff
    by_contra hnot
    push Not at hnot
    refine hcoeff ?_
    unfold counterexamplePolynomial
    rw [Polynomial.finset_sum_coeff]
    refine Finset.sum_eq_zero ?_
    intro j _hj
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]
    exact fun h => hnot j (by simp) h.symm
  · rintro ⟨j, _hj, rfl⟩
    rw [counterexamplePolynomial_coeff_exponent N K hK j]
    exact_mod_cast counterexampleRealCoeff_ne_zero N K hK j

/-- Its leading coefficient, at the advertised degree, is nonzero. -/
theorem counterexamplePolynomial_coeff_degree_ne_zero
    (N K : ℕ) (_hN : 1 ≤ N) (hK : 2 ≤ K) :
    (counterexamplePolynomial N K).coeff (counterexampleDegree N K) ≠ 0 := by
  unfold counterexamplePolynomial
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single (Fin.last (N + 1))]
  · rw [Polynomial.coeff_C_mul_X_pow, counterexampleExponent_last, if_pos rfl]
    exact_mod_cast counterexampleRealCoeff_ne_zero N K hK (Fin.last (N + 1))
  · intro j _hj hne
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]
    intro hexp
    have hlast :
        counterexampleExponent N K j =
          counterexampleExponent N K (Fin.last (N + 1)) := by
      rw [counterexampleExponent_last]
      exact hexp.symm
    exact hne (counterexampleExponent_injective N K hK hlast)
  · intro hlast
    simp at hlast

/-- The counterexample polynomial has the advertised degree `d = K ^ N`. -/
theorem counterexamplePolynomial_natDegree
    (N K : ℕ) (hN : 1 ≤ N) (hK : 2 ≤ K) :
    (counterexamplePolynomial N K).natDegree = counterexampleDegree N K := by
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_
    (counterexamplePolynomial_coeff_degree_ne_zero N K hN hK)
  unfold counterexamplePolynomial
  refine Polynomial.natDegree_sum_le_of_forall_le
    (s := (Finset.univ : Finset (Fin (N + 2))))
    (f := fun j : Fin (N + 2) =>
      Polynomial.C (counterexampleRealCoeff N K j : ℂ) *
        Polynomial.X ^ counterexampleExponent N K j) ?_
  intro j _hj
  refine (Polynomial.natDegree_C_mul_X_pow_le
    (counterexampleRealCoeff N K j : ℂ) (counterexampleExponent N K j)).trans ?_
  rw [counterexampleDegree]
  rw [counterexampleExponent]
  split_ifs with hzero
  · exact Nat.zero_le _
  · refine Nat.pow_le_pow_right (by omega) ?_
    exact Nat.sub_le_of_le_add (by omega)

/-- Its constant coefficient is nonzero. -/
theorem counterexamplePolynomial_coeff_zero_ne_zero
    (N K : ℕ) (_hN : 1 ≤ N) (hK : 2 ≤ K) :
    (counterexamplePolynomial N K).coeff 0 ≠ 0 := by
  unfold counterexamplePolynomial
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin (N + 2))]
  · rw [Polynomial.coeff_C_mul_X_pow, counterexampleExponent_zero, if_pos rfl]
    exact_mod_cast counterexampleRealCoeff_ne_zero N K hK ⟨0, by omega⟩
  · intro j _hj hne
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]
    intro hexp
    have hzero :
        counterexampleExponent N K j =
          counterexampleExponent N K (⟨0, by omega⟩ : Fin (N + 2)) := by
      rw [counterexampleExponent_zero]
      exact hexp.symm
    exact hne (counterexampleExponent_injective N K hK hzero)
  · intro hfirst
    simp at hfirst

/-- The counterexample polynomial has exactly the `N + 2` lacunary coefficients from the
construction. -/
theorem counterexamplePolynomial_coeffSupportCard
    (N K : ℕ) (hN : 1 ≤ N) (hK : 2 ≤ K) :
    coeffSupportCardUpTo (counterexamplePolynomial N K) (counterexampleDegree N K) = N + 2 := by
  let p := counterexamplePolynomial N K
  have hsupport_card : p.support.card = N + 2 := by
    unfold p counterexamplePolynomial
    exact Polynomial.card_support_eq'
      (k := counterexampleExponent N K)
      (x := fun j : Fin (N + 2) => (counterexampleRealCoeff N K j : ℂ))
      (counterexampleExponent_injective N K hK)
      (fun j => by
        change (counterexampleRealCoeff N K j : ℂ) ≠ 0
        exact_mod_cast counterexampleRealCoeff_ne_zero N K hK j)
  have hfilter :
      (Finset.range (counterexampleDegree N K + 1)).filter
          (fun k => (counterexamplePolynomial N K).coeff k ≠ 0) =
        p.support := by
    ext m
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hm
      simpa [p, Polynomial.mem_support_iff] using hm.2
    · intro hm
      have hcoeff : (counterexamplePolynomial N K).coeff m ≠ 0 := by
        simpa [p, Polynomial.mem_support_iff] using hm
      have hmle : m ≤ counterexampleDegree N K := by
        simpa [counterexamplePolynomial_natDegree N K hN hK]
          using Polynomial.le_natDegree_of_ne_zero hcoeff
      exact ⟨Nat.lt_succ_of_le hmle, hcoeff⟩
  unfold coeffSupportCardUpTo
  rw [hfilter]
  exact hsupport_card

/-- The positive normalization factor `A_j = sqrt (Δ_0 Δ_last) / Δ_j` used in the tex height
calculation. -/
noncomputable def counterexampleHeightAmplitude
    (N K : ℕ) (j : Fin (N + 2)) : ℝ :=
  Real.sqrt
    (counterexampleDelta N K ⟨0, by omega⟩ *
      counterexampleDelta N K (Fin.last (N + 1))) /
    counterexampleDelta N K j

/-- The exact-height expression
`∑ A_j T ^ (1 - 2 λ_j)` appearing in Proposition `height` of the tex proof. -/
noncomputable def counterexampleHeightFormula (N K : ℕ) : ℝ :=
  ∑ j : Fin (N + 2),
    counterexampleHeightAmplitude N K j *
      counterexampleTilt N K ^ (1 - 2 * counterexampleLambda N K j)

/-- For the lacunary counterexample, the coefficient ratio is the sum of absolute constructed
coefficients, normalized by the two endpoint coefficients. -/
theorem counterexample_coefficientRatio_eq_sum_normalized_realCoeff
    (N K : ℕ) (hN : 1 ≤ N) (hK : 2 ≤ K) :
    coefficientRatio (counterexamplePolynomial N K) (counterexampleDegree N K) =
      (∑ j : Fin (N + 2), ‖(counterexampleRealCoeff N K j : ℂ)‖) /
        Real.sqrt
          (‖(counterexampleRealCoeff N K ⟨0, by omega⟩ : ℂ)‖ *
            ‖(counterexampleRealCoeff N K (Fin.last (N + 1)) : ℂ)‖) := by
  let p := counterexamplePolynomial N K
  let d := counterexampleDegree N K
  have hnatDegree : p.natDegree = d := counterexamplePolynomial_natDegree N K hN hK
  have hsupport_subset_range : p.support ⊆ Finset.range (d + 1) := by
    intro m hm
    have hcoeff : p.coeff m ≠ 0 := by
      simpa [p, Polynomial.mem_support_iff] using hm
    have hmle : m ≤ d := by
      simpa [p, d, hnatDegree] using Polynomial.le_natDegree_of_ne_zero hcoeff
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hmle)
  have hnum_range :
      (∑ k ∈ Finset.range (d + 1), ‖p.coeff k‖) =
        p.sum (fun _ a => ‖a‖) := by
    rw [Polynomial.sum_eq_of_subset (p := p) (s := Finset.range (d + 1))
      (f := fun _ a => ‖a‖) (by simp) hsupport_subset_range]
  have hnum :
      (∑ k ∈ Finset.range (d + 1), ‖p.coeff k‖) =
        ∑ j : Fin (N + 2), ‖(counterexampleRealCoeff N K j : ℂ)‖ := by
    rw [hnum_range, Polynomial.sum_def, counterexamplePolynomial_support_eq_image N K hK]
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl ?_
      intro j _hj
      rw [counterexamplePolynomial_coeff_exponent N K hK j]
    · intro i _hi j _hj hij
      exact counterexampleExponent_injective N K hK hij
  have hcoeff_zero :
      p.coeff 0 = (counterexampleRealCoeff N K ⟨0, by omega⟩ : ℂ) := by
    change (counterexamplePolynomial N K).coeff 0 =
      (counterexampleRealCoeff N K ⟨0, by omega⟩ : ℂ)
    simpa [counterexampleExponent_zero] using
      counterexamplePolynomial_coeff_exponent N K hK ⟨0, by omega⟩
  have hcoeff_last :
      p.coeff d = (counterexampleRealCoeff N K (Fin.last (N + 1)) : ℂ) := by
    change (counterexamplePolynomial N K).coeff (counterexampleDegree N K) =
      (counterexampleRealCoeff N K (Fin.last (N + 1)) : ℂ)
    simpa [counterexampleExponent_last] using
      counterexamplePolynomial_coeff_exponent N K hK (Fin.last (N + 1))
  unfold coefficientRatio
  simp only [p, d] at hnum hcoeff_zero hcoeff_last
  rw [hnum, hcoeff_zero, hcoeff_last]

/-- The normalized size of each real coefficient is the corresponding term in the exact
height formula. -/
theorem counterexampleRealCoeff_norm_eq_tilt_power_div_delta
    (N K : ℕ) (hK : 2 ≤ K) (j : Fin (N + 2)) :
    ‖(counterexampleRealCoeff N K j : ℂ)‖ =
      counterexampleTilt N K ^ (-2 * counterexampleLambda N K j) /
        counterexampleDelta N K j := by
  have hΔ_pos : 0 < counterexampleDelta N K j := counterexampleDelta_pos N K hK j
  have hA₁_pos : 0 < counterexampleA₁ N K := by
    unfold counterexampleA₁
    exact Real.sqrt_pos.mpr (div_pos
      (counterexampleDelta_pos N K hK (Fin.last (N + 1)))
      (counterexampleDelta_pos N K hK ⟨0, by omega⟩))
  have hT_pos : 0 < counterexampleTilt N K := by
    unfold counterexampleTilt
    positivity
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold counterexampleRealCoeff
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [abs_of_pos (Real.exp_pos _), abs_of_pos hΔ_pos]
  rw [counterexampleTau, Real.rpow_def_of_pos hT_pos]
  congr 1
  ring_nf

theorem counterexampleRealCoeff_endpoint_norm_sqrt
    (N K : ℕ) (hK : 2 ≤ K) :
    Real.sqrt
      (‖(counterexampleRealCoeff N K ⟨0, by omega⟩ : ℂ)‖ *
        ‖(counterexampleRealCoeff N K (Fin.last (N + 1)) : ℂ)‖) =
      counterexampleTilt N K ^ (-1 : ℝ) /
        Real.sqrt (counterexampleDelta N K ⟨0, by omega⟩ *
          counterexampleDelta N K (Fin.last (N + 1))) := by
  have hΔ₀_pos : 0 < counterexampleDelta N K ⟨0, by omega⟩ :=
    counterexampleDelta_pos N K hK ⟨0, by omega⟩
  have hΔs_pos : 0 < counterexampleDelta N K (Fin.last (N + 1)) :=
    counterexampleDelta_pos N K hK (Fin.last (N + 1))
  have hA₁_pos : 0 < counterexampleA₁ N K := by
    unfold counterexampleA₁
    exact Real.sqrt_pos.mpr (div_pos hΔs_pos hΔ₀_pos)
  have hT_pos : 0 < counterexampleTilt N K := by
    unfold counterexampleTilt
    positivity
  have hTinv_nonneg : 0 ≤ counterexampleTilt N K ^ (-1 : ℝ) :=
    Real.rpow_nonneg hT_pos.le _
  rw [counterexampleRealCoeff_norm_eq_tilt_power_div_delta N K hK ⟨0, by omega⟩]
  rw [counterexampleRealCoeff_norm_eq_tilt_power_div_delta N K hK (Fin.last (N + 1))]
  rw [counterexampleLambda_zero, counterexampleLambda_last N K (by omega : 0 < K)]
  simp only [mul_zero, Real.rpow_zero, mul_one]
  change Real.sqrt ((1 / counterexampleDelta N K ⟨0, by omega⟩) *
      (counterexampleTilt N K ^ (-2 : ℝ) /
        counterexampleDelta N K (Fin.last (N + 1)))) =
    counterexampleTilt N K ^ (-1 : ℝ) /
      Real.sqrt (counterexampleDelta N K ⟨0, by omega⟩ *
        counterexampleDelta N K (Fin.last (N + 1)))
  rw [show counterexampleTilt N K ^ (-2 : ℝ) =
      (counterexampleTilt N K ^ (-1 : ℝ)) ^ 2 by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hT_pos.le]
    norm_num]
  rw [show (1 / counterexampleDelta N K ⟨0, by omega⟩) *
      ((counterexampleTilt N K ^ (-1 : ℝ)) ^ 2 /
        counterexampleDelta N K (Fin.last (N + 1))) =
      (counterexampleTilt N K ^ (-1 : ℝ)) ^ 2 /
        (counterexampleDelta N K ⟨0, by omega⟩ *
          counterexampleDelta N K (Fin.last (N + 1))) by
    field_simp [hΔ₀_pos.ne', hΔs_pos.ne']]
  rw [Real.sqrt_div (sq_nonneg _)
    (counterexampleDelta N K ⟨0, by omega⟩ *
      counterexampleDelta N K (Fin.last (N + 1)))]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hTinv_nonneg]

theorem counterexample_normalized_realCoeff_norm_eq_heightTerm
    (N K : ℕ) (hK : 2 ≤ K) (j : Fin (N + 2)) :
    ‖(counterexampleRealCoeff N K j : ℂ)‖ /
        Real.sqrt
          (‖(counterexampleRealCoeff N K ⟨0, by omega⟩ : ℂ)‖ *
            ‖(counterexampleRealCoeff N K (Fin.last (N + 1)) : ℂ)‖) =
      counterexampleHeightAmplitude N K j *
        counterexampleTilt N K ^ (1 - 2 * counterexampleLambda N K j) := by
  have hΔj_pos : 0 < counterexampleDelta N K j := counterexampleDelta_pos N K hK j
  have hΔ₀_pos : 0 < counterexampleDelta N K ⟨0, by omega⟩ :=
    counterexampleDelta_pos N K hK ⟨0, by omega⟩
  have hΔs_pos : 0 < counterexampleDelta N K (Fin.last (N + 1)) :=
    counterexampleDelta_pos N K hK (Fin.last (N + 1))
  have hA₁_pos : 0 < counterexampleA₁ N K := by
    unfold counterexampleA₁
    exact Real.sqrt_pos.mpr (div_pos hΔs_pos hΔ₀_pos)
  have hT_pos : 0 < counterexampleTilt N K := by
    unfold counterexampleTilt
    positivity
  have hsqrtΔ_ne :
      Real.sqrt (counterexampleDelta N K ⟨0, by omega⟩ *
        counterexampleDelta N K (Fin.last (N + 1))) ≠ 0 := by
    exact Real.sqrt_ne_zero (mul_pos hΔ₀_pos hΔs_pos).le |>.mpr
      (mul_pos hΔ₀_pos hΔs_pos).ne'
  have hTinv_ne : counterexampleTilt N K ^ (-1 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hT_pos _).ne'
  rw [counterexampleRealCoeff_norm_eq_tilt_power_div_delta N K hK j]
  rw [counterexampleRealCoeff_endpoint_norm_sqrt N K hK]
  unfold counterexampleHeightAmplitude
  rw [show counterexampleTilt N K ^ (1 - 2 * counterexampleLambda N K j) =
      counterexampleTilt N K ^ (-2 * counterexampleLambda N K j) /
        counterexampleTilt N K ^ (-1 : ℝ) by
    rw [← Real.rpow_sub hT_pos]
    congr 1
    ring]
  field_simp [hΔj_pos.ne', hTinv_ne, hsqrtΔ_ne]

/-- The coefficient ratio equals the exact height expression from the tex proof. -/
theorem counterexample_coefficientRatio_eq_heightFormula
    (N K : ℕ) (hN : 1 ≤ N) (hK : 2 ≤ K) :
    coefficientRatio (counterexamplePolynomial N K) (counterexampleDegree N K) =
      counterexampleHeightFormula N K := by
  rw [counterexample_coefficientRatio_eq_sum_normalized_realCoeff N K hN hK]
  rw [Finset.sum_div]
  unfold counterexampleHeightFormula
  refine Finset.sum_congr rfl ?_
  intro j _hj
  exact counterexample_normalized_realCoeff_norm_eq_heightTerm N K hK j

/-- The first height amplitude is the `A_1` normalization from the tex proof. -/
theorem counterexampleHeightAmplitude_zero_eq_A₁ (N K : ℕ) (hK : 2 ≤ K) :
    counterexampleHeightAmplitude N K ⟨0, by omega⟩ = counterexampleA₁ N K := by
  let Δ₀ := counterexampleDelta N K ⟨0, by omega⟩
  let Δs := counterexampleDelta N K (Fin.last (N + 1))
  have hΔ₀_pos : 0 < Δ₀ := counterexampleDelta_pos N K hK ⟨0, by omega⟩
  have hΔs_pos : 0 < Δs := counterexampleDelta_pos N K hK (Fin.last (N + 1))
  have hsqrt_Δ₀_ne : Real.sqrt Δ₀ ≠ 0 := Real.sqrt_ne_zero hΔ₀_pos.le |>.mpr hΔ₀_pos.ne'
  unfold counterexampleHeightAmplitude counterexampleA₁
  change Real.sqrt (Δ₀ * Δs) / Δ₀ = Real.sqrt (Δs / Δ₀)
  rw [Real.sqrt_div hΔs_pos.le]
  field_simp [hsqrt_Δ₀_ne]
  rw [Real.sqrt_mul hΔ₀_pos.le]
  ring_nf
  rw [Real.sq_sqrt hΔ₀_pos.le]
  ring

/-- The first height-formula term is exactly `1 / √2`. -/
theorem counterexample_heightFormula_zero_term_eq (N K : ℕ) (hK : 2 ≤ K) :
    counterexampleHeightAmplitude N K ⟨0, by omega⟩ *
        counterexampleTilt N K ^
          (1 - 2 * counterexampleLambda N K ⟨0, by omega⟩) =
      1 / Real.sqrt 2 := by
  have hA₁_pos : 0 < counterexampleA₁ N K := by
    unfold counterexampleA₁
    exact Real.sqrt_pos.mpr (div_pos
      (counterexampleDelta_pos N K hK (Fin.last (N + 1)))
      (counterexampleDelta_pos N K hK ⟨0, by omega⟩))
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by norm_num : 0 < (2 : ℝ))
  rw [counterexampleHeightAmplitude_zero_eq_A₁ N K hK]
  rw [counterexampleLambda_zero]
  norm_num
  unfold counterexampleTilt
  field_simp [hA₁_pos.ne', hsqrt2_ne]

/-- The fixed-`N` limit of the `j`th term in the height formula.

The surviving terms are the first endpoint, the exponent-`1` term, and the last endpoint. -/
noncomputable def counterexampleHeightTermLimit (N : ℕ) (j : Fin (N + 2)) : ℝ :=
  if j.val = 0 then 1 / Real.sqrt 2
  else if j.val = 1 then 1 / Real.sqrt 2
  else if j.val = N + 1 then Real.sqrt 2
  else 0

/-- The height-formula term indexed by the constant term tends to `1/√2`. -/
theorem counterexample_heightFormula_zero_term_tendsto
    (N : ℕ) (hN : 1 ≤ N) :
    Filter.Tendsto
      (fun K : ℕ =>
        counterexampleHeightAmplitude N K ⟨0, by omega⟩ *
          counterexampleTilt N K ^
            (1 - 2 * counterexampleLambda N K ⟨0, by omega⟩))
      Filter.atTop
      (nhds (1 / Real.sqrt 2)) := by
  refine tendsto_const_nhds.congr' ?_
  refine Filter.eventually_atTop.2 ⟨2, ?_⟩
  intro K hK
  exact (counterexample_heightFormula_zero_term_eq N K hK).symm

/-- Ratios of height amplitudes cancel to the reciprocal ratio of positive Vandermonde
denominators. -/
theorem counterexampleHeightAmplitude_div_zero_eq_delta_ratio
    (N K : ℕ) (hK : 2 ≤ K) (j : Fin (N + 2)) :
    counterexampleHeightAmplitude N K j /
        counterexampleHeightAmplitude N K ⟨0, by omega⟩ =
      counterexampleDelta N K ⟨0, by omega⟩ / counterexampleDelta N K j := by
  let Δ₀ := counterexampleDelta N K ⟨0, by omega⟩
  let Δs := counterexampleDelta N K (Fin.last (N + 1))
  let Δj := counterexampleDelta N K j
  have hΔ₀_pos : 0 < Δ₀ := counterexampleDelta_pos N K hK ⟨0, by omega⟩
  have hΔs_pos : 0 < Δs := counterexampleDelta_pos N K hK (Fin.last (N + 1))
  have hΔj_pos : 0 < Δj := counterexampleDelta_pos N K hK j
  have hS_ne : Real.sqrt (Δ₀ * Δs) ≠ 0 := by
    exact Real.sqrt_ne_zero (mul_pos hΔ₀_pos hΔs_pos).le |>.mpr
      (mul_pos hΔ₀_pos hΔs_pos).ne'
  unfold counterexampleHeightAmplitude
  change (Real.sqrt (Δ₀ * Δs) / Δj) / (Real.sqrt (Δ₀ * Δs) / Δ₀) = Δ₀ / Δj
  field_simp [hS_ne, hΔ₀_pos.ne', hΔj_pos.ne']

/-- The finite product of correction factors for `Δ_0 / Δ_1`. -/
noncomputable def counterexampleFirstDeltaCorrectionProduct (N K : ℕ) : ℝ :=
  ∏ r : Fin N, (1 - (K : ℝ) ^ (-((r.val + 1 : ℕ) : ℝ)))⁻¹

/-- The explicit product formula for `Δ_0 / Δ_1` from the tex proof. -/
theorem counterexample_delta_zero_div_one_eq_correctionProduct
    (N K : ℕ) (hN : 1 ≤ N) (hK : 2 ≤ K) :
    counterexampleDelta N K ⟨0, by omega⟩ / counterexampleDelta N K ⟨1, by omega⟩ =
      counterexampleFirstDeltaCorrectionProduct N K := by
  have hlambda0 : counterexampleLambda N K ⟨0, by omega⟩ = 0 :=
    counterexampleLambda_zero N K
  have hlambda0_fin : counterexampleLambda N K (0 : Fin (N + 2)) = 0 := by
    simpa using counterexampleLambda_zero N K
  have hdelta0 :
      counterexampleDelta N K ⟨0, by omega⟩ =
        ∏ i : Fin (N + 1), counterexampleLambda N K i.succ := by
    unfold counterexampleDelta
    rw [Fin.prod_univ_succ]
    simp only [Fin.zero_eta, ↓reduceIte, one_mul]
    refine Finset.prod_congr rfl ?_
    intro i _hi
    rw [hlambda0_fin, zero_sub, abs_neg]
    rw [abs_of_nonneg]
    · rw [if_neg (Fin.succ_ne_zero i)]
    have hnonneg :
        0 ≤ counterexampleLambda N K i.succ := by
      have hlt := counterexampleLambda_strictMono N K hK
        (show (0 : Fin (N + 2)) < i.succ by simp)
      rw [hlambda0_fin] at hlt
      exact hlt.le
    exact hnonneg
  have hdelta1 :
      counterexampleDelta N K ⟨1, by omega⟩ =
        counterexampleLambda N K ⟨1, by omega⟩ *
          ∏ r : Fin N,
            (counterexampleLambda N K r.succ.succ -
              counterexampleLambda N K ⟨1, by omega⟩) := by
    unfold counterexampleDelta
    rw [Fin.prod_univ_succ]
    have hzeroFactor :
        (if (0 : Fin (N + 2)) = ⟨1, by omega⟩ then (1 : ℝ)
          else |counterexampleLambda N K ⟨1, by omega⟩ -
            counterexampleLambda N K (0 : Fin (N + 2))|) =
          counterexampleLambda N K ⟨1, by omega⟩ := by
      rw [hlambda0_fin, sub_zero]
      rw [abs_of_nonneg]
      · rw [if_neg
          (by norm_num :
            (0 : Fin (N + 2)) ≠
              ⟨1, Nat.succ_lt_succ (Nat.succ_pos N)⟩)]
      have hlt := counterexampleLambda_strictMono N K hK
        (show (0 : Fin (N + 2)) < ⟨1, by omega⟩ by norm_num)
      rw [hlambda0_fin] at hlt
      exact hlt.le
    rw [hzeroFactor]
    rw [Fin.prod_univ_succ]
    simp only [Fin.succ_zero_eq_one]
    rw [show (1 : Fin (N + 2)) = ⟨1, by omega⟩ by ext; simp]
    rw [if_pos rfl, one_mul]
    congr 1
    refine Finset.prod_congr rfl ?_
    intro r _hr
    have hne : r.succ.succ ≠ (⟨1, by omega⟩ : Fin (N + 2)) := by
      exact Fin.ne_of_val_ne (by simp)
    rw [if_neg hne]
    rw [abs_of_neg]
    · ring
    · exact sub_neg.mpr (counterexampleLambda_strictMono N K hK
        (show (⟨1, by omega⟩ : Fin (N + 2)) < r.succ.succ by
          exact Fin.mk_lt_mk.mpr (by omega)))
  rw [hdelta0, hdelta1]
  rw [Fin.prod_univ_succ]
  have hlambda1_pos :
      counterexampleLambda N K ⟨1, by omega⟩ ≠ 0 := by
    have hlt := counterexampleLambda_strictMono N K hK
      (show (0 : Fin (N + 2)) < ⟨1, by omega⟩ by norm_num)
    rw [hlambda0_fin] at hlt
    exact hlt.ne'
  rw [show (counterexampleLambda N K (Fin.succ 0)) =
      counterexampleLambda N K ⟨1, by omega⟩ by rfl]
  field_simp [hlambda1_pos]
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl ?_
  intro r _hr
  rw [counterexampleLambda, counterexampleLambda]
  simp only [counterexampleExponent, counterexampleDegree, Fin.val_succ, Nat.add_eq_zero_iff,
    one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right, Nat.cast_pow]
  have hK_pos : 0 < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hq_ne : (K : ℝ) ^ (r.val + 1) ≠ 0 := pow_ne_zero _ hK_pos.ne'
  have hd_ne : (K : ℝ) ^ N ≠ 0 := pow_ne_zero _ hK_pos.ne'
  have hneg :
      (K : ℝ) ^ (-(((r.val + 1 : ℕ) : ℝ))) =
        ((K : ℝ) ^ (r.val + 1))⁻¹ := by
    rw [Real.rpow_neg hK_pos.le, Real.rpow_natCast]
  rw [hneg]
  norm_num
  field_simp [hq_ne, hd_ne]

/-- The explicit correction product for `Δ_0 / Δ_1` tends to `1`. -/
theorem counterexample_first_delta_correctionProduct_tendsto
    (N : ℕ) :
    Filter.Tendsto
      (fun K : ℕ => counterexampleFirstDeltaCorrectionProduct N K)
      Filter.atTop
      (nhds 1) := by
  have hprod :
      Filter.Tendsto
        (fun K : ℕ =>
          ∏ r : Fin N, (1 - (K : ℝ) ^ (-((r.val + 1 : ℕ) : ℝ)))⁻¹)
        Filter.atTop
        (nhds (∏ _r : Fin N, (1 : ℝ))) := by
    exact tendsto_finset_prod Finset.univ (fun r _hr => by
      have he_pos : 0 < (((r.val + 1 : ℕ) : ℝ)) := by positivity
      have hz :
          Filter.Tendsto
            (fun K : ℕ => (K : ℝ) ^ (-(((r.val + 1 : ℕ) : ℝ))))
            Filter.atTop
            (nhds 0) :=
        (tendsto_rpow_neg_atTop he_pos).comp tendsto_natCast_atTop_atTop
      have hsub :
          Filter.Tendsto
            (fun K : ℕ => 1 - (K : ℝ) ^ (-(((r.val + 1 : ℕ) : ℝ))))
            Filter.atTop
            (nhds (1 - 0)) :=
        tendsto_const_nhds.sub hz
      have hinv := hsub.inv₀ (by norm_num : (1 - (0 : ℝ)) ≠ 0)
      simpa using hinv)
  simpa [counterexampleFirstDeltaCorrectionProduct] using hprod

/-- In the tex notation, `R_1 = Δ_0 / Δ_1 → 1`. -/
theorem counterexample_delta_zero_div_one_tendsto
    (N : ℕ) (hN : 1 ≤ N) :
    Filter.Tendsto
      (fun K : ℕ =>
        counterexampleDelta N K ⟨0, by omega⟩ /
          counterexampleDelta N K ⟨1, by omega⟩)
      Filter.atTop
      (nhds 1) := by
  refine (counterexample_first_delta_correctionProduct_tendsto N).congr' ?_
  refine Filter.eventually_atTop.2 ⟨2, ?_⟩
  intro K hK
  exact (counterexample_delta_zero_div_one_eq_correctionProduct N K hN hK).symm

/-- The tilt `T` is eventually positive. -/
theorem eventually_counterexampleTilt_pos (N : ℕ) :
    ∀ᶠ K in Filter.atTop, 0 < counterexampleTilt N K := by
  refine Filter.eventually_atTop.2 ⟨2, ?_⟩
  intro K hK
  have hA₁_pos : 0 < counterexampleA₁ N K := by
    unfold counterexampleA₁
    exact Real.sqrt_pos.mpr (div_pos
      (counterexampleDelta_pos N K hK (Fin.last (N + 1)))
      (counterexampleDelta_pos N K hK ⟨0, by omega⟩))
  unfold counterexampleTilt
  positivity

theorem counterexample_log_nat_mul_rpow_neg_tendsto_zero (N : ℕ) (hN : 1 ≤ N) :
    Filter.Tendsto (fun K : ℕ => Real.log (K : ℝ) * (K : ℝ) ^ (-(N : ℝ)))
      Filter.atTop (nhds 0) := by
  have hLittle :
      (fun x : ℝ => Real.log x) =o[Filter.atTop]
        (fun x : ℝ => x ^ ((N : ℝ) / 2)) := by
    exact isLittleO_log_rpow_atTop (by positivity)
  have hdiv :
      Filter.Tendsto
        (fun x : ℝ => Real.log x / (x ^ ((N : ℝ) / 2)))
        Filter.atTop (nhds 0) :=
    hLittle.tendsto_div_nhds_zero
  have hpow :
      Filter.Tendsto (fun K : ℕ => (K : ℝ) ^ (-(N : ℝ) / 2))
        Filter.atTop (nhds 0) := by
    have hpos : 0 < (N : ℝ) / 2 := by positivity
    simpa [neg_div] using
      (tendsto_rpow_neg_atTop hpos).comp tendsto_natCast_atTop_atTop
  have hprod := (hdiv.comp tendsto_natCast_atTop_atTop).mul hpow
  rw [zero_mul] at hprod
  refine hprod.congr' ?_
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun K hK => hK⟩] with K hK
  have hK_pos : 0 < (K : ℝ) := by exact_mod_cast hK
  rw [div_eq_mul_inv]
  rw [show ((N : ℝ) * 2⁻¹) = ((N : ℝ) / 2) by ring]
  change (Real.log (K : ℝ) * ((K : ℝ) ^ ((N : ℝ) / 2))⁻¹) *
      (K : ℝ) ^ (-(N : ℝ) / 2) =
    Real.log (K : ℝ) * (K : ℝ) ^ (-(N : ℝ))
  rw [mul_assoc]
  rw [← Real.rpow_neg hK_pos.le ((N : ℝ) / 2)]
  rw [← Real.rpow_add hK_pos]
  congr 2
  ring

theorem counterexampleDelta_last_formula (N K : ℕ) (hK : 2 ≤ K) :
    counterexampleDelta N K (Fin.last (N + 1)) =
      ∏ i : Fin (N + 1), (1 - counterexampleLambda N K i.castSucc) := by
  have hlast : counterexampleLambda N K (Fin.last (N + 1)) = 1 :=
    counterexampleLambda_last N K (by omega)
  unfold counterexampleDelta
  rw [Fin.prod_univ_castSucc]
  rw [if_pos rfl, mul_one]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  have hne : i.castSucc ≠ Fin.last (N + 1) := Fin.castSucc_ne_last i
  rw [if_neg hne]
  rw [hlast]
  rw [abs_of_nonneg]
  have hle : counterexampleLambda N K i.castSucc ≤ 1 := by
    have hlt := counterexampleLambda_strictMono N K hK (Fin.castSucc_lt_last i)
    rw [hlast] at hlt
    exact hlt.le
  linarith

theorem counterexampleDelta_zero_formula (N K : ℕ) (hK : 2 ≤ K) :
    counterexampleDelta N K ⟨0, by omega⟩ =
      ∏ i : Fin (N + 1), counterexampleLambda N K i.succ := by
  have hlambda0_fin : counterexampleLambda N K (0 : Fin (N + 2)) = 0 := by
    simpa using counterexampleLambda_zero N K
  unfold counterexampleDelta
  rw [Fin.prod_univ_succ]
  simp only [Fin.zero_eta, ↓reduceIte, one_mul]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  rw [hlambda0_fin, zero_sub, abs_neg]
  rw [abs_of_nonneg]
  · rw [if_neg (Fin.succ_ne_zero i)]
  have hnonneg :
      0 ≤ counterexampleLambda N K i.succ := by
    have hlt := counterexampleLambda_strictMono N K hK
      (show (0 : Fin (N + 2)) < i.succ by simp)
    rw [hlambda0_fin] at hlt
    exact hlt.le
  exact hnonneg

noncomputable def counterexampleDeltaZeroDivFactor
    (N K : ℕ) (j l : Fin (N + 2)) : ℝ :=
  if l.val = 0 then 1
  else if l = j then 1
  else if l.val = N + 1 then (1 - counterexampleLambda N K j)⁻¹
  else
    counterexampleLambda N K l /
      |counterexampleLambda N K j - counterexampleLambda N K l|

noncomputable def counterexampleDeltaZeroDivFactorLimit
    (N : ℕ) (j l : Fin (N + 2)) : ℝ :=
  if l.val = 0 then 1
  else if l = j then 1
  else if l.val = N + 1 then 1
  else if l.val < j.val then 0
  else 1

theorem counterexample_delta_zero_div_eq_prod_factor
    (N K : ℕ) (hK : 2 ≤ K) (j : Fin (N + 2))
    (hj0 : j.val ≠ 0) (hjlast : j.val ≠ N + 1) :
    counterexampleDelta N K ⟨0, by omega⟩ / counterexampleDelta N K j =
      ∏ l : Fin (N + 2), counterexampleDeltaZeroDivFactor N K j l := by
  let z : Fin (N + 2) := ⟨0, by omega⟩
  let last : Fin (N + 2) := Fin.last (N + 1)
  have hj_ne_zero : j ≠ z := fun h => hj0 (by
    simpa [z] using congrArg Fin.val h)
  have hj_ne_last : j ≠ last := fun h => hjlast (by
    simpa [last, Fin.val_last] using congrArg Fin.val h)
  have hlambda0 : counterexampleLambda N K z = 0 := by
    simpa [z] using counterexampleLambda_zero N K
  have hlambdalast : counterexampleLambda N K last = 1 := by
    simpa [last] using counterexampleLambda_last N K (by omega : 0 < K)
  have hΔj_ne : counterexampleDelta N K j ≠ 0 := counterexampleDelta_ne_zero N K hK j
  rw [counterexampleDelta_eq_prod_erase N K z, counterexampleDelta_eq_prod_erase N K j]
  have hj_mem_erase_z : j ∈ Finset.univ.erase z := by
    rw [Finset.mem_erase]
    exact ⟨hj_ne_zero, Finset.mem_univ j⟩
  have hz_mem_erase_j : z ∈ Finset.univ.erase j := by
    rw [Finset.mem_erase]
    exact ⟨hj_ne_zero.symm, Finset.mem_univ z⟩
  rw [← Finset.prod_erase_mul (Finset.univ.erase z)
      (fun l => |counterexampleLambda N K z - counterexampleLambda N K l|)
      hj_mem_erase_z]
  rw [← Finset.prod_erase_mul (Finset.univ.erase j)
      (fun l => |counterexampleLambda N K j - counterexampleLambda N K l|)
      hz_mem_erase_j]
  have hz_factor :
      |counterexampleLambda N K j - counterexampleLambda N K z| ≠ 0 := by
    exact abs_ne_zero.mpr (sub_ne_zero.mpr (fun h =>
      hj_ne_zero (counterexampleLambda_injective N K hK h)))
  have hj_factor :
      |counterexampleLambda N K z - counterexampleLambda N K j| ≠ 0 := by
    exact abs_ne_zero.mpr (sub_ne_zero.mpr (fun h =>
      hj_ne_zero ((counterexampleLambda_injective N K hK h).symm)))
  have herase :
      (Finset.univ.erase j).erase z = (Finset.univ.erase z).erase j := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    tauto
  rw [herase]
  field_simp [hz_factor, hj_factor]
  rw [hlambda0, zero_sub, abs_neg]
  rw [sub_zero]
  have hlambdaj_abs_ne : |counterexampleLambda N K j| ≠ 0 := by
    simpa [hlambda0] using hz_factor
  field_simp [hlambdaj_abs_ne]
  simp only [zero_sub, abs_neg]
  rw [← Finset.prod_div_distrib]
  rw [show (∏ x ∈ (Finset.univ.erase z).erase j,
        |counterexampleLambda N K x| /
          |counterexampleLambda N K j - counterexampleLambda N K x|) =
      ∏ x : Fin (N + 2), counterexampleDeltaZeroDivFactor N K j x by
    rw [← Finset.prod_erase_mul (s := Finset.univ) (a := z)
      (f := fun x : Fin (N + 2) => counterexampleDeltaZeroDivFactor N K j x)
      (Finset.mem_univ z)]
    rw [show counterexampleDeltaZeroDivFactor N K j z = 1 by
      simp [counterexampleDeltaZeroDivFactor, z]]
    rw [mul_one]
    rw [← Finset.prod_erase_mul (s := Finset.univ.erase z) (a := j)
      (f := fun x : Fin (N + 2) => counterexampleDeltaZeroDivFactor N K j x)
      hj_mem_erase_z]
    rw [show counterexampleDeltaZeroDivFactor N K j j = 1 by
      simp [counterexampleDeltaZeroDivFactor, hj0]]
    rw [mul_one]
    refine Finset.prod_congr rfl ?_
    intro x hx
    have hxz : x.val ≠ 0 := by
      intro hxval
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1 (Fin.ext hxval)
    have hxj : x ≠ j := (Finset.mem_erase.mp hx).1
    unfold counterexampleDeltaZeroDivFactor
    rw [if_neg hxz, if_neg hxj]
    by_cases hxlast : x.val = N + 1
    · rw [if_pos hxlast]
      have hxlast' : x = last := Fin.ext (by simpa [last] using hxlast)
      rw [hxlast', hlambdalast]
      have hle : counterexampleLambda N K j ≤ 1 := by
        have hlt := counterexampleLambda_strictMono N K hK
          (show j < last by exact Fin.mk_lt_mk.mpr (by
            simp
            omega))
        rw [hlambdalast] at hlt
        exact hlt.le
      rw [abs_one]
      rw [show |counterexampleLambda N K j - 1| = 1 - counterexampleLambda N K j by
        rw [abs_of_nonpos]
        · ring
        · linarith]
      ring
    · rw [if_neg hxlast]
      rw [abs_of_nonneg]
      have hnonneg : 0 ≤ counterexampleLambda N K x := by
        have hx_pos : 0 < x.val := by omega
        have hlt := counterexampleLambda_strictMono N K hK
          (show (0 : Fin (N + 2)) < x by exact Fin.mk_lt_mk.mpr (by
            exact hx_pos))
        rw [show counterexampleLambda N K (0 : Fin (N + 2)) = 0 by
          simpa using counterexampleLambda_zero N K] at hlt
        exact hlt.le
      exact hnonneg
  ]

theorem counterexample_log_tilt_eq_sums (N K : ℕ) (hK : 2 ≤ K) :
    Real.log (counterexampleTilt N K) =
      -Real.log (Real.sqrt 2)
        - (∑ i : Fin (N + 1), Real.log (1 - counterexampleLambda N K i.castSucc)) / 2
        + (∑ i : Fin (N + 1), Real.log (counterexampleLambda N K i.succ)) / 2 := by
  let Δ₀ := counterexampleDelta N K ⟨0, by omega⟩
  let Δs := counterexampleDelta N K (Fin.last (N + 1))
  have hΔ₀_pos : 0 < Δ₀ := counterexampleDelta_pos N K hK ⟨0, by omega⟩
  have hΔs_pos : 0 < Δs := counterexampleDelta_pos N K hK (Fin.last (N + 1))
  have hA_pos : 0 < counterexampleA₁ N K := by
    unfold counterexampleA₁
    exact Real.sqrt_pos.mpr (div_pos hΔs_pos hΔ₀_pos)
  have hsqrtquot_pos : 0 < Real.sqrt (Δs / Δ₀) :=
    Real.sqrt_pos.mpr (div_pos hΔs_pos hΔ₀_pos)
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hδ0 := counterexampleDelta_zero_formula N K hK
  have hδs := counterexampleDelta_last_formula N K hK
  have hδ0' : Δ₀ = ∏ i : Fin (N + 1), counterexampleLambda N K i.succ := by
    simpa [Δ₀] using hδ0
  have hδs' : Δs = ∏ i : Fin (N + 1), (1 - counterexampleLambda N K i.castSucc) := by
    simpa [Δs] using hδs
  unfold counterexampleTilt counterexampleA₁
  change Real.log (1 / (Real.sqrt 2 * Real.sqrt (Δs / Δ₀))) = _
  rw [Real.log_div one_ne_zero (mul_ne_zero hsqrt2_pos.ne' hsqrtquot_pos.ne')]
  rw [Real.log_one, zero_sub]
  rw [Real.log_mul hsqrt2_pos.ne' hsqrtquot_pos.ne']
  rw [Real.log_sqrt (div_pos hΔs_pos hΔ₀_pos).le]
  rw [Real.log_div hΔs_pos.ne' hΔ₀_pos.ne']
  rw [hδ0', hδs']
  rw [Real.log_prod, Real.log_prod]
  · ring
  · intro i _hi
    have hlt := counterexampleLambda_strictMono N K hK
      (show (0 : Fin (N + 2)) < i.succ by simp)
    rw [show counterexampleLambda N K (0 : Fin (N + 2)) = 0 by
      simpa using counterexampleLambda_zero N K] at hlt
    exact hlt.ne'
  · intro i _hi
    have hlast : counterexampleLambda N K (Fin.last (N + 1)) = 1 :=
      counterexampleLambda_last N K (by omega)
    have hlt := counterexampleLambda_strictMono N K hK (Fin.castSucc_lt_last i)
    rw [hlast] at hlt
    linarith

theorem counterexampleLambda_one_eq_rpow_neg (N K : ℕ) (_hK : 2 ≤ K) :
    counterexampleLambda N K ⟨1, by omega⟩ = (K : ℝ) ^ (-(N : ℝ)) := by
  rw [counterexampleLambda, counterexampleExponent, counterexampleDegree]
  simp

theorem counterexampleLambda_castSucc_tendsto_zero (N : ℕ) (_hN : 1 ≤ N) (i : Fin (N + 1)) :
    Filter.Tendsto
      (fun K : ℕ => counterexampleLambda N K i.castSucc)
      Filter.atTop (nhds 0) := by
  by_cases hi0 : i.val = 0
  · refine tendsto_const_nhds.congr' ?_
    refine Filter.eventually_atTop.2 ⟨2, ?_⟩
    intro K hK
    have hi : i.castSucc = (0 : Fin (N + 2)) := Fin.ext (by simpa using hi0)
    rw [hi]
    exact (counterexampleLambda_zero N K).symm
  · have hpos : 0 < ((N + 1 - i.val : ℕ) : ℝ) := by
      have hi_le : i.val ≤ N := by omega
      have hsub_pos : 0 < N + 1 - i.val := by omega
      exact_mod_cast hsub_pos
    have hlim :
        Filter.Tendsto
          (fun K : ℕ => (K : ℝ) ^ (-(((N + 1 - i.val : ℕ) : ℝ))))
          Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hpos).comp tendsto_natCast_atTop_atTop
    refine hlim.congr' ?_
    refine Filter.eventually_atTop.2 ⟨2, ?_⟩
    intro K hK
    change (K : ℝ) ^ (-(((N + 1 - i.val : ℕ) : ℝ))) =
      counterexampleLambda N K i.castSucc
    unfold counterexampleLambda counterexampleExponent counterexampleDegree
    have hK_pos : 0 < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
    have hnum_ne : (K : ℝ) ^ (i.val - 1) ≠ 0 := pow_ne_zero _ hK_pos.ne'
    have hq_ne : (K : ℝ) ^ (N + 1 - i.val) ≠ 0 := pow_ne_zero _ hK_pos.ne'
    have hpowN :
        (K : ℝ) ^ N =
          (K : ℝ) ^ (i.val - 1) * (K : ℝ) ^ (N + 1 - i.val) := by
      rw [← pow_add]
      congr
      have hival_pos : 1 ≤ i.val := by omega
      have hival_le : i.val ≤ N := by omega
      omega
    rw [if_neg (by simpa [Fin.val_castSucc] using hi0)]
    simp only [Fin.val_castSucc, Nat.cast_pow]
    rw [Real.rpow_neg hK_pos.le, Real.rpow_natCast]
    rw [hpowN]
    field_simp [hnum_ne, hq_ne]

theorem counterexample_log_lambda_succ_mul_first_tendsto_zero
    (N : ℕ) (hN : 1 ≤ N) (i : Fin (N + 1)) :
    Filter.Tendsto
      (fun K : ℕ =>
        Real.log (counterexampleLambda N K i.succ) * (K : ℝ) ^ (-(N : ℝ)))
      Filter.atTop (nhds 0) := by
  by_cases hilast : i.val = N
  · refine tendsto_const_nhds.congr' ?_
    refine Filter.eventually_atTop.2 ⟨2, ?_⟩
    intro K hK
    have hi : i.succ = Fin.last (N + 1) := Fin.ext (by
      simp [Fin.val_succ, Fin.val_last, hilast])
    simp [hi, counterexampleLambda_last N K (by omega : 0 < K)]
  · have hbase := (counterexample_log_nat_mul_rpow_neg_tendsto_zero N hN).const_mul
      ((i.val : ℝ) - (N : ℝ))
    rw [mul_zero] at hbase
    refine hbase.congr' ?_
    refine Filter.eventually_atTop.2 ⟨2, ?_⟩
    intro K hK
    have hK_pos : 0 < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
    have hnum_ne : (K : ℝ) ^ i.val ≠ 0 := pow_ne_zero _ hK_pos.ne'
    have hden_ne : (K : ℝ) ^ N ≠ 0 := pow_ne_zero _ hK_pos.ne'
    unfold counterexampleLambda counterexampleExponent counterexampleDegree
    simp only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast, Fin.val_succ,
      Nat.add_eq_zero_iff, Fin.val_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      add_tsub_cancel_right, Nat.cast_pow]
    rw [Real.log_div hnum_ne hden_ne, Real.log_pow, Real.log_pow]
    ring

theorem counterexample_log_lambda_succ_mul_rpow_neg_tendsto_zero
    (N q : ℕ) (hq : 1 ≤ q) (i : Fin (N + 1)) :
    Filter.Tendsto
      (fun K : ℕ =>
        Real.log (counterexampleLambda N K i.succ) * (K : ℝ) ^ (-(q : ℝ)))
      Filter.atTop (nhds 0) := by
  by_cases hilast : i.val = N
  · refine tendsto_const_nhds.congr' ?_
    refine Filter.eventually_atTop.2 ⟨2, ?_⟩
    intro K hK
    have hi : i.succ = Fin.last (N + 1) := Fin.ext (by
      simp [Fin.val_succ, Fin.val_last, hilast])
    simp [hi, counterexampleLambda_last N K (by omega : 0 < K)]
  · have hbase := (counterexample_log_nat_mul_rpow_neg_tendsto_zero q hq).const_mul
      ((i.val : ℝ) - (N : ℝ))
    rw [mul_zero] at hbase
    refine hbase.congr' ?_
    refine Filter.eventually_atTop.2 ⟨2, ?_⟩
    intro K hK
    have hK_pos : 0 < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
    have hnum_ne : (K : ℝ) ^ i.val ≠ 0 := pow_ne_zero _ hK_pos.ne'
    have hden_ne : (K : ℝ) ^ N ≠ 0 := pow_ne_zero _ hK_pos.ne'
    unfold counterexampleLambda counterexampleExponent counterexampleDegree
    simp only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast, Fin.val_succ,
      Nat.add_eq_zero_iff, Fin.val_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      add_tsub_cancel_right, Nat.cast_pow]
    rw [Real.log_div hnum_ne hden_ne, Real.log_pow, Real.log_pow]
    ring

theorem counterexample_log_tilt_mul_rpow_neg_tendsto_zero
    (N q : ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q) :
    Filter.Tendsto
      (fun K : ℕ => (K : ℝ) ^ (-(q : ℝ)) * Real.log (counterexampleTilt N K))
      Filter.atTop (nhds 0) := by
  have hdecay :
      Filter.Tendsto (fun K : ℕ => (K : ℝ) ^ (-(q : ℝ))) Filter.atTop (nhds 0) := by
    exact (tendsto_rpow_neg_atTop (by positivity : 0 < (q : ℝ))).comp
      tendsto_natCast_atTop_atTop
  have hconst :
      Filter.Tendsto
        (fun K : ℕ => (-Real.log (Real.sqrt 2)) * (K : ℝ) ^ (-(q : ℝ)))
        Filter.atTop (nhds 0) := by
    simpa using hdecay.const_mul (-Real.log (Real.sqrt 2))
  have hlastSum :
      Filter.Tendsto
        (fun K : ℕ =>
          (∑ i : Fin (N + 1),
            Real.log (1 - counterexampleLambda N K i.castSucc)) *
            (K : ℝ) ^ (-(q : ℝ)))
        Filter.atTop (nhds 0) := by
    have hlastSum' :
        Filter.Tendsto
          (fun K : ℕ =>
            ∑ i : Fin (N + 1),
              Real.log (1 - counterexampleLambda N K i.castSucc) *
                (K : ℝ) ^ (-(q : ℝ)))
          Filter.atTop (nhds 0) := by
      have hsum := tendsto_finset_sum Finset.univ (fun (i : Fin (N + 1)) _hi => by
        have harg :
            Filter.Tendsto (fun K : ℕ => 1 - counterexampleLambda N K i.castSucc)
              Filter.atTop (nhds 1) := by
          simpa using tendsto_const_nhds.sub (counterexampleLambda_castSucc_tendsto_zero
            N hN i)
        have hlog :
            Filter.Tendsto
              (fun K : ℕ => Real.log (1 - counterexampleLambda N K i.castSucc))
              Filter.atTop (nhds 0) := by
          have h := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
            harg
          simpa using h
        exact hlog.mul hdecay)
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_zero] using hsum
    simpa only [Finset.sum_mul] using hlastSum'
  have hzeroSum :
      Filter.Tendsto
        (fun K : ℕ =>
          (∑ i : Fin (N + 1), Real.log (counterexampleLambda N K i.succ)) *
            (K : ℝ) ^ (-(q : ℝ)))
        Filter.atTop (nhds 0) := by
    have hzeroSum' :
        Filter.Tendsto
          (fun K : ℕ =>
            ∑ i : Fin (N + 1),
              Real.log (counterexampleLambda N K i.succ) * (K : ℝ) ^ (-(q : ℝ)))
          Filter.atTop (nhds 0) := by
      simpa using tendsto_finset_sum Finset.univ
        (fun i _hi => counterexample_log_lambda_succ_mul_rpow_neg_tendsto_zero N q hq i)
    simpa only [Finset.sum_mul] using hzeroSum'
  have hcombo := (hconst.sub (hlastSum.const_mul ((2 : ℝ)⁻¹))).add
    (hzeroSum.const_mul ((2 : ℝ)⁻¹))
  have hcombo0 : 0 - (2 : ℝ)⁻¹ * 0 + (2 : ℝ)⁻¹ * 0 = 0 := by ring
  rw [hcombo0] at hcombo
  refine hcombo.congr' ?_
  refine Filter.eventually_atTop.2 ⟨2, ?_⟩
  intro K hK
  change -Real.log (Real.sqrt 2) * (K : ℝ) ^ (-(q : ℝ)) -
        (2 : ℝ)⁻¹ *
          ((∑ i : Fin (N + 1),
            Real.log (1 - counterexampleLambda N K i.castSucc)) *
              (K : ℝ) ^ (-(q : ℝ))) +
        (2 : ℝ)⁻¹ *
          ((∑ i : Fin (N + 1), Real.log (counterexampleLambda N K i.succ)) *
            (K : ℝ) ^ (-(q : ℝ))) =
      (K : ℝ) ^ (-(q : ℝ)) * Real.log (counterexampleTilt N K)
  rw [counterexample_log_tilt_eq_sums N K hK]
  ring

/-- Logarithmic form of the exponent-`1` small-power estimate:
`log T * (-2 λ_1) → 0`. -/
theorem counterexample_one_tilt_log_mul_lambda_tendsto_zero
    (N : ℕ) (hN : 1 ≤ N) :
    Filter.Tendsto
      (fun K : ℕ =>
        Real.log (counterexampleTilt N K) *
          (-2 * counterexampleLambda N K ⟨1, by omega⟩))
      Filter.atTop
      (nhds 0) := by
  have hlambda1_tendsto :
      Filter.Tendsto (fun K : ℕ => (K : ℝ) ^ (-(N : ℝ))) Filter.atTop (nhds 0) := by
    exact (tendsto_rpow_neg_atTop (by positivity : 0 < (N : ℝ))).comp
      tendsto_natCast_atTop_atTop
  have hconst :
      Filter.Tendsto
        (fun K : ℕ => (-Real.log (Real.sqrt 2)) * (K : ℝ) ^ (-(N : ℝ)))
        Filter.atTop (nhds 0) := by
    simpa using hlambda1_tendsto.const_mul (-Real.log (Real.sqrt 2))
  have hlastSum :
      Filter.Tendsto
        (fun K : ℕ =>
          (∑ i : Fin (N + 1),
            Real.log (1 - counterexampleLambda N K i.castSucc)) *
            (K : ℝ) ^ (-(N : ℝ)))
        Filter.atTop (nhds 0) := by
    have hlastSum' :
        Filter.Tendsto
          (fun K : ℕ =>
            ∑ i : Fin (N + 1),
              Real.log (1 - counterexampleLambda N K i.castSucc) *
                (K : ℝ) ^ (-(N : ℝ)))
          Filter.atTop (nhds 0) := by
      have hsum := tendsto_finset_sum Finset.univ (fun (i : Fin (N + 1)) _hi => by
        have harg :
            Filter.Tendsto (fun K : ℕ => 1 - counterexampleLambda N K i.castSucc)
              Filter.atTop (nhds 1) := by
          simpa using tendsto_const_nhds.sub (counterexampleLambda_castSucc_tendsto_zero
            N hN i)
        have hlog :
            Filter.Tendsto
              (fun K : ℕ => Real.log (1 - counterexampleLambda N K i.castSucc))
              Filter.atTop (nhds 0) := by
          have h := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
            harg
          simpa using h
        exact hlog.mul hlambda1_tendsto)
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_zero] using hsum
    simpa only [Finset.sum_mul] using hlastSum'
  have hzeroSum :
      Filter.Tendsto
        (fun K : ℕ =>
          (∑ i : Fin (N + 1), Real.log (counterexampleLambda N K i.succ)) *
            (K : ℝ) ^ (-(N : ℝ)))
        Filter.atTop (nhds 0) := by
    have hzeroSum' :
        Filter.Tendsto
          (fun K : ℕ =>
            ∑ i : Fin (N + 1),
              Real.log (counterexampleLambda N K i.succ) * (K : ℝ) ^ (-(N : ℝ)))
          Filter.atTop (nhds 0) := by
      simpa using tendsto_finset_sum Finset.univ
        (fun i _hi => counterexample_log_lambda_succ_mul_first_tendsto_zero N hN i)
    simpa only [Finset.sum_mul] using hzeroSum'
  have hlogTiltTimes :
      Filter.Tendsto
        (fun K : ℕ => (K : ℝ) ^ (-(N : ℝ)) * Real.log (counterexampleTilt N K))
        Filter.atTop (nhds 0) := by
    have hcombo := (hconst.sub (hlastSum.const_mul ((2 : ℝ)⁻¹))).add
      (hzeroSum.const_mul ((2 : ℝ)⁻¹))
    have hcombo0 : 0 - (2 : ℝ)⁻¹ * 0 + (2 : ℝ)⁻¹ * 0 = 0 := by ring
    rw [hcombo0] at hcombo
    simpa [div_eq_mul_inv, mul_add, mul_sub, add_mul, sub_eq_add_neg, mul_assoc,
      mul_comm, mul_left_comm] using hcombo.congr' (by
        refine Filter.eventually_atTop.2 ⟨2, ?_⟩
        intro K hK
        have hK_pos : 0 < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
        change -Real.log (Real.sqrt 2) * (K : ℝ) ^ (-(N : ℝ)) -
              (2 : ℝ)⁻¹ *
                ((∑ i : Fin (N + 1),
                  Real.log (1 - counterexampleLambda N K i.castSucc)) *
                    (K : ℝ) ^ (-(N : ℝ))) +
              (2 : ℝ)⁻¹ *
                ((∑ i : Fin (N + 1), Real.log (counterexampleLambda N K i.succ)) *
                  (K : ℝ) ^ (-(N : ℝ))) =
            ((K : ℝ) ^ N)⁻¹ * Real.log (counterexampleTilt N K)
        rw [← Real.rpow_natCast (K : ℝ) N]
        rw [← Real.rpow_neg hK_pos.le (N : ℝ)]
        rw [counterexample_log_tilt_eq_sums N K hK]
        ring)
  have htarget : Filter.Tendsto
      (fun K : ℕ => -2 * ((K : ℝ) ^ (-(N : ℝ)) * Real.log (counterexampleTilt N K)))
      Filter.atTop (nhds 0) := by
    simpa using hlogTiltTimes.const_mul (-2)
  refine htarget.congr' ?_
  refine Filter.eventually_atTop.2 ⟨2, ?_⟩
  intro K hK
  change -2 * ((K : ℝ) ^ (-(N : ℝ)) * Real.log (counterexampleTilt N K)) =
    Real.log (counterexampleTilt N K) *
      (-2 * counterexampleLambda N K ⟨1, by omega⟩)
  rw [show counterexampleLambda N K ⟨1, by omega⟩ = (K : ℝ) ^ (-(N : ℝ)) by
    exact counterexampleLambda_one_eq_rpow_neg N K hK]
  ring

/-- The small exponent attached to the exponent-`1` term does not change the limit:
`T^{-2λ_1} → 1`. -/
theorem counterexample_one_tilt_small_power_tendsto
    (N : ℕ) (hN : 1 ≤ N) :
    Filter.Tendsto
      (fun K : ℕ =>
        counterexampleTilt N K ^ (-2 * counterexampleLambda N K ⟨1, by omega⟩))
      Filter.atTop
      (nhds 1) := by
  have hexp :
      Filter.Tendsto
        (fun K : ℕ =>
          Real.exp
            (Real.log (counterexampleTilt N K) *
              (-2 * counterexampleLambda N K ⟨1, by omega⟩)))
        Filter.atTop
        (nhds 1) := by
    have h := Real.continuous_exp.continuousAt.tendsto.comp
      (counterexample_one_tilt_log_mul_lambda_tendsto_zero N hN)
    simpa using h
  refine hexp.congr' ?_
  filter_upwards [eventually_counterexampleTilt_pos N] with K hT_pos
  rw [Real.rpow_def_of_pos hT_pos]

theorem counterexampleLambda_interior_eq_rpow_neg
    (N K : ℕ) (hK : 2 ≤ K) (j : Fin (N + 2))
    (hj0 : j.val ≠ 0) (hjlast : j.val ≠ N + 1) :
    counterexampleLambda N K j = (K : ℝ) ^ (-((N + 1 - j.val : ℕ) : ℝ)) := by
  have hK_pos : 0 < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hnum_ne : (K : ℝ) ^ (j.val - 1) ≠ 0 := pow_ne_zero _ hK_pos.ne'
  have hden_ne : (K : ℝ) ^ N ≠ 0 := pow_ne_zero _ hK_pos.ne'
  have hjpos : 1 ≤ j.val := by omega
  have hjleN : j.val ≤ N := by
    have hjlt : j.val < N + 2 := j.isLt
    omega
  unfold counterexampleLambda counterexampleExponent counterexampleDegree
  rw [if_neg hj0]
  simp only [Nat.cast_pow]
  rw [Real.rpow_neg hK_pos.le, Real.rpow_natCast]
  have hq_ne : (K : ℝ) ^ (N + 1 - j.val) ≠ 0 := pow_ne_zero _ hK_pos.ne'
  have hpowN :
      (K : ℝ) ^ N =
        (K : ℝ) ^ (j.val - 1) * (K : ℝ) ^ (N + 1 - j.val) := by
    rw [← pow_add]
    congr
    omega
  rw [hpowN]
  field_simp [hnum_ne, hq_ne]

theorem counterexampleLambda_div_tendsto_zero_of_val_lt
    (N : ℕ) (i j : Fin (N + 2))
    (hi0 : i.val ≠ 0) (hilast : i.val ≠ N + 1)
    (hj0 : j.val ≠ 0) (hjlast : j.val ≠ N + 1)
    (hij : i.val < j.val) :
    Filter.Tendsto
      (fun K : ℕ => counterexampleLambda N K i / counterexampleLambda N K j)
      Filter.atTop
      (nhds 0) := by
  let q : ℕ := j.val - i.val
  have hq_pos : 0 < (q : ℝ) := by
    dsimp [q]
    exact_mod_cast (by omega : 0 < j.val - i.val)
  have hlim :
      Filter.Tendsto
        (fun K : ℕ => (K : ℝ) ^ (-(q : ℝ)))
        Filter.atTop
        (nhds 0) :=
    (tendsto_rpow_neg_atTop hq_pos).comp tendsto_natCast_atTop_atTop
  refine hlim.congr' ?_
  refine Filter.eventually_atTop.2 ⟨2, ?_⟩
  intro K hK
  change (K : ℝ) ^ (-(q : ℝ)) =
    counterexampleLambda N K i / counterexampleLambda N K j
  have hK_pos : 0 < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hilambda := counterexampleLambda_interior_eq_rpow_neg N K hK i hi0 hilast
  have hjlambda := counterexampleLambda_interior_eq_rpow_neg N K hK j hj0 hjlast
  have hqi_nonzero :
      (K : ℝ) ^ (N + 1 - i.val) ≠ 0 := pow_ne_zero _ hK_pos.ne'
  have hqj_nonzero :
      (K : ℝ) ^ (N + 1 - j.val) ≠ 0 := pow_ne_zero _ hK_pos.ne'
  rw [hilambda, hjlambda]
  rw [Real.rpow_neg hK_pos.le, Real.rpow_natCast]
  rw [Real.rpow_neg hK_pos.le, Real.rpow_natCast]
  rw [Real.rpow_neg hK_pos.le, Real.rpow_natCast]
  have hpow :
      (K : ℝ) ^ (N + 1 - i.val) =
        (K : ℝ) ^ (N + 1 - j.val) * (K : ℝ) ^ q := by
    dsimp [q]
    rw [← pow_add]
    congr
    omega
  rw [hpow]
  field_simp [hqi_nonzero, hqj_nonzero, pow_ne_zero q hK_pos.ne']

theorem counterexampleDeltaZeroDivFactor_tendsto
    (N : ℕ) (_hN : 1 ≤ N) (j l : Fin (N + 2))
    (hj0 : j.val ≠ 0) (hjlast : j.val ≠ N + 1) :
    Filter.Tendsto
      (fun K : ℕ => counterexampleDeltaZeroDivFactor N K j l)
      Filter.atTop
      (nhds (counterexampleDeltaZeroDivFactorLimit N j l)) := by
  by_cases hl0 : l.val = 0
  · refine tendsto_const_nhds.congr' ?_
    refine Filter.eventually_atTop.2 ⟨0, ?_⟩
    intro K _hK
    simp [counterexampleDeltaZeroDivFactor, counterexampleDeltaZeroDivFactorLimit, hl0]
  · by_cases hlj : l = j
    · refine tendsto_const_nhds.congr' ?_
      refine Filter.eventually_atTop.2 ⟨0, ?_⟩
      intro K _hK
      simp [counterexampleDeltaZeroDivFactor, counterexampleDeltaZeroDivFactorLimit, hlj]
    · by_cases hllast : l.val = N + 1
      · have hlambda_j :
            Filter.Tendsto (fun K : ℕ => counterexampleLambda N K j)
              Filter.atTop (nhds 0) := by
          have hq : 1 ≤ N + 1 - j.val := by
            have hjlt : j.val < N + 2 := j.isLt
            omega
          have hlim :
              Filter.Tendsto
                (fun K : ℕ => (K : ℝ) ^ (-(((N + 1 - j.val : ℕ) : ℝ))))
                Filter.atTop
                (nhds 0) := by
            exact (tendsto_rpow_neg_atTop (by positivity : 0 < ((N + 1 - j.val : ℕ) : ℝ))).comp
              tendsto_natCast_atTop_atTop
          refine hlim.congr' ?_
          refine Filter.eventually_atTop.2 ⟨2, ?_⟩
          intro K hK
          exact (counterexampleLambda_interior_eq_rpow_neg N K hK j hj0 hjlast).symm
        have htend :
            Filter.Tendsto
              (fun K : ℕ => (1 - counterexampleLambda N K j)⁻¹)
              Filter.atTop
              (nhds 1) := by
          have hsub := (tendsto_const_nhds (x := (1 : ℝ))).sub hlambda_j
          have hinv := hsub.inv₀ (by norm_num : (1 - (0 : ℝ)) ≠ 0)
          simpa using hinv
        have htarget :
            Filter.Tendsto
              (fun K : ℕ => (1 - counterexampleLambda N K j)⁻¹)
              Filter.atTop
              (nhds (counterexampleDeltaZeroDivFactorLimit N j l)) := by
          simpa [counterexampleDeltaZeroDivFactorLimit, hlj, hllast] using htend
        refine htarget.congr' ?_
        refine Filter.eventually_atTop.2 ⟨0, ?_⟩
        intro K _hK
        simp [counterexampleDeltaZeroDivFactor, hlj, hllast]
      · by_cases hlt : l.val < j.val
        · have hl_last : l.val ≠ N + 1 := hllast
          have hratio :=
            counterexampleLambda_div_tendsto_zero_of_val_lt N l j hl0 hl_last
              hj0 hjlast hlt
          have hone_minus :
              Filter.Tendsto
                (fun K : ℕ => 1 - counterexampleLambda N K l / counterexampleLambda N K j)
                Filter.atTop
                (nhds 1) := by
            simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hratio
          have hcore :
              Filter.Tendsto
                (fun K : ℕ =>
                  (counterexampleLambda N K l / counterexampleLambda N K j) /
                    |1 - counterexampleLambda N K l / counterexampleLambda N K j|)
                Filter.atTop
                (nhds 0) := by
            have habs := (continuous_abs.continuousAt.tendsto.comp hone_minus).inv₀
              (by norm_num : |(1 : ℝ)| ≠ 0)
            simpa using hratio.mul habs
          have htarget :
              Filter.Tendsto
                (fun K : ℕ =>
                  (counterexampleLambda N K l / counterexampleLambda N K j) /
                    |1 - counterexampleLambda N K l / counterexampleLambda N K j|)
                Filter.atTop
                (nhds (counterexampleDeltaZeroDivFactorLimit N j l)) := by
            simpa [counterexampleDeltaZeroDivFactorLimit, hl0, hlj, hllast, hlt]
              using hcore
          refine htarget.congr' ?_
          refine Filter.eventually_atTop.2 ⟨2, ?_⟩
          intro K hK
          have hlambdaj_pos : 0 < counterexampleLambda N K j := by
            have hj_pos : 0 < j.val := by omega
            have hlt0 := counterexampleLambda_strictMono N K hK
              (show (0 : Fin (N + 2)) < j by exact Fin.mk_lt_mk.mpr hj_pos)
            rw [show counterexampleLambda N K (0 : Fin (N + 2)) = 0 by
              simpa using counterexampleLambda_zero N K] at hlt0
            exact hlt0
          have hlambdaj_ne : counterexampleLambda N K j ≠ 0 := hlambdaj_pos.ne'
          change
            counterexampleLambda N K l / counterexampleLambda N K j /
                |1 - counterexampleLambda N K l / counterexampleLambda N K j| =
              counterexampleDeltaZeroDivFactor N K j l
          unfold counterexampleDeltaZeroDivFactor
          rw [if_neg hl0, if_neg hlj, if_neg hllast]
          rw [show |counterexampleLambda N K j - counterexampleLambda N K l| =
              counterexampleLambda N K j *
                |1 - counterexampleLambda N K l / counterexampleLambda N K j| by
            rw [← abs_of_pos hlambdaj_pos, ← abs_mul]
            congr 1
            field_simp [hlambdaj_ne]
            rw [abs_of_pos hlambdaj_pos]
            ring]
          field_simp [hlambdaj_ne]
        · have hj_lt_l : j.val < l.val := by
            have hle : j.val ≤ l.val := by omega
            exact lt_of_le_of_ne hle (by
              intro h
              exact hlj (Fin.ext h.symm))
          have hl_last : l.val ≠ N + 1 := hllast
          have hratio :=
            counterexampleLambda_div_tendsto_zero_of_val_lt N j l hj0 hjlast
              hl0 hl_last hj_lt_l
          have hone_minus :
              Filter.Tendsto
                (fun K : ℕ => 1 - counterexampleLambda N K j / counterexampleLambda N K l)
                Filter.atTop
                (nhds 1) := by
            simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hratio
          have hcore :
              Filter.Tendsto
                (fun K : ℕ =>
                  1 / |1 - counterexampleLambda N K j / counterexampleLambda N K l|)
                Filter.atTop
                (nhds 1) := by
            have habs := continuous_abs.continuousAt.tendsto.comp hone_minus
            have hinv := habs.inv₀ (by norm_num : |(1 : ℝ)| ≠ 0)
            simpa using hinv
          have htarget :
              Filter.Tendsto
                (fun K : ℕ =>
                  1 / |1 - counterexampleLambda N K j / counterexampleLambda N K l|)
                Filter.atTop
                (nhds (counterexampleDeltaZeroDivFactorLimit N j l)) := by
            simpa [counterexampleDeltaZeroDivFactorLimit, hl0, hlj, hllast, hlt]
              using hcore
          refine htarget.congr' ?_
          refine Filter.eventually_atTop.2 ⟨2, ?_⟩
          intro K hK
          have hlambdal_pos : 0 < counterexampleLambda N K l := by
            have hl_pos : 0 < l.val := by omega
            have hlt0 := counterexampleLambda_strictMono N K hK
              (show (0 : Fin (N + 2)) < l by exact Fin.mk_lt_mk.mpr hl_pos)
            rw [show counterexampleLambda N K (0 : Fin (N + 2)) = 0 by
              simpa using counterexampleLambda_zero N K] at hlt0
            exact hlt0
          have hlambdal_ne : counterexampleLambda N K l ≠ 0 := hlambdal_pos.ne'
          change 1 / |1 - counterexampleLambda N K j / counterexampleLambda N K l| =
            counterexampleDeltaZeroDivFactor N K j l
          unfold counterexampleDeltaZeroDivFactor
          rw [if_neg hl0, if_neg hlj, if_neg hllast]
          rw [show |counterexampleLambda N K j - counterexampleLambda N K l| =
              counterexampleLambda N K l *
                |counterexampleLambda N K j / counterexampleLambda N K l - 1| by
            rw [← abs_of_pos hlambdal_pos, ← abs_mul]
            congr 1
            field_simp [hlambdal_ne]
            rw [abs_of_pos hlambdal_pos]
            ring]
          rw [show |counterexampleLambda N K j / counterexampleLambda N K l - 1| =
              |1 - counterexampleLambda N K j / counterexampleLambda N K l| by
            rw [← abs_neg]
            congr 1
            ring]
          field_simp [hlambdal_ne]

theorem counterexample_interior_tilt_small_power_tendsto_one
    (N : ℕ) (hN : 1 ≤ N) (j : Fin (N + 2))
    (hj0 : j.val ≠ 0) (hjlast : j.val ≠ N + 1) :
    Filter.Tendsto
      (fun K : ℕ =>
        counterexampleTilt N K ^ (-2 * counterexampleLambda N K j))
      Filter.atTop
      (nhds 1) := by
  let q : ℕ := N + 1 - j.val
  have hq : 1 ≤ q := by
    dsimp [q]
    have hjlt : j.val < N + 2 := j.isLt
    omega
  have hlog :
      Filter.Tendsto
        (fun K : ℕ =>
          Real.log (counterexampleTilt N K) *
            (-2 * (K : ℝ) ^ (-(q : ℝ))))
        Filter.atTop (nhds 0) := by
    have h := (counterexample_log_tilt_mul_rpow_neg_tendsto_zero N q hN hq).const_mul (-2)
    rw [mul_zero] at h
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  have hlog' :
      Filter.Tendsto
        (fun K : ℕ =>
          Real.log (counterexampleTilt N K) *
            (-2 * counterexampleLambda N K j))
        Filter.atTop (nhds 0) := by
    refine hlog.congr' ?_
    refine Filter.eventually_atTop.2 ⟨2, ?_⟩
    intro K hK
    change Real.log (counterexampleTilt N K) * (-2 * (K : ℝ) ^ (-(q : ℝ))) =
      Real.log (counterexampleTilt N K) * (-2 * counterexampleLambda N K j)
    rw [← counterexampleLambda_interior_eq_rpow_neg N K hK j hj0 hjlast]
  have hexp :
      Filter.Tendsto
        (fun K : ℕ =>
          Real.exp
            (Real.log (counterexampleTilt N K) *
              (-2 * counterexampleLambda N K j)))
        Filter.atTop
        (nhds 1) := by
    have h := Real.continuous_exp.continuousAt.tendsto.comp hlog'
    simpa using h
  refine hexp.congr' ?_
  filter_upwards [eventually_counterexampleTilt_pos N] with K hT_pos
  rw [Real.rpow_def_of_pos hT_pos]

/-- The normalized second height term: `(A_2/A_1) T^{-2λ_2} → 1`.

This is the product of the tex proof's `R_1 → 1` and `T^{-2x_1} → 1`. -/
theorem counterexample_heightFormula_one_normalized_factor_tendsto
    (N : ℕ) (hN : 1 ≤ N) :
    Filter.Tendsto
      (fun K : ℕ =>
        (counterexampleHeightAmplitude N K ⟨1, by omega⟩ /
            counterexampleHeightAmplitude N K ⟨0, by omega⟩) *
          counterexampleTilt N K ^
            (-2 * counterexampleLambda N K ⟨1, by omega⟩))
      Filter.atTop
      (nhds 1) := by
  have hprod :=
    (counterexample_delta_zero_div_one_tendsto N hN).mul
      (counterexample_one_tilt_small_power_tendsto N hN)
  rw [one_mul] at hprod
  refine hprod.congr' ?_
  refine Filter.eventually_atTop.2 ⟨2, ?_⟩
  intro K hK
  dsimp
  exact congrArg
    (fun r : ℝ => r * counterexampleTilt N K ^ (-2 * counterexampleLambda N K (1 : Fin (N + 2))))
    (counterexampleHeightAmplitude_div_zero_eq_delta_ratio N K hK (1 : Fin (N + 2))).symm

/-- The second height term factors as the constant-term contribution times the normalized
middle factor. -/
theorem counterexample_heightFormula_one_term_eq_zero_term_mul_normalized_factor
    (N K : ℕ) (hK : 2 ≤ K) :
    counterexampleHeightAmplitude N K ⟨1, by omega⟩ *
        counterexampleTilt N K ^
          (1 - 2 * counterexampleLambda N K ⟨1, by omega⟩) =
      (counterexampleHeightAmplitude N K ⟨0, by omega⟩ *
        counterexampleTilt N K ^
          (1 - 2 * counterexampleLambda N K ⟨0, by omega⟩)) *
        ((counterexampleHeightAmplitude N K ⟨1, by omega⟩ /
            counterexampleHeightAmplitude N K ⟨0, by omega⟩) *
          counterexampleTilt N K ^
            (-2 * counterexampleLambda N K ⟨1, by omega⟩)) := by
  have hA₁_pos : 0 < counterexampleA₁ N K := by
    unfold counterexampleA₁
    exact Real.sqrt_pos.mpr (div_pos
      (counterexampleDelta_pos N K hK (Fin.last (N + 1)))
      (counterexampleDelta_pos N K hK ⟨0, by omega⟩))
  have hT_pos : 0 < counterexampleTilt N K := by
    unfold counterexampleTilt
    positivity
  have hH0_ne : counterexampleHeightAmplitude N K ⟨0, by omega⟩ ≠ 0 := by
    rw [counterexampleHeightAmplitude_zero_eq_A₁ N K hK]
    exact hA₁_pos.ne'
  rw [counterexampleLambda_zero]
  norm_num
  change counterexampleHeightAmplitude N K ⟨1, by omega⟩ *
      counterexampleTilt N K ^ (1 + (-(2 * counterexampleLambda N K ⟨1, by omega⟩))) =
    counterexampleHeightAmplitude N K ⟨0, by omega⟩ * counterexampleTilt N K *
      (counterexampleHeightAmplitude N K ⟨1, by omega⟩ /
          counterexampleHeightAmplitude N K ⟨0, by omega⟩ *
        counterexampleTilt N K ^ (-(2 * counterexampleLambda N K ⟨1, by omega⟩)))
  rw [Real.rpow_add hT_pos, Real.rpow_one]
  field_simp [hH0_ne]

/-- The height-formula term indexed by the exponent `1` tends to `1/√2`. -/
theorem counterexample_heightFormula_one_term_tendsto
    (N : ℕ) (hN : 1 ≤ N) :
    Filter.Tendsto
      (fun K : ℕ =>
        counterexampleHeightAmplitude N K ⟨1, by omega⟩ *
          counterexampleTilt N K ^
            (1 - 2 * counterexampleLambda N K ⟨1, by omega⟩))
      Filter.atTop
      (nhds (1 / Real.sqrt 2)) := by
  have hprod :=
    (counterexample_heightFormula_zero_term_tendsto N hN).mul
      (counterexample_heightFormula_one_normalized_factor_tendsto N hN)
  have hlimit : (1 / Real.sqrt 2) * 1 = 1 / Real.sqrt 2 := by ring
  rw [hlimit] at hprod
  refine hprod.congr' ?_
  refine Filter.eventually_atTop.2 ⟨2, ?_⟩
  intro K hK
  exact (counterexample_heightFormula_one_term_eq_zero_term_mul_normalized_factor N K hK).symm

/-- The leading height amplitude is the reciprocal of `A_1`. -/
theorem counterexampleHeightAmplitude_last_mul_A₁ (N K : ℕ) (hK : 2 ≤ K) :
    counterexampleHeightAmplitude N K (Fin.last (N + 1)) * counterexampleA₁ N K = 1 := by
  let Δ₀ := counterexampleDelta N K ⟨0, by omega⟩
  let Δs := counterexampleDelta N K (Fin.last (N + 1))
  have hΔ₀_pos : 0 < Δ₀ := counterexampleDelta_pos N K hK ⟨0, by omega⟩
  have hΔs_pos : 0 < Δs := counterexampleDelta_pos N K hK (Fin.last (N + 1))
  have hsqrt_Δ₀_ne : Real.sqrt Δ₀ ≠ 0 := Real.sqrt_ne_zero hΔ₀_pos.le |>.mpr hΔ₀_pos.ne'
  have hsqrt_Δs_ne : Real.sqrt Δs ≠ 0 := Real.sqrt_ne_zero hΔs_pos.le |>.mpr hΔs_pos.ne'
  unfold counterexampleHeightAmplitude counterexampleA₁
  change (Real.sqrt (Δ₀ * Δs) / Δs) * Real.sqrt (Δs / Δ₀) = 1
  rw [Real.sqrt_div hΔs_pos.le]
  rw [Real.sqrt_mul hΔ₀_pos.le]
  field_simp [hsqrt_Δ₀_ne, hsqrt_Δs_ne]
  ring_nf
  rw [Real.sq_sqrt hΔs_pos.le]

/-- The leading height-formula term is exactly `√2`. -/
theorem counterexample_heightFormula_last_term_eq (N K : ℕ) (hK : 2 ≤ K) :
    counterexampleHeightAmplitude N K (Fin.last (N + 1)) *
        counterexampleTilt N K ^
          (1 - 2 * counterexampleLambda N K (Fin.last (N + 1))) =
      Real.sqrt 2 := by
  have hA₁_pos : 0 < counterexampleA₁ N K := by
    unfold counterexampleA₁
    exact Real.sqrt_pos.mpr (div_pos
      (counterexampleDelta_pos N K hK (Fin.last (N + 1)))
      (counterexampleDelta_pos N K hK ⟨0, by omega⟩))
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by norm_num : 0 < (2 : ℝ))
  rw [counterexampleLambda_last N K (by omega : 0 < K)]
  norm_num
  unfold counterexampleTilt
  rw [Real.rpow_neg_one]
  field_simp [hA₁_pos.ne', hsqrt2_ne]
  nlinarith [counterexampleHeightAmplitude_last_mul_A₁ N K hK]

/-- The height-formula term indexed by the leading exponent tends to `√2`. -/
theorem counterexample_heightFormula_last_term_tendsto
    (N : ℕ) (_hN : 1 ≤ N) :
    Filter.Tendsto
      (fun K : ℕ =>
        counterexampleHeightAmplitude N K (Fin.last (N + 1)) *
          counterexampleTilt N K ^
            (1 - 2 * counterexampleLambda N K (Fin.last (N + 1))))
      Filter.atTop
      (nhds (Real.sqrt 2)) := by
  refine tendsto_const_nhds.congr' ?_
  refine Filter.eventually_atTop.2 ⟨2, ?_⟩
  intro K hK
  exact (counterexample_heightFormula_last_term_eq N K hK).symm

/-- Pure delta-ratio part of the middle-term estimate:
`Δ₀ / Δⱼ → 0` for all middle indices after the exponent `1`. -/
theorem counterexample_delta_zero_div_factor_product_tendsto_zero
    (N : ℕ) (hN : 1 ≤ N) (j : Fin (N + 2))
    (hj0 : j.val ≠ 0) (hj1 : j.val ≠ 1) (hjlast : j.val ≠ N + 1) :
    Filter.Tendsto
      (fun K : ℕ => ∏ l : Fin (N + 2), counterexampleDeltaZeroDivFactor N K j l)
      Filter.atTop
      (nhds 0) := by
  have hprod :
      Filter.Tendsto
        (fun K : ℕ => ∏ l : Fin (N + 2), counterexampleDeltaZeroDivFactor N K j l)
        Filter.atTop
        (nhds (∏ l : Fin (N + 2), counterexampleDeltaZeroDivFactorLimit N j l)) := by
    exact tendsto_finset_prod Finset.univ (fun l _hl =>
      counterexampleDeltaZeroDivFactor_tendsto N hN j l hj0 hjlast)
  have hlimit : (∏ l : Fin (N + 2), counterexampleDeltaZeroDivFactorLimit N j l) = 0 := by
    rw [← Finset.prod_erase_mul (s := Finset.univ) (a := (⟨1, by omega⟩ : Fin (N + 2)))
      (f := fun l : Fin (N + 2) => counterexampleDeltaZeroDivFactorLimit N j l)
      (Finset.mem_univ _)]
    rw [show counterexampleDeltaZeroDivFactorLimit N j ⟨1, by omega⟩ = 0 by
      unfold counterexampleDeltaZeroDivFactorLimit
      rw [if_neg (by omega : (1 : ℕ) ≠ 0)]
      rw [if_neg (fun h : (⟨1, by omega⟩ : Fin (N + 2)) = j =>
        hj1 (by simpa using congrArg Fin.val h.symm))]
      rw [if_neg (by omega : (1 : ℕ) ≠ N + 1)]
      rw [if_pos (by omega : (1 : ℕ) < j.val)]]
    ring
  rw [hlimit] at hprod
  exact hprod

theorem counterexample_interior_delta_zero_div_tendsto_zero
    (N : ℕ) (hN : 1 ≤ N) (j : Fin (N + 2))
    (hj0 : j.val ≠ 0) (hj1 : j.val ≠ 1) (hjlast : j.val ≠ N + 1) :
    Filter.Tendsto
      (fun K : ℕ =>
        counterexampleDelta N K ⟨0, by omega⟩ / counterexampleDelta N K j)
      Filter.atTop
      (nhds 0) := by
  refine (counterexample_delta_zero_div_factor_product_tendsto_zero
    N hN j hj0 hj1 hjlast).congr' ?_
  refine Filter.eventually_atTop.2 ⟨2, ?_⟩
  intro K hK
  exact (counterexample_delta_zero_div_eq_prod_factor N K hK j hj0 hjlast).symm

/-- The normalized non-surviving height terms tend to zero.

This is the tex proof's estimate
`R_i T^{-2 x_i} → 0` for the middle indices other than the exponent `1`. -/
theorem counterexample_interior_delta_ratio_mul_tilt_power_tendsto_zero
    (N : ℕ) (hN : 1 ≤ N) (j : Fin (N + 2))
    (hj0 : j.val ≠ 0) (hj1 : j.val ≠ 1) (hjlast : j.val ≠ N + 1) :
    Filter.Tendsto
      (fun K : ℕ =>
        (counterexampleDelta N K ⟨0, by omega⟩ / counterexampleDelta N K j) *
          counterexampleTilt N K ^ (-2 * counterexampleLambda N K j))
      Filter.atTop
      (nhds 0) := by
  have hdelta := counterexample_interior_delta_zero_div_tendsto_zero
    N hN j hj0 hj1 hjlast
  have htilt := counterexample_interior_tilt_small_power_tendsto_one
    N hN j hj0 hjlast
  have hprod := hdelta.mul htilt
  simpa using hprod

theorem counterexample_heightFormula_interior_normalized_factor_tendsto_zero
    (N : ℕ) (hN : 1 ≤ N) (j : Fin (N + 2))
    (hj0 : j.val ≠ 0) (hj1 : j.val ≠ 1) (hjlast : j.val ≠ N + 1) :
    Filter.Tendsto
      (fun K : ℕ =>
        (counterexampleHeightAmplitude N K j /
            counterexampleHeightAmplitude N K ⟨0, by omega⟩) *
          counterexampleTilt N K ^ (-2 * counterexampleLambda N K j))
      Filter.atTop
      (nhds 0) := by
  refine (counterexample_interior_delta_ratio_mul_tilt_power_tendsto_zero
    N hN j hj0 hj1 hjlast).congr' ?_
  refine Filter.eventually_atTop.2 ⟨2, ?_⟩
  intro K hK
  exact congrArg
    (fun r : ℝ => r * counterexampleTilt N K ^ (-2 * counterexampleLambda N K j))
    (counterexampleHeightAmplitude_div_zero_eq_delta_ratio N K hK j).symm

/-- Any height-formula term factors as the constant-term contribution times its normalized
factor. -/
theorem counterexample_heightFormula_term_eq_zero_term_mul_normalized_factor
    (N K : ℕ) (hK : 2 ≤ K) (j : Fin (N + 2)) :
    counterexampleHeightAmplitude N K j *
        counterexampleTilt N K ^ (1 - 2 * counterexampleLambda N K j) =
      (counterexampleHeightAmplitude N K ⟨0, by omega⟩ *
        counterexampleTilt N K ^
          (1 - 2 * counterexampleLambda N K ⟨0, by omega⟩)) *
        ((counterexampleHeightAmplitude N K j /
            counterexampleHeightAmplitude N K ⟨0, by omega⟩) *
          counterexampleTilt N K ^ (-2 * counterexampleLambda N K j)) := by
  have hA₁_pos : 0 < counterexampleA₁ N K := by
    unfold counterexampleA₁
    exact Real.sqrt_pos.mpr (div_pos
      (counterexampleDelta_pos N K hK (Fin.last (N + 1)))
      (counterexampleDelta_pos N K hK ⟨0, by omega⟩))
  have hT_pos : 0 < counterexampleTilt N K := by
    unfold counterexampleTilt
    positivity
  have hH0_ne : counterexampleHeightAmplitude N K ⟨0, by omega⟩ ≠ 0 := by
    rw [counterexampleHeightAmplitude_zero_eq_A₁ N K hK]
    exact hA₁_pos.ne'
  rw [counterexampleLambda_zero]
  norm_num
  change counterexampleHeightAmplitude N K j *
      counterexampleTilt N K ^ (1 + (-(2 * counterexampleLambda N K j))) =
    counterexampleHeightAmplitude N K ⟨0, by omega⟩ * counterexampleTilt N K *
      (counterexampleHeightAmplitude N K j /
          counterexampleHeightAmplitude N K ⟨0, by omega⟩ *
        counterexampleTilt N K ^ (-(2 * counterexampleLambda N K j)))
  rw [Real.rpow_add hT_pos, Real.rpow_one]
  field_simp [hH0_ne]

/-- The remaining middle height-formula terms tend to zero. -/
theorem counterexample_heightFormula_interior_term_tendsto_zero
    (N : ℕ) (hN : 1 ≤ N) (j : Fin (N + 2))
    (hj0 : j.val ≠ 0) (hj1 : j.val ≠ 1) (hjlast : j.val ≠ N + 1) :
    Filter.Tendsto
      (fun K : ℕ =>
        counterexampleHeightAmplitude N K j *
          counterexampleTilt N K ^ (1 - 2 * counterexampleLambda N K j))
      Filter.atTop
      (nhds 0) := by
  have hprod :=
    (counterexample_heightFormula_zero_term_tendsto N hN).mul
      (counterexample_heightFormula_interior_normalized_factor_tendsto_zero
        N hN j hj0 hj1 hjlast)
  rw [mul_zero] at hprod
  refine hprod.congr' ?_
  refine Filter.eventually_atTop.2 ⟨2, ?_⟩
  intro K hK
  exact (counterexample_heightFormula_term_eq_zero_term_mul_normalized_factor N K hK j).symm

/-- Termwise form of Proposition `height` in the tex proof.

It packages the asymptotics of the Vandermonde products `Δ_j`, the identity `A_1 T = 1/√2`,
and the estimate `T^{-2 λ_j} → 1` for the small middle exponents. -/
theorem counterexample_heightFormula_term_tendsto
    (N : ℕ) (hN : 1 ≤ N) (j : Fin (N + 2)) :
    Filter.Tendsto
      (fun K : ℕ =>
        counterexampleHeightAmplitude N K j *
          counterexampleTilt N K ^ (1 - 2 * counterexampleLambda N K j))
      Filter.atTop
      (nhds (counterexampleHeightTermLimit N j)) := by
  by_cases hj0 : j.val = 0
  · have hj : j = ⟨0, by omega⟩ := Fin.ext hj0
    rw [hj]
    simpa [counterexampleHeightTermLimit] using
      counterexample_heightFormula_zero_term_tendsto N hN
  by_cases hj1 : j.val = 1
  · have hj : j = ⟨1, by omega⟩ := Fin.ext hj1
    rw [hj]
    simpa [counterexampleHeightTermLimit] using
      counterexample_heightFormula_one_term_tendsto N hN
  by_cases hjlast : j.val = N + 1
  · have hj : j = Fin.last (N + 1) := by
      exact Fin.ext (by simpa [Fin.val_last] using hjlast)
    rw [hj]
    have hN_ne_zero : N ≠ 0 := by omega
    simpa [counterexampleHeightTermLimit, hN_ne_zero] using
      counterexample_heightFormula_last_term_tendsto N hN
  · rw [counterexampleHeightTermLimit]
    rw [if_neg hj0, if_neg hj1, if_neg hjlast]
    exact counterexample_heightFormula_interior_term_tendsto_zero N hN j hj0 hj1 hjlast

/-- The limits of the height-formula terms sum to `2√2`. -/
theorem counterexampleHeightTermLimit_sum (N : ℕ) (hN : 1 ≤ N) :
    (∑ j : Fin (N + 2), counterexampleHeightTermLimit N j) = 2 * Real.sqrt 2 := by
  let a : Fin (N + 2) := ⟨0, by omega⟩
  let b : Fin (N + 2) := ⟨1, by omega⟩
  let c : Fin (N + 2) := Fin.last (N + 1)
  have hsum_small :
      (∑ j : Fin (N + 2), counterexampleHeightTermLimit N j) =
        ∑ j ∈ ({a, b, c} : Finset (Fin (N + 2))), counterexampleHeightTermLimit N j := by
    symm
    refine Finset.sum_subset ?_ ?_
    · simp
    · intro j _hjuniv hjsmall
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hjsmall
      have hj0 : j.val ≠ 0 := by
        intro h
        exact hjsmall.1 (Fin.ext h)
      have hj1 : j.val ≠ 1 := by
        intro h
        exact hjsmall.2.1 (Fin.ext h)
      have hjlast : j.val ≠ N + 1 := by
        intro h
        exact hjsmall.2.2 (Fin.ext (by simpa [c] using h))
      simp [counterexampleHeightTermLimit, hj0, hj1, hjlast]
  have ha_ne_b : a ≠ b := by
    intro h
    have := congr_arg Fin.val h
    simp [a, b] at this
  have ha_ne_c : a ≠ c := by
    intro h
    have := congr_arg Fin.val h
    simp [a, c] at this
  have hb_ne_c : b ≠ c := by
    intro h
    have := congr_arg Fin.val h
    simp [b, c] at this
    omega
  have hsmall :
      (∑ j ∈ ({a, b, c} : Finset (Fin (N + 2))), counterexampleHeightTermLimit N j) =
        counterexampleHeightTermLimit N a + counterexampleHeightTermLimit N b +
          counterexampleHeightTermLimit N c := by
    rw [Finset.sum_insert]
    · rw [Finset.sum_insert]
      · rw [Finset.sum_singleton]
        ring
      · simp [hb_ne_c]
    · simp [ha_ne_b, ha_ne_c]
  have hN_ne_zero : N ≠ 0 := by omega
  rw [hsum_small, hsmall]
  simp [a, b, c, counterexampleHeightTermLimit, hN_ne_zero]
  have hsqrt_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hsqrt_ne]
  nlinarith

/-- Proposition `height` in the tex proof, after rewriting `M(f_{N,K})` as its exact
`A_j T^(1-2λ_j)` expression. -/
theorem counterexample_heightFormula_tendsto
    (N : ℕ) (hN : 1 ≤ N) :
    Filter.Tendsto
      (fun K : ℕ => counterexampleHeightFormula N K)
      Filter.atTop
      (nhds (2 * Real.sqrt 2)) := by
  have hsum :
      Filter.Tendsto
        (fun K : ℕ =>
          ∑ j : Fin (N + 2),
            counterexampleHeightAmplitude N K j *
              counterexampleTilt N K ^ (1 - 2 * counterexampleLambda N K j))
        Filter.atTop
        (nhds (∑ j : Fin (N + 2), counterexampleHeightTermLimit N j)) := by
    exact tendsto_finset_sum Finset.univ
      (fun j _hj => counterexample_heightFormula_term_tendsto N hN j)
  rw [counterexampleHeightTermLimit_sum N hN] at hsum
  simpa [counterexampleHeightFormula] using hsum

/-- The height asymptotic computed in the tex proof, Proposition `height`. -/
theorem counterexample_coefficientRatio_tendsto_from_height_asymptotic
    (N : ℕ) (hN : 1 ≤ N) :
    Filter.Tendsto
      (fun K : ℕ => coefficientRatio (counterexamplePolynomial N K) (counterexampleDegree N K))
      Filter.atTop
      (nhds (2 * Real.sqrt 2)) := by
  refine (counterexample_heightFormula_tendsto N hN).congr' ?_
  refine Filter.eventually_atTop.2 ⟨2, ?_⟩
  intro K hK
  exact (counterexample_coefficientRatio_eq_heightFormula N K hN hK).symm

/-- The scale-invariant coefficient ratio has the limit computed in the tex height
proposition. -/
theorem counterexample_coefficientRatio_tendsto (N : ℕ) (hN : 1 ≤ N) :
    Filter.Tendsto
      (fun K : ℕ => coefficientRatio (counterexamplePolynomial N K) (counterexampleDegree N K))
      Filter.atTop
      (nhds (2 * Real.sqrt 2)) :=
  counterexample_coefficientRatio_tendsto_from_height_asymptotic N hN

/-- In particular, for fixed `N`, the coefficient ratio is eventually below `3`. -/
theorem eventually_counterexample_coefficientRatio_lt_three (N : ℕ) (hN : 1 ≤ N) :
    ∀ᶠ K in Filter.atTop,
      coefficientRatio (counterexamplePolynomial N K) (counterexampleDegree N K) < 3 := by
  have hlimit := counterexample_coefficientRatio_tendsto N hN
  have hlt : 2 * Real.sqrt 2 < 3 := by
    have hsqrt_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith
  exact hlimit.eventually (isOpen_Iio.mem_nhds hlt)

/-- Roots of the counterexample polynomial, counted with multiplicity, can be enumerated with
admissible arguments; moreover the `N + 1` positive-root copies can be selected explicitly from
that enumeration.

This is the root-listing package obtained from algebraic closedness of `ℂ`, the proved degree and
endpoint coefficient facts, and the high multiplicity of `counterexamplePositiveRoot`. -/
theorem exists_counterexample_rootsWithArguments_from_complex_roots
    (N K : ℕ) (hN : 1 ≤ N) (hK : 2 ≤ K) :
    ∃ (z : Fin (counterexampleDegree N K) → ℂ)
      (θ : Fin (counterexampleDegree N K) → ℝ),
      HasRootsWithArguments (counterexamplePolynomial N K) (counterexampleDegree N K) z θ ∧
        ∃ repeatedPositive : Fin (N + 1) → Fin (counterexampleDegree N K),
          Function.Injective repeatedPositive ∧
            ∀ i : Fin (N + 1),
              z (repeatedPositive i) = (counterexamplePositiveRoot N K : ℂ) ∧
                θ (repeatedPositive i) = 0 := by
  let p : Polynomial ℂ := counterexamplePolynomial N K
  let d : ℕ := counterexampleDegree N K
  let positiveRoot : ℂ := (counterexamplePositiveRoot N K : ℂ)
  have hnatDegree : p.natDegree = d := counterexamplePolynomial_natDegree N K hN hK
  have hdegree_coeff : p.coeff d ≠ 0 :=
    counterexamplePolynomial_coeff_degree_ne_zero N K hN hK
  have hzero_coeff : p.coeff 0 ≠ 0 :=
    counterexamplePolynomial_coeff_zero_ne_zero N K hN hK
  have hp_ne_zero : p ≠ 0 := by
    intro hp
    rw [hp, Polynomial.coeff_zero] at hdegree_coeff
    exact hdegree_coeff rfl
  let m : Multiset ℂ := p.roots
  have hcard_m : Multiset.card m = d := by
    change Multiset.card p.roots = d
    rw [IsAlgClosed.card_roots_eq_natDegree, hnatDegree]
  have hfintype_m : Fintype.card m = d := by
    rw [Multiset.card_coe, hcard_m]
  let rootsEquiv : m ≃ Fin d := Fintype.equivFinOfCardEq hfintype_m
  let z : Fin d → ℂ := fun i => ((rootsEquiv.symm i : m) : ℂ)
  let θ : Fin d → ℝ := fun i => argumentRepresentative (z i)
  have hcount_positiveRoot : m.count positiveRoot = N + 1 := by
    change p.roots.count positiveRoot = N + 1
    rw [Polynomial.count_roots]
    exact counterexamplePolynomial_rootMultiplicity_positiveRoot N K hN hK
  let positiveOccurrence : Fin (N + 1) → m := fun i =>
    m.mkToType positiveRoot (Fin.cast hcount_positiveRoot.symm i)
  let repeatedPositive : Fin (N + 1) → Fin d := fun i => rootsEquiv (positiveOccurrence i)
  refine ⟨z, θ, ?_, repeatedPositive, ?_, ?_⟩
  · refine ⟨hnatDegree, hdegree_coeff, hzero_coeff, ?_, ?_⟩
    · have hsplits : p.Splits := IsAlgClosed.splits p
      have hprod_roots :
          p = Polynomial.C p.leadingCoeff * (p.roots.map (Polynomial.X - Polynomial.C ·)).prod :=
        hsplits.eq_prod_roots
      have hleading : p.leadingCoeff = p.coeff d := by
        rw [Polynomial.leadingCoeff, hnatDegree]
      have hfin_prod :
          (p.roots.map (Polynomial.X - Polynomial.C ·)).prod =
            ∏ i : Fin d, (Polynomial.X - Polynomial.C (z i)) := by
        change (m.map (Polynomial.X - Polynomial.C ·)).prod =
          ∏ i : Fin d, (Polynomial.X - Polynomial.C (z i))
        calc
          (m.map (Polynomial.X - Polynomial.C ·)).prod =
              ((Finset.univ : Finset m).val.map
                (fun x : m => Polynomial.X - Polynomial.C ((x : m) : ℂ))).prod := by
            rw [← Multiset.map_univ m (fun a : ℂ => Polynomial.X - Polynomial.C a)]
          _ = ∏ x : m, (Polynomial.X - Polynomial.C ((x : m) : ℂ)) := rfl
          _ = ∏ i : Fin d, (Polynomial.X - Polynomial.C (z i)) := by
            symm
            exact Equiv.prod_comp rootsEquiv.symm
              (fun x : m => Polynomial.X - Polynomial.C ((x : m) : ℂ))
      calc
        p = Polynomial.C p.leadingCoeff * (p.roots.map (Polynomial.X - Polynomial.C ·)).prod :=
          hprod_roots
        _ = Polynomial.C (p.coeff d) * ∏ i : Fin d, (Polynomial.X - Polynomial.C (z i)) := by
          rw [hleading, hfin_prod]
    · intro i
      exact ⟨isArgument_argumentRepresentative (z i), argumentRepresentative_mem_Ico (z i)⟩
  · intro i j hij
    apply rootsEquiv.injective at hij
    apply Fin.ext
    have hval := congr_arg (fun x : m => x.2.val) hij
    simpa [positiveOccurrence] using hval
  · intro i
    constructor
    · dsimp [repeatedPositive, positiveOccurrence, z, positiveRoot]
      rw [Equiv.symm_apply_apply]
    · dsimp [repeatedPositive, positiveOccurrence, z, θ, positiveRoot]
      rw [Equiv.symm_apply_apply]
      exact argumentRepresentative_ofReal_pos (counterexamplePositiveRoot_pos N K)

/-- All roots of the counterexample polynomial can be enumerated, and the enumeration contains
`N + 1` specified copies of the positive root with argument `0`. -/
theorem exists_counterexample_rootsWithArguments
    (N K : ℕ) (hN : 1 ≤ N) (hK : 2 ≤ K) :
    ∃ (z : Fin (counterexampleDegree N K) → ℂ)
      (θ : Fin (counterexampleDegree N K) → ℝ),
      HasRootsWithArguments (counterexamplePolynomial N K) (counterexampleDegree N K) z θ ∧
        ∃ repeatedPositive : Fin (N + 1) → Fin (counterexampleDegree N K),
          Function.Injective repeatedPositive ∧
            ∀ i : Fin (N + 1),
              z (repeatedPositive i) = (counterexamplePositiveRoot N K : ℂ) ∧
                θ (repeatedPositive i) = 0 := by
  exact exists_counterexample_rootsWithArguments_from_complex_roots N K hN hK

/-- The final large-`N` arithmetic: a linear lower bound beats the proposed square-root
right-hand side with bounded height. -/
theorem exists_N_beating_sparse_sqrt_bound (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    ∃ N : ℕ, 1 ≤ N ∧ C * Real.sqrt ((N + 2 : ℝ) * B) < N + (1 / 2 : ℝ) := by
  rcases exists_nat_gt (4 * C ^ 2 * B + 4) with ⟨N, hNlarge⟩
  refine ⟨N, ?_, ?_⟩
  · have hNreal : (1 : ℝ) < N := by nlinarith
    exact_mod_cast le_of_lt hNreal
  · have hNpos : 0 < (N : ℝ) := by nlinarith
    have hNnonneg : 0 ≤ (N : ℝ) := le_of_lt hNpos
    have hCB_lt : C ^ 2 * B < (N : ℝ) / 4 := by nlinarith
    have hrad_nonneg : 0 ≤ (N + 2 : ℝ) * B := by positivity
    have hleft_nonneg : 0 ≤ C * Real.sqrt ((N + 2 : ℝ) * B) := by positivity
    have hright_pos : 0 < (N : ℝ) + 1 / 2 := by positivity
    have hsquare_lt :
        (C * Real.sqrt ((N + 2 : ℝ) * B)) ^ 2 < ((N : ℝ) + 1 / 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hrad_nonneg]
      have hmain : C ^ 2 * ((N + 2 : ℝ) * B) < ((N : ℝ) + 1 / 2) ^ 2 := by
        calc
          C ^ 2 * ((N + 2 : ℝ) * B) = (C ^ 2 * B) * ((N : ℝ) + 2) := by ring
          _ < ((N : ℝ) / 4) * ((N : ℝ) + 2) := by
            exact mul_lt_mul_of_pos_right hCB_lt (by positivity)
          _ < ((N : ℝ) + 1 / 2) ^ 2 := by
            nlinarith
      simpa [mul_assoc] using hmain
    have habs_lt := sq_lt_sq.mp hsquare_lt
    rwa [abs_of_nonneg hleft_nonneg, abs_of_pos hright_pos] at habs_lt

/-- Choose the parameters `N` and `K` so that the actual right-hand side of the proposed
estimate is already smaller than the number of repeated positive roots. -/
theorem exists_counterexample_parameters_beating_bound (C : ℝ) (hC : 0 ≤ C) :
    ∃ N K : ℕ, 1 ≤ N ∧ 2 ≤ K ∧
      C * Real.sqrt
          ((coeffSupportCardUpTo (counterexamplePolynomial N K) (counterexampleDegree N K) : ℝ) *
            Real.log (coefficientRatio (counterexamplePolynomial N K)
              (counterexampleDegree N K))) <
        N + 1 := by
  have hlog3_nonneg : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  rcases exists_N_beating_sparse_sqrt_bound C (Real.log 3) hC hlog3_nonneg with
    ⟨N, hN, hNbeats⟩
  have heventual :=
    (eventually_counterexample_coefficientRatio_lt_three N hN).and
      (Filter.eventually_atTop.2 ⟨2, fun K hK => hK⟩)
  rcases heventual.exists with ⟨K, hratio_lt_three, hK⟩
  refine ⟨N, K, hN, hK, ?_⟩
  let ratio : ℝ := coefficientRatio (counterexamplePolynomial N K) (counterexampleDegree N K)
  have hratio_pos : 0 < ratio := by
    exact coefficientRatio_pos_of_endpoint_ne_zero
      (counterexamplePolynomial_coeff_zero_ne_zero N K hN hK)
      (counterexamplePolynomial_coeff_degree_ne_zero N K hN hK)
  have hlog_le : Real.log ratio ≤ Real.log 3 :=
    Real.log_le_log hratio_pos hratio_lt_three.le
  have hsqrt_le :
      Real.sqrt ((coeffSupportCardUpTo (counterexamplePolynomial N K)
            (counterexampleDegree N K) : ℝ) * Real.log ratio) ≤
        Real.sqrt ((N + 2 : ℝ) * Real.log 3) := by
    rw [counterexamplePolynomial_coeffSupportCard N K hN hK]
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    exact Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left hlog_le (show 0 ≤ (N : ℝ) + 2 by positivity))
  calc
    C * Real.sqrt
          ((coeffSupportCardUpTo (counterexamplePolynomial N K) (counterexampleDegree N K) : ℝ) *
            Real.log (coefficientRatio (counterexamplePolynomial N K)
              (counterexampleDegree N K)))
        = C * Real.sqrt
          ((coeffSupportCardUpTo (counterexamplePolynomial N K) (counterexampleDegree N K) : ℝ) *
            Real.log ratio) := by rfl
    _ ≤ C * Real.sqrt ((N + 2 : ℝ) * Real.log 3) := mul_le_mul_of_nonneg_left hsqrt_le hC
    _ < N + (1 / 2 : ℝ) := hNbeats
    _ < N + 1 := by norm_num

/-- A root-enumerated angular counterexample to the proposed estimate for the constant `C`. -/
def AngularCounterexample (C : ℝ) (d : ℕ) (f : Polynomial ℂ) (z : Fin d → ℂ)
    (θ : Fin d → ℝ) (α β : ℝ) : Prop :=
  HasRootsWithArguments f d z θ ∧
    0 ≤ α ∧ α ≤ β ∧ β ≤ 2 * Real.pi ∧
      C * Real.sqrt ((coeffSupportCardUpTo f d : ℝ) * Real.log (coefficientRatio f d)) <
        |(argumentCount θ α β : ℝ) - ((β - α) / (2 * Real.pi)) * d|

/-- The explicit family from the tex solution, after choosing `N` and then `K` large
enough for the proposed constant `C`.

This packages the remaining analytic/asymptotic work: bounded coefficient ratio, the
high-multiplicity positive root transferred from the exponential polynomial, enumeration of all
roots with arguments, and the final large-`N` arithmetic. -/
theorem exists_rootEnumerated_counterexample_on_interval_from_zero (C : ℝ) (hC : 0 ≤ C) :
    ∃ (d : ℕ) (f : Polynomial ℂ) (z : Fin d → ℂ) (θ : Fin d → ℝ) (β : ℝ),
      HasRootsWithArguments f d z θ ∧
        0 ≤ β ∧ β ≤ 2 * Real.pi ∧
          C * Real.sqrt ((coeffSupportCardUpTo f d : ℝ) * Real.log (coefficientRatio f d)) <
            |(argumentCount θ 0 β : ℝ) - (β / (2 * Real.pi)) * d| := by
  rcases exists_counterexample_parameters_beating_bound C hC with
    ⟨N, K, hN, hK, hbeats⟩
  rcases exists_counterexample_rootsWithArguments N K hN hK with
    ⟨z, θ, hroots, repeatedPositive, hrepeated_inj, hrepeated⟩
  refine ⟨counterexampleDegree N K, counterexamplePolynomial N K, z, θ, 0, hroots,
    le_rfl, ?_, ?_⟩
  · positivity
  · rw [zero_div, zero_mul, sub_zero]
    refine lt_of_lt_of_le hbeats ?_
    rw [abs_of_nonneg]
    · norm_cast
      change N + 1 ≤ argumentCount θ 0 0
      rw [argumentCount]
      let counted : Finset (Fin (counterexampleDegree N K)) :=
        Finset.univ.filter fun i => 0 ≤ θ i ∧ θ i ≤ 0
      let repeated : Finset (Fin (counterexampleDegree N K)) :=
        Finset.univ.image repeatedPositive
      have hrepeated_subset_counted : repeated ⊆ counted := by
        intro i hi
        rcases Finset.mem_image.mp hi with ⟨j, _hj, rfl⟩
        have hθ := (hrepeated j).2
        simp [counted, hθ]
      have hcard_repeated : repeated.card = N + 1 := by
        rw [Finset.card_image_of_injective]
        · simp
        · exact hrepeated_inj
      calc
        N + 1 = repeated.card := hcard_repeated.symm
        _ ≤ counted.card := Finset.card_le_card hrepeated_subset_counted
    · positivity

/-- The explicit family from the tex solution gives angular counterexamples for every
proposed absolute constant. -/
theorem exists_angularCounterexample (C : ℝ) (hC : 0 ≤ C) :
    ∃ (d : ℕ) (f : Polynomial ℂ) (z : Fin d → ℂ) (θ : Fin d → ℝ) (α β : ℝ),
      AngularCounterexample C d f z θ α β := by
  rcases exists_rootEnumerated_counterexample_on_interval_from_zero C hC with
    ⟨d, f, z, θ, β, hroots, hβ_nonneg, hβ_le, hbeats⟩
  refine ⟨d, f, z, θ, 0, β, ?_⟩
  refine ⟨hroots, le_rfl, hβ_nonneg, hβ_le, ?_⟩
  simpa using hbeats

/-- Arbitrarily large explicit angular counterexamples contradict the proposed estimate. -/
theorem not_sparseErdosTuranEstimate_of_counterexamples
    (hcounter : ∀ C : ℝ, 0 ≤ C →
      ∃ (d : ℕ) (f : Polynomial ℂ) (z : Fin d → ℂ) (θ : Fin d → ℝ) (α β : ℝ),
        AngularCounterexample C d f z θ α β) :
    ¬ SparseErdosTuranEstimate := by
  rintro ⟨C, hC, hestimate⟩
  rcases hcounter C hC with ⟨d, f, z, θ, α, β, hbad⟩
  rcases hbad with ⟨hroots, hα, hαβ, hβ, hlt⟩
  exact not_lt_of_ge (hestimate d f z θ hroots α β hα hαβ hβ) hlt

/-- Erdos 990 has a negative answer: the proposed sparse Erdős--Turán estimate is false. -/
theorem erdos990 : ¬ SparseErdosTuranEstimate := by
  exact not_sparseErdosTuranEstimate_of_counterexamples exists_angularCounterexample

#print axioms erdos990
-- 'Erdos990.erdos990' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos990
