/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib
import ErdosProblems.Erdos1149.AnalyticParameters
import ErdosProblems.Erdos1149.ErdosTuran
import ErdosProblems.Erdos1149.HigherDerivative

/-!
# Power discrepancy estimates for Erdős Problem 1149

This file specializes the finite higher-derivative and Erdős--Turán
machinery to the monomial phases `a * n ^ γ`.  The point of the
specialization is that the derivative order must vary with the size of the
coefficient `a`, but only through a bounded finite set when
`a ≤ X ^ A`.

The elementary parameter-selection and derivative estimates are kept here,
separate from the general analytic inequalities.
-/

namespace Erdos1149

open scoped BigOperators

/-- The real monomial whose fractional parts are counted below. -/
noncomputable def monomialValue (γ a : ℝ) (n : ℕ) : ℝ :=
  a * (n : ℝ) ^ γ

/-- The number of `n` in the half-open integer interval `[u,v)` for which
the fractional part of `a * n ^ γ` belongs to `[0,b)`. -/
noncomputable def monomialIntervalCount
    (γ a b : ℝ) (u v : ℕ) : ℕ := by
  classical
  exact ((Finset.Ico u v).filter fun n ↦
    Int.fract (monomialValue γ a n) < b).card

/-- Signed discrepancy of the monomial fractional parts on `[u,v)` from
the expected count `b * (v-u)`. -/
noncomputable def monomialIntervalError
    (γ a b : ℝ) (u v : ℕ) : ℝ :=
  (monomialIntervalCount γ a b u v : ℝ) - b * (v - u : ℕ)

lemma monomialIntervalCount_le_length
    (γ a b : ℝ) (u v : ℕ) :
    monomialIntervalCount γ a b u v ≤ v - u := by
  classical
  unfold monomialIntervalCount
  exact (Finset.card_filter_le _ _).trans_eq (Nat.card_Ico u v)

/-- The elementary bound used to absorb finitely many small dyadic
blocks in a power-saving estimate. -/
lemma abs_monomialIntervalError_le_length
    (γ a b : ℝ) (u v : ℕ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    |monomialIntervalError γ a b u v| ≤ (v - u : ℕ) := by
  have hcountNat := monomialIntervalCount_le_length γ a b u v
  have hcount : (monomialIntervalCount γ a b u v : ℝ) ≤ (v - u : ℕ) := by
    exact_mod_cast hcountNat
  have hcount0 : (0 : ℝ) ≤ monomialIntervalCount γ a b u v := by
    positivity
  have hmain0 : 0 ≤ b * (v - u : ℕ) := mul_nonneg hb0 (by positivity)
  have hmain : b * (v - u : ℕ) ≤ (v - u : ℕ) := by
    have hlen : (0 : ℝ) ≤ ((v - u : ℕ) : ℝ) := Nat.cast_nonneg _
    simpa using mul_le_mul_of_nonneg_right hb1 hlen
  rw [monomialIntervalError, abs_le]
  constructor <;> linarith

/-- Exact additivity of the interval count at an intermediate integer. -/
lemma monomialIntervalCount_add
    (γ a b : ℝ) {u m v : ℕ} (hum : u ≤ m) (hmv : m ≤ v) :
    monomialIntervalCount γ a b u m + monomialIntervalCount γ a b m v =
      monomialIntervalCount γ a b u v := by
  classical
  unfold monomialIntervalCount
  let P : ℕ → Prop := fun n ↦ Int.fract (monomialValue γ a n) < b
  have hinterval : Finset.Ico u m ∪ Finset.Ico m v = Finset.Ico u v := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisjoint : Disjoint (Finset.Ico u m) (Finset.Ico m v) := by
    rw [Finset.disjoint_left]
    intro n hnum hnmv
    simp only [Finset.mem_Ico] at hnum hnmv
    omega
  have hfdisjoint : Disjoint
      ((Finset.Ico u m).filter fun n ↦ Int.fract (monomialValue γ a n) < b)
      ((Finset.Ico m v).filter fun n ↦ Int.fract (monomialValue γ a n) < b) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn1 hn2
    omega
  rw [← Finset.card_union_of_disjoint hfdisjoint]
  congr 1
  rw [← Finset.filter_union, hinterval]

/-- Signed discrepancies add exactly across adjacent intervals. -/
lemma monomialIntervalError_add
    (γ a b : ℝ) {u m v : ℕ} (hum : u ≤ m) (hmv : m ≤ v) :
    monomialIntervalError γ a b u m + monomialIntervalError γ a b m v =
      monomialIntervalError γ a b u v := by
  rw [monomialIntervalError, monomialIntervalError, monomialIntervalError]
  have hcount := monomialIntervalCount_add γ a b hum hmv
  have hlength : (m - u) + (v - m) = v - u := by omega
  have hcountR :
      (monomialIntervalCount γ a b u m : ℝ) +
          monomialIntervalCount γ a b m v =
        monomialIntervalCount γ a b u v := by
    exact_mod_cast hcount
  rw [← hcountR, ← hlength]
  push_cast
  ring

/-- A coefficient lies in the `s`th multiplicative `X`-scale.  Real powers
are used deliberately, even though `s` is a natural number, because this is
the normalization used by the derivative estimates. -/
noncomputable def IsCoefficientScale (X a : ℝ) (s : ℕ) : Prop :=
  X ^ (s : ℝ) ≤ a ∧
    a < X ^ ((s : ℝ) + 1)

/-- The derivative order attached to the coefficient scale `s`.  If
`X^s ≤ a < X^(s+1)`, this order makes the derivative of `a*x^γ` have
size between powers `X^(-2)` and `X^0`, uniformly in `s`. -/
noncomputable def adaptiveDerivativeOrder (γ : ℝ) (s : ℕ) : ℕ :=
  s + ⌊γ⌋₊ + 2

/-- The derivative order used at the terminal Kusmin--Landau leaf.

It is one larger than `adaptiveDerivativeOrder`.  This extra derivative is
essential: if `γ = m + ρ`, with `0 < ρ < 1`, and `X^s ≤ a < X^(s+1)`,
then the `terminalDerivativeOrder`th derivative of `a*x^γ` is between fixed
multiples of `X^(ρ-3)` and `X^(ρ-2)`.  Thus its exponent stays strictly on
one side of the balancing threshold used to choose the finite-difference
step. -/
noncomputable def terminalDerivativeOrder (γ : ℝ) (s : ℕ) : ℕ :=
  s + ⌊γ⌋₊ + 3

/-- The number of controlled Weyl-differencing levels preceding the final
first-derivative estimate. -/
noncomputable def monomialDifferencingDepth (γ : ℝ) (s : ℕ) : ℕ :=
  terminalDerivativeOrder γ s - 1

/-- Fractional part of a positive exponent, expressed using the natural
floor (which agrees with the integer floor in this range). -/
noncomputable def monomialFractionalExponent (γ : ℝ) : ℝ :=
  γ - (⌊γ⌋₊ : ℝ)

lemma monomialFractionalExponent_pos_lt_one
    {γ : ℝ} (hγ : 0 < γ)
    (hγint : γ ∉ Set.range ((↑) : ℤ → ℝ)) :
    0 < monomialFractionalExponent γ ∧
      monomialFractionalExponent γ < 1 := by
  have hfloor : (⌊γ⌋₊ : ℝ) < γ := by
    rw [natCast_floor_eq_intCast_floor hγ.le]
    exact Int.floor_lt_self_iff.mpr hγint
  have hceil : γ < ((⌊γ⌋₊ + 1 : ℕ) : ℝ) := by
    simpa using Nat.lt_floor_add_one γ
  constructor
  · simpa [monomialFractionalExponent, sub_pos] using hfloor
  · simp only [monomialFractionalExponent]
    push_cast at hceil
    linarith

/-- Absolute coefficient of the terminal derivative on coefficient scale
`s`. -/
noncomputable def terminalDerivativeCoefficient (γ : ℝ) (s : ℕ) : ℝ :=
  |(descPochhammer ℝ (terminalDerivativeOrder γ s)).eval γ|

/-- Ratio between the terminal derivative at `5*X` and at `X`. -/
noncomputable def terminalDerivativeDilationRatio (γ : ℝ) (s : ℕ) : ℝ :=
  5 ^ (γ - (terminalDerivativeOrder γ s : ℝ))

/-- Lower and upper extrema used for the terminal derivative on the
enlarged window `[X,5X]`. -/
noncomputable def terminalDerivativeLower
    (γ a X : ℝ) (s : ℕ) : ℝ :=
  terminalDerivativeCoefficient γ s * a *
    (5 * X) ^ (γ - (terminalDerivativeOrder γ s : ℝ))

noncomputable def terminalDerivativeUpper
    (γ a X : ℝ) (s : ℕ) : ℝ :=
  terminalDerivativeCoefficient γ s * a *
    X ^ (γ - (terminalDerivativeOrder γ s : ℝ))

lemma terminalDerivativeDilationRatio_pos (γ : ℝ) (s : ℕ) :
    0 < terminalDerivativeDilationRatio γ s := by
  exact Real.rpow_pos_of_pos (by norm_num) _

lemma terminalDerivativeOrder_eq_adaptive_add_one (γ : ℝ) (s : ℕ) :
    terminalDerivativeOrder γ s = adaptiveDerivativeOrder γ s + 1 := by
  simp [terminalDerivativeOrder, adaptiveDerivativeOrder]

lemma monomialDifferencingDepth_eq (γ : ℝ) (s : ℕ) :
    monomialDifferencingDepth γ s = s + ⌊γ⌋₊ + 2 := by
  simp [monomialDifferencingDepth, terminalDerivativeOrder]

lemma two_le_monomialDifferencingDepth (γ : ℝ) (s : ℕ) :
    2 ≤ monomialDifferencingDepth γ s := by
  simp [monomialDifferencingDepth_eq]

/-- The iterated derivative commutes with multiplication by a real
constant.  This formulation uses the same `Function.iterate` convention as
`Real.iter_deriv_rpow_const`. -/
lemma iter_deriv_const_mul (a : ℝ) (f : ℝ → ℝ) (l : ℕ) (x : ℝ) :
    deriv^[l] (fun y ↦ a * f y) x = a * deriv^[l] f x := by
  rw [← iteratedDeriv_eq_iterate, ← iteratedDeriv_eq_iterate]
  exact iteratedDeriv_const_mul_field a f

/-- Exact derivative formula for a scaled real power. -/
lemma iter_deriv_scaled_rpow (γ a x : ℝ) (l : ℕ) :
    deriv^[l] (fun y : ℝ ↦ a * y ^ γ) x =
      a * (descPochhammer ℝ l).eval γ *
        x ^ (γ - (l : ℝ)) := by
  rw [iter_deriv_const_mul]
  rw [Real.iter_deriv_rpow_const]
  ring

/-- An explicit derivative tower for the monomial.  Writing the tower this
way, instead of repeatedly unfolding `deriv`, makes the hypotheses of the
mixed mean-value theorem completely transparent. -/
noncomputable def monomialDerivativeFamily
    (γ a : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  a * (descPochhammer ℝ j).eval γ * x ^ (γ - (j : ℝ))

@[simp] lemma monomialDerivativeFamily_zero (γ a x : ℝ) :
    monomialDerivativeFamily γ a 0 x = a * x ^ γ := by
  simp [monomialDerivativeFamily]

/-- Consecutive members of the explicit derivative tower are derivatives
of one another at every nonzero point. -/
lemma hasDerivAt_monomialDerivativeFamily
    {γ a x : ℝ} (j : ℕ) (hx : x ≠ 0) :
    HasDerivAt (monomialDerivativeFamily γ a j)
      (monomialDerivativeFamily γ a (j + 1) x) x := by
  have h :=
    (Real.hasDerivAt_rpow_const (p := γ - (j : ℝ)) (Or.inl hx)).const_mul
      (a * (descPochhammer ℝ j).eval γ)
  change HasDerivAt
    (fun y : ℝ ↦ a * (descPochhammer ℝ j).eval γ * y ^ (γ - (j : ℝ)))
    (a * (descPochhammer ℝ (j + 1)).eval γ *
      x ^ (γ - ((j + 1 : ℕ) : ℝ))) x
  simpa only [descPochhammer_succ_eval, Nat.cast_add, Nat.cast_one,
    sub_sub, mul_assoc] using h

/-- Derivative tower after translating the integer interval to start at
zero. -/
noncomputable def shiftedMonomialDerivativeFamily
    (γ a : ℝ) (u : ℕ) (j : ℕ) (x : ℝ) : ℝ :=
  monomialDerivativeFamily γ a j ((u : ℝ) + x)

@[simp] lemma shiftedMonomialDerivativeFamily_zero_nat
    (γ a : ℝ) (u n : ℕ) :
    shiftedMonomialDerivativeFamily γ a u 0 n =
      monomialValue γ a (u + n) := by
  simp [shiftedMonomialDerivativeFamily, monomialValue, Nat.cast_add]

lemma hasDerivAt_shiftedMonomialDerivativeFamily
    {γ a : ℝ} (u j : ℕ) {x : ℝ} (hx : (u : ℝ) + x ≠ 0) :
    HasDerivAt (shiftedMonomialDerivativeFamily γ a u j)
      (shiftedMonomialDerivativeFamily γ a u (j + 1) x) x := by
  change HasDerivAt
    (fun y : ℝ ↦ monomialDerivativeFamily γ a j ((u : ℝ) + y))
    (monomialDerivativeFamily γ a (j + 1) ((u : ℝ) + x)) x
  exact
    (hasDerivAt_monomialDerivativeFamily (γ := γ) (a := a) j hx).comp_const_add
      (u : ℝ) x

lemma monomialDerivativeFamily_pos_of_coefficient_pos
    {γ a x : ℝ} {j : ℕ} (ha : 0 < a) (hx : 0 < x)
    (hc : 0 < (descPochhammer ℝ j).eval γ) :
    0 < monomialDerivativeFamily γ a j x := by
  unfold monomialDerivativeFamily
  exact mul_pos (mul_pos ha hc) (Real.rpow_pos_of_pos hx _)

lemma monomialDerivativeFamily_neg_of_coefficient_neg
    {γ a x : ℝ} {j : ℕ} (ha : 0 < a) (hx : 0 < x)
    (hc : (descPochhammer ℝ j).eval γ < 0) :
    monomialDerivativeFamily γ a j x < 0 := by
  unfold monomialDerivativeFamily
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ha hc)
    (Real.rpow_pos_of_pos hx _)

/-- Beyond the exponent, consecutive descending-Pochhammer coefficients
have opposite signs. -/
lemma terminal_next_coefficient_sign
    {γ : ℝ} {s : ℕ} :
    let l := terminalDerivativeOrder γ s
    (descPochhammer ℝ (l + 1)).eval γ =
      (descPochhammer ℝ l).eval γ * (γ - (l : ℝ)) := by
  dsimp only
  rw [descPochhammer_succ_eval]

/-- A constant sign normalization of the translated derivative tower. -/
noncomputable def signedShiftedMonomialDerivativeFamily
    (ε γ a : ℝ) (u : ℕ) (j : ℕ) (x : ℝ) : ℝ :=
  ε * shiftedMonomialDerivativeFamily γ a u j x

lemma hasDerivAt_signedShiftedMonomialDerivativeFamily
    {ε γ a : ℝ} (u j : ℕ) {x : ℝ} (hx : (u : ℝ) + x ≠ 0) :
    HasDerivAt (signedShiftedMonomialDerivativeFamily ε γ a u j)
      (signedShiftedMonomialDerivativeFamily ε γ a u (j + 1) x) x := by
  unfold signedShiftedMonomialDerivativeFamily
  exact (hasDerivAt_shiftedMonomialDerivativeFamily u j hx).const_mul ε

lemma HigherDerivative.iteratedPairDifference_neg
    (f : ℕ → ℝ) (hs : List (ℕ × ℕ × ℕ)) (x : ℕ) :
    HigherDerivative.iteratedPairDifference (fun n ↦ -f n) hs x =
      -HigherDerivative.iteratedPairDifference f hs x := by
  induction hs generalizing x with
  | nil => rfl
  | cons h hs ih =>
      rcases h with ⟨d, k, l⟩
      simp only [HigherDerivative.iteratedPairDifference,
        HigherDerivative.pairDifference, ih]
      ring

/-- The four-branch terminal Kusmin--Landau condition is invariant under
negating the phase. -/
lemma HigherDerivative.TerminalIncrementCondition.neg
    {g : ℕ → ℝ} {N : ℕ} {lam : ℝ}
    (h : HigherDerivative.TerminalIncrementCondition g N lam) :
    HigherDerivative.TerminalIncrementCondition (fun n ↦ -g n) N lam := by
  rcases h with ⟨hb, hm | ha⟩ | ⟨hb, hm | ha⟩
  · right
    refine ⟨?_, Or.inr ?_⟩
    · intro k hk
      have hbk := hb k hk
      constructor <;> dsimp only <;> linarith
    · intro i hi j hj hij
      dsimp only
      convert neg_le_neg (hm hi hj hij) using 1 <;> ring
  · right
    refine ⟨?_, Or.inl ?_⟩
    · intro k hk
      have hbk := hb k hk
      constructor <;> dsimp only <;> linarith
    · intro i hi j hj hij
      dsimp only
      convert neg_le_neg (ha hi hj hij) using 1 <;> ring
  · left
    refine ⟨?_, Or.inr ?_⟩
    · intro k hk
      have hbk := hb k hk
      constructor <;> dsimp only <;> linarith
    · intro i hi j hj hij
      dsimp only
      convert neg_le_neg (hm hi hj hij) using 1 <;> ring
  · left
    refine ⟨?_, Or.inl ?_⟩
    · intro k hk
      have hbk := hb k hk
      constructor <;> dsimp only <;> linarith
    · intro i hi j hj hij
      dsimp only
      convert neg_le_neg (ha hi hj hij) using 1 <;> ring

/-- Nonintegrality is exactly what prevents a descending Pochhammer
coefficient, of any order, from vanishing. -/
lemma descPochhammer_eval_ne_zero_of_nonint
    (γ : ℝ) (hγ : γ ∉ Set.range ((↑) : ℤ → ℝ)) (l : ℕ) :
    (descPochhammer ℝ l).eval γ ≠ 0 := by
  rw [descPochhammer_eval_eq_prod_range]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj hzero
  have hγj : γ = (j : ℝ) := sub_eq_zero.mp hzero
  apply hγ
  exact ⟨(j : ℤ), by simp [hγj]⟩

lemma terminalDerivativeCoefficient_pos
    {γ : ℝ} (hγint : γ ∉ Set.range ((↑) : ℤ → ℝ)) (s : ℕ) :
    0 < terminalDerivativeCoefficient γ s := by
  exact abs_pos.mpr (descPochhammer_eval_ne_zero_of_nonint γ hγint _)

/-- Uniform positive lower constant for all terminal derivatives in the
finitely many coefficient scales `s ≤ S`. -/
noncomputable def uniformTerminalLowerConstant (γ : ℝ) (S : ℕ) : ℝ :=
  (Finset.range (S + 1)).inf' (by simp)
    (fun s ↦ terminalDerivativeCoefficient γ s *
      terminalDerivativeDilationRatio γ s)

/-- Uniform positive lower bound for the fixed-dilation ratio. -/
noncomputable def uniformTerminalRatioConstant (γ : ℝ) (S : ℕ) : ℝ :=
  (Finset.range (S + 1)).inf' (by simp)
    (terminalDerivativeDilationRatio γ)

/-- A convenient uniform upper bound for all terminal Pochhammer
coefficients in scales `s ≤ S`. -/
noncomputable def uniformTerminalUpperConstant (γ : ℝ) (S : ℕ) : ℝ :=
  1 + ∑ s ∈ Finset.range (S + 1), terminalDerivativeCoefficient γ s

lemma uniformTerminalLowerConstant_pos
    {γ : ℝ} (hγint : γ ∉ Set.range ((↑) : ℤ → ℝ)) (S : ℕ) :
    0 < uniformTerminalLowerConstant γ S := by
  unfold uniformTerminalLowerConstant
  apply Finset.inf'_mem {x : ℝ | 0 < x}
  · intro x hx y hy
    change 0 < x at hx
    change 0 < y at hy
    exact lt_min hx hy
  · intro s hs
    exact mul_pos (terminalDerivativeCoefficient_pos hγint s)
      (terminalDerivativeDilationRatio_pos γ s)

lemma uniformTerminalRatioConstant_pos (γ : ℝ) (S : ℕ) :
    0 < uniformTerminalRatioConstant γ S := by
  unfold uniformTerminalRatioConstant
  apply Finset.inf'_mem {x : ℝ | 0 < x}
  · intro x hx y hy
    change 0 < x at hx
    change 0 < y at hy
    exact lt_min hx hy
  · intro s hs
    exact terminalDerivativeDilationRatio_pos γ s

lemma uniformTerminalUpperConstant_pos (γ : ℝ) (S : ℕ) :
    0 < uniformTerminalUpperConstant γ S := by
  unfold uniformTerminalUpperConstant
  have hsum : 0 ≤ ∑ s ∈ Finset.range (S + 1),
      terminalDerivativeCoefficient γ s := by
    exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  linarith

lemma uniformTerminalLowerConstant_le
    (γ : ℝ) {S s : ℕ} (hs : s ≤ S) :
    uniformTerminalLowerConstant γ S ≤
      terminalDerivativeCoefficient γ s *
        terminalDerivativeDilationRatio γ s := by
  unfold uniformTerminalLowerConstant
  apply Finset.inf'_le
  simp only [Finset.mem_range]
  omega

lemma uniformTerminalRatioConstant_le
    (γ : ℝ) {S s : ℕ} (hs : s ≤ S) :
    uniformTerminalRatioConstant γ S ≤
      terminalDerivativeDilationRatio γ s := by
  unfold uniformTerminalRatioConstant
  apply Finset.inf'_le
  simp only [Finset.mem_range]
  omega

lemma terminalDerivativeCoefficient_le_uniformUpper
    (γ : ℝ) {S s : ℕ} (hs : s ≤ S) :
    terminalDerivativeCoefficient γ s ≤
      uniformTerminalUpperConstant γ S := by
  unfold uniformTerminalUpperConstant
  have hmem : s ∈ Finset.range (S + 1) := by simp; omega
  have hle : terminalDerivativeCoefficient γ s ≤
      ∑ t ∈ Finset.range (S + 1), terminalDerivativeCoefficient γ t := by
    apply Finset.single_le_sum
    · intro i hi
      exact abs_nonneg _
    · exact hmem
  linarith

/-- For a positive noninteger exponent, the chosen adaptive order is
strictly larger than the exponent. -/
lemma lt_adaptiveDerivativeOrder
    {γ : ℝ} (hγ : 0 < γ)
    (hγint : γ ∉ Set.range ((↑) : ℤ → ℝ)) (s : ℕ) :
    γ < (adaptiveDerivativeOrder γ s : ℝ) := by
  have hfloor : (⌊γ⌋₊ : ℝ) < γ := by
    rw [natCast_floor_eq_intCast_floor hγ.le]
    exact Int.floor_lt_self_iff.mpr hγint
  have hceil : γ < ((⌊γ⌋₊ + 1 : ℕ) : ℝ) := by
    simpa using Nat.lt_floor_add_one γ
  have hceil' : γ < (⌊γ⌋₊ : ℝ) + 1 := by
    simpa [Nat.cast_add, Nat.cast_one] using hceil
  rw [adaptiveDerivativeOrder]
  push_cast
  calc
    γ < (⌊γ⌋₊ : ℝ) + 1 := hceil'
    _ ≤ (s : ℝ) + (⌊γ⌋₊ : ℝ) + 2 := by
      have hs : 0 ≤ (s : ℝ) := Nat.cast_nonneg s
      linarith

/-- The exponent left after differentiating at the adaptive order lies
strictly between `-(s+2)` and `-(s+1)`. -/
lemma adaptiveDerivativeExponent_bounds
    {γ : ℝ} (hγ : 0 < γ)
    (hγint : γ ∉ Set.range ((↑) : ℤ → ℝ)) (s : ℕ) :
    -((s : ℝ) + 2) < γ - (adaptiveDerivativeOrder γ s : ℝ) ∧
      γ - (adaptiveDerivativeOrder γ s : ℝ) < -((s : ℝ) + 1) := by
  have hfloor : (⌊γ⌋₊ : ℝ) < γ := by
    rw [natCast_floor_eq_intCast_floor hγ.le]
    exact Int.floor_lt_self_iff.mpr hγint
  have hceil : γ < ((⌊γ⌋₊ + 1 : ℕ) : ℝ) := by
    simpa using Nat.lt_floor_add_one γ
  have hceil' : γ < (⌊γ⌋₊ : ℝ) + 1 := by
    simpa [Nat.cast_add, Nat.cast_one] using hceil
  rw [adaptiveDerivativeOrder]
  push_cast
  constructor
  · linarith
  · linarith

/-- At the terminal order the remaining power lies between `-(s+3)` and
`-(s+2)`. -/
lemma terminalDerivativeExponent_bounds
    {γ : ℝ} (hγ : 0 < γ)
    (hγint : γ ∉ Set.range ((↑) : ℤ → ℝ)) (s : ℕ) :
    -((s : ℝ) + 3) < γ - (terminalDerivativeOrder γ s : ℝ) ∧
      γ - (terminalDerivativeOrder γ s : ℝ) < -((s : ℝ) + 2) := by
  have h := adaptiveDerivativeExponent_bounds hγ hγint s
  rw [terminalDerivativeOrder_eq_adaptive_add_one]
  push_cast
  constructor <;> linarith [h.1, h.2]

lemma lt_terminalDerivativeOrder
    {γ : ℝ} (hγ : 0 < γ)
    (hγint : γ ∉ Set.range ((↑) : ℤ → ℝ)) (s : ℕ) :
    γ < (terminalDerivativeOrder γ s : ℝ) := by
  have h := lt_adaptiveDerivativeOrder hγ hγint s
  rw [terminalDerivativeOrder_eq_adaptive_add_one]
  push_cast
  linarith

/-- In the lower dyadic derivative bound, the power of `X` is independent
of the coefficient-scale index.  Only the harmless factor `2^q` retains
the chosen derivative order. -/
lemma adaptive_lower_power_identity
    {γ X : ℝ} {s : ℕ} (hX : 0 < X) :
    let l := adaptiveDerivativeOrder γ s
    let q := γ - (l : ℝ)
    X ^ (s : ℝ) * (2 * X) ^ q =
      2 ^ q * X ^ (γ - (⌊γ⌋₊ : ℝ) - 2) := by
  dsimp only
  rw [Real.mul_rpow (by positivity) hX.le]
  calc
    X ^ (s : ℝ) *
        (2 ^ (γ - (adaptiveDerivativeOrder γ s : ℝ)) *
          X ^ (γ - (adaptiveDerivativeOrder γ s : ℝ))) =
        2 ^ (γ - (adaptiveDerivativeOrder γ s : ℝ)) *
          (X ^ (s : ℝ) *
            X ^ (γ - (adaptiveDerivativeOrder γ s : ℝ))) := by ring
    _ = 2 ^ (γ - (adaptiveDerivativeOrder γ s : ℝ)) *
          X ^ ((s : ℝ) +
            (γ - (adaptiveDerivativeOrder γ s : ℝ))) := by
          rw [Real.rpow_add hX]
    _ = _ := by
      rw [adaptiveDerivativeOrder]
      push_cast
      congr 2
      ring

/-- The upper dyadic derivative bound likewise has an `X`-exponent which
is independent of the coefficient scale. -/
lemma adaptive_upper_power_identity
    {γ X : ℝ} {s : ℕ} (hX : 0 < X) :
    let l := adaptiveDerivativeOrder γ s
    let q := γ - (l : ℝ)
    X ^ ((s : ℝ) + 1) * X ^ q =
      X ^ (γ - (⌊γ⌋₊ : ℝ) - 1) := by
  dsimp only
  rw [← Real.rpow_add hX]
  rw [adaptiveDerivativeOrder]
  push_cast
  congr 1
  ring

/-- Scale cancellation at the terminal derivative order, lower endpoint. -/
lemma terminal_lower_power_identity
    {γ X : ℝ} {s : ℕ} (hX : 0 < X) :
    let l := terminalDerivativeOrder γ s
    let q := γ - (l : ℝ)
    X ^ (s : ℝ) * (2 * X) ^ q =
      2 ^ q * X ^ (γ - (⌊γ⌋₊ : ℝ) - 3) := by
  dsimp only
  rw [Real.mul_rpow (by positivity) hX.le]
  calc
    X ^ (s : ℝ) *
        (2 ^ (γ - (terminalDerivativeOrder γ s : ℝ)) *
          X ^ (γ - (terminalDerivativeOrder γ s : ℝ))) =
        2 ^ (γ - (terminalDerivativeOrder γ s : ℝ)) *
          (X ^ (s : ℝ) *
            X ^ (γ - (terminalDerivativeOrder γ s : ℝ))) := by ring
    _ = 2 ^ (γ - (terminalDerivativeOrder γ s : ℝ)) *
          X ^ ((s : ℝ) +
            (γ - (terminalDerivativeOrder γ s : ℝ))) := by
          rw [Real.rpow_add hX]
    _ = _ := by
      rw [terminalDerivativeOrder]
      push_cast
      congr 2
      ring

/-- Scale cancellation at the terminal order for an arbitrary positive
dilation factor. -/
lemma terminal_dilation_power_identity
    {γ X C : ℝ} {s : ℕ} (hX : 0 < X) (hC : 0 ≤ C) :
    let l := terminalDerivativeOrder γ s
    let q := γ - (l : ℝ)
    X ^ (s : ℝ) * (C * X) ^ q =
      C ^ q * X ^ (γ - (⌊γ⌋₊ : ℝ) - 3) := by
  dsimp only
  rw [Real.mul_rpow hC hX.le]
  calc
    X ^ (s : ℝ) *
        (C ^ (γ - (terminalDerivativeOrder γ s : ℝ)) *
          X ^ (γ - (terminalDerivativeOrder γ s : ℝ))) =
        C ^ (γ - (terminalDerivativeOrder γ s : ℝ)) *
          (X ^ (s : ℝ) *
            X ^ (γ - (terminalDerivativeOrder γ s : ℝ))) := by ring
    _ = C ^ (γ - (terminalDerivativeOrder γ s : ℝ)) *
          X ^ ((s : ℝ) +
            (γ - (terminalDerivativeOrder γ s : ℝ))) := by
          rw [Real.rpow_add hX]
    _ = _ := by
      rw [terminalDerivativeOrder]
      push_cast
      congr 2
      ring

/-- Scale cancellation at the terminal derivative order, upper endpoint. -/
lemma terminal_upper_power_identity
    {γ X : ℝ} {s : ℕ} (hX : 0 < X) :
    let l := terminalDerivativeOrder γ s
    let q := γ - (l : ℝ)
    X ^ ((s : ℝ) + 1) * X ^ q =
      X ^ (γ - (⌊γ⌋₊ : ℝ) - 2) := by
  dsimp only
  rw [← Real.rpow_add hX]
  rw [terminalDerivativeOrder]
  push_cast
  congr 1
  ring

/-- Every positive coefficient has a unique logarithmic scale when the
base is greater than one.  Only existence is needed by the analytic
specialization. -/
lemma exists_coefficientScale
    {X a : ℝ} (hX : 1 < X) (ha : 1 ≤ a) :
    ∃ s : ℕ, IsCoefficientScale X a s := by
  let t : ℝ := Real.log a / Real.log X
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hloga : 0 ≤ Real.log a := Real.log_nonneg ha
  have ht : 0 ≤ t := div_nonneg hloga hlogX.le
  let s : ℕ := ⌊t⌋₊
  refine ⟨s, ?_⟩
  have hsle : (s : ℝ) ≤ t := by
    dsimp [s]
    exact Nat.floor_le ht
  have hslt : t < (s : ℝ) + 1 := by
    dsimp [s]
    simpa using Nat.lt_floor_add_one t
  have hXa : X ^ (s : ℝ) ≤ a := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hX)]
    rw [← Real.exp_log (lt_of_lt_of_le zero_lt_one ha)]
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hsle hlogX.le
    rw [div_mul_cancel₀ _ hlogX.ne'] at hmul
    simpa [mul_comm] using hmul
  have haX : a < X ^ ((s : ℝ) + 1) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hX)]
    rw [← Real.exp_log (lt_of_lt_of_le zero_lt_one ha)]
    apply Real.exp_lt_exp.mpr
    have hmul := mul_lt_mul_of_pos_right hslt hlogX
    rw [div_mul_cancel₀ _ hlogX.ne'] at hmul
    simpa [mul_comm] using hmul
  exact ⟨hXa, haX⟩

/-- If `a ≤ X^A`, the logarithmic scale index is bounded by every
natural `S` with `A ≤ S`.  This is the finiteness input for taking a
uniform minimum over the finitely many derivative orders. -/
lemma coefficientScale_index_le
    {X a A : ℝ} {s S : ℕ}
    (hX : 1 < X) (hscale : IsCoefficientScale X a s)
    (haA : a ≤ X ^ A) (hAS : A ≤ S) :
    s ≤ S := by
  by_contra hnot
  have hSs : S + 1 ≤ s := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hnot)
  have hpowSS : X ^ ((S : ℝ) + 1) ≤ X ^ (s : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hX.le
    exact_mod_cast hSs
  have hpowA : X ^ A < X ^ ((S : ℝ) + 1) := by
    apply Real.rpow_lt_rpow_of_exponent_lt hX
    exact lt_of_le_of_lt hAS (by exact_mod_cast Nat.lt_succ_self S)
  have ha_lt : a < X ^ (s : ℝ) :=
    haA.trans_lt (hpowA.trans_le hpowSS)
  exact (not_lt_of_ge hscale.1) ha_lt

/-- Under a polynomial coefficient envelope, one may choose the scale
index from the fixed finite set `{0,…,ceil A}`. -/
lemma exists_coefficientScale_le_natCeil
    {X a A : ℝ} (hX : 1 < X) (ha : 1 ≤ a)
    (haA : a ≤ X ^ A) :
    ∃ s : ℕ, s ≤ ⌈A⌉₊ ∧ IsCoefficientScale X a s := by
  obtain ⟨s, hscale⟩ := exists_coefficientScale hX ha
  refine ⟨s, coefficientScale_index_le hX hscale haA (Nat.le_ceil A), hscale⟩

/-- Consequently all adaptive derivative orders lie in one finite range
depending only on `γ` and the coefficient-growth exponent `A`. -/
lemma adaptiveDerivativeOrder_le_of_polynomial_coefficient
    {γ X a A : ℝ} {s : ℕ}
    (hX : 1 < X) (hscale : IsCoefficientScale X a s)
    (haA : a ≤ X ^ A) :
    adaptiveDerivativeOrder γ s ≤ ⌈A⌉₊ + ⌊γ⌋₊ + 2 := by
  unfold adaptiveDerivativeOrder
  have hs := coefficientScale_index_le hX hscale haA (Nat.le_ceil A)
  omega

/-- Generic dyadic window for a member of the explicit monomial derivative
tower whose remaining power is negative. -/
lemma abs_monomialDerivativeFamily_dyadic_bounds
    {γ a X x : ℝ} {l : ℕ}
    (hγint : γ ∉ Set.range ((↑) : ℤ → ℝ))
    (hX : 0 < X) (hXx : X ≤ x) (hx2X : x ≤ 2 * X)
    (ha : 0 < a) (hq : γ - (l : ℝ) < 0) :
    let c := |(descPochhammer ℝ l).eval γ|
    let q := γ - (l : ℝ)
    c * a * (2 * X) ^ q ≤ |monomialDerivativeFamily γ a l x| ∧
      |monomialDerivativeFamily γ a l x| ≤ c * a * X ^ q := by
  dsimp only
  let c := |(descPochhammer ℝ l).eval γ|
  let q := γ - (l : ℝ)
  have hx : 0 < x := hX.trans_le hXx
  have hc : 0 < c := abs_pos.mpr
    (descPochhammer_eval_ne_zero_of_nonint γ hγint l)
  rw [monomialDerivativeFamily, abs_mul, abs_mul, abs_of_pos ha]
  rw [abs_of_pos (Real.rpow_pos_of_pos hx q)]
  change c * a * (2 * X) ^ q ≤ a * c * x ^ q ∧
    a * c * x ^ q ≤ c * a * X ^ q
  constructor
  · have hpow : (2 * X) ^ q ≤ x ^ q :=
      Real.rpow_le_rpow_of_nonpos hx hx2X hq.le
    calc
      c * a * (2 * X) ^ q ≤ c * a * x ^ q := by gcongr
      _ = a * c * x ^ q := by ring
  · have hpow : x ^ q ≤ X ^ q :=
      Real.rpow_le_rpow_of_nonpos hX hXx hq.le
    calc
      a * c * x ^ q ≤ a * c * X ^ q := by gcongr
      _ = c * a * X ^ q := by ring

/-- The same derivative window on an arbitrary fixed dilation `[X,C*X]`.
The monomial application below uses `C = 4` to accommodate both the
original dyadic interval and all controlled translations. -/
lemma abs_monomialDerivativeFamily_dilation_bounds
    {γ a X C x : ℝ} {l : ℕ}
    (hγint : γ ∉ Set.range ((↑) : ℤ → ℝ))
    (hX : 0 < X) (hXx : X ≤ x) (hxCX : x ≤ C * X)
    (ha : 0 < a) (hq : γ - (l : ℝ) < 0) :
    let c := |(descPochhammer ℝ l).eval γ|
    let q := γ - (l : ℝ)
    c * a * (C * X) ^ q ≤ |monomialDerivativeFamily γ a l x| ∧
      |monomialDerivativeFamily γ a l x| ≤ c * a * X ^ q := by
  dsimp only
  let c := |(descPochhammer ℝ l).eval γ|
  let q := γ - (l : ℝ)
  have hx : 0 < x := hX.trans_le hXx
  have hc : 0 < c := abs_pos.mpr
    (descPochhammer_eval_ne_zero_of_nonint γ hγint l)
  rw [monomialDerivativeFamily, abs_mul, abs_mul, abs_of_pos ha]
  rw [abs_of_pos (Real.rpow_pos_of_pos hx q)]
  change c * a * (C * X) ^ q ≤ a * c * x ^ q ∧
    a * c * x ^ q ≤ c * a * X ^ q
  constructor
  · have hpow : (C * X) ^ q ≤ x ^ q :=
      Real.rpow_le_rpow_of_nonpos hx hxCX hq.le
    calc
      c * a * (C * X) ^ q ≤ c * a * x ^ q := by gcongr
      _ = a * c * x ^ q := by ring
  · have hpow : x ^ q ≤ X ^ q :=
      Real.rpow_le_rpow_of_nonpos hX hXx hq.le
    calc
      a * c * x ^ q ≤ a * c * X ^ q := by gcongr
      _ = c * a * X ^ q := by ring

/-- Exact dyadic derivative window at the terminal order. -/
lemma abs_terminalDerivative_scaled_rpow_dyadic_bounds_exact
    {γ a X x : ℝ} {s : ℕ}
    (hγ : 0 < γ)
    (hγint : γ ∉ Set.range ((↑) : ℤ → ℝ))
    (hX : 0 < X) (hXx : X ≤ x) (hx2X : x ≤ 2 * X)
    (ha : 0 < a) :
    let l := terminalDerivativeOrder γ s
    let c := |(descPochhammer ℝ l).eval γ|
    let q := γ - (l : ℝ)
    c * a * (2 * X) ^ q ≤ |monomialDerivativeFamily γ a l x| ∧
      |monomialDerivativeFamily γ a l x| ≤ c * a * X ^ q := by
  dsimp only
  exact abs_monomialDerivativeFamily_dyadic_bounds hγint hX hXx hx2X ha
    (sub_neg.mpr (lt_terminalDerivativeOrder hγ hγint s))

/-- Coefficient-scale version of the terminal derivative window. -/
lemma abs_terminalDerivative_scaled_rpow_dyadic_bounds
    {γ a X x : ℝ} {s : ℕ}
    (hγ : 0 < γ)
    (hγint : γ ∉ Set.range ((↑) : ℤ → ℝ))
    (hX : 0 < X) (hXx : X ≤ x) (hx2X : x ≤ 2 * X)
    (ha : 0 < a) (hscale : IsCoefficientScale X a s) :
    let l := terminalDerivativeOrder γ s
    let c := |(descPochhammer ℝ l).eval γ|
    let q := γ - (l : ℝ)
    c * X ^ (s : ℝ) * (2 * X) ^ q ≤
        |monomialDerivativeFamily γ a l x| ∧
      |monomialDerivativeFamily γ a l x| ≤
        c * X ^ ((s : ℝ) + 1) * X ^ q := by
  dsimp only
  let l := terminalDerivativeOrder γ s
  let c := |(descPochhammer ℝ l).eval γ|
  let q := γ - (l : ℝ)
  have hexact := abs_terminalDerivative_scaled_rpow_dyadic_bounds_exact
    hγ hγint hX hXx hx2X ha (s := s)
  dsimp only at hexact
  constructor
  · calc
      c * X ^ (s : ℝ) * (2 * X) ^ q ≤
          c * a * (2 * X) ^ q := by gcongr; exact hscale.1
      _ ≤ |monomialDerivativeFamily γ a l x| := hexact.1
  · calc
      |monomialDerivativeFamily γ a l x| ≤ c * a * X ^ q := hexact.2
      _ ≤ c * X ^ ((s : ℝ) + 1) * X ^ q := by
        gcongr
        exact hscale.2.le

/-- The exact derivative extrema satisfy the uniform hypotheses of the
rounded analytic parameter-selection theorem. -/
lemma terminalDerivative_parameter_bounds
    {γ a X : ℝ} {s S : ℕ}
    (hγ : 0 < γ)
    (hγint : γ ∉ Set.range ((↑) : ℤ → ℝ))
    (hX : 0 < X) (ha : 0 < a) (hscale : IsCoefficientScale X a s)
    (hsS : s ≤ S) :
    let ρ := monomialFractionalExponent γ
    let l := terminalDerivativeOrder γ s
    let c := terminalDerivativeCoefficient γ s
    let q := γ - (l : ℝ)
    let Dlow := c * a * (5 * X) ^ q
    let Dup := c * a * X ^ q
    let cL := uniformTerminalLowerConstant γ S
    let cU := uniformTerminalUpperConstant γ S
    let cRatio := uniformTerminalRatioConstant γ S
    0 < Dup ∧
      Dup ≤ cU * X ^ (ρ - 2) ∧
      cL * X ^ (ρ - 3) ≤ Dlow ∧
      cRatio * Dup ≤ Dlow ∧ Dlow ≤ Dup := by
  dsimp only
  let ρ := monomialFractionalExponent γ
  let l := terminalDerivativeOrder γ s
  let c := terminalDerivativeCoefficient γ s
  let q := γ - (l : ℝ)
  let Dlow := c * a * (5 * X) ^ q
  let Dup := c * a * X ^ q
  let cL := uniformTerminalLowerConstant γ S
  let cU := uniformTerminalUpperConstant γ S
  let cRatio := uniformTerminalRatioConstant γ S
  have hc : 0 < c := terminalDerivativeCoefficient_pos hγint s
  have hq : q < 0 := by
    dsimp only [q, l]
    have h := (terminalDerivativeExponent_bounds hγ hγint s).2
    have hs0 : (0 : ℝ) ≤ s := by positivity
    linarith
  have hDup : 0 < Dup := by
    dsimp only [Dup]
    exact mul_pos (mul_pos hc ha) (Real.rpow_pos_of_pos hX _)
  have hpow0 (z : ℝ) : 0 ≤ X ^ z := Real.rpow_nonneg hX.le _
  have hcU : c ≤ cU := terminalDerivativeCoefficient_le_uniformUpper γ hsS
  have hupperIdentity : X ^ ((s : ℝ) + 1) * X ^ q = X ^ (ρ - 2) := by
    simpa only [l, q, ρ, monomialFractionalExponent] using
      (terminal_upper_power_identity (γ := γ) (X := X) (s := s) hX)
  have hDupUpper : Dup ≤ cU * X ^ (ρ - 2) := by
    calc
      Dup = c * a * X ^ q := rfl
      _ ≤ c * X ^ ((s : ℝ) + 1) * X ^ q := by
        gcongr
        exact hscale.2.le
      _ = c * (X ^ ((s : ℝ) + 1) * X ^ q) := by ring
      _ = c * X ^ (ρ - 2) := by rw [hupperIdentity]
      _ ≤ cU * X ^ (ρ - 2) := by gcongr
  have hratioS : cRatio ≤ terminalDerivativeDilationRatio γ s :=
    uniformTerminalRatioConstant_le γ hsS
  have hlowerS : cL ≤ c * terminalDerivativeDilationRatio γ s :=
    uniformTerminalLowerConstant_le γ hsS
  have hlowerIdentity : X ^ (s : ℝ) * (5 * X) ^ q =
      terminalDerivativeDilationRatio γ s * X ^ (ρ - 3) := by
    simpa only [l, q, ρ, monomialFractionalExponent,
      terminalDerivativeDilationRatio] using
      (terminal_dilation_power_identity (γ := γ) (X := X) (C := 5)
        (s := s) hX (by norm_num))
  have hDlowLower : cL * X ^ (ρ - 3) ≤ Dlow := by
    calc
      cL * X ^ (ρ - 3) ≤
          (c * terminalDerivativeDilationRatio γ s) * X ^ (ρ - 3) := by
        gcongr
      _ = c * (X ^ (s : ℝ) * (5 * X) ^ q) := by
        rw [hlowerIdentity]
        ring
      _ ≤ c * (a * (5 * X) ^ q) := by gcongr; exact hscale.1
      _ = Dlow := by dsimp only [Dlow]; ring
  have hratioIdentity : terminalDerivativeDilationRatio γ s * Dup = Dlow := by
    dsimp only [terminalDerivativeDilationRatio, Dup, Dlow, q, l]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) hX.le]
    ring
  have hRatio : cRatio * Dup ≤ Dlow := by
    calc
      cRatio * Dup ≤ terminalDerivativeDilationRatio γ s * Dup := by gcongr
      _ = Dlow := hratioIdentity
  have h4ratio : terminalDerivativeDilationRatio γ s ≤ 1 := by
    dsimp only [terminalDerivativeDilationRatio]
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 5) hq.le
  have hDlowDup : Dlow ≤ Dup := by
    rw [← hratioIdentity]
    exact mul_le_of_le_one_left hDup.le h4ratio
  exact ⟨hDup, hDupUpper, hDlowLower, hRatio, hDlowDup⟩

/-- Terminal derivative bounds after translating a dyadic interval to
start at zero.  The calculus window `[0,3X]` maps into `[X,5X]`. -/
lemma abs_shifted_terminalDerivative_bounds_on_Icc
    {γ a : ℝ} {X u s : ℕ}
    (hγ : 0 < γ)
    (hγint : γ ∉ Set.range ((↑) : ℤ → ℝ))
    (hX : 1 ≤ X) (hXu : X ≤ u) (hu2X : u ≤ 2 * X) (ha : 0 < a) :
    ∀ y ∈ Set.Icc (0 : ℝ) (3 * X),
      terminalDerivativeLower γ a X s ≤
          |shiftedMonomialDerivativeFamily γ a u
            (terminalDerivativeOrder γ s) y| ∧
        |shiftedMonomialDerivativeFamily γ a u
            (terminalDerivativeOrder γ s) y| ≤
          terminalDerivativeUpper γ a X s := by
  intro y hy
  have hXR : 0 < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hleft : (X : ℝ) ≤ (u : ℝ) + y := by
    have hXuR : (X : ℝ) ≤ u := by exact_mod_cast hXu
    linarith [hy.1]
  have hright : (u : ℝ) + y ≤ 5 * X := by
    have huR : (u : ℝ) ≤ 2 * X := by exact_mod_cast hu2X
    linarith [hy.2]
  have hb := abs_monomialDerivativeFamily_dilation_bounds
    (l := terminalDerivativeOrder γ s) hγint hXR hleft hright ha
      (sub_neg.mpr (lt_terminalDerivativeOrder hγ hγint s))
  simpa only [terminalDerivativeLower, terminalDerivativeUpper,
    terminalDerivativeCoefficient, shiftedMonomialDerivativeFamily] using hb

/-- The rounded terminal inequalities imply the four-branch
Kusmin--Landau condition at every controlled Weyl leaf. -/
lemma monomialLeafTerminalIncrementCondition
    {γ a lam : ℝ} {X u P s K d : ℕ}
    (hγ : 0 < γ)
    (hγint : γ ∉ Set.range ((↑) : ℤ → ℝ))
    (hX : 1 ≤ X) (hXu : X ≤ u) (hu2X : u ≤ 2 * X)
    (hP : P ≤ X) (ha : 0 < a)
    (hK : 0 < K)
    (htranslate : (monomialDifferencingDepth γ s : ℝ) * K * d ≤ X)
    (hlower : lam ≤ (d : ℝ) ^ monomialDifferencingDepth γ s *
      terminalDerivativeLower γ a X s)
    (hupper : (K : ℝ) ^ monomialDifferencingDepth γ s *
      (d : ℝ) ^ monomialDifferencingDepth γ s *
        terminalDerivativeUpper γ a X s ≤ 1 / 2)
    (hlamhalf : lam ≤ 1 / 2)
    (leaf : RestrictedWeyl.History)
    (hleaf : leaf ∈ RestrictedWeyl.offDiagonalHistoryLeaves
      (HigherDerivative.constantControlledSteps
        (monomialDifferencingDepth γ s) K d hK) []) :
    HigherDerivative.TerminalIncrementCondition
      (HigherDerivative.iteratedPairDifference
        (fun n ↦ monomialValue γ a (u + n)) leaf) P lam := by
  let r := monomialDifferencingDepth γ s
  let l := terminalDerivativeOrder γ s
  let p : ℝ := (descPochhammer ℝ l).eval γ
  let ε : ℝ := if 0 < p then 1 else -1
  let F : ℕ → ℝ → ℝ :=
    signedShiftedMonomialDerivativeFamily ε γ a u
  let f : ℝ → ℝ := fun y ↦ ε * (a * ((u : ℝ) + y) ^ γ)
  let Dlow := terminalDerivativeLower γ a X s
  let Dup := terminalDerivativeUpper γ a X s
  let Nup : ℝ :=
    |(descPochhammer ℝ (l + 1)).eval γ| * a *
      (X : ℝ) ^ (γ - ((l + 1 : ℕ) : ℝ))
  have hp0 : p ≠ 0 := by
    dsimp only [p, l]
    exact descPochhammer_eval_ne_zero_of_nonint γ hγint _
  have hεabs : |ε| = 1 := by
    dsimp only [ε]
    split <;> norm_num
  have hεp : 0 < ε * p := by
    dsimp only [ε]
    split_ifs with hp
    · simpa using hp
    · have hpneg : p < 0 := lt_of_le_of_ne (le_of_not_gt hp) hp0
      simpa using neg_pos.mpr hpneg
  have hq : γ - (l : ℝ) < 0 := by
    dsimp only [l]
    have h := (terminalDerivativeExponent_bounds hγ hγint s).2
    have hs0 : (0 : ℝ) ≤ s := by positivity
    linarith
  have hr2 : 2 ≤ r := by
    dsimp only [r]
    exact two_le_monomialDifferencingDepth γ s
  have hrl : r + 1 = l := by
    dsimp only [r, l]
    rw [monomialDifferencingDepth_eq, terminalDerivativeOrder]
  have hleafLength := HigherDerivative.leaf_length_eq_of_constantControlledSteps
    r K d hK leaf hleaf
  have hstepsLength :
      (MixedDifference.historySteps (MixedDifference.realHistory leaf)).length = r := by
    rw [MixedDifference.length_historySteps, MixedDifference.length_realHistory,
      hleafLength]
  have hbudget :=
    HigherDerivative.historyBase_add_steps_sum_le_of_constantControlledSteps
      r K d hK leaf hleaf
  have hbudget' :
      (P : ℝ) + MixedDifference.historyBase (MixedDifference.realHistory leaf) + 1 +
          (MixedDifference.historySteps (MixedDifference.realHistory leaf)).sum ≤
        3 * X := by
    have hPR : (P : ℝ) ≤ X := by exact_mod_cast hP
    have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have htranslate' : (r : ℝ) * K * d ≤ X := by simpa only [r] using htranslate
    nlinarith [htranslate']
  have hbase0 : (0 : ℝ) ≤
      MixedDifference.historyBase (MixedDifference.realHistory leaf) := by
    rw [MixedDifference.historyBase_realHistory]
    unfold MixedDifference.natHistoryBase
    apply List.sum_nonneg
    intro z hz
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hz
    unfold MixedDifference.natPairBase
    positivity
  have hFzero : F 0 = f := by
    funext y
    simp [F, f, signedShiftedMonomialDerivativeFamily,
      shiftedMonomialDerivativeFamily, monomialDerivativeFamily]
  have hsmooth : ∀ j <
      (MixedDifference.historySteps (MixedDifference.realHistory leaf)).length + 2,
      ∀ y ∈ Set.Icc (0 : ℝ) (3 * X),
        HasDerivAt (F j) (F (j + 1) y) y := by
    intro j hj y hy
    apply hasDerivAt_signedShiftedMonomialDerivativeFamily
    have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hX.trans hXu
    linarith [hy.1]
  have habsTerminal := abs_shifted_terminalDerivative_bounds_on_Icc
    (γ := γ) (a := a) (X := X) (u := u) (s := s)
    hγ hγint hX hXu hu2X ha
  have hterminal : ∀ y ∈ Set.Icc (0 : ℝ) (3 * X),
      Dlow ≤ F
        ((MixedDifference.historySteps (MixedDifference.realHistory leaf)).length + 1) y ∧
      F ((MixedDifference.historySteps (MixedDifference.realHistory leaf)).length + 1) y ≤
        Dup := by
    intro y hy
    have habs := habsTerminal y hy
    have hindex :
        (MixedDifference.historySteps (MixedDifference.realHistory leaf)).length + 1 = l := by
      rw [hstepsLength, hrl]
    have hpos : 0 < F l y := by
      dsimp only [F, signedShiftedMonomialDerivativeFamily,
        shiftedMonomialDerivativeFamily, monomialDerivativeFamily]
      have hxy : 0 < (u : ℝ) + y := by
        have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hX.trans hXu
        linarith [hy.1]
      rw [show ε * (a * p * ((u : ℝ) + y) ^ (γ - (l : ℝ))) =
          (ε * p) * a * ((u : ℝ) + y) ^ (γ - (l : ℝ)) by ring]
      exact mul_pos (mul_pos hεp ha) (Real.rpow_pos_of_pos hxy _)
    have habsF : |F l y| =
        |shiftedMonomialDerivativeFamily γ a u l y| := by
      dsimp only [F, signedShiftedMonomialDerivativeFamily]
      rw [abs_mul, hεabs, one_mul]
    rw [hindex]
    rw [← habsF] at habs
    simpa only [abs_of_pos hpos, Dlow, Dup] using habs
  have hnext : ∀ y ∈ Set.Icc (0 : ℝ) (3 * X),
      -Nup ≤ F
        ((MixedDifference.historySteps (MixedDifference.realHistory leaf)).length + 2) y ∧
      F ((MixedDifference.historySteps (MixedDifference.realHistory leaf)).length + 2) y ≤ 0 := by
    intro y hy
    have hindex :
        (MixedDifference.historySteps (MixedDifference.realHistory leaf)).length + 2 =
          l + 1 := by
      rw [hstepsLength]
      omega
    have hxy : 0 < (u : ℝ) + y := by
      have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hX.trans hXu
      linarith [hy.1]
    have hpnext : ε * (descPochhammer ℝ (l + 1)).eval γ < 0 := by
      rw [descPochhammer_succ_eval]
      have ht := mul_neg_of_pos_of_neg hεp hq
      simpa only [mul_assoc] using ht
    have hneg : F (l + 1) y < 0 := by
      dsimp only [F, signedShiftedMonomialDerivativeFamily,
        shiftedMonomialDerivativeFamily, monomialDerivativeFamily]
      rw [show ε * (a * (descPochhammer ℝ (l + 1)).eval γ *
          ((u : ℝ) + y) ^ (γ - ((l + 1 : ℕ) : ℝ))) =
          (ε * (descPochhammer ℝ (l + 1)).eval γ) * a *
            ((u : ℝ) + y) ^ (γ - ((l + 1 : ℕ) : ℝ)) by ring]
      exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hpnext ha)
        (Real.rpow_pos_of_pos hxy _)
    have hXR : 0 < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
    have hleft : (X : ℝ) ≤ (u : ℝ) + y := by
      have hXuR : (X : ℝ) ≤ u := by exact_mod_cast hXu
      linarith [hy.1]
    have hright : (u : ℝ) + y ≤ 5 * X := by
      have huR : (u : ℝ) ≤ 2 * X := by exact_mod_cast hu2X
      linarith [hy.2]
    have habs := abs_monomialDerivativeFamily_dilation_bounds
      (l := l + 1) hγint hXR hleft hright ha (by
        push_cast
        linarith)
    have habsF : |F (l + 1) y| =
        |monomialDerivativeFamily γ a (l + 1) ((u : ℝ) + y)| := by
      dsimp only [F, signedShiftedMonomialDerivativeFamily,
        shiftedMonomialDerivativeFamily]
      rw [abs_mul, hεabs, one_mul]
    have hupp : |F (l + 1) y| ≤ Nup := by
      rw [habsF]
      exact habs.2
    rw [hindex]
    constructor
    · linarith [neg_abs_le (F (l + 1) y)]
    · exact hneg.le
  have hprodLower :=
    HigherDerivative.pow_le_historySteps_prod_of_constantControlledSteps
      r K d hK leaf hleaf
  have hprodUpper :=
    HigherDerivative.historySteps_prod_le_pow_of_constantControlledSteps
      r K d hK leaf hleaf
  have hDlow0 : 0 ≤ Dlow := by
    dsimp only [Dlow, terminalDerivativeLower,
      terminalDerivativeCoefficient]
    positivity
  have hDup0 : 0 ≤ Dup := by
    dsimp only [Dup, terminalDerivativeUpper,
      terminalDerivativeCoefficient]
    positivity
  have hlowerLeaf : lam ≤ Dlow *
      (MixedDifference.historySteps (MixedDifference.realHistory leaf)).prod := by
    calc
      lam ≤ (d : ℝ) ^ r * Dlow := by simpa only [r] using hlower
      _ = Dlow * (d : ℝ) ^ r := by ring
      _ ≤ Dlow *
          (MixedDifference.historySteps (MixedDifference.realHistory leaf)).prod := by
        gcongr
  have hupperLeaf : Dup *
      (MixedDifference.historySteps (MixedDifference.realHistory leaf)).prod ≤
        1 - lam := by
    calc
      Dup * (MixedDifference.historySteps (MixedDifference.realHistory leaf)).prod ≤
          Dup * (((K : ℝ) * d) ^ r) := by gcongr
      _ = (K : ℝ) ^ r * (d : ℝ) ^ r * Dup := by rw [mul_pow]; ring
      _ ≤ 1 / 2 := by simpa only [r] using hupper
      _ ≤ 1 - lam := by linarith
  have hcond : HigherDerivative.TerminalIncrementCondition
      (HigherDerivative.iteratedPairDifference (fun n ↦ f n) leaf) P lam := by
    apply HigherDerivative.terminalIncrementCondition_of_derivBounds_and_next_nonpos_on_Icc
      F f leaf P 0 (3 * X) Dlow Dup (-Nup) 0 lam hFzero hbase0 hbudget'
      hsmooth hterminal hnext (by norm_num) hlowerLeaf hupperLeaf
  let g : ℕ → ℝ := fun n ↦ a * ((u : ℝ) + n) ^ γ
  have hg : g = fun n ↦ monomialValue γ a (u + n) := by
    funext n
    simp [g, monomialValue, Nat.cast_add]
  by_cases hp : 0 < p
  · have hε : ε = 1 := by simp [ε, hp]
    have hcond' : HigherDerivative.TerminalIncrementCondition
        (HigherDerivative.iteratedPairDifference g leaf) P lam := by
      simpa only [f, hε, one_mul, g] using hcond
    simpa only [hg] using hcond'
  · have hε : ε = -1 := by simp [ε, hp]
    have hcond' : HigherDerivative.TerminalIncrementCondition
        (HigherDerivative.iteratedPairDifference (fun n ↦ -g n) leaf) P lam := by
      simpa only [f, hε, neg_one_mul, g] using hcond
    have hnegcond := hcond'.neg
    have hcancel (n : ℕ) :
        -HigherDerivative.iteratedPairDifference (fun n ↦ -g n) leaf n =
          HigherDerivative.iteratedPairDifference g leaf n := by
      rw [HigherDerivative.iteratedPairDifference_neg]
      simp
    have horig : HigherDerivative.TerminalIncrementCondition
        (HigherDerivative.iteratedPairDifference g leaf) P lam := by
      simpa only [hcancel] using hnegcond
    simpa only [hg] using horig

/-- Uniform saving exponent after at most `R` controlled differencing
levels. -/
noncomputable def monomialExponentialSavingExponent (ρ : ℝ) (R : ℕ) : ℝ :=
  AnalyticParameters.shiftCountExponent ρ R / (2 : ℝ) ^ R

/-- Uniform envelope constant over all differencing depths `r ≤ R`. -/
noncomputable def monomialEnvelopeBoundConstant (cL : ℝ) (R : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (R + 1),
    AnalyticParameters.envelopeConstant
      (2 + 8 * (2 * Real.sqrt (cL⁻¹)) ^ 2) 1 r

lemma monomialEnvelopeBoundConstant_nonneg (cL : ℝ) (R : ℕ) :
    0 ≤ monomialEnvelopeBoundConstant cL R := by
  unfold monomialEnvelopeBoundConstant
  apply Finset.sum_nonneg
  intro r hr
  apply AnalyticParameters.envelopeConstant_nonneg <;> positivity

lemma envelopeConstant_le_monomialEnvelopeBoundConstant
    {cL : ℝ} {R r : ℕ} (hrR : r ≤ R) :
    AnalyticParameters.envelopeConstant
        (2 + 8 * (2 * Real.sqrt (cL⁻¹)) ^ 2) 1 r ≤
      monomialEnvelopeBoundConstant cL R := by
  unfold monomialEnvelopeBoundConstant
  apply Finset.single_le_sum
  · intro j hj
    apply AnalyticParameters.envelopeConstant_nonneg <;> positivity
  · simp only [Finset.mem_range]
    omega

/-- Large-scale exponential-sum estimate after all analytic parameters
have been selected. -/
theorem norm_monomial_phase_sum_range_le_large
    {γ a : ℝ} {X u P s S R : ℕ}
    (hγ : 0 < γ)
    (hγint : γ ∉ Set.range ((↑) : ℤ → ℝ))
    (hXu : X ≤ u) (hu2X : u ≤ 2 * X) (hP : P ≤ X)
    (ha : 1 ≤ a) (hscale : IsCoefficientScale X a s) (hsS : s ≤ S)
    (hrR : monomialDifferencingDepth γ s ≤ R)
    (hlarge : AnalyticParameters.IsLargeMonomialScale
      (monomialFractionalExponent γ)
      (uniformTerminalRatioConstant γ S)
      (uniformTerminalUpperConstant γ S) R X)
    (htranslationScale :
      2 * Real.sqrt ((uniformTerminalLowerConstant γ S)⁻¹) * R ≤
        (X : ℝ) ^ AnalyticParameters.roundingLossExponent
          (monomialFractionalExponent γ)) :
    ‖∑ n ∈ Finset.range P,
        HigherDerivative.phase (monomialValue γ a (u + n))‖ ≤
      monomialEnvelopeBoundConstant (uniformTerminalLowerConstant γ S) R *
        (X : ℝ) ^ (1 - monomialExponentialSavingExponent
          (monomialFractionalExponent γ) R) := by
  let ρ := monomialFractionalExponent γ
  let r := monomialDifferencingDepth γ s
  let cL := uniformTerminalLowerConstant γ S
  let cU := uniformTerminalUpperConstant γ S
  let cRatio := uniformTerminalRatioConstant γ S
  let Dlow := terminalDerivativeLower γ a X s
  let Dup := terminalDerivativeUpper γ a X s
  let K := AnalyticParameters.monomialShiftCount ρ R X
  let d := AnalyticParameters.monomialStepSize ρ Dup X r
  let τ := AnalyticParameters.terminalScaleExponent ρ
  let σ := AnalyticParameters.roundingLossExponent ρ
  let κ := AnalyticParameters.shiftCountExponent ρ R
  let theta : ℝ := 3 * ρ / 8
  let lam : ℝ := (X : ℝ) ^ (-(τ + σ))
  have hρ := monomialFractionalExponent_pos_lt_one hγ hγint
  have hcL : 0 < cL := uniformTerminalLowerConstant_pos hγint S
  have hcU : 0 < cU := uniformTerminalUpperConstant_pos γ S
  have hcRatio : 0 < cRatio := uniformTerminalRatioConstant_pos γ S
  have hr2 : 2 ≤ r := by
    dsimp only [r]
    exact two_le_monomialDifferencingDepth γ s
  have hR2 : 2 ≤ R := hr2.trans hrR
  have hR0 : 0 < R := by omega
  have hX1 : 1 ≤ X := hlarge.1
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hXR0 : 0 < (X : ℝ) := zero_lt_one.trans_le hXR
  have hderiv := terminalDerivative_parameter_bounds hγ hγint hXR0
    (lt_of_lt_of_le zero_lt_one ha) hscale hsS
  change 0 < Dup ∧
      Dup ≤ cU * (X : ℝ) ^ (ρ - 2) ∧
      cL * (X : ℝ) ^ (ρ - 3) ≤ Dlow ∧
      cRatio * Dup ≤ Dlow ∧ Dlow ≤ Dup at hderiv
  have hparam := AnalyticParameters.monomialParameters_leaf_bounds
    hρ.1 hρ.2 hcRatio hcL hcU hr2 hrR hlarge hderiv.1 hderiv.2.1
      hderiv.2.2.1 hderiv.2.2.2.1 hderiv.2.2.2.2
  change 0 < K ∧ 0 < d ∧
      (K : ℝ) ^ r * (d : ℝ) ^ r * Dup ≤ 1 / 2 ∧
      lam ≤ (d : ℝ) ^ r * Dlow ∧ lam ≤ 1 / 2 ∧
      (K : ℝ) * d ≤ 2 * Real.sqrt (cL⁻¹) * (X : ℝ) ^ (1 - σ) at hparam
  have htranslate : (r : ℝ) * K * d ≤ X :=
    AnalyticParameters.monomialTranslation_le hX1 hrR htranslationScale hparam.2.2.2.2.2
  have hlam0 : 0 < lam := Real.rpow_pos_of_pos hXR0 _
  have hphase := HigherDerivative.norm_phaseSum_add_le_controlled_of_terminalIncrements
    (monomialValue γ a) u P
      (HigherDerivative.constantControlledSteps r K d hparam.1)
      lam hlam0 hparam.2.2.2.2.1 (by
        intro leaf hleaf
        exact monomialLeafTerminalIncrementCondition hγ hγint hX1 hXu hu2X hP
          (lt_of_lt_of_le zero_lt_one ha) hparam.1 htranslate hparam.2.2.2.1
          hparam.2.2.1 hparam.2.2.2.2.1 leaf hleaf)
  have hκ0 : 0 < κ := by
    dsimp only [κ, AnalyticParameters.shiftCountExponent]
    exact div_pos (by simpa only [ρ] using hρ.1) (by positivity)
  have hκtheta : κ ≤ theta := by
    dsimp only [κ, theta, AnalyticParameters.shiftCountExponent]
    have hRreal : (2 : ℝ) ≤ R := by exact_mod_cast hR2
    have hρ0 : 0 < ρ := by simpa only [ρ] using hρ.1
    rw [show 3 * ρ / 8 = ρ / (8 / 3) by ring]
    apply (div_le_div_iff_of_pos_left hρ0
      (by positivity : (0 : ℝ) < 32 * R) (by norm_num : (0 : ℝ) < 8 / 3)).2
    nlinarith
  have hκsigma : κ ≤ 2 * σ := by
    dsimp only [κ, σ, AnalyticParameters.shiftCountExponent,
      AnalyticParameters.roundingLossExponent]
    have hRreal : (2 : ℝ) ≤ R := by exact_mod_cast hR2
    have hρ0 : 0 < ρ := by simpa only [ρ] using hρ.1
    rw [show 2 * (ρ / 8) = ρ / 4 by ring]
    apply (div_le_div_iff_of_pos_left hρ0
      (by positivity : (0 : ℝ) < 32 * R) (by norm_num : (0 : ℝ) < 4)).2
    nlinarith
  have hKlower : (X : ℝ) ^ κ ≤ (K : ℝ) := by
    dsimp only [K, AnalyticParameters.monomialShiftCount]
    exact Nat.le_ceil _
  have hterminalEq : 1 / lam = (X : ℝ) ^ (1 - theta) := by
    dsimp only [lam, τ, σ, theta,
      AnalyticParameters.terminalScaleExponent,
      AnalyticParameters.roundingLossExponent]
    rw [one_div, ← Real.rpow_neg hXR0.le]
    congr 1
    ring
  have henvelope := AnalyticParameters.finiteHistoryEnvelope_replicate_le_rpow
    X P K d r κ σ theta (2 * Real.sqrt (cL⁻¹)) 1 (1 / lam)
      hX1 hP hparam.1 hκ0 (by positivity) (by norm_num) hκtheta hκsigma
      hKlower hparam.2.2.2.2.2 (by positivity) (by rw [hterminalEq]; simp)
  have hconst := envelopeConstant_le_monomialEnvelopeBoundConstant
    (cL := cL) hrR
  have hexp : 1 - κ / (2 : ℝ) ^ r ≤
      1 - monomialExponentialSavingExponent ρ R := by
    have hpow : (2 : ℝ) ^ r ≤ (2 : ℝ) ^ R :=
      pow_le_pow_right₀ (by norm_num) hrR
    have hposr : 0 < (2 : ℝ) ^ r := by positivity
    have hposR : 0 < (2 : ℝ) ^ R := by positivity
    have hdiv : κ / (2 : ℝ) ^ R ≤ κ / (2 : ℝ) ^ r := by
      exact div_le_div_of_nonneg_left hκ0.le hposr hpow
    dsimp only [monomialExponentialSavingExponent]
    linarith
  have hpowExp : (X : ℝ) ^ (1 - κ / (2 : ℝ) ^ r) ≤
      (X : ℝ) ^ (1 - monomialExponentialSavingExponent ρ R) :=
    Real.rpow_le_rpow_of_exponent_le hXR hexp
  calc
    ‖∑ n ∈ Finset.range P,
        HigherDerivative.phase (monomialValue γ a (u + n))‖ ≤
      RestrictedWeyl.finiteHistoryEnvelope P (1 / lam)
        (HigherDerivative.constantControlledSteps r K d hparam.1) := hphase
    _ ≤ AnalyticParameters.envelopeConstant
        (2 + 8 * (2 * Real.sqrt (cL⁻¹)) ^ 2) 1 r *
          (X : ℝ) ^ (1 - κ / (2 : ℝ) ^ r) := by
      simpa only [HigherDerivative.constantControlledSteps,
        HigherDerivative.controlledStep] using henvelope
    _ ≤ monomialEnvelopeBoundConstant cL R *
        (X : ℝ) ^ (1 - monomialExponentialSavingExponent ρ R) := by
      exact mul_le_mul hconst hpowExp (Real.rpow_nonneg hXR0.le _)
        (monomialEnvelopeBoundConstant_nonneg cL R)

/-- Uniform power saving for a translated finite monomial exponential
sum. -/
def MonomialRangeExponentialPowerSaving (γ A eta C : ℝ) : Prop :=
  ∀ (X u P : ℕ) (a : ℝ),
    2 ≤ X → X ≤ u → u ≤ 2 * X → P ≤ X →
    1 ≤ a → a ≤ (X : ℝ) ^ A →
    ‖∑ n ∈ Finset.range P,
        HigherDerivative.phase (monomialValue γ a (u + n))‖ ≤
      C * (X : ℝ) ^ (1 - eta)

/-- Unconditional uniform exponential-sum power saving for nonintegral
positive powers and polynomially growing positive coefficients. -/
theorem exists_monomialRangeExponentialPowerSaving
    {γ A : ℝ} (hγ : 0 < γ)
    (hγint : γ ∉ Set.range ((↑) : ℤ → ℝ)) (hA : 0 ≤ A) :
    ∃ eta C : ℝ, 0 < eta ∧ eta < 1 ∧ 0 ≤ C ∧
      MonomialRangeExponentialPowerSaving γ A eta C := by
  let S : ℕ := ⌈A⌉₊
  let R : ℕ := S + ⌊γ⌋₊ + 2
  let ρ := monomialFractionalExponent γ
  let cL := uniformTerminalLowerConstant γ S
  let cU := uniformTerminalUpperConstant γ S
  let cRatio := uniformTerminalRatioConstant γ S
  let eta := monomialExponentialSavingExponent ρ R
  let Cexp := monomialEnvelopeBoundConstant cL R
  have hρ := monomialFractionalExponent_pos_lt_one hγ hγint
  have hcL : 0 < cL := uniformTerminalLowerConstant_pos hγint S
  have hcU : 0 < cU := uniformTerminalUpperConstant_pos γ S
  have hcRatio : 0 < cRatio := uniformTerminalRatioConstant_pos γ S
  have hR2 : 2 ≤ R := by dsimp only [R]; omega
  have hR0 : 0 < R := by omega
  obtain ⟨Xlarge, hXlarge⟩ :=
    AnalyticParameters.exists_largeMonomialScale_threshold hρ.1 hρ.2
      hcRatio hcU hR0
  obtain ⟨Xtrans, hXtrans⟩ :=
    AnalyticParameters.exists_monomialTranslation_threshold hρ.1 hcL
      (R := R)
  let X0 : ℕ := max 2 (max Xlarge Xtrans)
  have heta0 : 0 < eta := by
    dsimp only [eta, monomialExponentialSavingExponent,
      AnalyticParameters.shiftCountExponent]
    exact div_pos
      (div_pos (by simpa only [ρ] using hρ.1)
        (mul_pos (by norm_num) (by exact_mod_cast hR0))) (by positivity)
  have heta1 : eta < 1 := by
    have hRreal : (2 : ℝ) ≤ R := by exact_mod_cast hR2
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ R := one_le_pow₀ (by norm_num)
    dsimp only [eta, monomialExponentialSavingExponent,
      AnalyticParameters.shiftCountExponent]
    have hρ1 : ρ < 1 := by simpa only [ρ] using hρ.2
    have hden : 1 ≤ 32 * (R : ℝ) * (2 : ℝ) ^ R := by nlinarith
    rw [div_div]
    apply (div_lt_one (by positivity : (0 : ℝ) < 32 * (R : ℝ) * (2 : ℝ) ^ R)).2
    calc
      ρ < 1 := hρ1
      _ ≤ 32 * (R : ℝ) * (2 : ℝ) ^ R := hden
  have hCexp : 0 ≤ Cexp := monomialEnvelopeBoundConstant_nonneg cL R
  refine ⟨eta, Cexp + X0, heta0, heta1, by positivity, ?_⟩
  intro X u P a hX2 hXu hu2X hP ha haA
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  by_cases hXX0 : X0 ≤ X
  · have hXlargeX : Xlarge ≤ X :=
      (le_max_left Xlarge Xtrans).trans
        ((le_max_right 2 (max Xlarge Xtrans)).trans hXX0)
    have hXtransX : Xtrans ≤ X :=
      (le_max_right Xlarge Xtrans).trans
        ((le_max_right 2 (max Xlarge Xtrans)).trans hXX0)
    have hlarge : AnalyticParameters.IsLargeMonomialScale ρ cRatio cU R X :=
      hXlarge X hXlargeX
    have htrans : 2 * Real.sqrt (cL⁻¹) * R ≤
        (X : ℝ) ^ AnalyticParameters.roundingLossExponent ρ :=
      hXtrans X hXtransX
    obtain ⟨s, hsS, hscale⟩ :=
      exists_coefficientScale_le_natCeil (show (1 : ℝ) < X by exact_mod_cast hX2)
        ha haA
    have hsS' : s ≤ S := by simpa only [S] using hsS
    have hrR : monomialDifferencingDepth γ s ≤ R := by
      rw [monomialDifferencingDepth_eq]
      dsimp only [R, S]
      omega
    have hmain := norm_monomial_phase_sum_range_le_large
      hγ hγint hXu hu2X hP ha hscale hsS' hrR hlarge htrans
    calc
      ‖∑ n ∈ Finset.range P,
          HigherDerivative.phase (monomialValue γ a (u + n))‖ ≤
        Cexp * (X : ℝ) ^ (1 - eta) := by simpa only [Cexp, cL, eta, ρ] using hmain
      _ ≤ (Cexp + X0) * (X : ℝ) ^ (1 - eta) := by
        gcongr
        exact le_add_of_nonneg_right (Nat.cast_nonneg X0)
  · have hXlt : X < X0 := lt_of_not_ge hXX0
    have hnorm : ‖∑ n ∈ Finset.range P,
        HigherDerivative.phase (monomialValue γ a (u + n))‖ ≤ P := by
      calc
        _ ≤ ∑ n ∈ Finset.range P,
            ‖HigherDerivative.phase (monomialValue γ a (u + n))‖ :=
          norm_sum_le _ _
        _ = P := by simp
    have hPX0 : (P : ℝ) ≤ X0 := by exact_mod_cast hP.trans (Nat.le_of_lt hXlt)
    have hpow1 : (1 : ℝ) ≤ (X : ℝ) ^ (1 - eta) :=
      Real.one_le_rpow hXR (by linarith)
    calc
      ‖∑ n ∈ Finset.range P,
          HigherDerivative.phase (monomialValue γ a (u + n))‖ ≤ P := hnorm
      _ ≤ (X0 : ℝ) := hPX0
      _ ≤ (Cexp + X0) * (X : ℝ) ^ (1 - eta) := by
        have hCX : (X0 : ℝ) ≤ Cexp + X0 := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hpow1 (by positivity : 0 ≤ Cexp + X0)]

/-- The integer Fourier mode in the Erdős--Turán sum is exactly the real
Fourier phase used by the higher-derivative estimate. -/
lemma norm_exponentialSum_monomial_Ico_eq_phase_sum_range
    (γ a : ℝ) (u v : ℕ) (h : ℤ) :
    ‖ErdosTuran.exponentialSum (Finset.Ico u v) (monomialValue γ a) h‖ =
      ‖∑ n ∈ Finset.range (v - u),
        HigherDerivative.phase ((h : ℝ) * a * ((u + n : ℕ) : ℝ) ^ γ)‖ := by
  unfold ErdosTuran.exponentialSum
  rw [Finset.sum_Ico_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  unfold monomialValue HigherDerivative.phase
  rw [fourier_coe_apply, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

/-- Reversing the sign of a real Fourier phase complex-conjugates the sum
and hence does not change its norm. -/
lemma norm_sum_phase_neg (s : Finset ℕ) (f : ℕ → ℝ) :
    ‖∑ n ∈ s, HigherDerivative.phase (-f n)‖ =
      ‖∑ n ∈ s, HigherDerivative.phase (f n)‖ := by
  have hneg (x : ℝ) :
      HigherDerivative.phase (-x) =
        starRingEnd ℂ (HigherDerivative.phase x) := by
    change ((Real.fourierChar (-x) : Circle) : ℂ) =
      starRingEnd ℂ ((Real.fourierChar x : Circle) : ℂ)
    rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  simp_rw [hneg]
  rw [← map_sum]
  exact norm_star _

/-- The norm of a monomial phase sum at an integer frequency depends only
on the absolute value of the frequency. -/
lemma norm_sum_phase_int_mul_eq_natAbs
    (s : Finset ℕ) (h : ℤ) (a γ : ℝ) (m : ℕ → ℕ) :
    ‖∑ n ∈ s, HigherDerivative.phase
        ((h : ℝ) * a * ((m n : ℕ) : ℝ) ^ γ)‖ =
      ‖∑ n ∈ s, HigherDerivative.phase
        ((h.natAbs : ℝ) * a * ((m n : ℕ) : ℝ) ^ γ)‖ := by
  have hnabs : (h.natAbs : ℝ) = |(h : ℝ)| := by
    have hz := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs h)
    simpa using hz
  by_cases hh : 0 ≤ h
  · have hhR : (0 : ℝ) ≤ h := by exact_mod_cast hh
    have heq : (h.natAbs : ℝ) = (h : ℝ) := by
      rw [hnabs, abs_of_nonneg hhR]
    rw [heq]
  · have hhR : (h : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hh)
    have heq : (h : ℝ) = -(h.natAbs : ℝ) := by
      rw [hnabs, abs_of_neg hhR]
      ring
    rw [heq]
    calc
      ‖∑ n ∈ s, HigherDerivative.phase
          (-(h.natAbs : ℝ) * a * ((m n : ℕ) : ℝ) ^ γ)‖ =
          ‖∑ n ∈ s, HigherDerivative.phase
            (-((h.natAbs : ℝ) * a * ((m n : ℕ) : ℝ) ^ γ))‖ := by
        congr 1
        apply Finset.sum_congr rfl
        intro n hn
        congr 2
        ring
      _ =
          ‖∑ n ∈ s, HigherDerivative.phase
            ((h.natAbs : ℝ) * a * ((m n : ℕ) : ℝ) ^ γ)‖ :=
        norm_sum_phase_neg s
          (fun n => (h.natAbs : ℝ) * a * ((m n : ℕ) : ℝ) ^ γ)

/-- A uniform bound for all nonzero Fourier modes in the truncated window
gives a convenient coarse form of Erdős--Turán. -/
lemma abs_monomialIntervalError_le_of_uniform_exponentialSum
    (γ a b B δ : ℝ) (u v H : ℕ)
    (hH : 1 ≤ H) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hExp : ∀ h ∈ ErdosTuran.nonzeroFrequencyWindow H,
      ‖ErdosTuran.exponentialSum (Finset.Ico u v) (monomialValue γ a) h‖ ≤ B) :
    |monomialIntervalError γ a b u v| ≤
      (δ + 4 / (δ * H)) * (Finset.Ico u v).card + 16 * H * B := by
  classical
  have hone : (1 : ℤ) ∈ ErdosTuran.nonzeroFrequencyWindow H := by
    simp [ErdosTuran.nonzeroFrequencyWindow, ErdosTuran.frequencyWindow, hH]
  have hB : 0 ≤ B :=
    (norm_nonneg (ErdosTuran.exponentialSum
      (Finset.Ico u v) (monomialValue γ a) 1)).trans (hExp 1 hone)
  have hET := ErdosTuran.erdosTuran_fract_count
    (Finset.Ico u v) (monomialValue γ a) H δ b hH hδ hδ1 hb0 hb1
  rw [show
    |(((Finset.Ico u v).filter fun n =>
        Int.fract (monomialValue γ a n) < b).card : ℝ) -
          b * (Finset.Ico u v).card| =
      |monomialIntervalError γ a b u v| by
        simp [monomialIntervalError, monomialIntervalCount, Nat.card_Ico]] at hET
  refine hET.trans ?_
  have hterm : ∀ h ∈ ErdosTuran.nonzeroFrequencyWindow H,
      8 / |(h : ℝ)| *
          ‖ErdosTuran.exponentialSum (Finset.Ico u v) (monomialValue γ a) h‖ ≤
        8 * B := by
    intro h hh
    have hh0 : h ≠ 0 := Finset.ne_of_mem_erase hh
    have habs : (1 : ℝ) ≤ |(h : ℝ)| := by
      exact_mod_cast Int.one_le_abs hh0
    have habs0 : 0 < |(h : ℝ)| := lt_of_lt_of_le zero_lt_one habs
    have hcoeff : 8 / |(h : ℝ)| ≤ (8 : ℝ) := by
      rw [div_le_iff₀ habs0]
      nlinarith
    calc
      8 / |(h : ℝ)| *
            ‖ErdosTuran.exponentialSum (Finset.Ico u v) (monomialValue γ a) h‖
          ≤ 8 * ‖ErdosTuran.exponentialSum
              (Finset.Ico u v) (monomialValue γ a) h‖ :=
        mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
      _ ≤ 8 * B := by gcongr; exact hExp h hh
  have hsum :
      (∑ h ∈ ErdosTuran.nonzeroFrequencyWindow H,
        8 / |(h : ℝ)| *
          ‖ErdosTuran.exponentialSum (Finset.Ico u v) (monomialValue γ a) h‖) ≤
        (ErdosTuran.nonzeroFrequencyWindow H).card * (8 * B) := by
    calc
      _ ≤ ∑ _h ∈ ErdosTuran.nonzeroFrequencyWindow H, 8 * B := by
        exact Finset.sum_le_sum fun h hh => hterm h hh
      _ = (ErdosTuran.nonzeroFrequencyWindow H).card * (8 * B) := by simp
  have hcardNat :
      (ErdosTuran.nonzeroFrequencyWindow H).card ≤ 2 * H := by
    simp [ErdosTuran.nonzeroFrequencyWindow, ErdosTuran.frequencyWindow,
      Int.card_Icc]
    omega
  have hcard :
      ((ErdosTuran.nonzeroFrequencyWindow H).card : ℝ) ≤ 2 * H := by
    exact_mod_cast hcardNat
  have htail :
      ((ErdosTuran.nonzeroFrequencyWindow H).card : ℝ) * (8 * B) ≤
        16 * H * B := by
    calc
      ((ErdosTuran.nonzeroFrequencyWindow H).card : ℝ) * (8 * B) ≤
          (2 * H) * (8 * B) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg (by norm_num) hB)
      _ = 16 * H * B := by ring
  exact add_le_add (le_refl _) (hsum.trans htail)

/-- Exact dyadic derivative window at the adaptive order.  Retaining `a`
on both sides is important: the ratio between the upper and lower bounds is
then a constant depending on the (bounded) derivative order, not on `X`. -/
lemma abs_iter_deriv_scaled_rpow_dyadic_bounds_exact
    {γ a X x : ℝ} {s : ℕ}
    (hγ : 0 < γ)
    (hγint : γ ∉ Set.range ((↑) : ℤ → ℝ))
    (hX : 0 < X) (hXx : X ≤ x) (hx2X : x ≤ 2 * X)
    (ha : 0 < a) :
    let l := adaptiveDerivativeOrder γ s
    let c := |(descPochhammer ℝ l).eval γ|
    let q := γ - (l : ℝ)
    c * a * (2 * X) ^ q ≤
        |deriv^[l] (fun y : ℝ ↦ a * y ^ γ) x| ∧
      |deriv^[l] (fun y : ℝ ↦ a * y ^ γ) x| ≤
        c * a * X ^ q := by
  dsimp only
  let l := adaptiveDerivativeOrder γ s
  let c := |(descPochhammer ℝ l).eval γ|
  let q := γ - (l : ℝ)
  have hx : 0 < x := hX.trans_le hXx
  have h2X : 0 < 2 * X := mul_pos (by norm_num) hX
  have hq : q < 0 := sub_neg.mpr (lt_adaptiveDerivativeOrder hγ hγint s)
  have hc : 0 < c := abs_pos.mpr
    (descPochhammer_eval_ne_zero_of_nonint γ hγint l)
  rw [iter_deriv_scaled_rpow]
  rw [abs_mul, abs_mul, abs_of_pos ha]
  rw [abs_of_pos (Real.rpow_pos_of_pos hx q)]
  change
    c * a * (2 * X) ^ q ≤
        a * c * x ^ q ∧
      a * c * x ^ q ≤
        c * a * X ^ q
  constructor
  · have hpow : (2 * X) ^ q ≤ x ^ q :=
      Real.rpow_le_rpow_of_nonpos hx hx2X hq.le
    calc
      c * a * (2 * X) ^ q ≤ c * a * x ^ q := by gcongr
      _ = a * c * x ^ q := by ring
  · have hpow : x ^ q ≤ X ^ q :=
      Real.rpow_le_rpow_of_nonpos hX hXx hq.le
    calc
      a * c * x ^ q ≤ a * c * X ^ q := by gcongr
      _ = c * a * X ^ q := by ring

/-- Coefficient-scale form of the exact derivative window.  This exhibits
the derivative size using only powers of `X`, which is convenient when
selecting a power-saving exponent uniformly over all coefficients. -/
lemma abs_iter_deriv_scaled_rpow_dyadic_bounds
    {γ a X x : ℝ} {s : ℕ}
    (hγ : 0 < γ)
    (hγint : γ ∉ Set.range ((↑) : ℤ → ℝ))
    (hX : 0 < X) (hXx : X ≤ x) (hx2X : x ≤ 2 * X)
    (ha : 0 < a) (hscale : IsCoefficientScale X a s) :
    let l := adaptiveDerivativeOrder γ s
    let c := |(descPochhammer ℝ l).eval γ|
    let q := γ - (l : ℝ)
    c * X ^ (s : ℝ) * (2 * X) ^ q ≤
        |deriv^[l] (fun y : ℝ ↦ a * y ^ γ) x| ∧
      |deriv^[l] (fun y : ℝ ↦ a * y ^ γ) x| ≤
        c * X ^ ((s : ℝ) + 1) * X ^ q := by
  dsimp only
  let l := adaptiveDerivativeOrder γ s
  let c := |(descPochhammer ℝ l).eval γ|
  let q := γ - (l : ℝ)
  have hexact := abs_iter_deriv_scaled_rpow_dyadic_bounds_exact
    hγ hγint hX hXx hx2X ha (s := s)
  dsimp only at hexact
  constructor
  · calc
      c * X ^ (s : ℝ) * (2 * X) ^ q ≤
          c * a * (2 * X) ^ q := by gcongr; exact hscale.1
      _ ≤ |deriv^[l] (fun y : ℝ ↦ a * y ^ γ) x| := hexact.1
  · calc
      |deriv^[l] (fun y : ℝ ↦ a * y ^ γ) x| ≤
          c * a * X ^ q := hexact.2
      _ ≤ c * X ^ ((s : ℝ) + 1) * X ^ q := by
        gcongr
        exact hscale.2.le

/-- Uniform dyadic interval discrepancy with a power saving.  The
coefficient may grow like `X^A`; the constants and saving depend only on
`γ` and `A`. -/
def MonomialIntervalPowerSaving (γ A η C : ℝ) : Prop :=
  ∀ (X u v : ℕ) (a b : ℝ),
    2 ≤ X → X ≤ u → u ≤ v → v ≤ 2 * X →
    1 ≤ a → a ≤ (X : ℝ) ^ A →
    0 ≤ b → b ≤ 1 →
    |monomialIntervalError γ a b u v| ≤
      C * (X : ℝ) ^ (1 - η)

/-- Erdős--Turán, with a power-sized frequency cutoff, upgrades the
uniform monomial exponential-sum estimate to a uniform discrepancy
estimate on every dyadic subinterval. -/
theorem exists_monomialIntervalPowerSaving
    {γ A : ℝ} (hγ : 0 < γ)
    (hγint : γ ∉ Set.range ((↑) : ℤ → ℝ)) (hA : 0 ≤ A) :
    ∃ eta C : ℝ, 0 < eta ∧ eta < 1 ∧ 0 ≤ C ∧
      MonomialIntervalPowerSaving γ A eta C := by
  obtain ⟨etaExp, Cexp, hetaExp0, hetaExp1, hCexp,
      hExp⟩ := exists_monomialRangeExponentialPowerSaving
        hγ hγint (show 0 ≤ A + 1 by linarith)
  let eta : ℝ := etaExp / 8
  have heta0 : 0 < eta := by dsimp only [eta]; positivity
  have heta1 : eta < 1 := by dsimp only [eta]; linarith
  have htwoeta : 2 * eta < 1 := by dsimp only [eta]; linarith
  have hpowGap : 1 - etaExp + 2 * eta ≤ 1 - eta := by
    dsimp only [eta]
    linarith
  have ht : Filter.Tendsto (fun X : ℕ ↦ (X : ℝ) ^ eta)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop heta0).comp tendsto_natCast_atTop_atTop
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.1
    (ht.eventually (Filter.eventually_ge_atTop (2 : ℝ)))
  let C : ℝ := 9 + 16 * Cexp + X0
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨eta, C, heta0, heta1, hC, ?_⟩
  intro X u v a b hX2 hXu huv hv2X ha haA hb0 hb1
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hXR0 : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hXR
  have hP : v - u ≤ X := by omega
  by_cases hXX0 : X0 ≤ X
  · let H : ℕ := ⌊(X : ℝ) ^ (2 * eta)⌋₊
    let delta : ℝ := (X : ℝ) ^ (-eta)
    let B : ℝ := Cexp * (X : ℝ) ^ (1 - etaExp)
    have hXeta2 : 2 ≤ (X : ℝ) ^ eta := hX0 X hXX0
    have hXtwoeta : 2 ≤ (X : ℝ) ^ (2 * eta) := by
      rw [show 2 * eta = eta + eta by ring, Real.rpow_add hXR0]
      nlinarith
    have hH : 1 ≤ H := by
      apply (Nat.floor_pos).2
      exact hXtwoeta.trans' (by norm_num)
    have hHlower : (X : ℝ) ^ (2 * eta) / 2 ≤ (H : ℝ) := by
      exact AnalyticParameters.half_le_natFloor hXtwoeta
    have hHupper : (H : ℝ) ≤ (X : ℝ) ^ (2 * eta) := by
      exact Nat.floor_le (Real.rpow_nonneg hXR0.le _)
    have hdelta0 : 0 < delta := by
      dsimp only [delta]
      positivity
    have hdelta1 : delta ≤ 1 := by
      dsimp only [delta]
      exact Real.rpow_le_one_of_one_le_of_nonpos hXR (by linarith)
    have hdeltaHlower : (X : ℝ) ^ eta / 2 ≤ delta * H := by
      calc
        (X : ℝ) ^ eta / 2 =
            (X : ℝ) ^ (-eta) * ((X : ℝ) ^ (2 * eta) / 2) := by
          rw [show 2 * eta = eta + eta by ring,
            Real.rpow_add hXR0, Real.rpow_neg hXR0.le]
          field_simp
        _ ≤ (X : ℝ) ^ (-eta) * H := by
          gcongr
        _ = delta * H := by rfl
    have hdeltaH0 : 0 < delta * H :=
      mul_pos hdelta0 (by exact_mod_cast (show 0 < H by omega))
    have htailCoeff : 4 / (delta * H) ≤ 8 * (X : ℝ) ^ (-eta) := by
      have hhalf0 : 0 < (X : ℝ) ^ eta / 2 := by positivity
      calc
        4 / (delta * H) ≤ 4 / ((X : ℝ) ^ eta / 2) :=
          div_le_div_of_nonneg_left (by norm_num) hhalf0 hdeltaHlower
        _ = 8 * (X : ℝ) ^ (-eta) := by
          rw [Real.rpow_neg hXR0.le]
          field_simp
          ring
    have hcoeff : delta + 4 / (delta * H) ≤
        9 * (X : ℝ) ^ (-eta) := by
      dsimp only [delta]
      linarith
    have hcard : ((Finset.Ico u v).card : ℝ) ≤ X := by
      simp only [Nat.card_Ico]
      exact_mod_cast hP
    have hfirst :
        (delta + 4 / (delta * H)) * (Finset.Ico u v).card ≤
          9 * (X : ℝ) ^ (1 - eta) := by
      calc
        (delta + 4 / (delta * H)) * (Finset.Ico u v).card ≤
            (9 * (X : ℝ) ^ (-eta)) * X := by
          exact mul_le_mul hcoeff hcard (by positivity) (by positivity)
        _ = 9 * (X : ℝ) ^ (1 - eta) := by
          rw [show 1 - eta = -eta + 1 by ring,
            Real.rpow_add hXR0, Real.rpow_one]
          ring
    have hmode : ∀ h ∈ ErdosTuran.nonzeroFrequencyWindow H,
        ‖ErdosTuran.exponentialSum (Finset.Ico u v)
          (monomialValue γ a) h‖ ≤ B := by
      intro h hh
      have hh0 : h ≠ 0 := Finset.ne_of_mem_erase hh
      have hhnat1 : 1 ≤ h.natAbs := Int.natAbs_pos.mpr hh0
      have hhnatH : h.natAbs ≤ H :=
        (ErdosTuran.mem_frequencyWindow_iff H h).mp (Finset.mem_of_mem_erase hh)
      let ah : ℝ := (h.natAbs : ℝ) * a
      have hah1 : 1 ≤ ah := by
        dsimp only [ah]
        nlinarith [show (1 : ℝ) ≤ h.natAbs by exact_mod_cast hhnat1]
      have hhHreal : (h.natAbs : ℝ) ≤ H := by exact_mod_cast hhnatH
      have hahH : ah ≤ (X : ℝ) ^ (2 * eta) * (X : ℝ) ^ A := by
        dsimp only [ah]
        exact mul_le_mul (hhHreal.trans hHupper) haA (by linarith)
          (Real.rpow_nonneg hXR0.le _)
      have hAexp : A + 2 * eta ≤ A + 1 := by linarith
      have hah : ah ≤ (X : ℝ) ^ (A + 1) := by
        calc
          ah ≤ (X : ℝ) ^ (2 * eta) * (X : ℝ) ^ A := hahH
          _ = (X : ℝ) ^ (A + 2 * eta) := by
            rw [← Real.rpow_add hXR0]
            congr 1
            ring
          _ ≤ (X : ℝ) ^ (A + 1) :=
            Real.rpow_le_rpow_of_exponent_le hXR hAexp
      rw [norm_exponentialSum_monomial_Ico_eq_phase_sum_range]
      rw [norm_sum_phase_int_mul_eq_natAbs
        (Finset.range (v - u)) h a γ (fun n => u + n)]
      simpa only [B, ah, monomialValue, mul_assoc] using
        hExp X u (v - u) ah hX2 hXu (huv.trans hv2X) hP hah1 hah
    have hET := abs_monomialIntervalError_le_of_uniform_exponentialSum
      γ a b B delta u v H hH hdelta0 hdelta1 hb0 hb1 hmode
    have hsecond : 16 * H * B ≤
        16 * Cexp * (X : ℝ) ^ (1 - eta) := by
      have hB0 : 0 ≤ B := by dsimp only [B]; positivity
      have hraw : 16 * (H : ℝ) * B ≤
          16 * (X : ℝ) ^ (2 * eta) *
            (Cexp * (X : ℝ) ^ (1 - etaExp)) := by
        gcongr
      calc
        16 * H * B ≤ 16 * (X : ℝ) ^ (2 * eta) *
            (Cexp * (X : ℝ) ^ (1 - etaExp)) := hraw
        _ = 16 * Cexp * (X : ℝ) ^ (1 - etaExp + 2 * eta) := by
          rw [Real.rpow_add hXR0]
          ring
        _ ≤ 16 * Cexp * (X : ℝ) ^ (1 - eta) := by
          gcongr
    calc
      |monomialIntervalError γ a b u v| ≤
          (delta + 4 / (delta * H)) * (Finset.Ico u v).card +
            16 * H * B := hET
      _ ≤ (9 + 16 * Cexp) * (X : ℝ) ^ (1 - eta) := by
        calc
          _ ≤ 9 * (X : ℝ) ^ (1 - eta) +
              16 * Cexp * (X : ℝ) ^ (1 - eta) :=
            add_le_add hfirst hsecond
          _ = _ := by ring
      _ ≤ C * (X : ℝ) ^ (1 - eta) := by
        apply mul_le_mul_of_nonneg_right
        · dsimp only [C]
          linarith
        · positivity
  · have hXlt : X < X0 := lt_of_not_ge hXX0
    have htriv := abs_monomialIntervalError_le_length γ a b u v hb0 hb1
    have hlen : ((v - u : ℕ) : ℝ) ≤ X0 := by
      exact_mod_cast hP.trans (Nat.le_of_lt hXlt)
    have hpow1 : (1 : ℝ) ≤ (X : ℝ) ^ (1 - eta) :=
      Real.one_le_rpow hXR (by linarith)
    calc
      |monomialIntervalError γ a b u v| ≤ (v - u : ℕ) := htriv
      _ ≤ X0 := hlen
      _ ≤ C * (X : ℝ) ^ (1 - eta) := by
        have hX0C : (X0 : ℝ) ≤ C := by
          dsimp only [C]
          linarith
        nlinarith [mul_le_mul_of_nonneg_left hpow1 hC]

/-- Prefix discrepancy in the positive range `[1,N)`. -/
def MonomialPrefixPowerSaving (γ A η C : ℝ) : Prop :=
  ∀ (N : ℕ) (a b : ℝ),
    2 ≤ N → 1 ≤ a → a ≤ (N : ℝ) ^ A →
    0 ≤ b → b ≤ 1 →
    |monomialIntervalError γ a b 1 N| ≤
      C * (N : ℝ) ^ (1 - η)

/-- Quantitative halving lemma behind the dyadic-to-prefix reduction.

The recursion stops as soon as `a > M^B`.  At that point the whole
remaining prefix has length at most `2 * a^(1/B)`.  Otherwise the last
half is a legal dyadic interval and the induction continues. -/
lemma prefix_error_le_of_intervalPowerSaving_aux
    {γ B η C : ℝ}
    (hB : 0 < B) (hη0 : 0 < η) (hη1 : η < 1) (hC : 0 ≤ C)
    (hinterval : MonomialIntervalPowerSaving γ B η C) :
    ∀ (N : ℕ) (a b : ℝ), 1 ≤ a → 0 ≤ b → b ≤ 1 →
      |monomialIntervalError γ a b 1 N| ≤
        2 * a ^ B⁻¹ +
          (C / (((3 / 2 : ℝ) ^ (1 - η)) - 1)) *
            (N : ℝ) ^ (1 - η) := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro a b ha hb0 hb1
      let r : ℝ := 1 - η
      let q : ℝ := (3 / 2 : ℝ) ^ r
      let K : ℝ := C / (q - 1)
      have hr0 : 0 < r := by dsimp [r]; linarith
      have hq1 : 1 < q := by
        dsimp [q]
        exact Real.one_lt_rpow (by norm_num) hr0
      have hK0 : 0 ≤ K := div_nonneg hC (sub_nonneg.mpr hq1.le)
      by_cases hN : N < 4
      · have htriv := abs_monomialIntervalError_le_length γ a b 1 N hb0 hb1
        have hroot : 1 ≤ a ^ B⁻¹ :=
          Real.one_le_rpow ha (inv_nonneg.mpr hB.le)
        have hpowN : 0 ≤ (N : ℝ) ^ r :=
          Real.rpow_nonneg (Nat.cast_nonneg N) r
        change |monomialIntervalError γ a b 1 N| ≤
          2 * a ^ B⁻¹ + K * (N : ℝ) ^ r
        have hlen : ((N - 1 : ℕ) : ℝ) ≤ 2 := by
          exact_mod_cast (show N - 1 ≤ 2 by omega)
        exact htriv.trans (by nlinarith)
      · have hN4 : 4 ≤ N := by omega
        let M : ℕ := (N + 1) / 2
        have hM2 : 2 ≤ M := by dsimp [M]; omega
        have hMN : M ≤ N := by dsimp [M]; omega
        have hMltN : M < N := by dsimp [M]; omega
        have hN2M : N ≤ 2 * M := by dsimp [M]; omega
        have hratioNat : 3 * M ≤ 2 * N := by dsimp [M]; omega
        by_cases hscale : a ≤ (M : ℝ) ^ B
        · have hfirst := ih M hMltN a b ha hb0 hb1
          have hlast := hinterval M M N a b hM2 le_rfl hMN hN2M
            ha hscale hb0 hb1
          have hadd := monomialIntervalError_add γ a b
            (u := 1) (m := M) (v := N) (by omega) hMN
          have hratio : (3 / 2 : ℝ) * (M : ℝ) ≤ (N : ℝ) := by
            have hratioReal : (3 : ℝ) * M ≤ 2 * N := by
              exact_mod_cast hratioNat
            linarith
          have hpowRatio : q * (M : ℝ) ^ r ≤ (N : ℝ) ^ r := by
            have hp := Real.rpow_le_rpow (by positivity) hratio hr0.le
            rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg M)] at hp
            exact hp
          have hKC : K + C = K * q := by
            dsimp [K]
            field_simp [sub_ne_zero.mpr hq1.ne']
            ring
          have hcontract : (K + C) * (M : ℝ) ^ r ≤
              K * (N : ℝ) ^ r := by
            rw [hKC, mul_assoc]
            exact mul_le_mul_of_nonneg_left hpowRatio hK0
          change |monomialIntervalError γ a b 1 N| ≤
            2 * a ^ B⁻¹ + K * (N : ℝ) ^ r
          change |monomialIntervalError γ a b 1 M| ≤
            2 * a ^ B⁻¹ + K * (M : ℝ) ^ r at hfirst
          change |monomialIntervalError γ a b M N| ≤
            C * (M : ℝ) ^ r at hlast
          calc
            |monomialIntervalError γ a b 1 N| =
                |monomialIntervalError γ a b 1 M +
                  monomialIntervalError γ a b M N| := by rw [hadd]
            _ ≤ |monomialIntervalError γ a b 1 M| +
                |monomialIntervalError γ a b M N| := abs_add_le _ _
            _ ≤ (2 * a ^ B⁻¹ + K * (M : ℝ) ^ r) +
                C * (M : ℝ) ^ r := add_le_add hfirst hlast
            _ = 2 * a ^ B⁻¹ + (K + C) * (M : ℝ) ^ r := by ring
            _ ≤ 2 * a ^ B⁻¹ + K * (N : ℝ) ^ r := by gcongr
        · have hMa : (M : ℝ) < a ^ B⁻¹ := by
            have hMBa : (M : ℝ) ^ B < a := lt_of_not_ge hscale
            have hp := Real.rpow_lt_rpow (by positivity) hMBa
              (inv_pos.mpr hB)
            rw [← Real.rpow_mul (Nat.cast_nonneg M)] at hp
            have hBB : B * B⁻¹ = 1 := mul_inv_cancel₀ hB.ne'
            rw [hBB, Real.rpow_one] at hp
            exact hp
          have htriv := abs_monomialIntervalError_le_length γ a b 1 N hb0 hb1
          have hlenN : ((N - 1 : ℕ) : ℝ) ≤ 2 * M := by
            exact_mod_cast (show N - 1 ≤ 2 * M by omega)
          have hpowN : 0 ≤ (N : ℝ) ^ r :=
            Real.rpow_nonneg (Nat.cast_nonneg N) r
          change |monomialIntervalError γ a b 1 N| ≤
            2 * a ^ B⁻¹ + K * (N : ℝ) ^ r
          exact htriv.trans (by nlinarith)

/-- A dyadic interval power saving, with a slightly larger coefficient
growth allowance, gives a power saving for the whole positive prefix.

The exponent `2*A+1` is a convenient fixed choice.  The stopped initial
piece has size `O(N^(A/(2*A+1)))`, while the dyadic pieces retain the
original saving. -/
theorem exists_monomialPrefixPowerSaving_of_interval
    {γ A η C : ℝ}
    (hA : 0 ≤ A) (hη0 : 0 < η) (hη1 : η < 1) (hC : 0 ≤ C)
    (hinterval : MonomialIntervalPowerSaving γ (2 * A + 1) η C) :
    ∃ η' C' : ℝ, 0 < η' ∧ η' < 1 ∧ 0 ≤ C' ∧
      MonomialPrefixPowerSaving γ A η' C' := by
  let B : ℝ := 2 * A + 1
  have hB : 0 < B := by dsimp [B]; linarith
  let δ : ℝ := 1 - A / B
  have hδ0 : 0 < δ := by
    dsimp [δ]
    rw [sub_pos, div_lt_one hB]
    dsimp [B]
    linarith
  let η' : ℝ := min η δ
  have hη'0 : 0 < η' := lt_min hη0 hδ0
  have hη'1 : η' < 1 :=
    (min_le_left η δ).trans_lt hη1
  let r : ℝ := 1 - η
  let q : ℝ := (3 / 2 : ℝ) ^ r
  let K : ℝ := C / (q - 1)
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hq1 : 1 < q := by
    dsimp [q]
    exact Real.one_lt_rpow (by norm_num) hr0
  have hK0 : 0 ≤ K := div_nonneg hC (sub_nonneg.mpr hq1.le)
  refine ⟨η', 2 + K, hη'0, hη'1, by positivity, ?_⟩
  intro N a b hN ha haN hb0 hb1
  have haux := prefix_error_le_of_intervalPowerSaving_aux
    hB hη0 hη1 hC hinterval N a b ha hb0 hb1
  change |monomialIntervalError γ a b 1 N| ≤
    2 * a ^ B⁻¹ + K * (N : ℝ) ^ r at haux
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hroot : a ^ B⁻¹ ≤ (N : ℝ) ^ (A / B) := by
    have hp := Real.rpow_le_rpow (by linarith) haN (inv_nonneg.mpr hB.le)
    rw [← Real.rpow_mul (Nat.cast_nonneg N)] at hp
    convert hp using 1
    field_simp [hB.ne']
  have hAexp : A / B ≤ 1 - η' := by
    have hη'δ : η' ≤ δ := min_le_right _ _
    dsimp [δ] at hη'δ
    linarith
  have hreta : r ≤ 1 - η' := by
    have hη'η : η' ≤ η := min_le_left _ _
    dsimp [r]
    linarith
  have hroot' : a ^ B⁻¹ ≤ (N : ℝ) ^ (1 - η') :=
    hroot.trans (Real.rpow_le_rpow_of_exponent_le hN1 hAexp)
  have hrpow : (N : ℝ) ^ r ≤ (N : ℝ) ^ (1 - η') :=
    Real.rpow_le_rpow_of_exponent_le hN1 hreta
  have htarget_nonneg : 0 ≤ (N : ℝ) ^ (1 - η') :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc
    |monomialIntervalError γ a b 1 N| ≤
        2 * a ^ B⁻¹ + K * (N : ℝ) ^ r := haux
    _ ≤ 2 * (N : ℝ) ^ (1 - η') +
        K * (N : ℝ) ^ (1 - η') := by gcongr
    _ = (2 + K) * (N : ℝ) ^ (1 - η') := by ring

/-- Every positive nonintegral monomial has a uniform prefix discrepancy
power saving, uniformly for coefficients of any fixed polynomial growth. -/
theorem exists_monomialPrefixPowerSaving
    {γ A : ℝ} (hγ : 0 < γ)
    (hγint : γ ∉ Set.range ((↑) : ℤ → ℝ)) (hA : 0 ≤ A) :
    ∃ eta C : ℝ, 0 < eta ∧ eta < 1 ∧ 0 ≤ C ∧
      MonomialPrefixPowerSaving γ A eta C := by
  obtain ⟨eta, C, heta0, heta1, hC, hinterval⟩ :=
    exists_monomialIntervalPowerSaving hγ hγint
      (show 0 ≤ 2 * A + 1 by linarith)
  exact exists_monomialPrefixPowerSaving_of_interval
    hA heta0 heta1 hC hinterval

end Erdos1149
