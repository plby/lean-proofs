import ErdosProblems.Erdos378.ReciprocalExponential
import BoundedGaps.BombieriVinogradov.Analytic.GranvilleRamarePrefix
import BoundedGaps.BombieriVinogradov.Analytic.VaughanThirdCoefficient
import BoundedGaps.BombieriVinogradov.Analytic.VaughanTwistedDecomposition
import BoundedGaps.BombieriVinogradov.Analytic.PositiveDivisorPairReindex

/-!
# Prime reciprocal exponential sums

This file adapts the axiom-free Vaughan decomposition in the local
`BoundedGaps` package from Dirichlet-character twists to an arbitrary complex
weight.  The specialization used below is the real reciprocal phase
`exp (2 * pi * I * X / n)`.

The finite identities in this file deliberately retain the weight at the
product `m * k`; no multiplicativity of the weight is assumed.
-/

namespace Erdos378
namespace PrimeReciprocal

open scoped BigOperators ArithmeticFunction.vonMangoldt ComplexConjugate

open BoundedGaps.Maynard
open ReciprocalExponential

noncomputable section

/-- A von Mangoldt sum with an arbitrary complex weight. -/
def weightedChebyshevSum (w : ℕ → ℂ) (y : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y,
    (ArithmeticFunction.vonMangoldt n : ℂ) * w n

/-- The first term of the arbitrarily weighted Vaughan decomposition. -/
def weightedVaughanSumOne (w : ℕ → ℂ) (U : ℝ) (y : ℕ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 y).filter (fun n : ℕ ↦ (n : ℝ) ≤ U),
    (ArithmeticFunction.vonMangoldt n : ℂ) * w n

/-- The second term of the arbitrarily weighted Vaughan decomposition. -/
def weightedVaughanSumTwo (w : ℕ → ℂ) (V : ℝ) (y : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y,
    (((∑ hd ∈ n.divisorsAntidiagonal.filter
        (fun hd : ℕ × ℕ ↦ (hd.2 : ℝ) ≤ V),
        (ArithmeticFunction.moebius hd.2 : ℝ) * Real.log hd.1 : ℝ) : ℂ) * w n)

/-- The third term of the arbitrarily weighted Vaughan decomposition. -/
def weightedVaughanSumThree
    (w : ℕ → ℂ) (U V : ℝ) (y : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y,
    ((-∑ tr ∈ n.divisorsAntidiagonal,
        ∑ md ∈ tr.1.divisorsAntidiagonal.filter
          (fun md : ℕ × ℕ ↦
            (md.1 : ℝ) ≤ U ∧ (md.2 : ℝ) ≤ V),
          ArithmeticFunction.vonMangoldt md.1 *
            (ArithmeticFunction.moebius : ArithmeticFunction ℝ) md.2 : ℝ) : ℂ) * w n

/-- The fourth term of the arbitrarily weighted Vaughan decomposition. -/
def weightedVaughanSumFour
    (w : ℕ → ℂ) (U V : ℝ) (y : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y,
    ((-∑ mk ∈ n.divisorsAntidiagonal.filter
        (fun mk : ℕ × ℕ ↦ U < (mk.1 : ℝ) ∧ V < (mk.2 : ℝ)),
        ArithmeticFunction.vonMangoldt mk.1 *
          ∑ d ∈ mk.2.divisors.filter (fun d : ℕ ↦ (d : ℝ) ≤ V),
            (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d : ℝ) : ℂ) * w n

/-- Vaughan's identity remains valid after multiplication by any complex
weight and summation over a finite initial interval. -/
theorem weightedChebyshevSum_eq_vaughan
    {w : ℕ → ℂ} {U V : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V) (y : ℕ) :
    weightedChebyshevSum w y =
      weightedVaughanSumOne w U y +
      weightedVaughanSumTwo w V y +
      weightedVaughanSumThree w U V y +
      weightedVaughanSumFour w U V y := by
  unfold weightedChebyshevSum weightedVaughanSumOne weightedVaughanSumTwo
    weightedVaughanSumThree weightedVaughanSumFour
  rw [Finset.sum_filter]
  simp_rw [← vaughanLambdaTwo_apply,
    ← vaughanLambdaThree_apply hU hV,
    ← vaughanLambdaFour_apply hU hV]
  have hS1 :
      (∑ n ∈ Finset.Icc 1 y,
        if (n : ℝ) ≤ U then
          (ArithmeticFunction.vonMangoldt n : ℂ) * w n
        else 0) =
      ∑ n ∈ Finset.Icc 1 y,
        (arithmeticFunctionLowCutoff U
          ArithmeticFunction.vonMangoldt n : ℂ) * w n := by
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases hnU : (n : ℝ) ≤ U
    · rw [if_pos hnU, arithmeticFunctionLowCutoff_apply_of_le hnU]
    · rw [if_neg hnU,
        arithmeticFunctionLowCutoff_apply_of_lt (lt_of_not_ge hnU)]
      simp
  rw [hS1, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [← add_mul, ← add_mul, ← add_mul]
  congr 1
  rw [← Complex.ofReal_add, ← Complex.ofReal_add,
    ← Complex.ofReal_add]
  simpa only [sub_eq_add_neg, ArithmeticFunction.add_apply,
    ArithmeticFunction.neg_apply] using
    (congrArg (fun f : ArithmeticFunction ℝ ↦ (f n : ℂ))
      (vaughanConvolutionIdentity U V)).symm

/-- Positive factor pairs, in a form suited to nested sums. -/
lemma mem_positiveFactorPairs_iff {y : ℕ} (p : ℕ × ℕ) :
    p ∈ positiveFactorPairs y ↔
      p.1 ∈ Finset.Icc 1 y ∧ p.2 ∈ Finset.Icc 1 (y / p.1) := by
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hprod⟩
    rcases Finset.mem_product.mp hp with ⟨hp₁, hp₂⟩
    rw [Finset.mem_Ioc] at hp₁ hp₂
    exact ⟨Finset.mem_Icc.mpr ⟨hp₁.1, hp₁.2⟩,
      Finset.mem_Icc.mpr ⟨hp₂.1,
        (Nat.le_div_iff_mul_le hp₁.1).mpr (by
          simpa only [Nat.mul_comm] using hprod)⟩⟩
  · rintro ⟨hm, hk⟩
    rw [Finset.mem_Icc] at hm hk
    have hprod : p.1 * p.2 ≤ y := by
      simpa only [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le hm.1).mp hk.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Ioc.mpr hm,
          Finset.mem_Ioc.mpr
            ⟨hk.1, hk.2.trans (Nat.div_le_self y p.1)⟩⟩,
        hprod⟩

/-- The complete third term, regrouped by the bounded coefficient index
`t = m*d`. -/
theorem neg_weightedVaughanSumThree_eq_nested
    (w : ℕ → ℂ) (U V : ℝ) (y : ℕ) :
    -weightedVaughanSumThree w U V y =
      ∑ t ∈ Finset.Icc 1 y,
        ((vaughanThirdCoefficient U V t : ℝ) : ℂ) *
          ∑ r ∈ Finset.Icc 1 (y / t), w (t * r) := by
  unfold weightedVaughanSumThree
  change -(∑ n ∈ Finset.Icc 1 y,
      ((-∑ tr ∈ n.divisorsAntidiagonal,
        vaughanThirdCoefficient U V tr.1 : ℝ) : ℂ) * w n) = _
  rw [← Finset.sum_neg_distrib]
  calc
    (∑ n ∈ Finset.Icc 1 y,
        -(((-∑ tr ∈ n.divisorsAntidiagonal,
          vaughanThirdCoefficient U V tr.1 : ℝ) : ℂ) * w n)) =
        ∑ n ∈ Finset.Icc 1 y,
          ∑ tr ∈ n.divisorsAntidiagonal,
            ((vaughanThirdCoefficient U V tr.1 : ℝ) : ℂ) * w n := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [Complex.ofReal_neg, Complex.ofReal_sum]
      simp only [neg_mul, neg_neg]
      rw [Finset.sum_mul]
    _ = ∑ n ∈ Finset.Ioc 0 y,
        ∑ tr ∈ n.divisorsAntidiagonal,
          ((vaughanThirdCoefficient U V tr.1 : ℝ) : ℂ) *
            w (tr.1 * tr.2) := by
      rw [show Finset.Icc 1 y = Finset.Ioc 0 y by
        simpa using Finset.Icc_succ_left_eq_Ioc 0 y]
      apply Finset.sum_congr rfl
      intro n _hn
      apply Finset.sum_congr rfl
      intro tr htr
      rw [(Nat.mem_divisorsAntidiagonal.mp htr).1]
    _ = ∑ tr ∈ positiveFactorPairs y,
        ((vaughanThirdCoefficient U V tr.1 : ℝ) : ℂ) *
          w (tr.1 * tr.2) :=
      sum_divisorsAntidiagonal_up_to_eq_sum_positiveFactorPairs
        (fun t r ↦ ((vaughanThirdCoefficient U V t : ℝ) : ℂ) * w (t * r))
    _ = ∑ t ∈ Finset.Icc 1 y,
        ∑ r ∈ Finset.Icc 1 (y / t),
          ((vaughanThirdCoefficient U V t : ℝ) : ℂ) * w (t * r) := by
      exact Finset.sum_finset_product
        (positiveFactorPairs y) (Finset.Icc 1 y)
        (fun t ↦ Finset.Icc 1 (y / t)) mem_positiveFactorPairs_iff
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [Finset.mul_sum]

/-- The fourth term as a finite bilinear sum over positive factor pairs. -/
theorem weightedVaughanSumFour_eq_pairs
    (w : ℕ → ℂ) (U V : ℝ) (y : ℕ) :
    weightedVaughanSumFour w U V y =
      -∑ mk ∈ (positiveFactorPairs y).filter
          (fun mk : ℕ × ℕ ↦ U < (mk.1 : ℝ) ∧ V < (mk.2 : ℝ)),
        ((ArithmeticFunction.vonMangoldt mk.1 : ℝ) : ℂ) *
          ((vaughanFourthCoefficient V mk.2 : ℝ) : ℂ) * w (mk.1 * mk.2) := by
  let f : ℕ → ℕ → ℂ := fun m k ↦
    if U < (m : ℝ) ∧ V < (k : ℝ) then
      ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
        ((vaughanFourthCoefficient V k : ℝ) : ℂ) * w (m * k)
    else 0
  unfold weightedVaughanSumFour
  calc
    (∑ n ∈ Finset.Icc 1 y,
        ((-∑ mk ∈ n.divisorsAntidiagonal.filter
            (fun mk : ℕ × ℕ ↦ U < (mk.1 : ℝ) ∧ V < (mk.2 : ℝ)),
          ArithmeticFunction.vonMangoldt mk.1 *
            ∑ d ∈ mk.2.divisors.filter (fun d : ℕ ↦ (d : ℝ) ≤ V),
              (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d : ℝ) : ℂ) * w n) =
        -(∑ n ∈ Finset.Ioc 0 y,
          ∑ mk ∈ n.divisorsAntidiagonal, f mk.1 mk.2) := by
      rw [show Finset.Icc 1 y = Finset.Ioc 0 y by
        simpa using Finset.Icc_succ_left_eq_Ioc 0 y]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro n _hn
      rw [Complex.ofReal_neg, Complex.ofReal_sum, neg_mul, neg_inj,
        Finset.sum_filter, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro mk hmk
      have hprod := (Nat.mem_divisorsAntidiagonal.mp hmk).1
      by_cases hcut : U < (mk.1 : ℝ) ∧ V < (mk.2 : ℝ)
      · simp only [if_pos hcut, f]
        rw [← hprod, Complex.ofReal_mul,
          show (∑ d ∈ mk.2.divisors.filter (fun d : ℕ ↦ (d : ℝ) ≤ V),
              (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d) =
              vaughanFourthCoefficient V mk.2 by rfl]
      · simp only [f, if_neg hcut]
        simp
    _ = -(∑ mk ∈ positiveFactorPairs y, f mk.1 mk.2) := by
      rw [sum_divisorsAntidiagonal_up_to_eq_sum_positiveFactorPairs f]
    _ = _ := by
      rw [Finset.sum_filter]

/-- The reciprocal phase used to twist primes and prime powers. -/
def reciprocalWeight (X : ℝ) (n : ℕ) : ℂ :=
  e (-X / (n : ℝ))

@[simp] theorem norm_reciprocalWeight (X : ℝ) (n : ℕ) :
    ‖reciprocalWeight X n‖ = 1 := by
  simp [reciprocalWeight, norm_e]

/-- Correlating two reciprocal product phases leaves an ordinary reciprocal
phase in the common factor.  The frequency is positive when `k₁ < k₂`,
which is precisely the orientation used after the bilinear square is
expanded. -/
theorem reciprocalWeight_mul_conj_product
    (X : ℝ) {m k₁ k₂ : ℕ} (hm : 0 < m) (hk₁ : 0 < k₁) (hk₁k₂ : k₁ ≤ k₂) :
    reciprocalWeight X (m * k₁) * conj (reciprocalWeight X (m * k₂)) =
      reciprocalWeight
        (X * ((k₂ - k₁ : ℕ) : ℝ) / ((k₁ * k₂ : ℕ) : ℝ)) m := by
  rw [reciprocalWeight, reciprocalWeight, reciprocalWeight, ← e_sub]
  congr 1
  have hk₂ : 0 < k₂ := hk₁.trans_le hk₁k₂
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have hk₁R : (k₁ : ℝ) ≠ 0 := by positivity
  have hk₂R : (k₂ : ℝ) ≠ 0 := by positivity
  push_cast [hk₁k₂]
  field_simp
  ring

/-! ## Interval form

The reciprocal estimates are effective on dyadic intervals, rather than on
prefixes beginning at one.  We therefore record the same decomposition on
`(x,y]` and reindex all convolution factors while retaining the lower
product bound.
-/

/-- A weighted von Mangoldt sum on the natural interval `(x,y]`. -/
def weightedChebyshevInterval (w : ℕ → ℂ) (x y : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc x y, (ArithmeticFunction.vonMangoldt n : ℂ) * w n

def weightedVaughanIntervalOne
    (w : ℕ → ℂ) (U : ℝ) (x y : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc x y,
    (arithmeticFunctionLowCutoff U ArithmeticFunction.vonMangoldt n : ℂ) * w n

def weightedVaughanIntervalTwo
    (w : ℕ → ℂ) (V : ℝ) (x y : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc x y,
    ((arithmeticFunctionLowCutoff V
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
        ArithmeticFunction.log) n : ℂ) * w n

def weightedVaughanIntervalThree
    (w : ℕ → ℂ) (U V : ℝ) (x y : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc x y,
    ((-(arithmeticFunctionLowCutoff U ArithmeticFunction.vonMangoldt *
      arithmeticFunctionLowCutoff V
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ))) n : ℂ) * w n

def weightedVaughanIntervalFour
    (w : ℕ → ℂ) (U V : ℝ) (x y : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc x y,
    ((arithmeticFunctionHighCutoff U ArithmeticFunction.vonMangoldt -
      arithmeticFunctionHighCutoff U ArithmeticFunction.vonMangoldt *
        arithmeticFunctionLowCutoff V
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n : ℂ) * w n

theorem weightedChebyshevInterval_eq_vaughan
    {w : ℕ → ℂ} {U V : ℝ} (x y : ℕ) :
    weightedChebyshevInterval w x y =
      weightedVaughanIntervalOne w U x y +
      weightedVaughanIntervalTwo w V x y +
      weightedVaughanIntervalThree w U V x y +
      weightedVaughanIntervalFour w U V x y := by
  unfold weightedChebyshevInterval weightedVaughanIntervalOne
    weightedVaughanIntervalTwo weightedVaughanIntervalThree
    weightedVaughanIntervalFour
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [← add_mul, ← add_mul, ← add_mul]
  congr 1
  rw [← Complex.ofReal_add, ← Complex.ofReal_add,
    ← Complex.ofReal_add]
  simpa only [sub_eq_add_neg, ArithmeticFunction.add_apply,
    ArithmeticFunction.neg_apply] using
    (congrArg (fun f : ArithmeticFunction ℝ ↦ (f n : ℂ))
      (vaughanConvolutionIdentity U V)).symm

/-- Positive factor pairs whose product lies in `(x,y]`. -/
def intervalFactorPairs (x y : ℕ) : Finset (ℕ × ℕ) :=
  (positiveFactorPairs y).filter (fun p ↦ x < p.1 * p.2)

/-- Reindex divisor antidiagonals throughout a natural interval. -/
theorem sum_divisorsAntidiagonal_interval_eq_sum_factorPairs
    {x y : ℕ} {M : Type*} [AddCommMonoid M] (f : ℕ → ℕ → M) :
    (∑ n ∈ Finset.Ioc x y,
      ∑ p ∈ n.divisorsAntidiagonal, f p.1 p.2) =
      ∑ p ∈ intervalFactorPairs x y, f p.1 p.2 := by
  let T : Finset ℕ := Finset.Ioc x y
  let g : ℕ × ℕ → ℕ := fun p ↦ p.1 * p.2
  have hmaps : ∀ p ∈ intervalFactorPairs x y, g p ∈ T := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hxprod⟩
    rcases Finset.mem_filter.mp hp with ⟨hp, hyprod⟩
    exact Finset.mem_Ioc.mpr ⟨hxprod, hyprod⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := intervalFactorPairs x y) (t := T) hmaps
    (fun p ↦ f p.1 p.2)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro n hn
  change n ∈ Finset.Ioc x y at hn
  have hnBounds := Finset.mem_Ioc.mp hn
  have hnPos : n ≠ 0 :=
    (lt_of_le_of_lt (Nat.zero_le x) hnBounds.1).ne'
  rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le (N := y)]
  · apply Finset.sum_congr
    · ext p
      simp only [intervalFactorPairs, positiveFactorPairs, g, Finset.mem_filter]
      constructor
      · rintro ⟨hp, hprod⟩
        refine ⟨⟨⟨hp, ?_⟩, ?_⟩, hprod⟩
        · simpa only [hprod] using (Finset.mem_Ioc.mp hn).2
        · simpa only [hprod] using (Finset.mem_Ioc.mp hn).1
      · rintro ⟨⟨⟨hp, _hy⟩, _hx⟩, hprod⟩
        exact ⟨hp, hprod⟩
    · intro p _hp
      rfl
  · exact hnPos
  · exact (Finset.mem_Ioc.mp hn).2

lemma mem_intervalFactorPairs_iff (x y : ℕ) (p : ℕ × ℕ) :
    p ∈ intervalFactorPairs x y ↔
      p.1 ∈ Finset.Icc 1 y ∧
        p.2 ∈ Finset.Ioc (x / p.1) (y / p.1) := by
  rw [intervalFactorPairs, Finset.mem_filter, mem_positiveFactorPairs_iff]
  constructor
  · rintro ⟨⟨hp₁, hp₂⟩, hx⟩
    have hp₁Pos := (Finset.mem_Icc.mp hp₁).1
    have hp₂Bounds := Finset.mem_Icc.mp hp₂
    refine ⟨hp₁, Finset.mem_Ioc.mpr ⟨?_, hp₂Bounds.2⟩⟩
    exact (Nat.div_lt_iff_lt_mul hp₁Pos).mpr (by simpa [Nat.mul_comm] using hx)
  · rintro ⟨hp₁, hp₂⟩
    have hp₁Pos := (Finset.mem_Icc.mp hp₁).1
    have hp₂Bounds := Finset.mem_Ioc.mp hp₂
    refine ⟨⟨hp₁, Finset.mem_Icc.mpr ⟨?_, hp₂Bounds.2⟩⟩, ?_⟩
    · exact Nat.zero_lt_of_lt hp₂Bounds.1
    · exact (Nat.div_lt_iff_lt_mul hp₁Pos).mp hp₂Bounds.1 |>.trans_eq
        (Nat.mul_comm p.2 p.1)

lemma mem_intervalFactorPairs_iff_right (x y : ℕ) (p : ℕ × ℕ) :
    p ∈ intervalFactorPairs x y ↔
      p.2 ∈ Finset.Icc 1 y ∧
        p.1 ∈ Finset.Ioc (x / p.2) (y / p.2) := by
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpPairs, hxprod⟩
    rcases Finset.mem_filter.mp hpPairs with ⟨hpProduct, hyprod⟩
    rcases Finset.mem_product.mp hpProduct with ⟨hp₁, hp₂⟩
    have hp₂Bounds := Finset.mem_Ioc.mp hp₂
    refine ⟨Finset.mem_Icc.mpr hp₂Bounds, Finset.mem_Ioc.mpr ⟨?_, ?_⟩⟩
    · exact (Nat.div_lt_iff_lt_mul hp₂Bounds.1).mpr hxprod
    · exact (Nat.le_div_iff_mul_le hp₂Bounds.1).mpr hyprod
  · rintro ⟨hp₂, hp₁⟩
    have hp₂Bounds := Finset.mem_Icc.mp hp₂
    have hp₁Bounds := Finset.mem_Ioc.mp hp₁
    have hp₁Pos : 0 < p.1 := Nat.zero_lt_of_lt hp₁Bounds.1
    have hyprod : p.1 * p.2 ≤ y :=
      (Nat.le_div_iff_mul_le hp₂Bounds.1).mp hp₁Bounds.2
    have hp₁y : p.1 ≤ y := hp₁Bounds.2.trans (Nat.div_le_self y p.2)
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, hyprod⟩, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hp₁Pos, hp₁y⟩,
          Finset.mem_Ioc.mpr hp₂Bounds⟩
    · exact (Nat.div_lt_iff_lt_mul hp₂Bounds.1).mp hp₁Bounds.1

/-- The second interval term after exposing the small Möbius factor. -/
theorem weightedVaughanIntervalTwo_eq_nested
    (w : ℕ → ℂ) (V : ℝ) (x y : ℕ) :
    weightedVaughanIntervalTwo w V x y =
      ∑ d ∈ (Finset.Icc 1 y).filter (fun d : ℕ ↦ (d : ℝ) ≤ V),
        ((ArithmeticFunction.moebius d : ℝ) : ℂ) *
          ∑ h ∈ Finset.Ioc (x / d) (y / d),
            (Real.log h : ℂ) * w (d * h) := by
  unfold weightedVaughanIntervalTwo
  simp_rw [vaughanLambdaTwo_apply, Complex.ofReal_sum,
    Complex.ofReal_mul, Finset.sum_mul]
  calc
    (∑ n ∈ Finset.Ioc x y,
        ∑ hd ∈ n.divisorsAntidiagonal.filter
            (fun hd : ℕ × ℕ ↦ (hd.2 : ℝ) ≤ V),
          (((ArithmeticFunction.moebius hd.2 : ℝ) : ℂ) *
            (Real.log hd.1 : ℂ)) * w n) =
      ∑ n ∈ Finset.Ioc x y,
        ∑ hd ∈ n.divisorsAntidiagonal,
          if (hd.2 : ℝ) ≤ V then
            (((ArithmeticFunction.moebius hd.2 : ℝ) : ℂ) *
              (Real.log hd.1 : ℂ)) * w (hd.1 * hd.2)
          else 0 := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [Finset.sum_filter]

      apply Finset.sum_congr rfl
      intro hd hhd
      rw [← (Nat.mem_divisorsAntidiagonal.mp hhd).1]
    _ = ∑ hd ∈ intervalFactorPairs x y,
        if (hd.2 : ℝ) ≤ V then
          (((ArithmeticFunction.moebius hd.2 : ℝ) : ℂ) *
            (Real.log hd.1 : ℂ)) * w (hd.1 * hd.2)
        else 0 :=
      sum_divisorsAntidiagonal_interval_eq_sum_factorPairs
        (fun h d ↦ if (d : ℝ) ≤ V then
          (((ArithmeticFunction.moebius d : ℝ) : ℂ) *
            (Real.log h : ℂ)) * w (h * d)
          else 0)
    _ = ∑ d ∈ (Finset.Icc 1 y).filter (fun d : ℕ ↦ (d : ℝ) ≤ V),
        ∑ h ∈ Finset.Ioc (x / d) (y / d),
          ((ArithmeticFunction.moebius d : ℝ) : ℂ) *
            ((Real.log h : ℂ) * w (d * h)) := by
      rw [← Finset.sum_filter]
      simpa only [Nat.mul_comm, mul_assoc] using
        Finset.sum_finset_product_right'
        ((intervalFactorPairs x y).filter
          (fun p : ℕ × ℕ ↦ (p.2 : ℝ) ≤ V))
        ((Finset.Icc 1 y).filter (fun d : ℕ ↦ (d : ℝ) ≤ V))
        (fun d ↦ Finset.Ioc (x / d) (y / d))
        (by
          intro p
          rw [Finset.mem_filter, mem_intervalFactorPairs_iff_right]
          simp only [Finset.mem_filter]
          tauto)
        (f := fun h d ↦
          ((ArithmeticFunction.moebius d : ℝ) : ℂ) *
            ((Real.log h : ℂ) * w (d * h)))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.mul_sum]

/-- The third interval term after grouping the two cutoff factors. -/
theorem neg_weightedVaughanIntervalThree_eq_nested
    (w : ℕ → ℂ) {U V : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V) (x y : ℕ) :
    -weightedVaughanIntervalThree w U V x y =
      ∑ t ∈ Finset.Icc 1 y,
        ((vaughanThirdCoefficient U V t : ℝ) : ℂ) *
          ∑ r ∈ Finset.Ioc (x / t) (y / t), w (t * r) := by
  unfold weightedVaughanIntervalThree
  simp_rw [vaughanLambdaThree_apply (U := U) (V := V)
    hU hV]
  change -(∑ n ∈ Finset.Ioc x y,
      ((-∑ tr ∈ n.divisorsAntidiagonal,
        vaughanThirdCoefficient U V tr.1 : ℝ) : ℂ) * w n) = _
  rw [← Finset.sum_neg_distrib]
  calc
    (∑ n ∈ Finset.Ioc x y,
        -(((-∑ tr ∈ n.divisorsAntidiagonal,
          vaughanThirdCoefficient U V tr.1 : ℝ) : ℂ) * w n)) =
      ∑ n ∈ Finset.Ioc x y,
        ∑ tr ∈ n.divisorsAntidiagonal,
          ((vaughanThirdCoefficient U V tr.1 : ℝ) : ℂ) *
            w (tr.1 * tr.2) := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [Complex.ofReal_neg, Complex.ofReal_sum]
      simp only [neg_mul, neg_neg]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro tr htr
      rw [← (Nat.mem_divisorsAntidiagonal.mp htr).1]
    _ = ∑ tr ∈ intervalFactorPairs x y,
        ((vaughanThirdCoefficient U V tr.1 : ℝ) : ℂ) *
          w (tr.1 * tr.2) :=
      sum_divisorsAntidiagonal_interval_eq_sum_factorPairs
        (fun t r ↦ ((vaughanThirdCoefficient U V t : ℝ) : ℂ) * w (t * r))
    _ = ∑ t ∈ Finset.Icc 1 y,
        ∑ r ∈ Finset.Ioc (x / t) (y / t),
          ((vaughanThirdCoefficient U V t : ℝ) : ℂ) * w (t * r) := by
      exact Finset.sum_finset_product
        (intervalFactorPairs x y) (Finset.Icc 1 y)
        (fun t ↦ Finset.Ioc (x / t) (y / t))
        (mem_intervalFactorPairs_iff x y)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [Finset.mul_sum]

/-- The fourth interval term as the exact bilinear sum carrying the
Granville--Ramaré coefficient. -/
theorem weightedVaughanIntervalFour_eq_pairs
    (w : ℕ → ℂ) {U V : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V) (x y : ℕ) :
    weightedVaughanIntervalFour w U V x y =
      -∑ mk ∈ (intervalFactorPairs x y).filter
          (fun mk : ℕ × ℕ ↦ U < (mk.1 : ℝ) ∧ V < (mk.2 : ℝ)),
        ((ArithmeticFunction.vonMangoldt mk.1 : ℝ) : ℂ) *
          ((vaughanFourthCoefficient V mk.2 : ℝ) : ℂ) *
            w (mk.1 * mk.2) := by
  unfold weightedVaughanIntervalFour
  simp_rw [vaughanLambdaFour_apply (U := U) (V := V) hU hV]
  change (∑ n ∈ Finset.Ioc x y,
      ((-∑ mk ∈ n.divisorsAntidiagonal.filter
          (fun mk : ℕ × ℕ ↦ U < (mk.1 : ℝ) ∧ V < (mk.2 : ℝ)),
        ArithmeticFunction.vonMangoldt mk.1 *
          vaughanFourthCoefficient V mk.2 : ℝ) : ℂ) * w n) = _
  calc
    (∑ n ∈ Finset.Ioc x y,
        ((-∑ mk ∈ n.divisorsAntidiagonal.filter
            (fun mk : ℕ × ℕ ↦ U < (mk.1 : ℝ) ∧ V < (mk.2 : ℝ)),
          ArithmeticFunction.vonMangoldt mk.1 *
            vaughanFourthCoefficient V mk.2 : ℝ) : ℂ) * w n) =
      -(∑ n ∈ Finset.Ioc x y,
        ∑ mk ∈ n.divisorsAntidiagonal,
          if U < (mk.1 : ℝ) ∧ V < (mk.2 : ℝ) then
            ((ArithmeticFunction.vonMangoldt mk.1 : ℝ) : ℂ) *
              ((vaughanFourthCoefficient V mk.2 : ℝ) : ℂ) *
                w (mk.1 * mk.2)
          else 0) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro n _hn
      rw [Complex.ofReal_neg, Complex.ofReal_sum, neg_mul, neg_inj,
        Finset.sum_filter, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro mk hmk
      by_cases hcut : U < (mk.1 : ℝ) ∧ V < (mk.2 : ℝ)
      · rw [if_pos hcut, if_pos hcut,
          ← (Nat.mem_divisorsAntidiagonal.mp hmk).1]
        push_cast
        ring
      · simp [hcut]
    _ = -(∑ mk ∈ intervalFactorPairs x y,
        if U < (mk.1 : ℝ) ∧ V < (mk.2 : ℝ) then
          ((ArithmeticFunction.vonMangoldt mk.1 : ℝ) : ℂ) *
            ((vaughanFourthCoefficient V mk.2 : ℝ) : ℂ) *
              w (mk.1 * mk.2)
        else 0) := by
      apply congrArg Neg.neg
      exact sum_divisorsAntidiagonal_interval_eq_sum_factorPairs
        (fun m k ↦
          if U < (m : ℝ) ∧ V < (k : ℝ) then
            ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
              ((vaughanFourthCoefficient V k : ℝ) : ℂ) * w (m * k)
          else 0)
    _ = _ := by
      rw [Finset.sum_filter]

/-- The fourth interval term grouped by its von Mangoldt factor. -/
theorem weightedVaughanIntervalFour_eq_nested
    (w : ℕ → ℂ) {U V : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V) (x y : ℕ) :
    weightedVaughanIntervalFour w U V x y =
      -∑ m ∈ (Finset.Icc 1 y).filter (fun m : ℕ ↦ U < (m : ℝ)),
        ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
          ∑ k ∈ (Finset.Ioc (x / m) (y / m)).filter
              (fun k : ℕ ↦ V < (k : ℝ)),
            ((vaughanFourthCoefficient V k : ℝ) : ℂ) * w (m * k) := by
  rw [weightedVaughanIntervalFour_eq_pairs w hU hV x y]
  apply congrArg Neg.neg
  let f : ℕ → ℕ → ℂ := fun m k ↦
    ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
      ((vaughanFourthCoefficient V k : ℝ) : ℂ) * w (m * k)
  change (∑ mk ∈ (intervalFactorPairs x y).filter
    (fun mk : ℕ × ℕ ↦ U < (mk.1 : ℝ) ∧ V < (mk.2 : ℝ)),
      f mk.1 mk.2) = _
  rw [Finset.sum_filter]
  calc
    (∑ mk ∈ intervalFactorPairs x y,
        if U < (mk.1 : ℝ) ∧ V < (mk.2 : ℝ) then f mk.1 mk.2 else 0) =
      ∑ m ∈ Finset.Icc 1 y,
        ∑ k ∈ Finset.Ioc (x / m) (y / m),
          if U < (m : ℝ) ∧ V < (k : ℝ) then f m k else 0 := by
      exact Finset.sum_finset_product
        (intervalFactorPairs x y) (Finset.Icc 1 y)
        (fun m ↦ Finset.Ioc (x / m) (y / m))
        (mem_intervalFactorPairs_iff x y)
    _ = ∑ m ∈ (Finset.Icc 1 y).filter (fun m : ℕ ↦ U < (m : ℝ)),
        ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
          ∑ k ∈ (Finset.Ioc (x / m) (y / m)).filter
              (fun k : ℕ ↦ V < (k : ℝ)),
            ((vaughanFourthCoefficient V k : ℝ) : ℂ) * w (m * k) := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hmU : U < (m : ℝ)
      · simp only [hmU, true_and, if_true, f]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hkV : V < (k : ℝ)
        · simp [hkV, mul_assoc]
        · simp [hkV]
      · simp only [hmU, false_and, if_false, Finset.sum_const_zero]

/-! ## Reciprocal sums on product intervals -/

theorem sum_Ioc_eq_sum_range {R : Type*} [AddCommMonoid R]
    (F : ℕ → R) (a b : ℕ) :
    (∑ n ∈ Finset.Ioc a b, F n) =
      ∑ i ∈ Finset.range (b - a), F (a + 1 + i) := by
  by_cases hab : a ≤ b
  · have hset : Finset.Ioc a b =
        (Finset.range (b - a)).image (fun i : ℕ ↦ a + 1 + i) := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_image, Finset.mem_range]
      constructor
      · intro hn
        refine ⟨n - (a + 1), ?_, ?_⟩
        · omega
        · omega
      · rintro ⟨i, hi, rfl⟩
        omega
    rw [hset, Finset.sum_image]
    intro i _hi j _hj hij
    exact Nat.add_left_cancel hij
  · have hba : b ≤ a := le_of_not_ge hab
    have hnlt : ¬a < b := Nat.not_lt_of_ge hba
    have hsub : b - a = 0 := Nat.sub_eq_zero_of_le hba
    simp [Finset.Ioc_eq_empty hnlt, hsub]

/-- The reciprocal phase on products `t*r`, with `r` in `(a,b]`. -/
def reciprocalProductIntervalSum (X : ℝ) (t a b : ℕ) : ℂ :=
  ∑ r ∈ Finset.Ioc a b, reciprocalWeight X (t * r)

/-- Correlation identity on an arbitrary consecutive interval. -/
theorem sum_reciprocalWeight_product_correlation
    (X : ℝ) {a b k₁ k₂ : ℕ} (hk₁ : 0 < k₁) (hk₁k₂ : k₁ ≤ k₂) :
    (∑ m ∈ Finset.Ioc a b,
        reciprocalWeight X (m * k₁) * conj (reciprocalWeight X (m * k₂))) =
      reciprocalProductIntervalSum
        (X * ((k₂ - k₁ : ℕ) : ℝ) / ((k₁ * k₂ : ℕ) : ℝ)) 1 a b := by
  unfold reciprocalProductIntervalSum
  simp only [one_mul]
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < m := Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hm).1
  exact reciprocalWeight_mul_conj_product X hmpos hk₁ hk₁k₂

theorem reciprocalProductIntervalSum_eq_phase
    (X : ℝ) {t a b : ℕ} (ht : 0 < t) :
    reciprocalProductIntervalSum X t a b =
      ∑ i ∈ Finset.range (b - a),
        e (reciprocalPhase (X / (t : ℝ)) (a + 1) i) := by
  rw [reciprocalProductIntervalSum, sum_Ioc_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [reciprocalWeight, reciprocalPhase]
  have htR : (t : ℝ) ≠ 0 := by positivity
  have har : (((a + 1 + i : ℕ) : ℝ)) ≠ 0 := by positivity
  congr 1
  push_cast
  field_simp

/-- The finite second-derivative estimate, transported to a product
interval. -/
theorem reciprocalProductInterval_second_derivative_bound
    (X : ℝ) (hX : 0 < X) {t a b L : ℕ} (ht : 0 < t)
    (hN : 3 ≤ b - a) (hL : 2 ≤ L) (hLN : L ≤ b - a - 1)
    (hsmall :
      2 * (X / (t : ℝ)) * L / ((a + 1 : ℕ) : ℝ) ^ 3 ≤ 1 / 2) :
    (L : ℝ) ^ 2 * ‖reciprocalProductIntervalSum X t a b‖ ^ 2 ≤
      2 * (L : ℝ) * ((b - a : ℕ) : ℝ) ^ 2 +
        4 * ((b - a : ℕ) : ℝ) * (L : ℝ) *
          ((L : ℝ) +
            (3 * ((((a + 1) + (b - a) : ℕ) : ℝ) ^ 3) /
              (4 * (X / (t : ℝ)))) *
                (harmonic (L - 1) : ℝ)) := by
  rw [reciprocalProductIntervalSum_eq_phase X ht]
  exact reciprocal_second_derivative_bound
    (X / (t : ℝ)) (div_pos hX (by positivity))
    (show 0 < a + 1 by omega) hN hL hLN hsmall

/-- The two-stage van der Corput estimate transported to a product
interval.  This is the form used for the long-variable sums in the balanced
part of Vaughan's identity. -/
theorem reciprocalProductInterval_third_derivative_bound
    (X : ℝ) (hX : 0 < X) {t a b L₁ L₂ : ℕ} (ht : 0 < t)
    (hN : 4 ≤ b - a) (hL₁ : 2 ≤ L₁) (hL₂ : 2 ≤ L₂)
    (hshifts : L₁ + L₂ ≤ b - a)
    (hsmall :
      6 * (X / (t : ℝ)) * L₁ * L₂ / ((a + 1 : ℕ) : ℝ) ^ 4 ≤ 1 / 2) :
    (L₁ : ℝ) ^ 4 * (L₂ : ℝ) ^ 2 *
        ‖reciprocalProductIntervalSum X t a b‖ ^ 4 ≤
      2 * (L₂ : ℝ) ^ 2 *
          (2 * (L₁ : ℝ) * ((b - a : ℕ) : ℝ) ^ 2) ^ 2 +
        2 * (4 * ((b - a : ℕ) : ℝ) * (L₁ : ℝ)) ^ 2 *
          ((Finset.Icc 1 (L₁ - 1)).card : ℝ) *
            ∑ ℓ₁ ∈ Finset.Icc 1 (L₁ - 1),
              reciprocalThirdStageMajorant (X / (t : ℝ)) (a + 1)
                (b - a) L₂ ℓ₁ := by
  rw [reciprocalProductIntervalSum_eq_phase X ht]
  exact reciprocal_third_derivative_bound
    (X / (t : ℝ)) (div_pos hX (by positivity))
    (show 0 < a + 1 by omega) hN hL₁ hL₂ hshifts hsmall

/-- Explicit harmonic form of the two-stage product-interval estimate. -/
theorem reciprocalProductInterval_third_derivative_bound_explicit
    (X : ℝ) (hX : 0 < X) {t a b L₁ L₂ : ℕ} (ht : 0 < t)
    (hN : 4 ≤ b - a) (hL₁ : 2 ≤ L₁) (hL₂ : 2 ≤ L₂)
    (hshifts : L₁ + L₂ ≤ b - a)
    (hsmall :
      6 * (X / (t : ℝ)) * L₁ * L₂ / ((a + 1 : ℕ) : ℝ) ^ 4 ≤ 1 / 2) :
    (L₁ : ℝ) ^ 4 * (L₂ : ℝ) ^ 2 *
        ‖reciprocalProductIntervalSum X t a b‖ ^ 4 ≤
      reciprocalThirdDerivativeMajorant (X / (t : ℝ)) (a + 1)
        (b - a) L₁ L₂ := by
  rw [reciprocalProductIntervalSum_eq_phase X ht]
  exact reciprocal_third_derivative_bound_explicit
    (X / (t : ℝ)) (div_pos hX (by positivity))
    (show 0 < a + 1 by omega) hN hL₁ hL₂ hshifts hsmall


end

end PrimeReciprocal
end Erdos378
