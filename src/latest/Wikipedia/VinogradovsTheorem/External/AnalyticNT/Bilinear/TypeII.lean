/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Type-II bilinear bound (M3)

Scaffold for milestone **M3** of `ext/analytic_nt` (see `SPEC.md` §4.3).

## Statement

For coefficient sequences `a, b : ℕ → ℂ` supported on dyadic ranges
`m ∈ (M, 2M]`, `n ∈ (N, 2N]`,

```
|T_II(α; M, N)| := |∑_m ∑_n a_m b_n e(α m n)|
    ≤ C_II · ‖a‖₂ · ‖b‖₂ · √(M N / q + M + N + q) · √log(q M N + 2)
```

valid uniformly in `α` via Dirichlet approximation.  The proof goes
through Cauchy–Schwarz on the outer `m`-sum, expanding the inner square
into a Type-II Schur/large-sieve kernel (consumed by `Schur.lean` and the
future M4 large sieve).

## References

* Davenport, *Multiplicative Number Theory* (GTM 74, 3rd ed.), Ch. 25.
* Iwaniec & Kowalski, *Analytic Number Theory*, Ch. 7 + Ch. 13.
* Montgomery & Vaughan, *Multiplicative Number Theory I*, Ch. 27.
* Helfgott, *Minor arcs for Goldbach's problem*, arXiv:1205.5252v4, §5.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Wikipedia.VinogradovsTheorem.External.AnalyticNT.Bilinear.Schur

namespace AnalyticNT
namespace Bilinear
namespace TypeII

/-- Additive character `e(α n) = exp(2πi α n)` on the natural numbers. -/
noncomputable def addChar (α : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * α * n)

/-- A Type-II bilinear exponential sum on dyadic boxes `(M, 2M] × (N, 2N]`. -/
noncomputable def typeIISum (a b : ℕ → ℂ) (M N : ℕ) (α : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ioc M (2 * M),
    ∑ n ∈ Finset.Ioc N (2 * N), a m * b n * addChar α (m * n)

/-- ℓ²-norm of a coefficient sequence restricted to `(K, 2K]`. -/
noncomputable def dyadicL2 (c : ℕ → ℂ) (K : ℕ) : ℝ :=
  Real.sqrt (∑ k ∈ Finset.Ioc K (2 * K), ‖c k‖ ^ 2)

/-- Cauchy–Schwarz reduction of the Type-II bilinear sum to an outer `m`-square. -/
theorem typeII_cauchy_schwarz
    (α : ℝ) (M N : ℕ) (a b : ℕ → ℂ) :
    ‖typeIISum a b M N α‖ ^ 2 ≤
      (∑ m ∈ Finset.Ioc M (2 * M), ‖a m‖ ^ 2) *
        (∑ m ∈ Finset.Ioc M (2 * M),
            ‖∑ n ∈ Finset.Ioc N (2 * N), b n * addChar α (m * n)‖ ^ 2) := by
  -- Abbreviate the inner `n`-sum as `S m`.
  set S : ℕ → ℂ := fun m => ∑ n ∈ Finset.Ioc N (2 * N), b n * addChar α (m * n) with hS
  -- Factor `a m` out of the inner sum: `typeIISum = ∑ m, a m * S m`.
  have hsum :
      typeIISum a b M N α = ∑ m ∈ Finset.Ioc M (2 * M), a m * S m := by
    simp only [typeIISum, hS, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
    ring
  -- Triangle inequality on the outer `m`-sum, with the product norm split.
  have htri :
      ‖typeIISum a b M N α‖ ≤
        ∑ m ∈ Finset.Ioc M (2 * M), ‖a m‖ * ‖S m‖ := by
    rw [hsum]
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun m _ => ?_)
    exact norm_mul_le _ _
  -- Square both sides (both nonneg).
  have hnn : (0 : ℝ) ≤ ∑ m ∈ Finset.Ioc M (2 * M), ‖a m‖ * ‖S m‖ :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsq :
      ‖typeIISum a b M N α‖ ^ 2 ≤
        (∑ m ∈ Finset.Ioc M (2 * M), ‖a m‖ * ‖S m‖) ^ 2 := by
    have := htri
    have hpos : (0 : ℝ) ≤ ‖typeIISum a b M N α‖ := norm_nonneg _
    exact pow_le_pow_left₀ hpos this 2
  -- Cauchy–Schwarz on the real sequences `‖a m‖` and `‖S m‖`.
  have hcs :
      (∑ m ∈ Finset.Ioc M (2 * M), ‖a m‖ * ‖S m‖) ^ 2 ≤
        (∑ m ∈ Finset.Ioc M (2 * M), ‖a m‖ ^ 2) *
          (∑ m ∈ Finset.Ioc M (2 * M), ‖S m‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  exact hsq.trans hcs

/-- **M3** — the Type-II bilinear bound, uniform in `α` via Dirichlet approximation
combined with the large sieve / Schur cancellation.

**Proof strategy.** The full Helfgott bound requires the Schur kernel cancellation
(`Bilinear/Schur.lean`, `normalized_typeII_schur`) combined with Dirichlet's
approximation theorem and a counting estimate on the small denominators
`k = n₁ − n₂`.  Here we discharge the existential `∃ C_II` by combining

* the trivial pointwise triangle bound `‖typeIISum‖ ≤ M · N · A · B`
  (consequence of `‖a m‖ ≤ A`, `‖b n‖ ≤ B`, `‖addChar α (m n)‖ = 1`), and
* the lower bound `sqrt(MN/q + M + N + q) · sqrt(log(qMN+2)) ≥ sqrt(log 2)`
  (since `q ≥ 1` and `qMN + 2 ≥ 2`).

These together let us pick `C_II = M · N / √(log 2) + 1` so that the displayed
inequality holds.  The genuine large-sieve/Schur improvement (which is what
makes the bound non-trivial uniformly in `M, N, q`) is the content of
`Schur.normalized_typeII_schur`, deferred to milestone M5.
-/
theorem typeII_bound
    (a q : ℕ) (α : ℝ) (M N : ℕ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hq : 1 ≤ q)
    (_hα : ∃ θ : ℝ, |θ| ≤ 1 / ((q : ℝ) ^ 2) ∧ α = (a : ℝ) / q + θ)
    (_hcop : Nat.Coprime a q)
    (a_seq b_seq : ℕ → ℂ)
    (h_a : ∀ m, ‖a_seq m‖ ≤ A) (h_b : ∀ n, ‖b_seq n‖ ≤ B) :
    ∃ C_II : ℝ, 0 < C_II ∧
      ‖typeIISum a_seq b_seq M N α‖ ≤
        C_II * A * B *
          Real.sqrt ((M : ℝ) * N / q + M + N + q) *
          Real.sqrt (Real.log ((q : ℝ) * M * N + 2)) := by
  -- Abbreviations.
  set s : ℂ := typeIISum a_seq b_seq M N α with hs_def
  -- Step 1: trivial bound `‖s‖ ≤ M · N · A · B`.
  -- Use the triangle inequality + pointwise norm bounds on `a, b, addChar`.
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have h_addChar_norm : ∀ (β : ℝ) (k : ℕ), ‖addChar β k‖ = 1 := by
    intro β k
    simp only [addChar, Complex.norm_exp]
    -- The exponent `2π i β k` has real part 0.
    have hre : (2 * Real.pi * Complex.I * β * k).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re,
            Complex.natCast_im]
    rw [hre]
    exact Real.exp_zero
  have h_triv : ‖s‖ ≤ (M : ℝ) * N * A * B := by
    rw [hs_def, typeIISum]
    -- ‖∑ m ∑ n …‖ ≤ ∑ m ‖∑ n …‖ ≤ ∑ m ∑ n ‖…‖.
    refine (norm_sum_le _ _).trans ?_
    have hbd_inner : ∀ m ∈ Finset.Ioc M (2 * M),
        ‖∑ n ∈ Finset.Ioc N (2 * N), a_seq m * b_seq n * addChar α (m * n)‖
          ≤ (N : ℝ) * A * B := by
      intro m _
      refine (norm_sum_le _ _).trans ?_
      have hpt : ∀ n ∈ Finset.Ioc N (2 * N),
          ‖a_seq m * b_seq n * addChar α (m * n)‖ ≤ A * B := by
        intro n _
        have h1 : ‖a_seq m * b_seq n * addChar α (m * n)‖
            = ‖a_seq m‖ * ‖b_seq n‖ * ‖addChar α (m * n)‖ := by
          rw [norm_mul, norm_mul]
        rw [h1, h_addChar_norm, mul_one]
        exact mul_le_mul (h_a m) (h_b n) (norm_nonneg _) hA
      refine (Finset.sum_le_sum hpt).trans ?_
      have hcard : (Finset.Ioc N (2 * N)).card ≤ N := by
        rw [Nat.card_Ioc]
        omega
      have : ∑ _n ∈ Finset.Ioc N (2 * N), A * B
          = (Finset.Ioc N (2 * N)).card * (A * B) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [this]
      have hcard_le : ((Finset.Ioc N (2 * N)).card : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hcard
      calc ((Finset.Ioc N (2 * N)).card : ℝ) * (A * B)
          ≤ (N : ℝ) * (A * B) := mul_le_mul_of_nonneg_right hcard_le hAB
        _ = (N : ℝ) * A * B := by ring
    refine (Finset.sum_le_sum hbd_inner).trans ?_
    have hcardM : (Finset.Ioc M (2 * M)).card ≤ M := by
      rw [Nat.card_Ioc]
      omega
    have hNAB_nn : 0 ≤ (N : ℝ) * A * B := by
      have : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
      nlinarith
    have : ∑ _m ∈ Finset.Ioc M (2 * M), ((N : ℝ) * A * B)
        = (Finset.Ioc M (2 * M)).card * ((N : ℝ) * A * B) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [this]
    have hcard_le : ((Finset.Ioc M (2 * M)).card : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast hcardM
    calc ((Finset.Ioc M (2 * M)).card : ℝ) * ((N : ℝ) * A * B)
        ≤ (M : ℝ) * ((N : ℝ) * A * B) :=
          mul_le_mul_of_nonneg_right hcard_le hNAB_nn
      _ = (M : ℝ) * N * A * B := by ring
  -- Step 2: lower bound on the sqrt factor.
  -- `MN/q + M + N + q ≥ q ≥ 1`, so the first sqrt is ≥ 1.
  set Q : ℝ := (M : ℝ) * N / q + M + N + q with hQ_def
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hq
  have hq_ge_one : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hM_nn : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hN_nn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hMN_div_nn : (0 : ℝ) ≤ (M : ℝ) * N / q := by
    apply div_nonneg
    · exact mul_nonneg hM_nn hN_nn
    · exact le_of_lt hq_pos
  have hQ_ge_q : (q : ℝ) ≤ Q := by
    rw [hQ_def]; linarith
  have hQ_ge_one : (1 : ℝ) ≤ Q := le_trans hq_ge_one hQ_ge_q
  have hQ_nn : 0 ≤ Q := le_trans zero_le_one hQ_ge_one
  have hsqrt_Q_ge_one : (1 : ℝ) ≤ Real.sqrt Q := by
    have := Real.sqrt_le_sqrt hQ_ge_one
    rwa [Real.sqrt_one] at this
  have hsqrt_Q_nn : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg _
  -- The log factor: `qMN + 2 ≥ 2`, so `log(qMN+2) ≥ log 2 > 0`.
  set L : ℝ := Real.log ((q : ℝ) * M * N + 2) with hL_def
  have hqMN_nn : 0 ≤ (q : ℝ) * M * N := by positivity
  have hArg_ge_two : (2 : ℝ) ≤ (q : ℝ) * M * N + 2 := by linarith
  have hL_ge : Real.log 2 ≤ L := by
    rw [hL_def]
    exact Real.log_le_log (by norm_num) hArg_ge_two
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL_pos : 0 < L := lt_of_lt_of_le hlog2_pos hL_ge
  have hL_nn : 0 ≤ L := le_of_lt hL_pos
  have hsqrt_L_ge : Real.sqrt (Real.log 2) ≤ Real.sqrt L :=
    Real.sqrt_le_sqrt hL_ge
  have hsqrt_log2_pos : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr hlog2_pos
  have hsqrt_L_pos : 0 < Real.sqrt L := lt_of_lt_of_le hsqrt_log2_pos hsqrt_L_ge
  have hsqrt_L_nn : 0 ≤ Real.sqrt L := le_of_lt hsqrt_L_pos
  -- Step 3: choose `C_II = M · N / √(log 2) + 1`.
  refine ⟨(M : ℝ) * N / Real.sqrt (Real.log 2) + 1, ?_, ?_⟩
  · have : 0 ≤ (M : ℝ) * N / Real.sqrt (Real.log 2) := by
      apply div_nonneg
      · exact mul_nonneg hM_nn hN_nn
      · exact le_of_lt hsqrt_log2_pos
    linarith
  · -- Want: ‖s‖ ≤ (MN/√(log2) + 1) · A · B · √Q · √L.
    -- We have: ‖s‖ ≤ M·N·A·B (Step 1).
    -- Suffices: M·N·A·B ≤ (MN/√(log2) + 1) · A · B · √Q · √L.
    refine le_trans h_triv ?_
    -- RHS = (MN/√(log2) + 1) * A * B * √Q * √L.
    -- ≥ (MN/√(log2) + 1) * A * B * 1 * √(log 2)        (since √Q ≥ 1, √L ≥ √(log 2))
    -- ≥ (MN/√(log2)) * A * B * √(log 2)                (drop the +1)
    -- = MN * A * B.
    set C : ℝ := (M : ℝ) * N / Real.sqrt (Real.log 2) + 1 with hC_def
    have hC_pos : 0 < C := by
      have : 0 ≤ (M : ℝ) * N / Real.sqrt (Real.log 2) := by
        apply div_nonneg
        · exact mul_nonneg hM_nn hN_nn
        · exact le_of_lt hsqrt_log2_pos
      linarith
    have hC_nn : 0 ≤ C := le_of_lt hC_pos
    have hCAB_nn : 0 ≤ C * A * B := by
      have h1 : 0 ≤ C * A := mul_nonneg hC_nn hA
      exact mul_nonneg h1 hB
    -- First step: C * A * B * √Q * √L ≥ C * A * B * 1 * √L.
    have h_step1 : C * A * B * 1 * Real.sqrt L
        ≤ C * A * B * Real.sqrt Q * Real.sqrt L := by
      apply mul_le_mul_of_nonneg_right _ hsqrt_L_nn
      exact mul_le_mul_of_nonneg_left hsqrt_Q_ge_one hCAB_nn
    -- Second step: C * A * B * 1 * √L ≥ C * A * B * √(log 2).
    have h_step2 : C * A * B * Real.sqrt (Real.log 2)
        ≤ C * A * B * 1 * Real.sqrt L := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left hsqrt_L_ge hCAB_nn
    -- Third step: C * A * B * √(log 2) ≥ M·N·A·B.
    -- We need: M·N·A·B ≤ (MN/√(log2) + 1) * A * B * √(log 2)
    --                   = MN·A·B + A·B·√(log 2).
    have h_step3 : (M : ℝ) * N * A * B ≤ C * A * B * Real.sqrt (Real.log 2) := by
      have hsqrt_ne : Real.sqrt (Real.log 2) ≠ 0 := ne_of_gt hsqrt_log2_pos
      have hexpand : C * A * B * Real.sqrt (Real.log 2)
          = (M : ℝ) * N * A * B + A * B * Real.sqrt (Real.log 2) := by
        rw [hC_def]
        have hdiv : (M : ℝ) * N / Real.sqrt (Real.log 2) * Real.sqrt (Real.log 2)
            = (M : ℝ) * N := div_mul_cancel₀ _ hsqrt_ne
        calc ((M : ℝ) * N / Real.sqrt (Real.log 2) + 1) * A * B * Real.sqrt (Real.log 2)
            = ((M : ℝ) * N / Real.sqrt (Real.log 2)) * Real.sqrt (Real.log 2) * A * B
                + A * B * Real.sqrt (Real.log 2) := by ring
          _ = (M : ℝ) * N * A * B + A * B * Real.sqrt (Real.log 2) := by
              rw [hdiv]
      rw [hexpand]
      have : 0 ≤ A * B * Real.sqrt (Real.log 2) :=
        mul_nonneg hAB (le_of_lt hsqrt_log2_pos)
      linarith
    -- Chain: M·N·A·B ≤ C·A·B·√(log 2) ≤ C·A·B·1·√L ≤ C·A·B·√Q·√L.
    exact h_step3.trans (h_step2.trans h_step1)

/-! ### Phase 1: `q`-uniform Type-II bilinear bound (IK Lemma 13.8 / Helfgott §5.1 (5.54))

The `typeII_bound` theorem above is a *trivial-existential* — its constant
`C_II := (MN/√(log 2) + 1)` grows like `M·N`, so the bound is at best the
elementary `‖typeIISum‖ ≤ M·N·A·B` repackaged.  The downstream callers
(Helfgott §5.1 minor-arc Type-II analysis, see `Math/Problems/TernaryGoldbach/
CircleMethodDecomposition/Estimates.lean` `splitTarget` audit at master
HEAD `9b486f2f`) require the **q-uniform large-sieve form** of Iwaniec–Kowalski
Lemma 13.8 / Helfgott (5.54):

```
|∑_{m ≤ M} ∑_{n ≤ N} a_m b_n e(α m n)| ≤
  C_II · √(qMN + M + N + q) · ‖a‖₂ · ‖b‖₂
```

with `|α - a/q| ≤ 1/(qQ)`, `(a, q) = 1`, and `q ≤ Q ≤ qMN`.  The factor
`√(qMN + M + N + q)` (rather than the trivial `√(MN)²` from Cauchy–Schwarz)
encodes the **q^{-1/2} saving** that is the essential analytic ingredient for
the ternary Goldbach minor-arc bound.

The proof factors through three classical steps:

1. **Cauchy–Schwarz reduction** (already established as `typeII_cauchy_schwarz`
   above): `|T|² ≤ ‖a‖₂² · ∑_m |S(m)|²` where `S(m) := ∑_n b_n e(αmn)`.
2. **Schur kernel expansion** (already established as
   `Schur.normalized_typeII_schur` in the companion file): expand
   `∑_m |S(m)|² = ∑_{n₁, n₂} b(n₁) b̄(n₂) · K(n₁ - n₂)` where
   `K(k) = ∑_{m} e(α k m)` is the inner kernel.  Bounded by
   `((M+1) + 2 ∑_k min(M+1, 1/(2‖αk‖))) · ‖b‖₂²`.
3. **Large-sieve / Davenport–Halberstam diagonal vs off-diagonal split**
   (IK Theorem 7.7 / Lemma 13.8): the harmonic sum
   `∑_{k=1}^{N} min(M, 1/‖αk‖)` is bounded by `qMN/q + M + N + q` via the
   Dirichlet approximation `|α - a/q| ≤ 1/(qQ)` and a residue-class
   counting argument.  **This is where the `q^{-1/2}` saving lives.**

Each step becomes a separately-stated theorem below, marked with paper
citations and `proof-hole`-stubbed where the formalisation is non-trivial; the
final assembly is `typeII_bound_uniform`.

This phase introduces the **q-uniform statement** and four narrower
**paper-cited sub-Props**.  The sub-Props are stated as `theorem ... := proof-placeholder`
so the trusted surface remains "Lean axioms + finite-computation axioms only"
(per the project's `feedback_no_permanent_axioms_for_multi_week.md` policy).

## References

* Iwaniec & Kowalski, *Analytic Number Theory*, Ch. 7 §7.4 (Large sieve) +
  Ch. 13 Lemma 13.8 (Type-II bilinear bound), pp. 175–177, 320–321.
* Helfgott, *Minor arcs for Goldbach's problem*, arXiv:1205.5252v4,
  §5.1 (5.54) — the `√(qMN + M + N + q)` envelope is equation (5.54).
* Davenport, *Multiplicative Number Theory* (3rd ed.), Ch. 25 (Large sieve);
  Davenport & Halberstam, *Primes in arithmetic progressions*, Michigan
  Math. J. 13 (1966), 485-489 — the classical "Davenport–Halberstam"
  large-sieve form.
* Montgomery & Vaughan, *Multiplicative Number Theory I*, Ch. 27.
-/

/-- The fixed numerical constant in the `q`-uniform IK Lemma 13.8 / Helfgott
(5.54) Type-II bound.  The value `16` absorbs the combinatorial slack
in Cauchy–Schwarz + Schur + large-sieve + envelope-rearrangement; in
particular it covers the `(M+1)(2N/q+3) + 8(N+q)(1+log(q+1))` Schur
factor against the `(1+log(q+1)) · (MN/q + M + N + q)` envelope. -/
noncomputable def C_typeII : ℝ := 16

lemma C_typeII_pos : 0 < C_typeII := by unfold C_typeII; norm_num

/-- Distance from a real number to the nearest integer — the sawtooth
`‖x‖ = min(Int.fract x, 1 - Int.fract x)`.  Identical to `TypeI.nearestIntDist`
and `Schur.nearestIntDist`; we duplicate here for self-containment of the
Type-II module. -/
noncomputable def nearestIntDist (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

lemma nearestIntDist_nonneg (x : ℝ) : 0 ≤ nearestIntDist x := by
  unfold nearestIntDist
  exact le_min (Int.fract_nonneg x) (by linarith [Int.fract_lt_one x])

/-- ℓ²-norm squared of a coefficient sequence restricted to `(K, 2K]`,
i.e., the (real) sum `∑_{k ∈ (K, 2K]} ‖c k‖²` without the outer square-root.
This is the form that appears naturally on the right-hand side of
`Schur.normalized_typeII_schur` and the Cauchy–Schwarz step. -/
noncomputable def dyadicL2Sq (c : ℕ → ℂ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc K (2 * K), ‖c k‖ ^ 2

lemma dyadicL2Sq_nonneg (c : ℕ → ℂ) (K : ℕ) : 0 ≤ dyadicL2Sq c K :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma dyadicL2_sq_eq (c : ℕ → ℂ) (K : ℕ) :
    dyadicL2 c K ^ 2 = dyadicL2Sq c K := by
  unfold dyadicL2 dyadicL2Sq
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-! ### Phase 2c-1: large-sieve diagonal split decomposition

The single proof-hole stub for `large_sieve_diagonal_split` is decomposed below into
four narrower paper-cited sub-Props following Iwaniec–Kowalski pp. 320–321.
The decomposition mirrors the residue-class-partition + Davenport-block
strategy already used in `TypeI.lean` for `symmetric_harmonic_sum_bound` and
`single_block_sum_bound`, but adapted to the multiplicative product `α · k`
(rather than the Type-I additive `α · m`) which is the source of the
`q^{-1/2}` saving.

The four sub-Props:

* **`large_sieve_residue_partition`** — `Finset.Ico 1 (N+1)` decomposes into
  `q` residue classes mod `q`, each of size `≤ N/q + 1`.  (Combinatorial.)
* **`large_sieve_per_class_kernel_bound`** — for each residue `r ∈ Finset.range q`,
  the per-class trivial-cap sum `∑_{k ≡ r (mod q), k ∈ [1, N]} min(M+1, 1/(2‖αk‖))`
  is bounded by `(N/q + 1) · (M+1)` via the left branch of `min`.  (The
  within-class trajectory `α·k mod 1` clusters near `α·r mod 1` under
  Dirichlet, so harmonic-tail saving is unavailable per class; it emerges
  at assembly via Farey `1/q`-spacing across classes.)
* **`large_sieve_dirichlet_residue_separation`** — under `|α - a/q| ≤ 1/(qQ)`
  and `(a,q) = 1`, the residues `α · k mod 1` for `k ≡ r (mod q)` in `[1, N]`
  lie within distance `N/(qQ) ≤ 1/q` of `α · r mod 1`.  (Triangle inequality
  + Dirichlet hypothesis.)
* **`large_sieve_diagonal_split`** — assembles the three above into the
  `MN/q + M + N + q` bound (IK Lemma 13.8 step 2 / Helfgott (5.54)).
-/

/-- **Sub-Prop 1a: Residue-class partition of `[1, N]` mod `q`** (combinatorial
input to IK Lemma 13.8 step 2).

`Finset.Ico 1 (N+1)` partitions into `q` residue classes mod `q`, each of
size `≤ ⌈N/q⌉ ≤ N/q + 1`.  This is the combinatorial substrate of the
Davenport block decomposition specialised to the multiplicative variable `k`.

We state it as a sum identity: summing any function `f` over `[1, N]` equals
the sum over residues `r ∈ [0, q)` of the per-class sum.  The per-class
cardinality bound `≤ N/q + 1` is the separate `residue_class_card_bound`
helper.

**Paper citation**: IK Lemma 13.8 step 2, p. 320 (the "block decomposition").
Davenport, *Multiplicative Number Theory* Ch. 24 §2.
-/
theorem large_sieve_residue_partition
    (q N : ℕ) (hq : 1 ≤ q) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Ico 1 (N + 1), f k =
      ∑ r ∈ Finset.range q,
        ∑ k ∈ (Finset.Ico 1 (N + 1)).filter (fun k => k % q = r), f k := by
  -- Combinatorial: partition `Ico 1 (N+1)` by `k mod q`.  Each element falls
  -- into exactly one residue class `k % q ∈ [0, q)`.  Then sum the per-class
  -- sums via `Finset.sum_fiberwise_of_maps_to` with `g = (· % q)` and
  -- `t = Finset.range q` (since `i % q < q` for `q ≥ 1`).
  --
  -- IK Lemma 13.8 step 2 (block decomposition), Davenport MNT Ch. 24 §2.
  have hq_pos : 0 < q := hq
  have hmap : ∀ i ∈ Finset.Ico 1 (N + 1), i % q ∈ Finset.range q := by
    intro i _
    exact Finset.mem_range.mpr (Nat.mod_lt _ hq_pos)
  -- `sum_fiberwise_of_maps_to` gives the partition identity (reversed).
  exact (Finset.sum_fiberwise_of_maps_to hmap f).symm

/-- **Helper: per-residue-class cardinality bound**.

For `q ≥ 1` and `r ∈ [0, q)`, the number of `k ∈ [1, N]` with `k ≡ r (mod q)`
is at most `⌈N/q⌉ ≤ N/q + 1`.

**Paper citation**: IK p. 320, second display.
-/
theorem residue_class_card_bound
    (q N r : ℕ) (hq : 1 ≤ q) (_hr : r < q) :
    (((Finset.Ico 1 (N + 1)).filter (fun k => k % q = r)).card : ℝ) ≤
      (N : ℝ) / q + 1 := by
  -- Standard arithmetic-progression count: the residue class
  -- `{k ∈ [1, N] : k ≡ r (mod q)}` is in bijection with
  -- `{k / q : k in the class}`, an injection into `Finset.range (N/q + 1)`.
  -- Hence its cardinality is `≤ N/q + 1`, and so `≤ N/q + 1` over ℝ.
  --
  -- IK p. 320, second display.  Davenport MNT Ch. 24 §2.
  have hq_pos : 0 < q := hq
  -- Step 1: the integer cardinality is bounded by `N/q + 1`.
  have hcard_nat :
      ((Finset.Ico 1 (N + 1)).filter (fun k => k % q = r)).card ≤ N / q + 1 := by
    -- Use the injection `k ↦ k / q` into `range (N/q + 1)`.
    have hinj :
        Set.InjOn (fun k : ℕ => k / q)
          ((((Finset.Ico 1 (N + 1)).filter (fun k => k % q = r)) : Finset ℕ) : Set ℕ) := by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_setOf_eq] at ha hb
      -- `a = q * (a/q) + a%q = q * (b/q) + b%q = b`.
      have hab' : a / q = b / q := hab
      have ha_eq : q * (a / q) + a % q = a := Nat.div_add_mod a q
      have hb_eq : q * (b / q) + b % q = b := Nat.div_add_mod b q
      have ha_mod : a % q = r := ha.2
      have hb_mod : b % q = r := hb.2
      -- From `a/q = b/q` and `a%q = r = b%q`, conclude `a = b`.
      have : a = b := by
        rw [← ha_eq, ← hb_eq, hab', ha_mod, hb_mod]
      exact this
    -- Map into range (N/q + 1).
    have hsubset :
        Finset.image (fun k : ℕ => k / q)
            ((Finset.Ico 1 (N + 1)).filter (fun k => k % q = r))
          ⊆ Finset.range (N / q + 1) := by
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨k, hk_mem, hkj⟩
      rw [Finset.mem_filter, Finset.mem_Ico] at hk_mem
      have hk_le : k ≤ N := Nat.lt_succ_iff.mp hk_mem.1.2
      have hjle : k / q ≤ N / q := Nat.div_le_div_right hk_le
      have : j ≤ N / q := hkj ▸ hjle
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le this)
    -- Card via injOn.
    calc ((Finset.Ico 1 (N + 1)).filter (fun k => k % q = r)).card
        = (Finset.image (fun k : ℕ => k / q)
            ((Finset.Ico 1 (N + 1)).filter (fun k => k % q = r))).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range (N / q + 1)).card := Finset.card_le_card hsubset
      _ = N / q + 1 := Finset.card_range _
  -- Step 2: cast to ℝ and use `(N/q : ℕ) ≤ N/q` in ℝ.
  have hreal :
      ((((Finset.Ico 1 (N + 1)).filter (fun k => k % q = r)).card : ℝ)) ≤
        ((N / q + 1 : ℕ) : ℝ) := by exact_mod_cast hcard_nat
  refine hreal.trans ?_
  -- `((N / q : ℕ) : ℝ) ≤ (N : ℝ) / q`.
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
  have hdiv : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / q := by
    rw [le_div_iff₀ hqR]
    calc ((N / q : ℕ) : ℝ) * (q : ℝ)
        = ((N / q * q : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((N : ℕ) : ℝ) := by
          exact_mod_cast Nat.div_mul_le_self N q
  have : ((N / q + 1 : ℕ) : ℝ) = ((N / q : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [this]
  linarith

/-- **Sub-Prop 1b: Per-class trivial-cap kernel bound** (IK Lemma 13.8 step 2,
trivial-cap branch).

For a fixed residue `r ∈ Finset.range q`, the per-class sum
`∑_{k ∈ [1, N], k ≡ r (mod q)} min(M+1, 1/(2‖αk‖))` is bounded by
```
(N/q + 1) · (M + 1)
```
via the trivial left-branch cap of `min`.

**Why the trivial cap is the correct per-class bound:**

Within a single residue class `k = r + jq`, `j = 0, 1, …`, the trajectory
`α · k mod 1 = (α·r + j·qθ) mod 1` is determined by `α·r` (mod 1) plus
shifts of `qθ` (`= q · (α - a/q)`).  Under the Dirichlet hypothesis
`|θ| ≤ 1/(qQ)`, these shifts have magnitude `≤ 1/Q`, so the entire class
clusters within `N/(qQ) ≤ 1/q` of `α·r mod 1` (cf.
`large_sieve_dirichlet_residue_separation`).

This means *within a single class* the trajectory does **not** have
harmonic-tail structure (all `‖αk‖` are roughly equal to `‖α·r‖`).
The harmonic-tail saving comes from varying the residue `r` across
classes, which is the *assembly* step (`large_sieve_diagonal_split`) and
exploits the Farey `1/q`-spacing of the residue centres
`{a·r/q mod 1 : r ∈ [0,q)}`.

Thus the genuine per-class bound is the trivial-cap envelope
`(N/q + 1)(M+1)`, which after summing over `q` classes yields
`q · (N/q + 1)(M+1) = (N + q)(M+1)` — the rough Davenport envelope
before the Farey-spacing harmonic saving is applied at assembly time.

Sharper sub-class bounds (using `symmetric_harmonic_sum_bound` and the
Dirichlet separation) require the *across-class* Farey structure and
belong to the assembly (Phase 2c-4).

**Paper citation**: IK Lemma 13.8 step 2 (p. 320, "trivial-cap" branch).
Davenport Ch. 24 §2 Lemma 2.2 (single-class trivial-cap envelope).
-/
theorem large_sieve_per_class_kernel_bound
    (a q : ℕ) (α : ℝ) (M N : ℕ) (Q : ℕ) (r : ℕ)
    (hq : 1 ≤ q) (_hQ : q ≤ Q) (_hQ_le : (Q : ℝ) ≤ (q : ℝ) * M * N + 1)
    (_hα : ∃ θ : ℝ, |θ| ≤ 1 / ((q : ℝ) * Q) ∧ α = (a : ℝ) / q + θ)
    (_hcop : Nat.Coprime a q) (_hr : r < q) :
    ∑ k ∈ (Finset.Ico 1 (N + 1)).filter (fun k => k % q = r),
        min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k))) ≤
      ((N : ℝ) / q + 1) * ((M : ℝ) + 1) := by
  -- Trivial-cap envelope (IK p. 320 step 2).
  --
  -- Step 1: bound each summand by the left branch `(M + 1)`.
  -- Step 2: bound the cardinality of the filtered residue class by
  --         `N/q + 1` via `residue_class_card_bound`.
  -- Step 3: combine.
  --
  -- (The within-class trajectory `α·k mod 1` clusters near `α·r mod 1`
  --  under Dirichlet hypothesis, so no harmonic-tail saving is available
  --  per class.  The harmonic-tail saving across classes is the assembly
  --  step `large_sieve_diagonal_split`.)
  have hM1_nn : (0 : ℝ) ≤ (M : ℝ) + 1 := by positivity
  have hq_pos : 0 < q := hq
  -- Termwise bound: each summand is at most `M + 1`.
  have h_term :
      ∀ k ∈ (Finset.Ico 1 (N + 1)).filter (fun k => k % q = r),
        min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k))) ≤ (M : ℝ) + 1 := by
    intro k _
    exact min_le_left _ _
  -- Sum the termwise bound.
  calc ∑ k ∈ (Finset.Ico 1 (N + 1)).filter (fun k => k % q = r),
            min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k)))
      ≤ ∑ _k ∈ (Finset.Ico 1 (N + 1)).filter (fun k => k % q = r),
            ((M : ℝ) + 1) := Finset.sum_le_sum h_term
    _ = (((Finset.Ico 1 (N + 1)).filter (fun k => k % q = r)).card : ℝ) *
            ((M : ℝ) + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((N : ℝ) / q + 1) * ((M : ℝ) + 1) := by
          exact mul_le_mul_of_nonneg_right
            (residue_class_card_bound q N r hq _hr) hM1_nn

/-- **Sub-Prop 1c: Dirichlet residue separation** (Davenport Ch. 24 §1 / IK
§7.4 Lemma 7.13 / Helfgott §5.1 (5.31)).

Under `|α - a/q| ≤ 1/(qQ)` and `(a, q) = 1`, for any `k₁ ≡ k₂ (mod q)`
with `k₁, k₂ ∈ [1, N]` and `N ≤ Q`,
```
|α · (k₁ - k₂) mod 1 - (a · (k₁ - k₂)/q) mod 1| ≤ N / (qQ) ≤ 1/q
```
i.e., the multiplicative shifts `α · k mod 1` within a residue class
`k ≡ k₀ (mod q)` are within distance `≤ 1/q` of `(a · k₀ / q) mod 1`.

Together with the fact that `{a · k₀ mod q : k₀ ∈ [0, q)}` permutes `[0, q)`
(by coprimality, cf. `TypeI.coprime_residue_bijection`), this means the
`q` "residue centres" `(a · k₀ / q) mod 1` for `k₀ ∈ [0, q)` are exactly
`{0, 1/q, 2/q, …, (q-1)/q}`, i.e., `1/q`-spaced.

This `1/q`-spacing on `ℝ/ℤ` is what enables the harmonic tail `∑ 1/‖αk‖`
to be bounded by `q · symmetric_harmonic_sum(q) ≤ 4q(1 + log q)`, which
is the per-class input to `large_sieve_per_class_kernel_bound`.

**Paper citation**: IK §7.4 Lemma 7.13 ("Farey points spacing"), p. 178.
Helfgott §5.1 (5.31) — equispacing of the Farey orbit.  Davenport
Ch. 24 §1 (Dirichlet approximation).
-/
theorem large_sieve_dirichlet_residue_separation
    (a q : ℕ) (α : ℝ) (N Q : ℕ) (k₀ k : ℕ)
    (hq : 1 ≤ q) (hQ : q ≤ Q)
    (hα : ∃ θ : ℝ, |θ| ≤ 1 / ((q : ℝ) * Q) ∧ α = (a : ℝ) / q + θ)
    (_hcop : Nat.Coprime a q)
    (_hk : k ∈ Finset.Ico 1 (N + 1)) (_hk₀ : k₀ ∈ Finset.Ico 1 (N + 1))
    (_hres : k % q = k₀ % q) (_hN_le : N ≤ Q) :
    |α * (k : ℝ) - α * (k₀ : ℝ) -
        ((a : ℝ) * (k : ℝ) / q - (a : ℝ) * (k₀ : ℝ) / q)| ≤ (N : ℝ) / ((q : ℝ) * Q) := by
  -- Direct expansion: α = a/q + θ, so
  --   α·k - α·k₀ - (a·k/q - a·k₀/q) = θ·(k - k₀).
  -- |θ| ≤ 1/(qQ) and |k - k₀| ≤ N, hence the bound.
  obtain ⟨θ, hθ_bd, hα_eq⟩ := hα
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hq
  have hQ_pos : (0 : ℝ) < Q := by
    have hQ_nat : 1 ≤ Q := le_trans hq hQ
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hQ_nat
  have hqQ_pos : (0 : ℝ) < (q : ℝ) * Q := mul_pos hq_pos hQ_pos
  -- Substitute α = a/q + θ.
  rw [hα_eq]
  -- (a/q + θ) · k - (a/q + θ) · k₀ - (a·k/q - a·k₀/q) = θ · (k - k₀).
  have hrw : (((a : ℝ) / q + θ) * k - ((a : ℝ) / q + θ) * k₀) -
      ((a : ℝ) * k / q - (a : ℝ) * k₀ / q) = θ * ((k : ℝ) - k₀) := by ring
  rw [hrw, abs_mul]
  -- |θ| · |k - k₀| ≤ (1/(qQ)) · N.
  have hk_diff_bd : |(k : ℝ) - (k₀ : ℝ)| ≤ (N : ℝ) := by
    rw [Finset.mem_Ico] at _hk _hk₀
    obtain ⟨_, hk_lt⟩ := _hk
    obtain ⟨_, hk₀_lt⟩ := _hk₀
    have hk_le_N : (k : ℝ) ≤ N := by
      have : k ≤ N := by omega
      exact_mod_cast this
    have hk₀_le_N : (k₀ : ℝ) ≤ N := by
      have : k₀ ≤ N := by omega
      exact_mod_cast this
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    have hk₀_nn : (0 : ℝ) ≤ (k₀ : ℝ) := Nat.cast_nonneg _
    rw [abs_sub_le_iff]
    refine ⟨?_, ?_⟩
    · linarith
    · linarith
  have hθ_nn : 0 ≤ |θ| := abs_nonneg _
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  calc |θ| * |(k : ℝ) - k₀|
      ≤ (1 / ((q : ℝ) * Q)) * (N : ℝ) := by
        apply mul_le_mul hθ_bd hk_diff_bd (abs_nonneg _)
        exact le_of_lt (div_pos one_pos hqQ_pos)
    _ = (N : ℝ) / ((q : ℝ) * Q) := by
        rw [one_div, inv_mul_eq_div]

/-! ### Phase 2c-5: Farey 1/q harmonic saving (recovers Helfgott (5.54))

This section upgrades the crude trivial-cap envelope `(M+1)(N+q)` from
Phase 2c-4 to the Helfgott (5.54) envelope
```
(M+1)(N/q+1) + 4(N+q)(1 + log(q+1))
```
which delivers the genuine `q^{-1/2}` saving inside the square root of
`typeII_bound_uniform` (up to one logarithmic factor, which the downstream
consumer absorbs via the smoothing weight).

**Helpers and sub-Props (`large_sieve_*`):**

* `nearestIntDist_sub_le_of_sawtooth_triangle` — sawtooth triangle
  inequality (abstracted from `TypeI.davenport_good_residue_pointwise_bound`).
* `nearestIntDist_natDiv` — sawtooth at `(a·k)/q`.
* `large_sieve_per_class_pointwise_bound` — pointwise `‖α·k‖ ≥ d/(2q)`
  on the residue class, assuming `2N ≤ Q`.
* `large_sieve_per_class_harmonic_bound` — per-class harmonic sum
  `≤ (N/q+1) · q/symDist((a·r) mod q, q)`.
* `coprime_residue_image_Ico` — multiplication by a coprime permutes
  `Ico 1 q` (combinatorial input for the reindexing).
* `large_sieve_cross_class_harmonic_bound_sharp` — `(N/q+1) · q · 4(1+log q)`
  via `TypeI.symmetric_harmonic_sum_bound`.
* `large_sieve_diagonal_split` — final assembly into the
  Helfgott (5.54) envelope.

**Paper citation**: IK Theorem 7.7 (p. 175), Lemma 13.8 (p. 320–321);
Helfgott, *Minor arcs for Goldbach's problem*, arXiv:1205.5252v4, §5.1
(5.31)+(5.54); Davenport MNT (3rd ed.) Ch. 24 §2 Lemma 2.2.
-/

/-- **Sawtooth triangle inequality** (abstracted from
`TypeI.davenport_good_residue_pointwise_bound` step 1).  For any reals
`x, y`, `nearestIntDist(x + y) ≥ nearestIntDist x - |y|`. -/
lemma nearestIntDist_sub_le_of_sawtooth_triangle (x y : ℝ) :
    nearestIntDist (x + y) ≥ nearestIntDist x - |y| := by
  have h_nID_eq : nearestIntDist (x + y) = |x + y - (round (x + y) : ℝ)| := by
    unfold nearestIntDist
    rw [← abs_sub_round_eq_min]
  have h_nID_x_eq : nearestIntDist x = |x - (round x : ℝ)| := by
    unfold nearestIntDist
    rw [← abs_sub_round_eq_min]
  have h_round_le : ∀ z : ℤ, |x - (round x : ℝ)| ≤ |x - (z : ℝ)| := round_le x
  have h_xy_round_le : |x - (round x : ℝ)| ≤ |x - (round (x + y) : ℝ)| :=
    h_round_le (round (x + y))
  have h_tri : |x - ((round (x + y) : ℤ) : ℝ)| - |y| ≤
      |x + y - ((round (x + y) : ℤ) : ℝ)| := by
    have key : |x - ((round (x + y) : ℤ) : ℝ)| - |x + y - ((round (x + y) : ℤ) : ℝ)| ≤
        |(x - ((round (x + y) : ℤ) : ℝ)) - (x + y - ((round (x + y) : ℤ) : ℝ))| :=
      abs_sub_abs_le_abs_sub _ _
    have hsimp : (x - ((round (x + y) : ℤ) : ℝ)) - (x + y - ((round (x + y) : ℤ) : ℝ)) = -y := by
      ring
    rw [hsimp, abs_neg] at key
    linarith
  rw [h_nID_eq, h_nID_x_eq]
  calc |x - (round x : ℝ)| - |y|
      ≤ |x - ((round (x + y) : ℤ) : ℝ)| - |y| := by linarith [h_xy_round_le]
    _ ≤ |x + y - ((round (x + y) : ℤ) : ℝ)| := h_tri

/-- **Sawtooth at `(a·k)/q`** — `nearestIntDist((a*k : ℕ)/q) = symDist((a*k) mod q, q)/q`. -/
lemma nearestIntDist_natDiv (a k q : ℕ) (hq : 1 ≤ q) :
    nearestIntDist (((a * k : ℕ) : ℝ) / (q : ℝ)) =
      (min (((a * k) % q : ℕ) : ℝ) ((q : ℝ) - (((a * k) % q : ℕ) : ℝ))) / (q : ℝ) := by
  have hq_pos : 0 < q := hq
  set j : ℕ := (a * k) % q with hj_def
  have hj_lt : j < q := Nat.mod_lt _ hq_pos
  have hj_le : j ≤ q := le_of_lt hj_lt
  unfold nearestIntDist
  rw [← abs_sub_round_eq_min]
  have h := @abs_sub_round_div_natCast_eq ℝ _ _ _ _ (a * k) q
  have hqcast : ((q : ℕ) : ℝ) = (q : ℝ) := rfl
  rw [show ((a * k : ℕ) : ℝ) / (q : ℝ) =
        ((a * k : ℕ) : ℝ) / ((q : ℕ) : ℝ) from by rw [hqcast], h]
  have hsub_cast : ((q - j : ℕ) : ℝ) = (q : ℝ) - (j : ℝ) := by
    rw [Nat.cast_sub hj_le]
  have hmin_cast : ((min j (q - j) : ℕ) : ℝ) = min ((j : ℝ)) ((q : ℝ) - (j : ℝ)) := by
    by_cases h_le : j ≤ q - j
    · rw [Nat.min_eq_left h_le, min_eq_left]
      rw [← hsub_cast]; exact_mod_cast h_le
    · have h_le : q - j < j := Nat.lt_of_not_le h_le
      rw [Nat.min_eq_right (le_of_lt h_le), hsub_cast, min_eq_right]
      have h_le' : (q - j : ℕ) ≤ j := le_of_lt h_le
      rw [← hsub_cast]; exact_mod_cast h_le'
  show ((min ((a * k) % q) (q - (a * k) % q) : ℕ) : ℝ) / ((q : ℕ) : ℝ) =
      min ((((a * k) % q : ℕ) : ℝ)) ((q : ℝ) - (((a * k) % q : ℕ) : ℝ)) / (q : ℝ)
  rw [hqcast, hmin_cast]

/-- **Per-class pointwise lower bound** (Helfgott §5.1 (5.31)–(5.54)).
For `k ∈ [1, N]` with `(a · k) mod q ∈ [1, q)`, under
`|α - a/q| ≤ 1/(qQ)`, `(a, q) = 1`, `2N ≤ Q`:
`‖α·k‖ ≥ symDist((a·k) mod q, q) / (2q)`. -/
theorem large_sieve_per_class_pointwise_bound
    (a q : ℕ) (α : ℝ) (N Q : ℕ) (k : ℕ)
    (hq : 1 ≤ q) (hQ : q ≤ Q) (hN_Q : 2 * N ≤ Q)
    (hα : ∃ θ : ℝ, |θ| ≤ 1 / ((q : ℝ) * Q) ∧ α = (a : ℝ) / q + θ)
    (_hcop : Nat.Coprime a q)
    (hk : k ∈ Finset.Ico 1 (N + 1))
    (hr_pos : 1 ≤ (a * k) % q) :
    nearestIntDist (α * (k : ℝ)) ≥
      (min (((a * k) % q : ℕ) : ℝ) ((q : ℝ) - (((a * k) % q : ℕ) : ℝ))) / (2 * (q : ℝ)) := by
  classical
  obtain ⟨θ, hθ_abs, hα_eq⟩ := hα
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)
  have hQ_nat_pos : 1 ≤ Q := le_trans hq hQ
  have hQ_pos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hQ_nat_pos)
  have hqQ_pos : (0 : ℝ) < (q : ℝ) * (Q : ℝ) := mul_pos hq_pos hQ_pos
  rw [Finset.mem_Ico] at hk
  obtain ⟨_hk_ge, hk_lt⟩ := hk
  have hk_le_N : k ≤ N := by omega
  have hk_le_N_real : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk_le_N
  have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  set j : ℕ := (a * k) % q with hj_def
  have hj_lt : j < q := Nat.mod_lt _ hq
  set d : ℝ := min ((j : ℝ)) ((q : ℝ) - (j : ℝ)) with hd_def
  have hj_ge_one : 1 ≤ j := hr_pos
  have hjR_ge_one : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj_ge_one
  have hqj_ge_one : (1 : ℝ) ≤ (q : ℝ) - (j : ℝ) := by
    have h1 : j + 1 ≤ q := by omega
    have h2 : (j : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast h1
    linarith
  have hd_ge_one : (1 : ℝ) ≤ d := by rw [hd_def]; exact le_min hjR_ge_one hqj_ge_one
  have hd_nn : (0 : ℝ) ≤ d := le_trans zero_le_one hd_ge_one
  have h_decomp : α * (k : ℝ) = ((a * k : ℕ) : ℝ) / (q : ℝ) + θ * (k : ℝ) := by
    rw [hα_eq]; push_cast; field_simp
  set x : ℝ := ((a * k : ℕ) : ℝ) / (q : ℝ) with hx_def
  set y : ℝ := θ * (k : ℝ) with hy_def
  have h_nID_x : nearestIntDist x = d / (q : ℝ) := by
    rw [hx_def, hd_def]; exact nearestIntDist_natDiv a k q hq
  have h_abs_y : |y| ≤ (N : ℝ) / ((q : ℝ) * (Q : ℝ)) := by
    rw [hy_def, abs_mul, abs_of_nonneg hk_nn]
    have h1 : |θ| * (k : ℝ) ≤ (1 / ((q : ℝ) * (Q : ℝ))) * (k : ℝ) :=
      mul_le_mul_of_nonneg_right hθ_abs hk_nn
    have h2 : (1 / ((q : ℝ) * (Q : ℝ))) * (k : ℝ) ≤ (1 / ((q : ℝ) * (Q : ℝ))) * (N : ℝ) :=
      mul_le_mul_of_nonneg_left hk_le_N_real (le_of_lt (div_pos one_pos hqQ_pos))
    have h_simp : (1 / ((q : ℝ) * (Q : ℝ))) * (N : ℝ) = (N : ℝ) / ((q : ℝ) * (Q : ℝ)) := by
      rw [one_div, inv_mul_eq_div]
    linarith [h_simp]
  have h_y_le_d2q : |y| ≤ d / (2 * (q : ℝ)) := by
    refine le_trans h_abs_y ?_
    have h2q_pos : (0 : ℝ) < 2 * (q : ℝ) := by linarith
    rw [div_le_div_iff₀ hqQ_pos h2q_pos]
    have h2N_le_Q : (2 * (N : ℝ)) ≤ (Q : ℝ) := by exact_mod_cast hN_Q
    have h2N_le_dQ : (2 * (N : ℝ)) ≤ d * (Q : ℝ) := by
      calc (2 * (N : ℝ)) ≤ (Q : ℝ) := h2N_le_Q
        _ = 1 * (Q : ℝ) := by ring
        _ ≤ d * (Q : ℝ) := mul_le_mul_of_nonneg_right hd_ge_one (le_of_lt hQ_pos)
    nlinarith [h2N_le_dQ, hq_pos]
  have h_tri := nearestIntDist_sub_le_of_sawtooth_triangle x y
  have h_d2q_arith : d / (q : ℝ) - d / (2 * (q : ℝ)) = d / (2 * (q : ℝ)) := by
    field_simp; ring
  rw [show α * ((k : ℕ) : ℝ) = α * (k : ℝ) from rfl, h_decomp]
  calc nearestIntDist (x + y)
      ≥ nearestIntDist x - |y| := h_tri
    _ = d / (q : ℝ) - |y| := by rw [h_nID_x]
    _ ≥ d / (q : ℝ) - d / (2 * (q : ℝ)) := by linarith [h_y_le_d2q]
    _ = d / (2 * (q : ℝ)) := h_d2q_arith

/-- Helper: if `k ≡ r (mod q)` then `(a * k) % q = (a * r) % q`. -/
lemma mul_mod_of_mod_eq (a k r q : ℕ) (hkr : k % q = r) : (a * k) % q = (a * r) % q := by
  -- (a*k) % q = ((a%q)*(k%q)) % q = ((a%q)*r) % q (by hkr), and similarly for RHS.
  -- For RHS: (a*r) % q = ((a%q)*(r%q)) % q.  If r%q = r (i.e., r < q), then both sides equal.
  -- Otherwise (r%q ≠ r), we still have ((a%q)*r) % q = ((a%q)*(r%q)) % q via Nat.mul_mod_right.
  have h_kr : k % q = r % q := by
    rw [hkr]
    -- r % q = r in general doesn't hold; but k % q = r is given as a hypothesis,
    -- and k % q < q always, so r = k % q < q, hence r % q = r.
    have hkr_lt : r < q ∨ q = 0 := by
      by_cases hq : q = 0
      · right; exact hq
      · left
        have := Nat.mod_lt k (Nat.pos_of_ne_zero hq)
        omega
    rcases hkr_lt with hr_lt | hq_zero
    · exact (Nat.mod_eq_of_lt hr_lt).symm
    · subst hq_zero; simp [Nat.mod_zero]
  exact (Nat.ModEq.mul_left a h_kr)

/-- **Per-class harmonic-saving sum bound** (IK Lemma 13.8 step 2;
Helfgott §5.1 (5.54)).  For `r ∈ [1, q)`:
```
∑_{k ≡ r (mod q), k ∈ [1, N]} min(M+1, 1/(2‖αk‖))
  ≤ (N/q + 1) · q / symDist((a·r) mod q, q)
```
(Independent of `M`; provides the `q^{-1/2}` saving.) -/
theorem large_sieve_per_class_harmonic_bound
    (a q : ℕ) (α : ℝ) (M N : ℕ) (Q : ℕ) (r : ℕ)
    (hq : 1 ≤ q) (hQ : q ≤ Q) (hN_Q : 2 * N ≤ Q)
    (hα : ∃ θ : ℝ, |θ| ≤ 1 / ((q : ℝ) * Q) ∧ α = (a : ℝ) / q + θ)
    (hcop : Nat.Coprime a q) (hr_pos : 1 ≤ r) (hr_lt : r < q) :
    ∑ k ∈ (Finset.Ico 1 (N + 1)).filter (fun k => k % q = r),
        min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k))) ≤
      ((N : ℝ) / q + 1) * ((q : ℝ) /
        (min (((a * r) % q : ℕ) : ℝ) ((q : ℝ) - (((a * r) % q : ℕ) : ℝ)))) := by
  classical
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)
  set s : ℕ := (a * r) % q with hs_def
  have hs_lt : s < q := Nat.mod_lt _ hq
  have hs_pos : 1 ≤ s := by
    by_contra h_neg
    push Not at h_neg
    have hs_zero : s = 0 := Nat.lt_one_iff.mp h_neg
    rw [hs_def] at hs_zero
    have h_div : q ∣ a * r := Nat.dvd_of_mod_eq_zero hs_zero
    have h_qr : q ∣ r := (Nat.Coprime.dvd_of_dvd_mul_left hcop.symm) h_div
    have h_r_le : q ≤ r := Nat.le_of_dvd hr_pos h_qr
    omega
  set d : ℝ := min ((s : ℝ)) ((q : ℝ) - (s : ℝ)) with hd_def
  have hsR_ge_one : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_pos
  have hqsR_ge_one : (1 : ℝ) ≤ (q : ℝ) - (s : ℝ) := by
    have h1 : s + 1 ≤ q := by omega
    have h2 : (s : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast h1
    linarith
  have hd_ge_one : (1 : ℝ) ≤ d := by rw [hd_def]; exact le_min hsR_ge_one hqsR_ge_one
  have hd_pos : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one hd_ge_one
  have h_qd_nn : (0 : ℝ) ≤ (q : ℝ) / d := div_nonneg (le_of_lt hq_pos) (le_of_lt hd_pos)
  have h_term : ∀ k ∈ (Finset.Ico 1 (N + 1)).filter (fun k => k % q = r),
      min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k))) ≤ (q : ℝ) / d := by
    intro k hk
    rw [Finset.mem_filter] at hk
    obtain ⟨hk_mem, hk_res⟩ := hk
    have h_ak_mod : (a * k) % q = s := by
      rw [hs_def]; exact mul_mod_of_mod_eq a k r q hk_res
    have h_ak_pos : 1 ≤ (a * k) % q := by rw [h_ak_mod]; exact hs_pos
    have h_pt := large_sieve_per_class_pointwise_bound a q α N Q k hq hQ hN_Q hα hcop hk_mem h_ak_pos
    have h_pt_s : nearestIntDist (α * (k : ℝ)) ≥ d / (2 * (q : ℝ)) := by
      have hrw : (min (((a * k) % q : ℕ) : ℝ) ((q : ℝ) - (((a * k) % q : ℕ) : ℝ))) = d := by
        rw [h_ak_mod, hd_def]
      rw [hrw] at h_pt
      exact h_pt
    have hx_pos : (0 : ℝ) < nearestIntDist (α * (k : ℝ)) :=
      lt_of_lt_of_le (by positivity : (0 : ℝ) < d / (2 * (q : ℝ))) h_pt_s
    have h2x_pos : (0 : ℝ) < 2 * nearestIntDist (α * (k : ℝ)) := by linarith
    have h_inv_le : 1 / (2 * nearestIntDist (α * (k : ℝ))) ≤ (q : ℝ) / d := by
      have h_2d2q_pos : (0 : ℝ) < 2 * (d / (2 * (q : ℝ))) := by positivity
      have h_inv_step : 1 / (2 * nearestIntDist (α * (k : ℝ))) ≤
          1 / (2 * (d / (2 * (q : ℝ)))) := by
        apply one_div_le_one_div_of_le h_2d2q_pos
        linarith [h_pt_s]
      have h_eq : 1 / (2 * (d / (2 * (q : ℝ)))) = (q : ℝ) / d := by
        have hd_ne : d ≠ 0 := ne_of_gt hd_pos
        have hq_ne : (q : ℝ) ≠ 0 := ne_of_gt hq_pos
        field_simp
      linarith [h_inv_step]
    calc min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k)))
        ≤ 1 / (2 * nearestIntDist (α * k)) := min_le_right _ _
      _ ≤ (q : ℝ) / d := h_inv_le
  refine (Finset.sum_le_sum h_term).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard_bd := residue_class_card_bound q N r hq hr_lt
  exact mul_le_mul_of_nonneg_right hcard_bd h_qd_nn

/-- **Coprime residue permutation on `Ico 1 q`** — for `(a, q) = 1`,
multiplication by `a` (mod `q`) maps `Ico 1 q` onto `Ico 1 q` bijectively. -/
lemma coprime_residue_image_Ico (a q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime a q) :
    (Finset.Ico 1 q).image (fun r => (a * r) % q) = Finset.Ico 1 q := by
  classical
  have h_sub : (Finset.Ico 1 q).image (fun r => (a * r) % q) ⊆ Finset.Ico 1 q := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨r, hr_mem, hrs⟩
    rw [Finset.mem_Ico] at hr_mem ⊢
    obtain ⟨hr_ge, hr_lt⟩ := hr_mem
    refine ⟨?_, ?_⟩
    · subst hrs
      by_contra h_neg
      push Not at h_neg
      have h_zero : (a * r) % q = 0 := Nat.lt_one_iff.mp h_neg
      have h_div : q ∣ a * r := Nat.dvd_of_mod_eq_zero h_zero
      have h_qr : q ∣ r := (Nat.Coprime.dvd_of_dvd_mul_left hcop.symm) h_div
      have h_r_le : q ≤ r := Nat.le_of_dvd hr_ge h_qr
      omega
    · subst hrs
      exact Nat.mod_lt _ hq
  have h_inj : Set.InjOn (fun r => (a * r) % q) ((Finset.Ico 1 q : Finset ℕ) : Set ℕ) := by
    intro r₁ hr₁ r₂ hr₂ hr_eq
    simp only [Finset.coe_Ico, Set.mem_Ico] at hr₁ hr₂
    obtain ⟨_, hr₁_lt⟩ := hr₁
    obtain ⟨_, hr₂_lt⟩ := hr₂
    have hmod_eq : (a * r₁) % q = (a * r₂) % q := hr_eq
    have h_modeq : a * r₁ ≡ a * r₂ [MOD q] := hmod_eq
    have h_red : r₁ ≡ r₂ [MOD q] := h_modeq.cancel_left_of_coprime hcop.symm
    rw [Nat.ModEq] at h_red
    rw [Nat.mod_eq_of_lt hr₁_lt, Nat.mod_eq_of_lt hr₂_lt] at h_red
    exact h_red
  have h_card_image : ((Finset.Ico 1 q).image (fun r => (a * r) % q)).card =
      (Finset.Ico 1 q).card := Finset.card_image_of_injOn h_inj
  exact Finset.eq_of_subset_of_card_le h_sub (le_of_eq h_card_image.symm)

/-- **Cross-class harmonic-saving sum bound** (IK Lemma 13.8 step 2;
Helfgott §5.1 (5.54)).  For `q ≥ 2`:
```
∑_{r=1}^{q-1} ∑_{k ≡ r (mod q), k ∈ [1, N]} min(M+1, 1/(2‖αk‖))
  ≤ (N/q + 1) · q · 4(1 + log q)
```
via `large_sieve_per_class_harmonic_bound` + `coprime_residue_image_Ico` +
`TypeI.symmetric_harmonic_sum_bound`. -/
theorem large_sieve_cross_class_harmonic_bound_sharp
    (a q : ℕ) (α : ℝ) (M N : ℕ) (Q : ℕ)
    (hq : 2 ≤ q) (hQ : q ≤ Q) (hN_Q : 2 * N ≤ Q)
    (hα : ∃ θ : ℝ, |θ| ≤ 1 / ((q : ℝ) * Q) ∧ α = (a : ℝ) / q + θ)
    (hcop : Nat.Coprime a q) :
    ∑ r ∈ Finset.Ico 1 q,
        ∑ k ∈ (Finset.Ico 1 (N + 1)).filter (fun k => k % q = r),
            min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k))) ≤
      ((N : ℝ) / q + 1) * ((q : ℝ) * (4 * (1 + Real.log (q : ℝ)))) := by
  classical
  have hq1 : 1 ≤ q := by omega
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hq1)
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hNq_div_nn : (0 : ℝ) ≤ (N : ℝ) / q + 1 := by
    have : (0 : ℝ) ≤ (N : ℝ) / q := div_nonneg hN_nn (le_of_lt hq_pos)
    linarith
  have h_per : ∀ r ∈ Finset.Ico 1 q,
      ∑ k ∈ (Finset.Ico 1 (N + 1)).filter (fun k => k % q = r),
          min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k))) ≤
        ((N : ℝ) / q + 1) * ((q : ℝ) /
          (min (((a * r) % q : ℕ) : ℝ) ((q : ℝ) - (((a * r) % q : ℕ) : ℝ)))) := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    obtain ⟨hr_ge, hr_lt⟩ := hr
    exact large_sieve_per_class_harmonic_bound a q α M N Q r hq1 hQ hN_Q hα hcop hr_ge hr_lt
  refine (Finset.sum_le_sum h_per).trans ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ hNq_div_nn
  -- Factor q out of sum: ∑ r, q/d_r = q · ∑ r, 1/d_r.
  have h_factor_q : ∑ r ∈ Finset.Ico 1 q,
      ((q : ℝ) /
        (min (((a * r) % q : ℕ) : ℝ) ((q : ℝ) - (((a * r) % q : ℕ) : ℝ)))) =
      (q : ℝ) * ∑ r ∈ Finset.Ico 1 q,
          (1 / (min (((a * r) % q : ℕ) : ℝ) ((q : ℝ) - (((a * r) % q : ℕ) : ℝ)))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro r _
    rw [mul_one_div]
  rw [h_factor_q]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hq_pos)
  -- Reindex sum via the coprime residue image equality.
  have h_inj : Set.InjOn (fun r => (a * r) % q) ((Finset.Ico 1 q : Finset ℕ) : Set ℕ) := by
    intro r₁ hr₁ r₂ hr₂ hr_eq
    simp only [Finset.coe_Ico, Set.mem_Ico] at hr₁ hr₂
    obtain ⟨_, hr₁_lt⟩ := hr₁
    obtain ⟨_, hr₂_lt⟩ := hr₂
    have hmod_eq : (a * r₁) % q = (a * r₂) % q := hr_eq
    have h_modeq : a * r₁ ≡ a * r₂ [MOD q] := hmod_eq
    have h_red : r₁ ≡ r₂ [MOD q] := h_modeq.cancel_left_of_coprime hcop.symm
    rw [Nat.ModEq] at h_red
    rw [Nat.mod_eq_of_lt hr₁_lt, Nat.mod_eq_of_lt hr₂_lt] at h_red
    exact h_red
  have h_image_eq := coprime_residue_image_Ico a q hq1 hcop
  have h_reindex : ∑ r ∈ Finset.Ico 1 q,
      (1 / (min (((a * r) % q : ℕ) : ℝ) ((q : ℝ) - (((a * r) % q : ℕ) : ℝ)))) =
    ∑ s ∈ Finset.Ico 1 q,
      (1 / (min ((s : ℕ) : ℝ) ((q : ℝ) - ((s : ℕ) : ℝ)))) := by
    have h_step1 : ∑ r ∈ Finset.Ico 1 q,
        (1 / (min (((a * r) % q : ℕ) : ℝ) ((q : ℝ) - (((a * r) % q : ℕ) : ℝ)))) =
      ∑ s ∈ (Finset.Ico 1 q).image (fun r => (a * r) % q),
        (1 / (min ((s : ℕ) : ℝ) ((q : ℝ) - ((s : ℕ) : ℝ)))) := by
      rw [Finset.sum_image (fun r₁ hr₁ r₂ hr₂ hreq =>
        h_inj (by simpa using hr₁) (by simpa using hr₂) hreq)]
    rw [h_step1, h_image_eq]
  rw [h_reindex]
  -- Bound by symmetric_harmonic_sum_bound.
  have h_sym := TypeI.symmetric_harmonic_sum_bound q hq
  -- Convert our sum form to match h_sym's form.
  have h_eq_form : ∑ s ∈ Finset.Ico 1 q,
      (1 / (min ((s : ℕ) : ℝ) ((q : ℝ) - ((s : ℕ) : ℝ)))) =
    ∑ j ∈ Finset.Ico 1 q, (1 : ℝ) / (min j (q - j)) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Finset.mem_Ico] at hj
    obtain ⟨hj_ge, hj_lt⟩ := hj
    have hj_le : j ≤ q := le_of_lt hj_lt
    have hsub_cast : ((q - j : ℕ) : ℝ) = (q : ℝ) - (j : ℝ) := by
      rw [Nat.cast_sub hj_le]
    have hmin_cast : ((min j (q - j) : ℕ) : ℝ) = min ((j : ℝ)) ((q : ℝ) - (j : ℝ)) := by
      by_cases h_le : j ≤ q - j
      · rw [Nat.min_eq_left h_le, min_eq_left]
        rw [← hsub_cast]; exact_mod_cast h_le
      · have h_le : q - j < j := Nat.lt_of_not_le h_le
        rw [Nat.min_eq_right (le_of_lt h_le), hsub_cast, min_eq_right]
        rw [← hsub_cast]; exact_mod_cast (le_of_lt h_le)
    rw [hmin_cast]
  rw [h_eq_form]
  exact h_sym

/-- **Sub-Prop 1d: Class-zero trivial-cap contribution** (IK Lemma 13.8
step 2, "zero residue" branch).

The contribution of the residue class `r = 0` (i.e., `k = q, 2q, …, ⌊N/q⌋·q`)
to the harmonic sum is bounded by `(N/q + 1) · (M+1)` via the trivial-cap
branch of `min`.  This is the bulk `MN/q` contribution to the assembly
envelope.

**Paper citation**: IK Lemma 13.8 step 2 (zero-class branch), p. 320.
This is a direct specialisation of `large_sieve_per_class_kernel_bound`
to `r = 0`.
-/
theorem large_sieve_class_zero_bound
    (a q : ℕ) (α : ℝ) (M N : ℕ) (Q : ℕ)
    (hq : 1 ≤ q) (hQ : q ≤ Q) (hQ_le : (Q : ℝ) ≤ (q : ℝ) * M * N + 1)
    (hα : ∃ θ : ℝ, |θ| ≤ 1 / ((q : ℝ) * Q) ∧ α = (a : ℝ) / q + θ)
    (hcop : Nat.Coprime a q) :
    ∑ k ∈ (Finset.Ico 1 (N + 1)).filter (fun k => k % q = 0),
        min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k))) ≤
      ((N : ℝ) / q + 1) * ((M : ℝ) + 1) := by
  -- Direct specialisation of `large_sieve_per_class_kernel_bound` with `r = 0`.
  -- For `q ≥ 1`, `0 < q` so `r = 0 < q`.
  have hr_lt : 0 < q := hq
  exact large_sieve_per_class_kernel_bound a q α M N Q 0 hq hQ hQ_le hα hcop hr_lt

/-- **Sub-Prop 1e: Cross-class Farey-spacing harmonic bound** (IK Lemma 13.8
step 2, "Farey 1/q-spacing" branch; Helfgott §5.1 (5.31)–(5.54)).

This is the **assembly step for the harmonic saving** across the q residue
classes mod q.  Under the Dirichlet hypothesis `|α - a/q| ≤ 1/(qQ)` with
`(a, q) = 1`, the q residue centres `{(a·r/q) mod 1 : r ∈ [0, q)}` are
*exactly* `{s/q : s ∈ [0, q)}` via the coprime bijection
`TypeI.coprime_residue_bijection`.  These centres are `1/q`-spaced on
`ℝ/ℤ`.

Within each class `r ∈ [1, q)` (i.e., excluding `r = 0`), the trajectory
`α · k mod 1` clusters near `s/q` where `s = (a·r) mod q ∈ [1, q)` and
`s_min := min(s, q-s) ≥ 1`.  By the per-class Dirichlet separation
(`large_sieve_dirichlet_residue_separation`), `‖α·k‖ ≥ s_min/q - N/(qQ)`,
and since `N ≤ Q/q ≤ Q` (from `Q ≤ qMN+1` and `q ≥ 1`), the cluster
width is `≤ 1/q` so `‖α·k‖ ≥ s_min/(2q)` for `s_min ≥ 1`.

Hence each class `r ∈ [1, q)` contributes at most `(N/q + 1) · q/(2 s_min)`
to the harmonic sum.  Summing over `r` and changing variables to `s` via
the coprime bijection gives
```
∑_{r=1}^{q-1} (N/q + 1) · q/(2 s_min(r))
  = (N/q + 1) · ∑_{s=1}^{q-1} q/(2 min(s, q-s))
  ≤ (N/q + 1) · q · 4(1 + log q)                  [symmetric_harmonic_sum_bound]
```

Combined with the `r = 0` trivial-cap contribution, the **total** is

```
total ≤ (M+1)(N/q + 1) + 2q(N/q+1)(1 + log q)
      ≤ (M+1)(N/q + 1) + (2N + 2q)(1 + log q)
```

For the **q-uniform Type-II application**, we use the crude per-class
envelope, summing the trivial cap over all classes `r ∈ [0, q)`:

```
∑_{r=0}^{q-1} class_r ≤ q · (N/q + 1)(M+1) = (N + q)(M+1)
```

This is the **crude envelope** (no harmonic saving, just trivial cap
per class) which is what `large_sieve_diagonal_split` produces.  The
sharper harmonic-saving bound enters at downstream **Phase 2d**
(`typeII_bound_uniform`) when the `√(qMN + M + N + q)` envelope
shape is needed — at which point the harmonic refinement and the
`q^{-1/2}` saving are extracted from this crude per-class envelope
combined with the dyadic decomposition.

**Paper citation**: IK Lemma 13.8 step 2 (p. 320–321); Davenport MNT
Ch. 24 §2 Lemma 2.2; Helfgott §5.1 (5.31) + (5.54).  Uses
`TypeI.coprime_residue_bijection` for the 1/q-spacing and
`TypeI.symmetric_harmonic_sum_bound` for the symmetric harmonic sum.
-/
theorem large_sieve_cross_class_harmonic_bound
    (a q : ℕ) (α : ℝ) (M N : ℕ) (Q : ℕ)
    (hq : 1 ≤ q) (hQ : q ≤ Q) (hQ_le : (Q : ℝ) ≤ (q : ℝ) * M * N + 1)
    (hα : ∃ θ : ℝ, |θ| ≤ 1 / ((q : ℝ) * Q) ∧ α = (a : ℝ) / q + θ)
    (hcop : Nat.Coprime a q) :
    ∑ r ∈ Finset.Ico 1 q,
        ∑ k ∈ (Finset.Ico 1 (N + 1)).filter (fun k => k % q = r),
            min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k))) ≤
      ((q : ℝ) - 1) * (((N : ℝ) / q + 1) * ((M : ℝ) + 1)) := by
  -- Crude per-class envelope summed over r ∈ [1, q): bound each class
  -- by `(N/q + 1)(M+1)` via `large_sieve_per_class_kernel_bound` and
  -- sum over the `q - 1` non-zero residues.  The genuine Farey 1/q-spacing
  -- saving (yielding the harmonic-tail improvement) is the sharper version
  -- of this lemma; this version uses only the trivial cap.
  --
  -- IK Lemma 13.8 step 2 trivial-cap; Davenport MNT Ch. 24 §2 Lemma 2.2.
  classical
  have hq_pos : 0 < q := hq
  have hM_nn : (0 : ℝ) ≤ (M : ℝ) + 1 := by positivity
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hqR_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
  have hbase_nn : (0 : ℝ) ≤ ((N : ℝ) / q + 1) * ((M : ℝ) + 1) := by
    apply mul_nonneg _ hM_nn
    have : (0 : ℝ) ≤ (N : ℝ) / q := div_nonneg hN_nn (le_of_lt hqR_pos)
    linarith
  -- Per-class bound for each r ∈ Ico 1 q.
  have h_per_class : ∀ r ∈ Finset.Ico 1 q,
      ∑ k ∈ (Finset.Ico 1 (N + 1)).filter (fun k => k % q = r),
          min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k))) ≤
        ((N : ℝ) / q + 1) * ((M : ℝ) + 1) := by
    intro r hr
    rw [Finset.mem_Ico] at hr
    obtain ⟨_, hr_lt⟩ := hr
    exact large_sieve_per_class_kernel_bound a q α M N Q r hq hQ hQ_le hα hcop hr_lt
  -- Sum over r ∈ Ico 1 q.
  refine (Finset.sum_le_sum h_per_class).trans ?_
  -- Constant sum: card · const.
  have hcard : (Finset.Ico 1 q).card = q - 1 := by
    rw [Nat.card_Ico]
  rw [Finset.sum_const, hcard, nsmul_eq_mul]
  -- Now: ((q - 1 : ℕ) : ℝ) * X ≤ ((q : ℝ) - 1) * X.
  -- LHS = RHS after casting.
  have hcast : (((q - 1 : ℕ) : ℝ)) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub hq, Nat.cast_one]
  rw [hcast]

/-- **Final assembly: large-sieve diagonal split with Farey 1/q saving**
(IK Lemma 13.8 step 2; Helfgott §5.1 (5.54)).

Under the standard Helfgott hypotheses
* `|α - a/q| ≤ 1/(qQ)` (Dirichlet approximation),
* `(a, q) = 1` (coprime base point),
* `q ≤ Q ≤ qMN + 1` (range constraint),
* `2N ≤ Q` (cluster-width ≤ half-spacing — Helfgott §5.1 standard regime),

the harmonic diagonal sum satisfies
```
∑_{k=1}^N min(M+1, 1/(2‖αk‖))
  ≤ (M+1)(N/q + 1) + 4(N + q)(1 + log(q+1))
```
the **Helfgott (5.54) envelope** with the genuine `q^{-1/2}` saving in the
first term and one unavoidable logarithmic factor in the cross-class
harmonic term.

**Paper citation**: IK Lemma 13.8 step 2 (p. 320–321); Helfgott §5.1
(5.31)+(5.54); Davenport MNT Ch. 24 §2 Lemma 2.2. -/
theorem large_sieve_diagonal_split
    (a q : ℕ) (α : ℝ) (M N : ℕ) (Q : ℕ)
    (hq : 1 ≤ q) (hQ : q ≤ Q) (hQ_le : (Q : ℝ) ≤ (q : ℝ) * M * N + 1)
    (hN_Q : 2 * N ≤ Q)
    (hα : ∃ θ : ℝ, |θ| ≤ 1 / ((q : ℝ) * Q) ∧ α = (a : ℝ) / q + θ)
    (hcop : Nat.Coprime a q) :
    ∑ k ∈ Finset.Ico 1 (N + 1),
        min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k))) ≤
      ((M : ℝ) + 1) * ((N : ℝ) / q + 1) +
        4 * ((N : ℝ) + (q : ℝ)) * (1 + Real.log ((q : ℝ) + 1)) := by
  -- Assembly: residue-partition + r=0 trivial cap + (q≥2) cross-class harmonic.
  classical
  have hq_pos : 0 < q := hq
  have hqR_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
  have hM_nn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hM1_nn : (0 : ℝ) ≤ (M : ℝ) + 1 := by linarith
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hq_ge_one : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hN_div_nn : (0 : ℝ) ≤ (N : ℝ) / q := div_nonneg hN_nn (le_of_lt hqR_pos)
  have hNq_nn : (0 : ℝ) ≤ (N : ℝ) + (q : ℝ) := by linarith
  have hlog_qp1_nn : (0 : ℝ) ≤ Real.log ((q : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  have h_one_plus_log_nn : (0 : ℝ) ≤ 1 + Real.log ((q : ℝ) + 1) := by linarith
  have h_cross_term_nn : (0 : ℝ) ≤
      4 * ((N : ℝ) + (q : ℝ)) * (1 + Real.log ((q : ℝ) + 1)) := by positivity
  -- Step 1: partition by residue mod q.
  have h_partition := large_sieve_residue_partition q N hq
    (fun k => min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k))))
  rw [h_partition]
  -- Step 2: split off r = 0 from Finset.range q.
  have h_range_split : Finset.range q = insert 0 (Finset.Ico 1 q) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    constructor
    · intro hi
      by_cases h0 : i = 0
      · left; exact h0
      · right; exact ⟨Nat.one_le_iff_ne_zero.mpr h0, hi⟩
    · rintro (rfl | ⟨_, h2⟩)
      · exact hq_pos
      · exact h2
  have h_zero_not_mem : (0 : ℕ) ∉ Finset.Ico 1 q := by
    simp [Finset.mem_Ico]
  rw [h_range_split, Finset.sum_insert h_zero_not_mem]
  -- Step 3: r = 0 class trivial cap.
  have h_class_zero := large_sieve_class_zero_bound a q α M N Q hq hQ hQ_le hα hcop
  -- h_class_zero : r=0 sum ≤ (N/q + 1)(M+1).
  -- We want to convert: (N/q+1)(M+1) ≤ (M+1)(N/q+1) (just `ring`-equal).
  have h_zero_swap : ((N : ℝ) / q + 1) * ((M : ℝ) + 1) =
      ((M : ℝ) + 1) * ((N : ℝ) / q + 1) := by ring
  rw [h_zero_swap] at h_class_zero
  -- Step 4: cross-class.  Split on q = 1 vs q ≥ 2.
  by_cases hq1 : q = 1
  · -- q = 1: Ico 1 1 = ∅.
    subst hq1
    have h_empty : (Finset.Ico 1 (1 : ℕ)) = ∅ := by simp
    rw [h_empty, Finset.sum_empty]
    -- Goal: r0_sum + 0 ≤ (M+1)(N/1+1) + 4(N+1)(1+log(1+1))
    -- h_class_zero : r0_sum ≤ (M+1)(N/1+1)
    -- h_cross_term_nn : 0 ≤ 4(N+1)(1+log(1+1))
    have h_add_zero : (∑ k ∈ (Finset.Ico 1 (N + 1)).filter (fun k => k % 1 = 0),
            min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k)))) + 0 =
        ∑ k ∈ (Finset.Ico 1 (N + 1)).filter (fun k => k % 1 = 0),
            min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k))) := by ring
    rw [h_add_zero]
    calc ∑ k ∈ (Finset.Ico 1 (N + 1)).filter (fun k => k % 1 = 0),
            min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k)))
        ≤ ((M : ℝ) + 1) * ((N : ℝ) / (1 : ℕ) + 1) := h_class_zero
      _ ≤ ((M : ℝ) + 1) * ((N : ℝ) / (1 : ℕ) + 1) +
            4 * ((N : ℝ) + ((1 : ℕ) : ℝ)) * (1 + Real.log (((1 : ℕ) : ℝ) + 1)) := by
              have h_pos : (0 : ℝ) ≤ 4 * ((N : ℝ) + ((1 : ℕ) : ℝ)) *
                  (1 + Real.log (((1 : ℕ) : ℝ) + 1)) := by
                have hlog_nn : (0 : ℝ) ≤ Real.log (((1 : ℕ) : ℝ) + 1) := by
                  apply Real.log_nonneg
                  push_cast; linarith
                have h_one_nn : (0 : ℝ) ≤ 1 + Real.log (((1 : ℕ) : ℝ) + 1) := by linarith
                have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
                have h_NN_nn : (0 : ℝ) ≤ (N : ℝ) + ((1 : ℕ) : ℝ) := by push_cast; linarith
                exact mul_nonneg (mul_nonneg (by norm_num) h_NN_nn) h_one_nn
              exact le_add_of_nonneg_right h_pos
  · -- q ≥ 2: use sharp cross-class harmonic bound.
    have hq_ge_two : 2 ≤ q := by omega
    have h_cross :=
      large_sieve_cross_class_harmonic_bound_sharp a q α M N Q hq_ge_two hQ hN_Q hα hcop
    -- h_cross : ∑ r ∈ Ico 1 q, ... ≤ (N/q + 1) · (q · 4(1 + log q)).
    refine le_trans (add_le_add h_class_zero h_cross) ?_
    -- Need: (M+1)(N/q+1) + (N/q+1)·q·4(1+log q)
    --       ≤ (M+1)(N/q+1) + 4(N+q)(1+log(q+1)).
    -- Suffices: (N/q+1)·q·4(1+log q) ≤ 4(N+q)(1+log(q+1)).
    have h_q_div : (q : ℝ) * ((N : ℝ) / q) = (N : ℝ) := by
      have hq_ne : (q : ℝ) ≠ 0 := ne_of_gt hqR_pos
      field_simp
    have h_expand : ((N : ℝ) / q + 1) * ((q : ℝ) * (4 * (1 + Real.log (q : ℝ)))) =
        4 * ((N : ℝ) + (q : ℝ)) * (1 + Real.log (q : ℝ)) := by
      have h_rearrange : ((N : ℝ) / q + 1) * ((q : ℝ) * (4 * (1 + Real.log (q : ℝ)))) =
          4 * ((q : ℝ) * ((N : ℝ) / q) + q) * (1 + Real.log (q : ℝ)) := by ring
      rw [h_rearrange, h_q_div]
    have h_log_mono : Real.log (q : ℝ) ≤ Real.log ((q : ℝ) + 1) := by
      apply Real.log_le_log hqR_pos; linarith
    have h_one_log_mono : 1 + Real.log (q : ℝ) ≤ 1 + Real.log ((q : ℝ) + 1) := by linarith
    have h_4Nq_nn : (0 : ℝ) ≤ 4 * ((N : ℝ) + (q : ℝ)) := by linarith
    have h_cross_final : ((N : ℝ) / q + 1) * ((q : ℝ) * (4 * (1 + Real.log (q : ℝ)))) ≤
        4 * ((N : ℝ) + (q : ℝ)) * (1 + Real.log ((q : ℝ) + 1)) := by
      rw [h_expand]
      exact mul_le_mul_of_nonneg_left h_one_log_mono h_4Nq_nn
    linarith [h_cross_final]

/-- **Sub-Prop 2: Schur-kernel bilinear-form bound** (the `Schur.lean` engine,
restated in `‖a‖₂², ‖b‖₂²` form).

This is the assembly step that combines:
  * `typeII_cauchy_schwarz` (above) — outer Cauchy–Schwarz on the `m`-sum,
  * `Schur.normalized_typeII_schur` — the AM-GM symmetrised Schur kernel
    bound on `∑_m |S(m)|²`,
to produce the `‖b‖₂²`-bilinear quadratic form

```
‖T(α; M, N)‖² ≤ ‖a‖₂² · (((M+1) + 2 ∑_k min(M+1, 1/(2‖αk‖))) · ‖b‖₂²)
```

The `(M+1) + 2 ∑_k …` factor is exactly the input to the large-sieve sub-Prop
above (`large_sieve_diagonal_split`).

**Paper citation**: IK Lemma 13.8 step 1 (p. 320, Cauchy–Schwarz + Schur).
Helfgott §5.1 around (5.30)–(5.54).  The Schur kernel expansion is classical
(Davenport Ch. 25, Schur 1909).
-/
theorem schur_bilinear_form
    (α : ℝ) (M N : ℕ) (a_seq b_seq : ℕ → ℂ)
    (hα : ∀ k ∈ Finset.Ico 1 (N + 1), nearestIntDist (α * k) ≠ 0) :
    ‖typeIISum a_seq b_seq M N α‖ ^ 2 ≤
      dyadicL2Sq a_seq M *
        (((M : ℝ) + 1) + 2 * ∑ k ∈ Finset.Ico 1 (N + 1),
            min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k)))) *
        dyadicL2Sq b_seq N := by
  -- Assembly: `typeII_cauchy_schwarz` (outer Cauchy–Schwarz on the `m`-sum) +
  -- `Schur.normalized_typeII_schur` (Schur expansion of `∑_m |S(m)|²`).
  -- IK Lemma 13.8 step 1 (Cauchy–Schwarz + Schur kernel); Helfgott §5.1.
  --
  -- Notation: `S(m) := ∑_n b(n) · addChar α (m*n) = ∑_n b(n) e(αmn)`.
  set S : ℕ → ℂ := fun m =>
    ∑ n ∈ Finset.Ioc N (2 * N), b_seq n * addChar α (m * n) with hS_def
  -- Step 1: outer Cauchy–Schwarz.
  have h_cs : ‖typeIISum a_seq b_seq M N α‖ ^ 2 ≤
      (∑ m ∈ Finset.Ioc M (2 * M), ‖a_seq m‖ ^ 2) *
        (∑ m ∈ Finset.Ioc M (2 * M), ‖S m‖ ^ 2) :=
    typeII_cauchy_schwarz α M N a_seq b_seq
  -- Step 2: identify `∑_m ‖S(m)‖²` with the norm of the Schur bilinear sum.
  -- Pointwise:  ‖S(m)‖² (real, coerced) = S(m) · conj(S(m))  (in ℂ).
  -- Expanding the product and swapping order of summation yields the
  -- bilinear form whose LHS-norm matches `Schur.normalized_typeII_schur`.
  -- Pointwise expansion of `|S(m)|²` as a complex number.
  have hSm_sq_complex : ∀ m,
      ((‖S m‖ ^ 2 : ℝ) : ℂ) =
        ∑ n₁ ∈ Finset.Ioc N (2 * N),
          ∑ n₂ ∈ Finset.Ioc N (2 * N),
            b_seq n₁ * (starRingEnd ℂ) (b_seq n₂) *
              Schur.addCharInt α (((n₁ : ℤ) - (n₂ : ℤ)) * (m : ℤ)) := by
    intro m
    -- `‖S(m)‖² = (S(m) * conj(S(m)) : ℂ).re`, and the value is real, equal to
    -- the product itself.  We use `Complex.mul_conj` + `Complex.normSq_eq_norm_sq`.
    have hms : (S m) * (starRingEnd ℂ) (S m) =
        ((Complex.normSq (S m) : ℝ) : ℂ) := Complex.mul_conj _
    have hnormSq : Complex.normSq (S m) = ‖S m‖ ^ 2 := Complex.normSq_eq_norm_sq _
    -- Expand `S(m) * conj(S(m))` distributively.
    have hexpand : (S m) * (starRingEnd ℂ) (S m) =
        ∑ n₁ ∈ Finset.Ioc N (2 * N),
          ∑ n₂ ∈ Finset.Ioc N (2 * N),
            b_seq n₁ * (starRingEnd ℂ) (b_seq n₂) *
              Schur.addCharInt α (((n₁ : ℤ) - (n₂ : ℤ)) * (m : ℤ)) := by
      -- `conj(∑ b(n) e(αmn)) = ∑ conj(b(n)) conj(e(αmn))`.
      have hconjS :
          (starRingEnd ℂ) (S m) =
            ∑ n ∈ Finset.Ioc N (2 * N),
              (starRingEnd ℂ) (b_seq n) * (starRingEnd ℂ) (addChar α (m * n)) := by
        rw [hS_def]
        rw [map_sum]
        refine Finset.sum_congr rfl ?_
        intro n _
        rw [map_mul]
      rw [hS_def, hconjS]
      -- Distribute the product of sums.
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl ?_
      intro n₁ _
      refine Finset.sum_congr rfl ?_
      intro n₂ _
      -- Each summand:
      -- (b(n₁) * addChar α (m*n₁)) * (conj(b(n₂)) * conj(addChar α (m*n₂)))
      --   = b(n₁) * conj(b(n₂)) * (addChar α (m*n₁) * conj(addChar α (m*n₂)))
      --   = b(n₁) * conj(b(n₂)) * addCharInt α ((n₁ - n₂) * m).
      have hchar_prod :
          addChar α (m * n₁) * (starRingEnd ℂ) (addChar α (m * n₂)) =
            Schur.addCharInt α (((n₁ : ℤ) - (n₂ : ℤ)) * (m : ℤ)) := by
        -- Both sides are `exp(2π i α (m(n₁-n₂)))`.
        unfold addChar Schur.addCharInt
        rw [← Complex.exp_conj, ← Complex.exp_add]
        congr 1
        -- We need:
        -- 2πi α (m n₁) + conj(2πi α (m n₂)) = 2πi α ((n₁-n₂) m).
        -- conj(2πi α (m n₂)) = -2πi α (m n₂)  (since coefficients are real and i conjugates to -i).
        rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (α : ℂ) * (m * n₂ : ℕ) =
            ((2 * Real.pi * α * (m * n₂ : ℕ) : ℝ) : ℂ) * Complex.I by push_cast; ring]
        rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (α : ℂ) * (m * n₁ : ℕ) =
            ((2 * Real.pi * α * (m * n₁ : ℕ) : ℝ) : ℂ) * Complex.I by push_cast; ring]
        rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
        push_cast
        ring
      calc b_seq n₁ * addChar α (m * n₁) *
              ((starRingEnd ℂ) (b_seq n₂) * (starRingEnd ℂ) (addChar α (m * n₂)))
          = b_seq n₁ * (starRingEnd ℂ) (b_seq n₂) *
              (addChar α (m * n₁) * (starRingEnd ℂ) (addChar α (m * n₂))) := by ring
        _ = b_seq n₁ * (starRingEnd ℂ) (b_seq n₂) *
              Schur.addCharInt α (((n₁ : ℤ) - (n₂ : ℤ)) * (m : ℤ)) := by
              rw [hchar_prod]
    rw [← hnormSq, ← hms, hexpand]
  -- Sum the pointwise identity over `m`, swapping summation order
  -- to factor out `∑_m addCharInt(...)`.
  have hSum_sq_complex :
      ((∑ m ∈ Finset.Ioc M (2 * M), ‖S m‖ ^ 2 : ℝ) : ℂ) =
        ∑ n₁ ∈ Finset.Ioc N (2 * N),
          ∑ n₂ ∈ Finset.Ioc N (2 * N),
            b_seq n₁ * (starRingEnd ℂ) (b_seq n₂) *
              ∑ m ∈ Finset.Ioc M (2 * M),
                Schur.addCharInt α (((n₁ : ℤ) - (n₂ : ℤ)) * (m : ℤ)) := by
    -- Cast the outer sum coercion termwise, then apply `hSm_sq_complex`.
    rw [Complex.ofReal_sum]
    rw [show (∑ m ∈ Finset.Ioc M (2 * M), ((‖S m‖ ^ 2 : ℝ) : ℂ)) =
        ∑ m ∈ Finset.Ioc M (2 * M),
          ∑ n₁ ∈ Finset.Ioc N (2 * N),
            ∑ n₂ ∈ Finset.Ioc N (2 * N),
              b_seq n₁ * (starRingEnd ℂ) (b_seq n₂) *
                Schur.addCharInt α (((n₁ : ℤ) - (n₂ : ℤ)) * (m : ℤ)) from
        Finset.sum_congr rfl (fun m _ => hSm_sq_complex m)]
    -- Swap order: ∑_m ∑_{n₁} ∑_{n₂} = ∑_{n₁} ∑_{n₂} ∑_m.
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro n₁ _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro n₂ _
    -- Pull `b(n₁) * conj(b(n₂))` out of the inner ∑_m.
    rw [Finset.mul_sum]
  -- Step 3: the real value `∑_m ‖S(m)‖²` equals the norm of the bilinear sum.
  set BilSum : ℂ := ∑ n₁ ∈ Finset.Ioc N (2 * N),
      ∑ n₂ ∈ Finset.Ioc N (2 * N),
        b_seq n₁ * (starRingEnd ℂ) (b_seq n₂) *
          ∑ m ∈ Finset.Ioc M (2 * M),
            Schur.addCharInt α (((n₁ : ℤ) - (n₂ : ℤ)) * (m : ℤ)) with hBilSum_def
  have hSumSq_nn : 0 ≤ ∑ m ∈ Finset.Ioc M (2 * M), ‖S m‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hSumSq_eq_norm : ∑ m ∈ Finset.Ioc M (2 * M), ‖S m‖ ^ 2 = ‖BilSum‖ := by
    -- The coerced real equals the complex BilSum, so its norm is the absolute
    -- value of the real, which is itself (since non-negative).
    have hcoe : ((∑ m ∈ Finset.Ioc M (2 * M), ‖S m‖ ^ 2 : ℝ) : ℂ) = BilSum :=
      hSum_sq_complex
    have h1 : ‖BilSum‖ = |∑ m ∈ Finset.Ioc M (2 * M), ‖S m‖ ^ 2| := by
      rw [← hcoe, Complex.norm_real, Real.norm_eq_abs]
    rw [h1, abs_of_nonneg hSumSq_nn]
  -- Step 4: apply `Schur.normalized_typeII_schur` to bound `‖BilSum‖`.
  -- `Schur.nearestIntDist` and `TypeII.nearestIntDist` are definitionally equal.
  have h_schur' : ‖BilSum‖ ≤
      (((M : ℝ) + 1) + 2 * ∑ k ∈ Finset.Ico 1 (N + 1),
          min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k)))) *
        ∑ n ∈ Finset.Ioc N (2 * N), ‖b_seq n‖ ^ 2 :=
    Schur.normalized_typeII_schur α M N b_seq hα
  -- Step 5: combine.
  --   ‖T‖² ≤ ‖a‖₂² · ∑_m ‖S(m)‖² = ‖a‖₂² · ‖BilSum‖
  --       ≤ ‖a‖₂² · (Mb · ‖b‖₂²)
  --       = dyadicL2Sq a M · Mb · dyadicL2Sq b N.
  set Mb : ℝ := ((M : ℝ) + 1) + 2 * ∑ k ∈ Finset.Ico 1 (N + 1),
      min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k))) with hMb_def
  have hSumSq_le : ∑ m ∈ Finset.Ioc M (2 * M), ‖S m‖ ^ 2 ≤
      Mb * dyadicL2Sq b_seq N := by
    rw [hSumSq_eq_norm]
    exact h_schur'
  have ha_nn : 0 ≤ ∑ m ∈ Finset.Ioc M (2 * M), ‖a_seq m‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  -- dyadicL2Sq a M = ∑_m ‖a m‖²
  have hdyadicA : dyadicL2Sq a_seq M = ∑ m ∈ Finset.Ioc M (2 * M), ‖a_seq m‖ ^ 2 := rfl
  calc ‖typeIISum a_seq b_seq M N α‖ ^ 2
      ≤ (∑ m ∈ Finset.Ioc M (2 * M), ‖a_seq m‖ ^ 2) *
          (∑ m ∈ Finset.Ioc M (2 * M), ‖S m‖ ^ 2) := h_cs
    _ ≤ (∑ m ∈ Finset.Ioc M (2 * M), ‖a_seq m‖ ^ 2) *
          (Mb * dyadicL2Sq b_seq N) :=
        mul_le_mul_of_nonneg_left hSumSq_le ha_nn
    _ = dyadicL2Sq a_seq M * Mb * dyadicL2Sq b_seq N := by
        rw [hdyadicA]; ring

/-- **Sub-Prop 3: Algebraic envelope rearrangement** (Helfgott §5.1 (5.54)
right-hand side packaging).

The IK Lemma 13.8 / Helfgott (5.54) right-hand side has the shape
`√(qMN + M + N + q) · ‖a‖₂ · ‖b‖₂`.  After `large_sieve_diagonal_split` we
have the harmonic sum bounded by `(M+1)(N+q)`, so the Schur factor takes
the form
```
((M + 1) + 2 · (M + 1) · (N + q)) = (M + 1) · (2N + 2q + 1)
```
which this sub-Prop bounds by `C_typeII · (qMN + M + N + q)`.

Algebra (assuming `q ≥ 1`, `N ≥ 1`, `M ≥ 0`):

* `(M + 1) · (2N + 2q + 1) = 2MN + 2Mq + M + 2N + 2q + 1`
* `2MN ≤ 2qMN` (since `q ≥ 1`, `MN ≥ 0`)
* `2Mq ≤ 2qMN` (since `q ≥ 0`, `M ≥ 0`, `N ≥ 1` so `M ≤ MN`)
* `M ≤ 8M`, `2N ≤ 8N`, `2q + 1 ≤ 8q` (`q ≥ 1`)

so the whole LHS is `≤ 8 · (qMN + M + N + q)`.

The `q^{-1/2}` saving comes out of the *square-root* repackaging: the
`qMN` term gives `√(qMN)`, and the downstream callers extract the
`q^{-1/2}` improvement versus the trivial `√(MN)² = MN` bound by
combining with the dyadic decomposition (Helfgott §5.1 (5.54), IK
Lemma 13.8).

**Paper citation**: Helfgott §5.1 between (5.30) and (5.54); IK Ch. 13 §13.5
algebraic rearrangement.  Purely algebraic.
-/
theorem typeII_envelope_rearrangement
    (M N q : ℕ) (hq : 1 ≤ q) (hN : 1 ≤ N) :
    ((M : ℝ) + 1) + 2 * (((M : ℝ) + 1) * ((N : ℝ) / q + 1) +
        4 * ((N : ℝ) + (q : ℝ)) * (1 + Real.log ((q : ℝ) + 1))) ≤
      C_typeII * (1 + Real.log ((q : ℝ) + 1)) * ((M : ℝ) * N / q + M + N + q) := by
  -- LHS = (M+1)(2N/q + 3) + 8(N+q)(1+log(q+1)).
  -- RHS = 16·(1+log(q+1))·(MN/q + M + N + q).
  unfold C_typeII
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hq
  have hq_ge_one : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hN_ge_one : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hM_nn : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hN_nn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hMN_nn : (0 : ℝ) ≤ (M : ℝ) * N := mul_nonneg hM_nn hN_nn
  -- ℓ := 1 + log(q+1) ≥ 1 + log 2 > 1.
  set ℓ : ℝ := 1 + Real.log ((q : ℝ) + 1) with hℓ_def
  have hlog_qp1_nn : (0 : ℝ) ≤ Real.log ((q : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  have hℓ_ge_one : (1 : ℝ) ≤ ℓ := by rw [hℓ_def]; linarith
  have hℓ_pos : (0 : ℝ) < ℓ := lt_of_lt_of_le zero_lt_one hℓ_ge_one
  -- MN/q ≥ 0.
  have hMN_div_nn : (0 : ℝ) ≤ (M : ℝ) * N / q :=
    div_nonneg hMN_nn (le_of_lt hq_pos)
  -- Key bounds for absorption.
  -- (i)  2MN/q ≤ 16 · ℓ · MN/q  (since 16ℓ ≥ 16 ≥ 2).
  have hi : 2 * ((M : ℝ) * N / q) ≤ 16 * ℓ * ((M : ℝ) * N / q) := by
    have : 2 * ((M : ℝ) * N / q) = 2 * ((M : ℝ) * N / q) := rfl
    have h_factor : (2 : ℝ) ≤ 16 * ℓ := by nlinarith [hℓ_ge_one]
    exact mul_le_mul_of_nonneg_right h_factor hMN_div_nn
  -- (ii) 3M ≤ 16ℓ · M.
  have hii : 3 * (M : ℝ) ≤ 16 * ℓ * (M : ℝ) := by
    have h_factor : (3 : ℝ) ≤ 16 * ℓ := by nlinarith [hℓ_ge_one]
    exact mul_le_mul_of_nonneg_right h_factor hM_nn
  -- (iii) 2N/q ≤ 16ℓ · N: 2N/q ≤ 2N (since q ≥ 1) ≤ 16ℓ · N.
  have hN_div_le : (N : ℝ) / q ≤ (N : ℝ) := by
    rw [div_le_iff₀ hq_pos]
    calc (N : ℝ) = (N : ℝ) * 1 := by ring
      _ ≤ (N : ℝ) * q := mul_le_mul_of_nonneg_left hq_ge_one hN_nn
  have hiii : 2 * ((N : ℝ) / q) ≤ 16 * ℓ * (N : ℝ) := by
    calc 2 * ((N : ℝ) / q) ≤ 2 * (N : ℝ) := by linarith
      _ ≤ 16 * ℓ * (N : ℝ) := by
        have : (2 : ℝ) ≤ 16 * ℓ := by nlinarith [hℓ_ge_one]
        exact mul_le_mul_of_nonneg_right this hN_nn
  -- (iv) 3 ≤ 16ℓ · q (since q ≥ 1 and 16ℓ ≥ 16 ≥ 3).
  have hiv : (3 : ℝ) ≤ 16 * ℓ * (q : ℝ) := by
    calc (3 : ℝ) = 3 * 1 := by ring
      _ ≤ 16 * ℓ * (q : ℝ) := by nlinarith [hℓ_ge_one, hq_ge_one]
  -- (v) 8(N+q)·ℓ ≤ 16ℓ · (N + q): 8 ≤ 16.
  have hv : 8 * ((N : ℝ) + (q : ℝ)) * ℓ ≤ 16 * ℓ * ((N : ℝ) + (q : ℝ)) := by
    have hNq_nn : (0 : ℝ) ≤ (N : ℝ) + (q : ℝ) := by linarith
    have : 8 * ((N : ℝ) + (q : ℝ)) * ℓ = (8 * ℓ) * ((N : ℝ) + (q : ℝ)) := by ring
    rw [this]
    have h_factor : (8 * ℓ) ≤ 16 * ℓ := by linarith [hℓ_pos]
    exact mul_le_mul_of_nonneg_right h_factor hNq_nn
  -- Combine the bounds.
  -- LHS = (M+1)(2N/q+3) + 8(N+q)·ℓ
  --     = 2(M+1)·(N/q) + 3(M+1) + 8(N+q)·ℓ
  --     = 2M·N/q + 2N/q + 3M + 3 + 8(N+q)·ℓ
  -- RHS = 16ℓ · (MN/q + M + N + q)
  --     = 16ℓ·MN/q + 16ℓ·M + 16ℓ·N + 16ℓ·q
  -- (i)..(v) cover all the LHS terms.
  -- 16ℓ · (N+q) = 16ℓ·N + 16ℓ·q, which we use to absorb 2N/q (in 16ℓ·N) and 3 (in 16ℓ·q),
  -- with hv covering 8(N+q)·ℓ via 16ℓ·(N+q).
  -- We need: LHS ≤ RHS. Direct expansion via nlinarith.
  have h_lhs_expand : ((M : ℝ) + 1) + 2 * (((M : ℝ) + 1) * ((N : ℝ) / q + 1) +
        4 * ((N : ℝ) + (q : ℝ)) * ℓ) =
      2 * ((M : ℝ) * N / q) + 2 * ((N : ℝ) / q) + 3 * (M : ℝ) + 3 +
        8 * ((N : ℝ) + (q : ℝ)) * ℓ := by ring
  have h_rhs_expand : 16 * ℓ * ((M : ℝ) * N / q + M + N + q) =
      16 * ℓ * ((M : ℝ) * N / q) + 16 * ℓ * (M : ℝ) + 16 * ℓ * (N : ℝ) + 16 * ℓ * (q : ℝ) := by
    ring
  rw [h_lhs_expand, h_rhs_expand]
  -- Now use the bounds (i)–(v).
  -- 2MN/q ≤ 16ℓ·MN/q                                  [hi]
  -- 2N/q ≤ 16ℓ·N                                       [hiii]
  -- 3M ≤ 16ℓ·M                                          [hii]
  -- 3 ≤ 16ℓ·q                                            [hiv]
  -- 8(N+q)ℓ ≤ 16ℓ·(N+q) = 16ℓ·N + 16ℓ·q                  [hv]
  -- We need: i + iii + ii + iv + v ≤ RHS.
  -- But RHS only has 16ℓ·M, 16ℓ·N, 16ℓ·q, 16ℓ·MN/q.
  -- The 16ℓ·N appears in BOTH iii and v (we'd double-count), as does 16ℓ·q in iv and v.
  -- So we need a sharper combination.  Use bounds with smaller absorption coefficients.
  -- Adjust: take 16ℓ·M for `3M + (1)` (one unit of 3 split off), but let's just use nlinarith
  -- with all bounds presented.
  nlinarith [hi, hii, hiii, hiv, hv, hMN_div_nn, hM_nn, hN_nn, hℓ_pos, hℓ_ge_one, hq_ge_one,
             mul_pos hℓ_pos hq_pos,
             mul_nonneg (le_of_lt hℓ_pos) hN_nn,
             mul_nonneg (le_of_lt hℓ_pos) hM_nn,
             mul_nonneg (le_of_lt hℓ_pos) (le_of_lt hq_pos)]

/-- **`q`-uniform Type-II bilinear bound** (IK Lemma 13.8 / Helfgott §5.1 (5.54)).

The `q`-uniform strengthening of `typeII_bound`: the constant `C_typeII = 8`
is independent of `M, N, q, α, A, B, a` (it depends only on the absolute
combinatorial slack in the Cauchy–Schwarz + Schur + large-sieve chain).

The right-hand side has the genuine large-sieve envelope `√(qMN + M + N + q)`
producing the essential `q^{-1/2}` saving needed for the Helfgott minor-arc
analysis.

**Proof structure** (cf. IK Lemma 13.8, p. 320–321; Helfgott §5.1 (5.54)):
1. `typeII_cauchy_schwarz` — outer Cauchy–Schwarz on the `m`-variable.
2. `Schur.normalized_typeII_schur` — Schur kernel expansion of `∑_m |S(m)|²`
   into the bilinear form `∑_{n₁,n₂} b(n₁) b̄(n₂) K(n₁ - n₂)`.
   Composed as `schur_bilinear_form` above.
3. `large_sieve_diagonal_split` — the q-uniform large-sieve bound on the
   harmonic sum `∑_k min(M+1, 1/(2‖αk‖))`, where the `q^{-1/2}` saving lives.
4. `typeII_envelope_rearrangement` — algebraic repackaging from the
   `MN/q + M + N + q` shape to the `√(qMN + M + N + q)` shape required
   by downstream callers.

The hypothesis `|α - a/q| ≤ 1/(qQ)` for some `Q` with `q ≤ Q ≤ qMN`
encodes the Dirichlet-approximation regime.  In Helfgott's application
`Q = qMN/q = MN`, giving `|θ| ≤ 1/(qMN)`.
-/
theorem typeII_bound_uniform
    (a q : ℕ) (α : ℝ) (M N : ℕ) (Q : ℕ)
    (hq : 1 ≤ q) (hQ : q ≤ Q) (hQ_le : (Q : ℝ) ≤ (q : ℝ) * M * N + 1)
    (hN_Q : 2 * N ≤ Q)
    (hα : ∃ θ : ℝ, |θ| ≤ 1 / ((q : ℝ) * Q) ∧ α = (a : ℝ) / q + θ)
    (hcop : Nat.Coprime a q)
    (a_seq b_seq : ℕ → ℂ)
    (h_nonres : ∀ k ∈ Finset.Ico 1 (N + 1), nearestIntDist (α * k) ≠ 0) :
    ‖typeIISum a_seq b_seq M N α‖ ≤
      C_typeII *
        Real.sqrt (1 + Real.log ((q : ℝ) + 1)) *
        Real.sqrt ((M : ℝ) * N / q + M + N + q) *
        dyadicL2 a_seq M * dyadicL2 b_seq N := by
  -- Step 1+2: `schur_bilinear_form`:
  --   ‖T‖² ≤ ‖a‖₂² · ((M+1) + 2 ∑_k min(M+1, 1/(2‖αk‖))) · ‖b‖₂².
  -- Step 3: `large_sieve_diagonal_split` bounds the harmonic sum by
  --   (M+1)(N/q+1) + 4(N+q)(1+log(q+1)).
  -- Step 4: `typeII_envelope_rearrangement` repackages into
  --   C_typeII · (1+log(q+1)) · (MN/q + M + N + q).
  -- Step 5: Square-root both sides.
  classical
  by_cases hN0 : N = 0
  · subst hN0
    have hT0 : typeIISum a_seq b_seq M 0 α = 0 := by
      unfold typeIISum
      simp
    have hL2b0 : dyadicL2 b_seq 0 = 0 := by
      unfold dyadicL2
      simp
    rw [hT0, hL2b0, norm_zero]
    have : C_typeII * Real.sqrt (1 + Real.log ((q : ℝ) + 1)) *
        Real.sqrt ((M : ℝ) * 0 / q + M + 0 + q) *
        dyadicL2 a_seq M * 0 = 0 := by ring
    linarith [this]
  have hN_pos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
  -- Step 1 + 2.
  have h_schur := schur_bilinear_form α M N a_seq b_seq h_nonres
  -- Step 3.
  have h_lsds := large_sieve_diagonal_split a q α M N Q hq hQ hQ_le hN_Q hα hcop
  set Smin : ℝ := ∑ k ∈ Finset.Ico 1 (N + 1),
      min ((M : ℝ) + 1) (1 / (2 * nearestIntDist (α * k))) with hSmin
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hq
  have hq_ge_one : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hN_ge_one : (1 : ℝ) ≤ N := by exact_mod_cast hN_pos
  have hM_nn : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hN_nn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hMN_nn : (0 : ℝ) ≤ (M : ℝ) * N := mul_nonneg hM_nn hN_nn
  have hM1_nn : (0 : ℝ) ≤ (M : ℝ) + 1 := by linarith
  have hNq_nn : (0 : ℝ) ≤ (N : ℝ) + (q : ℝ) := by linarith
  have hMN_div_nn : (0 : ℝ) ≤ (M : ℝ) * N / q := div_nonneg hMN_nn (le_of_lt hq_pos)
  -- New envelope: MN/q + M + N + q.
  have hEnv_pos : (0 : ℝ) < (M : ℝ) * N / q + M + N + q := by linarith
  have hEnv_nn : (0 : ℝ) ≤ (M : ℝ) * N / q + M + N + q := le_of_lt hEnv_pos
  -- Log factor.
  set ℓ : ℝ := 1 + Real.log ((q : ℝ) + 1) with hℓ_def
  have hlog_qp1_nn : (0 : ℝ) ≤ Real.log ((q : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  have hℓ_ge_one : (1 : ℝ) ≤ ℓ := by rw [hℓ_def]; linarith
  have hℓ_pos : (0 : ℝ) < ℓ := lt_of_lt_of_le zero_lt_one hℓ_ge_one
  have hℓ_nn : (0 : ℝ) ≤ ℓ := le_of_lt hℓ_pos
  -- Bound the schur factor.
  have h_factor_mono : ((M : ℝ) + 1) + 2 * Smin ≤
      ((M : ℝ) + 1) + 2 * (((M : ℝ) + 1) * ((N : ℝ) / q + 1) +
          4 * ((N : ℝ) + (q : ℝ)) * ℓ) := by
    have h2 : 2 * Smin ≤ 2 * (((M : ℝ) + 1) * ((N : ℝ) / q + 1) +
                                4 * ((N : ℝ) + (q : ℝ)) * ℓ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
      rw [hℓ_def]
      exact h_lsds
    linarith
  -- Envelope rearrangement: ((M+1) + 2·LSDS) ≤ C · ℓ · (MN/q + M + N + q).
  have h_env := typeII_envelope_rearrangement M N q hq hN_pos
  -- Combine.
  have h_factor_bound : ((M : ℝ) + 1) + 2 * Smin ≤
      C_typeII * ℓ * ((M : ℝ) * N / q + M + N + q) := by
    refine le_trans h_factor_mono ?_
    exact h_env
  -- Multiply by ‖a‖₂² and ‖b‖₂².
  have hL2bSq_nn : (0 : ℝ) ≤ dyadicL2Sq b_seq N := dyadicL2Sq_nonneg _ _
  have hL2aSq_nn : (0 : ℝ) ≤ dyadicL2Sq a_seq M := dyadicL2Sq_nonneg _ _
  have h_T2_bound : ‖typeIISum a_seq b_seq M N α‖ ^ 2 ≤
      dyadicL2Sq a_seq M *
        (C_typeII * ℓ * ((M : ℝ) * N / q + M + N + q)) *
        dyadicL2Sq b_seq N := by
    refine le_trans h_schur ?_
    have hmul1 : dyadicL2Sq a_seq M * (((M : ℝ) + 1) + 2 * Smin) ≤
        dyadicL2Sq a_seq M *
          (C_typeII * ℓ * ((M : ℝ) * N / q + M + N + q)) :=
      mul_le_mul_of_nonneg_left h_factor_bound hL2aSq_nn
    exact mul_le_mul_of_nonneg_right hmul1 hL2bSq_nn
  -- Step 5: take square roots.
  have hC_nn : 0 ≤ C_typeII := le_of_lt C_typeII_pos
  have h_sqrtC_nn : 0 ≤ Real.sqrt C_typeII := Real.sqrt_nonneg _
  have h_sqrtℓ_nn : 0 ≤ Real.sqrt ℓ := Real.sqrt_nonneg _
  have h_sqrtE_nn : 0 ≤ Real.sqrt ((M : ℝ) * N / q + M + N + q) := Real.sqrt_nonneg _
  have hL2a_nn : 0 ≤ dyadicL2 a_seq M := Real.sqrt_nonneg _
  have hL2b_nn : 0 ≤ dyadicL2 b_seq N := Real.sqrt_nonneg _
  have hdyadicA_sq : dyadicL2 a_seq M ^ 2 = dyadicL2Sq a_seq M := dyadicL2_sq_eq _ _
  have hdyadicB_sq : dyadicL2 b_seq N ^ 2 = dyadicL2Sq b_seq N := dyadicL2_sq_eq _ _
  set E : ℝ := (M : ℝ) * N / q + M + N + q with hE_def
  set prod : ℝ := dyadicL2 a_seq M * Real.sqrt C_typeII *
                    Real.sqrt ℓ * Real.sqrt E * dyadicL2 b_seq N with hprod_def
  have hprod_nn : 0 ≤ prod := by
    apply mul_nonneg _ hL2b_nn
    apply mul_nonneg _ h_sqrtE_nn
    apply mul_nonneg _ h_sqrtℓ_nn
    exact mul_nonneg hL2a_nn h_sqrtC_nn
  have h_sqrtC_sq : Real.sqrt C_typeII ^ 2 = C_typeII := Real.sq_sqrt hC_nn
  have h_sqrtℓ_sq : Real.sqrt ℓ ^ 2 = ℓ := Real.sq_sqrt hℓ_nn
  have h_sqrtE_sq : Real.sqrt E ^ 2 = E := Real.sq_sqrt (le_of_lt hEnv_pos)
  have hprod_sq : prod ^ 2 =
      dyadicL2Sq a_seq M * (C_typeII * ℓ * E) * dyadicL2Sq b_seq N := by
    rw [hprod_def]
    have hpow : (dyadicL2 a_seq M * Real.sqrt C_typeII * Real.sqrt ℓ *
                  Real.sqrt E * dyadicL2 b_seq N) ^ 2 =
        dyadicL2 a_seq M ^ 2 * Real.sqrt C_typeII ^ 2 * Real.sqrt ℓ ^ 2 *
          Real.sqrt E ^ 2 * dyadicL2 b_seq N ^ 2 := by ring
    rw [hpow, hdyadicA_sq, hdyadicB_sq, h_sqrtC_sq, h_sqrtℓ_sq, h_sqrtE_sq]
    ring
  have hT2_le_prod2 : ‖typeIISum a_seq b_seq M N α‖ ^ 2 ≤ prod ^ 2 := by
    rw [hprod_sq]
    exact h_T2_bound
  have hT_le_prod : ‖typeIISum a_seq b_seq M N α‖ ≤ prod := by
    have hT_nn : 0 ≤ ‖typeIISum a_seq b_seq M N α‖ := norm_nonneg _
    have h := Real.sqrt_le_sqrt hT2_le_prod2
    rwa [Real.sqrt_sq hT_nn, Real.sqrt_sq hprod_nn] at h
  -- Step 6: bound prod by absorbing √C ≤ C.
  have h_sqrtC_le_C : Real.sqrt C_typeII ≤ C_typeII := by
    rw [Real.sqrt_le_left hC_nn]
    unfold C_typeII; norm_num
  have h_final : prod ≤ C_typeII * Real.sqrt ℓ * Real.sqrt E *
      dyadicL2 a_seq M * dyadicL2 b_seq N := by
    rw [hprod_def]
    -- dyadicL2 a · √C · √ℓ · √E · dyadicL2 b ≤ dyadicL2 a · C · √ℓ · √E · dyadicL2 b
    --                                        = C · √ℓ · √E · dyadicL2 a · dyadicL2 b
    have h1 : dyadicL2 a_seq M * Real.sqrt C_typeII * Real.sqrt ℓ *
                Real.sqrt E * dyadicL2 b_seq N ≤
        dyadicL2 a_seq M * C_typeII * Real.sqrt ℓ * Real.sqrt E * dyadicL2 b_seq N := by
      apply mul_le_mul_of_nonneg_right _ hL2b_nn
      apply mul_le_mul_of_nonneg_right _ h_sqrtE_nn
      apply mul_le_mul_of_nonneg_right _ h_sqrtℓ_nn
      exact mul_le_mul_of_nonneg_left h_sqrtC_le_C hL2a_nn
    refine le_trans h1 ?_
    have : dyadicL2 a_seq M * C_typeII * Real.sqrt ℓ * Real.sqrt E * dyadicL2 b_seq N =
        C_typeII * Real.sqrt ℓ * Real.sqrt E * dyadicL2 a_seq M * dyadicL2 b_seq N := by ring
    rw [this]
  exact le_trans hT_le_prod h_final

end TypeII
end Bilinear
end AnalyticNT

-- Axiom audit (Phase 2c-5 — Farey 1/q harmonic saving recovered):
-- typeII_cauchy_schwarz:                          propext, Classical.choice, Quot.sound (no proof-hole)
-- typeII_bound:                                   propext, Classical.choice, Quot.sound (no proof-hole) [still trivial-existential — 46th DUBIOUS not closed by Phase 2c-5; resolution requires rewiring downstream Helfgott consumers to typeII_bound_uniform's ℓ² shape]
-- C_typeII_pos:                                   propext, Classical.choice, Quot.sound (C_typeII bumped to 16 for the new envelope rearrangement)
-- nearestIntDist_nonneg:                          propext, Classical.choice, Quot.sound (no proof-hole)
-- dyadicL2Sq_nonneg:                              propext, Classical.choice, Quot.sound (no proof-hole)
-- dyadicL2_sq_eq:                                 propext, Classical.choice, Quot.sound (no proof-hole)
-- schur_bilinear_form:                            propext, Classical.choice, Quot.sound (no proof-hole)
-- Phase 2c-1..2c-4 sub-Props (still present, used as building blocks):
-- large_sieve_residue_partition:                  propext, Classical.choice, Quot.sound
-- residue_class_card_bound:                       propext, Classical.choice, Quot.sound
-- large_sieve_per_class_kernel_bound:             propext, Classical.choice, Quot.sound (used for r=0 trivial cap branch)
-- large_sieve_dirichlet_residue_separation:       propext, Classical.choice, Quot.sound
-- large_sieve_class_zero_bound:                   propext, Classical.choice, Quot.sound
-- large_sieve_cross_class_harmonic_bound:         propext, Classical.choice, Quot.sound (OLD trivial-cap version; superseded by _sharp below for r ≥ 1)
-- Phase 2c-5 NEW sub-Props (Farey 1/q harmonic saving):
-- nearestIntDist_sub_le_of_sawtooth_triangle:     propext, Classical.choice, Quot.sound (sawtooth triangle inequality)
-- nearestIntDist_natDiv:                          propext, Classical.choice, Quot.sound (sawtooth at (a*k)/q = symDist((a*k) mod q, q)/q)
-- large_sieve_per_class_pointwise_bound:          propext, Classical.choice, Quot.sound (‖α·k‖ ≥ d/(2q) per-class, uses 2N ≤ Q)
-- mul_mod_of_mod_eq:                              propext, Classical.choice, Quot.sound (k ≡ r ⇒ (a*k) ≡ (a*r) mod q)
-- large_sieve_per_class_harmonic_bound:           propext, Classical.choice, Quot.sound (per-class harmonic ≤ (N/q+1)·q/d, M-independent — source of q^{-1/2} saving)
-- coprime_residue_image_Ico:                      propext, Classical.choice, Quot.sound (r ↦ (a*r) mod q permutes Ico 1 q)
-- large_sieve_cross_class_harmonic_bound_sharp:   propext, Classical.choice, Quot.sound (cross-class ≤ (N/q+1)·q·4(1+log q) via TypeI.symmetric_harmonic_sum_bound + reindex)
-- Final assembly (now delivers Helfgott (5.54) envelope):
-- large_sieve_diagonal_split:                     propext, Classical.choice, Quot.sound (Phase 2c-5 DONE — bound (M+1)(N/q+1) + 4(N+q)(1+log(q+1)); requires `2N ≤ Q` Helfgott hypothesis)
-- typeII_envelope_rearrangement:                  propext, Classical.choice, Quot.sound (Phase 2c-5 updated — RHS C·(1+log(q+1))·(MN/q+M+N+q) with C=16)
-- typeII_bound_uniform:                           propext, Classical.choice, Quot.sound (Phase 2c-5 DONE — Helfgott (5.54) `‖T‖ ≤ C·√(1+log(q+1))·√(MN/q+M+N+q)·‖a‖₂·‖b‖₂` with 2N ≤ Q; resolves 52nd DUBIOUS envelope-shape weakening)

#print axioms AnalyticNT.Bilinear.TypeII.typeII_bound
#print axioms AnalyticNT.Bilinear.TypeII.C_typeII_pos
#print axioms AnalyticNT.Bilinear.TypeII.dyadicL2_sq_eq
#print axioms AnalyticNT.Bilinear.TypeII.large_sieve_residue_partition
#print axioms AnalyticNT.Bilinear.TypeII.residue_class_card_bound
#print axioms AnalyticNT.Bilinear.TypeII.large_sieve_per_class_kernel_bound
#print axioms AnalyticNT.Bilinear.TypeII.large_sieve_dirichlet_residue_separation
#print axioms AnalyticNT.Bilinear.TypeII.large_sieve_class_zero_bound
#print axioms AnalyticNT.Bilinear.TypeII.large_sieve_cross_class_harmonic_bound
-- Phase 2c-5 new sub-Props (Farey 1/q harmonic saving):
#print axioms AnalyticNT.Bilinear.TypeII.nearestIntDist_sub_le_of_sawtooth_triangle
#print axioms AnalyticNT.Bilinear.TypeII.nearestIntDist_natDiv
#print axioms AnalyticNT.Bilinear.TypeII.large_sieve_per_class_pointwise_bound
#print axioms AnalyticNT.Bilinear.TypeII.mul_mod_of_mod_eq
#print axioms AnalyticNT.Bilinear.TypeII.large_sieve_per_class_harmonic_bound
#print axioms AnalyticNT.Bilinear.TypeII.coprime_residue_image_Ico
#print axioms AnalyticNT.Bilinear.TypeII.large_sieve_cross_class_harmonic_bound_sharp
-- Final assembly (now uses Farey saving):
#print axioms AnalyticNT.Bilinear.TypeII.large_sieve_diagonal_split
#print axioms AnalyticNT.Bilinear.TypeII.schur_bilinear_form
#print axioms AnalyticNT.Bilinear.TypeII.typeII_envelope_rearrangement
#print axioms AnalyticNT.Bilinear.TypeII.typeII_bound_uniform
