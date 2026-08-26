import ErdosProblems.Erdos67b.MRT
import ErdosProblems.Erdos67b.FiniteFourier
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Major arcs and the Matomäki--Radziwiłł mean-square boundary

This file records source-near finite infrastructure for the major-arc part of the
Matomäki--Radziwiłł--Tao short-interval estimate.  There are three layers.

* `ScaledRationalApproximation` and `RationalApproximation` give an interface to Mathlib's
  Dirichlet approximation theorem with an integral numerator and a positive natural
  denominator.
* periodic weights on `ZMod q` are expanded exactly into additive characters.  In particular,
  a rational additive phase is a periodic weight of this kind.
* `MRComplexNonpretentiousMeanSquareInput` is the exact discrete complex mean-square theorem
  which the analytic part must prove.  Its quantitative nonpretentiousness hypothesis is
  essential: the unrestricted complex statement is false for `f(n)=n^{it}`.  It is a
  proposition, not an assumption or declaration.  The final lemmas show unconditionally how a
  proof of this proposition supplies the required first-moment bound.

All sums are finite.  Thus the only non-elementary dependency boundary in this file is the
explicit proposition `MRComplexNonpretentiousMeanSquareInput`.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67b

noncomputable section

/-! ## Rational approximation -/

/-- The scaled form of a rational approximation.  This is the form returned directly by
Dirichlet's pigeonhole argument: `|q α - a|` is small, with `q` positive and bounded by `Q`. -/
def ScaledRationalApproximation (α : ℝ) (Q : ℕ) (a : ℤ) (q : ℕ) : Prop :=
  0 < q ∧ q ≤ Q ∧ |(q : ℝ) * α - (a : ℝ)| ≤ 1 / ((Q : ℝ) + 1)

/-- The usual unscaled form `|α-a/q| ≤ δ`. -/
def RationalApproximation (α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ) : Prop :=
  0 < q ∧ |α - (a : ℝ) / (q : ℝ)| ≤ δ

/-- Dirichlet's approximation theorem in the exact scaled interface used above. -/
theorem exists_scaledRationalApproximation (α : ℝ) {Q : ℕ} (hQ : 0 < Q) :
    ∃ a : ℤ, ∃ q : ℕ, ScaledRationalApproximation α Q a q := by
  obtain ⟨q, hq, hqQ, happrox⟩ := Real.exists_nat_abs_mul_sub_round_le α hQ
  exact ⟨round ((q : ℝ) * α), q, hq, hqQ, happrox⟩

/-- Dividing the scaled error by the positive denominator gives the standard approximation. -/
theorem rationalApproximation_of_scaled {α : ℝ} {Q q : ℕ} {a : ℤ}
    (h : ScaledRationalApproximation α Q a q) :
    RationalApproximation α a q (1 / (((Q : ℝ) + 1) * q)) := by
  rcases h with ⟨hq, hqQ, hscaled⟩
  refine ⟨hq, ?_⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have heq : α - (a : ℝ) / (q : ℝ) = ((q : ℝ) * α - (a : ℝ)) / q := by
    field_simp
  rw [heq, abs_div, abs_of_pos hqR]
  calc
    |(q : ℝ) * α - (a : ℝ)| / q ≤ (1 / ((Q : ℝ) + 1)) / q :=
      div_le_div_of_nonneg_right hscaled hqR.le
    _ = 1 / (((Q : ℝ) + 1) * q) := by rw [div_div]

/-- Dirichlet's theorem in unscaled form, with the numerator and denominator exposed. -/
theorem exists_rationalApproximation (α : ℝ) {Q : ℕ} (hQ : 0 < Q) :
    ∃ a : ℤ, ∃ q : ℕ, q ≤ Q ∧
      RationalApproximation α a q (1 / (((Q : ℝ) + 1) * q)) := by
  obtain ⟨a, q, h⟩ := exists_scaledRationalApproximation α hQ
  exact ⟨a, q, h.2.1, rationalApproximation_of_scaled h⟩

/-- Reduced Dirichlet approximation.  The coprimality is essential on the
minor arcs, where the Vinogradov residue-block estimate is stated for a
reduced numerator and denominator. -/
theorem exists_reducedRationalApproximation
    (α : ℝ) {Q : ℕ} (hQ : 0 < Q) :
    ∃ a : ℤ, ∃ q : ℕ,
      0 < q ∧ q ≤ Q ∧ Nat.Coprime a.natAbs q ∧
        |α - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * Q) := by
  obtain ⟨r, happrox, hden⟩ :=
    Real.exists_rat_abs_sub_le_and_den_le α hQ
  refine ⟨r.num, r.den, r.den_pos, hden, r.reduced, ?_⟩
  have hcast : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
    exact_mod_cast r.num_div_den.symm
  rw [hcast] at happrox
  refine happrox.trans ?_
  have hq : (0 : ℝ) < r.den := by positivity
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  apply one_div_le_one_div_of_le (mul_pos hq hQR)
  nlinarith

/-- Dirichlet approximation together with the exact major/minor denominator
dichotomy at an arbitrary cutoff. -/
theorem exists_reducedRationalApproximation_dichotomy
    (α : ℝ) {Q W : ℕ} (hQ : 0 < Q) :
    ∃ a : ℤ, ∃ q : ℕ,
      0 < q ∧ q ≤ Q ∧ Nat.Coprime a.natAbs q ∧
        |α - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * Q) ∧
        (q < W ∨ W ≤ q) := by
  obtain ⟨a, q, hq, hqQ, hcop, happ⟩ :=
    exists_reducedRationalApproximation α hQ
  exact ⟨a, q, hq, hqQ, hcop, happ, lt_or_ge q W⟩

/-- Floor-safe short-interval form of reduced Dirichlet approximation.  The
cutoff `H / W + 1` is the smallest simple natural cutoff for which the phase
error has exactly the MRT size `W / (Hq)` without silently replacing natural
division by real division. -/
theorem exists_reducedRationalApproximation_shortInterval
    (α : ℝ) {H W : ℕ} (hH : 0 < H) (hW : 0 < W) :
    ∃ a : ℤ, ∃ q : ℕ,
      0 < q ∧ q ≤ H / W + 1 ∧ Nat.Coprime a.natAbs q ∧
        |α - (a : ℝ) / q| ≤
          (W : ℝ) / ((H : ℝ) * q) := by
  have hQ : (0 : ℕ) < H / W + 1 := Nat.zero_lt_succ _
  obtain ⟨a, q, hq, hqQ, hcop, happ⟩ :=
    exists_reducedRationalApproximation α hQ
  refine ⟨a, q, hq, hqQ, hcop, happ.trans ?_⟩
  have hmod : H % W < W := Nat.mod_lt H hW
  have hdecomp : H / W * W + H % W = H := by
    simpa [mul_comm] using Nat.div_add_mod H W
  have hHW : H ≤ (H / W + 1) * W := by
    calc
      H = H / W * W + H % W := hdecomp.symm
      _ ≤ H / W * W + W := Nat.add_le_add_left hmod.le _
      _ = (H / W + 1) * W := by ring
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hQR : (0 : ℝ) < ((H / W + 1 : ℕ) : ℝ) := by
    exact_mod_cast hQ
  apply (div_le_div_iff₀ (mul_pos hqR hQR) (mul_pos hHR hqR)).2
  have hHWR : (H : ℝ) ≤ (H / W + 1 : ℕ) * W := by
    exact_mod_cast hHW
  push_cast at hHWR ⊢
  nlinarith

theorem RationalApproximation.mono {α : ℝ} {a : ℤ} {q : ℕ} {δ δ' : ℝ}
    (h : RationalApproximation α a q δ) (hδ : δ ≤ δ') :
    RationalApproximation α a q δ' :=
  ⟨h.1, h.2.trans hδ⟩

/-- A major arc at denominator cutoff `Q` and phase resolution `δ`. -/
def IsMajorArc (α : ℝ) (Q : ℕ) (δ : ℝ) : Prop :=
  ∃ a : ℤ, ∃ q : ℕ, q ≤ Q ∧ RationalApproximation α a q δ

theorem isMajorArc_of_rationalApproximation {α : ℝ} {Q q : ℕ} {a : ℤ} {δ : ℝ}
    (hqQ : q ≤ Q) (h : RationalApproximation α a q δ) :
    IsMajorArc α Q δ :=
  ⟨a, q, hqQ, h⟩

/-! ## Rational phases and exact additive-character decomposition -/

/-- The additive character modulo `q` with frequency `a`. -/
def rationalAddChar (q : ℕ) [NeZero q] (a : ℤ) : AddChar (ZMod q) ℂ :=
  ZMod.stdAddChar.mulShift (a : ZMod q)

/-- The periodic weight on `ZMod q` associated with the rational phase `a/q`. -/
def rationalPhase (q : ℕ) [NeZero q] (a : ℤ) (x : ZMod q) : ℂ :=
  ZMod.stdAddChar ((a : ZMod q) * x)

@[simp]
theorem rationalAddChar_apply (q : ℕ) [NeZero q] (a : ℤ) (x : ZMod q) :
    rationalAddChar q a x = rationalPhase q a x := by
  simp [rationalAddChar, rationalPhase]

@[simp]
theorem norm_rationalPhase (q : ℕ) [NeZero q] (a : ℤ) (x : ZMod q) :
    ‖rationalPhase q a x‖ = 1 := by
  simp [rationalPhase]

/-- A rational real phase agrees exactly with its periodic `ZMod q` model. -/
theorem additivePhase_rational (q : ℕ) [NeZero q] (a : ℤ) (j : ℕ) :
    additivePhase ((a : ℝ) / q) j = rationalPhase q a (j : ZMod q) := by
  rw [additivePhase, rationalPhase]
  rw [show ((a : ZMod q) * (j : ZMod q)) = ((a * j : ℤ) : ZMod q) by
    push_cast
    rfl]
  rw [ZMod.stdAddChar_coe]
  congr 1
  push_cast
  field_simp [NeZero.ne q]

/-- A short interval sum carrying an arbitrary periodic weight modulo `q`. -/
def periodicWeightedShortSum {q : ℕ} [NeZero q]
    (f : ℕ → ℂ) (n H : ℕ) (w : ZMod q → ℂ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 H, f (n + j) * w (j : ZMod q)

/-- The inner sum against one additive character modulo `q`. -/
def additiveCharacterShortSum {q : ℕ} [NeZero q]
    (f : ℕ → ℂ) (n H : ℕ) (ψ : AddChar (ZMod q) ℂ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 H, f (n + j) * ψ (j : ZMod q)

/-- The rationally modulated sum is literally the sum against the corresponding additive
character on `ZMod q`. -/
theorem additiveCharacterShortSum_rational {q : ℕ} [NeZero q]
    (f : ℕ → ℂ) (n H : ℕ) (a : ℤ) :
    additiveCharacterShortSum f n H (rationalAddChar q a) =
      modulatedShortSum f n H ((a : ℝ) / q) := by
  unfold additiveCharacterShortSum modulatedShortSum
  apply Finset.sum_congr rfl
  intro j _
  rw [rationalAddChar_apply, ← additivePhase_rational]

/-- Local major-arc version of the elementary phase Lipschitz estimate. -/
theorem majorArc_norm_additivePhase_sub_le (alpha beta : ℝ) (n : ℕ) :
    ‖additivePhase alpha n - additivePhase beta n‖ ≤
      2 * Real.pi * |alpha - beta| * n := by
  let x : ℝ := 2 * Real.pi * (alpha - beta) * n
  have hfactor :
      additivePhase alpha n =
        additivePhase beta n * Complex.exp (x * Complex.I) := by
    unfold additivePhase
    rw [← Complex.exp_add]
    congr 1
    simp only [x]
    push_cast
    ring
  rw [hfactor]
  rw [show additivePhase beta n * Complex.exp (x * Complex.I) - additivePhase beta n =
      additivePhase beta n * (Complex.exp (x * Complex.I) - 1) by ring]
  rw [norm_mul, norm_additivePhase, one_mul]
  have hexp : ‖Complex.exp (x * Complex.I) - 1‖ ≤ ‖x‖ := by
    simpa [mul_comm] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x))
  calc
    ‖Complex.exp (x * Complex.I) - 1‖ ≤ ‖x‖ := hexp
    _ = 2 * Real.pi * |alpha - beta| * n := by
      simp only [x, Real.norm_eq_abs, abs_mul, abs_of_nonneg Real.pi_nonneg]
      have hnabs : |(n : ℝ)| = n := abs_of_nonneg (Nat.cast_nonneg n)
      rw [hnabs]
      ring

/-- Local major-arc perturbation estimate with the explicit coarse loss `2 π δ H²`. -/
theorem majorArc_norm_modulatedShortSum_sub_le
    {f : ℕ → ℂ} {n H : ℕ} {alpha beta delta : ℝ}
    (hf : ∀ j ∈ Finset.Icc 1 H, ‖f (n + j)‖ ≤ 1)
    (hdelta : |alpha - beta| ≤ delta) :
    ‖modulatedShortSum f n H alpha - modulatedShortSum f n H beta‖ ≤
      2 * Real.pi * delta * H ^ 2 := by
  have hdelta0 : 0 ≤ delta := (abs_nonneg (alpha - beta)).trans hdelta
  unfold modulatedShortSum
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ j ∈ Finset.Icc 1 H,
        (f (n + j) * additivePhase alpha j -
          f (n + j) * additivePhase beta j)‖ ≤
        ∑ j ∈ Finset.Icc 1 H,
          ‖f (n + j) * additivePhase alpha j -
            f (n + j) * additivePhase beta j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.Icc 1 H,
        (2 * Real.pi * delta * H : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← mul_sub, norm_mul]
      have hjH : j ≤ H := (Finset.mem_Icc.mp hj).2
      calc
        ‖f (n + j)‖ * ‖additivePhase alpha j - additivePhase beta j‖ ≤
            1 * (2 * Real.pi * |alpha - beta| * j) := by
          gcongr
          · exact hf j hj
          · exact majorArc_norm_additivePhase_sub_le alpha beta j
        _ ≤ 2 * Real.pi * delta * H := by
          have hj0 : (0 : ℝ) ≤ j := by positivity
          have hjHR : (j : ℝ) ≤ H := by exact_mod_cast hjH
          simp only [one_mul]
          calc
            2 * Real.pi * |alpha - beta| * (j : ℝ) =
                (2 * Real.pi) * (|alpha - beta| * j) := by ring
            _ ≤ (2 * Real.pi) * (delta * j) := by gcongr
            _ ≤ (2 * Real.pi) * (delta * H) := by gcongr
            _ = 2 * Real.pi * delta * H := by ring
    _ = 2 * Real.pi * delta * H ^ 2 := by
      simp
      ring

/-- A rational approximation gives an explicit finite error for replacing the phase by its
periodic major-arc model. -/
theorem norm_modulatedShortSum_sub_rational_le
    (f : ℕ → ℂ) (n H q : ℕ) (a : ℤ) (α δ : ℝ)
    (hf : ∀ m : ℕ, ‖f m‖ ≤ 1)
    (happrox : RationalApproximation α a q δ) :
    ‖modulatedShortSum f n H α - modulatedShortSum f n H ((a : ℝ) / q)‖ ≤
      2 * Real.pi * H ^ 2 * δ := by
  have h := majorArc_norm_modulatedShortSum_sub_le
    (f := f) (n := n) (H := H) (alpha := α) (beta := (a : ℝ) / q) (delta := δ)
    (fun j _ ↦ hf (n + j)) happrox.2
  convert h using 1 <;> ring

/-- Exact finite Fourier expansion of an arbitrary periodic short-interval weight. -/
theorem periodicWeightedShortSum_fourier {q : ℕ} [NeZero q]
    (f : ℕ → ℂ) (n H : ℕ) (w : ZMod q → ℂ) :
    periodicWeightedShortSum f n H w =
      ∑ ψ : AddChar (ZMod q) ℂ,
        fourierCoeff w ψ * additiveCharacterShortSum f n H ψ := by
  classical
  unfold periodicWeightedShortSum additiveCharacterShortSum
  simp_rw [← fourier_inversion w]
  simp only [smul_eq_mul]
  calc
    (∑ j ∈ Finset.Icc 1 H,
        f (n + j) * ∑ ψ : AddChar (ZMod q) ℂ,
          ψ (j : ZMod q) * fourierCoeff w ψ) =
        ∑ j ∈ Finset.Icc 1 H, ∑ ψ : AddChar (ZMod q) ℂ,
          f (n + j) * (ψ (j : ZMod q) * fourierCoeff w ψ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = ∑ ψ : AddChar (ZMod q) ℂ, ∑ j ∈ Finset.Icc 1 H,
          f (n + j) * (ψ (j : ZMod q) * fourierCoeff w ψ) := by
      rw [Finset.sum_comm]
    _ = ∑ ψ : AddChar (ZMod q) ℂ,
          fourierCoeff w ψ *
            ∑ j ∈ Finset.Icc 1 H, f (n + j) * ψ (j : ZMod q) := by
      apply Finset.sum_congr rfl
      intro ψ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- At an exact rational frequency, the real-frequency modulated sum is a periodic sum. -/
theorem modulatedShortSum_rational {q : ℕ} [NeZero q]
    (f : ℕ → ℂ) (n H : ℕ) (a : ℤ) :
    modulatedShortSum f n H ((a : ℝ) / q) =
      periodicWeightedShortSum f n H (rationalPhase q a) := by
  unfold modulatedShortSum periodicWeightedShortSum
  apply Finset.sum_congr rfl
  intro j _
  rw [additivePhase_rational]

/-- Fourier decomposition of a rationally modulated short sum into additive characters. -/
theorem modulatedShortSum_rational_fourier {q : ℕ} [NeZero q]
    (f : ℕ → ℂ) (n H : ℕ) (a : ℤ) :
    modulatedShortSum f n H ((a : ℝ) / q) =
      ∑ ψ : AddChar (ZMod q) ℂ,
        fourierCoeff (rationalPhase q a) ψ *
          additiveCharacterShortSum f n H ψ := by
  rw [modulatedShortSum_rational, periodicWeightedShortSum_fourier]

/-! ## Finite `L²` to `L¹` inequalities -/

/-- Cauchy--Schwarz for a finite family of nonnegative real numbers. -/
theorem sq_sum_le_card_mul_sum_sq_real {ι : Type*} (s : Finset ι) (u : ι → ℝ) :
    (∑ i ∈ s, u i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (u i) ^ 2 := by
  classical
  exact sq_sum_le_card_mul_sum_sq

/-- Complex finite Cauchy--Schwarz, stated in the form used for first moments. -/
theorem sq_sum_norm_le_card_mul_sum_normSq {ι : Type*}
    (s : Finset ι) (F : ι → ℂ) :
    (∑ i ∈ s, ‖F i‖) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, Complex.normSq (F i) := by
  simpa only [Complex.normSq_eq_norm_sq] using
    (sq_sum_le_card_mul_sum_sq_real s fun i ↦ ‖F i‖)

/-- An `L²` bound with root-mean-square at most `η` implies the corresponding `L¹` bound. -/
theorem sum_norm_le_of_sum_normSq_le {ι : Type*}
    (s : Finset ι) (F : ι → ℂ) (η : ℝ) (hη : 0 ≤ η)
    (h₂ : (∑ i ∈ s, Complex.normSq (F i)) ≤ η ^ 2 * s.card) :
    (∑ i ∈ s, ‖F i‖) ≤ η * s.card := by
  classical
  have hCS := sq_sum_norm_le_card_mul_sum_normSq s F
  have hcard : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  have hsum : 0 ≤ ∑ i ∈ s, ‖F i‖ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hrhs : 0 ≤ η * (s.card : ℝ) := mul_nonneg hη hcard
  nlinarith

/-! ## The Matomäki--Radziwiłł dependency boundary -/

/-- Source-level multiplicativity on positive naturals: multiplication is required only for
coprime arguments. -/
def IsMultiplicativeOnPositiveNat (f : ℕ → ℂ) : Prop :=
  f 1 = 1 ∧ ∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n → f (m * n) = f m * f n

/-- Complete multiplicativity, as used in Erdős discrepancy, implies the source-level
multiplicativity hypothesis of the Matomäki--Radziwiłł theorem. -/
theorem IsCompletelyMultiplicativeOnPositive.isMultiplicativeOnPositiveNat
    {f : ℕ → ℂ} (hf : IsCompletelyMultiplicativeOnPositive f) :
    IsMultiplicativeOnPositiveNat f := by
  refine ⟨hf.1, ?_⟩
  intro m n hm hn _
  exact hf.2 m n hm hn

/-- The average of `f` on the reference interval `(X,2X]`. -/
def longIntervalMean (f : ℕ → ℂ) (X : ℕ) : ℂ :=
  (X : ℂ)⁻¹ * ∑ m ∈ Finset.Ioc X (2 * X), f m

/-- Deviation of a length-`H` short sum from `H` times the reference mean. -/
def shortIntervalDeviation (f : ℕ → ℂ) (X n H : ℕ) : ℂ :=
  (∑ j ∈ Finset.Icc 1 H, f (n + j)) - (H : ℂ) * longIntervalMean f X

/-- Discrete mean-square of short-interval deviations for starting points `X < n ≤ 2X`. -/
def shortIntervalMeanSquare (f : ℕ → ℂ) (X H : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq (shortIntervalDeviation f X n H)

/-- The uncentered second moment used in Appendix A of Matomäki--Radziwiłł--Tao. -/
def uncenteredShortIntervalMeanSquare (f : ℕ → ℂ) (X H : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc X (2 * X),
    Complex.normSq (∑ j ∈ Finset.Icc 1 H, f (n + j))

/-- Quantitative separation from all Archimedean characters `n ↦ n^{it}` at scale `X`.

This is the essential extra hypothesis in the complex-valued Matomäki--Radziwiłł theorem. -/
def MRArchimedeanNonpretentious (f : ℕ → ℂ) (A X : ℕ) : Prop :=
  ∀ t : ℝ, |t| ≤ X →
    (A : ℝ) ≤ pretentiousDistSq f (archimedeanTwist t) X

/-- The finite epsilon-form of the complex Matomäki--Radziwiłł mean-square theorem used on
major arcs.

The parameter `A` is the quantitative lower bound for the distance from Archimedean twists.
The hierarchy is: choose an error, then a common threshold `B`; choose `A,H ≥ B`; finally take
`X` sufficiently large depending on `A,H`.  This is an explicit proposition to be proved by the
analytic argument, not an assumed declaration.

There is deliberately no unrestricted complex version here.  Such a version is false: the
functions `f(n)=n^{it}` have a positive limiting local-to-global variance. -/
def MRComplexNonpretentiousMeanSquareInput : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ B : ℕ, 1 ≤ B ∧
      ∀ A H : ℕ, B ≤ A → B ≤ H →
        ∃ X₀ : ℕ, max A H ≤ X₀ ∧
          ∀ X : ℕ, X₀ ≤ X →
            ∀ f : ℕ → ℂ,
              IsMultiplicativeOnPositiveNat f →
              (∀ m : ℕ, 0 < m → ‖f m‖ ≤ 1) →
              MRArchimedeanNonpretentious f A X →
              uncenteredShortIntervalMeanSquare f X H ≤ ε ^ 2 * H ^ 2 * X

/-- The interval `(X,2X]` has exactly `X` elements. -/
@[simp]
theorem card_Ioc_self_two_mul (X : ℕ) : (Finset.Ioc X (2 * X)).card = X := by
  simp
  omega

/-- A proved complex nonpretentious mean-square estimate immediately gives the corresponding
first-moment estimate for the short-interval deviations. -/
theorem mrComplexNonpretentiousMeanSquareInput_implies_firstMoment
    (hMR : MRComplexNonpretentiousMeanSquareInput) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, 1 ≤ B ∧
      ∀ A H : ℕ, B ≤ A → B ≤ H →
        ∃ X₀ : ℕ, max A H ≤ X₀ ∧
          ∀ X : ℕ, X₀ ≤ X →
            ∀ f : ℕ → ℂ,
              IsCompletelyMultiplicativeOnPositive f →
              (∀ m : ℕ, 0 < m → ‖f m‖ ≤ 1) →
              MRArchimedeanNonpretentious f A X →
              (∑ n ∈ Finset.Ioc X (2 * X),
                ‖∑ j ∈ Finset.Icc 1 H, f (n + j)‖) ≤
                ε * H * X := by
  obtain ⟨B, hB, hMR'⟩ := hMR ε hε
  refine ⟨B, hB, ?_⟩
  intro A H hA hH
  obtain ⟨X₀, hHX₀, hMRH⟩ := hMR' A H hA hH
  refine ⟨X₀, hHX₀, ?_⟩
  intro X hX f hmult hbound hnonpret
  have h₂ := hMRH X hX f hmult.isMultiplicativeOnPositiveNat hbound hnonpret
  have hL1 := sum_norm_le_of_sum_normSq_le
    (Finset.Ioc X (2 * X))
    (fun n ↦ ∑ j ∈ Finset.Icc 1 H, f (n + j)) (ε * H)
    (mul_nonneg hε.le (Nat.cast_nonneg H))
  rw [show (∑ n ∈ Finset.Ioc X (2 * X),
      Complex.normSq (∑ j ∈ Finset.Icc 1 H, f (n + j))) =
      uncenteredShortIntervalMeanSquare f X H by rfl] at hL1
  have hbound₂ : uncenteredShortIntervalMeanSquare f X H ≤
      (ε * H) ^ 2 * (Finset.Ioc X (2 * X)).card := by
    rw [card_Ioc_self_two_mul]
    convert h₂ using 1 <;> ring
  specialize hL1 hbound₂
  rw [card_Ioc_self_two_mul] at hL1
  convert hL1 using 1 <;> ring

end

end Erdos67b
