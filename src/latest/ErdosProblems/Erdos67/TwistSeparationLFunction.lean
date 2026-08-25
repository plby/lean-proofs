import ErdosProblems.Erdos67.TwistSeparationAnalytic
import ErdosProblems.Erdos67.TwistSeparationEdges
import ErdosProblems.Erdos67.Section4Assembly
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# From Dirichlet L-function bounds to the finite Euler logarithm

This file isolates the exact infinite-to-finite Euler-product comparison used
in the polynomial-height twist estimate.  The analytic input controlling the
size of the L-function is deliberately kept separate from the elementary
Euler-product bookkeeping.
-/

open scoped BigOperators LSeries.notation

namespace Erdos67

noncomputable section

/-- The primes at most `Y`, regarded as a finset of the subtype of primes. -/
def primeSubtypeUpTo (Y : ℕ) : Finset Nat.Primes :=
  (Nat.primesLE Y).attach.map
    { toFun := fun p : {n // n ∈ Nat.primesLE Y} ↦
        ⟨p.1, (Nat.mem_primesLE.mp p.2).2⟩
      inj' := fun (_ _ : {n // n ∈ Nat.primesLE Y}) h ↦
        Subtype.ext (congrArg (fun r : Nat.Primes ↦ r.1) h) }

@[simp] theorem mem_primeSubtypeUpTo {Y : ℕ} {p : Nat.Primes} :
    p ∈ primeSubtypeUpTo Y ↔ p.1 ≤ Y := by
  constructor
  · intro hp
    rcases Finset.mem_map.mp hp with ⟨q, hq, hqp⟩
    have hval : q.1 = p.1 := congrArg Subtype.val hqp
    have hqle := (Nat.mem_primesLE.mp q.2).1
    simpa only [hval] using hqle
  · intro hp
    have hmem : p.1 ∈ Nat.primesLE Y := Nat.mem_primesLE.mpr ⟨hp, p.2⟩
    refine Finset.mem_map.mpr ⟨⟨p.1, hmem⟩, Finset.mem_attach _ _, ?_⟩
    exact Subtype.ext rfl

/-- The full logarithmic Euler summand at the point used for polynomial
height separation. -/
def polynomialHeightFullEulerSummand {N : ℕ}
    (ψ : DirichletCharacter ℂ N) (Y : ℕ) (v : ℝ)
    (p : Nat.Primes) : ℂ :=
  -Complex.log (1 - ψ p * (p : ℂ) ^ (-polynomialHeightEulerPoint Y v))

theorem polynomialHeightFullEulerSummand_eq {N Y : ℕ}
    (ψ : DirichletCharacter ℂ N) (v : ℝ) (p : Nat.Primes) :
    polynomialHeightFullEulerSummand ψ Y v p =
      -Complex.log (1 - polynomialHeightEulerPrimeTerm ψ Y v p) := by
  rfl

/-- The Euler logarithm is absolutely summable at the shifted point. -/
theorem summable_polynomialHeightFullEulerSummand {N Y : ℕ}
    (ψ : DirichletCharacter ℂ N) (v : ℝ) (hY : 2 ≤ Y) :
    Summable (polynomialHeightFullEulerSummand ψ Y v) := by
  have hlogY : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  apply DirichletCharacter.summable_neg_log_one_sub_mul_prime_cpow
  simp only [polynomialHeightEulerPoint, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im,
    Complex.ofReal_im, mul_zero, sub_zero, add_zero]
  have hinv : 0 < (Real.log (Y : ℝ))⁻¹ := inv_pos.mpr hlogY
  linarith

/-- The real part of the full Euler logarithm is exactly the real logarithm
of the norm of the Dirichlet L-series. -/
theorem re_tsum_polynomialHeightFullEulerSummand_eq_log_norm_LSeries
    {N Y : ℕ} (ψ : DirichletCharacter ℂ N) (v : ℝ) (hY : 2 ≤ Y) :
    (∑' p : Nat.Primes, polynomialHeightFullEulerSummand ψ Y v p).re =
      Real.log ‖L ↗ψ (polynomialHeightEulerPoint Y v)‖ := by
  have hlogY : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hs : 1 < (polynomialHeightEulerPoint Y v).re := by
    simp only [polynomialHeightEulerPoint, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, add_zero]
    have hinv : 0 < (Real.log (Y : ℝ))⁻¹ := inv_pos.mpr hlogY
    linarith
  have heuler :=
    DirichletCharacter.LSeries_eulerProduct_exp_log ψ hs
  change Complex.exp
      (∑' p : Nat.Primes, polynomialHeightFullEulerSummand ψ Y v p) =
        L ↗ψ (polynomialHeightEulerPoint Y v) at heuler
  have hnorm := congrArg norm heuler
  rw [Complex.norm_exp] at hnorm
  rw [← hnorm, Real.log_exp]

/-- Exact decomposition of the full Euler logarithm into the primes through
`Y` and its complementary tail. -/
theorem truncatedEulerLog_add_complement_eq_full
    {N Y : ℕ} (ψ : DirichletCharacter ℂ N) (v : ℝ) (hY : 2 ≤ Y) :
    truncatedPolynomialHeightEulerLog ψ Y v +
        (∑' p : {p : Nat.Primes // p ∉ primeSubtypeUpTo Y},
          (polynomialHeightFullEulerSummand ψ Y v p.1).re) =
      Real.log ‖L ↗ψ (polynomialHeightEulerPoint Y v)‖ := by
  let f : Nat.Primes → ℂ := polynomialHeightFullEulerSummand ψ Y v
  have hf : Summable f := summable_polynomialHeightFullEulerSummand ψ v hY
  have hre : Summable (fun p ↦ (f p).re) := (Complex.hasSum_re hf.hasSum).summable
  have hsplit := hre.sum_add_tsum_subtype_compl (primeSubtypeUpTo Y)
  rw [← Complex.re_tsum hf,
    re_tsum_polynomialHeightFullEulerSummand_eq_log_norm_LSeries ψ v hY] at hsplit
  rw [← hsplit]
  congr 1
  unfold truncatedPolynomialHeightEulerLog primesUpTo primeSubtypeUpTo
  rw [← Nat.primesLE_eq_filter_range, Finset.sum_map]
  change
    (∑ p ∈ Nat.primesLE Y,
      (-Complex.log (1 - ψ p *
        (p : ℂ) ^ (-polynomialHeightEulerPoint Y v))).re) =
    ∑ p ∈ (Nat.primesLE Y).attach,
      (-Complex.log (1 - ψ p.1 *
        (p.1 : ℂ) ^ (-polynomialHeightEulerPoint Y v))).re
  exact (Finset.sum_attach (Nat.primesLE Y)
    (fun p : ℕ ↦
      (-Complex.log (1 - ψ p *
        (p : ℂ) ^ (-polynomialHeightEulerPoint Y v))).re)).symm

/-- The finite Euler logarithm is bounded by the logarithm of the L-series
plus the norm of the omitted Euler tail. -/
theorem truncatedEulerLog_le_log_norm_LSeries_add_tail
    {N Y : ℕ} (ψ : DirichletCharacter ℂ N) (v : ℝ) (hY : 2 ≤ Y) :
    truncatedPolynomialHeightEulerLog ψ Y v ≤
      Real.log ‖L ↗ψ (polynomialHeightEulerPoint Y v)‖ +
        ∑' p : {p : Nat.Primes // p ∉ primeSubtypeUpTo Y},
          ‖polynomialHeightFullEulerSummand ψ Y v p.1‖ := by
  have hsplit := truncatedEulerLog_add_complement_eq_full ψ v hY
  let g := fun p : {p : Nat.Primes // p ∉ primeSubtypeUpTo Y} ↦
    polynomialHeightFullEulerSummand ψ Y v p.1
  have hg : Summable g :=
    (summable_polynomialHeightFullEulerSummand ψ v hY).subtype _
  have hreNorm :
      -(∑' p, (g p).re) ≤ ∑' p, ‖g p‖ := by
    calc
      -(∑' p, (g p).re) = ∑' p, -(g p).re := by rw [tsum_neg]
      _ ≤ ∑' p, ‖g p‖ := by
        apply Summable.tsum_le_tsum
        · intro p
          exact (neg_le_abs (g p).re).trans (Complex.abs_re_le_norm (g p))
        · exact (Complex.hasSum_re hg.hasSum).summable.neg
        · exact hg.norm
  change truncatedPolynomialHeightEulerLog ψ Y v ≤
    Real.log ‖L ↗ψ (polynomialHeightEulerPoint Y v)‖ + ∑' p, ‖g p‖
  change truncatedPolynomialHeightEulerLog ψ Y v +
      (∑' p, (g p).re) =
    Real.log ‖L ↗ψ (polynomialHeightEulerPoint Y v)‖ at hsplit
  linarith

private theorem finite_primeSubtype_rpow_tail_le
    {Y : ℕ} (hY : 4 ≤ Y)
    (u : Finset {p : Nat.Primes // p ∉ primeSubtypeUpTo Y}) :
    (∑ p ∈ u,
      (p.1.1 : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹))) ≤
      4 * (Real.log 2 + primeLogIntervalMertensConstant) / Real.log 2 := by
  let Z : ℕ := ∑ p ∈ u, p.1.1
  let uNat : Finset ℕ := u.image (fun p ↦ p.1.1)
  have hinj : Set.InjOn (fun p : {p : Nat.Primes // p ∉ primeSubtypeUpTo Y} ↦
      p.1.1) u := by
    intro p hp q hq hpq
    exact Subtype.ext (Subtype.ext hpq)
  have hsum :
      (∑ p ∈ u,
        (p.1.1 : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹))) =
        ∑ p ∈ uNat,
          (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) := by
    dsimp only [uNat]
    symm
    exact Finset.sum_image hinj
  have hsubset : uNat ⊆ primesBetween Y Z := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨q, hqu, rfl⟩
    have hnotle : ¬q.1.1 ≤ Y := by
      simpa only [← mem_primeSubtypeUpTo] using q.2
    have hqZ : q.1.1 ≤ Z := by
      dsimp only [Z]
      exact Finset.single_le_sum (fun r _ ↦ Nat.zero_le r.1.1) hqu
    exact mem_primesBetween.mpr ⟨q.1.2, lt_of_not_ge hnotle, hqZ⟩
  rw [hsum]
  calc
    (∑ p ∈ uNat,
        (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹))) ≤
        ∑ p ∈ primesBetween Y Z,
          (p : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p hp hpu
      exact Real.rpow_nonneg (Nat.cast_nonneg p) _
    _ ≤ 4 * (Real.log 2 + primeLogIntervalMertensConstant) /
        Real.log 2 := reciprocalLog_primeRpow_tail_le hY

private theorem norm_polynomialHeightFullEulerSummand_le
    {N Y : ℕ} (ψ : DirichletCharacter ℂ N) (v : ℝ) (hY : 4 ≤ Y)
    (p : Nat.Primes) :
    ‖polynomialHeightFullEulerSummand ψ Y v p‖ ≤
      2 * (p.1 : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) := by
  let z := polynomialHeightEulerPrimeTerm ψ Y v p.1
  have hzlt : ‖z‖ < 1 / 2 :=
    norm_polynomialHeightEulerPrimeTerm_lt_half ψ v (by omega) p.2
  have hzle : ‖z‖ ≤
      (p.1 : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) := by
    unfold z polynomialHeightEulerPrimeTerm polynomialHeightEulerPoint
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.2.pos]
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, add_zero]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _)
      (ψ.norm_le_one p.1)
  have hlog := Complex.norm_log_one_add_half_le_self
    (z := -z) (by simpa only [norm_neg] using hzlt.le)
  unfold polynomialHeightFullEulerSummand
  change ‖-Complex.log (1 - z)‖ ≤ _
  rw [norm_neg]
  have hthreehalf : (3 / 2 : ℝ) ≤ 2 := by norm_num
  calc
    ‖Complex.log (1 - z)‖ = ‖Complex.log (1 + -z)‖ := by ring_nf
    _ ≤ (3 / 2 : ℝ) * ‖-z‖ := hlog
    _ ≤ 2 * ‖z‖ := by
      rw [norm_neg]
      exact mul_le_mul_of_nonneg_right hthreehalf (norm_nonneg z)
    _ ≤ 2 * (p.1 : ℝ) ^
        (-(1 + (Real.log (Y : ℝ))⁻¹)) := by gcongr

/-- The complementary logarithmic Euler tail has a uniform absolute bound
at `1 + 1 / log Y + iv`. -/
theorem tsum_norm_polynomialHeightFullEulerSummand_tail_le
    {N Y : ℕ} (ψ : DirichletCharacter ℂ N) (v : ℝ) (hY : 4 ≤ Y) :
    (∑' p : {p : Nat.Primes // p ∉ primeSubtypeUpTo Y},
      ‖polynomialHeightFullEulerSummand ψ Y v p.1‖) ≤
      8 * (Real.log 2 + primeLogIntervalMertensConstant) / Real.log 2 := by
  apply Real.tsum_le_of_sum_le (fun p ↦ norm_nonneg _)
  intro u
  have hpoint :
      (∑ p ∈ u, ‖polynomialHeightFullEulerSummand ψ Y v p.1‖) ≤
        ∑ p ∈ u,
          2 * (p.1.1 : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) := by
    exact Finset.sum_le_sum fun p hp ↦
      norm_polynomialHeightFullEulerSummand_le ψ v hY p.1
  calc
    (∑ p ∈ u, ‖polynomialHeightFullEulerSummand ψ Y v p.1‖) ≤
        ∑ p ∈ u,
          2 * (p.1.1 : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) := hpoint
    _ = 2 * (∑ p ∈ u,
          (p.1.1 : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹))) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * (4 * (Real.log 2 + primeLogIntervalMertensConstant) /
          Real.log 2) := by
      gcongr
      exact finite_primeSubtype_rpow_tail_le hY u
    _ = 8 * (Real.log 2 + primeLogIntervalMertensConstant) /
          Real.log 2 := by ring

/-- A convenient finite/full comparison with a completely explicit uniform
tail constant. -/
theorem truncatedEulerLog_le_log_norm_LSeries_add_uniform
    {N Y : ℕ} (ψ : DirichletCharacter ℂ N) (v : ℝ) (hY : 4 ≤ Y) :
    truncatedPolynomialHeightEulerLog ψ Y v ≤
      Real.log ‖L ↗ψ (polynomialHeightEulerPoint Y v)‖ +
        8 * (Real.log 2 + primeLogIntervalMertensConstant) / Real.log 2 := by
  exact (truncatedEulerLog_le_log_norm_LSeries_add_tail ψ v (by omega)).trans
    (add_le_add le_rfl
      (tsum_norm_polynomialHeightFullEulerSummand_tail_le ψ v hY))

/-! ## Consuming a high-height L-series estimate -/

/-- The bounded-conductor high-height estimate in the precise form needed
after the finite/full Euler comparison. -/
def BoundedConductorLSeriesLogBound (Q : ℕ) : Prop :=
  ∃ V₀ : ℕ, 3 ≤ V₀ ∧
    ∀ (N : ℕ), 0 < N → N ≤ Q * Q →
      ∀ (ψ : DirichletCharacter ℂ N) (σ v : ℝ),
        (V₀ : ℝ) ≤ |v| → 1 < σ → σ ≤ 2 →
          Real.log ‖L ↗ψ ((σ : ℝ) + Complex.I * (v : ℂ))‖ ≤
            (3 / 4 : ℝ) * Real.log (Real.log |v|)

/-- The weaker high-height estimate actually sufficient for the discrepancy
argument.  It asks that, for every fixed conductor cutoff, the Dirichlet
L-series on `1 < re s ≤ 2` is `o(log |im s|)`, uniformly over all characters
under that cutoff.  Classical fixed-depth Weyl differencing suffices for this
form; no Vinogradov--Korobov exponent is needed. -/
def BoundedConductorLSeriesSublinear (Q : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ V₀ : ℕ, 3 ≤ V₀ ∧
      ∀ (N : ℕ), 0 < N → N ≤ Q * Q →
        ∀ (ψ : DirichletCharacter ℂ N) (σ v : ℝ),
          (V₀ : ℝ) ≤ |v| → 1 < σ → σ ≤ 2 →
            ‖L ↗ψ ((σ : ℝ) + Complex.I * (v : ℂ))‖ ≤
              ε * Real.log |v|

/-- A bounded-conductor `3/4` high-height L-series estimate supplies the
exact `5/6` finite Euler-logarithm endpoint. -/
theorem polynomialHeightTruncatedEulerLogBound_of_lseriesLogBound
    {Q : ℕ} (hL : BoundedConductorLSeriesLogBound Q)
    (D : ℕ) (T : ℝ) :
    PolynomialHeightTruncatedEulerLogBound Q D T := by
  by_cases hQ : Q = 0
  · subst Q
    refine ⟨2, le_rfl, ?_⟩
    intro Y N hY hN hNQ
    omega
  by_cases hD : D = 0
  · subst D
    obtain ⟨M, hTM⟩ : ∃ M : ℕ, T < M := exists_nat_gt T
    refine ⟨max 2 M, le_max_left 2 M, ?_⟩
    intro Y N hY hN hNQ ψ v hvLower hvUpper
    have hMY : M ≤ Y := (le_max_right 2 M).trans hY
    have hTY : T < (Y : ℝ) := hTM.trans_le (by exact_mod_cast hMY)
    simp only [pow_zero, mul_one] at hvUpper
    exfalso
    linarith
  by_cases hT : T ≤ 0
  · refine ⟨2, le_rfl, ?_⟩
    intro Y N hY hN hNQ ψ v hvLower hvUpper
    have hpow : 0 ≤ (Y : ℝ) ^ D := by positivity
    have hupperNonpos : T * (Y : ℝ) ^ D ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hT hpow
    have hYpos : (0 : ℝ) < Y := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hY)
    exfalso
    linarith [abs_nonneg v]
  have hTpos : 0 < T := lt_of_not_ge hT
  rcases hL with ⟨V₀, hV₀, hL⟩
  let E : ℝ :=
    8 * (Real.log 2 + primeLogIntervalMertensConstant) / Real.log 2
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact div_nonneg
      (mul_nonneg (by norm_num)
        (add_nonneg (Real.log_pos one_lt_two).le
          primeLogIntervalMertensConstant_nonneg))
      (Real.log_pos one_lt_two).le
  have hDpos : 0 < D := Nat.pos_of_ne_zero hD
  have hDone : (0 : ℝ) < D + 1 := by positivity
  have hloglog : Filter.Tendsto
      (fun Y : ℕ ↦ Real.log (Real.log (Y : ℝ)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hevent : ∀ᶠ Y : ℕ in Filter.atTop,
      12 * (E + (3 / 4 : ℝ) * Real.log (D + 1)) ≤
        Real.log (Real.log (Y : ℝ)) :=
    (Filter.tendsto_atTop.1 hloglog
      (12 * (E + (3 / 4 : ℝ) * Real.log (D + 1))))
  obtain ⟨NE, hNE⟩ := Filter.eventually_atTop.1 hevent
  let Y₀ : ℕ := max V₀ (max 4 (max ⌈T⌉₊ NE))
  refine ⟨Y₀, (by omega), ?_⟩
  intro Y N hY hN hNQ ψ v hvLower hvUpper
  have hVY : V₀ ≤ Y := (le_max_left _ _).trans hY
  have h4Y : 4 ≤ Y :=
    (le_max_left 4 (max ⌈T⌉₊ NE)).trans
      ((le_max_right V₀ (max 4 (max ⌈T⌉₊ NE))).trans hY)
  have hceilY : ⌈T⌉₊ ≤ Y :=
    (le_max_left ⌈T⌉₊ NE).trans
      ((le_max_right 4 (max ⌈T⌉₊ NE)).trans
        ((le_max_right V₀ (max 4 (max ⌈T⌉₊ NE))).trans hY))
  have hNEY : NE ≤ Y :=
    (le_max_right ⌈T⌉₊ NE).trans
      ((le_max_right 4 (max ⌈T⌉₊ NE)).trans
        ((le_max_right V₀ (max 4 (max ⌈T⌉₊ NE))).trans hY))
  have hTY : T ≤ (Y : ℝ) :=
    (Nat.le_ceil T).trans (by exact_mod_cast hceilY)
  have hYR : (1 : ℝ) < Y := by exact_mod_cast (show 1 < Y by omega)
  have hlogY : 0 < Real.log (Y : ℝ) := Real.log_pos hYR
  have hlogYone : 1 ≤ Real.log (Y : ℝ) := by
    have hexpY : Real.exp 1 ≤ (Y : ℝ) := by
      exact Real.exp_one_lt_three.le.trans
        (by exact_mod_cast (show 3 ≤ Y by omega))
    have hlog := Real.log_le_log (Real.exp_pos 1) hexpY
    simpa only [Real.log_exp] using hlog
  have hsigmaLower : 1 < 1 + (Real.log (Y : ℝ))⁻¹ := by
    have := inv_pos.mpr hlogY
    linarith
  have hsigmaUpper : 1 + (Real.log (Y : ℝ))⁻¹ ≤ 2 := by
    have hinv : (Real.log (Y : ℝ))⁻¹ ≤ 1 := by
      simpa only [one_div, inv_one] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hlogYone
    linarith
  have hVYR : (V₀ : ℝ) ≤ Y := by exact_mod_cast hVY
  have hvV₀ : (V₀ : ℝ) ≤ |v| := hVYR.trans hvLower
  have hYnonneg : (0 : ℝ) ≤ Y := by positivity
  have hupperPow : |v| ≤ (Y : ℝ) ^ (D + 1) := by
    calc
      |v| ≤ T * (Y : ℝ) ^ D := hvUpper
      _ ≤ (Y : ℝ) * (Y : ℝ) ^ D := by gcongr
      _ = (Y : ℝ) ^ (D + 1) := by rw [pow_succ]; ring
  have hvPos : 0 < |v| := lt_of_lt_of_le (by positivity : (0 : ℝ) < Y) hvLower
  have hlogvPos : 0 < Real.log |v| :=
    Real.log_pos (hYR.trans_le hvLower)
  have hlogvUpper :
      Real.log |v| ≤ (D + 1 : ℕ) * Real.log (Y : ℝ) := by
    calc
      Real.log |v| ≤ Real.log ((Y : ℝ) ^ (D + 1)) :=
        Real.log_le_log hvPos hupperPow
      _ = (D + 1 : ℕ) * Real.log (Y : ℝ) := by
        rw [Real.log_pow]
  have hloglogUpper :
      Real.log (Real.log |v|) ≤
        Real.log (Real.log (Y : ℝ)) + Real.log (D + 1) := by
    calc
      Real.log (Real.log |v|) ≤
          Real.log (((D + 1 : ℕ) : ℝ) * Real.log (Y : ℝ)) :=
        Real.log_le_log hlogvPos hlogvUpper
      _ = Real.log (Real.log (Y : ℝ)) + Real.log (D + 1) := by
        rw [Real.log_mul (by exact_mod_cast hDone.ne') hlogY.ne']
        simp only [Nat.cast_add, Nat.cast_one, add_comm]
  have hLpoint := hL N hN hNQ ψ
    (1 + (Real.log (Y : ℝ))⁻¹) v hvV₀ hsigmaLower hsigmaUpper
  have hpoint :
      ((1 + (Real.log (Y : ℝ))⁻¹ : ℝ) : ℂ) +
          Complex.I * (v : ℂ) = polynomialHeightEulerPoint Y v := rfl
  rw [hpoint] at hLpoint
  have heuler := truncatedEulerLog_le_log_norm_LSeries_add_uniform ψ v h4Y
  have habsorb := hNE Y hNEY
  have htail :
      E + (3 / 4 : ℝ) * Real.log (D + 1) ≤
        (1 / 12 : ℝ) * Real.log (Real.log (Y : ℝ)) := by
    nlinarith
  dsimp only [E] at htail
  calc
    truncatedPolynomialHeightEulerLog ψ Y v ≤
        Real.log ‖L ↗ψ (polynomialHeightEulerPoint Y v)‖ +
          8 * (Real.log 2 + primeLogIntervalMertensConstant) /
            Real.log 2 := heuler
    _ ≤ (3 / 4 : ℝ) * Real.log (Real.log |v|) +
          8 * (Real.log 2 + primeLogIntervalMertensConstant) /
            Real.log 2 := by gcongr
    _ ≤ (3 / 4 : ℝ) *
          (Real.log (Real.log (Y : ℝ)) + Real.log (D + 1)) +
          8 * (Real.log 2 + primeLogIntervalMertensConstant) /
            Real.log 2 := by gcongr
    _ ≤ (5 / 6 : ℝ) * Real.log (Real.log (Y : ℝ)) := by
      nlinarith

/-- A bounded-conductor high-height L-series estimate supplies the original
polynomial-height prime-correlation bound, including all finite Euler-product
and smoothing reductions. -/
theorem polynomialHeightPrimeCorrelationBound_of_lseriesLogBound
    {Q : ℕ} (hL : BoundedConductorLSeriesLogBound Q)
    (D : ℕ) (T : ℝ) :
    PolynomialHeightPrimeCorrelationBound Q D T :=
  polynomialHeightPrimeCorrelationBound_of_truncatedEulerLogBound
    (polynomialHeightTruncatedEulerLogBound_of_lseriesLogBound hL D T)

/-- Uniform bounded-conductor L-series estimates provide the exact eventual
two-scale twist-separation input consumed by the Section 4 assembly. -/
theorem eventuallyTwoScaleTwistSeparation_of_lseriesLogBound
    (hL : ∀ Q : ℕ, BoundedConductorLSeriesLogBound Q) :
    EventuallyTwoScaleTwistSeparation :=
  eventuallyTwoScaleTwistSeparation_of_polynomialHeight fun A D _ _ ↦
    polynomialHeightPrimeCorrelationBound_of_lseriesLogBound
      (hL A) D (2 * A : ℕ)

/-! ## The weaker little-oh endpoint -/

/-- Uniform `o(log |t|)` bounds already separate bounded-conductor twists.
For fixed `A,D`, choose the little-oh coefficient exponentially small in
`A` and in the finite Euler/Mertens comparison constants.  The resulting
constant deficit from the full prime mass is at least `4*A`. -/
theorem eventually_twoScaleTwistSeparationConclusion_of_lseriesSublinear
    {A D : ℕ} (hD : 0 < D)
    (hL : BoundedConductorLSeriesSublinear A) :
    ∃ Y₀ : ℕ, 2 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      TwoScaleTwistSeparationConclusion A Y D := by
  let E : ℝ :=
    8 * (Real.log 2 + primeLogIntervalMertensConstant) / Real.log 2
  let K : ℝ := E + polynomialHeightPrimePowerRemainderBound +
    polynomialHeightWeightRemovalBound
  let C : ℝ := (4 : ℝ) * A + PrimeEstimates.mertensBound +
    Real.log (D + 1) + K
  let ε : ℝ := Real.exp (-C)
  have hε : 0 < ε := by simp only [ε]; positivity
  obtain ⟨V₀, hV₀, hL⟩ := hL ε hε
  let Y₀ : ℕ := max V₀ (max 4 (2 * A))
  refine ⟨Y₀, (by omega), ?_⟩
  intro Y hY
  have hVY : V₀ ≤ Y := (le_max_left _ _).trans hY
  have h4Y : 4 ≤ Y :=
    (le_max_left 4 (2 * A)).trans
      ((le_max_right V₀ (max 4 (2 * A))).trans hY)
  have hAY : 2 * A ≤ Y :=
    (le_max_right 4 (2 * A)).trans
      ((le_max_right V₀ (max 4 (2 * A))).trans hY)
  have hYR : (1 : ℝ) < Y := by exact_mod_cast (show 1 < Y by omega)
  have hlogY : 0 < Real.log (Y : ℝ) := Real.log_pos hYR
  have hlogYone : 1 ≤ Real.log (Y : ℝ) := by
    have hexpY : Real.exp 1 ≤ (Y : ℝ) := by
      exact Real.exp_one_lt_three.le.trans
        (by exact_mod_cast (show 3 ≤ Y by omega))
    have hlog := Real.log_le_log (Real.exp_pos 1) hexpY
    simpa only [Real.log_exp] using hlog
  have hsigmaLower : 1 < 1 + (Real.log (Y : ℝ))⁻¹ := by
    have := inv_pos.mpr hlogY
    linarith
  have hsigmaUpper : 1 + (Real.log (Y : ℝ))⁻¹ ≤ 2 := by
    have hinv : (Real.log (Y : ℝ))⁻¹ ≤ 1 := by
      simpa only [one_div, inv_one] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hlogYone
    linarith
  apply twoScaleTwistSeparationConclusion_of_characterTwistDistSq_lower
    (by omega : 2 ≤ Y) hD
  intro q hq hqA χ q' hq' hq'A χ' v hvLower hvUpper
  let N : ℕ := q * q'
  let ψ : DirichletCharacter ℂ N := quotientCharacter χ χ'
  have hN : 0 < N := by dsimp only [N]; positivity
  have hNle : N ≤ A * A := by
    dsimp only [N]
    exact Nat.mul_le_mul hqA hq'A
  have hVYR : (V₀ : ℝ) ≤ Y := by exact_mod_cast hVY
  have hvV₀ : (V₀ : ℝ) ≤ |v| := hVYR.trans hvLower
  have hAYR : (2 : ℝ) * A ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hupperPow : |v| ≤ (Y : ℝ) ^ (D + 1) := by
    calc
      |v| ≤ (2 * A : ℕ) * (Y ^ D : ℕ) := hvUpper
      _ ≤ (Y : ℝ) * (Y : ℝ) ^ D := by
        push_cast
        exact mul_le_mul_of_nonneg_right hAYR (by positivity)
      _ = (Y : ℝ) ^ (D + 1) := by
        rw [pow_succ]
        ring
  have hvPos : 0 < |v| :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < Y) hvLower
  have hlogvPos : 0 < Real.log |v| :=
    Real.log_pos (hYR.trans_le hvLower)
  have hlogvUpper :
      Real.log |v| ≤ (D + 1 : ℕ) * Real.log (Y : ℝ) := by
    calc
      Real.log |v| ≤ Real.log ((Y : ℝ) ^ (D + 1)) :=
        Real.log_le_log hvPos hupperPow
      _ = (D + 1 : ℕ) * Real.log (Y : ℝ) := by
        rw [Real.log_pow]
  have hDOne : (0 : ℝ) < D + 1 := by positivity
  have hloglogUpper :
      Real.log (Real.log |v|) ≤
        Real.log (Real.log (Y : ℝ)) + Real.log (D + 1) := by
    calc
      Real.log (Real.log |v|) ≤
          Real.log (((D + 1 : ℕ) : ℝ) * Real.log (Y : ℝ)) :=
        Real.log_le_log hlogvPos hlogvUpper
      _ = Real.log (Real.log (Y : ℝ)) + Real.log (D + 1) := by
        rw [Real.log_mul (by exact_mod_cast hDOne.ne') hlogY.ne']
        simp only [Nat.cast_add, Nat.cast_one, add_comm]
  have hLvalue := hL N hN hNle ψ
    (1 + (Real.log (Y : ℝ))⁻¹) v hvV₀ hsigmaLower hsigmaUpper
  have hpoint :
      ((1 + (Real.log (Y : ℝ))⁻¹ : ℝ) : ℂ) +
          Complex.I * (v : ℂ) = polynomialHeightEulerPoint Y v := rfl
  rw [hpoint] at hLvalue
  have hpointRe : (polynomialHeightEulerPoint Y v).re =
      1 + (Real.log (Y : ℝ))⁻¹ := by
    rw [polynomialHeightEulerPoint]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero,
      sub_zero, add_zero]
  have hLne : L ↗ψ (polynomialHeightEulerPoint Y v) ≠ 0 :=
    DirichletCharacter.LSeries_ne_zero_of_one_lt_re ψ
      (by rw [hpointRe]; exact hsigmaLower)
  have hnormPos : 0 < ‖L ↗ψ (polynomialHeightEulerPoint Y v)‖ :=
    norm_pos_iff.mpr hLne
  have hprodPos : 0 < ε * Real.log |v| := mul_pos hε hlogvPos
  have hlogNorm :
      Real.log ‖L ↗ψ (polynomialHeightEulerPoint Y v)‖ ≤
        -C + Real.log (Real.log |v|) := by
    calc
      Real.log ‖L ↗ψ (polynomialHeightEulerPoint Y v)‖ ≤
          Real.log (ε * Real.log |v|) :=
        Real.log_le_log hnormPos hLvalue
      _ = Real.log ε + Real.log (Real.log |v|) := by
        rw [Real.log_mul hε.ne' hlogvPos.ne']
      _ = -C + Real.log (Real.log |v|) := by
        simp only [ε, Real.log_exp]
  have heuler := truncatedEulerLog_le_log_norm_LSeries_add_uniform ψ v h4Y
  have hlinear := truncatedEulerLinear_le_log_add_remainder
    (Y := Y) ψ v (by omega)
  have hcorr := quotientCorrelation_le_eulerLinear_add_weightBound
    (Y := Y) hq hq' χ χ' v (by omega)
  have hcorrFinal :
      characterTwistPrimeCorrelation χ χ' v Y ≤
        Real.log (Real.log (Y : ℝ)) -
          PrimeEstimates.mertensBound - (4 : ℝ) * A := by
    calc
      characterTwistPrimeCorrelation χ χ' v Y ≤
          truncatedPolynomialHeightEulerLinear ψ Y v +
            polynomialHeightWeightRemovalBound := by
        simpa only [ψ, N] using hcorr
      _ ≤ truncatedPolynomialHeightEulerLog ψ Y v +
            polynomialHeightPrimePowerRemainderBound +
            polynomialHeightWeightRemovalBound := by
        gcongr
      _ ≤ Real.log ‖L ↗ψ (polynomialHeightEulerPoint Y v)‖ + E +
            polynomialHeightPrimePowerRemainderBound +
            polynomialHeightWeightRemovalBound := by
        dsimp only [E]
        gcongr
      _ ≤ (-C + Real.log (Real.log |v|)) + K := by
        dsimp only [K]
        linarith
      _ ≤ (-C +
            (Real.log (Real.log (Y : ℝ)) + Real.log (D + 1))) + K := by
        gcongr
      _ = Real.log (Real.log (Y : ℝ)) -
            PrimeEstimates.mertensBound - (4 : ℝ) * A := by
        dsimp only [C]
        ring
  rw [characterTwistDistSq_eq_mass_sub_correlation]
  have hmass := characterTwistPrimeMass_mertens_lower (Y := Y) (by omega)
  push_cast
  linarith

/-- A uniform family of little-oh L-series bounds is the sole analytic input
needed by the eventual Section 4 twist-separation package. -/
theorem eventuallyTwoScaleTwistSeparation_of_lseriesSublinear
    (hL : ∀ Q : ℕ, BoundedConductorLSeriesSublinear Q) :
    EventuallyTwoScaleTwistSeparation := by
  intro A D hA hD
  obtain ⟨Y₀, hY₀, hsep⟩ :=
    eventually_twoScaleTwistSeparationConclusion_of_lseriesSublinear
      hD (hL A)
  refine ⟨Y₀, ?_⟩
  intro K hY₀K
  apply hsep (4 ^ K)
  calc
    Y₀ ≤ K := hY₀K
    _ ≤ 2 ^ K := K.lt_two_pow_self.le
    _ ≤ 4 ^ K := Nat.pow_le_pow_left (by norm_num) K

end

end Erdos67
