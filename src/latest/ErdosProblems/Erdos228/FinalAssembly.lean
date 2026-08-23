import ErdosProblems.Erdos228.Basic
import ErdosProblems.Erdos228.Target
import ErdosProblems.Erdos228.Assembly

/-!
# Final assembly for Erdős Problem 228

This file contains the purely algebraic last step of the BBMST construction.
It has two deliberately narrow interfaces:

* `CenteredPairedInput` records the signed coefficients of a centered Laurent
  polynomial together with its already assembled cosine/even-sine/odd-sine
  value;
* `EventuallyCenteredPaired` says that these inputs have been constructed for
  every sufficiently large scale.

The first interface is discharged by the cosine and odd-sine construction
modules.  Everything after it--shifting the Laurent polynomial, filling the
last zero, one, two, or three degrees, and changing square-root scales--is
proved here.
-/

namespace Erdos228

open Filter
open scoped BigOperators

noncomputable section

/-- A length-`2 * pi` interval containing exactly the four real
representatives of the symmetric dangerous arcs used in the construction.
The analytic construction works on the circle quotient; keeping this
fundamental interval explicit prevents accidentally asking a bounded union of
real intervals to be periodic as a predicate on all of `ℝ`. -/
def InFundamentalAngle (theta : ℝ) : Prop :=
  theta ∈ Set.Icc (-Real.pi / 2) (3 * Real.pi / 2)

/-! ## Appending at most three sign coefficients -/

/-- A block of `r` consecutive monomials with coefficient `1`, immediately
after degree `base`. -/
def oneTail (base r : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range r, Polynomial.monomial (base + 1 + j) 1

theorem coeff_oneTail (base r i : ℕ) :
    (oneTail base r).coeff i =
      if base < i ∧ i ≤ base + r then 1 else 0 := by
  classical
  change Polynomial.lcoeff ℂ i
      (∑ j ∈ Finset.range r, Polynomial.monomial (base + 1 + j) 1) = _
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
  by_cases hi : base < i ∧ i ≤ base + r
  · rw [if_pos hi]
    have hj : i - (base + 1) < r := by omega
    rw [Finset.sum_eq_single (i - (base + 1))]
    · have heq : base + 1 + (i - (base + 1)) = i := by omega
      simp [heq]
    · intro b hb hne
      rw [if_neg]
      intro heq
      apply hne
      omega
    · simp [hj]
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg]
    intro heq
    apply hi
    simp only [Finset.mem_range] at hj
    omega

/-- Append a consecutive block of `1` coefficients after the old degree. -/
def appendOnes (base r : ℕ) (p : Polynomial ℂ) : Polynomial ℂ :=
  p + oneTail base r

theorem coeff_appendOnes_of_le {base r i : ℕ} {p : Polynomial ℂ}
    (hi : i ≤ base) :
    (appendOnes base r p).coeff i = p.coeff i := by
  rw [appendOnes, Polynomial.coeff_add, coeff_oneTail]
  simp [show ¬base < i by omega]

theorem coeff_appendOnes_of_lt_le {base r i : ℕ} {p : Polynomial ℂ}
    (hp : p.degree = base) (hlo : base < i) (hhi : i ≤ base + r) :
    (appendOnes base r p).coeff i = 1 := by
  rw [appendOnes, Polynomial.coeff_add, coeff_oneTail, if_pos ⟨hlo, hhi⟩]
  have hpzero : p.coeff i = 0 := by
    apply Polynomial.coeff_eq_zero_of_degree_lt
    rw [hp]
    exact_mod_cast hlo
  rw [hpzero, zero_add]

theorem degree_appendOnes {base r : ℕ} {p : Polynomial ℂ}
    (hp : p.degree = base) :
    (appendOnes base r p).degree = base + r := by
  apply Polynomial.degree_eq_of_le_of_coeff_ne_zero (n := base + r)
  · rw [Polynomial.degree_le_iff_coeff_zero]
    intro i hi
    have hisum : base + r < i := by exact_mod_cast hi
    rw [appendOnes, Polynomial.coeff_add, coeff_oneTail]
    have hibase : base < i := by omega
    have htail : ¬(base < i ∧ i ≤ base + r) := by omega
    rw [if_neg htail]
    simp only [add_zero]
    apply Polynomial.coeff_eq_zero_of_degree_lt
    rw [hp]
    exact_mod_cast hibase
  · by_cases hr : r = 0
    · subst r
      simpa only [Nat.add_zero, appendOnes, oneTail, Finset.range_zero,
        Finset.sum_empty, add_zero] using
        (show p.coeff base ≠ 0 by
          apply Polynomial.coeff_ne_zero_of_eq_degree hp)
    · rw [coeff_appendOnes_of_lt_le hp (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hr)) le_rfl]
      norm_num

theorem isLittlewood_appendOnes {base r : ℕ} {p : Polynomial ℂ}
    (hp : IsLittlewood base p) :
    IsLittlewood (base + r) (appendOnes base r p) := by
  constructor
  · exact degree_appendOnes hp.1
  · intro i hi
    by_cases hibase : i ≤ base
    · rw [coeff_appendOnes_of_le hibase]
      exact hp.2 i hibase
    · rw [coeff_appendOnes_of_lt_le hp.1 (Nat.lt_of_not_ge hibase) hi]
      exact Or.inl rfl

theorem eval_oneTail (base r : ℕ) (z : ℂ) :
    (oneTail base r).eval z = ∑ j ∈ Finset.range r, z ^ (base + 1 + j) := by
  simp [oneTail, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem norm_eval_oneTail_le {base r : ℕ} {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(oneTail base r).eval z‖ ≤ r := by
  rw [eval_oneTail]
  calc
    ‖∑ j ∈ Finset.range r, z ^ (base + 1 + j)‖ ≤
        ∑ j ∈ Finset.range r, ‖z ^ (base + 1 + j)‖ := norm_sum_le _ _
    _ = ∑ _j ∈ Finset.range r, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [norm_pow, hz]
    _ = r := by simp

theorem norm_eval_appendOnes_upper {base r : ℕ} {p : Polynomial ℂ}
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(appendOnes base r p).eval z‖ ≤ ‖p.eval z‖ + r := by
  rw [appendOnes, Polynomial.eval_add]
  calc
    ‖p.eval z + (oneTail base r).eval z‖ ≤
        ‖p.eval z‖ + ‖(oneTail base r).eval z‖ := norm_add_le _ _
    _ ≤ ‖p.eval z‖ + r := by
      gcongr
      exact norm_eval_oneTail_le hz

theorem norm_eval_appendOnes_lower {base r : ℕ} {p : Polynomial ℂ}
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖p.eval z‖ - r ≤ ‖(appendOnes base r p).eval z‖ := by
  have htri : ‖p.eval z‖ ≤
      ‖(appendOnes base r p).eval z‖ + ‖(oneTail base r).eval z‖ := by
    calc
      ‖p.eval z‖ =
          ‖(appendOnes base r p).eval z - (oneTail base r).eval z‖ := by
            congr 1
            simp [appendOnes]
      _ ≤ _ := norm_sub_le _ _
  linarith [norm_eval_oneTail_le (base := base) (r := r) hz]

/-! ## Centered paired input -/

/-- The exact output needed from the cosine/even-sine/odd-sine construction.
The coefficient vector is already shifted from exponents `[-2n,2n]` to
`[0,4n]`.  The evaluation identity says that removing the harmless phase
`z^(2n)` gives the paired value proved in `Assembly.lean`.

Keeping the coefficient vector in this interface makes the final theorem
depend on actual signs, rather than on a bare analytic existence statement. -/
structure CenteredPairedInput (n : ℕ) where
  coeff : Fin (4 * n + 1) → ℂ
  coeff_isSign : ∀ j, IsSign (coeff j)
  cosine : ℝ → ℝ
  evenSine : ℝ → ℝ
  oddSine : ℝ → ℝ
  dangerous : ℝ → Prop
  eval_eq : ∀ theta,
    (ofCoeffs (4 * n) coeff).eval (unitPoint theta) =
      unitPoint theta ^ (2 * n) *
        assembledValue (cosine theta) (evenSine theta) (oddSine theta)
  cosine_upper : ∀ theta, |cosine theta| ≤ Real.sqrt n
  evenSine_upper : ∀ theta, |evenSine theta| ≤ 6 * Real.sqrt n
  oddSine_upper : ∀ theta, |oddSine theta| ≤ 2 ^ 10 * Real.sqrt n
  cosine_lower_off_dangerous : ∀ theta, InFundamentalAngle theta →
    ¬ dangerous theta →
    (1 / 2 ^ 160 : ℝ) * Real.sqrt n + 1 ≤ 2 * |cosine theta|
  oddSine_lower_on_dangerous : ∀ theta, InFundamentalAngle theta →
    dangerous theta →
    10 * Real.sqrt n ≤ |oddSine theta|

/-- The ordinary polynomial obtained by multiplying the centered Laurent
polynomial by `z^(2n)`.  The shift is already reflected in the indexing of
`CenteredPairedInput.coeff`. -/
def CenteredPairedInput.polynomial {n : ℕ} (A : CenteredPairedInput n) :
    Polynomial ℂ :=
  ofCoeffs (4 * n) A.coeff

theorem CenteredPairedInput.isLittlewood {n : ℕ}
    (A : CenteredPairedInput n) : IsLittlewood (4 * n) A.polynomial := by
  exact isLittlewood_ofCoeffs (4 * n) A.coeff A.coeff_isSign

theorem CenteredPairedInput.norm_eval_eq {n : ℕ}
    (A : CenteredPairedInput n) (theta : ℝ) :
    ‖A.polynomial.eval (unitPoint theta)‖ =
      ‖assembledValue (A.cosine theta) (A.evenSine theta) (A.oddSine theta)‖ := by
  rw [CenteredPairedInput.polynomial, A.eval_eq, norm_mul, norm_pow,
    norm_unitPoint, one_pow, one_mul]

theorem CenteredPairedInput.flat_on_parametrized_circle {n : ℕ}
    (hn : 1 ≤ n) (A : CenteredPairedInput n) (theta : ℝ)
    (htheta : InFundamentalAngle theta) :
    (1 / 2 ^ 160 : ℝ) * Real.sqrt n ≤
        ‖A.polynomial.eval (unitPoint theta)‖ ∧
      ‖A.polynomial.eval (unitPoint theta)‖ ≤
        2 ^ 12 * Real.sqrt n := by
  rw [A.norm_eval_eq]
  constructor
  · by_cases hdanger : A.dangerous theta
    · have hbig := eight_sqrt_le_norm_assembledValue_of_odd_sine
          (c := A.cosine theta)
          (A.evenSine_upper theta)
          (A.oddSine_lower_on_dangerous theta htheta hdanger)
      have hsqrt : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
      norm_num at hbig ⊢
      nlinarith
    · have hcos := two_mul_abs_sub_one_le_norm_assembledValue
          (A.cosine theta) (A.evenSine theta) (A.oddSine theta)
      have hlower := A.cosine_lower_off_dangerous theta htheta hdanger
      norm_num at hlower ⊢
      linarith
  · exact norm_assembledValue_le_two_pow_twelve_sqrt hn
      (A.cosine_upper theta) (A.evenSine_upper theta) (A.oddSine_upper theta)

/-! ## Removing the unit-circle parametrization -/

theorem exists_unitPoint_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ theta : ℝ, unitPoint theta = z := by
  obtain ⟨theta, htheta⟩ := (Complex.norm_eq_one_iff z).1 hz
  exact ⟨theta, by simpa [unitPoint] using htheta⟩

@[simp] theorem unitPoint_add_two_pi (theta : ℝ) :
    unitPoint (theta + 2 * Real.pi) = unitPoint theta := by
  unfold unitPoint
  rw [show (((theta + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
      (theta : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I by
        push_cast
        ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- Every point of the unit circle has a representative in the fundamental
interval used by the cosine and odd-sine estimates. -/
theorem exists_fundamental_unitPoint_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ theta : ℝ, InFundamentalAngle theta ∧ unitPoint theta = z := by
  let a := z.arg
  have haLower : -Real.pi < a := Complex.neg_pi_lt_arg z
  have haUpper : a ≤ Real.pi := Complex.arg_le_pi z
  have haPoint : unitPoint a = z := by
    calc
      unitPoint a = Complex.exp ((a : ℂ) * Complex.I) := rfl
      _ = ‖z‖ * Complex.exp ((a : ℂ) * Complex.I) := by rw [hz]; simp
      _ = z := Complex.norm_mul_exp_arg_mul_I z
  by_cases ha : -Real.pi / 2 ≤ a
  · refine ⟨a, ⟨ha, ?_⟩, haPoint⟩
    nlinarith [Real.pi_pos]
  · refine ⟨a + 2 * Real.pi, ⟨?_, ?_⟩, ?_⟩
    · nlinarith [Real.pi_pos]
    · nlinarith [lt_of_not_ge ha]
    · rw [unitPoint_add_two_pi]
      exact haPoint

theorem CenteredPairedInput.flat_on_circle {n : ℕ}
    (hn : 1 ≤ n) (A : CenteredPairedInput n) :
    ∀ z : ℂ, ‖z‖ = 1 →
      (1 / 2 ^ 160 : ℝ) * Real.sqrt n ≤ ‖A.polynomial.eval z‖ ∧
      ‖A.polynomial.eval z‖ ≤ 2 ^ 12 * Real.sqrt n := by
  intro z hz
  obtain ⟨theta, htheta, rfl⟩ :=
    exists_fundamental_unitPoint_of_norm_eq_one hz
  exact A.flat_on_parametrized_circle hn theta htheta

/-! ## From degrees divisible by four to every large degree -/

private theorem sqrt_sixteen_mul (n : ℕ) :
    Real.sqrt (16 * (n : ℝ)) = 4 * Real.sqrt n := by
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 16)]
  norm_num

private theorem sqrt_mono_nat {a b : ℕ} (h : a ≤ b) :
    Real.sqrt a ≤ Real.sqrt b := by
  exact Real.sqrt_le_sqrt (by exact_mod_cast h)

/-- Starting with the degree `4*(d/4)` centered construction and appending
`d%4` leading `1` coefficients gives a degree-`d` Littlewood polynomial.  The
explicit absorption hypothesis is eventual because its left side tends to
infinity with `d`. -/
theorem extend_centered_to_degree (d : ℕ)
    (hn : 1 ≤ d / 4) (A : CenteredPairedInput (d / 4))
    (habsorb : 3 ≤ (1 / 2 ^ 163 : ℝ) * Real.sqrt d) :
    ∃ p : Polynomial ℂ, IsLittlewood d p ∧
      HasFlatBounds (1 / 2 ^ 163) (2 ^ 13) d p := by
  let n := d / 4
  let r := d % 4
  let q := A.polynomial
  let p := appendOnes (4 * n) r q
  have hr : r ≤ 3 := by
    dsimp [r]
    omega
  have hdecomp : 4 * n + r = d := by
    dsimp [n, r]
    omega
  have hqLittlewood : IsLittlewood (4 * n) q := by
    exact A.isLittlewood
  have hpLittlewood : IsLittlewood d p := by
    rw [← hdecomp]
    exact isLittlewood_appendOnes hqLittlewood
  refine ⟨p, hpLittlewood, ?_⟩
  intro z hz
  have hqflat := A.flat_on_circle hn z hz
  have hnle : n ≤ d := by
    dsimp [n]
    omega
  have hdle : d ≤ 16 * n := by
    rw [← hdecomp]
    omega
  have hsqrt_nd : Real.sqrt n ≤ Real.sqrt d := sqrt_mono_nat hnle
  have hsqrt_dn : Real.sqrt d ≤ 4 * Real.sqrt n := by
    calc
      Real.sqrt d ≤ Real.sqrt (16 * (n : ℝ)) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using sqrt_mono_nat hdle
      _ = 4 * Real.sqrt n := sqrt_sixteen_mul n
  have hsqrt_nonneg : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hsqrt_three : 3 ≤ Real.sqrt d := by
    have hfactor : (1 / 2 ^ 163 : ℝ) ≤ 1 := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hfactor hsqrt_nonneg]
  constructor
  · have htail := norm_eval_appendOnes_lower
        (base := 4 * n) (r := r) (p := q) hz
    change ‖q.eval z‖ - (r : ℝ) ≤ ‖p.eval z‖ at htail
    have hrR : (r : ℝ) ≤ 3 := by exact_mod_cast hr
    have hscale : (1 / 2 ^ 162 : ℝ) * Real.sqrt d ≤
        (1 / 2 ^ 160 : ℝ) * Real.sqrt n := by
      norm_num at ⊢
      nlinarith
    norm_num at hqflat habsorb ⊢
    nlinarith
  · have htail := norm_eval_appendOnes_upper
        (base := 4 * n) (r := r) (p := q) hz
    change ‖p.eval z‖ ≤ ‖q.eval z‖ + (r : ℝ) at htail
    have hrR : (r : ℝ) ≤ 3 := by exact_mod_cast hr
    norm_num at hqflat ⊢
    nlinarith

/-! ## Eventual construction and the exact target -/

/-- The sole eventual construction input expected from the analytic modules:
for every sufficiently large scale they produce actual centered sign
coefficients and the cosine/sine bounds recorded in `CenteredPairedInput`. -/
def EventuallyCenteredPaired : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, Nonempty (CenteredPairedInput n)

private theorem eventually_absorb_three :
    ∀ᶠ d : ℕ in Filter.atTop,
      3 ≤ (1 / 2 ^ 163 : ℝ) * Real.sqrt d := by
  have hsqrt : Filter.Tendsto (fun d : ℕ ↦ Real.sqrt (d : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hscaled : Filter.Tendsto
      (fun d : ℕ ↦ (1 / 2 ^ 163 : ℝ) * Real.sqrt d)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) hsqrt
  exact hscaled (eventually_ge_atTop 3)

/-- The centered construction supplies a uniform eventual family at every
degree.  The remainder `d % 4` is the only reason for the harmless loss from
`2^-160,2^12` to `2^-163,2^13`. -/
theorem eventually_flat_of_eventually_centered
    (hcentered : EventuallyCenteredPaired) :
    ∀ᶠ d : ℕ in Filter.atTop, ∃ p : Polynomial ℂ,
      IsLittlewood d p ∧
      HasFlatBounds (1 / 2 ^ 163) (2 ^ 13) d p := by
  rw [EventuallyCenteredPaired, eventually_atTop] at hcentered
  obtain ⟨N, hN⟩ := hcentered
  filter_upwards [eventually_ge_atTop (4 * max N 1), eventually_absorb_three]
    with d hd habsorb
  have hnN : N ≤ d / 4 := by omega
  have hn1 : 1 ≤ d / 4 := by omega
  obtain ⟨A⟩ := hN (d / 4) hnN
  exact extend_centered_to_degree d hn1 A habsorb

/-- Exact formal-conjectures conclusion, directly from the concrete centered
construction input. -/
theorem target_of_eventually_centered (hcentered : EventuallyCenteredPaired) :
    ∃ (c₁ : ℝ) (c₂ : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
    ∃ p : Polynomial ℂ, p.degree = n ∧
    (∀ i ≤ n, p.coeff i = 1 ∨ p.coeff i = -1) ∧
    ∀ z : ℂ, ‖z‖ = 1 →
    (Real.sqrt n < c₁ * ‖p.eval z‖ ∧
      ‖p.eval z‖ < c₂ * Real.sqrt n) := by
  refine Iff.mp ?_ trivial
  constructor
  · intro _
    have hflat := eventually_flat_of_eventually_centered hcentered
    have hstrict := eventually_strict_of_eventually_flat
      (delta := (1 / 2 ^ 163 : ℝ)) (Delta := (2 ^ 13 : ℝ))
      (by positivity) (by positivity) hflat
    exact ⟨2 / (1 / 2 ^ 163 : ℝ), 2 * (2 ^ 13 : ℝ), hstrict⟩
  · intro _
    trivial

end

end Erdos228
