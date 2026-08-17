/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos175.Vaughan

/-!
# The four-sum form of Vaughan's identity used by Granville--Ramaré

This is the exact algebraic content of Lemma 9.1 in Granville--Ramaré.  Put

`a = μ_{≤ M} * ζ`,  `b = μ_{≤ M} * Λ_{≤ K}`.

Split `b` at `M` into `bLow + bHigh`, and remove the convolution identity
coefficient from `a` by writing `a = 1 + aHigh`.  Then

`Λ_{> K} = μ_{≤ M} * log - ζ * bLow - ζ * bHigh - Λ_{> K} * aHigh`.

On an interval `(y,y']` with `K ≤ y`, `Λ = Λ_{>K}` term by term.  Applying
an arbitrary finite weight therefore gives the paper's signed decomposition

`Σ Λ(n)f(n) = Σ₁ - Σ₂,₁ - Σ₂,₂ - Σ₃`.

For the application the weight is `e(x/n)`, but the algebraic theorem is
stated for every complex-valued weight.
-/

noncomputable section

namespace Erdos175.VaughanFourSums

open scoped ArithmeticFunction BigOperators

open Vaughan

/-- `a_l = ∑_{m r = l, m ≤ M} μ(m)`. -/
def aCoeff (M : ℕ) : ArithmeticFunction ℝ :=
  muLow M * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)

/-- The portion of `a_l` with `l > M`; below this cutoff the full coefficient
is exactly the Dirichlet-convolution identity. -/
def aHigh (M : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun l => if M < l then aCoeff M l else 0, by simp [aCoeff]⟩

/-- `b_r = ∑_{m k = r, m ≤ M, k ≤ K} μ(m) Λ(k)`. -/
def bCoeff (M K : ℕ) : ArithmeticFunction ℝ :=
  muLow M * lambdaLow K

/-- The part of `b_r` with `r ≤ M`. -/
def bLow (M K : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun r => if r ≤ M then bCoeff M K r else 0, by simp [bCoeff]⟩

/-- The part of `b_r` with `M < r`.  The convolution defining `bCoeff`
automatically vanishes beyond `M*K`. -/
def bHigh (M K : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun r => if M < r then bCoeff M K r else 0, by simp [bCoeff]⟩

/-- The first paper term, `μ_{≤M} * log`. -/
def sigma1AF (M : ℕ) : ArithmeticFunction ℝ :=
  muLow M * ArithmeticFunction.log

/-- The part of `ζ * b` with `r ≤ M`. -/
def sigma21AF (M K : ℕ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * bLow M K

/-- The part of `ζ * b` with `M < r ≤ MK`. -/
def sigma22AF (M K : ℕ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * bHigh M K

/-- The Type-II paper term, `Λ_{>K} * a_{>M}`. -/
def sigma3AF (M K : ℕ) : ArithmeticFunction ℝ :=
  lambdaHigh K * aHigh M

/-- Below `M`, `a_l` is the convolution identity. -/
theorem aCoeff_eq_one_of_le {M l : ℕ} (hM : 1 ≤ M) (hl : l ≤ M) :
    aCoeff M l = (1 : ArithmeticFunction ℝ) l := by
  rcases Nat.eq_zero_or_pos l with rfl | hlpos
  · simp [aCoeff, ArithmeticFunction.map_zero]
  · rw [aCoeff, ArithmeticFunction.coe_mul_zeta_apply]
    calc
      ∑ d ∈ l.divisors, muLow M d =
          ∑ d ∈ l.divisors, (ArithmeticFunction.moebius d : ℝ) := by
        refine Finset.sum_congr rfl fun d hd => ?_
        change (if d ≤ M then (ArithmeticFunction.moebius d : ℝ) else 0) =
          (ArithmeticFunction.moebius d : ℝ)
        rw [if_pos ((Nat.divisor_le hd).trans hl)]
      _ = (((ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) l) := by
        rw [ArithmeticFunction.coe_mul_zeta_apply]
        simp
      _ = (1 : ArithmeticFunction ℝ) l := by
        rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]

/-- The exact decomposition `a = 1 + aHigh`. -/
theorem one_add_aHigh (M : ℕ) (hM : 1 ≤ M) :
    (1 : ArithmeticFunction ℝ) + aHigh M = aCoeff M := by
  ext l
  by_cases hl : l ≤ M
  · have hnot : ¬ M < l := not_lt.mpr hl
    change (1 : ArithmeticFunction ℝ) l +
        (if M < l then aCoeff M l else 0) = aCoeff M l
    rw [if_neg hnot, add_zero, aCoeff_eq_one_of_le hM hl]
  · have hlt : M < l := lt_of_not_ge hl
    have hlone : (1 : ArithmeticFunction ℝ) l = 0 := by
      have hlne : l ≠ 1 := by omega
      simp [hlne]
    change (1 : ArithmeticFunction ℝ) l +
        (if M < l then aCoeff M l else 0) = aCoeff M l
    rw [if_pos hlt, hlone, zero_add]

/-- The two ranges of the `b` coefficient form all of `b`. -/
theorem bLow_add_bHigh (M K : ℕ) :
    bLow M K + bHigh M K = bCoeff M K := by
  ext r
  change (if r ≤ M then bCoeff M K r else 0) +
      (if M < r then bCoeff M K r else 0) = bCoeff M K r
  by_cases hr : r ≤ M
  · simp [hr, not_lt.mpr hr]
  · simp [hr, lt_of_not_ge hr]

/-- Every truncated Möbius coefficient has absolute value at most one. -/
lemma abs_muLow_le_one (M m : ℕ) : |muLow M m| ≤ (1 : ℝ) := by
  unfold muLow
  by_cases hm : m ≤ M
  · simp [hm]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := m)
  · simp [hm]

/-- Truncation preserves nonnegativity of the von Mangoldt function. -/
lemma lambdaLow_nonneg (K k : ℕ) : 0 ≤ lambdaLow K k := by
  change 0 ≤ if k ≤ K then ArithmeticFunction.vonMangoldt k else 0
  by_cases hk : k ≤ K
  · simp [hk, ArithmeticFunction.vonMangoldt_nonneg]
  · simp [hk]

/-- The truncated von Mangoldt function is bounded by the full function. -/
lemma lambdaLow_le (K k : ℕ) :
    lambdaLow K k ≤ ArithmeticFunction.vonMangoldt k := by
  change (if k ≤ K then ArithmeticFunction.vonMangoldt k else 0) ≤
    ArithmeticFunction.vonMangoldt k
  by_cases hk : k ≤ K
  · simp [hk]
  · simp [hk, ArithmeticFunction.vonMangoldt_nonneg]

/-- Granville--Ramaré's elementary coefficient estimate
`|b_r| ≤ log r`.  The proof uses only `|μ| ≤ 1`, positivity of `Λ`, and
`∑_{d∣r} Λ(d) = log r`; hence both truncations may be completely arbitrary. -/
theorem abs_bCoeff_le_log (M K r : ℕ) :
    |bCoeff M K r| ≤ Real.log r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [bCoeff, ArithmeticFunction.map_zero]
  · rw [bCoeff, ArithmeticFunction.mul_apply]
    calc
      |∑ mk ∈ r.divisorsAntidiagonal,
          muLow M mk.1 * lambdaLow K mk.2| ≤
          ∑ mk ∈ r.divisorsAntidiagonal,
            |muLow M mk.1 * lambdaLow K mk.2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ mk ∈ r.divisorsAntidiagonal,
          ArithmeticFunction.vonMangoldt mk.2 := by
        refine Finset.sum_le_sum fun mk _hmk => ?_
        rw [abs_mul, abs_of_nonneg (lambdaLow_nonneg K mk.2)]
        calc
          |muLow M mk.1| * lambdaLow K mk.2 ≤
              1 * lambdaLow K mk.2 := by
            exact mul_le_mul_of_nonneg_right
              (abs_muLow_le_one M mk.1) (lambdaLow_nonneg K mk.2)
          _ ≤ ArithmeticFunction.vonMangoldt mk.2 := by
            simpa using lambdaLow_le K mk.2
      _ = (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ)) r) := by
        rw [ArithmeticFunction.mul_apply]
        refine Finset.sum_congr rfl fun mk _hmk => ?_
        have hm0 : mk.1 ≠ 0 :=
          Nat.left_ne_zero_of_mem_divisorsAntidiagonal _hmk
        simp [hm0]
      _ = Real.log r := by
        rw [ArithmeticFunction.zeta_mul_vonMangoldt]
        simp [ArithmeticFunction.log_apply]

/-- The coefficient `b_r` is supported on `r ≤ M*K`. -/
theorem bCoeff_eq_zero_of_mul_lt
    (M K r : ℕ) (hr : M * K < r) : bCoeff M K r = 0 := by
  rw [bCoeff, ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro mk hmk
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hmk).1
  by_cases hm : mk.1 ≤ M
  · have hk : K < mk.2 := by
      apply lt_of_not_ge
      intro hkle
      have hmul : mk.1 * mk.2 ≤ M * K := Nat.mul_le_mul hm hkle
      rw [hprod] at hmul
      exact (not_le_of_gt hr) hmul
    change (if mk.1 ≤ M then (ArithmeticFunction.moebius mk.1 : ℝ) else 0) *
        (if mk.2 ≤ K then ArithmeticFunction.vonMangoldt mk.2 else 0) = 0
    simp [hm, not_le.mpr hk]
  · change (if mk.1 ≤ M then (ArithmeticFunction.moebius mk.1 : ℝ) else 0) *
        (if mk.2 ≤ K then ArithmeticFunction.vonMangoldt mk.2 else 0) = 0
    simp [hm]

/-- The logarithmic piece is `a * Λ`. -/
theorem sigma1AF_eq (M : ℕ) :
    sigma1AF M =
      aCoeff M *
        (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) := by
  unfold sigma1AF aCoeff
  rw [← ArithmeticFunction.zeta_mul_vonMangoldt]
  ring

/-- The two `Σ₂` pieces reassemble as `a * Λ_{≤K}`. -/
theorem sigma21AF_add_sigma22AF (M K : ℕ) :
    sigma21AF M K + sigma22AF M K = aCoeff M * lambdaLow K := by
  unfold sigma21AF sigma22AF
  rw [← mul_add, bLow_add_bHigh]
  unfold bCoeff aCoeff
  ring

/-- The global four-piece arithmetic-function identity. -/
theorem four_piece_identity (M K : ℕ) (hM : 1 ≤ M) :
    sigma1AF M - sigma21AF M K - sigma22AF M K - sigma3AF M K =
      lambdaHigh K := by
  have ha : aCoeff M = (1 : ArithmeticFunction ℝ) + aHigh M :=
    (one_add_aHigh M hM).symm
  have hΛ :
      (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
        lambdaLow K + lambdaHigh K := (lambdaLow_add_lambdaHigh K).symm
  rw [show sigma1AF M = aCoeff M *
      (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) from sigma1AF_eq M]
  calc
    aCoeff M * (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
          sigma21AF M K - sigma22AF M K - sigma3AF M K =
        aCoeff M * (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
          (sigma21AF M K + sigma22AF M K) - sigma3AF M K := by ring
    _ = aCoeff M * (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
          aCoeff M * lambdaLow K - lambdaHigh K * aHigh M := by
      rw [sigma21AF_add_sigma22AF]
      rfl
    _ = lambdaHigh K := by
      rw [ha, hΛ]
      ring

/-- The weighted version of each paper term. -/
def sigma1 (s : Finset ℕ) (w : ℕ → ℂ) (M : ℕ) : ℂ :=
  finiteWeightedSum s w (sigma1AF M)

def sigma21 (s : Finset ℕ) (w : ℕ → ℂ) (M K : ℕ) : ℂ :=
  finiteWeightedSum s w (sigma21AF M K)

def sigma22 (s : Finset ℕ) (w : ℕ → ℂ) (M K : ℕ) : ℂ :=
  finiteWeightedSum s w (sigma22AF M K)

def sigma3 (s : Finset ℕ) (w : ℕ → ℂ) (M K : ℕ) : ℂ :=
  finiteWeightedSum s w (sigma3AF M K)

/-! ## Exact product regrouping -/

/-- The possible second factors for a fixed positive first factor `m`, subject
to `y < m*l ≤ y'`. -/
def innerProductInterval (y y' m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 y').filter fun l => y < m * l ∧ m * l ≤ y'

/-- For a positive multiplier, the product condition is the usual quotient
interval. -/
theorem innerProductInterval_eq_Ioc
    (y y' m : ℕ) (hm : 0 < m) :
    innerProductInterval y y' m = Finset.Ioc (y / m) (y' / m) := by
  ext l
  simp only [innerProductInterval, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_Ioc]
  constructor
  · rintro ⟨_hl, hyl, hly'⟩
    constructor
    · apply (Nat.div_lt_iff_lt_mul hm).2
      simpa [Nat.mul_comm] using hyl
    · apply (Nat.le_div_iff_mul_le hm).2
      simpa [Nat.mul_comm] using hly'
  · rintro ⟨hyl, hly'⟩
    have hyl' : y < m * l := by
      simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hm).1 hyl
    have hly'' : m * l ≤ y' := by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm).1 hly'
    have hlpos : 0 < l := lt_of_le_of_lt (Nat.zero_le _) hyl
    have hlle : l ≤ y' :=
      (Nat.le_mul_of_pos_left l hm).trans hly''
    exact ⟨⟨hlpos, hlle⟩, hyl', hly''⟩

/-- All factor pairs whose product belongs to `(y,y']`, with the first
factor restricted to `[1,M]`. -/
def factorPairs (y y' M : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 M).product (Finset.Icc 1 y')).filter fun ml =>
    y < ml.1 * ml.2 ∧ ml.1 * ml.2 ≤ y'

/-- Flatten the divisor antidiagonals of all integers in `(y,y']`. -/
def flatInterval (y y' : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc y y').biUnion fun n => n.divisorsAntidiagonal

private theorem divisorsAntidiagonal_pairwiseDisjoint (y y' : ℕ) :
    ((Finset.Ioc y y' : Finset ℕ) : Set ℕ).PairwiseDisjoint
      fun n => n.divisorsAntidiagonal := by
  intro a _ha b _hb hab
  simp only [Function.onFun]
  refine Finset.disjoint_left.mpr ?_
  intro p hpa hpb
  rw [Nat.mem_divisorsAntidiagonal] at hpa hpb
  exact hab (by rw [← hpa.1, ← hpb.1])

private theorem sum_Ioc_antidiagonal_eq_flatInterval
    {R : Type*} [AddCommMonoid R] (y y' : ℕ) (F : ℕ × ℕ → R) :
    ∑ n ∈ Finset.Ioc y y', ∑ p ∈ n.divisorsAntidiagonal, F p =
      ∑ p ∈ flatInterval y y', F p := by
  rw [flatInterval,
    Finset.sum_biUnion (divisorsAntidiagonal_pairwiseDisjoint y y')]

/-- Regroup a weighted convolution over `(y,y']` with a first factor
supported on `[1,M]`.  This is a completely finite equality. -/
theorem finiteWeightedSum_Ioc_mul_eq_outer
    (y y' M : ℕ) (w : ℕ → ℂ) (A B : ArithmeticFunction ℝ)
    (hA : ∀ m, M < m → A m = 0) :
    finiteWeightedSum (Finset.Ioc y y') w (A * B) =
      ∑ m ∈ Finset.Icc 1 M, ∑ l ∈ innerProductInterval y y' m,
        (A m : ℂ) * (B l : ℂ) * w (m * l) := by
  unfold finiteWeightedSum
  calc
    (∑ n ∈ Finset.Ioc y y', ((A * B) n : ℂ) * w n) =
        ∑ n ∈ Finset.Ioc y y', ∑ ml ∈ n.divisorsAntidiagonal,
          (A ml.1 : ℂ) * (B ml.2 : ℂ) * w (ml.1 * ml.2) := by
      refine Finset.sum_congr rfl fun n _hn => ?_
      rw [ArithmeticFunction.mul_apply, Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ml hml => ?_
      have hprod := (Nat.mem_divisorsAntidiagonal.mp hml).1
      rw [hprod]
      push_cast
      ring
    _ = ∑ ml ∈ flatInterval y y',
          (A ml.1 : ℂ) * (B ml.2 : ℂ) * w (ml.1 * ml.2) :=
      sum_Ioc_antidiagonal_eq_flatInterval y y' _
    _ = ∑ ml ∈ factorPairs y y' M,
          (A ml.1 : ℂ) * (B ml.2 : ℂ) * w (ml.1 * ml.2) := by
      symm
      refine Finset.sum_subset ?_ ?_
      · intro ml hml
        rw [factorPairs] at hml
        obtain ⟨hmlmem, hyl, hly'⟩ := Finset.mem_filter.mp hml
        obtain ⟨hm, hl⟩ := Finset.mem_product.mp hmlmem
        rw [flatInterval, Finset.mem_biUnion]
        refine ⟨ml.1 * ml.2, ?_, ?_⟩
        · exact Finset.mem_Ioc.mpr ⟨hyl, hly'⟩
        · rw [Nat.mem_divisorsAntidiagonal]
          exact ⟨rfl, by
            have hmpos := (Finset.mem_Icc.mp hm).1
            have hlpos := (Finset.mem_Icc.mp hl).1
            positivity⟩
      · intro ml hflat hnot
        rw [flatInterval, Finset.mem_biUnion] at hflat
        obtain ⟨n, hn, hml⟩ := hflat
        have hprod := (Nat.mem_divisorsAntidiagonal.mp hml).1
        have hmpos : 0 < ml.1 :=
          Nat.pos_of_ne_zero
            (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hml)
        have hlpos : 0 < ml.2 :=
          Nat.pos_of_ne_zero
            (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hml)
        have hle2 : ml.2 ≤ n := by
          have h := Nat.le_mul_of_pos_left ml.2 hmpos
          rwa [hprod] at h
        have hgt : M < ml.1 := by
          by_contra hnotgt
          apply hnot
          rw [factorPairs]
          apply Finset.mem_filter.mpr
          have hn' := Finset.mem_Ioc.mp hn
          exact ⟨Finset.mem_product.mpr
              ⟨Finset.mem_Icc.mpr ⟨hmpos, Nat.le_of_not_gt hnotgt⟩,
                Finset.mem_Icc.mpr ⟨hlpos, hle2.trans hn'.2⟩⟩,
            by simpa [hprod] using hn'.1,
            by simpa [hprod] using hn'.2⟩
        rw [hA ml.1 hgt, Complex.ofReal_zero, zero_mul, zero_mul]
    _ = ∑ m ∈ Finset.Icc 1 M, ∑ l ∈ innerProductInterval y y' m,
          (A m : ℂ) * (B l : ℂ) * w (m * l) := by
      simp only [factorPairs, innerProductInterval, Finset.sum_filter]
      rw [← Finset.sum_product']
      rfl

/-
/-- Without a support hypothesis the first factor is automatically at most
the interval's upper endpoint. -/
theorem finiteWeightedSum_Ioc_mul_eq_outer_to_endpoint
    (y y' : ℕ) (w : ℕ → ℂ) (A B : ArithmeticFunction ℝ) :
    finiteWeightedSum (Finset.Ioc y y') w (A * B) =
      ∑ m ∈ Finset.Icc 1 y', ∑ l ∈ Finset.Ioc (y / m) (y' / m),
        (A m : ℂ) * (B l : ℂ) * w (m * l) := by
  unfold finiteWeightedSum
  calc
    (∑ n ∈ Finset.Ioc y y', ((A * B) n : ℂ) * w n) =
        ∑ n ∈ Finset.Ioc y y', ∑ ml ∈ n.divisorsAntidiagonal,
          (A ml.1 : ℂ) * (B ml.2 : ℂ) * w (ml.1 * ml.2) := by
      refine Finset.sum_congr rfl fun n _hn => ?_
      rw [ArithmeticFunction.mul_apply, Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ml hml => ?_
      rw [(Nat.mem_divisorsAntidiagonal.mp hml).1]
      push_cast
      ring
    _ = ∑ ml ∈ flatInterval y y',
          (A ml.1 : ℂ) * (B ml.2 : ℂ) * w (ml.1 * ml.2) :=
      sum_Ioc_antidiagonal_eq_flatInterval y y' _
    _ = ∑ ml ∈ factorPairs y y' y',
          (A ml.1 : ℂ) * (B ml.2 : ℂ) * w (ml.1 * ml.2) := by
      apply Finset.sum_congr
      · ext ml
        constructor
        · intro hflat
          rw [flatInterval, Finset.mem_biUnion] at hflat
          obtain ⟨n, hn, hml⟩ := hflat
          have hprod := (Nat.mem_divisorsAntidiagonal.mp hml).1
          have hmpos : 0 < ml.1 := Nat.pos_of_ne_zero
            (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hml)
          have hlpos : 0 < ml.2 := Nat.pos_of_ne_zero
            (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hml)
          have hle1 : ml.1 ≤ n := by
            have h := Nat.le_mul_of_pos_right ml.1 hlpos
            rwa [hprod] at h
          have hle2 : ml.2 ≤ n := by
            have h := Nat.le_mul_of_pos_left ml.2 hmpos
            rwa [hprod] at h
          rw [factorPairs]
          apply Finset.mem_filter.mpr
          have hn' := Finset.mem_Ioc.mp hn
          exact ⟨Finset.mem_product.mpr
              ⟨Finset.mem_Icc.mpr ⟨hmpos, hle1.trans hn'.2⟩,
                Finset.mem_Icc.mpr ⟨hlpos, hle2.trans hn'.2⟩⟩,
            by simpa [hprod] using hn'.1,
            by simpa [hprod] using hn'.2⟩
        · intro hpairs
          rw [factorPairs] at hpairs
          obtain ⟨_hmem, hyl, hly'⟩ := Finset.mem_filter.mp hpairs
          rw [flatInterval, Finset.mem_biUnion]
          refine ⟨ml.1 * ml.2, Finset.mem_Ioc.mpr ⟨hyl, hly'⟩, ?_⟩
          rw [Nat.mem_divisorsAntidiagonal]
          exact ⟨rfl, by
            obtain ⟨hm, hl⟩ := Finset.mem_product.mp _hmem
            have hmpos := (Finset.mem_Icc.mp hm).1
            have hlpos := (Finset.mem_Icc.mp hl).1
            positivity⟩
      · intro _ _
        rfl
    _ = ∑ m ∈ Finset.Icc 1 y', ∑ l ∈ innerProductInterval y y' m,
          (A m : ℂ) * (B l : ℂ) * w (m * l) := by
      simp only [factorPairs, innerProductInterval, Finset.sum_filter]
      rw [← Finset.sum_product']
      rfl
    _ = ∑ m ∈ Finset.Icc 1 y', ∑ l ∈ Finset.Ioc (y / m) (y' / m),
          (A m : ℂ) * (B l : ℂ) * w (m * l) := by
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [innerProductInterval_eq_Ioc y y' m (Finset.mem_Icc.mp hm).1]

/-- Lower-annular form of the endpoint regrouping. -/
theorem finiteWeightedSum_Ioc_mul_eq_outer_endpoint_Ioc
    (y y' L : ℕ) (w : ℕ → ℂ) (A B : ArithmeticFunction ℝ)
    (hBelow : ∀ m, m ≤ L → A m = 0) :
    finiteWeightedSum (Finset.Ioc y y') w (A * B) =
      ∑ m ∈ Finset.Ioc L y', ∑ l ∈ Finset.Ioc (y / m) (y' / m),
        (A m : ℂ) * (B l : ℂ) * w (m * l) := by
  rw [finiteWeightedSum_Ioc_mul_eq_outer_to_endpoint]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro m hm
    have hm' := Finset.mem_Ioc.mp hm
    exact Finset.mem_Icc.mpr ⟨lt_of_le_of_lt (Nat.zero_le _) hm'.1, hm'.2⟩
  · intro m hmIcc hmnot
    have hmle : m ≤ L := by
      by_contra hnotle
      apply hmnot
      exact Finset.mem_Ioc.mpr ⟨lt_of_not_ge hnotle, (Finset.mem_Icc.mp hmIcc).2⟩
    simp [hBelow m hmle]

-/
/-- Expanded paper form of `Σ₁`. -/
theorem sigma1_Ioc_eq_outer
    (y y' M : ℕ) (w : ℕ → ℂ) :
    sigma1 (Finset.Ioc y y') w M =
      ∑ m ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Ioc (y / m) (y' / m),
        (ArithmeticFunction.moebius m : ℂ) *
          (Real.log l : ℂ) * w (m * l) := by
  unfold sigma1 sigma1AF
  rw [finiteWeightedSum_Ioc_mul_eq_outer]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [innerProductInterval_eq_Ioc y y' m (Finset.mem_Icc.mp hm).1]
    refine Finset.sum_congr rfl fun l _hl => ?_
    have hmle := (Finset.mem_Icc.mp hm).2
    change ((if m ≤ M then (ArithmeticFunction.moebius m : ℝ) else 0 : ℝ) : ℂ) *
        ((ArithmeticFunction.log l : ℝ) : ℂ) * w (m * l) = _
    rw [if_pos hmle]
    simp [ArithmeticFunction.log_apply]
  · intro m hm
    change (if m ≤ M then (ArithmeticFunction.moebius m : ℝ) else 0) = 0
    rw [if_neg (not_le.mpr hm)]

/-- Expanded paper form of `Σ₂,₁`. -/
theorem sigma21_Ioc_eq_outer
    (y y' M K : ℕ) (w : ℕ → ℂ) :
    sigma21 (Finset.Ioc y y') w M K =
      ∑ r ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Ioc (y / r) (y' / r),
        (bCoeff M K r : ℂ) * w (r * l) := by
  unfold sigma21 sigma21AF
  rw [mul_comm]
  rw [finiteWeightedSum_Ioc_mul_eq_outer]
  · refine Finset.sum_congr rfl fun r hr => ?_
    rw [innerProductInterval_eq_Ioc y y' r (Finset.mem_Icc.mp hr).1]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hrle := (Finset.mem_Icc.mp hr).2
    have hlne : l ≠ 0 := Nat.ne_of_gt
      (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hl).1)
    change ((if r ≤ M then bCoeff M K r else 0 : ℝ) : ℂ) *
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) l : ℂ) * w (r * l) = _
    rw [if_pos hrle]
    simp [hlne]
  · intro r hr
    change (if r ≤ M then bCoeff M K r else 0) = 0
    rw [if_neg (not_le.mpr hr)]

/-- Granville--Ramaré Lemma 9.1 for an arbitrary finite set supported above
`K`. -/
theorem finite_four_sum_identity
    (s : Finset ℕ) (w : ℕ → ℂ) (M K : ℕ) (hM : 1 ≤ M)
    (hs : ∀ n ∈ s, K < n) :
    finiteWeightedSum s w
        (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
      sigma1 s w M - sigma21 s w M K - sigma22 s w M K - sigma3 s w M K := by
  unfold sigma1 sigma21 sigma22 sigma3 finiteWeightedSum
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hpoint := congr_arg (fun F : ArithmeticFunction ℝ => F n)
    (four_piece_identity M K hM)
  have hhigh : lambdaHigh K n = ArithmeticFunction.vonMangoldt n := by
    simp [lambdaHigh, hs n hn]
  rw [hhigh] at hpoint
  have hpointC :
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) =
        (((sigma1AF M - sigma21AF M K - sigma22AF M K - sigma3AF M K) n : ℝ) : ℂ) := by
    exact_mod_cast hpoint.symm
  rw [hpointC]
  simp only [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply]
  push_cast
  ring

/-- The interval version of Lemma 9.1. -/
theorem Ioc_four_sum_identity
    (y y' M K : ℕ) (w : ℕ → ℂ) (hM : 1 ≤ M) (hKy : K ≤ y) :
    finiteWeightedSum (Finset.Ioc y y') w
        (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
      sigma1 (Finset.Ioc y y') w M -
        sigma21 (Finset.Ioc y y') w M K -
        sigma22 (Finset.Ioc y y') w M K -
        sigma3 (Finset.Ioc y y') w M K := by
  apply finite_four_sum_identity _ _ _ _ hM
  intro n hn
  exact lt_of_le_of_lt hKy (Finset.mem_Ioc.mp hn).1

/-- Lemma 9.1 specialized to the reciprocal phase `e(x/n)`. -/
theorem reciprocal_Ioc_four_sum_identity
    (y y' M K : ℕ) (x : ℝ) (hM : 1 ≤ M) (hKy : K ≤ y) :
    reciprocalSum (Finset.Ioc y y') x
        (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
      sigma1 (Finset.Ioc y y') (reciprocalPhase x) M -
        sigma21 (Finset.Ioc y y') (reciprocalPhase x) M K -
        sigma22 (Finset.Ioc y y') (reciprocalPhase x) M K -
        sigma3 (Finset.Ioc y y') (reciprocalPhase x) M K := by
  exact Ioc_four_sum_identity y y' M K (reciprocalPhase x) hM hKy

end Erdos175.VaughanFourSums
