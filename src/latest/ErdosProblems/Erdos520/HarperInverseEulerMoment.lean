import ErdosProblems.Erdos520.HarperPrimeBlockAsymptotic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Set Function Filter Finset MeasureTheory ProbabilityTheory Topology
open scoped BigOperators

noncomputable section

namespace Erdos
namespace Problem520

/-!
# Fair inverse moments of Rademacher Euler factors

The reciprocal lower barrier in Harper's Rademacher argument is controlled
under the fair sign law.  At one prime its expectation has an exact rational
form.  Its logarithm has first-order term

`(1 + 2 * cos (2 * u * log p)) / p`

and an `O(p⁻²)` remainder, which is summable over the primes.  This file
records that calculation independently of the tilted Gaussian comparison.
-/

/-- The fair one-prime expectation of the reciprocal squared Euler factor. -/
noncomputable def harperInverseEulerPrimeMoment (p : ℕ) (u : ℝ) : ℝ :=
  ∫ b, (harperCoordinateFactor p u b)⁻¹ ∂coin

theorem harperCoordinateFactor_pos
    {p : ℕ} (hp : p.Prime) (u : ℝ) (b : Bool) :
    0 < harperCoordinateFactor p u b := by
  unfold harperCoordinateFactor
  exact harperEulerFactor_pos (fun _ ↦ b) hp u

/-- Exact rational formula for the fair inverse moment at one prime. -/
theorem harperInverseEulerPrimeMoment_eq
    {p : ℕ} (hp : p.Prime) (u : ℝ) :
    harperInverseEulerPrimeMoment p u =
      (1 + (p : ℝ)⁻¹) /
        (1 - 2 * Real.cos (2 * (u * Real.log (p : ℝ))) * (p : ℝ)⁻¹ +
          (p : ℝ)⁻¹ ^ 2) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hsqrt : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.2 hpR).ne'
  have hsqrtSq : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) :=
    Real.sq_sqrt hpR.le
  let A : ℝ := 1 + (p : ℝ)⁻¹
  let B : ℝ := 2 * Real.cos (u * Real.log (p : ℝ)) / Real.sqrt (p : ℝ)
  let D : ℝ :=
    1 - 2 * Real.cos (2 * (u * Real.log (p : ℝ))) * (p : ℝ)⁻¹ +
      (p : ℝ)⁻¹ ^ 2
  have hfalse : harperCoordinateFactor p u false = A - B := by
    rw [harperCoordinateFactor, harperEulerFactor_eq (fun _ ↦ false) hp.pos]
    simp only [ε, Bool.false_eq_true, if_false]
    dsimp [A, B]
    ring
  have htrue : harperCoordinateFactor p u true = A + B := by
    rw [harperCoordinateFactor, harperEulerFactor_eq (fun _ ↦ true) hp.pos]
    simp only [ε, if_true]
    dsimp [A, B]
    ring
  have hminus : 0 < A - B := hfalse ▸ harperCoordinateFactor_pos hp u false
  have hplus : 0 < A + B := htrue ▸ harperCoordinateFactor_pos hp u true
  have hBsquare :
      B ^ 2 =
        4 * Real.cos (u * Real.log (p : ℝ)) ^ 2 * (p : ℝ)⁻¹ := by
    dsimp [B]
    rw [div_pow, Real.sq_sqrt hpR.le]
    ring
  have hprod : (A - B) * (A + B) = D := by
    rw [show (A - B) * (A + B) = A ^ 2 - B ^ 2 by ring, hBsquare]
    dsimp [A, D]
    rw [Real.cos_two_mul]
    ring
  rw [harperInverseEulerPrimeMoment, integral_coin_bool, hfalse, htrue]
  calc
    ((A - B)⁻¹ + (A + B)⁻¹) / 2 =
        A / ((A - B) * (A + B)) := by
      field_simp [hminus.ne', hplus.ne']
      ring
    _ = A / D := by rw [hprod]
    _ = _ := by rfl

theorem harperInverseEulerPrimeMoment_pos
    {p : ℕ} (hp : p.Prime) (u : ℝ) :
    0 < harperInverseEulerPrimeMoment p u := by
  unfold harperInverseEulerPrimeMoment
  rw [integral_coin_bool]
  exact div_pos
    (add_pos (inv_pos.mpr (harperCoordinateFactor_pos hp u false))
      (inv_pos.mpr (harperCoordinateFactor_pos hp u true)))
    (by norm_num)

/-! ## The sharp logarithmic majorant

The numerical constant `16` is deliberately uncomplicated.  The important
point is that the linear coefficient, including its oscillation, is kept
exact and the error is on the summable `p⁻²` scale.
-/

private theorem inverseEulerRational_log_le
    {x C : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 4)
    (hC : |C| ≤ 1) :
    Real.log ((1 + x) / (1 - 2 * C * x + x ^ 2)) ≤
      (1 + 2 * C) * x + 16 * x ^ 2 := by
  let D : ℝ := 1 - 2 * C * x + x ^ 2
  have hCneg : -1 ≤ C := (abs_le.mp hC).1
  have hCpos : C ≤ 1 := (abs_le.mp hC).2
  have hxnonneg : 0 ≤ x := hx0.le
  have honeSub : 3 / 4 ≤ 1 - x := by linarith
  have hDcompare : (1 - x) ^ 2 ≤ D := by
    dsimp [D]
    nlinarith [mul_nonneg hxnonneg (sub_nonneg.mpr hCpos)]
  have hDhalf : (1 / 2 : ℝ) ≤ D := by
    have hsquare : (9 / 16 : ℝ) ≤ (1 - x) ^ 2 := by nlinarith
    linarith
  have hDpos : 0 < D := by linarith
  have hAabs : |1 + 2 * C| ≤ 3 := by
    calc
      |1 + 2 * C| ≤ |(1 : ℝ)| + |2 * C| := abs_add_le _ _
      _ = 1 + 2 * |C| := by rw [abs_one, abs_mul, abs_of_nonneg (by norm_num)]
      _ ≤ 3 := by linarith
  have hBxabs : |2 * C - x| ≤ 9 / 4 := by
    calc
      |2 * C - x| ≤ |2 * C| + |x| := abs_sub _ _
      _ = 2 * |C| + x := by
        rw [abs_mul, abs_of_nonneg (by norm_num), abs_of_nonneg hxnonneg]
      _ ≤ 9 / 4 := by linarith
  have hbracketAbs : |(1 + 2 * C) * (2 * C - x) - 1| ≤ 8 := by
    calc
      |(1 + 2 * C) * (2 * C - x) - 1| ≤
          |(1 + 2 * C) * (2 * C - x)| + |(1 : ℝ)| := abs_sub _ _
      _ = |1 + 2 * C| * |2 * C - x| + 1 := by rw [abs_mul, abs_one]
      _ ≤ 3 * (9 / 4 : ℝ) + 1 := by gcongr
      _ ≤ 8 := by norm_num
  have hbracket : (1 + 2 * C) * (2 * C - x) - 1 ≤ 8 :=
    (le_abs_self _).trans hbracketAbs
  have herrorNumerator :
      x ^ 2 * ((1 + 2 * C) * (2 * C - x) - 1) ≤
        16 * x ^ 2 * D := by
    calc
      x ^ 2 * ((1 + 2 * C) * (2 * C - x) - 1) ≤
          x ^ 2 * 8 := mul_le_mul_of_nonneg_left hbracket (sq_nonneg x)
      _ ≤ 16 * x ^ 2 * D := by nlinarith [sq_nonneg x]
  let M : ℝ := (1 + x) / D
  have hMpos : 0 < M := div_pos (by linarith) hDpos
  have herrorIdentity :
      M - 1 - (1 + 2 * C) * x =
        x ^ 2 * ((1 + 2 * C) * (2 * C - x) - 1) / D := by
    dsimp [M]
    field_simp [hDpos.ne']
    dsimp [D]
    ring
  have hlinear : M - 1 ≤ (1 + 2 * C) * x + 16 * x ^ 2 := by
    have herror : M - 1 - (1 + 2 * C) * x ≤ 16 * x ^ 2 := by
      rw [herrorIdentity]
      exact (div_le_iff₀ hDpos).2 herrorNumerator
    linarith
  exact (Real.log_le_sub_one_of_pos hMpos).trans hlinear

/-- The one-prime logarithm retains the exact first-order oscillatory term;
the loss is a summable inverse-square remainder. -/
theorem log_harperInverseEulerPrimeMoment_le
    {p : ℕ} (hp : p.Prime) (hp4 : 4 ≤ p) (u : ℝ) :
    Real.log (harperInverseEulerPrimeMoment p u) ≤
      (1 + 2 * Real.cos (2 * (u * Real.log (p : ℝ)))) / (p : ℝ) +
        16 * (p : ℝ)⁻¹ ^ 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hx : (p : ℝ)⁻¹ ≤ 1 / 4 := by
    have hp4R : (4 : ℝ) ≤ p := by exact_mod_cast hp4
    simpa only [one_div] using!
      inv_anti₀ (by norm_num : (0 : ℝ) < 4) hp4R
  rw [harperInverseEulerPrimeMoment_eq hp u]
  have h := inverseEulerRational_log_le (inv_pos.mpr hpR) hx
    (Real.abs_cos_le_one (2 * (u * Real.log (p : ℝ))))
  simpa only [div_eq_mul_inv] using! h

/-- Exponential form of the same sharp one-prime estimate. -/
theorem harperInverseEulerPrimeMoment_le_exp
    {p : ℕ} (hp : p.Prime) (hp4 : 4 ≤ p) (u : ℝ) :
    harperInverseEulerPrimeMoment p u ≤
      Real.exp
        ((1 + 2 * Real.cos (2 * (u * Real.log (p : ℝ)))) / (p : ℝ) +
          16 * (p : ℝ)⁻¹ ^ 2) := by
  rw [← Real.exp_log (harperInverseEulerPrimeMoment_pos hp u)]
  exact Real.exp_le_exp.mpr (log_harperInverseEulerPrimeMoment_le hp hp4 u)

/-! ## Finite fair products -/

/-- Reciprocal Euler energy over a finite set of prime coordinates. -/
noncomputable def harperInverseEulerBlockProduct
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (u : ℝ) (eta : HarperPrimeCube y) : ℝ :=
  ∏ p ∈ S, (harperCoordinateFactor p.1 u (eta p))⁻¹

/-- Under the fair cube law, the inverse block expectation factors into the
exact one-prime moments. -/
theorem integral_harperInverseEulerBlockProduct
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (u : ℝ) :
    (∫ eta, harperInverseEulerBlockProduct y S u eta
        ∂Measure.pi (fun _ : HarperPrimeIndex y ↦ coin)) =
      ∏ p ∈ S, harperInverseEulerPrimeMoment p.1 u := by
  let X : ↑S → HarperPrimeCube y → ℝ :=
    fun p eta ↦ (harperCoordinateFactor p.1.1 u (eta p.1))⁻¹
  have hbaseFull : iIndepFun
      (fun p : HarperPrimeIndex y ↦ fun eta : HarperPrimeCube y ↦ eta p)
      (Measure.pi (fun _ : HarperPrimeIndex y ↦ coin)) := by
    exact iIndepFun_pi
      (X := fun _ : HarperPrimeIndex y ↦ id)
      (fun _ ↦ aemeasurable_id)
  have hbase : iIndepFun
      (fun p : ↑S ↦ fun eta : HarperPrimeCube y ↦ eta p.1)
      (Measure.pi (fun _ : HarperPrimeIndex y ↦ coin)) :=
    hbaseFull.precomp Subtype.val_injective
  have hX : iIndepFun X
      (Measure.pi (fun _ : HarperPrimeIndex y ↦ coin)) := by
    have hcomp := hbase.comp
      (fun p (b : Bool) ↦ (harperCoordinateFactor p.1.1 u b)⁻¹)
      (fun _ ↦ measurable_of_finite _)
    simpa only [X, Function.comp_apply] using! hcomp
  have hprod := hX.integral_fun_prod_eq_prod_integral
    (fun p ↦ (measurable_of_finite (X p)).aestronglyMeasurable)
  calc
    (∫ eta, harperInverseEulerBlockProduct y S u eta
        ∂Measure.pi (fun _ : HarperPrimeIndex y ↦ coin)) =
        ∫ eta, ∏ p : ↑S, X p eta
          ∂Measure.pi (fun _ : HarperPrimeIndex y ↦ coin) := by
      congr 1
      funext eta
      unfold harperInverseEulerBlockProduct X
      exact (Finset.prod_coe_sort S
        (fun p ↦ (harperCoordinateFactor p.1 u (eta p))⁻¹)).symm
    _ = ∏ p : ↑S,
        ∫ eta, X p eta
          ∂Measure.pi (fun _ : HarperPrimeIndex y ↦ coin) := by
      simpa only using! hprod
    _ = ∏ p : ↑S, harperInverseEulerPrimeMoment p.1.1 u := by
      apply Finset.prod_congr rfl
      intro p hpS
      let g : Bool → ℝ :=
        fun b ↦ (harperCoordinateFactor p.1.1 u b)⁻¹
      have hmp := measurePreserving_eval
        (fun _ : HarperPrimeIndex y ↦ coin) p.1
      calc
        (∫ eta, X p eta
            ∂Measure.pi (fun _ : HarperPrimeIndex y ↦ coin)) =
            ∫ b, g b ∂Measure.map
              (fun eta : HarperPrimeCube y ↦ eta p.1)
              (Measure.pi (fun _ : HarperPrimeIndex y ↦ coin)) := by
          symm
          exact integral_map hmp.measurable.aemeasurable
            (measurable_of_finite g).aestronglyMeasurable
        _ = ∫ b, g b ∂coin := by rw [hmp.map_eq]
        _ = harperInverseEulerPrimeMoment p.1.1 u := by rfl
    _ = ∏ p ∈ S, harperInverseEulerPrimeMoment p.1 u :=
      Finset.prod_coe_sort S
        (fun p ↦ harperInverseEulerPrimeMoment p.1 u)

/-- Product form of the one-prime exponential majorant. -/
noncomputable def harperInverseEulerPrimeExponent (p : ℕ) (u : ℝ) : ℝ :=
  (1 + 2 * Real.cos (2 * (u * Real.log (p : ℝ)))) / (p : ℝ) +
    16 * (p : ℝ)⁻¹ ^ 2

theorem integral_harperInverseEulerBlockProduct_le_exp
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (h4 : ∀ p ∈ S, 4 ≤ p.1) (u : ℝ) :
    (∫ eta, harperInverseEulerBlockProduct y S u eta
        ∂Measure.pi (fun _ : HarperPrimeIndex y ↦ coin)) ≤
      Real.exp (∑ p ∈ S, harperInverseEulerPrimeExponent p.1 u) := by
  rw [integral_harperInverseEulerBlockProduct]
  calc
    (∏ p ∈ S, harperInverseEulerPrimeMoment p.1 u) ≤
        ∏ p ∈ S,
          Real.exp (harperInverseEulerPrimeExponent p.1 u) := by
      apply Finset.prod_le_prod
      · intro p hpS
        exact (harperInverseEulerPrimeMoment_pos
          (Nat.prime_of_mem_primesBelow p.property) u).le
      · intro p hpS
        simpa only [harperInverseEulerPrimeExponent] using!
          harperInverseEulerPrimeMoment_le_exp
            (Nat.prime_of_mem_primesBelow p.property) (h4 p hpS) u
    _ = Real.exp
        (∑ p ∈ S, harperInverseEulerPrimeExponent p.1 u) := by
      rw [Real.exp_sum]

/-- The exponent separates into reciprocal mass, oscillatory mass, and the
summable inverse-square remainder. -/
theorem sum_harperInverseEulerPrimeExponent_eq
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (u : ℝ) :
    (∑ p ∈ S, harperInverseEulerPrimeExponent p.1 u) =
      (∑ p ∈ S, (p.1 : ℝ)⁻¹) +
        2 * (∑ p ∈ S,
          Real.cos ((2 * u) * Real.log (p.1 : ℝ)) / p.1) +
        16 * (∑ p ∈ S, (p.1 : ℝ)⁻¹ ^ 2) := by
  rw [Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hpS
  unfold harperInverseEulerPrimeExponent
  rw [show (2 * u) * Real.log (p.1 : ℝ) =
      2 * (u * Real.log (p.1 : ℝ)) by ring]
  ring

/-! ## Scheduled inverse-square control -/

/-- On a scheduled block, inverse-square mass is its reciprocal mass times
at most the inverse lower endpoint. -/
theorem sum_harperScheduledPrimeBlock_inv_sq_le
    (y j : ℕ) :
    (∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹ ^ 2) ≤
      (harperBlockEndpoint j : ℝ)⁻¹ *
        ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹ := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hpBlock
  have hApos : (0 : ℝ) < harperBlockEndpoint j := by
    exact_mod_cast harperBlockEndpoint_pos j
  have hpPos : (0 : ℝ) < p.1 := by
    exact_mod_cast (show 0 < p.1 by
      have := sixteen_le_prime_of_mem_harperScheduledPrimeBlock hpBlock
      omega)
  have hAp : (harperBlockEndpoint j : ℝ) ≤ p.1 := by
    exact_mod_cast ((mem_harperScheduledPrimeBlock p).mp hpBlock).1.le
  have hinv : (p.1 : ℝ)⁻¹ ≤ (harperBlockEndpoint j : ℝ)⁻¹ :=
    inv_anti₀ hApos hAp
  calc
    (p.1 : ℝ)⁻¹ ^ 2 = (p.1 : ℝ)⁻¹ * (p.1 : ℝ)⁻¹ := by ring
    _ ≤ (harperBlockEndpoint j : ℝ)⁻¹ * (p.1 : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hinv (inv_nonneg.mpr hpPos.le)

/-- Eventually the full logarithmic exponent of a scheduled inverse block is
at most `2`, uniformly on every fixed noncentral frequency window. -/
theorem exists_eventually_sum_harperScheduledInverseEulerPrimeExponent_le_two
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ u : ℝ, 1 ≤ |u| → |u| ≤ M →
          (∑ p ∈ harperScheduledPrimeBlock y j,
            harperInverseEulerPrimeExponent p.1 u) ≤ 2 := by
  obtain ⟨Jmass, hmass⟩ :=
    exists_eventually_harperScheduledPrimeBlock_inv_bounds
  obtain ⟨Josc, hosc⟩ :=
    exists_eventually_harperScheduledPrimeOscillation_le_eighth M
  have hend : Tendsto harperBlockEndpoint atTop atTop :=
    strictMono_harperBlockEndpoint.tendsto_atTop
  have hcast : Tendsto (fun j : ℕ ↦ (harperBlockEndpoint j : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hend
  have hinv : Tendsto
      (fun j : ℕ ↦ (harperBlockEndpoint j : ℝ)⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hcast
  have hscaled : Tendsto
      (fun j : ℕ ↦ 24 * (harperBlockEndpoint j : ℝ)⁻¹)
      atTop (nhds 0) := by
    convert! (tendsto_const_nhds.mul hinv) using 1 <;> norm_num
  have hevent : ∀ᶠ j : ℕ in atTop,
      24 * (harperBlockEndpoint j : ℝ)⁻¹ < 1 / 4 :=
    (tendsto_order.mp hscaled).2 (1 / 4) (by norm_num)
  obtain ⟨Jsmall, hsmall⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max Jmass (max Josc Jsmall), ?_⟩
  intro j hj y hy u huLower huUpper
  have hjmass : Jmass ≤ j :=
    (le_max_left Jmass (max Josc Jsmall)).trans hj
  have hjosc : Josc ≤ j :=
    (le_max_left Josc Jsmall).trans
      ((le_max_right Jmass (max Josc Jsmall)).trans hj)
  have hjsmall : Jsmall ≤ j :=
    (le_max_right Josc Jsmall).trans
      ((le_max_right Jmass (max Josc Jsmall)).trans hj)
  let reciprocalMass : ℝ :=
    ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹
  let oscillatoryMass : ℝ :=
    ∑ p ∈ harperScheduledPrimeBlock y j,
      Real.cos ((2 * u) * Real.log (p.1 : ℝ)) / p.1
  let squareMass : ℝ :=
    ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹ ^ 2
  have hmassUpper : reciprocalMass ≤ 3 / 2 :=
    (hmass j hjmass y hy).2
  have habsTwo : |2 * u| = 2 * |u| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have htauLower : 2 ≤ |2 * u| := by rw [habsTwo]; linarith
  have htauUpper : |2 * u| ≤ 2 * M := by
    rw [habsTwo]
    exact mul_le_mul_of_nonneg_left huUpper (by norm_num)
  have hoscAbs : |oscillatoryMass| ≤ 1 / 8 :=
    hosc j hjosc y hy (2 * u) htauLower htauUpper
  have hoscUpper : oscillatoryMass ≤ 1 / 8 := le_of_abs_le hoscAbs
  have hAinvNonneg : 0 ≤ (harperBlockEndpoint j : ℝ)⁻¹ := by positivity
  have hsquareUpper :
      squareMass ≤ (harperBlockEndpoint j : ℝ)⁻¹ * (3 / 2 : ℝ) := by
    calc
      squareMass ≤
          (harperBlockEndpoint j : ℝ)⁻¹ * reciprocalMass :=
        sum_harperScheduledPrimeBlock_inv_sq_le y j
      _ ≤ (harperBlockEndpoint j : ℝ)⁻¹ * (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hmassUpper hAinvNonneg
  have hremainder : 16 * squareMass < 1 / 4 := by
    calc
      16 * squareMass ≤
          24 * (harperBlockEndpoint j : ℝ)⁻¹ := by
        nlinarith
      _ < 1 / 4 := hsmall j hjsmall
  rw [sum_harperInverseEulerPrimeExponent_eq]
  change reciprocalMass + 2 * oscillatoryMass + 16 * squareMass ≤ 2
  linarith

/-- The scheduled fair inverse-product expectation is uniformly bounded by
`exp 2` on every fixed noncentral window. -/
theorem exists_eventually_integral_harperScheduledInverseEulerBlockProduct_le_exp_two
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ u : ℝ, 1 ≤ |u| → |u| ≤ M →
          (∫ eta,
              harperInverseEulerBlockProduct y
                (harperScheduledPrimeBlock y j) u eta
              ∂Measure.pi (fun _ : HarperPrimeIndex y ↦ coin)) ≤
            Real.exp 2 := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_sum_harperScheduledInverseEulerPrimeExponent_le_two M
  refine ⟨J, ?_⟩
  intro j hj y hy u huLower huUpper
  calc
    (∫ eta,
        harperInverseEulerBlockProduct y
          (harperScheduledPrimeBlock y j) u eta
        ∂Measure.pi (fun _ : HarperPrimeIndex y ↦ coin)) ≤
        Real.exp
          (∑ p ∈ harperScheduledPrimeBlock y j,
            harperInverseEulerPrimeExponent p.1 u) := by
      exact integral_harperInverseEulerBlockProduct_le_exp y
        (harperScheduledPrimeBlock y j)
        (fun p hp ↦ four_le_prime_of_mem_harperScheduledPrimeBlock hp) u
    _ ≤ Real.exp 2 :=
      Real.exp_le_exp.mpr (hJ j hj y hy u huLower huUpper)

end Problem520
end Erdos
