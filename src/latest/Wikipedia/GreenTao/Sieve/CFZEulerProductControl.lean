import Wikipedia.GreenTao.Sieve.EulerProductControl
import Wikipedia.GreenTao.Sieve.GoodPrimeLocalFactorBound

/-!
# CFZ good-prime ratios and Euler-product control

The normalized local coprimality factor is not compared directly with one
in the finite-field calculation.  Its natural first-order model is

`(p / (p - 1))^m * (1 - m / p)`.

The higher-order inclusion--exclusion estimate controls the difference from
this model by `O_m(p⁻²)`.  Dividing by the model exposes the local ratio
which belongs in the absolutely convergent remainder Euler product.  Above
`2m` the model is at least `1/2`, and the scale `(p/(p-1))^m` is at most
`2^m`; these elementary bounds give a uniform square-error constant.

The final theorems specialize this ratio to the CFZ affine-form family,
mask every prime below an explicit exceptional cutoff, and instantiate
`HasPrimeSquareError`.  This is the local-to-abstract-product bridge.  It
does not yet identify the nonmultiplicative smooth Selberg divisor sum with
this Euler product; that remains part of the Fourier/Mellin argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The first-order normalized local model for a system of `m` forms. -/
noncomputable def normalizedFirstOrderLocalModel
    (m p : ℕ) : ℝ :=
  ((p : ℝ) / (p - 1 : ℕ)) ^ m *
    (1 - (m : ℝ) / (p : ℝ))

/-- The normalized scale is at most `2^m` at every prime. -/
theorem normalizedLocalScale_le_pow_two
    (m : ℕ) {p : ℕ} (hp : p.Prime) :
    ((p : ℝ) / (p - 1 : ℕ)) ^ m ≤
      (2 : ℝ) ^ m := by
  have hpredNat : 0 < p - 1 :=
    Nat.sub_pos_of_lt hp.one_lt
  have hpred : 0 < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast hpredNat
  have hratio0 :
      0 ≤ (p : ℝ) / (p - 1 : ℕ) :=
    div_nonneg (Nat.cast_nonneg p) hpred.le
  have hratio2 :
      (p : ℝ) / (p - 1 : ℕ) ≤ 2 := by
    rw [div_le_iff₀ hpred]
    exact_mod_cast (show p ≤ 2 * (p - 1) by omega)
  exact pow_le_pow_left₀ hratio0 hratio2 m

/-- The first-order model is at least one half once `p ≥ 2m`. -/
theorem one_half_le_normalizedFirstOrderLocalModel
    {m p : ℕ} (hp : p.Prime) (hmp : 2 * m ≤ p) :
    (1 : ℝ) / 2 ≤ normalizedFirstOrderLocalModel m p := by
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hpredNat : 0 < p - 1 :=
    Nat.sub_pos_of_lt hp.one_lt
  have hpred : 0 < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast hpredNat
  have hratioOne :
      1 ≤ (p : ℝ) / (p - 1 : ℕ) := by
    rw [le_div_iff₀ hpred]
    norm_num [Nat.cast_sub hp.one_le]
  have hscaleOne :
      1 ≤ ((p : ℝ) / (p - 1 : ℕ)) ^ m :=
    one_le_pow₀ hratioOne
  have hscale0 :
      0 ≤ ((p : ℝ) / (p - 1 : ℕ)) ^ m :=
    (pow_nonneg
      (div_nonneg (Nat.cast_nonneg p) hpred.le) m)
  have hmpR : 2 * (m : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hmp
  have hmdiv :
      (m : ℝ) / (p : ℝ) ≤ (1 : ℝ) / 2 := by
    rw [div_le_iff₀ hpR]
    linarith
  have hsecond :
      (1 : ℝ) / 2 ≤ 1 - (m : ℝ) / (p : ℝ) := by
    linarith
  change
    (1 : ℝ) / 2 ≤
      ((p : ℝ) / (p - 1 : ℕ)) ^ m *
        (1 - (m : ℝ) / (p : ℝ))
  calc
    (1 : ℝ) / 2 = 1 * ((1 : ℝ) / 2) := by ring
    _ ≤
        ((p : ℝ) / (p - 1 : ℕ)) ^ m *
          (1 - (m : ℝ) / (p : ℝ)) :=
      mul_le_mul hscaleOne hsecond (by norm_num) hscale0

/-- In particular the first-order model is positive above `2m`. -/
theorem normalizedFirstOrderLocalModel_pos
    {m p : ℕ} (hp : p.Prime) (hmp : 2 * m ≤ p) :
    0 < normalizedFirstOrderLocalModel m p :=
  (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (one_half_le_normalizedFirstOrderLocalModel hp hmp)

/-- Ratio of the actual normalized system local factor to its first-order
model. -/
noncomputable def systemLocalCoprimeRatio
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p]
    (forms : κ → AffineForm ι ℤ) : ℝ :=
  mean (systemLocalCoprimeWeight p forms) /
    normalizedFirstOrderLocalModel (Fintype.card κ) p

/-- A convenient uniform constant for the normalized ratio error. -/
noncomputable def systemLocalRatioErrorConstant
    (m : ℕ) : ℝ :=
  2 * (2 : ℝ) ^ m * (2 : ℝ) ^ m

theorem systemLocalRatioErrorConstant_nonneg
    (m : ℕ) :
    0 ≤ systemLocalRatioErrorConstant m := by
  rw [systemLocalRatioErrorConstant]
  positivity

/-- The actual/model ratio is `1 + O_m(p⁻²)` at good primes. -/
theorem abs_systemLocalCoprimeRatio_sub_one_le
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p)
    (hcard : 2 * Fintype.card κ ≤ p) :
    |systemLocalCoprimeRatio p forms - 1| ≤
      systemLocalRatioErrorConstant (Fintype.card κ) /
        (p : ℝ) ^ 2 := by
  let m := Fintype.card κ
  let model := normalizedFirstOrderLocalModel m p
  let scale := ((p : ℝ) / (p - 1 : ℕ)) ^ m
  have hmodelHalf : (1 : ℝ) / 2 ≤ model := by
    exact one_half_le_normalizedFirstOrderLocalModel hp hcard
  have hmodelPos : 0 < model :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hmodelHalf
  have hscale :
      scale ≤ (2 : ℝ) ^ m := by
    exact normalizedLocalScale_le_pow_two m hp
  have hlocal :
      |mean (systemLocalCoprimeWeight p forms) - model| ≤
        scale *
          ((2 : ℝ) ^ m *
            ((1 : ℝ) / (p : ℝ) ^ 2)) := by
    simpa [m, model, scale,
      normalizedFirstOrderLocalModel] using
      (abs_mean_systemLocalCoprimeWeight_sub_firstOrder_le
        hnonzero hindependent hp hlarge)
  have hquot :
      |mean (systemLocalCoprimeWeight p forms) - model| / model ≤
        2 *
          |mean (systemLocalCoprimeWeight p forms) - model| := by
    rw [div_le_iff₀ hmodelPos]
    have hx0 :
        0 ≤
          2 *
            |mean (systemLocalCoprimeWeight p forms) - model| :=
      mul_nonneg (by norm_num) (abs_nonneg _)
    have hmul :=
      mul_le_mul_of_nonneg_left hmodelHalf
        hx0
    nlinarith
  have htailNonneg :
      0 ≤
        (2 : ℝ) ^ m *
          ((1 : ℝ) / (p : ℝ) ^ 2) := by
    positivity
  have hreplace :
      scale *
          ((2 : ℝ) ^ m *
            ((1 : ℝ) / (p : ℝ) ^ 2)) ≤
        (2 : ℝ) ^ m *
          ((2 : ℝ) ^ m *
            ((1 : ℝ) / (p : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_right hscale htailNonneg
  rw [systemLocalCoprimeRatio, div_sub_one hmodelPos.ne',
    abs_div, abs_of_pos hmodelPos]
  calc
    |mean (systemLocalCoprimeWeight p forms) - model| / model ≤
        2 *
          |mean (systemLocalCoprimeWeight p forms) - model| :=
      hquot
    _ ≤
        2 *
          (scale *
            ((2 : ℝ) ^ m *
              ((1 : ℝ) / (p : ℝ) ^ 2))) :=
      mul_le_mul_of_nonneg_left hlocal (by norm_num)
    _ ≤
        2 *
          ((2 : ℝ) ^ m *
            ((2 : ℝ) ^ m *
              ((1 : ℝ) / (p : ℝ) ^ 2))) :=
      mul_le_mul_of_nonneg_left hreplace (by norm_num)
    _ =
        systemLocalRatioErrorConstant m /
          (p : ℝ) ^ 2 := by
      rw [systemLocalRatioErrorConstant]
      ring

/-- The actual/model ratio is strictly positive once the prime is larger
than twice the number of forms. -/
theorem systemLocalCoprimeRatio_pos
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p)
    (hcard : 2 * Fintype.card κ ≤ p) :
    0 < systemLocalCoprimeRatio p forms := by
  let m := Fintype.card κ
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hm_lt_p : m < p := by
    by_cases hm : m = 0
    · simpa [hm] using hp.pos
    · omega
  have hmdiv_lt_one :
      (m : ℝ) / (p : ℝ) < 1 := by
    rw [div_lt_one hpR]
    exact_mod_cast hm_lt_p
  have havoidLower :
      0 < 1 - (m : ℝ) / (p : ℝ) :=
    sub_pos.mpr hmdiv_lt_one
  have havoid :
      0 < mean (localAvoidanceProduct p forms) :=
    havoidLower.trans_le
      (one_sub_card_div_le_mean_localAvoidanceProduct
        hnonzero hp hlarge)
  have hscale :
      0 <
        ((p : ℝ) / (p - 1 : ℕ)) ^ m := by
    have hpred : 0 < ((p - 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
    exact pow_pos (div_pos hpR hpred) m
  have hmean :
      0 < mean (systemLocalCoprimeWeight p forms) := by
    rw [mean_systemLocalCoprimeWeight_eq]
    exact mul_pos hscale havoid
  rw [systemLocalCoprimeRatio]
  exact div_pos hmean
    (normalizedFirstOrderLocalModel_pos hp hcard)

/-! ## CFZ specialization -/

/-- The actual/model good-prime ratio for the CFZ family. -/
noncomputable def cfzSystemLocalCoprimeRatio
    (k : ℕ) (p : Nat.Primes) : ℝ := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  exact systemLocalCoprimeRatio (p : ℕ)
    (fun q : CFZFormIndex k => cfzAffineForm q)

/-- A numerical cutoff containing the coefficient/minor exceptions and the
range in which the first-order model might be smaller than `1/2`. -/
def cfzEulerExceptionalBound (k : ℕ) : ℕ :=
  max
    (exceptionalPrimeBound
      (fun q : CFZFormIndex k => cfzAffineForm q))
    (2 * Fintype.card (CFZFormIndex k))

/-- The square-error constant for the CFZ ratio. -/
noncomputable def cfzEulerErrorConstant (k : ℕ) : ℝ :=
  systemLocalRatioErrorConstant
    (Fintype.card (CFZFormIndex k))

theorem cfzEulerErrorConstant_nonneg (k : ℕ) :
    0 ≤ cfzEulerErrorConstant k :=
  systemLocalRatioErrorConstant_nonneg _

/-- Explicit good-prime square-error estimate for the CFZ ratio. -/
theorem abs_cfzSystemLocalCoprimeRatio_sub_one_le
    {k : ℕ} (hk : 2 ≤ k)
    (p : Nat.Primes)
    (hlarge : cfzEulerExceptionalBound k < (p : ℕ)) :
    |cfzSystemLocalCoprimeRatio k p - 1| ≤
      cfzEulerErrorConstant k / (p : ℝ) ^ 2 := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  have hexceptional :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) <
        (p : ℕ) :=
    (Nat.le_max_left _ _).trans_lt hlarge
  have hcard :
      2 * Fintype.card (CFZFormIndex k) ≤
        (p : ℕ) :=
    (Nat.le_max_right _ _).trans hlarge.le
  simpa [cfzSystemLocalCoprimeRatio,
    cfzEulerErrorConstant] using
    (abs_systemLocalCoprimeRatio_sub_one_le
      (cfzAffineForms_nonzero hk)
      (cfzAffineForms_pairwiseIndependent hk)
      p.prop hexceptional hcard)

/-- Every unmasked good-prime CFZ ratio is positive. -/
theorem cfzSystemLocalCoprimeRatio_pos
    {k : ℕ} (hk : 2 ≤ k)
    (p : Nat.Primes)
    (hlarge : cfzEulerExceptionalBound k < (p : ℕ)) :
    0 < cfzSystemLocalCoprimeRatio k p := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  have hexceptional :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) <
        (p : ℕ) :=
    (Nat.le_max_left _ _).trans_lt hlarge
  have hcard :
      2 * Fintype.card (CFZFormIndex k) ≤
        (p : ℕ) :=
    (Nat.le_max_right _ _).trans hlarge.le
  simpa [cfzSystemLocalCoprimeRatio] using
    (systemLocalCoprimeRatio_pos
      (cfzAffineForms_nonzero hk)
      p.prop hexceptional hcard)

/-- After masking the explicit finite initial range, the full CFZ ratio
family has a global square-decaying error. -/
theorem hasPrimeSquareError_cfzSystemLocalCoprimeRatio
    {k : ℕ} (hk : 2 ≤ k) :
    HasPrimeSquareError
      (cfzEulerErrorConstant k)
      (boundedMaskedPrimeLocalFactor
        (cfzEulerExceptionalBound k)
        (cfzSystemLocalCoprimeRatio k)) := by
  exact hasPrimeSquareError_boundedMasked
    (cfzEulerExceptionalBound k)
    (cfzEulerErrorConstant_nonneg k)
    (fun p hp =>
      abs_cfzSystemLocalCoprimeRatio_sub_one_le hk p hp)

/-- The masked CFZ remainder Euler product is multipliable. -/
theorem multipliable_cfzSystemLocalCoprimeRatio
    {k : ℕ} (hk : 2 ≤ k) :
    Multipliable
      (boundedMaskedPrimeLocalFactor
        (cfzEulerExceptionalBound k)
        (cfzSystemLocalCoprimeRatio k)) :=
  (hasPrimeSquareError_cfzSystemLocalCoprimeRatio hk).multipliable

/-- The bounded masking preserves strict positivity at every prime. -/
theorem boundedMasked_cfzSystemLocalCoprimeRatio_pos
    {k : ℕ} (hk : 2 ≤ k)
    (p : Nat.Primes) :
    0 <
      boundedMaskedPrimeLocalFactor
        (cfzEulerExceptionalBound k)
        (cfzSystemLocalCoprimeRatio k) p := by
  by_cases hp :
      (p : ℕ) ≤ cfzEulerExceptionalBound k
  · rw [boundedMaskedPrimeLocalFactor_of_le hp]
    norm_num
  · rw [boundedMaskedPrimeLocalFactor_of_lt
      (Nat.lt_of_not_ge hp)]
    exact cfzSystemLocalCoprimeRatio_pos hk p
      (Nat.lt_of_not_ge hp)

/-- The convergent masked CFZ Euler product is nonzero. -/
theorem tprod_boundedMasked_cfzSystemLocalCoprimeRatio_ne_zero
    {k : ℕ} (hk : 2 ≤ k) :
    (∏' p : Nat.Primes,
      boundedMaskedPrimeLocalFactor
        (cfzEulerExceptionalBound k)
        (cfzSystemLocalCoprimeRatio k) p) ≠ 0 :=
  (hasPrimeSquareError_cfzSystemLocalCoprimeRatio hk)
    |>.tprod_ne_zero
      (fun p =>
        (boundedMasked_cfzSystemLocalCoprimeRatio_pos hk p).ne')

/-- Remote finite products of the masked CFZ ratios tend uniformly to one.
-/
theorem exists_tail_cfzSystemLocalCoprimeRatio_close_to_one
    {k : ℕ} (hk : 2 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset Nat.Primes,
      ∀ t : Finset Nat.Primes, Disjoint t s →
        |(∏ p ∈ t,
            boundedMaskedPrimeLocalFactor
              (cfzEulerExceptionalBound k)
              (cfzSystemLocalCoprimeRatio k) p) - 1| < ε :=
  (hasPrimeSquareError_cfzSystemLocalCoprimeRatio hk)
    |>.exists_tail_finsetProd_close_to_one hε

end Wikipedia.SzemeredisTheorem
