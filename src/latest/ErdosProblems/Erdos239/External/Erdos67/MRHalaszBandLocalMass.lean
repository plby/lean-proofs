import ErdosProblems.Erdos239.External.Erdos67.MRHalaszThreeBandEuler
import ErdosProblems.Erdos239.External.Erdos67.PrimeEulerTail

/-!
# Prime-band-local Euler mass

The coarse three-band Euler estimate charges the full zeta mass to each
candidate band.  Here we retain the actual mass of the selected prime band.
This is the form which cancels against the missing-band density in the
finite Halasz argument.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset Filter

namespace Erdos67.MRHalaszBands

noncomputable section

open Erdos67 Erdos67.EulerResidue Erdos67.MRHalaszEuler
  Erdos67.MRMultiplicativeEuler

/-- Reciprocal-prime mass restricted to one prime band. -/
def primeBandReciprocalMass
    (P : ℕ → Prop) [DecidablePred P] (X : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo X with P p, 1 / (p : ℝ)

/-- Pretentious distance restricted to one prime band. -/
def primeBandPretentiousDistSq
    (f g : ℕ → ℂ) (P : ℕ → Prop) [DecidablePred P]
    (X : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo X with P p, pretentiousTerm f g p

theorem norm_cpow_halaszPoint_le_inv
    {X p : ℕ} (hX : 1 < X) (hp : p.Prime) (t : ℝ) :
    ‖(p : ℂ) ^ (-halaszPoint X t)‖ ≤ (p : ℝ)⁻¹ := by
  rw [halaszPoint,
    Erdos67.HalaszCpowDeficit.norm_nat_cpow_neg_sigma_add_I_mul
      hp.pos (taoExponent X) t]
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hp.one_le) (by
      have := one_lt_taoExponent hX
      linarith)

/-- On a retained prime, the linear Euler term is bounded by reciprocal
mass minus the smoothed pretentious loss. -/
theorem prime_linearTerm_le_reciprocal_sub_pretentious
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X p : ℕ} (hX : 1 < X) (hp : p.Prime) (hpX : p ≤ X)
    (t : ℝ) :
    (f p * (p : ℂ) ^ (-halaszPoint X t)).re ≤
      1 / (p : ℝ) - Real.exp (-1) *
        pretentiousTerm f (archimedeanTwist t) p := by
  have hz : (f p * conj (archimedeanTwist t p)).re ≤ 1 := by
    calc
      (f p * conj (archimedeanTwist t p)).re ≤
          ‖f p * conj (archimedeanTwist t p)‖ := Complex.re_le_norm _
      _ ≤ 1 := by
        rw [norm_mul, norm_conj, norm_archimedeanTwist hp.pos, mul_one]
        exact hbound p hp.pos
  have hdef :=
    Erdos67.HalaszCpowDeficit.exp_neg_one_mul_pretentiousTerm_le_prime_cpow_deficit
      ⟨p, hp⟩ hX hpX (f p) t hz
  have hdef' :
      Real.exp (-1) * pretentiousTerm f (archimedeanTwist t) p ≤
        ‖(p : ℂ) ^ (-halaszPoint X t)‖ -
          (f p * (p : ℂ) ^ (-halaszPoint X t)).re := by
    simpa only [pretentiousTerm, halaszPoint, taoExponent,
      inv_eq_one_div] using hdef
  have hmass := norm_cpow_halaszPoint_le_inv hX hp t
  rw [one_div]
  linarith

/-- At a prime, the linear term of a band-restricted coefficient is either
the original linear term or zero. -/
theorem primeBand_linearTerm_eq_ite
    (f : ℕ → ℂ) (P : ℕ → Prop) [DecidablePred P]
    {p : ℕ} (hp : p.Prime) (s : ℂ) :
    (primeBandCoefficient f P p * (p : ℂ) ^ (-s)).re =
      if P p then (f p * (p : ℂ) ^ (-s)).re else 0 := by
  rw [primeBandCoefficient_at_prime f P hp]
  split_ifs <;> simp_all

/-- The three restricted reciprocal masses partition the full reciprocal
prime mass. -/
theorem sum_threeBand_primeBandReciprocalMass
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (X : ℕ) :
    primeBandReciprocalMass P₁ X +
        primeBandReciprocalMass (fun p ↦ ¬ P₁ p ∧ P₂ p) X +
        primeBandReciprocalMass (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) X =
      ∑ p ∈ primesUpTo X, 1 / (p : ℝ) := by
  unfold primeBandReciprocalMass
  let a : ℕ → ℝ := fun p ↦ 1 / (p : ℝ)
  have houter := Finset.sum_filter_add_sum_filter_not
    (primesUpTo X) P₁ a
  have hinner := Finset.sum_filter_add_sum_filter_not
    ((primesUpTo X).filter (fun p ↦ ¬ P₁ p)) P₂ a
  simp only [Finset.filter_filter, a] at hinner
  calc
    ∑ p ∈ primesUpTo X with P₁ p, 1 / (p : ℝ) +
          ∑ p ∈ primesUpTo X with (¬ P₁ p ∧ P₂ p), 1 / (p : ℝ) +
          ∑ p ∈ primesUpTo X with (¬ P₁ p ∧ ¬ P₂ p), 1 / (p : ℝ) =
        (∑ p ∈ primesUpTo X with P₁ p, a p) +
          ((∑ p ∈ primesUpTo X with (¬ P₁ p ∧ P₂ p), a p) +
           ∑ p ∈ primesUpTo X with (¬ P₁ p ∧ ¬ P₂ p), a p) := by
      simp only [a]
      ring
    _ = (∑ p ∈ primesUpTo X with P₁ p, a p) +
        ∑ p ∈ (primesUpTo X).filter (fun p ↦ ¬ P₁ p), a p := by
      rw [hinner]
    _ = ∑ p ∈ primesUpTo X, a p := houter

/-- The three restricted distances partition the original distance exactly. -/
theorem sum_threeBand_primeBandPretentiousDistSq
    (f g : ℕ → ℂ) (P₁ P₂ : ℕ → Prop)
    [DecidablePred P₁] [DecidablePred P₂] (X : ℕ) :
    primeBandPretentiousDistSq f g P₁ X +
        primeBandPretentiousDistSq f g (fun p ↦ ¬ P₁ p ∧ P₂ p) X +
        primeBandPretentiousDistSq f g (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) X =
      pretentiousDistSq f g X := by
  unfold primeBandPretentiousDistSq pretentiousDistSq
  let a : ℕ → ℝ := fun p ↦ pretentiousTerm f g p
  have houter := Finset.sum_filter_add_sum_filter_not
    (primesUpTo X) P₁ a
  have hinner := Finset.sum_filter_add_sum_filter_not
    ((primesUpTo X).filter (fun p ↦ ¬ P₁ p)) P₂ a
  simp only [Finset.filter_filter, a] at hinner
  calc
    ∑ p ∈ primesUpTo X with P₁ p, pretentiousTerm f g p +
          ∑ p ∈ primesUpTo X with (¬ P₁ p ∧ P₂ p), pretentiousTerm f g p +
          ∑ p ∈ primesUpTo X with (¬ P₁ p ∧ ¬ P₂ p), pretentiousTerm f g p =
        (∑ p ∈ primesUpTo X with P₁ p, a p) +
          ((∑ p ∈ primesUpTo X with (¬ P₁ p ∧ P₂ p), a p) +
           ∑ p ∈ primesUpTo X with (¬ P₁ p ∧ ¬ P₂ p), a p) := by
      simp only [a]
      ring
    _ = (∑ p ∈ primesUpTo X with P₁ p, a p) +
        ∑ p ∈ (primesUpTo X).filter (fun p ↦ ¬ P₁ p), a p := by
      rw [hinner]
    _ = ∑ p ∈ primesUpTo X, a p := houter

/-- The main exponent contributed by one band: its own prime mass minus
the smoothed pretentious loss on that band. -/
def primeBandEulerScore
    (f : ℕ → ℂ) (P : ℕ → Prop) [DecidablePred P]
    (X : ℕ) (t : ℝ) : ℝ :=
  primeBandReciprocalMass P X - Real.exp (-1) *
    primeBandPretentiousDistSq f (archimedeanTwist t) P X

/-- The three local Euler scores add to the original full mass minus its
pretentious loss. -/
theorem sum_threeBand_primeBandEulerScore
    (f : ℕ → ℂ) (P₁ P₂ : ℕ → Prop)
    [DecidablePred P₁] [DecidablePred P₂] (X : ℕ) (t : ℝ) :
    primeBandEulerScore f P₁ X t +
        primeBandEulerScore f (fun p ↦ ¬ P₁ p ∧ P₂ p) X t +
        primeBandEulerScore f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) X t =
      (∑ p ∈ primesUpTo X, 1 / (p : ℝ)) -
        Real.exp (-1) * pretentiousDistSq f (archimedeanTwist t) X := by
  unfold primeBandEulerScore
  have hm := sum_threeBand_primeBandReciprocalMass P₁ P₂ X
  have hd := sum_threeBand_primeBandPretentiousDistSq
    f (archimedeanTwist t) P₁ P₂ X
  calc
    _ = (primeBandReciprocalMass P₁ X +
          primeBandReciprocalMass (fun p ↦ ¬ P₁ p ∧ P₂ p) X +
          primeBandReciprocalMass (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) X) -
        Real.exp (-1) *
          (primeBandPretentiousDistSq f (archimedeanTwist t) P₁ X +
            primeBandPretentiousDistSq f (archimedeanTwist t)
              (fun p ↦ ¬ P₁ p ∧ P₂ p) X +
            primeBandPretentiousDistSq f (archimedeanTwist t)
              (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) X) := by ring
    _ = _ := by rw [hm, hd]

/-- At least one band has no more than one third of the total local Euler
score.  Unlike the coarse distance pigeonhole, this retains the band-local
prime mass. -/
theorem one_primeBandEulerScore_le_one_third
    (f : ℕ → ℂ) (P₁ P₂ : ℕ → Prop)
    [DecidablePred P₁] [DecidablePred P₂] (X : ℕ) (t : ℝ) :
    primeBandEulerScore f P₁ X t ≤
        (((∑ p ∈ primesUpTo X, 1 / (p : ℝ)) -
          Real.exp (-1) * pretentiousDistSq f (archimedeanTwist t) X) / 3) ∨
      primeBandEulerScore f (fun p ↦ ¬ P₁ p ∧ P₂ p) X t ≤
        (((∑ p ∈ primesUpTo X, 1 / (p : ℝ)) -
          Real.exp (-1) * pretentiousDistSq f (archimedeanTwist t) X) / 3) ∨
      primeBandEulerScore f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) X t ≤
        (((∑ p ∈ primesUpTo X, 1 / (p : ℝ)) -
          Real.exp (-1) * pretentiousDistSq f (archimedeanTwist t) X) / 3) := by
  have hsum := sum_threeBand_primeBandEulerScore f P₁ P₂ X t
  by_contra h
  push Not at h
  linarith

/-- A convenient absolute constant for the prime tail above the Halasz
cutoff. -/
def primeBandEulerTailConstant : ℝ :=
  4 * (Real.log 2 + primeLogIntervalMertensConstant) / Real.log 2

theorem primeBandEulerTailConstant_nonneg :
    0 ≤ primeBandEulerTailConstant := by
  unfold primeBandEulerTailConstant
  exact div_nonneg
    (mul_nonneg (by norm_num)
      (add_nonneg (Real.log_pos one_lt_two).le
        primeLogIntervalMertensConstant_nonneg))
    (Real.log_pos one_lt_two).le

/-- A finite Euler product sees only a uniformly bounded amount of prime
mass above its natural Halasz cutoff. -/
theorem sum_primesBelow_halaszPoint_tail_le
    {X N : ℕ} (hX : 4 ≤ X) (t : ℝ) :
    (∑ p ∈ N.primesBelow with X < p,
        ‖(p : ℂ) ^ (-halaszPoint X t)‖) ≤
      primeBandEulerTailConstant := by
  have hsubset : (N.primesBelow.filter fun p ↦ X < p) ⊆
      primesBetween X N := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hprime := Nat.prime_of_mem_primesBelow hp'.1
    have hpN := (Nat.mem_primesBelow.mp hp'.1).1.le
    exact mem_primesBetween.mpr ⟨hprime, hp'.2, hpN⟩
  calc
    (∑ p ∈ N.primesBelow with X < p,
        ‖(p : ℂ) ^ (-halaszPoint X t)‖) =
      ∑ p ∈ N.primesBelow with X < p,
        (p : ℝ) ^ (-(1 + (Real.log (X : ℝ))⁻¹)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [halaszPoint,
        Erdos67.HalaszCpowDeficit.norm_nat_cpow_neg_sigma_add_I_mul
          (Nat.Prime.pos (Nat.prime_of_mem_primesBelow
            (Finset.mem_filter.mp hp).1)) (taoExponent X) t]
      rfl
    _ ≤ ∑ p ∈ primesBetween X N,
        (p : ℝ) ^ (-(1 + (Real.log (X : ℝ))⁻¹)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p hp hnot
      exact Real.rpow_nonneg (Nat.cast_nonneg p) _
    _ ≤ primeBandEulerTailConstant := by
      simpa only [primeBandEulerTailConstant] using
        reciprocalLog_primeRpow_tail_le hX (Z := N)

/-- Once `N>X`, filtering its primes by `p≤X` gives precisely the primes
up to `X`. -/
theorem primesBelow_filter_le_eq_primesUpTo
    {X N : ℕ} (hXN : X < N) :
    N.primesBelow.filter (fun p ↦ p ≤ X) = primesUpTo X := by
  ext p
  simp only [Finset.mem_filter, Nat.mem_primesBelow, mem_primesUpTo]
  constructor
  · rintro ⟨⟨hpN, hp⟩, hpX⟩
    exact ⟨hp, hpX⟩
  · rintro ⟨hp, hpX⟩
    exact ⟨⟨hpX.trans_lt hXN, hp⟩, hpX⟩

/-- The linear Euler terms of one band are bounded by its local score plus
the uniform prime tail. -/
theorem sum_primeBand_linearTerm_le_score_add_tail
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P : ℕ → Prop) [DecidablePred P]
    {X N : ℕ} (hX : 4 ≤ X) (hXN : X < N) (t : ℝ) :
    (∑ p ∈ N.primesBelow,
        (primeBandCoefficient f P p *
          (p : ℂ) ^ (-halaszPoint X t)).re) ≤
      primeBandEulerScore f P X t + primeBandEulerTailConstant := by
  let r : ℕ → ℝ := fun p ↦ ‖(p : ℂ) ^ (-halaszPoint X t)‖
  let b : ℕ → ℝ := fun p ↦
    1 / (p : ℝ) - Real.exp (-1) *
      pretentiousTerm f (archimedeanTwist t) p
  let q : ℕ → ℝ := fun p ↦
    if p ≤ X then
      if P p then b p else 0
    else r p
  have hpoint : ∀ p ∈ N.primesBelow,
      (primeBandCoefficient f P p *
          (p : ℂ) ^ (-halaszPoint X t)).re ≤ q p := by
    intro p hpN
    have hp := Nat.prime_of_mem_primesBelow hpN
    by_cases hpX : p ≤ X
    · by_cases hP : P p
      · rw [primeBand_linearTerm_eq_ite f P hp, if_pos hP]
        simp only [q, if_pos hpX, hP]
        exact prime_linearTerm_le_reciprocal_sub_pretentious
          hbound (by omega) hp hpX t
      · rw [primeBand_linearTerm_eq_ite f P hp, if_neg hP]
        simp [q, hpX, hP]
    · have hr0 : 0 ≤ r p := norm_nonneg _
      rw [primeBand_linearTerm_eq_ite f P hp]
      simp only [q, if_neg hpX]
      by_cases hP : P p
      · rw [if_pos hP]
        exact (Complex.re_le_norm _).trans (by
          rw [norm_mul]
          simpa only [r, one_mul] using mul_le_mul_of_nonneg_right
            (hbound p hp.pos) (norm_nonneg ((p : ℂ) ^ (-halaszPoint X t))))
      · rw [if_neg hP]
        exact hr0
  have hsum := Finset.sum_le_sum hpoint
  have hsplit : (∑ p ∈ N.primesBelow, q p) =
      (∑ p ∈ (N.primesBelow.filter (fun p ↦ p ≤ X)).filter P,
        b p) +
      ∑ p ∈ N.primesBelow with X < p, r p := by
    classical
    rw [Finset.sum_filter P b,
      Finset.sum_filter (fun p ↦ X < p) r,
      Finset.sum_filter (fun p ↦ p ≤ X)
        (fun p ↦ if P p then b p else 0),
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only [q]
    by_cases hpX : p ≤ X
    · simp [hpX]
    · simp [hpX, lt_of_not_ge hpX]
  rw [hsplit] at hsum
  have hlow :
      (∑ p ∈ (N.primesBelow.filter (fun p ↦ p ≤ X)).filter P,
        b p) =
        primeBandEulerScore f P X t := by
    rw [primesBelow_filter_le_eq_primesUpTo hXN]
    unfold primeBandEulerScore primeBandReciprocalMass
      primeBandPretentiousDistSq
    dsimp only [b]
    rw [Finset.mul_sum, Finset.sum_sub_distrib]
  have htail := sum_primesBelow_halaszPoint_tail_le hX (N := N) t
  change (∑ p ∈ N.primesBelow with X < p, r p) ≤
    primeBandEulerTailConstant at htail
  rw [hlow] at hsum
  nlinarith

/-- Complete band Euler bound with the band-local reciprocal mass retained.
The only terms not in the local score are two universal Euler-tail
constants. -/
theorem norm_LSeries_primeBand_halaszPoint_le_localScore
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P : ℕ → Prop) [DecidablePred P]
    {X : ℕ} (hX : 4 ≤ X) (t : ℝ) :
    ‖LSeries (primeBandCoefficient f P) (halaszPoint X t)‖ ≤
      Real.exp
        (primeBandEulerScore f P X t + primeBandEulerTailConstant +
          3 * Erdos67.EulerQuantitative.primeQuadraticConstant) := by
  let a : ℕ → ℂ := primeBandCoefficient f P
  let r : ℕ → ℝ := fun p ↦ ‖(p : ℂ) ^ (-halaszPoint X t)‖
  let E : ℝ := primeBandEulerScore f P X t +
    primeBandEulerTailConstant +
      3 * Erdos67.EulerQuantitative.primeQuadraticConstant
  have haMul : IsMultiplicativeOnPositiveNat a :=
    primeBandCoefficient_isMultiplicativeOnPositiveNat hmul P
  have haBound : ∀ n, 0 < n → ‖a n‖ ≤ 1 := by
    intro n hn
    exact norm_primeBandCoefficient_le_one hbound P hn
  have hs : 1 < (halaszPoint X t).re := by
    rw [halaszPoint_re]
    exact one_lt_taoExponent (by omega)
  have hlim := tendsto_multiplicative_eulerProduct haMul haBound hs
  have hnorm := hlim.norm
  have hfinite : ∀ᶠ N : ℕ in atTop,
      ‖∏ p ∈ N.primesBelow,
          ∑' e : ℕ, a (p ^ e) *
            ((p : ℂ) ^ (-halaszPoint X t)) ^ e‖ ≤ Real.exp E := by
    filter_upwards [eventually_gt_atTop X] with N hXN
    have hsquare :
        (∑ p ∈ N.primesBelow, r p ^ 2) ≤
          Erdos67.EulerQuantitative.primeQuadraticConstant := by
      let G : Nat.Primes → ℝ := fun p ↦
        ‖(p.1 : ℂ) ^ (-halaszPoint X t)‖ ^ 2
      have hGs : Summable G := summable_primeCpowNorm_sq hs
      calc
        (∑ p ∈ N.primesBelow, r p ^ 2) =
            ∑ p : {p // p ∈ N.primesBelow}, G
              ⟨p, Nat.prime_of_mem_primesBelow p.property⟩ := by
          rw [Finset.sum_subtype N.primesBelow (fun _ ↦ Iff.rfl)]
        _ ≤ ∑' p : Nat.Primes, G p :=
          sum_primesBelow_le_tsum hGs (fun p ↦ sq_nonneg _) N
        _ ≤ Erdos67.EulerQuantitative.primeQuadraticConstant := by
          simpa only [G] using
            tsum_primeCpowNorm_sq_halaszPoint_le_constant (by omega) t
    have hlinear := sum_primeBand_linearTerm_le_score_add_tail
      hbound P hX hXN t
    calc
      ‖∏ p ∈ N.primesBelow,
          ∑' e : ℕ, a (p ^ e) *
            ((p : ℂ) ^ (-halaszPoint X t)) ^ e‖ =
          ∏ p ∈ N.primesBelow,
            ‖∑' e : ℕ, a (p ^ e) *
              ((p : ℂ) ^ (-halaszPoint X t)) ^ e‖ := by
        rw [norm_prod]
      _ ≤ ∏ p ∈ N.primesBelow,
          Real.exp
            ((a p * (p : ℂ) ^ (-halaszPoint X t)).re +
              3 * r p ^ 2) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact norm_nonneg _
        · intro p hp
          have hpPrime := Nat.prime_of_mem_primesBelow hp
          have hlocal := norm_multiplicative_localEulerFactor_halaszPoint_le
            (X := X) (p := p) haMul haBound (by omega) hpPrime t
          refine hlocal.trans_eq ?_
          congr 1
          unfold multiplicativeEulerDeficit r
          ring
      _ = Real.exp
          (∑ p ∈ N.primesBelow,
            ((a p * (p : ℂ) ^ (-halaszPoint X t)).re +
              3 * r p ^ 2)) := by
        rw [Real.exp_sum]
      _ ≤ Real.exp E := by
        apply Real.exp_le_exp.mpr
        have heq :
            (∑ p ∈ N.primesBelow,
              ((a p * (p : ℂ) ^ (-halaszPoint X t)).re +
                3 * r p ^ 2)) =
              (∑ p ∈ N.primesBelow,
                (a p * (p : ℂ) ^ (-halaszPoint X t)).re) +
                3 * (∑ p ∈ N.primesBelow, r p ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
        rw [heq]
        dsimp only [a] at hlinear ⊢
        dsimp only [E]
        linarith
  exact le_of_tendsto hnorm hfinite

/-- The selection-free common bound after retaining the local mass of each
of the three prime bands. -/
def threeBandLocalEulerBound (A X : ℕ) : ℝ :=
  Real.exp
    ((((∑ p ∈ primesUpTo X, 1 / (p : ℝ)) -
        Real.exp (-1) * (A : ℝ)) / 3) +
      primeBandEulerTailConstant +
        3 * Erdos67.EulerQuantitative.primeQuadraticConstant)

/-- At each admissible frequency, one of the three band L-series is small
with only one third of the full reciprocal-prime mass. -/
theorem one_threeBand_LSeries_small_localMass
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {A X : ℕ} (hX : 4 ≤ X)
    (hnonpret : MRArchimedeanNonpretentious f A X)
    {t : ℝ} (ht : |t| ≤ X) :
    ‖LSeries (primeBandCoefficient f P₁) (halaszPoint X t)‖ ≤
        threeBandLocalEulerBound A X ∨
      ‖LSeries
          (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p))
          (halaszPoint X t)‖ ≤ threeBandLocalEulerBound A X ∨
      ‖LSeries
          (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p))
          (halaszPoint X t)‖ ≤ threeBandLocalEulerBound A X := by
  have hscore := one_primeBandEulerScore_le_one_third f P₁ P₂ X t
  have hdist := hnonpret t ht
  have hscore' :
      primeBandEulerScore f P₁ X t ≤
          (((∑ p ∈ primesUpTo X, 1 / (p : ℝ)) -
            Real.exp (-1) * (A : ℝ)) / 3) ∨
        primeBandEulerScore f (fun p ↦ ¬ P₁ p ∧ P₂ p) X t ≤
          (((∑ p ∈ primesUpTo X, 1 / (p : ℝ)) -
            Real.exp (-1) * (A : ℝ)) / 3) ∨
        primeBandEulerScore f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) X t ≤
          (((∑ p ∈ primesUpTo X, 1 / (p : ℝ)) -
            Real.exp (-1) * (A : ℝ)) / 3) := by
    rcases hscore with hscore | hscore | hscore
    · exact Or.inl (hscore.trans (by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        gcongr))
    · exact Or.inr (Or.inl (hscore.trans (by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        gcongr)))
    · exact Or.inr (Or.inr (hscore.trans (by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        gcongr)))
  rcases hscore' with hscore' | hscore' | hscore'
  · left
    refine (norm_LSeries_primeBand_halaszPoint_le_localScore
      hmul hbound P₁ hX t).trans ?_
    apply Real.exp_le_exp.mpr
    linarith
  · right; left
    refine (norm_LSeries_primeBand_halaszPoint_le_localScore
      hmul hbound (fun p ↦ ¬ P₁ p ∧ P₂ p) hX t).trans ?_
    apply Real.exp_le_exp.mpr
    linarith
  · right; right
    refine (norm_LSeries_primeBand_halaszPoint_le_localScore
      hmul hbound (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) hX t).trans ?_
    apply Real.exp_le_exp.mpr
    linarith

end

end Erdos67.MRHalaszBands
