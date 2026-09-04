import ErdosProblems.Erdos67.MRGSA9A13Composition
import Mathlib.NumberTheory.LSeries.Positivity

/-!
# The full-series A.13--A.14 composition

This file combines the two genuine block-factor estimates with the common
high-prime factor.  The outside low-prime factor is kept exact; in
particular, no logarithmic estimate at the prime `2` is required.  Positive
prime-band series then recombine to the Riemann zeta function.
-/

open scoped BigOperators LSeries.notation ComplexOrder

namespace Erdos67.MRHalaszBands

noncomputable section

open Erdos67.EulerQuantitative

/-- Replacing a one-bounded coefficient by `1` on the same prime band
majorizes the norm of its L-series on every vertical line. -/
theorem norm_LSeries_primeBandCoefficient_le_positive
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P : ℕ → Prop) [DecidablePred P]
    {sigma t : ℝ} (hsigma : 1 < sigma) :
    ‖LSeries (primeBandCoefficient f P)
        ((sigma : ℂ) + Complex.I * (t : ℂ))‖ ≤
      ‖LSeries (primeBandCoefficient (fun _ : ℕ ↦ (1 : ℂ)) P)
        (sigma : ℂ)‖ := by
  let a : ℕ → ℂ := primeBandCoefficient (fun _ : ℕ ↦ (1 : ℂ)) P
  have haBound : ∀ n, n ≠ 0 → ‖a n‖ ≤ 1 := by
    intro n hn
    exact norm_primeBandCoefficient_le_one (fun _ _ ↦ by norm_num) P
      (Nat.pos_of_ne_zero hn)
  have haNonneg : ∀ n, 0 ≤ a n := by
    intro n
    dsimp only [a]
    unfold primeBandCoefficient
    split_ifs <;> simp
  have haOne : 0 < a 1 := by
    simp [a, primeBandCoefficient, primeSupported_one]
  have hsumA : LSeriesSummable a (sigma : ℂ) :=
    LSeriesSummable_of_bounded_of_one_lt_re haBound (by simpa using hsigma)
  have habscissa : LSeries.abscissaOfAbsConv a ≤ (1 : EReal) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro x hx
    exact LSeriesSummable_of_bounded_of_one_lt_re haBound (by simpa using hx)
  have habscissaLt : LSeries.abscissaOfAbsConv a < (sigma : EReal) :=
    habscissa.trans_lt (by exact_mod_cast hsigma)
  have hpos : 0 < LSeries a (sigma : ℂ) :=
    LSeries.positive haNonneg haOne habscissaLt
  have hterm (n : ℕ) :
      ‖LSeries.term a (sigma : ℂ) n‖ =
        (LSeries.term a (sigma : ℂ) n).re := by
    have hn := LSeries.term_nonneg (haNonneg n) sigma
    rw [Complex.nonneg_iff] at hn
    have heq : LSeries.term a (sigma : ℂ) n =
        ((LSeries.term a (sigma : ℂ) n).re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using hn.2.symm
    calc
      ‖LSeries.term a (sigma : ℂ) n‖ =
          ‖((LSeries.term a (sigma : ℂ) n).re : ℂ)‖ :=
        congrArg norm heq
      _ = (LSeries.term a (sigma : ℂ) n).re := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn.1]
  have hmass :
      (∑' n : ℕ, ‖LSeries.term a (sigma : ℂ) n‖) =
        (LSeries a (sigma : ℂ)).re := by
    unfold LSeries
    rw [Complex.re_tsum hsumA]
    exact tsum_congr hterm
  have hnormA : ‖LSeries a (sigma : ℂ)‖ =
      (LSeries a (sigma : ℂ)).re := by
    have hp := Complex.pos_iff.mp hpos
    have heq : LSeries a (sigma : ℂ) =
        ((LSeries a (sigma : ℂ)).re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using hp.2.symm
    calc
      ‖LSeries a (sigma : ℂ)‖ =
          ‖((LSeries a (sigma : ℂ)).re : ℂ)‖ := congrArg norm heq
      _ = (LSeries a (sigma : ℂ)).re := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp.1]
  have hsumF : LSeriesSummable (primeBandCoefficient f P)
      ((sigma : ℂ) + Complex.I * (t : ℂ)) :=
    primeBandCoefficient_LSeriesSummable hbound P (by simpa using hsigma)
  have hcoeff (n : ℕ) :
      ‖primeBandCoefficient f P n‖ ≤ ‖a n‖ := by
    dsimp only [a]
    unfold primeBandCoefficient
    by_cases hn : PrimeSupported P n
    · simp only [if_pos hn, norm_one]
      exact hbound n (Nat.pos_of_ne_zero hn.1)
    · simp [hn]
  unfold LSeries
  calc
    ‖∑' n : ℕ,
        LSeries.term (primeBandCoefficient f P)
          ((sigma : ℂ) + Complex.I * (t : ℂ)) n‖ ≤
        ∑' n : ℕ,
          ‖LSeries.term (primeBandCoefficient f P)
            ((sigma : ℂ) + Complex.I * (t : ℂ)) n‖ :=
      norm_tsum_le_tsum_norm hsumF.norm
    _ ≤ ∑' n : ℕ, ‖LSeries.term a (sigma : ℂ) n‖ := by
      apply Summable.tsum_le_tsum
      · intro n
        rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
        split_ifs
        · exact le_rfl
        · simpa using div_le_div_of_nonneg_right (hcoeff n) (by positivity)
      · exact hsumF.norm
      · exact hsumA.norm
    _ = ‖∑' n : ℕ, LSeries.term a (sigma : ℂ) n‖ := by
      change (∑' n : ℕ, ‖LSeries.term a (sigma : ℂ) n‖) =
        ‖LSeries a (sigma : ℂ)‖
      rw [hmass, hnormA]

/-- A finite prime-square sum on `Re s > 1` is bounded by the fixed
quadratic Euler constant. -/
theorem sum_norm_prime_cpow_sq_le_primeQuadraticConstant
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    {sigma t : ℝ} (hsigma : 1 < sigma) :
    (∑ p ∈ S,
        ‖(p : ℂ) ^ (-((sigma : ℂ) + Complex.I * (t : ℂ)))‖ ^ 2) ≤
      primeQuadraticConstant := by
  let e : {p // p ∈ S} → Nat.Primes := fun p ↦ ⟨p, hprime p p.property⟩
  have heinj : Function.Injective e := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun z : Nat.Primes ↦ (z : ℕ)) hpq
  let T : Finset Nat.Primes := Finset.univ.map ⟨e, heinj⟩
  let s : ℂ := (sigma : ℂ) + Complex.I * (t : ℂ)
  let G : Nat.Primes → ℝ := fun p ↦ ‖(p.1 : ℂ) ^ (-s)‖ ^ 2
  have hs : 1 < s.re := by simpa [s] using hsigma
  have hGs : Summable G := by
    exact Erdos67.MRHalaszEuler.summable_primeCpowNorm_sq hs
  have hsumEq :
      (∑ p ∈ S, ‖(p : ℂ) ^ (-s)‖ ^ 2) = ∑ p ∈ T, G p := by
    rw [Finset.sum_subtype S (fun _ ↦ Iff.rfl), Finset.sum_map]
    rfl
  have hsumT : (∑ p ∈ T, G p) ≤ ∑' p : Nat.Primes, G p :=
    hGs.sum_le_tsum T (fun p _ ↦ sq_nonneg _)
  have hnorm (p : Nat.Primes) :
      ‖(p.1 : ℂ) ^ (-s)‖ = (p.1 : ℝ) ^ (-sigma) := by
    dsimp only [s]
    exact Erdos67.HalaszCpowDeficit.norm_prime_cpow_neg_sigma_add_I_mul
      p sigma t
  have htotal : (∑' p : Nat.Primes, G p) ≤ primeQuadraticConstant := by
    have htwo := tsum_primeQuadraticError_le_constant hsigma
    have hnonneg : 0 ≤ ∑' p : Nat.Primes, G p :=
      tsum_nonneg fun p ↦ sq_nonneg _
    have heq : (∑' p : Nat.Primes, 2 * G p) =
        2 * ∑' p : Nat.Primes, G p := by rw [hGs.tsum_mul_left]
    have htwo' : 2 * ∑' p : Nat.Primes, G p ≤ primeQuadraticConstant := by
      rw [← heq]
      simpa only [G, hnorm] using htwo
    exact le_trans (by linarith) htwo'
  rw [show ((sigma : ℂ) + Complex.I * (t : ℂ)) = s by rfl]
  calc
    (∑ p ∈ S, ‖(p : ℂ) ^ (-s)‖ ^ 2) = ∑ p ∈ T, G p := hsumEq
    _ ≤ ∑' p : Nat.Primes, G p := hsumT
    _ ≤ primeQuadraticConstant := htotal

/-- Three disjoint filters (`Q`, `R`, and their common complement) recover
the original finite product. -/
theorem prod_neither_mul_prod_left_mul_prod_right_eq
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (Q R : ι → Prop) [DecidablePred Q] [DecidablePred R]
    (hdisj : ∀ x ∈ S, Q x → R x → False) (a : ι → ℂ) :
    (∏ x ∈ S with ¬ Q x ∧ ¬ R x, a x) *
        (∏ x ∈ S with Q x, a x) *
        (∏ x ∈ S with R x, a x) =
      ∏ x ∈ S, a x := by
  let A := S.filter Q
  let B := S.filter R
  let O := S.filter (fun x ↦ ¬ Q x ∧ ¬ R x)
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact hdisj x (Finset.mem_filter.mp hxA).1
      (Finset.mem_filter.mp hxA).2 (Finset.mem_filter.mp hxB).2
  have hAO : Disjoint A O := by
    rw [Finset.disjoint_left]
    intro x hxA hxO
    exact (Finset.mem_filter.mp hxO).2.1 (Finset.mem_filter.mp hxA).2
  have hBO : Disjoint B O := by
    rw [Finset.disjoint_left]
    intro x hxB hxO
    exact (Finset.mem_filter.mp hxO).2.2 (Finset.mem_filter.mp hxB).2
  have hA_BO : Disjoint A (B ∪ O) := by
    rw [Finset.disjoint_left]
    intro x hxA hxBO
    rw [Finset.mem_union] at hxBO
    exact hxBO.elim (fun hxB ↦ Finset.disjoint_left.mp hAB hxA hxB)
      (fun hxO ↦ Finset.disjoint_left.mp hAO hxA hxO)
  have hpartition : A ∪ (B ∪ O) = S := by
    ext x
    simp only [A, B, O, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩ | ⟨hx, _⟩)
      all_goals exact hx
    · intro hx
      by_cases hQ : Q x
      · exact Or.inl ⟨hx, hQ⟩
      · by_cases hR : R x
        · exact Or.inr (Or.inl ⟨hx, hR⟩)
        · exact Or.inr (Or.inr ⟨hx, hQ, hR⟩)
  change (∏ x ∈ O, a x) * (∏ x ∈ A, a x) * (∏ x ∈ B, a x) = _
  calc
    (∏ x ∈ O, a x) * (∏ x ∈ A, a x) * (∏ x ∈ B, a x) =
        (∏ x ∈ A, a x) * ((∏ x ∈ B, a x) * ∏ x ∈ O, a x) := by
      ring
    _ = ∏ x ∈ S, a x := by
      rw [← Finset.prod_union hBO, ← Finset.prod_union hA_BO, hpartition]

/-- Squared form of the genuine block estimate.  It is convenient when the
two blocks are recombined with the low/high factorization. -/
theorem sq_le_exp_radius_add_twenty_mul_square_mul_of_block_bounds
    {a p z R V : ℝ} (ha : 0 ≤ a)
    (hupper : a * Real.exp (-R / 2) ≤ Real.exp (z / 2 + 8 * V))
    (hlower : Real.exp (z - 4 * V) ≤ p) :
    a ^ 2 ≤ Real.exp (R + 20 * V) * p := by
  have hsq := mul_self_le_mul_self
    (mul_nonneg ha (Real.exp_pos _).le) hupper
  have hcancel : Real.exp (-R / 2) ^ 2 * Real.exp R = 1 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring_nf
  calc
    a ^ 2 = (a * Real.exp (-R / 2)) ^ 2 * Real.exp R := by
      rw [mul_pow]
      nlinarith
    _ ≤ Real.exp (z / 2 + 8 * V) ^ 2 * Real.exp R := by
      gcongr
    _ = Real.exp (R + 20 * V) * Real.exp (z - 4 * V) := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (R + 20 * V) * p := by gcongr

/-- Full A.13--A.14 estimate.  The alternating low factor times the common
high factor is bounded by the geometric mean of the original L-series and
zeta, up to a fixed quadratic-prime constant. -/
theorem norm_twoBlock_alternatingLow_mul_high_le_sqrt_full_mul_sqrt_zeta
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Q₂ Q₃ : ℕ → Prop) [DecidablePred Q₂] [DecidablePred Q₃]
    (y : ℕ)
    (hQ₂ : ∀ p, Q₂ p → p ≤ y) (hQ₃ : ∀ p, Q₃ p → p ≤ y)
    (hdisj : ∀ p ∈ primesUpTo y, Q₂ p → Q₃ p → False)
    (hthree₂ : ∀ p ∈ primesUpTo y, Q₂ p → 3 ≤ p)
    (hthree₃ : ∀ p ∈ primesUpTo y, Q₃ p → 3 ≤ p)
    {sigma t : ℝ} (hsigma : 1 < sigma) :
    let s : ℂ := (sigma : ℂ) + Complex.I * (t : ℂ)
    let Alt := LSeries (gsA9Low f y) s -
        LSeries (gsA9LowDeletion f Q₂ y) s -
        LSeries (gsA9LowDeletion f Q₃ y) s +
        LSeries (gsA9LowDeletion f (fun p ↦ Q₂ p ∨ Q₃ p) y) s
    ‖Alt * LSeries (gsA9High f y) s‖ ≤
      Real.exp (24 * primeQuadraticConstant) *
        Real.sqrt ‖LSeries f s‖ *
        Real.sqrt (riemannZeta (sigma : ℂ)).re := by
  dsimp only
  let s : ℂ := (sigma : ℂ) + Complex.I * (t : ℂ)
  let S₀ : Finset ℕ :=
    (primesUpTo y).filter (fun p ↦ ¬ Q₂ p ∧ ¬ Q₃ p)
  let S₂ : Finset ℕ := (primesUpTo y).filter Q₂
  let S₃ : Finset ℕ := (primesUpTo y).filter Q₃
  let z₂ : ℂ := ∑ p ∈ S₂, f p * (p : ℂ) ^ (-s)
  let z₃ : ℂ := ∑ p ∈ S₃, f p * (p : ℂ) ^ (-s)
  let R₂ : ℝ := ∑ p ∈ S₂, ‖(p : ℂ) ^ (-s)‖
  let R₃ : ℝ := ∑ p ∈ S₃, ‖(p : ℂ) ^ (-s)‖
  let V₂ : ℝ := ∑ p ∈ S₂, ‖(p : ℂ) ^ (-s)‖ ^ 2
  let V₃ : ℝ := ∑ p ∈ S₃, ‖(p : ℂ) ^ (-s)‖ ^ 2
  let P₀ : ℂ := ∏ p ∈ S₀, gsA9LocalEulerFactor f s p
  let P₂ : ℂ := ∏ p ∈ S₂, gsA9LocalEulerFactor f s p
  let P₃ : ℂ := ∏ p ∈ S₃, gsA9LocalEulerFactor f s p
  let H : ℂ := LSeries (gsA9High f y) s
  let one : ℕ → ℂ := fun _ ↦ 1
  let sr : ℂ := (sigma : ℂ)
  let P₀p : ℂ := ∏ p ∈ S₀, gsA9LocalEulerFactor one sr p
  let P₂p : ℂ := ∏ p ∈ S₂, gsA9LocalEulerFactor one sr p
  let P₃p : ℂ := ∏ p ∈ S₃, gsA9LocalEulerFactor one sr p
  let Hp : ℂ := LSeries (gsA9High one y) sr
  have hsre : 1 < s.re := by simpa [s] using hsigma
  have hsreWeak : 1 ≤ s.re := hsre.le
  have hsrre : 1 < sr.re := by simpa [sr] using hsigma
  have hsrreWeak : 1 ≤ sr.re := hsrre.le
  have hS₀prime : ∀ p ∈ S₀, p.Prime := by
    intro p hp
    exact (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
  have hS₂prime : ∀ p ∈ S₂, p.Prime := by
    intro p hp
    exact (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
  have hS₃prime : ∀ p ∈ S₃, p.Prime := by
    intro p hp
    exact (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
  have hS₂three : ∀ p ∈ S₂, 3 ≤ p := by
    intro p hp
    exact hthree₂ p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
  have hS₃three : ∀ p ∈ S₃, 3 ≤ p := by
    intro p hp
    exact hthree₃ p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
  have hV₂ : V₂ ≤ primeQuadraticConstant := by
    dsimp only [V₂]
    exact sum_norm_prime_cpow_sq_le_primeQuadraticConstant
      S₂ hS₂prime hsigma
  have hV₃ : V₃ ≤ primeQuadraticConstant := by
    dsimp only [V₃]
    exact sum_norm_prime_cpow_sq_le_primeQuadraticConstant
      S₃ hS₃prime hsigma
  have hV₂nonneg : 0 ≤ V₂ := by dsimp only [V₂]; positivity
  have hV₃nonneg : 0 ≤ V₃ := by dsimp only [V₃]; positivity
  have halt := twoBlock_alternatingLow_LSeries_eq_EulerFactors_of_disjoint
    hmul hbound Q₂ Q₃ y hdisj hsre
  have halt' :
      LSeries (gsA9Low f y) s - LSeries (gsA9LowDeletion f Q₂ y) s -
          LSeries (gsA9LowDeletion f Q₃ y) s +
          LSeries (gsA9LowDeletion f (fun p ↦ Q₂ p ∨ Q₃ p) y) s =
        P₀ * (P₂ - 1) * (P₃ - 1) := by
    simpa only [S₀, S₂, S₃, P₀, P₂, P₃] using halt
  have hblock₂ : ‖P₂ - 1‖ * Real.exp (-R₂ / 2) ≤
      Real.exp (z₂.re / 2 + 8 * V₂) := by
    dsimp only [P₂, R₂, z₂, V₂]
    exact norm_prod_gsA9LocalEulerFactor_sub_one_mul_exp_neg_radius_le
      hmul hbound S₂ hS₂prime hS₂three hsreWeak
  have hblock₃ : ‖P₃ - 1‖ * Real.exp (-R₃ / 2) ≤
      Real.exp (z₃.re / 2 + 8 * V₃) := by
    dsimp only [P₃, R₃, z₃, V₃]
    exact norm_prod_gsA9LocalEulerFactor_sub_one_mul_exp_neg_radius_le
      hmul hbound S₃ hS₃prime hS₃three hsreWeak
  have hlower₂ : Real.exp (z₂.re - 4 * V₂) ≤ ‖P₂‖ := by
    dsimp only [P₂, z₂, V₂]
    exact exp_linear_sub_square_le_norm_prod_gsA9LocalEulerFactor
      hmul hbound S₂ hS₂prime hS₂three hsreWeak
  have hlower₃ : Real.exp (z₃.re - 4 * V₃) ≤ ‖P₃‖ := by
    dsimp only [P₃, z₃, V₃]
    exact exp_linear_sub_square_le_norm_prod_gsA9LocalEulerFactor
      hmul hbound S₃ hS₃prime hS₃three hsreWeak
  have hsq₂ : ‖P₂ - 1‖ ^ 2 ≤
      Real.exp (R₂ + 20 * V₂) * ‖P₂‖ :=
    sq_le_exp_radius_add_twenty_mul_square_mul_of_block_bounds
      (norm_nonneg _) hblock₂ hlower₂
  have hsq₃ : ‖P₃ - 1‖ ^ 2 ≤
      Real.exp (R₃ + 20 * V₃) * ‖P₃‖ :=
    sq_le_exp_radius_add_twenty_mul_square_mul_of_block_bounds
      (norm_nonneg _) hblock₃ hlower₃
  have hnormShift (p : ℕ) (hp : p.Prime) :
      ‖(p : ℂ) ^ (-s)‖ = ‖(p : ℂ) ^ (-sr)‖ := by
    rw [show s = (sigma : ℂ) + Complex.I * (t : ℂ) by rfl,
      Erdos67.HalaszCpowDeficit.norm_nat_cpow_neg_sigma_add_I_mul hp.pos,
      show sr = (sigma : ℂ) by rfl,
      Erdos67.EulerQuantitative.norm_prime_cpow_neg_real sigma ⟨p, hp⟩]
  have hlinearReal (p : ℕ) (hp : 0 < p) :
      ((one p) * (p : ℂ) ^ (-sr)).re = ‖(p : ℂ) ^ (-s)‖ := by
    dsimp only [one]
    rw [one_mul, show sr = (sigma : ℂ) by rfl]
    have hr : ((p : ℂ) ^ (-(sigma : ℂ))) =
        (((p : ℝ) ^ (-sigma) : ℝ) : ℂ) := by
      rw [show -(sigma : ℂ) = ((-sigma : ℝ) : ℂ) by push_cast; ring]
      exact (Complex.ofReal_cpow (Nat.cast_nonneg p) (-sigma)).symm
    rw [hr, Complex.ofReal_re]
    exact (Erdos67.HalaszCpowDeficit.norm_nat_cpow_neg_sigma_add_I_mul
      hp sigma t).symm
  have hz₂p : (∑ p ∈ S₂, one p * (p : ℂ) ^ (-sr)).re = R₂ := by
    simp only [Complex.re_sum, R₂]
    apply Finset.sum_congr rfl
    intro p hp
    exact hlinearReal p (hS₂prime p hp).pos
  have hz₃p : (∑ p ∈ S₃, one p * (p : ℂ) ^ (-sr)).re = R₃ := by
    simp only [Complex.re_sum, R₃]
    apply Finset.sum_congr rfl
    intro p hp
    exact hlinearReal p (hS₃prime p hp).pos
  have hV₂p : (∑ p ∈ S₂, ‖(p : ℂ) ^ (-sr)‖ ^ 2) = V₂ := by
    dsimp only [V₂]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hnormShift p (hS₂prime p hp)]
  have hV₃p : (∑ p ∈ S₃, ‖(p : ℂ) ^ (-sr)‖ ^ 2) = V₃ := by
    dsimp only [V₃]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hnormShift p (hS₃prime p hp)]
  have honeMul : IsMultiplicativeOnPositiveNat one := by
    constructor <;> simp [one]
  have honeBound : ∀ n, 0 < n → ‖one n‖ ≤ 1 := by simp [one]
  have hlower₂p : Real.exp (R₂ - 4 * V₂) ≤ ‖P₂p‖ := by
    have h := exp_linear_sub_square_le_norm_prod_gsA9LocalEulerFactor
      honeMul honeBound S₂ hS₂prime hS₂three hsrreWeak
    simpa only [P₂p, hz₂p, hV₂p] using h
  have hlower₃p : Real.exp (R₃ - 4 * V₃) ≤ ‖P₃p‖ := by
    have h := exp_linear_sub_square_le_norm_prod_gsA9LocalEulerFactor
      honeMul honeBound S₃ hS₃prime hS₃three hsrreWeak
    simpa only [P₃p, hz₃p, hV₃p] using h
  let Pout : ℕ → Prop := fun p ↦ p ≤ y ∧ ¬ Q₂ p ∧ ¬ Q₃ p
  let : DecidablePred Pout := Classical.decPred Pout
  have hPout : ∀ p, Pout p → p ≤ y := fun p hp ↦ hp.1
  have hfilterOut : (primesUpTo y).filter Pout = S₀ := by
    ext p
    simp only [Pout, S₀, Finset.mem_filter, mem_primesUpTo]
    tauto
  have hP₀major : ‖P₀‖ ≤ ‖P₀p‖ := by
    have hmajor := norm_LSeries_primeBandCoefficient_le_positive
      hbound Pout hsigma (t := t)
    rw [LSeries_primeBandCoefficient_eq_finiteEulerProduct
          hmul hbound Pout y hPout hsre,
      LSeries_primeBandCoefficient_eq_finiteEulerProduct
          honeMul honeBound Pout y hPout hsrre] at hmajor
    simpa only [hfilterOut, P₀, P₀p, s, sr] using hmajor
  have hHmajor : ‖H‖ ≤ ‖Hp‖ := by
    have hmajor := norm_LSeries_primeBandCoefficient_le_positive
      hbound (fun p ↦ ¬ p ≤ y) hsigma (t := t)
    simpa only [gsA9High, H, Hp, s, sr, one] using hmajor
  have hLowProd : P₀ * P₂ * P₃ = LSeries (gsA9Low f y) s := by
    rw [LSeries_gsA9Low_eq_finiteEulerProduct hmul hbound y hsre]
    exact prod_neither_mul_prod_left_mul_prod_right_eq
      (primesUpTo y) Q₂ Q₃ hdisj (gsA9LocalEulerFactor f s)
  have hFullProd : (P₀ * P₂ * P₃) * H = LSeries f s := by
    rw [hLowProd]
    exact LSeries_gsA9Low_mul_gsA9High hmul hbound y hsre
  have hLowPosProd : P₀p * P₂p * P₃p =
      LSeries (gsA9Low one y) sr := by
    rw [LSeries_gsA9Low_eq_finiteEulerProduct honeMul honeBound y hsrre]
    exact prod_neither_mul_prod_left_mul_prod_right_eq
      (primesUpTo y) Q₂ Q₃ hdisj (gsA9LocalEulerFactor one sr)
  have hZetaProd : (P₀p * P₂p * P₃p) * Hp =
      riemannZeta (sigma : ℂ) := by
    rw [hLowPosProd]
    calc
      LSeries (gsA9Low one y) sr * Hp = LSeries one sr :=
        LSeries_gsA9Low_mul_gsA9High honeMul honeBound y hsrre
      _ = riemannZeta (sigma : ℂ) := by
        rw [show one = (1 : ℕ → ℂ) by funext n; simp [one]]
        simpa only [sr] using LSeries_one_eq_riemannZeta hsrre
  have hZetaPos : 0 < (riemannZeta (sigma : ℂ)).re := by
    exact (Complex.lt_def.mp (riemannZeta_pos_of_one_lt hsigma)).1
  have hZetaNorm : ‖riemannZeta (sigma : ℂ)‖ =
      (riemannZeta (sigma : ℂ)).re := by
    have hz := riemannZeta_pos_of_one_lt hsigma
    have hp := Complex.pos_iff.mp hz
    have heq : riemannZeta (sigma : ℂ) =
        (((riemannZeta (sigma : ℂ)).re : ℝ) : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using hp.2.symm
    calc
      ‖riemannZeta (sigma : ℂ)‖ =
          ‖(((riemannZeta (sigma : ℂ)).re : ℝ) : ℂ)‖ := congrArg norm heq
      _ = (riemannZeta (sigma : ℂ)).re := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZetaPos]
  have hExpR : Real.exp (R₂ + R₃) ≤
      Real.exp (4 * (V₂ + V₃)) * (‖P₂p‖ * ‖P₃p‖) := by
    calc
      Real.exp (R₂ + R₃) = Real.exp (4 * (V₂ + V₃)) *
          (Real.exp (R₂ - 4 * V₂) * Real.exp (R₃ - 4 * V₃)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (4 * (V₂ + V₃)) * (‖P₂p‖ * ‖P₃p‖) := by
        gcongr
  have hOther : ‖P₀‖ * ‖H‖ * Real.exp (R₂ + R₃) ≤
      Real.exp (4 * (V₂ + V₃)) *
        (riemannZeta (sigma : ℂ)).re := by
    calc
      ‖P₀‖ * ‖H‖ * Real.exp (R₂ + R₃) ≤
          ‖P₀p‖ * ‖Hp‖ *
            (Real.exp (4 * (V₂ + V₃)) * (‖P₂p‖ * ‖P₃p‖)) := by
        gcongr
      _ = Real.exp (4 * (V₂ + V₃)) *
          ‖(P₀p * P₂p * P₃p) * Hp‖ := by
        simp only [norm_mul]
        ring
      _ = Real.exp (4 * (V₂ + V₃)) *
          (riemannZeta (sigma : ℂ)).re := by rw [hZetaProd, hZetaNorm]
  have hAltNorm :
      ‖(LSeries (gsA9Low f y) s - LSeries (gsA9LowDeletion f Q₂ y) s -
          LSeries (gsA9LowDeletion f Q₃ y) s +
          LSeries (gsA9LowDeletion f (fun p ↦ Q₂ p ∨ Q₃ p) y) s) * H‖ =
        ‖P₀‖ * ‖P₂ - 1‖ * ‖P₃ - 1‖ * ‖H‖ := by
    rw [halt']
    simp only [norm_mul]
  have hFullNorm : ‖P₀‖ * ‖P₂‖ * ‖P₃‖ * ‖H‖ =
      ‖LSeries f s‖ := by
    rw [← norm_mul, ← norm_mul, ← norm_mul, hFullProd]
  have hSq :
      ‖(LSeries (gsA9Low f y) s - LSeries (gsA9LowDeletion f Q₂ y) s -
          LSeries (gsA9LowDeletion f Q₃ y) s +
          LSeries (gsA9LowDeletion f (fun p ↦ Q₂ p ∨ Q₃ p) y) s) * H‖ ^ 2 ≤
        Real.exp (24 * (V₂ + V₃)) * ‖LSeries f s‖ *
          (riemannZeta (sigma : ℂ)).re := by
    rw [hAltNorm]
    calc
      (‖P₀‖ * ‖P₂ - 1‖ * ‖P₃ - 1‖ * ‖H‖) ^ 2 =
          ‖P₀‖ ^ 2 * ‖P₂ - 1‖ ^ 2 * ‖P₃ - 1‖ ^ 2 * ‖H‖ ^ 2 := by ring
      _ ≤ ‖P₀‖ ^ 2 *
          (Real.exp (R₂ + 20 * V₂) * ‖P₂‖) *
          (Real.exp (R₃ + 20 * V₃) * ‖P₃‖) * ‖H‖ ^ 2 := by
        gcongr
      _ = Real.exp (20 * (V₂ + V₃)) *
          (‖P₀‖ * ‖P₂‖ * ‖P₃‖ * ‖H‖) *
          (‖P₀‖ * ‖H‖ * Real.exp (R₂ + R₃)) := by
        have he : Real.exp (R₂ + 20 * V₂) * Real.exp (R₃ + 20 * V₃) =
            Real.exp (20 * (V₂ + V₃)) * Real.exp (R₂ + R₃) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [show
          ‖P₀‖ ^ 2 * (Real.exp (R₂ + 20 * V₂) * ‖P₂‖) *
                (Real.exp (R₃ + 20 * V₃) * ‖P₃‖) * ‖H‖ ^ 2 =
              (Real.exp (R₂ + 20 * V₂) * Real.exp (R₃ + 20 * V₃)) *
                (‖P₀‖ * ‖P₂‖ * ‖P₃‖ * ‖H‖) *
                (‖P₀‖ * ‖H‖) by ring, he]
        ring
      _ ≤ Real.exp (20 * (V₂ + V₃)) * ‖LSeries f s‖ *
          (Real.exp (4 * (V₂ + V₃)) *
            (riemannZeta (sigma : ℂ)).re) := by
        rw [hFullNorm]
        gcongr
      _ = Real.exp (24 * (V₂ + V₃)) * ‖LSeries f s‖ *
          (riemannZeta (sigma : ℂ)).re := by
        have he : Real.exp (20 * (V₂ + V₃)) *
            Real.exp (4 * (V₂ + V₃)) =
              Real.exp (24 * (V₂ + V₃)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [show Real.exp (20 * (V₂ + V₃)) * ‖LSeries f s‖ *
              (Real.exp (4 * (V₂ + V₃)) *
                (riemannZeta (sigma : ℂ)).re) =
            (Real.exp (20 * (V₂ + V₃)) * Real.exp (4 * (V₂ + V₃))) *
              ‖LSeries f s‖ * (riemannZeta (sigma : ℂ)).re by ring, he]
  have hVsum : V₂ + V₃ ≤ 2 * primeQuadraticConstant := by linarith
  have hExpC : Real.exp (24 * (V₂ + V₃)) ≤
      Real.exp (48 * primeQuadraticConstant) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hSqC :
      ‖(LSeries (gsA9Low f y) s - LSeries (gsA9LowDeletion f Q₂ y) s -
          LSeries (gsA9LowDeletion f Q₃ y) s +
          LSeries (gsA9LowDeletion f (fun p ↦ Q₂ p ∨ Q₃ p) y) s) * H‖ ^ 2 ≤
        Real.exp (48 * primeQuadraticConstant) * ‖LSeries f s‖ *
          (riemannZeta (sigma : ℂ)).re := hSq.trans (by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hExpC (norm_nonneg _)) hZetaPos.le)
  have hleft : 0 ≤
      ‖(LSeries (gsA9Low f y) s - LSeries (gsA9LowDeletion f Q₂ y) s -
          LSeries (gsA9LowDeletion f Q₃ y) s +
          LSeries (gsA9LowDeletion f (fun p ↦ Q₂ p ∨ Q₃ p) y) s) * H‖ :=
    norm_nonneg _
  calc
    ‖(LSeries (gsA9Low f y) s - LSeries (gsA9LowDeletion f Q₂ y) s -
          LSeries (gsA9LowDeletion f Q₃ y) s +
          LSeries (gsA9LowDeletion f (fun p ↦ Q₂ p ∨ Q₃ p) y) s) * H‖ =
        Real.sqrt (‖(LSeries (gsA9Low f y) s - LSeries (gsA9LowDeletion f Q₂ y) s -
          LSeries (gsA9LowDeletion f Q₃ y) s +
          LSeries (gsA9LowDeletion f (fun p ↦ Q₂ p ∨ Q₃ p) y) s) * H‖ ^ 2) := by
      rw [Real.sqrt_sq hleft]
    _ ≤ Real.sqrt (Real.exp (48 * primeQuadraticConstant) *
          ‖LSeries f s‖ * (riemannZeta (sigma : ℂ)).re) :=
      Real.sqrt_le_sqrt hSqC
    _ = Real.exp (24 * primeQuadraticConstant) *
          Real.sqrt ‖LSeries f s‖ *
          Real.sqrt (riemannZeta (sigma : ℂ)).re := by
      rw [show Real.exp (48 * primeQuadraticConstant) * ‖LSeries f s‖ *
            (riemannZeta (sigma : ℂ)).re =
          Real.exp (48 * primeQuadraticConstant) *
            (‖LSeries f s‖ * (riemannZeta (sigma : ℂ)).re) by ring,
        Real.sqrt_mul (Real.exp_pos _).le,
        Real.sqrt_mul (norm_nonneg _), ← Real.exp_half,
        show 48 * primeQuadraticConstant / 2 =
          24 * primeQuadraticConstant by ring]
      ring

end

end Erdos67.MRHalaszBands
