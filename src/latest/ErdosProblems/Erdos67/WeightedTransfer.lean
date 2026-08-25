import ErdosProblems.Erdos67.BCC
import ErdosProblems.Erdos67.EulerResidue
import ErdosProblems.Erdos67.Pretentious
import ErdosProblems.Erdos67.Stochastic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The weighted transfer in the Borwein--Choi--Coons argument

This file isolates the finite, quantitative part of the transfer used in
Section 4 of Tao's proof of the Erdős discrepancy theorem.  In particular,
none of the statements below hides an asymptotic estimate.

* Prime-coordinate functions are split exactly into a modified character, an
  Archimedean factor, and a correction factor.
* The Archimedean factor is removed on a short interval by an explicit Taylor
  bound.  A specialization records the customary choice `X = Y ^ D`.
* A uniform stochastic second-moment bound is transferred to any finite
  nonnegative weighted average.
* Good residue classes are represented by a finite set, and a union
  bound counts the exceptional classes.
* Tao's shifted residue convolution is kept intact until the uniform
  `EulerResidue` estimate replaces every residue series by its common main
  term, giving a scale-free prefix-energy bound.

No analytic Euler-product estimate is postulated as a declaration.  The
The corrected final medium-energy theorem consumes the proved
principal/nonprincipal decomposition from `EulerResidue` and has a bound
independent of `q`, `k`, and `H`.
-/

open scoped BigOperators ComplexConjugate
open Finset MeasureTheory

namespace Erdos67

noncomputable section

/-! ## Exact factorization in prime coordinates -/

/-- Pointwise multiplication of two prime assignments. -/
def assignmentMul (z w : PrimeAssignment) : PrimeAssignment :=
  fun p ↦ z p * w p

/-- Pointwise inverse of a prime assignment. -/
def assignmentInv (z : PrimeAssignment) : PrimeAssignment :=
  fun p ↦ (z p)⁻¹

@[simp] theorem assignmentMul_apply (z w : PrimeAssignment) (p : PrimeNat) :
    assignmentMul z w p = z p * w p := rfl

@[simp] theorem assignmentInv_apply (z : PrimeAssignment) (p : PrimeNat) :
    assignmentInv z p = (z p)⁻¹ := rfl

@[simp] theorem assignmentMul_one (z : PrimeAssignment) :
    assignmentMul z 1 = z := by
  funext p
  simp [assignmentMul]

@[simp] theorem assignmentMul_inv (z : PrimeAssignment) :
    assignmentMul z (assignmentInv z) = 1 := by
  funext p
  simp [assignmentMul, assignmentInv]

/-- Prime extension commutes with pointwise multiplication of assignments. -/
theorem primeExtension_assignmentMul (z w : PrimeAssignment) (n : ℕ) :
    primeExtension (assignmentMul z w) n =
      primeExtension z n * primeExtension w n := by
  classical
  simp only [primeExtension, assignmentMul, primeValue]
  rw [← Finsupp.prod_mul]
  apply Finsupp.prod_congr
  intro p e
  split_ifs with hprime
  · rw [mul_pow]
  · simp

/-- The modified-character assignment.  On the finite exceptional set it is
chosen so that the correction factor below is exactly one; away from that set
it agrees with the supplied character model. -/
def modifiedAssignment (base model arch : PrimeAssignment)
    (exceptional : Finset PrimeNat) : PrimeAssignment :=
  fun p ↦ if p ∈ exceptional then base p * (arch p)⁻¹ else model p

/-- The completely multiplicative correction to `modifiedAssignment * arch`. -/
def correctionAssignment (base model arch : PrimeAssignment)
    (exceptional : Finset PrimeNat) : PrimeAssignment :=
  fun p ↦ base p * (modifiedAssignment base model arch exceptional p * arch p)⁻¹

@[simp] theorem modifiedAssignment_of_mem
    (base model arch : PrimeAssignment) (exceptional : Finset PrimeNat)
    {p : PrimeNat} (hp : p ∈ exceptional) :
    modifiedAssignment base model arch exceptional p = base p * (arch p)⁻¹ := by
  simp [modifiedAssignment, hp]

@[simp] theorem modifiedAssignment_of_not_mem
    (base model arch : PrimeAssignment) (exceptional : Finset PrimeNat)
    {p : PrimeNat} (hp : p ∉ exceptional) :
    modifiedAssignment base model arch exceptional p = model p := by
  simp [modifiedAssignment, hp]

@[simp] theorem correctionAssignment_of_mem
    (base model arch : PrimeAssignment) (exceptional : Finset PrimeNat)
    {p : PrimeNat} (hp : p ∈ exceptional) :
    correctionAssignment base model arch exceptional p = 1 := by
  simp [correctionAssignment, modifiedAssignment, hp]

/-- Exact pointwise factorization at every prime. -/
theorem modified_mul_arch_mul_correction
    (base model arch : PrimeAssignment) (exceptional : Finset PrimeNat) :
    assignmentMul (assignmentMul (modifiedAssignment base model arch exceptional) arch)
        (correctionAssignment base model arch exceptional) = base := by
  funext p
  simp [assignmentMul, correctionAssignment, mul_assoc, mul_left_comm, mul_comm]

/-- Exact completely multiplicative factorization on every natural number. -/
theorem primeExtension_modified_factorization
    (base model arch : PrimeAssignment) (exceptional : Finset PrimeNat) (n : ℕ) :
    primeExtension base n =
      primeExtension (modifiedAssignment base model arch exceptional) n *
        primeExtension arch n *
          primeExtension (correctionAssignment base model arch exceptional) n := by
  have h := congrArg (fun z : PrimeAssignment ↦ primeExtension z n)
    (modified_mul_arch_mul_correction base model arch exceptional)
  simp only [primeExtension_assignmentMul, mul_assoc] at h
  simpa only [mul_assoc] using h.symm

/-! ## Removing the Archimedean twist on a finite short interval -/

/-- The ratio `(n+h)^(it) / n^(it)`, written in exponential form.  This form
has no branch ambiguity because both arguments are positive reals. -/
def localArchimedeanRatio (t : ℝ) (n h : ℕ) : ℂ :=
  Complex.exp (Complex.I * (t * (Real.log (n + h : ℝ) - Real.log (n : ℝ))))

theorem localArchimedeanRatio_eq_twist_div (t : ℝ) {n h : ℕ} (hn : 0 < n) :
    localArchimedeanRatio t n h =
      archimedeanTwist t (n + h) / archimedeanTwist t n := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnhR : (0 : ℝ) < ((n + h : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_pos_left hn h
  rw [localArchimedeanRatio, archimedeanTwist, archimedeanTwist,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hnhR.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hnR.ne'), div_eq_mul_inv,
    ← Complex.exp_neg, ← Complex.exp_add]
  rw [show ((n + h : ℕ) : ℂ) = (((n + h : ℕ) : ℝ) : ℂ) by norm_num,
    show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_log hnhR.le, ← Complex.ofReal_log hnR.le]
  congr 1
  push_cast
  ring

/-- The logarithmic increment on a positive short interval is bounded by its
relative length. -/
theorem log_nat_add_sub_log_nat_le_div {n h : ℕ} (hn : 0 < n) :
    Real.log (n + h : ℝ) - Real.log (n : ℝ) ≤ (h : ℝ) / n := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnhR : (0 : ℝ) < (n : ℝ) + (h : ℝ) := by positivity
  calc
    Real.log ((n : ℝ) + h) - Real.log (n : ℝ) =
        Real.log (((n : ℝ) + h) / n) := by
      rw [Real.log_div hnhR.ne' hnR.ne']
    _ ≤ (((n : ℝ) + h) / n) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hnhR hnR)
    _ = (h : ℝ) / n := by
      field_simp
      ring

theorem log_nat_sub_nonneg {n h : ℕ} (hn : 0 < n) :
    0 ≤ Real.log (n + h : ℝ) - Real.log (n : ℝ) := by
  apply sub_nonneg.mpr
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnhR : (0 : ℝ) < (n : ℝ) + (h : ℝ) := by positivity
  exact Real.strictMonoOn_log.monotoneOn
    (show (n : ℝ) ∈ Set.Ioi 0 from hnR)
    (show (n : ℝ) + (h : ℝ) ∈ Set.Ioi 0 from hnhR)
    (by exact_mod_cast Nat.le_add_right n h)

/-- Quantitative Taylor bound for an Archimedean twist on a finite short
interval.  The constant is one. -/
theorem norm_localArchimedeanRatio_sub_one_le (t : ℝ) {n h : ℕ} (hn : 0 < n) :
    ‖localArchimedeanRatio t n h - 1‖ ≤ |t| * (h : ℝ) / n := by
  let δ : ℝ := Real.log (n + h : ℝ) - Real.log (n : ℝ)
  have hδ0 : 0 ≤ δ := log_nat_sub_nonneg hn
  have hδ : δ ≤ (h : ℝ) / n := log_nat_add_sub_log_nat_le_div hn
  calc
    ‖localArchimedeanRatio t n h - 1‖ ≤ ‖t * δ‖ := by
      simpa only [localArchimedeanRatio, δ, Complex.ofReal_mul, Complex.ofReal_sub] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * δ))
    _ = |t| * δ := by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hδ0]
    _ ≤ |t| * ((h : ℝ) / n) :=
      mul_le_mul_of_nonneg_left hδ (abs_nonneg t)
    _ = |t| * (h : ℝ) / n := by ring

/-- The same Taylor bound at the scale `X = Y ^ D`. -/
theorem norm_localArchimedeanRatio_sub_one_le_pow_scale
    (t : ℝ) {Y D n h : ℕ} (hY : 0 < Y) (hn : Y ^ D ≤ n) (hh : h ≤ Y) :
    ‖localArchimedeanRatio t n h - 1‖ ≤
      |t| * (Y : ℝ) / (Y : ℝ) ^ D := by
  have hnpos : 0 < n := lt_of_lt_of_le (pow_pos hY D) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hpowR : (0 : ℝ) < (Y : ℝ) ^ D := by positivity
  refine (norm_localArchimedeanRatio_sub_one_le t hnpos).trans ?_
  have hhR : (h : ℝ) ≤ Y := by exact_mod_cast hh
  have hnR' : (Y : ℝ) ^ D ≤ n := by exact_mod_cast hn
  have hdiv : (h : ℝ) / n ≤ (Y : ℝ) / (Y : ℝ) ^ D := by
    gcongr
  calc
    |t| * (h : ℝ) / n = |t| * ((h : ℝ) / n) := by ring
    _ ≤ |t| * ((Y : ℝ) / (Y : ℝ) ^ D) :=
      mul_le_mul_of_nonneg_left hdiv (abs_nonneg t)
    _ = |t| * (Y : ℝ) / (Y : ℝ) ^ D := by ring

/-- A convenient epsilon form of the power-scale Taylor estimate. -/
theorem norm_localArchimedeanRatio_sub_one_le_of_pow_scale
    (t ε : ℝ) {Y D n h : ℕ} (hY : 0 < Y) (hn : Y ^ D ≤ n) (hh : h ≤ Y)
    (hsmall : |t| * (Y : ℝ) ≤ ε * (Y : ℝ) ^ D) :
    ‖localArchimedeanRatio t n h - 1‖ ≤ ε := by
  have hpowR : (0 : ℝ) < (Y : ℝ) ^ D := by positivity
  refine (norm_localArchimedeanRatio_sub_one_le_pow_scale t hY hn hh).trans ?_
  exact (div_le_iff₀ hpowR).2 hsmall

/-! ## Uniform stochastic bounds and finite weighted averages -/

/-- A local additive increment of the random completely multiplicative
function.  Writing it as a difference of prefixes makes the transfer from a
uniform prefix bound completely transparent. -/
def circleLocalIncrement (z : PrimeAssignment) (n H : ℕ) : ℂ :=
  circlePartialSum z (n + H) - circlePartialSum z n

/-- Squared norm of a local increment. -/
def circleLocalIncrementEnergy (n H : ℕ) (z : PrimeAssignment) : ℝ :=
  ‖circleLocalIncrement z n H‖ ^ 2

theorem continuous_circleLocalIncrementEnergy (n H : ℕ) :
    Continuous (circleLocalIncrementEnergy n H) := by
  unfold circleLocalIncrementEnergy circleLocalIncrement
  exact ((continuous_circlePartialSum (n + H)).sub
    (continuous_circlePartialSum n)).norm.pow 2

theorem integrable_circleLocalIncrementEnergy
    (mu : ProbabilityMeasure PrimeAssignment) (n H : ℕ) :
    Integrable (circleLocalIncrementEnergy n H) (mu : Measure PrimeAssignment) :=
  (continuous_circleLocalIncrementEnergy n H).integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))

/-- Mean-square local increment under a law on prime assignments. -/
def meanSquareLocalIncrement
    (mu : ProbabilityMeasure PrimeAssignment) (n H : ℕ) : ℝ :=
  ∫ z, circleLocalIncrementEnergy n H z ∂(mu : Measure PrimeAssignment)

theorem norm_sub_sq_le_two_mul_add (x y : ℂ) :
    ‖x - y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have htri : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
  nlinarith [norm_nonneg (x - y), norm_nonneg x, norm_nonneg y,
    sq_nonneg (‖x‖ - ‖y‖)]

/-- A uniform stochastic prefix bound controls every local additive
increment, with the elementary factor four. -/
theorem meanSquareLocalIncrement_le_four_mul
    (mu : ProbabilityMeasure PrimeAssignment) (C : ℝ)
    (hbound : ∀ m : ℕ, meanSquarePartialSum mu m ≤ C) (n H : ℕ) :
    meanSquareLocalIncrement mu n H ≤ 4 * C := by
  have hpoint (z : PrimeAssignment) :
      circleLocalIncrementEnergy n H z ≤
        2 * (circlePartialSumEnergy (n + H) z + circlePartialSumEnergy n z) := by
    exact norm_sub_sq_le_two_mul_add _ _
  have hlocal : Integrable (circleLocalIncrementEnergy n H)
      (mu : Measure PrimeAssignment) := integrable_circleLocalIncrementEnergy mu n H
  have hright : Integrable
      (fun z ↦ 2 * (circlePartialSumEnergy (n + H) z + circlePartialSumEnergy n z))
      (mu : Measure PrimeAssignment) := by
    apply Integrable.const_mul
    apply Integrable.add
    · exact (continuous_circlePartialSumEnergy (n + H)).integrable_of_hasCompactSupport
        (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
    · exact (continuous_circlePartialSumEnergy n).integrable_of_hasCompactSupport
        (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  calc
    meanSquareLocalIncrement mu n H ≤
        ∫ z, 2 * (circlePartialSumEnergy (n + H) z + circlePartialSumEnergy n z)
          ∂(mu : Measure PrimeAssignment) :=
      integral_mono hlocal hright hpoint
    _ = 2 * ∫ z, circlePartialSumEnergy (n + H) z + circlePartialSumEnergy n z
          ∂(mu : Measure PrimeAssignment) := by rw [integral_const_mul]
    _ = 2 * (meanSquarePartialSum mu (n + H) + meanSquarePartialSum mu n) := by
      rw [integral_add]
      · rfl
      · exact (continuous_circlePartialSumEnergy (n + H)).integrable_of_hasCompactSupport
          (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
      · exact (continuous_circlePartialSumEnergy n).integrable_of_hasCompactSupport
          (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
    _ ≤ 4 * C := by linarith [hbound (n + H), hbound n]

/-- A finite nonnegative weighted average of local mean-square increments. -/
def weightedLocalMeanSquare
    (mu : ProbabilityMeasure PrimeAssignment) (centers : Finset ℕ)
    (weight : ℕ → ℝ) (H : ℕ) : ℝ :=
  ∑ n ∈ centers, weight n * meanSquareLocalIncrement mu n H

/-- The uniform stochastic prefix bound transfers to any finite nonnegative
weighted average of local increments. -/
theorem weightedLocalMeanSquare_le
    (mu : ProbabilityMeasure PrimeAssignment) (centers : Finset ℕ)
    (weight : ℕ → ℝ) (H : ℕ) (C : ℝ)
    (hweight : ∀ n ∈ centers, 0 ≤ weight n)
    (hbound : ∀ m : ℕ, meanSquarePartialSum mu m ≤ C) :
    weightedLocalMeanSquare mu centers weight H ≤
      4 * C * ∑ n ∈ centers, weight n := by
  unfold weightedLocalMeanSquare
  calc
    (∑ n ∈ centers, weight n * meanSquareLocalIncrement mu n H) ≤
        ∑ n ∈ centers, weight n * (4 * C) := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left
        (meanSquareLocalIncrement_le_four_mul mu C hbound n H) (hweight n hn)
    _ = 4 * C * ∑ n ∈ centers, weight n := by
      rw [← Finset.sum_mul]
      ring

/-! ## Good residue classes and their exceptional-set count -/

/-- A fiber of the reduction map `ZMod N → ZMod d`. -/
def castResidueFiber {N d : ℕ} [NeZero N] [NeZero d]
    (hd : d ∣ N) (b : ZMod d) : Finset (ZMod N) :=
  Finset.univ.filter fun a ↦ ZMod.castHom hd (ZMod d) a = b

/-- Every fiber of reduction modulo a divisor has the expected cardinality. -/
theorem card_castResidueFiber {N d : ℕ} [NeZero N] [NeZero d]
    (hd : d ∣ N) (b : ZMod d) :
    (castResidueFiber hd b).card = N / d := by
  classical
  let f : ZMod N →+ ZMod d := (ZMod.castHom hd (ZMod d)).toAddMonoidHom
  have hsurj : Function.Surjective f := ZMod.castHom_surjective hd
  have hconst (c : ZMod d) :
      (castResidueFiber hd c).card = (castResidueFiber hd 0).card := by
    exact AddMonoidHom.card_fiber_eq_of_mem_range f (hsurj c) (hsurj 0)
  have htotal :
      N = ∑ c : ZMod d, (castResidueFiber hd c).card := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (ZMod N)))
      (t := (Finset.univ : Finset (ZMod d)))
      (f := f) (fun _ _ ↦ Finset.mem_univ _)
    change N = ∑ c : ZMod d,
      (Finset.univ.filter fun a : ZMod N ↦ f a = c).card
    simpa only [Finset.card_univ, ZMod.card] using h
  have htotal0 : N = d * (castResidueFiber hd 0).card := by
    calc
      N = ∑ c : ZMod d, (castResidueFiber hd c).card := htotal
      _ = ∑ _c : ZMod d, (castResidueFiber hd 0).card := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hconst c
      _ = d * (castResidueFiber hd 0).card := by simp
  calc
    (castResidueFiber hd b).card = (castResidueFiber hd 0).card := hconst b
    _ = N / d := by
      symm
      apply (Nat.div_eq_iff_eq_mul_left (NeZero.pos d) hd).2
      simpa only [mul_comm] using htotal0

/-- Residues modulo `q^k` for which the translate by `m` is divisible by
`p^k`.  The definition is empty when `p` is not a prime factor of `q`; this
makes later finite unions nondependent. -/
def cyclicBadAt (q k p m : ℕ) [NeZero q] : Finset (ZMod (q ^ k)) :=
  if hp : p ∈ q.primeFactors then
    Finset.univ.filter fun a ↦
      ZMod.castHom (pow_dvd_pow_of_dvd (Nat.dvd_of_mem_primeFactors hp) k)
        (ZMod (p ^ k)) (a + (m : ZMod (q ^ k))) = 0
  else ∅

/-- A bad residue has one forbidden prime-power divisor in one of its first
`2H` positive translates. -/
def cyclicBadResidues (q k H : ℕ) [NeZero q] : Finset (ZMod (q ^ k)) :=
  q.primeFactors.biUnion fun p ↦
    (Finset.Icc 1 (2 * H)).biUnion fun m ↦ cyclicBadAt q k p m

/-- The complementary set of good cyclic residues. -/
def cyclicGoodResidues (q k H : ℕ) [NeZero q] : Finset (ZMod (q ^ k)) :=
  Finset.univ \ cyclicBadResidues q k H

/-- A single forbidden translate occupies exactly `q^k / p^k` residue
classes. -/
theorem card_cyclicBadAt (q k p m : ℕ) [NeZero q]
    (hp : p ∈ q.primeFactors) :
    (cyclicBadAt q k p m).card = q ^ k / p ^ k := by
  classical
  have hpPrime : p.Prime := (Nat.mem_primeFactors.mp hp).1
  let hpNe : NeZero (p ^ k) := ⟨pow_ne_zero k hpPrime.ne_zero⟩
  let hd : p ^ k ∣ q ^ k :=
    pow_dvd_pow_of_dvd (Nat.dvd_of_mem_primeFactors hp) k
  have heq : cyclicBadAt q k p m =
      @castResidueFiber (q ^ k) (p ^ k) inferInstance hpNe hd
        (-((m : ℕ) : ZMod (p ^ k))) := by
    ext a
    simp only [cyclicBadAt, hp, dite_true, castResidueFiber, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [map_add, map_natCast]
    exact add_eq_zero_iff_eq_neg
  rw [heq, @card_castResidueFiber (q ^ k) (p ^ k) inferInstance hpNe]

/-- Union bound for all bad residue classes, before simplifying the number
of shifts. -/
theorem card_cyclicBadResidues_le_sum (q k H : ℕ) [NeZero q] :
    (cyclicBadResidues q k H).card ≤
      ∑ p ∈ q.primeFactors, ∑ _m ∈ Finset.Icc 1 (2 * H), q ^ k / p ^ k := by
  classical
  unfold cyclicBadResidues
  calc
    (q.primeFactors.biUnion fun p ↦
        (Finset.Icc 1 (2 * H)).biUnion fun m ↦ cyclicBadAt q k p m).card ≤
        ∑ p ∈ q.primeFactors,
          ((Finset.Icc 1 (2 * H)).biUnion fun m ↦ cyclicBadAt q k p m).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ p ∈ q.primeFactors,
        ∑ _m ∈ Finset.Icc 1 (2 * H), q ^ k / p ^ k := by
      apply Finset.sum_le_sum
      intro p hp
      refine Finset.card_biUnion_le.trans_eq ?_
      apply Finset.sum_congr rfl
      intro m hm
      exact card_cyclicBadAt q k p m hp

/-- The standard exceptional-set estimate
`#bad ≤ 2H * ∑_{p|q} q^k/p^k`. -/
theorem card_cyclicBadResidues_le (q k H : ℕ) [NeZero q] :
    (cyclicBadResidues q k H).card ≤
      (2 * H) * ∑ p ∈ q.primeFactors, q ^ k / p ^ k := by
  have hcard : (Finset.Icc 1 (2 * H)).card = 2 * H := by
    rw [Nat.card_Icc]
    omega
  calc
    (cyclicBadResidues q k H).card ≤
        ∑ p ∈ q.primeFactors,
          ∑ _m ∈ Finset.Icc 1 (2 * H), q ^ k / p ^ k :=
      card_cyclicBadResidues_le_sum q k H
    _ = ∑ p ∈ q.primeFactors, (2 * H) * (q ^ k / p ^ k) := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [hcard]
    _ = (2 * H) * ∑ p ∈ q.primeFactors, q ^ k / p ^ k := by
      rw [Finset.mul_sum]

/-- Uniform `2^{-k}` version of the exceptional-residue bound.  Every prime
factor of `q` is at least two, so each forbidden fiber has size at most
`q^k / 2^k`. -/
theorem card_cyclicBadResidues_le_twoPow (q k H : ℕ) [NeZero q] :
    (cyclicBadResidues q k H).card ≤
      (2 * H) * q.primeFactors.card * (q ^ k / 2 ^ k) := by
  calc
    (cyclicBadResidues q k H).card ≤
        (2 * H) * ∑ p ∈ q.primeFactors, q ^ k / p ^ k :=
      card_cyclicBadResidues_le q k H
    _ ≤ (2 * H) *
        ∑ _p ∈ q.primeFactors, q ^ k / 2 ^ k := by
      gcongr with p hp
      have hpPrime : p.Prime := (Nat.mem_primeFactors.mp hp).1
      exact hpPrime.two_le
    _ = (2 * H) * q.primeFactors.card * (q ^ k / 2 ^ k) := by
      simp
      ring

/-- Lower bound for the number of good residues obtained from the preceding
explicit union bound. -/
theorem sub_badBound_le_card_cyclicGoodResidues (q k H : ℕ) [NeZero q] :
    q ^ k - (2 * H) * ∑ p ∈ q.primeFactors, q ^ k / p ^ k ≤
      (cyclicGoodResidues q k H).card := by
  have hbad := card_cyclicBadResidues_le q k H
  unfold cyclicGoodResidues
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simpa only [Finset.card_univ, ZMod.card] using Nat.sub_le_sub_left hbad (q ^ k)

/-- The complete finite BCC consumer with the cyclic exceptional set restored.
The last term displays the loss `q^k / 2^k` explicitly. -/
theorem qpower_card_lower_le_cyclicGood_prefix_energy
    {q k H : ℕ} [NeZero q] (s : Finset ℕ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (d : ℕ → ℕ) (hq : 1 < q)
    (hd : ∀ i ∈ s, NeZero (d i))
    (hdH : ∀ i ∈ s, 2 * d i ≤ H)
    (hN : ∀ i ∈ s, q ^ k = q ^ i * (q * d i))
    (R : ℝ) (hR : 0 ≤ R)
    (hbad : ∀ L ∈ Finset.Ioc H (2 * H),
      ∀ a ∉ cyclicGoodResidues q k H,
        Complex.normSq
          (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a) ≤ R) :
    (H : ℝ) *
        ((s.card : ℝ) * ((q ^ k : ℕ) : ℝ) * (q.totient : ℝ)) ≤
      8 * (q : ℝ) *
        ((∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ cyclicGoodResidues q k H,
              Complex.normSq
                (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a)) +
          (H : ℝ) *
            ((((2 * H) * q.primeFactors.card * (q ^ k / 2 ^ k) : ℕ) : ℝ) * R)) := by
  have hbase := qpower_card_lower_le_medium_good_prefix_energy
    s χ hχ d hq hd hdH hN (cyclicGoodResidues q k H) R hbad
  have hcardNat :
      ((Finset.univ \ cyclicGoodResidues q k H).card) ≤
        (2 * H) * q.primeFactors.card * (q ^ k / 2 ^ k) := by
    simpa [cyclicGoodResidues] using card_cyclicBadResidues_le_twoPow q k H
  have hcard :
      (((Finset.univ \ cyclicGoodResidues q k H).card : ℕ) : ℝ) ≤
        (((2 * H) * q.primeFactors.card * (q ^ k / 2 ^ k) : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  refine hbase.trans ?_
  gcongr

/-! ## Cauchy and the Euler-residue dependency boundary -/

/-- Finite Cauchy--Schwarz for complex sums, in squared-norm form. -/
theorem normSq_sum_le_card_mul_sum_normSq {iota : Type*}
    (s : Finset iota) (f : iota → ℂ) :
    Complex.normSq (∑ i ∈ s, f i) ≤
      (s.card : ℝ) * ∑ i ∈ s, Complex.normSq (f i) := by
  classical
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ = (s.card : ℝ) * ∑ i ∈ s, Complex.normSq (f i) := by
      simp only [Complex.normSq_eq_norm_sq]

/-- The exact lower-bound input supplied by the Euler-product residue-class
calculation: every selected residue fiber carries at least mass `rho`.

This is a definition, not a global assumption.  The reduction theorem below
takes a proof of it as an ordinary argument. -/
def EulerResidueLowerBound {iota alpha : Type*} [DecidableEq alpha]
    (s : Finset iota) (residue : iota → alpha) (weight : iota → ℝ)
    (good : Finset alpha) (rho : ℝ) : Prop :=
  ∀ a ∈ good, rho ≤ ∑ i ∈ s.filter (fun i ↦ residue i = a), weight i

/-- Weighted energy on the finite source. -/
def weightedResidueEnergy {iota alpha : Type*}
    (s : Finset iota) (residue : iota → alpha) (weight : iota → ℝ)
    (F : alpha → ℂ) : ℝ :=
  ∑ i ∈ s, weight i * Complex.normSq (F (residue i))

/-- Once the explicit Euler residue-mass lower bound is provided, the total
weighted energy dominates `rho` times the energy on the good residues. -/
theorem rho_mul_goodResidueEnergy_le_weighted
    {iota alpha : Type*} [DecidableEq alpha]
    (s : Finset iota) (residue : iota → alpha) (weight : iota → ℝ)
    (good : Finset alpha) (F : alpha → ℂ) (rho : ℝ)
    (hweight : ∀ i ∈ s, 0 ≤ weight i)
    (hEuler : EulerResidueLowerBound s residue weight good rho) :
    rho * ∑ a ∈ good, Complex.normSq (F a) ≤
      weightedResidueEnergy s residue weight F := by
  classical
  calc
    rho * ∑ a ∈ good, Complex.normSq (F a) =
        ∑ a ∈ good, rho * Complex.normSq (F a) := by rw [Finset.mul_sum]
    _ ≤ ∑ a ∈ good,
        (∑ i ∈ s.filter (fun i ↦ residue i = a), weight i) *
          Complex.normSq (F a) := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_right (hEuler a ha) (Complex.normSq_nonneg _)
    _ = ∑ i ∈ s, ∑ a ∈ good,
        if residue i = a then weight i * Complex.normSq (F a) else 0 := by
      simp_rw [Finset.sum_filter, Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
    _ ≤ ∑ i ∈ s, weight i * Complex.normSq (F (residue i)) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hir : residue i ∈ good
      · simp [hir, eq_comm]
      · simp [hir, eq_comm, mul_nonneg (hweight i hi) (Complex.normSq_nonneg _)]
    _ = weightedResidueEnergy s residue weight F := rfl

/-- Consumer form of the residue-energy reduction.  The only analytic input
is the displayed `EulerResidueLowerBound` proof. -/
theorem goodResidueEnergy_le_of_eulerResidue
    {iota alpha : Type*} [DecidableEq alpha]
    (s : Finset iota) (residue : iota → alpha) (weight : iota → ℝ)
    (good : Finset alpha) (F : alpha → ℂ) (rho B : ℝ)
    (hrho : 0 < rho) (hweight : ∀ i ∈ s, 0 ≤ weight i)
    (hEuler : EulerResidueLowerBound s residue weight good rho)
    (henergy : weightedResidueEnergy s residue weight F ≤ B) :
    (∑ a ∈ good, Complex.normSq (F a)) ≤ B / rho := by
  rw [le_div_iff₀ hrho]
  simpa only [mul_comm] using (rho_mul_goodResidueEnergy_le_weighted
    s residue weight good F rho hweight hEuler).trans henergy

/-! ## Discharging the residue input with `EulerResidue` -/

/-- The complex weighted energy obtained after grouping the Dirichlet series
by residue class.  This is the finite residue sum which occurs immediately
before Tao divides by the singular-series main term. -/
def eulerResidueWeightedEnergy {r : ℕ} [NeZero r]
    (h : ℕ →*₀ ℂ) (sigma : ℂ) (good : Finset (ZMod r))
    (A : ZMod r → ℂ) : ℂ :=
  ∑ a ∈ good, EulerResidue.residueLSeries h a sigma * Complex.normSq (A a)

/-- The explicit error furnished by the principal/nonprincipal decomposition
in `EulerResidue.norm_residueLSeries_sub_main_le`. -/
def eulerResidueError (r : ℕ) (E₀ E : ℝ) : ℝ :=
  E₀ + ‖((r.totient : ℂ)⁻¹)‖ *
    ((EulerResidue.nonprincipalCharacters r).card : ℝ) * E

/-- Deterministic weighted-to-residue-energy transfer with the Euler input
fully discharged by `EulerResidue.norm_residueLSeries_sub_main_le`.

The conclusion is exact: the denominator is the norm of the main term minus
the complete, explicit character-expansion error. -/
theorem goodResidueEnergy_le_of_eulerResidueLSeries
    {r : ℕ} [NeZero r] {h : ℕ →*₀ ℂ}
    (hh : EulerResidue.HasUnitNorm h) {sigma : ℂ} (hsigma : 1 < sigma.re)
    (M : ℂ) (E₀ E : ℝ)
    (hprincipal :
      ‖(r.totient : ℂ)⁻¹ * EulerResidue.principalTwistSeries h r sigma - M‖ ≤ E₀)
    (hnonprincipal : EulerResidue.NonprincipalTwistsBounded h r sigma E)
    (good : Finset (ZMod r)) (hgood : ∀ a ∈ good, IsUnit a)
    (A : ZMod r → ℂ) (B : ℝ)
    (hgap : eulerResidueError r E₀ E < ‖M‖)
    (hweighted : ‖eulerResidueWeightedEnergy h sigma good A‖ ≤ B) :
    (∑ a ∈ good, Complex.normSq (A a)) ≤
      B / (‖M‖ - eulerResidueError r E₀ E) := by
  classical
  let T : ℝ := ∑ a ∈ good, Complex.normSq (A a)
  let Err : ℝ := eulerResidueError r E₀ E
  have hT : 0 ≤ T := by
    dsimp [T]
    exact Finset.sum_nonneg fun a _ ↦ Complex.normSq_nonneg (A a)
  have hres (a : ZMod r) (ha : a ∈ good) :
      ‖EulerResidue.residueLSeries h a sigma - M‖ ≤ Err := by
    simpa only [Err, eulerResidueError] using
      EulerResidue.norm_residueLSeries_sub_main_le (r := r) hh hsigma M E₀ E
        hprincipal hnonprincipal (hgood a ha)
  have hid :
      M * (T : ℂ) = eulerResidueWeightedEnergy h sigma good A +
        ∑ a ∈ good,
          (M - EulerResidue.residueLSeries h a sigma) * Complex.normSq (A a) := by
    dsimp [T, eulerResidueWeightedEnergy]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have herrsum :
      ‖∑ a ∈ good,
          (M - EulerResidue.residueLSeries h a sigma) * Complex.normSq (A a)‖ ≤
        Err * T := by
    refine (norm_sum_le _ _).trans ?_
    calc
      (∑ a ∈ good,
          ‖(M - EulerResidue.residueLSeries h a sigma) * Complex.normSq (A a)‖) ≤
          ∑ a ∈ good, Err * Complex.normSq (A a) := by
        apply Finset.sum_le_sum
        intro a ha
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Complex.normSq_nonneg (A a))]
        apply mul_le_mul_of_nonneg_right _ (Complex.normSq_nonneg (A a))
        rw [show M - EulerResidue.residueLSeries h a sigma =
          -(EulerResidue.residueLSeries h a sigma - M) by ring, norm_neg]
        exact hres a ha
      _ = Err * T := by
        dsimp [T]
        rw [Finset.mul_sum]
  have hmain : ‖M‖ * T ≤ B + Err * T := by
    calc
      ‖M‖ * T = ‖M * (T : ℂ)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT]
      _ = ‖eulerResidueWeightedEnergy h sigma good A +
          ∑ a ∈ good,
            (M - EulerResidue.residueLSeries h a sigma) * Complex.normSq (A a)‖ := by
        rw [hid]
      _ ≤ ‖eulerResidueWeightedEnergy h sigma good A‖ +
          ‖∑ a ∈ good,
            (M - EulerResidue.residueLSeries h a sigma) * Complex.normSq (A a)‖ :=
        norm_add_le _ _
      _ ≤ B + Err * T := add_le_add hweighted herrsum
  have hden : 0 < ‖M‖ - Err := sub_pos.mpr (by simpa [Err] using hgap)
  rw [le_div_iff₀ hden]
  dsimp [T] at hmain
  nlinarith

/-- The same deterministic transfer with a uniform Euler estimate for all
selected residue classes.  In particular, no residue is assumed to be a
unit.  The gcd-reduction theorem in `EulerResidue` supplies `hresidue` for
the actual good classes used by Tao. -/
theorem goodResidueEnergy_le_of_uniformResidueLSeries
    {r : ℕ} [NeZero r] {h : ℕ →*₀ ℂ} {sigma : ℂ}
    (M : ℂ) (Err : ℝ)
    (hresidue : ∀ a : ZMod r,
      ‖EulerResidue.residueLSeries h a sigma - M‖ ≤ Err)
    (good : Finset (ZMod r)) (A : ZMod r → ℂ) (B : ℝ)
    (hgap : Err < ‖M‖)
    (hweighted : ‖eulerResidueWeightedEnergy h sigma good A‖ ≤ B) :
    (∑ a ∈ good, Complex.normSq (A a)) ≤ B / (‖M‖ - Err) := by
  classical
  let T : ℝ := ∑ a ∈ good, Complex.normSq (A a)
  have hT : 0 ≤ T := by
    dsimp [T]
    exact Finset.sum_nonneg fun a _ ↦ Complex.normSq_nonneg (A a)
  have hid :
      M * (T : ℂ) = eulerResidueWeightedEnergy h sigma good A +
        ∑ a ∈ good,
          (M - EulerResidue.residueLSeries h a sigma) * Complex.normSq (A a) := by
    dsimp [T, eulerResidueWeightedEnergy]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have herrsum :
      ‖∑ a ∈ good,
          (M - EulerResidue.residueLSeries h a sigma) * Complex.normSq (A a)‖ ≤
        Err * T := by
    refine (norm_sum_le _ _).trans ?_
    calc
      (∑ a ∈ good,
          ‖(M - EulerResidue.residueLSeries h a sigma) * Complex.normSq (A a)‖) ≤
          ∑ a ∈ good, Err * Complex.normSq (A a) := by
        apply Finset.sum_le_sum
        intro a ha
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Complex.normSq_nonneg (A a))]
        apply mul_le_mul_of_nonneg_right _ (Complex.normSq_nonneg (A a))
        rw [show M - EulerResidue.residueLSeries h a sigma =
          -(EulerResidue.residueLSeries h a sigma - M) by ring, norm_neg]
        exact hresidue a
      _ = Err * T := by
        dsimp [T]
        rw [Finset.mul_sum]
  have hmain : ‖M‖ * T ≤ B + Err * T := by
    calc
      ‖M‖ * T = ‖M * (T : ℂ)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT]
      _ = ‖eulerResidueWeightedEnergy h sigma good A +
          ∑ a ∈ good,
            (M - EulerResidue.residueLSeries h a sigma) * Complex.normSq (A a)‖ := by
        rw [hid]
      _ ≤ ‖eulerResidueWeightedEnergy h sigma good A‖ +
          ‖∑ a ∈ good,
            (M - EulerResidue.residueLSeries h a sigma) * Complex.normSq (A a)‖ :=
        norm_add_le _ _
      _ ≤ B + Err * T := add_le_add hweighted herrsum
  have hden : 0 < ‖M‖ - Err := sub_pos.mpr hgap
  rw [le_div_iff₀ hden]
  dsimp [T] at hmain
  nlinarith

/-- Scale-free transfer from a uniform estimate valid for arbitrary
residue classes. -/
theorem normalized_goodResidueEnergy_le_two_mul_of_uniformResidueLSeries
    {r : ℕ} [NeZero r] {h : ℕ →*₀ ℂ} {sigma : ℂ}
    (M : ℂ) (Err K : ℝ)
    (hresidue : ∀ a : ZMod r,
      ‖EulerResidue.residueLSeries h a sigma - M‖ ≤ Err)
    (good : Finset (ZMod r)) (A : ZMod r → ℂ)
    (hM : 0 < ‖M‖) (hhalf : 2 * Err ≤ ‖M‖)
    (hweighted : ‖eulerResidueWeightedEnergy h sigma good A‖ ≤
      K * ‖M‖ * (r : ℝ)) :
    (1 / (r : ℝ)) * ∑ a ∈ good, Complex.normSq (A a) ≤ 2 * K := by
  have hgap : Err < ‖M‖ := by linarith
  have hraw := goodResidueEnergy_le_of_uniformResidueLSeries M Err hresidue
    good A (K * ‖M‖ * (r : ℝ)) hgap hweighted
  have hden : ‖M‖ / 2 ≤ ‖M‖ - Err := by linarith
  have hT : 0 ≤ ∑ a ∈ good, Complex.normSq (A a) :=
    Finset.sum_nonneg fun a _ ↦ Complex.normSq_nonneg (A a)
  have hmul :
      (‖M‖ - Err) * (∑ a ∈ good, Complex.normSq (A a)) ≤
        K * ‖M‖ * (r : ℝ) := by
    simpa only [mul_comm] using (le_div_iff₀ (sub_pos.mpr hgap)).mp hraw
  have hmul' : ‖M‖ / 2 * (∑ a ∈ good, Complex.normSq (A a)) ≤
      K * ‖M‖ * (r : ℝ) :=
    (mul_le_mul_of_nonneg_right hden hT).trans hmul
  have hr : (0 : ℝ) < r := by exact_mod_cast NeZero.pos r
  rw [one_div, inv_mul_eq_div, div_le_iff₀ hr]
  have hcancel :
      ∑ a ∈ good, Complex.normSq (A a) ≤ 2 * K * (r : ℝ) := by
    apply le_of_mul_le_mul_left _ hM
    nlinarith
  simpa only [mul_assoc] using hcancel

/-- Medium-length form of the arbitrary-class transfer. -/
theorem normalized_medium_goodResidueEnergy_le_two_mul_of_uniformResidueLSeries
    {r : ℕ} [NeZero r] {h : ℕ →*₀ ℂ} {sigma : ℂ}
    (M : ℂ) (Err K : ℝ)
    (hresidue : ∀ a : ZMod r,
      ‖EulerResidue.residueLSeries h a sigma - M‖ ≤ Err)
    (good : Finset (ZMod r)) (A : ℕ → ZMod r → ℂ)
    (H : ℕ) (hH : 0 < H) (hM : 0 < ‖M‖)
    (hhalf : 2 * Err ≤ ‖M‖)
    (hweighted : ∀ H' ∈ Finset.Ioc H (2 * H),
      ‖eulerResidueWeightedEnergy h sigma good (A H')‖ ≤
        K * ‖M‖ * (r : ℝ)) :
    (1 / ((r : ℝ) * H)) *
        ∑ H' ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good, Complex.normSq (A H' a) ≤ 2 * K := by
  have hr : (0 : ℝ) < r := by exact_mod_cast NeZero.pos r
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hone (H' : ℕ) (hH' : H' ∈ Finset.Ioc H (2 * H)) :
      ∑ a ∈ good, Complex.normSq (A H' a) ≤ 2 * K * (r : ℝ) := by
    have hn :=
      normalized_goodResidueEnergy_le_two_mul_of_uniformResidueLSeries
        M Err K hresidue good (A H') hM hhalf (hweighted H' hH')
    rw [one_div, inv_mul_eq_div, div_le_iff₀ hr] at hn
    exact hn
  have hsum :
      (∑ H' ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good, Complex.normSq (A H' a)) ≤
        (H : ℝ) * (2 * K * (r : ℝ)) := by
    calc
      (∑ H' ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good, Complex.normSq (A H' a)) ≤
          ∑ _H' ∈ Finset.Ioc H (2 * H), 2 * K * (r : ℝ) := by
        apply Finset.sum_le_sum
        intro H' hH'
        exact hone H' hH'
      _ = (H : ℝ) * (2 * K * (r : ℝ)) := by
        have hcard : (Finset.Ioc H (2 * H)).card = H := by
          rw [Nat.card_Ioc]
          omega
        simp [hcard, nsmul_eq_mul]
  rw [one_div, inv_mul_eq_div, div_le_iff₀ (mul_pos hr hHR)]
  calc
    (∑ H' ∈ Finset.Ioc H (2 * H),
        ∑ a ∈ good, Complex.normSq (A H' a)) ≤
        (H : ℝ) * (2 * K * (r : ℝ)) := hsum
    _ = 2 * K * ((r : ℝ) * H) := by ring

/-! ## The shifted convolution in Tao's equation (15) -/

/-- The residue-class convolution which actually occurs after the weighted
local-increment estimate is grouped modulo `r`.  Notice that the residue
series is *inside* the sum over the shift.  This is the essential feature
missing from the older pointwise-product interface below. -/
def shiftedResidueConvolution {r : ℕ} [NeZero r]
    (h : ℕ →*₀ ℂ) (sigma : ℂ) (u : ZMod r → ℂ)
    (L : ℕ) (a : ZMod r) : ℂ :=
  ∑ m ∈ Finset.Icc 1 L,
    u (a + (m : ZMod r)) *
      EulerResidue.residueLSeries h (a + (m : ZMod r)) sigma

/-- The unweighted prefix left after every residue series in the shifted
convolution is replaced by its common main term. -/
def shiftedResiduePrefix {r : ℕ} [NeZero r]
    (u : ZMod r → ℂ) (L : ℕ) (a : ZMod r) : ℂ :=
  ∑ m ∈ Finset.Icc 1 L, u (a + (m : ZMod r))

/-- Tao's grouped energy: a sum of squared norms of shifted convolutions.
Unlike `eulerMappedResidueWeightedEnergy`, this is real and nonnegative. -/
def shiftedResidueConvolutionEnergy {r : ℕ} [NeZero r]
    (h : ℕ →*₀ ℂ) (sigma : ℂ) (u : ZMod r → ℂ)
    (good : Finset (ZMod r)) (L : ℕ) : ℝ :=
  ∑ a ∈ good, Complex.normSq (shiftedResidueConvolution h sigma u L a)

/-- Replacing every residue series by the same main term costs at most
`L * Err`, provided the shift coefficients lie in the closed unit disc. -/
theorem norm_shiftedResidueConvolution_sub_main_mul_prefix_le
    {r : ℕ} [NeZero r] {h : ℕ →*₀ ℂ} {sigma M : ℂ}
    {Err : ℝ} (_hErr : 0 ≤ Err)
    (hresidue : ∀ b : ZMod r,
      ‖EulerResidue.residueLSeries h b sigma - M‖ ≤ Err)
    (u : ZMod r → ℂ) (hu : ∀ b, ‖u b‖ ≤ 1)
    (L : ℕ) (a : ZMod r) :
    ‖shiftedResidueConvolution h sigma u L a -
        M * shiftedResiduePrefix u L a‖ ≤ (L : ℝ) * Err := by
  classical
  have hid :
      shiftedResidueConvolution h sigma u L a -
          M * shiftedResiduePrefix u L a =
        ∑ m ∈ Finset.Icc 1 L,
          u (a + (m : ZMod r)) *
            (EulerResidue.residueLSeries h (a + (m : ZMod r)) sigma - M) := by
    simp only [shiftedResidueConvolution, shiftedResiduePrefix]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [hid]
  calc
    ‖∑ m ∈ Finset.Icc 1 L,
        u (a + (m : ZMod r)) *
          (EulerResidue.residueLSeries h (a + (m : ZMod r)) sigma - M)‖ ≤
        ∑ m ∈ Finset.Icc 1 L,
          ‖u (a + (m : ZMod r)) *
            (EulerResidue.residueLSeries h (a + (m : ZMod r)) sigma - M)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc 1 L, Err := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul]
      exact (mul_le_mul (hu _) (hresidue _) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul Err)
    _ = (L : ℝ) * Err := by
      have hcard : (Finset.Icc 1 L).card = L := by
        rw [Nat.card_Icc]
        omega
      simp [hcard]

/-- Pointwise squared-norm form of the common-main-term replacement. -/
theorem normSq_main_mul_shiftedResiduePrefix_le
    {r : ℕ} [NeZero r] {h : ℕ →*₀ ℂ} {sigma M : ℂ}
    {Err : ℝ} (hErr : 0 ≤ Err)
    (hresidue : ∀ b : ZMod r,
      ‖EulerResidue.residueLSeries h b sigma - M‖ ≤ Err)
    (u : ZMod r → ℂ) (hu : ∀ b, ‖u b‖ ≤ 1)
    (L : ℕ) (a : ZMod r) :
    Complex.normSq (M * shiftedResiduePrefix u L a) ≤
      2 * Complex.normSq (shiftedResidueConvolution h sigma u L a) +
        2 * ((L : ℝ) * Err) ^ 2 := by
  have herr := norm_shiftedResidueConvolution_sub_main_mul_prefix_le
    hErr hresidue u hu L a
  have hsquare :
      ‖shiftedResidueConvolution h sigma u L a -
          M * shiftedResiduePrefix u L a‖ ^ 2 ≤ ((L : ℝ) * Err) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) herr 2
  have hbase := norm_sub_sq_le_two_mul_add
    (shiftedResidueConvolution h sigma u L a)
    (shiftedResidueConvolution h sigma u L a -
      M * shiftedResiduePrefix u L a)
  rw [show shiftedResidueConvolution h sigma u L a -
      (shiftedResidueConvolution h sigma u L a -
        M * shiftedResiduePrefix u L a) =
      M * shiftedResiduePrefix u L a by ring] at hbase
  simp only [Complex.normSq_eq_norm_sq]
  nlinarith

/-- Aggregate common-main-term transfer in precisely the medium-length form
needed by BCC.  Both hypotheses are scale-normalized.  Thus if `K` and `J`
are absolute constants, so is the conclusion, independently of `r` and
`H`. -/
theorem normalized_medium_shiftedResiduePrefixEnergy_le
    {r : ℕ} [NeZero r] {h : ℕ →*₀ ℂ} {sigma M : ℂ}
    {Err K J : ℝ} (hErr : 0 ≤ Err)
    (hresidue : ∀ b : ZMod r,
      ‖EulerResidue.residueLSeries h b sigma - M‖ ≤ Err)
    (u : ZMod r → ℂ) (hu : ∀ b, ‖u b‖ ≤ 1)
    (good : Finset (ZMod r)) (H : ℕ) (hH : 0 < H) (hM : 0 < ‖M‖)
    (hconv :
      ∑ L ∈ Finset.Ioc H (2 * H),
          shiftedResidueConvolutionEnergy h sigma u good L ≤
        K * ‖M‖ ^ 2 * ((r : ℕ) : ℝ) * H)
    (hsmall : 4 * (H : ℝ) ^ 2 * Err ^ 2 ≤ J * ‖M‖ ^ 2) :
    (1 / (((r : ℕ) : ℝ) * H)) *
        ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good, Complex.normSq (shiftedResiduePrefix u L a) ≤
      2 * K + 2 * J := by
  classical
  have hr : (0 : ℝ) < r := by exact_mod_cast NeZero.pos r
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hcardGoodNat : good.card ≤ r := by
    simpa only [Finset.card_univ, ZMod.card] using
      (Finset.card_le_card (Finset.subset_univ good))
  have hcardGood : (good.card : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast hcardGoodNat
  have hpoint (L : ℕ) (hL : L ∈ Finset.Ioc H (2 * H)) (a : ZMod r) :
      ‖M‖ ^ 2 * Complex.normSq (shiftedResiduePrefix u L a) ≤
        2 * Complex.normSq (shiftedResidueConvolution h sigma u L a) +
          2 * ((L : ℝ) * Err) ^ 2 := by
    have hraw :=
      normSq_main_mul_shiftedResiduePrefix_le hErr hresidue u hu L a
    rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq] at hraw
    exact hraw
  have hLerr (L : ℕ) (hL : L ∈ Finset.Ioc H (2 * H)) :
      ((L : ℝ) * Err) ^ 2 ≤ 4 * (H : ℝ) ^ 2 * Err ^ 2 := by
    have hLR : (L : ℝ) ≤ 2 * H := by
      exact_mod_cast (Finset.mem_Ioc.mp hL).2
    have hL0 : (0 : ℝ) ≤ L := by positivity
    have hER : 0 ≤ Err := hErr
    nlinarith [sq_nonneg ((L : ℝ) * Err), sq_nonneg ((H : ℝ) * Err),
      mul_self_le_mul_self (mul_nonneg hL0 hER)
        (mul_le_mul hLR (le_refl Err) hER (by positivity))]
  have hsumPoint :
      ‖M‖ ^ 2 *
          (∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ good, Complex.normSq (shiftedResiduePrefix u L a)) ≤
        2 * (∑ L ∈ Finset.Ioc H (2 * H),
          shiftedResidueConvolutionEnergy h sigma u good L) +
          2 * ((H : ℝ) * ((r : ℝ) * (4 * (H : ℝ) ^ 2 * Err ^ 2))) := by
    calc
      ‖M‖ ^ 2 *
          (∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ good, Complex.normSq (shiftedResiduePrefix u L a)) =
          ∑ L ∈ Finset.Ioc H (2 * H), ∑ a ∈ good,
            ‖M‖ ^ 2 * Complex.normSq (shiftedResiduePrefix u L a) := by
        simp_rw [Finset.mul_sum]
      _ ≤ ∑ L ∈ Finset.Ioc H (2 * H), ∑ a ∈ good,
          (2 * Complex.normSq (shiftedResidueConvolution h sigma u L a) +
            2 * ((L : ℝ) * Err) ^ 2) := by
        apply Finset.sum_le_sum
        intro L hL
        apply Finset.sum_le_sum
        intro a ha
        exact hpoint L hL a
      _ ≤ ∑ L ∈ Finset.Ioc H (2 * H), ∑ _a ∈ good,
          (2 * Complex.normSq (shiftedResidueConvolution h sigma u L _a) +
            2 * (4 * (H : ℝ) ^ 2 * Err ^ 2)) := by
        apply Finset.sum_le_sum
        intro L hL
        apply Finset.sum_le_sum
        intro a ha
        gcongr
        exact hLerr L hL
      _ = 2 * (∑ L ∈ Finset.Ioc H (2 * H),
          shiftedResidueConvolutionEnergy h sigma u good L) +
          2 * ((H : ℝ) * ((good.card : ℝ) *
            (4 * (H : ℝ) ^ 2 * Err ^ 2))) := by
        have hcard : (Finset.Ioc H (2 * H)).card = H := by
          rw [Nat.card_Ioc]
          omega
        simp only [shiftedResidueConvolutionEnergy, Finset.sum_add_distrib,
          Finset.mul_sum]
        simp [hcard]
        ring
      _ ≤ 2 * (∑ L ∈ Finset.Ioc H (2 * H),
          shiftedResidueConvolutionEnergy h sigma u good L) +
          2 * ((H : ℝ) * ((r : ℝ) *
            (4 * (H : ℝ) ^ 2 * Err ^ 2))) := by
        gcongr
  have hscaled :
      ‖M‖ ^ 2 *
          (∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ good, Complex.normSq (shiftedResiduePrefix u L a)) ≤
        (2 * K + 2 * J) * ‖M‖ ^ 2 * ((r : ℝ) * H) := by
    refine hsumPoint.trans ?_
    calc
      2 * (∑ L ∈ Finset.Ioc H (2 * H),
          shiftedResidueConvolutionEnergy h sigma u good L) +
          2 * ((H : ℝ) * ((r : ℝ) *
            (4 * (H : ℝ) ^ 2 * Err ^ 2))) ≤
          2 * (K * ‖M‖ ^ 2 * (r : ℝ) * H) +
            2 * ((H : ℝ) * ((r : ℝ) * (J * ‖M‖ ^ 2))) := by
        gcongr
      _ = (2 * K + 2 * J) * ‖M‖ ^ 2 * ((r : ℝ) * H) := by ring
  rw [one_div, inv_mul_eq_div, div_le_iff₀ (mul_pos hr hHR)]
  apply le_of_mul_le_mul_left _ (sq_pos_of_pos hM)
  nlinarith

/-- Correct normalized-main, nonunit-residue endpoint for Tao's shifted
convolution.  The arbitrary-residue estimate (including gcd reduction) is
discharged here.  The stochastic side has to supply the *aggregate*
convolution bound `hconv`; no pointwise product of a residue series and an
already formed prefix appears in this statement. -/
theorem normalized_medium_cyclicGood_shiftedResiduePrefixEnergy_le
    {q : ℕ} [NeZero q] (k : ℕ) {h : ℕ →*₀ ℂ}
    (hh : EulerResidue.HasUnitNorm h) {sigma : ℂ} (hsigma : 1 < sigma.re)
    (S : ℂ) (E₀ E delta : ℕ → ℝ) (Err K J : ℝ)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ q → h p = 1)
    (hprincipal : ∀ t, t ∣ q ^ k → t ≠ 0 →
      ‖(t.totient : ℂ)⁻¹ * EulerResidue.principalTwistSeries h t sigma -
          S / (t : ℂ)‖ ≤ E₀ t)
    (hnonprincipal : ∀ t, t ∣ q ^ k → t ≠ 0 →
      EulerResidue.NonprincipalTwistsBounded h t sigma (E t))
    (hfactor : ∀ d, d ∣ q ^ k → d ≠ 0 →
      ‖(d : ℂ) ^ (1 - sigma) - 1‖ ≤ delta d)
    (hbudget : ∀ d, d ∣ q ^ k → d ≠ 0 →
      ‖EulerResidue.residueScale h d sigma‖ *
          eulerResidueError (q ^ k / d) (E₀ (q ^ k / d)) (E (q ^ k / d)) +
        ‖S / ((q ^ k : ℕ) : ℂ)‖ * delta d ≤ Err)
    (u : ZMod (q ^ k) → ℂ) (hu : ∀ b, ‖u b‖ ≤ 1)
    (H : ℕ) (hH : 0 < H)
    (hMain : 0 < ‖S / ((q ^ k : ℕ) : ℂ)‖) (hErr : 0 ≤ Err)
    (hconv :
      ∑ L ∈ Finset.Ioc H (2 * H),
          shiftedResidueConvolutionEnergy h sigma u
            (cyclicGoodResidues q k H) L ≤
        K * ‖S / ((q ^ k : ℕ) : ℂ)‖ ^ 2 *
          ((q ^ k : ℕ) : ℝ) * H)
    (hsmall :
      4 * (H : ℝ) ^ 2 * Err ^ 2 ≤
        J * ‖S / ((q ^ k : ℕ) : ℂ)‖ ^ 2) :
    (1 / (((q ^ k : ℕ) : ℝ) * H)) *
        ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ cyclicGoodResidues q k H,
            Complex.normSq (shiftedResiduePrefix u L a) ≤
      2 * K + 2 * J := by
  let Main : ℂ := S / ((q ^ k : ℕ) : ℂ)
  let Mdiv : ℕ → ℂ := fun t ↦ S / (t : ℂ)
  let U : ℕ → ℝ := fun t ↦ eulerResidueError t (E₀ t) (E t)
  let Esc : ℕ → ℝ := fun d ↦ ‖Main‖ * delta d
  have hunit : ∀ t, t ∣ q ^ k → t ≠ 0 →
      ∀ b : ZMod t, IsUnit b →
        ‖EulerResidue.residueLSeries h b sigma - Mdiv t‖ ≤ U t := by
    intro t ht ht0 b hb
    letI : NeZero t := ⟨ht0⟩
    simpa only [U, Mdiv, eulerResidueError] using
      EulerResidue.norm_residueLSeries_sub_main_le hh hsigma
        (S / (t : ℂ)) (E₀ t) (E t) (hprincipal t ht ht0)
          (hnonprincipal t ht ht0) hb
  have hscale : ∀ d, d ∣ q ^ k → d ≠ 0 →
      ‖EulerResidue.residueScale h d sigma * Mdiv (q ^ k / d) - Main‖ ≤
        Esc d := by
    intro d hd hd0
    have hdone : h d = 1 :=
      EulerResidue.map_eq_one_of_dvd_pow (NeZero.ne q) hprime hd
    have heq := EulerResidue.residueScale_mul_div_reducedModulus
      hd (pow_ne_zero k (NeZero.ne q)) hdone sigma S
    dsimp only [Mdiv, Main, Esc]
    rw [heq]
    calc
      ‖S / ((q ^ k : ℕ) : ℂ) * (d : ℂ) ^ (1 - sigma) -
          S / ((q ^ k : ℕ) : ℂ)‖ =
          ‖(S / ((q ^ k : ℕ) : ℂ)) *
            ((d : ℂ) ^ (1 - sigma) - 1)‖ := by ring_nf
      _ = ‖S / ((q ^ k : ℕ) : ℂ)‖ *
          ‖(d : ℂ) ^ (1 - sigma) - 1‖ := norm_mul _ _
      _ ≤ ‖S / ((q ^ k : ℕ) : ℂ)‖ * delta d :=
        mul_le_mul_of_nonneg_left (hfactor d hd hd0) (norm_nonneg _)
  have hresidue : ∀ a : ZMod (q ^ k),
      ‖EulerResidue.residueLSeries h a sigma - Main‖ ≤ Err := by
    apply EulerResidue.uniform_arbitrary_residue_estimate hh hsigma
      Mdiv U Esc Main Err
    · exact hunit
    · exact hscale
    · intro d hd hd0
      simpa only [U, Esc, Main] using hbudget d hd hd0
  apply normalized_medium_shiftedResiduePrefixEnergy_le
    hErr hresidue u hu (cyclicGoodResidues q k H) H hH
  · simpa only [Main] using hMain
  · simpa only [Main] using hconv
  · simpa only [Main] using hsmall

/-- Legacy algebraic energy in which one residue-series value multiplies a
prefix norm.  This remains useful as a standalone deterministic identity,
but it is **not** the grouped stochastic energy in Tao's equation (15).
New Section 4 consumers must use `shiftedResidueConvolutionEnergy`. -/
def eulerMappedResidueWeightedEnergy {r : ℕ} [NeZero r]
    (h : ℕ →*₀ ℂ) (sigma : ℂ) (good : Finset (ZMod r))
    (classOf : ZMod r → ZMod r) (A : ZMod r → ℂ) : ℂ :=
  ∑ a ∈ good,
    EulerResidue.residueLSeries h (classOf a) sigma * Complex.normSq (A a)

/-- Deterministic transfer for shifted or otherwise mapped residue classes,
using a uniform estimate on every target residue. -/
theorem goodResidueEnergy_le_of_uniform_mappedResidueLSeries
    {r : ℕ} [NeZero r] {h : ℕ →*₀ ℂ} {sigma : ℂ}
    (M : ℂ) (Err : ℝ)
    (hresidue : ∀ a : ZMod r,
      ‖EulerResidue.residueLSeries h a sigma - M‖ ≤ Err)
    (good : Finset (ZMod r)) (classOf : ZMod r → ZMod r)
    (A : ZMod r → ℂ) (B : ℝ) (hgap : Err < ‖M‖)
    (hweighted :
      ‖eulerMappedResidueWeightedEnergy h sigma good classOf A‖ ≤ B) :
    (∑ a ∈ good, Complex.normSq (A a)) ≤ B / (‖M‖ - Err) := by
  classical
  let T : ℝ := ∑ a ∈ good, Complex.normSq (A a)
  have hT : 0 ≤ T := by
    dsimp [T]
    exact Finset.sum_nonneg fun a _ ↦ Complex.normSq_nonneg (A a)
  have hid :
      M * (T : ℂ) = eulerMappedResidueWeightedEnergy h sigma good classOf A +
        ∑ a ∈ good,
          (M - EulerResidue.residueLSeries h (classOf a) sigma) *
            Complex.normSq (A a) := by
    dsimp [T, eulerMappedResidueWeightedEnergy]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have herrsum :
      ‖∑ a ∈ good,
          (M - EulerResidue.residueLSeries h (classOf a) sigma) *
            Complex.normSq (A a)‖ ≤ Err * T := by
    refine (norm_sum_le _ _).trans ?_
    calc
      (∑ a ∈ good,
          ‖(M - EulerResidue.residueLSeries h (classOf a) sigma) *
            Complex.normSq (A a)‖) ≤
          ∑ a ∈ good, Err * Complex.normSq (A a) := by
        apply Finset.sum_le_sum
        intro a ha
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Complex.normSq_nonneg (A a))]
        apply mul_le_mul_of_nonneg_right _ (Complex.normSq_nonneg (A a))
        rw [show M - EulerResidue.residueLSeries h (classOf a) sigma =
          -(EulerResidue.residueLSeries h (classOf a) sigma - M) by ring, norm_neg]
        exact hresidue (classOf a)
      _ = Err * T := by
        dsimp [T]
        rw [Finset.mul_sum]
  have hmain : ‖M‖ * T ≤ B + Err * T := by
    calc
      ‖M‖ * T = ‖M * (T : ℂ)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT]
      _ = ‖eulerMappedResidueWeightedEnergy h sigma good classOf A +
          ∑ a ∈ good,
            (M - EulerResidue.residueLSeries h (classOf a) sigma) *
              Complex.normSq (A a)‖ := by rw [hid]
      _ ≤ ‖eulerMappedResidueWeightedEnergy h sigma good classOf A‖ +
          ‖∑ a ∈ good,
            (M - EulerResidue.residueLSeries h (classOf a) sigma) *
              Complex.normSq (A a)‖ := norm_add_le _ _
      _ ≤ B + Err * T := add_le_add hweighted herrsum
  have hden : 0 < ‖M‖ - Err := sub_pos.mpr hgap
  rw [le_div_iff₀ hden]
  dsimp [T] at hmain
  nlinarith

/-- Scale-free medium estimate for arbitrary shifted residue maps. -/
theorem normalized_medium_mappedResidueEnergy_le_two_mul
    {r : ℕ} [NeZero r] {h : ℕ →*₀ ℂ} {sigma : ℂ}
    (M : ℂ) (Err K : ℝ)
    (hresidue : ∀ a : ZMod r,
      ‖EulerResidue.residueLSeries h a sigma - M‖ ≤ Err)
    (good : Finset (ZMod r))
    (classOf : ℕ → ZMod r → ZMod r) (A : ℕ → ZMod r → ℂ)
    (H : ℕ) (hH : 0 < H) (hM : 0 < ‖M‖)
    (hhalf : 2 * Err ≤ ‖M‖)
    (hweighted : ∀ H' ∈ Finset.Ioc H (2 * H),
      ‖eulerMappedResidueWeightedEnergy h sigma good (classOf H') (A H')‖ ≤
        K * ‖M‖ * (r : ℝ)) :
    (1 / ((r : ℝ) * H)) *
        ∑ H' ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good, Complex.normSq (A H' a) ≤ 2 * K := by
  have hr : (0 : ℝ) < r := by exact_mod_cast NeZero.pos r
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hgap : Err < ‖M‖ := by linarith
  have hone (H' : ℕ) (hH' : H' ∈ Finset.Ioc H (2 * H)) :
      ∑ a ∈ good, Complex.normSq (A H' a) ≤ 2 * K * (r : ℝ) := by
    have hraw := goodResidueEnergy_le_of_uniform_mappedResidueLSeries
      M Err hresidue good (classOf H') (A H')
      (K * ‖M‖ * (r : ℝ)) hgap (hweighted H' hH')
    have hT : 0 ≤ ∑ a ∈ good, Complex.normSq (A H' a) :=
      Finset.sum_nonneg fun a _ ↦ Complex.normSq_nonneg (A H' a)
    have hmul :
        (‖M‖ - Err) * (∑ a ∈ good, Complex.normSq (A H' a)) ≤
          K * ‖M‖ * (r : ℝ) := by
      simpa only [mul_comm] using (le_div_iff₀ (sub_pos.mpr hgap)).mp hraw
    have hden : ‖M‖ / 2 ≤ ‖M‖ - Err := by linarith
    have hmul' := (mul_le_mul_of_nonneg_right hden hT).trans hmul
    apply le_of_mul_le_mul_left _ hM
    nlinarith
  have hsum :
      (∑ H' ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good, Complex.normSq (A H' a)) ≤
        (H : ℝ) * (2 * K * (r : ℝ)) := by
    calc
      (∑ H' ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good, Complex.normSq (A H' a)) ≤
          ∑ _H' ∈ Finset.Ioc H (2 * H), 2 * K * (r : ℝ) := by
        apply Finset.sum_le_sum
        intro H' hH'
        exact hone H' hH'
      _ = (H : ℝ) * (2 * K * (r : ℝ)) := by
        have hcard : (Finset.Ioc H (2 * H)).card = H := by
          rw [Nat.card_Ioc]
          omega
        simp [hcard, nsmul_eq_mul]
  rw [one_div, inv_mul_eq_div, div_le_iff₀ (mul_pos hr hHR)]
  calc
    (∑ H' ∈ Finset.Ioc H (2 * H),
        ∑ a ∈ good, Complex.normSq (A H' a)) ≤
        (H : ℝ) * (2 * K * (r : ℝ)) := hsum
    _ = 2 * K * ((r : ℝ) * H) := by ring

/-- Scale-free form used by the BCC contradiction.  If the residue error is
at most half the main term and the grouped weighted energy is at most
`K * |M| * r`, then the normalized good-residue energy is at most `2K`.
The bound is independent of the modulus and of all later parameters. -/
theorem normalized_goodResidueEnergy_le_two_mul
    {r : ℕ} [NeZero r] {h : ℕ →*₀ ℂ}
    (hh : EulerResidue.HasUnitNorm h) {sigma : ℂ} (hsigma : 1 < sigma.re)
    (M : ℂ) (E₀ E K : ℝ)
    (hprincipal :
      ‖(r.totient : ℂ)⁻¹ * EulerResidue.principalTwistSeries h r sigma - M‖ ≤ E₀)
    (hnonprincipal : EulerResidue.NonprincipalTwistsBounded h r sigma E)
    (good : Finset (ZMod r)) (hgood : ∀ a ∈ good, IsUnit a)
    (A : ZMod r → ℂ) (hM : 0 < ‖M‖)
    (hhalf : 2 * eulerResidueError r E₀ E ≤ ‖M‖)
    (hweighted : ‖eulerResidueWeightedEnergy h sigma good A‖ ≤
      K * ‖M‖ * (r : ℝ)) :
    (1 / (r : ℝ)) * ∑ a ∈ good, Complex.normSq (A a) ≤ 2 * K := by
  have hgap : eulerResidueError r E₀ E < ‖M‖ := by linarith
  have hraw := goodResidueEnergy_le_of_eulerResidueLSeries hh hsigma M E₀ E
    hprincipal hnonprincipal good hgood A (K * ‖M‖ * (r : ℝ)) hgap hweighted
  have hden : ‖M‖ / 2 ≤ ‖M‖ - eulerResidueError r E₀ E := by linarith
  have hT : 0 ≤ ∑ a ∈ good, Complex.normSq (A a) :=
    Finset.sum_nonneg fun a _ ↦ Complex.normSq_nonneg (A a)
  have hmul :
      (‖M‖ - eulerResidueError r E₀ E) *
          (∑ a ∈ good, Complex.normSq (A a)) ≤
        K * ‖M‖ * (r : ℝ) := by
    simpa only [mul_comm] using (le_div_iff₀ (sub_pos.mpr hgap)).mp hraw
  have hmul' : ‖M‖ / 2 * (∑ a ∈ good, Complex.normSq (A a)) ≤
      K * ‖M‖ * (r : ℝ) :=
    (mul_le_mul_of_nonneg_right hden hT).trans hmul
  have hr : (0 : ℝ) < r := by exact_mod_cast NeZero.pos r
  rw [one_div, inv_mul_eq_div, div_le_iff₀ hr]
  have hcancel :
      ∑ a ∈ good, Complex.normSq (A a) ≤ 2 * K * (r : ℝ) := by
    apply le_of_mul_le_mul_left _ hM
    nlinarith
  simpa only [mul_assoc] using hcancel

/-- The medium-length average occurring in Tao's equation (17).  The
constant `2 * K` is independent of `H`, the modulus `r`, and (when
`r = q^k`) both `q` and `k`.  All Euler-series input is discharged by the
principal/nonprincipal theorem in `EulerResidue`. -/
theorem normalized_medium_goodResidueEnergy_le_two_mul
    {r : ℕ} [NeZero r] {h : ℕ →*₀ ℂ}
    (hh : EulerResidue.HasUnitNorm h) {sigma : ℂ} (hsigma : 1 < sigma.re)
    (M : ℂ) (E₀ E K : ℝ)
    (hprincipal :
      ‖(r.totient : ℂ)⁻¹ * EulerResidue.principalTwistSeries h r sigma - M‖ ≤ E₀)
    (hnonprincipal : EulerResidue.NonprincipalTwistsBounded h r sigma E)
    (good : Finset (ZMod r)) (hgood : ∀ a ∈ good, IsUnit a)
    (A : ℕ → ZMod r → ℂ) (H : ℕ) (hH : 0 < H) (hM : 0 < ‖M‖)
    (hhalf : 2 * eulerResidueError r E₀ E ≤ ‖M‖)
    (hweighted : ∀ H' ∈ Finset.Ioc H (2 * H),
      ‖eulerResidueWeightedEnergy h sigma good (A H')‖ ≤
        K * ‖M‖ * (r : ℝ)) :
    (1 / ((r : ℝ) * H)) *
        ∑ H' ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good, Complex.normSq (A H' a) ≤ 2 * K := by
  have hr : (0 : ℝ) < r := by exact_mod_cast NeZero.pos r
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hone (H' : ℕ) (hH' : H' ∈ Finset.Ioc H (2 * H)) :
      ∑ a ∈ good, Complex.normSq (A H' a) ≤ 2 * K * (r : ℝ) := by
    have hnormalized := normalized_goodResidueEnergy_le_two_mul hh hsigma M E₀ E K
      hprincipal hnonprincipal good hgood (A H') hM hhalf (hweighted H' hH')
    rw [one_div, inv_mul_eq_div, div_le_iff₀ hr] at hnormalized
    exact hnormalized
  have hsum :
      (∑ H' ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good, Complex.normSq (A H' a)) ≤
        (H : ℝ) * (2 * K * (r : ℝ)) := by
    calc
      (∑ H' ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good, Complex.normSq (A H' a)) ≤
          ∑ _H' ∈ Finset.Ioc H (2 * H), 2 * K * (r : ℝ) := by
        apply Finset.sum_le_sum
        intro H' hH'
        exact hone H' hH'
      _ = (H : ℝ) * (2 * K * (r : ℝ)) := by
        have hcard : (Finset.Ioc H (2 * H)).card = H := by
          rw [Nat.card_Ioc]
          omega
        simp [hcard, nsmul_eq_mul]
  rw [one_div, inv_mul_eq_div, div_le_iff₀ (mul_pos hr hHR)]
  calc
    (∑ H' ∈ Finset.Ioc H (2 * H),
        ∑ a ∈ good, Complex.normSq (A H' a)) ≤
        (H : ℝ) * (2 * K * (r : ℝ)) := hsum
    _ = 2 * K * ((r : ℝ) * H) := by ring

/-- Power-modulus specialization of
`normalized_medium_goodResidueEnergy_le_two_mul`.  This is the form consumed
when the generalized BCC argument fixes a conductor `q` and then lets `k`
and `H` grow.  The right-hand side contains neither `q`, `k`, nor `H`. -/
theorem normalized_medium_goodResidueEnergy_pow_le_two_mul
    {q : ℕ} [NeZero q] (k : ℕ) {h : ℕ →*₀ ℂ}
    (hh : EulerResidue.HasUnitNorm h) {sigma : ℂ} (hsigma : 1 < sigma.re)
    (M : ℂ) (E₀ E K : ℝ)
    (hprincipal :
      ‖((q ^ k).totient : ℂ)⁻¹ *
          EulerResidue.principalTwistSeries h (q ^ k) sigma - M‖ ≤ E₀)
    (hnonprincipal :
      EulerResidue.NonprincipalTwistsBounded h (q ^ k) sigma E)
    (good : Finset (ZMod (q ^ k))) (hgood : ∀ a ∈ good, IsUnit a)
    (A : ℕ → ZMod (q ^ k) → ℂ) (H : ℕ) (hH : 0 < H) (hM : 0 < ‖M‖)
    (hhalf : 2 * eulerResidueError (q ^ k) E₀ E ≤ ‖M‖)
    (hweighted : ∀ H' ∈ Finset.Ioc H (2 * H),
      ‖eulerResidueWeightedEnergy h sigma good (A H')‖ ≤
        K * ‖M‖ * ((q ^ k : ℕ) : ℝ)) :
    (1 / (((q ^ k : ℕ) : ℝ) * H)) *
        ∑ H' ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good, Complex.normSq (A H' a) ≤ 2 * K := by
  exact normalized_medium_goodResidueEnergy_le_two_mul hh hsigma M E₀ E K
    hprincipal hnonprincipal good hgood A H hH hM hhalf hweighted

/-! ## Correct nonunit good-residue endpoint -/

/-- Tao's actual good residues are not required to be units: they only
exclude divisibility of the shifted classes by a full prime power.  This
endpoint therefore uses `cyclicGoodResidues q k H` verbatim, permits an
arbitrary shifted class map, and discharges the uniform estimate through
the gcd-reduction theorem in `EulerResidue`.

The right side is the absolute constant `2*K`, independent of `H`, `q`,
and `k`. -/
theorem normalized_medium_cyclicGoodResidueEnergy_pow_le_two_mul
    {q : ℕ} [NeZero q] (k : ℕ) {h : ℕ →*₀ ℂ}
    (hh : EulerResidue.HasUnitNorm h) {sigma : ℂ} (hsigma : 1 < sigma.re)
    (Mdiv : ℕ → ℂ) (E₀ E Esc : ℕ → ℝ) (Main : ℂ) (Err K : ℝ)
    (hprincipal : ∀ t, t ∣ q ^ k → t ≠ 0 →
      ‖(t.totient : ℂ)⁻¹ *
          EulerResidue.principalTwistSeries h t sigma - Mdiv t‖ ≤ E₀ t)
    (hnonprincipal : ∀ t, t ∣ q ^ k → t ≠ 0 →
      EulerResidue.NonprincipalTwistsBounded h t sigma (E t))
    (hscale : ∀ d, d ∣ q ^ k → d ≠ 0 →
      ‖EulerResidue.residueScale h d sigma * Mdiv (q ^ k / d) - Main‖ ≤ Esc d)
    (hbudget : ∀ d, d ∣ q ^ k → d ≠ 0 →
      ‖EulerResidue.residueScale h d sigma‖ *
          eulerResidueError (q ^ k / d) (E₀ (q ^ k / d)) (E (q ^ k / d)) +
        Esc d ≤ Err)
    (classOf : ℕ → ZMod (q ^ k) → ZMod (q ^ k))
    (A : ℕ → ZMod (q ^ k) → ℂ) (H : ℕ) (hH : 0 < H)
    (hMain : 0 < ‖Main‖) (hhalf : 2 * Err ≤ ‖Main‖)
    (hweighted : ∀ H' ∈ Finset.Ioc H (2 * H),
      ‖eulerMappedResidueWeightedEnergy h sigma (cyclicGoodResidues q k H)
          (classOf H') (A H')‖ ≤
        K * ‖Main‖ * ((q ^ k : ℕ) : ℝ)) :
    (1 / (((q ^ k : ℕ) : ℝ) * H)) *
        ∑ H' ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ cyclicGoodResidues q k H,
            Complex.normSq (A H' a) ≤ 2 * K := by
  let U : ℕ → ℝ := fun t ↦ eulerResidueError t (E₀ t) (E t)
  have hunit : ∀ t, t ∣ q ^ k → t ≠ 0 →
      ∀ b : ZMod t, IsUnit b →
        ‖EulerResidue.residueLSeries h b sigma - Mdiv t‖ ≤ U t := by
    intro t ht ht0 b hb
    letI : NeZero t := ⟨ht0⟩
    simpa only [U, eulerResidueError] using
      EulerResidue.norm_residueLSeries_sub_main_le hh hsigma
        (Mdiv t) (E₀ t) (E t) (hprincipal t ht ht0)
          (hnonprincipal t ht ht0) hb
  have hresidue : ∀ a : ZMod (q ^ k),
      ‖EulerResidue.residueLSeries h a sigma - Main‖ ≤ Err := by
    apply EulerResidue.uniform_arbitrary_residue_estimate hh hsigma
      Mdiv U Esc Main Err
    · exact hunit
    · exact hscale
    · intro d hd hd0
      simpa only [U] using hbudget d hd hd0
  exact normalized_medium_mappedResidueEnergy_le_two_mul
    Main Err K hresidue (cyclicGoodResidues q k H) classOf A H hH
      hMain hhalf hweighted

/-- Normalized-main specialization of the preceding theorem.  Here the unit
estimate at modulus `t` is centered at `S/t`.  The assumption that `h` is
one on primes dividing `q` is propagated to every `d ∣ q^k`; consequently
the scaling error is derived, rather than assumed, from the explicit
`d^(1-sigma)-1` bound. -/
theorem normalized_medium_cyclicGoodResidueEnergy_pow_normalizedMain_le_two_mul
    {q : ℕ} [NeZero q] (k : ℕ) {h : ℕ →*₀ ℂ}
    (hh : EulerResidue.HasUnitNorm h) {sigma : ℂ} (hsigma : 1 < sigma.re)
    (S : ℂ) (E₀ E delta : ℕ → ℝ) (Err K : ℝ)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ q → h p = 1)
    (hprincipal : ∀ t, t ∣ q ^ k → t ≠ 0 →
      ‖(t.totient : ℂ)⁻¹ * EulerResidue.principalTwistSeries h t sigma -
          S / (t : ℂ)‖ ≤ E₀ t)
    (hnonprincipal : ∀ t, t ∣ q ^ k → t ≠ 0 →
      EulerResidue.NonprincipalTwistsBounded h t sigma (E t))
    (hfactor : ∀ d, d ∣ q ^ k → d ≠ 0 →
      ‖(d : ℂ) ^ (1 - sigma) - 1‖ ≤ delta d)
    (hbudget : ∀ d, d ∣ q ^ k → d ≠ 0 →
      ‖EulerResidue.residueScale h d sigma‖ *
          eulerResidueError (q ^ k / d) (E₀ (q ^ k / d)) (E (q ^ k / d)) +
        ‖S / ((q ^ k : ℕ) : ℂ)‖ * delta d ≤ Err)
    (classOf : ℕ → ZMod (q ^ k) → ZMod (q ^ k))
    (A : ℕ → ZMod (q ^ k) → ℂ) (H : ℕ) (hH : 0 < H)
    (hMain : 0 < ‖S / ((q ^ k : ℕ) : ℂ)‖)
    (hhalf : 2 * Err ≤ ‖S / ((q ^ k : ℕ) : ℂ)‖)
    (hweighted : ∀ H' ∈ Finset.Ioc H (2 * H),
      ‖eulerMappedResidueWeightedEnergy h sigma (cyclicGoodResidues q k H)
          (classOf H') (A H')‖ ≤
        K * ‖S / ((q ^ k : ℕ) : ℂ)‖ * ((q ^ k : ℕ) : ℝ)) :
    (1 / (((q ^ k : ℕ) : ℝ) * H)) *
        ∑ H' ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ cyclicGoodResidues q k H,
            Complex.normSq (A H' a) ≤ 2 * K := by
  let Main : ℂ := S / ((q ^ k : ℕ) : ℂ)
  let Mdiv : ℕ → ℂ := fun t ↦ S / (t : ℂ)
  let Esc : ℕ → ℝ := fun d ↦ ‖Main‖ * delta d
  have hscale : ∀ d, d ∣ q ^ k → d ≠ 0 →
      ‖EulerResidue.residueScale h d sigma * Mdiv (q ^ k / d) - Main‖ ≤ Esc d := by
    intro d hd hd0
    have hdone : h d = 1 :=
      EulerResidue.map_eq_one_of_dvd_pow (NeZero.ne q) hprime hd
    have heq := EulerResidue.residueScale_mul_div_reducedModulus
      hd (pow_ne_zero k (NeZero.ne q)) hdone sigma S
    dsimp only [Mdiv, Main, Esc]
    rw [heq]
    calc
      ‖S / ((q ^ k : ℕ) : ℂ) * (d : ℂ) ^ (1 - sigma) -
          S / ((q ^ k : ℕ) : ℂ)‖ =
          ‖(S / ((q ^ k : ℕ) : ℂ)) *
            ((d : ℂ) ^ (1 - sigma) - 1)‖ := by ring_nf
      _ = ‖S / ((q ^ k : ℕ) : ℂ)‖ *
          ‖(d : ℂ) ^ (1 - sigma) - 1‖ := norm_mul _ _
      _ ≤ ‖S / ((q ^ k : ℕ) : ℂ)‖ * delta d :=
        mul_le_mul_of_nonneg_left (hfactor d hd hd0) (norm_nonneg _)
  apply normalized_medium_cyclicGoodResidueEnergy_pow_le_two_mul
    k hh hsigma Mdiv E₀ E Esc Main Err K
  · intro t ht ht0
    simpa only [Mdiv] using hprincipal t ht ht0
  · exact hnonprincipal
  · exact hscale
  · intro d hd hd0
    simpa only [Esc, Main] using hbudget d hd hd0
  · exact hH
  · simpa only [Main] using hMain
  · simpa only [Main] using hhalf
  · intro H' hH'
    simpa only [Main] using hweighted H' hH'

end

end Erdos67
