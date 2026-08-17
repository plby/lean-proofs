/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.ActiveLcm
import ErdosProblems.Erdos297.FourierPhase
import ErdosProblems.Erdos297.GoodFactorization
import ErdosProblems.Erdos297.MajorArc
import ErdosProblems.Erdos297.NearbyMultiple
import ErdosProblems.Erdos297.WeightedFourier

/-!
# Minor arcs for Erdős Problem 297

This file formalizes the finite combinatorial core of the minor-arc argument
in Liu--Sawhney's local limit theorem.  For an integral frequency `h`,
`centeredResidue h n` is the representative of `h` modulo `n` obtained by
rounding `h / n` to the nearest integer.  The sets `nearbySet` and
`goodModuli` are the source's `U_q` and `D_h`.

The first half proves the product decay directly from the prime-power
incidence bound for good denominators.  The second half packages the
auxiliary-prime construction and proves the common-nearby-multiple and
frequency-counting steps.  All estimates are finite and contain their
rounding constants explicitly.
-/

open scoped BigOperators

namespace Erdos297.MinorArc

open Finset Real
open Erdos297.GoodFactorization
open Erdos297.MajorArc
open Erdos297.NearbyMultiple
open Erdos297.WeightedFourier

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The centered representative of the integral frequency `h` modulo `n`.
For the tie at a half-integer, it uses Mathlib's fixed `round` convention. -/
def centeredResidue (h : ℤ) (n : ℕ) : ℤ :=
  h - (n : ℤ) * round ((h : ℝ) / n)

/-- The absolute size of the centered residue, regarded as a real number. -/
def residueMagnitude (h : ℤ) (n : ℕ) : ℝ :=
  |(centeredResidue h n : ℝ)|

/-- Denominators in `A_q` whose centered residue lies in the interval of
radius `K / 2`.  This is the source's set `U_q`. -/
def nearbySet (A : Finset ℕ) (h : ℤ) (K q : ℕ) : Finset ℕ :=
  (divisiblePart A q).filter fun n ↦ residueMagnitude h n < (K : ℝ) / 2

/-- Denominators in `A_q` outside the central interval. -/
def farSet (A : Finset ℕ) (h : ℤ) (K q : ℕ) : Finset ℕ :=
  (divisiblePart A q).filter fun n ↦ (K : ℝ) / 2 ≤ residueMagnitude h n

/-- The source's set `D_h`, relative to a specified set of active prime
powers: the moduli for which fewer than `T` denominators in `A_q` have a far
centered residue. -/
def goodModuliOn (moduli : Finset ℕ) (A : Finset ℕ)
    (h : ℤ) (K T : ℕ) : Finset ℕ :=
  moduli.filter fun q ↦ (farSet A h K q).card < T

/-- The smooth-prime-power specialization.  The concrete local-limit theorem
uses `goodModuliOn` with the *active* prime powers of `A`; using all prime
powers up to `S` would introduce spurious zero modes. -/
def goodModuli (S : ℕ) (A : Finset ℕ) (h : ℤ) (K T : ℕ) : Finset ℕ :=
  goodModuliOn (smoothPrimePowers S) A h K T

@[simp] lemma mem_goodModuliOn {moduli A : Finset ℕ} {h : ℤ} {K T q : ℕ} :
    q ∈ goodModuliOn moduli A h K T ↔
      q ∈ moduli ∧ (farSet A h K q).card < T := by
  simp [goodModuliOn]

@[simp] lemma mem_nearbySet {A : Finset ℕ} {h : ℤ} {K q n : ℕ} :
    n ∈ nearbySet A h K q ↔
      n ∈ A ∧ q ∣ n ∧ residueMagnitude h n < (K : ℝ) / 2 := by
  simp [nearbySet, and_assoc]

@[simp] lemma mem_farSet {A : Finset ℕ} {h : ℤ} {K q n : ℕ} :
    n ∈ farSet A h K q ↔
      n ∈ A ∧ q ∣ n ∧ (K : ℝ) / 2 ≤ residueMagnitude h n := by
  simp [farSet, and_assoc]

@[simp] lemma mem_goodModuli {S : ℕ} {A : Finset ℕ} {h : ℤ} {K T q : ℕ} :
    q ∈ goodModuli S A h K T ↔
      q ∈ smoothPrimePowers S ∧ (farSet A h K q).card < T := by
  simp [goodModuli]

lemma nearbySet_subset_divisiblePart (A : Finset ℕ) (h : ℤ) (K q : ℕ) :
    nearbySet A h K q ⊆ divisiblePart A q :=
  filter_subset _ _

lemma farSet_subset_divisiblePart (A : Finset ℕ) (h : ℤ) (K q : ℕ) :
    farSet A h K q ⊆ divisiblePart A q :=
  filter_subset _ _

lemma farSet_eq_sdiff_nearbySet (A : Finset ℕ) (h : ℤ) (K q : ℕ) :
    farSet A h K q = divisiblePart A q \ nearbySet A h K q := by
  ext n
  simp only [mem_farSet, mem_sdiff, mem_divisiblePart, mem_nearbySet]
  constructor
  · rintro ⟨hnA, hqn, hfar⟩
    exact ⟨⟨hnA, hqn⟩, fun hnear ↦ (not_lt_of_ge hfar) hnear.2.2⟩
  · rintro ⟨⟨hnA, hqn⟩, hnear⟩
    exact ⟨hnA, hqn, not_lt.mp (fun hlt ↦ hnear ⟨hnA, hqn, hlt⟩)⟩

lemma goodModuli_subset_smoothPrimePowers (S : ℕ) (A : Finset ℕ)
    (h : ℤ) (K T : ℕ) :
    goodModuli S A h K T ⊆ smoothPrimePowers S :=
  filter_subset _ _

lemma card_farSet_ge_of_not_mem_goodModuli
    {moduli : Finset ℕ} {A : Finset ℕ} {h : ℤ} {K T q : ℕ}
    (hqS : q ∈ moduli)
    (hq : q ∉ goodModuliOn moduli A h K T) :
    T ≤ (farSet A h K q).card := by
  simp only [goodModuliOn, mem_filter, hqS, true_and, not_lt] at hq
  exact hq

/-! ## Residue geometry -/

lemma circleDistance_int_div_nat {h : ℤ} {n : ℕ} (hn : 0 < n) :
    circleDistance ((h : ℝ) / n) = residueMagnitude h n / n := by
  rw [circleDistance_eq_round]
  unfold residueMagnitude centeredResidue
  rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [show (h : ℝ) / n - round ((h : ℝ) / n) =
      ((h : ℝ) - n * round ((h : ℝ) / n)) / n by field_simp]
  rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ))]

lemma circleDistance_ge_of_mem_farSet
    {A : Finset ℕ} {h : ℤ} {K q n N : ℕ}
    (hn : n ∈ farSet A h K q) (hnN : n ≤ N) (hn0 : 0 < n) :
    (K : ℝ) / (2 * N) ≤ circleDistance ((h : ℝ) / n) := by
  rw [circleDistance_int_div_nat hn0]
  have hfar : (K : ℝ) / 2 ≤ residueMagnitude h n :=
    (mem_farSet.mp hn).2.2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hNR : (n : ℝ) ≤ N := by exact_mod_cast hnN
  by_cases hK : K = 0
  · rw [hK, Nat.cast_zero, zero_div]
    exact div_nonneg (abs_nonneg (centeredResidue h n : ℝ)) (Nat.cast_nonneg n)
  · have hN : 0 < N := lt_of_lt_of_le hn0 hnN
    have hNR' : (0 : ℝ) < N := by exact_mod_cast hN
    calc
      (K : ℝ) / (2 * N) ≤ (K : ℝ) / (2 * n) := by
        gcongr
      _ = ((K : ℝ) / 2) / n := by ring
      _ ≤ residueMagnitude h n / n := (div_le_div_iff_of_pos_right hnR).2 hfar

/-! ## Incidence-weighted product decay -/

/-- Counting far incidences in the two orders. -/
lemma sum_card_farSet_comm (S : ℕ) (A : Finset ℕ) (h : ℤ) (K : ℕ)
    (hA0 : ∀ n ∈ A, n ≠ 0) :
    ∑ q ∈ smoothPrimePowers S, (farSet A h K q).card =
      ∑ n ∈ A, (primePowerDivisors n ∩ smoothPrimePowers S).card *
        (if (K : ℝ) / 2 ≤ residueMagnitude h n then 1 else 0) := by
  calc
    ∑ q ∈ smoothPrimePowers S, (farSet A h K q).card =
        ∑ q ∈ smoothPrimePowers S, ∑ n ∈ A,
          if q ∣ n ∧ (K : ℝ) / 2 ≤ residueMagnitude h n then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [show farSet A h K q =
          A.filter fun n ↦ q ∣ n ∧ (K : ℝ) / 2 ≤ residueMagnitude h n by
        ext n
        simp [farSet, divisiblePart, and_assoc]]
      simp
    _ = ∑ n ∈ A, ∑ q ∈ smoothPrimePowers S,
          if q ∣ n ∧ (K : ℝ) / 2 ≤ residueMagnitude h n then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ A, (primePowerDivisors n ∩ smoothPrimePowers S).card *
          (if (K : ℝ) / 2 ≤ residueMagnitude h n then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 := hA0 n hn
      by_cases hfar : (K : ℝ) / 2 ≤ residueMagnitude h n
      · simp only [hfar, and_true, if_true, mul_one]
        rw [Finset.sum_boole]
        apply congrArg Finset.card
        ext q
        rw [mem_filter, mem_inter, mem_primePowerDivisors hn0,
          Erdos285.PrimePowers.mem_primePowersUpTo]
        aesop
      · simp [hfar]

/-- The sum of the squared circle distances dominates the number of bad
prime-power incidences.  `F` is the multiplicity budget for each member of
`A`. -/
lemma bad_moduli_mul_distance_sq_le
    {N S K T F : ℕ} {moduli A : Finset ℕ} {h : ℤ}
    (hmoduli : moduli ⊆ smoothPrimePowers S)
    (hA0 : ∀ n ∈ A, 0 < n) (hAN : ∀ n ∈ A, n ≤ N)
    (hfac : ∀ n ∈ A, (primePowerDivisors n).card ≤ F) :
    ((moduli \ goodModuliOn moduli A h K T).card * T : ℕ) *
        (((K : ℝ) / (2 * N)) ^ 2) ≤
      F * ∑ n ∈ A, circleDistance ((h : ℝ) / n) ^ 2 := by
  have hbadCard :
      (moduli \ goodModuliOn moduli A h K T).card * T ≤
        ∑ q ∈ smoothPrimePowers S, (farSet A h K q).card := by
    calc
      (moduli \ goodModuliOn moduli A h K T).card * T =
          ∑ q ∈ moduli \ goodModuliOn moduli A h K T, T := by simp
      _ ≤ ∑ q ∈ moduli \ goodModuliOn moduli A h K T,
          (farSet A h K q).card := by
        apply Finset.sum_le_sum
        intro q hq
        exact card_farSet_ge_of_not_mem_goodModuli
          (mem_sdiff.mp hq).1 (mem_sdiff.mp hq).2
      _ ≤ ∑ q ∈ smoothPrimePowers S, (farSet A h K q).card := by
        exact sum_le_sum_of_subset_of_nonneg
          (sdiff_subset.trans hmoduli)
          (fun _ _ _ ↦ Nat.zero_le _)
  have hweighted :
      (↑(∑ q ∈ smoothPrimePowers S, (farSet A h K q).card) : ℝ) *
          (((K : ℝ) / (2 * N)) ^ 2) ≤
        F * ∑ n ∈ A, circleDistance ((h : ℝ) / n) ^ 2 := by
    rw [sum_card_farSet_comm S A h K (fun n hn ↦ (hA0 n hn).ne')]
    push_cast
    rw [Finset.sum_mul]
    calc
      ∑ n ∈ A,
          ((↑((primePowerDivisors n ∩ smoothPrimePowers S).card) : ℝ) *
            (if (K : ℝ) / 2 ≤ residueMagnitude h n then 1 else 0)) *
            ((K : ℝ) / (2 * N)) ^ 2 ≤
          ∑ n ∈ A, (F : ℝ) * circleDistance ((h : ℝ) / n) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hfar : (K : ℝ) / 2 ≤ residueMagnitude h n
        · simp only [hfar, if_true, mul_one]
          have hcard : (primePowerDivisors n ∩ smoothPrimePowers S).card ≤ F :=
            (card_le_card inter_subset_left).trans (hfac n hn)
          have hcircle := circleDistance_ge_of_mem_farSet
            (A := A) (q := 1) (N := N)
            (mem_farSet.mpr ⟨hn, one_dvd n, hfar⟩) (hAN n hn) (hA0 n hn)
          have hsq := sq_le_sq₀ (by positivity : 0 ≤ (K : ℝ) / (2 * N))
            (circleDistance_nonneg _) |>.2 hcircle
          exact mul_le_mul (by exact_mod_cast hcard) hsq (sq_nonneg _) (by positivity)
        · rw [if_neg hfar]
          norm_num
          positivity
      _ = F * ∑ n ∈ A, circleDistance ((h : ℝ) / n) ^ 2 := by
        rw [Finset.mul_sum]
  have hcast :
      (((moduli \ goodModuliOn moduli A h K T).card * T : ℕ) : ℝ) ≤
        (∑ q ∈ smoothPrimePowers S, (farSet A h K q).card : ℕ) := by
    exact_mod_cast hbadCard
  exact (mul_le_mul_of_nonneg_right hcast (sq_nonneg _)).trans hweighted

/-- Product decay in the exact exponential form needed before choosing the
source's numerical constants. -/
theorem phaseProduct_decay
    {N M S K T F : ℕ} {moduli A : Finset ℕ} {p : ℕ → ℝ}
    {h : ℤ} {delta : ℝ}
    (hM : 1 ≤ M) (hA : A ⊆ goodDenominators N M S)
    (hmoduli : moduli ⊆ smoothPrimePowers S)
    (hpLower : ∀ n ∈ A, delta ≤ p n)
    (hpUpper : ∀ n ∈ A, p n ≤ 1 / 2)
    (hfactor : factorBound N ≤ F) (hF : 0 < F) (hdelta : 0 ≤ delta) :
    ‖∏ n ∈ A, bernoulliFactor (p n) ((h : ℝ) / n)‖ ≤
      Real.exp (-(4 * delta / F *
        ((moduli \ goodModuliOn moduli A h K T).card * T : ℕ) *
          ((K : ℝ) / (2 * N)) ^ 2)) := by
  have hp0 : ∀ n ∈ A, 0 ≤ p n := fun n hn ↦ hdelta.trans (hpLower n hn)
  have hp1 : ∀ n ∈ A, p n ≤ 1 := fun n hn ↦ (hpUpper n hn).trans (by norm_num)
  have hbase := bernoulliFactor_prod_norm_le_exp A p
    (fun n ↦ (h : ℝ) / n) hp0 hp1
  have hinc := bad_moduli_mul_distance_sq_le
    (N := N) (S := S) (K := K) (T := T) (F := F) (moduli := moduli)
    (A := A) (h := h) hmoduli
    (fun n hn ↦ goodDenominator_pos hM (hA hn))
    (fun n hn ↦ (mem_goodDenominators.mp (hA hn)).2.1)
    (fun n hn ↦ by
      rw [card_primePowerDivisors (goodDenominator_pos hM (hA hn)).ne']
      exact (goodDenominator_factorBound (hA hn)).trans hfactor)
  apply hbase.trans
  apply Real.exp_le_exp.mpr
  have hFreal : (0 : ℝ) < F := by exact_mod_cast hF
  calc
    -(8 * ∑ n ∈ A, p n * (1 - p n) *
        circleDistance ((h : ℝ) / n) ^ 2) ≤
        -(4 * delta * ∑ n ∈ A,
          circleDistance ((h : ℝ) / n) ^ 2) := by
      apply neg_le_neg
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      have hhalf : (1 : ℝ) / 2 ≤ 1 - p n := by linarith [hpUpper n hn]
      have hlower := hpLower n hn
      have hd : 0 ≤ circleDistance ((h : ℝ) / n) ^ 2 := sq_nonneg _
      have hprod : delta * ((1 : ℝ) / 2) ≤ p n * (1 - p n) :=
        mul_le_mul hlower hhalf (by norm_num) (hp0 n hn)
      have hcoeff : 4 * delta ≤ 8 * p n * (1 - p n) := by nlinarith [hprod]
      convert mul_le_mul_of_nonneg_right hcoeff hd using 1 <;> ring
    _ ≤ -(4 * delta / F *
        ((moduli \ goodModuliOn moduli A h K T).card * T : ℕ) *
          ((K : ℝ) / (2 * N)) ^ 2) := by
      apply neg_le_neg
      calc
        4 * delta / F *
            (((moduli \ goodModuliOn moduli A h K T).card * T : ℕ) : ℝ) *
              ((K : ℝ) / (2 * N)) ^ 2 =
            (4 * delta / F) *
              ((((moduli \ goodModuliOn moduli A h K T).card * T : ℕ) : ℝ) *
                ((K : ℝ) / (2 * N)) ^ 2) := by ring
        _ ≤ (4 * delta / F) *
              (F * ∑ n ∈ A, circleDistance ((h : ℝ) / n) ^ 2) := by
          gcongr
        _ = 4 * delta * ∑ n ∈ A,
              circleDistance ((h : ℝ) / n) ^ 2 := by
          field_simp

lemma exp_neg_ten_log_mul_eq {N s : ℕ} (hN : 0 < N) :
    Real.exp (-(10 * Real.log (N : ℝ) * s)) =
      1 / (N : ℝ) ^ (10 * s) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  rw [show -(10 * Real.log (N : ℝ) * s) =
      -(Real.log (N : ℝ) * (10 * s : ℕ)) by push_cast; ring]
  rw [Real.exp_neg, ← Real.rpow_def_of_pos hNreal, Real.rpow_natCast]
  simp [div_eq_mul_inv]

/-- A per-omitted-factor exponential rate of at least `10 log N` is exactly
the polynomial decay `N^(-10s)` used in the fixed-`D` sum. -/
lemma exp_decay_to_power {N s : ℕ} {c : ℝ} (hN : 0 < N)
    (hc : 10 * Real.log (N : ℝ) ≤ c) :
    Real.exp (-(c * s)) ≤ 1 / (N : ℝ) ^ (10 * s) := by
  rw [← exp_neg_ten_log_mul_eq hN]
  apply Real.exp_le_exp.mpr
  have hs : (0 : ℝ) ≤ s := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hc hs]

/-! ## Cleared reciprocal characters -/

lemma bernoulliFactor_norm_neg (p x : ℝ) :
    ‖bernoulliFactor p (-x)‖ = ‖bernoulliFactor p x‖ := by
  have hsquares : ‖bernoulliFactor p (-x)‖ ^ 2 = ‖bernoulliFactor p x‖ ^ 2 := by
    rw [bernoulliFactor_norm_sq, bernoulliFactor_norm_sq]
    rw [show 2 * Real.pi * -x = -(2 * Real.pi * x) by ring, Real.cos_neg]
  nlinarith [norm_nonneg (bernoulliFactor p (-x)),
    norm_nonneg (bernoulliFactor p x)]

/-- The norm of the reciprocal phase product is even in its integral
frequency.  This lets the arithmetic construction use the balanced
representative itself, while the DFT coefficient naturally contains its
negative. -/
lemma phaseProduct_norm_neg (A : Finset ℕ) (p : ℕ → ℝ) (h : ℤ) :
    ‖∏ n ∈ A, bernoulliFactor (p n) (-(h : ℝ) / n)‖ =
      ‖∏ n ∈ A, bernoulliFactor (p n) ((h : ℝ) / n)‖ := by
  rw [norm_prod, norm_prod]
  apply Finset.prod_congr rfl
  intro n hn
  rw [show -(h : ℝ) / n = -((h : ℝ) / n) by ring]
  exact bernoulliFactor_norm_neg _ _

/-- At the active LCM, the finite Fourier coefficient is exactly the real
reciprocal phase product used in `phaseProduct_decay`. -/
lemma coefficient_eq_phaseProduct
    {Q : ℕ} [NeZero Q] {A : Finset ℕ} {p : ℕ → ℝ}
    (hpos : ∀ n ∈ A, 0 < n) (hdiv : ∀ n ∈ A, n ∣ Q) (h : ZMod Q) :
    coefficient A (fun n ↦ (Q / n : ZMod Q)) p h =
      ∏ n ∈ A, bernoulliFactor (p n) (-(h.valMinAbs : ℝ) / n) := by
  unfold coefficient
  apply Finset.prod_congr rfl
  intro n hn
  rw [stdAddChar_clearedReciprocal (hpos n hn) (hdiv n hn)]
  unfold bernoulliFactor fourierPhase reciprocalAngle
  congr 2
  congr 1
  push_cast
  ring

/-- Source-ready pointwise minor coefficient estimate.  The arithmetic
incidence argument supplies the omitted-factor count, while `hrate` is the
single scalar inequality verified from the chosen threshold. -/
theorem coefficient_norm_le_power
    {Q N M S K T F : ℕ} [NeZero Q]
    {moduli A : Finset ℕ} {p : ℕ → ℝ} {delta : ℝ}
    (hM : 1 ≤ M) (hA : A ⊆ goodDenominators N M S)
    (hmoduli : moduli ⊆ smoothPrimePowers S)
    (hpLower : ∀ n ∈ A, delta ≤ p n)
    (hpUpper : ∀ n ∈ A, p n ≤ 1 / 2)
    (hfactor : factorBound N ≤ F) (hF : 0 < F) (hdelta : 0 ≤ delta)
    (hdiv : ∀ n ∈ A, n ∣ Q)
    (hN : 0 < N)
    (hrate : 10 * Real.log (N : ℝ) ≤
      4 * delta / F * T * ((K : ℝ) / (2 * N)) ^ 2)
    (h : ZMod Q) :
    ‖coefficient A (fun n ↦ (Q / n : ZMod Q)) p h‖ ≤
      1 / (N : ℝ) ^
        (10 * (moduli \ goodModuliOn moduli A h.valMinAbs K T).card) := by
  have hpos : ∀ n ∈ A, 0 < n := fun n hn ↦
    goodDenominator_pos hM (hA hn)
  rw [coefficient_eq_phaseProduct hpos hdiv,
    phaseProduct_norm_neg A p h.valMinAbs]
  have hphase := phaseProduct_decay (N := N) (M := M) (S := S)
    (K := K) (T := T) (F := F) (moduli := moduli) (A := A)
    (p := p) (h := h.valMinAbs) hM hA hmoduli hpLower hpUpper
    hfactor hF hdelta
  apply hphase.trans
  let s := (moduli \ goodModuliOn moduli A h.valMinAbs K T).card
  have hpower := exp_decay_to_power (s := s) hN hrate
  calc
    Real.exp (-(4 * delta / F *
        ((moduli \ goodModuliOn moduli A h.valMinAbs K T).card * T : ℕ) *
          ((K : ℝ) / (2 * N)) ^ 2)) =
        Real.exp (-(4 * delta / F * T * ((K : ℝ) / (2 * N)) ^ 2 * s)) := by
      congr 1
      dsimp [s]
      push_cast
      ring
    _ ≤ 1 / (N : ℝ) ^ (10 * s) := hpower
    _ = 1 / (N : ℝ) ^
        (10 * (moduli \ goodModuliOn moduli A h.valMinAbs K T).card) := by
      rfl

/-- Character factors have norm one, so a block is bounded by the sum of
the norms of its Bernoulli coefficients, uniformly in the target residue. -/
lemma norm_fourierBlock_le_sum
    {Q : ℕ} [NeZero Q] (H : Finset (ZMod Q)) (A : Finset ℕ)
    (p : ℕ → ℝ) (target : ZMod Q) :
    ‖fourierBlock H A (fun n ↦ (Q / n : ZMod Q)) p target‖ ≤
      ∑ h ∈ H, ‖coefficient A (fun n ↦ (Q / n : ZMod Q)) p h‖ := by
  unfold fourierBlock
  calc
    ‖∑ h ∈ H, ZMod.stdAddChar (h * target) *
        coefficient A (fun n ↦ (Q / n : ZMod Q)) p h‖ ≤
        ∑ h ∈ H, ‖ZMod.stdAddChar (h * target) *
          coefficient A (fun n ↦ (Q / n : ZMod Q)) p h‖ := by
      simpa using norm_sum_le H
        (fun h ↦ ZMod.stdAddChar (h * target) *
          coefficient A (fun n ↦ (Q / n : ZMod Q)) p h)
    _ = _ := by
      apply sum_congr rfl
      intro h hh
      rw [norm_mul, AddChar.norm_apply, one_mul]

/-- The active-LCM minor-frequency block for the normalized logistic source
measure, with exactly the same set, step, weight and target as
`MajorArc.normalizedMajorBlock`. -/
noncomputable def normalizedMinorBlock (lam : ℝ) (N : ℕ) : ℂ := by
  let A := Erdos297.LogisticNormalization.goodSet N
  let Q := Erdos297.ActiveLcm.activeLcm A
  letI : NeZero Q := ⟨Erdos297.ActiveLcm.activeLcm_ne_zero A⟩
  exact fourierBlock (minorFrequencies Q (M N)) A
    (fun n ↦ (Q / n : ZMod Q))
    (Erdos297.LogisticNormalization.normalizedLogisticProbability lam N)
    (Q : ZMod Q)

/-! ## Common nearby multiple -/

/-- Finite data produced by the auxiliary-prime sieve for one frequency.
The structure records only the output used after the sieve has run. -/
structure AuxiliaryData (indices : Finset ℕ) (lower upper : ℤ) (N : ℕ) where
  chosen : ℕ → ℤ
  primes : Finset ℕ
  aux : ℕ → Finset ℕ
  intervalExists : ∃ z : ℤ, InHalfOpenInterval lower upper z
  width : upper - lower ≤ (N : ℤ)
  chosen_mem : ∀ q ∈ indices, InHalfOpenInterval lower upper (chosen q)
  modulus_dvd : ∀ q ∈ indices, (q : ℤ) ∣ chosen q
  aux_subset : ∀ q ∈ indices, aux q ⊆ primes
  aux_dense : ∀ q ∈ indices, 9 * primes.card ≤ 10 * (aux q).card
  aux_prod_dvd : ∀ q ∈ indices, (((aux q).prod id : ℕ) : ℤ) ∣ chosen q
  large_product : ∀ block ⊆ primes,
    4 * primes.card ≤ 5 * block.card → N < block.prod id

/-- The auxiliary-prime output gives a single nearby multiple of the LCM of
all moduli in `D_h`. -/
theorem commonNearbyMultiple_of_auxiliaryData
    {indices : Finset ℕ} {lower upper : ℤ} {N : ℕ}
    (data : AuxiliaryData indices lower upper N) :
    ∃ z : ℤ, InHalfOpenInterval lower upper z ∧
      (∀ q ∈ indices, (q : ℤ) ∣ z) ∧
      ((indices.lcm id : ℕ) : ℤ) ∣ z := by
  exact common_nearby_multiple indices id lower upper N data.chosen data.primes data.aux
    data.intervalExists data.width data.chosen_mem data.modulus_dvd data.aux_subset
    data.aux_dense data.aux_prod_dvd data.large_product

/-! ## Frequency fibers -/

/-- Integer frequencies in a half-open complete interval `(lower, upper]`. -/
def integerInterval (lower upper : ℤ) : Finset ℤ :=
  Finset.Ioc lower upper

@[simp] lemma mem_integerInterval {lower upper h : ℤ} :
    h ∈ integerInterval lower upper ↔ InHalfOpenInterval lower upper h := by
  simp [integerInterval, InHalfOpenInterval]

/-- A residue class modulo `L` occurs at most `Q / L + 1` times in an
integer interval of length at most `Q`. -/
lemma card_Ioc_filter_dvd_le {lower upper : ℤ} {Q L : ℕ} (hL : 0 < L)
    (hwidth : upper - lower ≤ (Q : ℤ)) :
    ((Finset.Ioc lower upper).filter fun x ↦ (L : ℤ) ∣ x).card ≤ Q / L + 1 := by
  have hLR : (0 : ℚ) < L := by exact_mod_cast hL
  let fb : ℤ := ⌊(upper : ℚ) / (L : ℚ)⌋
  let fa : ℤ := ⌊(lower : ℚ) / (L : ℚ)⌋
  have hb : (fb : ℚ) ≤ (upper : ℚ) / L := Int.floor_le _
  have ha : (lower : ℚ) / L < (fa : ℚ) + 1 := Int.lt_floor_add_one _
  have hw : (upper : ℚ) - lower ≤ Q := by exact_mod_cast hwidth
  have hdiv : ((upper : ℚ) - lower) / L ≤ (Q : ℚ) / L :=
    div_le_div_of_nonneg_right hw hLR.le
  have hsubdiv : ((upper : ℚ) - lower) / L =
      (upper : ℚ) / L - (lower : ℚ) / L := by ring
  have hq : (Q : ℚ) / L < ((Q / L : ℕ) : ℚ) + 1 := by
    rw [div_lt_iff₀ hLR]
    have hnat := Nat.lt_mul_div_succ Q hL
    exact_mod_cast (show Q < (Q / L + 1) * L by simpa [mul_comm] using hnat)
  have hstrict : fb - fa < ((Q / L : ℕ) : ℤ) + 2 := by
    have hr : (fb : ℚ) - fa < ((Q / L : ℕ) : ℚ) + 2 := by
      rw [hsubdiv] at hdiv
      linarith
    have hr' : fb - fa < ((Q / L + 2 : ℕ) : ℤ) := by
      apply (Int.cast_lt (R := ℚ)).mp
      calc
        ((fb - fa : ℤ) : ℚ) = (fb : ℚ) - fa := by rw [Int.cast_sub]
        _ < ((Q / L : ℕ) : ℚ) + 2 := hr
        _ = (((Q / L + 2 : ℕ) : ℤ) : ℚ) := by push_cast; rfl
    simpa using hr'
  have hmax : max (fb - fa) 0 ≤ ((Q / L + 1 : ℕ) : ℤ) := by
    rw [max_le_iff]
    constructor
    · norm_num [Nat.cast_add, Nat.cast_one] at hstrict ⊢
      omega
    · positivity
  have hcard := Int.Ioc_filter_dvd_card lower upper
    (r := (L : ℤ)) (by exact_mod_cast hL)
  have hcInt :
      (↑((Finset.Ioc lower upper).filter fun x ↦ (L : ℤ) ∣ x).card : ℤ) ≤
        ((Q / L + 1 : ℕ) : ℤ) := hcard.trans_le hmax
  exact_mod_cast hcInt

/-- The same count for a translated residue class. -/
lemma card_Ioc_filter_add_dvd_le {lower upper d : ℤ} {Q L : ℕ} (hL : 0 < L)
    (hwidth : upper - lower ≤ (Q : ℤ)) :
    ((Finset.Ioc lower upper).filter fun x ↦ (L : ℤ) ∣ x + d).card ≤
      Q / L + 1 := by
  have heq :
      ((Finset.Ioc lower upper).filter fun x ↦ (L : ℤ) ∣ x + d) =
        ((Finset.Ioc lower upper).filter fun x ↦ x ≡ -d [ZMOD (L : ℤ)]) := by
    ext x
    simp only [mem_filter, mem_Ioc, and_congr_right_iff]
    intro hx
    rw [Int.modEq_iff_dvd]
    constructor
    · intro hdvd
      simpa [sub_eq_add_neg, add_comm] using (dvd_neg.mpr hdvd)
    · intro hdvd
      have hneg : (L : ℤ) ∣ -(x + d) := by
        simpa [sub_eq_add_neg, add_comm] using hdvd
      exact dvd_neg.mp hneg
  rw [heq, Int.Ioc_filter_modEq_eq, card_map]
  apply card_Ioc_filter_dvd_le hL
  omega

/-- A frequency whose radius-`K/2` neighborhood contains a multiple of `L`
can be encoded by that multiple and its displacement. -/
def nearbyMultiplePair (K L : ℕ) (h : ℤ) : Prop :=
  ∃ x : ℤ, (L : ℤ) ∣ x ∧ |x - h| ≤ (K : ℤ)

/-- Direct bridge from an auxiliary-supply certificate to the predicate used
by fixed-fiber counting.  Endpoint rounding is isolated in `hwindow`. -/
lemma nearbyMultiplePair_lcm_of_auxiliaryData
    {indices : Finset ℕ} {lower upper h : ℤ} {N K : ℕ}
    (data : AuxiliaryData indices lower upper N)
    (hwindow : ∀ z, InHalfOpenInterval lower upper z → |z - h| ≤ (K : ℤ)) :
    nearbyMultiplePair K (indices.lcm id) h := by
  obtain ⟨z, hzI, _hzq, hzL⟩ := commonNearbyMultiple_of_auxiliaryData data
  exact ⟨z, hzL, hwindow z hzI⟩

/-- The `2K+1` possible integral displacements from a frequency to a nearby
multiple.  The source uses a radius `K/2`, giving `K+1`; this symmetric
enlargement is convenient and remains more than sufficient numerically. -/
noncomputable def frequencyOffsets (K : ℕ) : Finset ℤ :=
  Finset.Icc (-(K : ℤ)) K

@[simp] lemma card_frequencyOffsets (K : ℕ) :
    (frequencyOffsets K).card = 2 * K + 1 := by
  simp [frequencyOffsets]
  omega

/-- Sharp fixed-fiber frequency count.  A frequency admitting a multiple of
`L` within distance `K` lies in one of `2K+1` residue classes modulo `L`. -/
theorem card_filter_nearbyMultiplePair_le
    {lower upper : ℤ} {Q K L : ℕ} (hL : 0 < L)
    (hwidth : upper - lower ≤ (Q : ℤ)) :
    ((integerInterval lower upper).filter (nearbyMultiplePair K L)).card ≤
      (2 * K + 1) * (Q / L + 1) := by
  let fibers : ℤ → Finset ℤ := fun d ↦
    (Finset.Ioc lower upper).filter fun h ↦ (L : ℤ) ∣ h + d
  have hsub :
      ((integerInterval lower upper).filter (nearbyMultiplePair K L)) ⊆
        (frequencyOffsets K).biUnion fibers := by
    intro h hh
    rw [mem_filter] at hh
    obtain ⟨x, hLx, hdist⟩ := hh.2
    let d := x - h
    rw [mem_biUnion]
    refine ⟨d, ?_, ?_⟩
    · rw [frequencyOffsets, mem_Icc]
      exact abs_le.mp (by simpa [d] using hdist)
    · rw [mem_filter]
      refine ⟨hh.1, ?_⟩
      simpa [d] using hLx
  calc
    ((integerInterval lower upper).filter (nearbyMultiplePair K L)).card ≤
        ((frequencyOffsets K).biUnion fibers).card := card_le_card hsub
    _ ≤ ∑ d ∈ frequencyOffsets K, (fibers d).card := Finset.card_biUnion_le
    _ ≤ ∑ _d ∈ frequencyOffsets K, (Q / L + 1) := by
      apply sum_le_sum
      intro d hd
      exact card_Ioc_filter_add_dvd_le hL hwidth
    _ = (2 * K + 1) * (Q / L + 1) := by simp

/-- The length-`Q` interval containing the balanced representatives of
`ZMod Q`.  For odd `Q` it is `[-⌊Q/2⌋,⌊Q/2⌋]`; for even `Q` the
negative endpoint is omitted and the positive endpoint included. -/
noncomputable def balancedIntegerInterval (Q : ℕ) : Finset ℤ :=
  Finset.Ioc ((-(Q : ℤ)) / 2) ((Q : ℤ) / 2)

lemma valMinAbs_mem_balancedIntegerInterval {Q : ℕ} [NeZero Q] (h : ZMod Q) :
    h.valMinAbs ∈ balancedIntegerInterval Q := by
  rw [balancedIntegerInterval, Finset.mem_Ioc]
  have hm := h.valMinAbs_mem_Ioc
  constructor
  · rw [Int.ediv_lt_iff_lt_mul (by norm_num)]
    simpa [mul_comm] using hm.1
  · rw [Int.le_ediv_iff_mul_le (by norm_num)]
    simpa [mul_comm] using hm.2

lemma balancedIntegerInterval_width (Q : ℕ) :
    (Q : ℤ) / 2 - (-(Q : ℤ)) / 2 ≤ (Q : ℤ) := by
  omega

/-- Fixed-nearby-multiple counting directly on a finite Fourier group.  The
injective balanced representative loses no frequencies and the ambient
integer interval has exactly the modulus length. -/
theorem card_filter_zmod_nearbyMultiplePair_le
    {Q K L : ℕ} [NeZero Q] (H : Finset (ZMod Q)) (hL : 0 < L) :
    (H.filter fun h ↦ nearbyMultiplePair K L h.valMinAbs).card ≤
      (2 * K + 1) * (Q / L + 1) := by
  let source := H.filter fun h ↦ nearbyMultiplePair K L h.valMinAbs
  let target := (balancedIntegerInterval Q).filter (nearbyMultiplePair K L)
  have hmap : Set.MapsTo (fun h : ZMod Q ↦ h.valMinAbs) source target := by
    intro h hh
    rw [Finset.coe_filter, Set.mem_ofPred_eq] at hh
    change h.valMinAbs ∈ target
    rw [Finset.mem_filter]
    exact ⟨valMinAbs_mem_balancedIntegerInterval h, hh.2⟩
  have hcard : source.card ≤ target.card :=
    Finset.card_le_card_of_injOn (fun h : ZMod Q ↦ h.valMinAbs) hmap
      ZMod.injective_valMinAbs.injOn
  exact hcard.trans
    (card_filter_nearbyMultiplePair_le hL (balancedIntegerInterval_width Q))

/-- If a balanced frequency has a multiple of its ambient modulus within
distance `K < Q/2`, then the frequency itself has magnitude at most `K`.
This is the step which prevents `D_h` from containing every active factor on
the minor arcs. -/
lemma nearby_activeLcm_imp_small
    {Q K : ℕ} [NeZero Q] (hQ : 2 * K < Q) (h : ZMod Q)
    (hnear : nearbyMultiplePair K Q h.valMinAbs) :
    h.valMinAbs.natAbs ≤ K := by
  obtain ⟨x, hxQ, hdist⟩ := hnear
  obtain ⟨c, rfl⟩ := hxQ
  have hbal := h.valMinAbs_mem_Ioc
  have hd := abs_le.mp hdist
  have hQpos : (0 : ℤ) < Q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hQint : 2 * (K : ℤ) < (Q : ℤ) := by exact_mod_cast hQ
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have hc' : c ≤ -1 := by omega
    have hmul : (Q : ℤ) * c ≤ -(Q : ℤ) := by nlinarith
    exfalso
    nlinarith [hbal.1]
  · subst c
    simp only [mul_zero, zero_sub, abs_neg] at hdist
    have hcast : (h.valMinAbs.natAbs : ℤ) ≤ (K : ℤ) := by
      simpa [Int.natCast_natAbs] using hdist
    exact_mod_cast hcast
  · have hc' : 1 ≤ c := by omega
    have hmul : (Q : ℤ) ≤ (Q : ℤ) * c := by nlinarith
    exfalso
    nlinarith [hbal.2]

/-- A canonical minor frequency cannot have a nearby multiple of the full
active modulus once `K ≤ M/2` and `2K < Q`. -/
lemma not_nearby_activeLcm_of_minor
    {Q M K : ℕ} [NeZero Q] (hQ : 2 * K < Q) (hKM : K ≤ M / 2)
    {h : ZMod Q} (hminor : h ∈ minorFrequencies Q M) :
    ¬ nearbyMultiplePair K Q h.valMinAbs := by
  intro hnear
  have hsmall := nearby_activeLcm_imp_small hQ h hnear
  have hlarge : M / 2 < h.valMinAbs.natAbs := by
    rw [minorFrequencies, Finset.mem_sdiff, majorFrequencies,
      Finset.mem_filter] at hminor
    apply not_le.mp
    intro hle
    exact hminor.2 ⟨hminor.1, hle⟩
  omega

/-- The fixed-`D` fiber count: once every frequency in a fiber has a nearby
multiple of `lcm D`, the balanced-representative count applies verbatim. -/
theorem card_fixedKey_fiber_le
    {Q K : ℕ} [NeZero Q] {H : Finset (ZMod Q)}
    {key : ZMod Q → Finset ℕ} (D : Finset ℕ)
    (hL : 0 < D.lcm id)
    (hnear : ∀ h ∈ H, nearbyMultiplePair K ((key h).lcm id) h.valMinAbs) :
    (H.filter fun h ↦ key h = D).card ≤
      (2 * K + 1) * (Q / D.lcm id + 1) := by
  have hsub : (H.filter fun h ↦ key h = D) ⊆
      H.filter fun h ↦ nearbyMultiplePair K (D.lcm id) h.valMinAbs := by
    intro h hh
    rw [Finset.mem_filter] at hh ⊢
    exact ⟨hh.1, hh.2 ▸ hnear h hh.1⟩
  exact (Finset.card_le_card hsub).trans
    (card_filter_zmod_nearbyMultiplePair_le H hL)

/-- Source-shaped fixed-fiber count at the active modulus.  Omitting `s`
active prime powers costs at most their product, and hence at most `N^s` for
good denominators. -/
theorem card_active_fixedKey_fiber_le
    {N M S K : ℕ} {A : Finset ℕ}
    (hM : 1 ≤ M) (hA : A ⊆ goodDenominators N M S)
    {H : Finset (ZMod (Erdos297.ActiveLcm.activeLcm A))}
    {key : ZMod (Erdos297.ActiveLcm.activeLcm A) → Finset ℕ}
    (hkey : ∀ h ∈ H, key h ⊆ Erdos297.ActiveLcm.activePrimePowers A)
    (hnear : ∀ h ∈ H,
      nearbyMultiplePair K ((key h).lcm id) h.valMinAbs)
    (D : Finset ℕ) (hD : D ⊆ Erdos297.ActiveLcm.activePrimePowers A) :
    (H.filter fun h ↦ key h = D).card ≤
      (2 * K + 1) *
        (N ^ (Erdos297.ActiveLcm.activePrimePowers A \ D).card + 1) := by
  letI : NeZero (Erdos297.ActiveLcm.activeLcm A) :=
    ⟨Erdos297.ActiveLcm.activeLcm_ne_zero A⟩
  have hL : 0 < D.lcm id := by
    apply Nat.pos_iff_ne_zero.mpr
    apply UnitFractions.lcm_ne_zero_of_zero_not_mem
    intro hzero
    exact Erdos297.ActiveLcm.zero_not_mem_activePrimePowers A (hD hzero)
  have hbase := card_fixedKey_fiber_le D hL hnear
  apply hbase.trans
  gcongr
  exact (Erdos297.ActiveLcm.activeLcm_div_lcm_le_complement_prod hD).trans
    (Erdos297.ActiveLcm.complement_prod_good_le_pow hM hA)

/-- Complete fixed-`D` summation.  This is the combinatorial heart of the
minor-arc estimate: frequencies are partitioned by `D_h`, each fiber is
counted by a nearby `lcm D`, and omitting `s` active factors costs at most
`N^s`.  The remaining scalar sum is where the numerical decay
`N^(-10s)` is inserted. -/
theorem active_minor_sum_le_powerset
    {N M S K : ℕ} {A : Finset ℕ}
    (hM : 1 ≤ M) (hA : A ⊆ goodDenominators N M S)
    {H : Finset (ZMod (Erdos297.ActiveLcm.activeLcm A))}
    (key : ZMod (Erdos297.ActiveLcm.activeLcm A) → Finset ℕ)
    (f : ZMod (Erdos297.ActiveLcm.activeLcm A) → ℝ)
    (decay : ℕ → ℝ)
    (hdecay : ∀ s, 0 ≤ decay s)
    (hkey : ∀ h ∈ H, key h ⊆ Erdos297.ActiveLcm.activePrimePowers A)
    (hproper : ∀ h ∈ H, key h ≠ Erdos297.ActiveLcm.activePrimePowers A)
    (hnear : ∀ h ∈ H,
      nearbyMultiplePair K ((key h).lcm id) h.valMinAbs)
    (hpoint : ∀ h ∈ H,
      f h ≤ decay (Erdos297.ActiveLcm.activePrimePowers A \ key h).card) :
    ∑ h ∈ H, f h ≤
      ∑ D ∈ (Erdos297.ActiveLcm.activePrimePowers A).powerset.erase
          (Erdos297.ActiveLcm.activePrimePowers A),
        (((2 * K + 1) *
          (N ^ (Erdos297.ActiveLcm.activePrimePowers A \ D).card + 1) : ℕ) : ℝ) *
            decay (Erdos297.ActiveLcm.activePrimePowers A \ D).card := by
  letI : NeZero (Erdos297.ActiveLcm.activeLcm A) :=
    ⟨Erdos297.ActiveLcm.activeLcm_ne_zero A⟩
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := H) (t := (Erdos297.ActiveLcm.activePrimePowers A).powerset.erase
      (Erdos297.ActiveLcm.activePrimePowers A))
    (g := key) (fun h hh ↦ Finset.mem_erase.mpr
      ⟨hproper h hh, Finset.mem_powerset.mpr (hkey h hh)⟩) f]
  apply Finset.sum_le_sum
  intro D hD
  have hDsub : D ⊆ Erdos297.ActiveLcm.activePrimePowers A :=
    Finset.mem_powerset.mp (Finset.mem_erase.mp hD).2
  calc
    ∑ h ∈ H with key h = D, f h ≤
        ∑ _h ∈ H.filter (fun h ↦ key h = D),
          decay (Erdos297.ActiveLcm.activePrimePowers A \ D).card := by
      apply Finset.sum_le_sum
      intro h hh
      rw [Finset.mem_filter] at hh
      simpa [hh.2] using hpoint h hh.1
    _ = ((H.filter fun h ↦ key h = D).card : ℝ) *
          decay (Erdos297.ActiveLcm.activePrimePowers A \ D).card := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((2 * K + 1) *
          (N ^ (Erdos297.ActiveLcm.activePrimePowers A \ D).card + 1) : ℕ) : ℝ) *
          decay (Erdos297.ActiveLcm.activePrimePowers A \ D).card := by
      apply mul_le_mul_of_nonneg_right _ (hdecay _)
      exact_mod_cast card_active_fixedKey_fiber_le hM hA hkey hnear D hDsub

/-- Subsets of `U` with exactly `s` omitted elements. -/
noncomputable def complementCardClass {α : Type*} [DecidableEq α]
    (U : Finset α) (s : ℕ) : Finset (Finset α) :=
  U.powerset.filter fun D ↦ (U \ D).card = s

/-- There are at most `N^s` ways to omit `s` elements from a set of size at
most `N`.  We use the complement injection into `powersetCard s U`, followed
by `choose(N,s) ≤ N^s`. -/
lemma card_complementCardClass_le_pow {α : Type*} [DecidableEq α]
    {U : Finset α} {N s : ℕ} (hUN : U.card ≤ N) :
    (complementCardClass U s).card ≤ N ^ s := by
  have hmap : Set.MapsTo (fun D : Finset α ↦ U \ D)
      (complementCardClass U s) (U.powersetCard s) := by
    intro D hD
    change D ∈ complementCardClass U s at hD
    simp only [complementCardClass, Finset.mem_filter,
      Finset.mem_powerset] at hD
    change U \ D ∈ U.powersetCard s
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.sdiff_subset, hD.2⟩
  have hinj : Set.InjOn (fun D : Finset α ↦ U \ D)
      (complementCardClass U s) := by
    intro D hD E hE heq
    change D ∈ complementCardClass U s at hD
    change E ∈ complementCardClass U s at hE
    simp only [complementCardClass, Finset.mem_filter,
      Finset.mem_powerset] at hD hE
    have hDU : D ⊆ U := hD.1
    have hEU : E ⊆ U := hE.1
    have hcomp := congrArg (fun X : Finset α ↦ U \ X) heq
    simpa [Finset.sdiff_sdiff_eq_self hDU,
      Finset.sdiff_sdiff_eq_self hEU] using hcomp
  calc
    (complementCardClass U s).card ≤ (U.powersetCard s).card :=
      Finset.card_le_card_of_injOn _ hmap hinj
    _ = U.card.choose s := Finset.card_powersetCard s U
    _ ≤ U.card ^ s := Nat.choose_le_pow _ _
    _ ≤ N ^ s := Nat.pow_le_pow_left hUN _

/-- The contribution attached to one fixed omitted-cardinality class. -/
lemma scalarMinorTerm_le {N K s : ℕ} (hN : 3 ≤ N) (hK : K ≤ N) :
    (((2 * K + 1) * (N ^ s + 1) : ℕ) : ℝ) *
        (1 / (N : ℝ) ^ (10 * s)) ≤
      6 * (N : ℝ) / (N : ℝ) ^ (9 * s) := by
  have hNone : 1 ≤ N := by omega
  have hpowone : 1 ≤ N ^ s := one_le_pow₀ hNone
  have hfirst : 2 * K + 1 ≤ 3 * N := by omega
  have hsecond : N ^ s + 1 ≤ 2 * N ^ s := by omega
  have hnat : (2 * K + 1) * (N ^ s + 1) ≤ 6 * N * N ^ s := by
    calc
      (2 * K + 1) * (N ^ s + 1) ≤ (3 * N) * (2 * N ^ s) :=
        Nat.mul_le_mul hfirst hsecond
      _ = 6 * N * N ^ s := by ring
  have hNreal : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 3) hN)
  calc
    (((2 * K + 1) * (N ^ s + 1) : ℕ) : ℝ) *
        (1 / (N : ℝ) ^ (10 * s)) ≤
        (((6 * N * N ^ s : ℕ) : ℝ) *
          (1 / (N : ℝ) ^ (10 * s))) := by
      gcongr
    _ = 6 * (N : ℝ) / (N : ℝ) ^ (9 * s) := by
      push_cast
      rw [show 10 * s = s + 9 * s by omega, pow_add]
      field_simp

lemma scalarMinorClass_le {N K s c : ℕ} (hN : 3 ≤ N) (hK : K ≤ N)
    (hs : 1 ≤ s) (hc : c ≤ N ^ s) :
    (c : ℝ) * ((((2 * K + 1) * (N ^ s + 1) : ℕ) : ℝ) *
        (1 / (N : ℝ) ^ (10 * s))) ≤
      6 * (N : ℝ) / (N : ℝ) ^ (8 * s) := by
  calc
    (c : ℝ) * ((((2 * K + 1) * (N ^ s + 1) : ℕ) : ℝ) *
        (1 / (N : ℝ) ^ (10 * s))) ≤
        (N ^ s : ℕ) * (6 * (N : ℝ) / (N : ℝ) ^ (9 * s)) := by
      gcongr
      exact scalarMinorTerm_le hN hK
    _ = 6 * (N : ℝ) / (N : ℝ) ^ (8 * s) := by
      push_cast
      have hNreal : (0 : ℝ) < N := by positivity
      rw [show 9 * s = s + 8 * s by omega, pow_add]
      field_simp

/-- The complete scalar estimate after fixed-`D` counting.  After the
unnormalized frequency sum this is `2/N`; Fourier inversion contributes the
additional `1/Q`, giving the source's `2/(QN)`. -/
theorem scalar_minor_sum_le_two_div {α : Type*} [DecidableEq α]
    {U : Finset α} {N K : ℕ} (hN : 3 ≤ N) (hK : K ≤ N)
    (hUN : U.card ≤ N) :
    ∑ D ∈ U.powerset.erase U,
      (((2 * K + 1) * (N ^ (U \ D).card + 1) : ℕ) : ℝ) *
        (1 / (N : ℝ) ^ (10 * (U \ D).card)) ≤ 2 / (N : ℝ) := by
  let term : Finset α → ℝ := fun D ↦
    (((2 * K + 1) * (N ^ (U \ D).card + 1) : ℕ) : ℝ) *
      (1 / (N : ℝ) ^ (10 * (U \ D).card))
  have hmaps : ∀ D ∈ U.powerset.erase U, (U \ D).card ∈ Finset.Icc 1 N := by
    intro D hD
    rw [Finset.mem_Icc]
    have hsub : D ⊆ U := Finset.mem_powerset.mp (Finset.mem_erase.mp hD).2
    have hne : D ≠ U := (Finset.mem_erase.mp hD).1
    constructor
    · rw [Nat.one_le_iff_ne_zero, Finset.card_ne_zero]
      exact Finset.sdiff_nonempty.mpr fun hUD ↦ hne (hsub.antisymm hUD)
    · exact (Finset.card_le_card Finset.sdiff_subset).trans hUN
  change ∑ D ∈ U.powerset.erase U, term D ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to (s := U.powerset.erase U)
    (t := Finset.Icc 1 N) (g := fun D ↦ (U \ D).card) hmaps term]
  calc
    ∑ s ∈ Finset.Icc 1 N,
        ∑ D ∈ U.powerset.erase U with (U \ D).card = s, term D ≤
        ∑ _s ∈ Finset.Icc 1 N, 6 * (N : ℝ) / (N : ℝ) ^ 8 := by
      apply Finset.sum_le_sum
      intro s hs
      rw [Finset.mem_Icc] at hs
      let fiber := (U.powerset.erase U).filter fun D ↦ (U \ D).card = s
      have hfiber : fiber ⊆ complementCardClass U s := by
        intro D hD
        rw [Finset.mem_filter] at hD
        rw [complementCardClass, Finset.mem_filter]
        exact ⟨(Finset.mem_erase.mp hD.1).2, hD.2⟩
      have hcard : fiber.card ≤ N ^ s :=
        (Finset.card_le_card hfiber).trans (card_complementCardClass_le_pow hUN)
      have hconst : ∀ D ∈ fiber, term D =
          (((2 * K + 1) * (N ^ s + 1) : ℕ) : ℝ) *
            (1 / (N : ℝ) ^ (10 * s)) := by
        intro D hD
        have hsD : (U \ D).card = s := (Finset.mem_filter.mp hD).2
        simp only [term, hsD]
      calc
        ∑ D ∈ U.powerset.erase U with (U \ D).card = s, term D =
            (fiber.card : ℝ) *
              ((((2 * K + 1) * (N ^ s + 1) : ℕ) : ℝ) *
                (1 / (N : ℝ) ^ (10 * s))) := by
          change ∑ D ∈ fiber, term D = _
          calc
            ∑ D ∈ fiber, term D =
                ∑ _D ∈ fiber,
                  (((2 * K + 1) * (N ^ s + 1) : ℕ) : ℝ) *
                    (1 / (N : ℝ) ^ (10 * s)) := by
              apply Finset.sum_congr rfl
              exact hconst
            _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 6 * (N : ℝ) / (N : ℝ) ^ (8 * s) :=
          scalarMinorClass_le hN hK hs.1 hcard
        _ ≤ 6 * (N : ℝ) / (N : ℝ) ^ 8 := by
          have hNreal : (1 : ℝ) ≤ N := by
            exact_mod_cast (show 1 ≤ N by omega)
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact pow_le_pow_right₀ hNreal (by omega)
    _ = (Finset.Icc 1 N).card * (6 * (N : ℝ) / (N : ℝ) ^ 8) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * (6 * (N : ℝ) / (N : ℝ) ^ 8) := by
      gcongr
      simp
    _ ≤ 2 / (N : ℝ) := by
      have hNreal : (3 : ℝ) ≤ N := by exact_mod_cast hN
      have hNpos : (0 : ℝ) < N := by positivity
      field_simp
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hNreal 5]

theorem scalar_minor_sum_le_quarter {α : Type*} [DecidableEq α]
    {U : Finset α} {N K : ℕ} (hN : 8 ≤ N) (hK : K ≤ N)
    (hUN : U.card ≤ N) :
    ∑ D ∈ U.powerset.erase U,
      (((2 * K + 1) * (N ^ (U \ D).card + 1) : ℕ) : ℝ) *
        (1 / (N : ℝ) ^ (10 * (U \ D).card)) ≤ (1 / 4 : ℝ) := by
  apply (scalar_minor_sum_le_two_div (show 3 ≤ N by omega) hK hUN).trans
  have hNreal : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by positivity
  rw [div_le_iff₀ hNpos]
  linarith

/-- Coarse count of frequencies in an interval of length at most `Q` having
a multiple of `L` within distance `K`.  The harmless `+1` accommodates both
endpoints and all integer-rounding conventions. -/
theorem card_filter_nearbyMultiplePair_le_coarse
    {lower upper : ℤ} {Q K L : ℕ} (_hL : 0 < L)
    (hwidth : upper - lower ≤ (Q : ℤ)) :
    ((integerInterval lower upper).filter (nearbyMultiplePair K L)).card ≤
      (2 * K + 1) * Q := by
  have hsub : (integerInterval lower upper).filter (nearbyMultiplePair K L) ⊆
      integerInterval lower upper := filter_subset _ _
  have hcard := card_le_card hsub
  have hinterval : (integerInterval lower upper).card ≤ Q := by
    simp only [integerInterval, Int.card_Ioc]
    omega
  have hfactor : 1 ≤ 2 * K + 1 := by omega
  exact hcard.trans (hinterval.trans (Nat.le_mul_of_pos_left Q hfactor))

end

end Erdos297.MinorArc

#print axioms Erdos297.MinorArc.phaseProduct_decay
#print axioms Erdos297.MinorArc.coefficient_norm_le_power
#print axioms Erdos297.MinorArc.commonNearbyMultiple_of_auxiliaryData
#print axioms Erdos297.MinorArc.active_minor_sum_le_powerset
#print axioms Erdos297.MinorArc.scalar_minor_sum_le_two_div
