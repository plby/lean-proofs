/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.FactorDensity
import ErdosProblems.Erdos297.ActiveLcm
import ErdosProblems.Erdos297.PrimeIntervals
import ErdosProblems.Erdos297.SmoothMultiple

/-!
# Repaired auxiliary-prime sieve for Erdős Problem 297

This file isolates the finite source-supply combinatorics from the density
estimates.  The first arXiv version of Liu--Sawhney's Proposition 3.2 loses
one factor of `log log N` in its `p'` pigeonhole argument.  The exact finite
budget below shows why the repaired cutoff uses `(log log N)^4`, and hence a
sixth-power scale condition, rather than the printed third/fifth powers.
-/

namespace Erdos297.AuxiliarySupply

open Filter Finset Real
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

open ActiveLcm GoodFactorization FactorDensity PrimeIntervals SmoothMultiple
open Erdos285.PrimePowers

/-- Primes at most `X` which are coprime to `q`. -/
def smallPrimeCandidates (X q : ℕ) : Finset ℕ :=
  (Icc 2 X).filter fun p ↦ p.Prime ∧ p.Coprime q

@[simp] lemma mem_smallPrimeCandidates {X q p : ℕ} :
    p ∈ smallPrimeCandidates X q ↔
      2 ≤ p ∧ p ≤ X ∧ p.Prime ∧ p.Coprime q := by
  simp [smallPrimeCandidates, and_assoc]

/-- The broad prime interval used to multiply `d` into `[2K,100K]`. -/
def extensionPrimes (K d : ℕ) : Finset ℕ :=
  primesOneFifty (K / d + 1)

@[simp] lemma mem_extensionPrimes {K d p : ℕ} :
    p ∈ extensionPrimes K d ↔
      K / d < p ∧ p ≤ 50 * (K / d + 1) ∧ p.Prime := by
  rw [extensionPrimes, mem_primesOneFifty]
  constructor
  · rintro ⟨hlo, hhi, hprime⟩
    exact ⟨Nat.lt_of_succ_le hlo, hhi, hprime⟩
  · rintro ⟨hlo, hhi, hprime⟩
    exact ⟨Nat.succ_le_iff.mpr hlo, hhi, hprime⟩

lemma mul_mem_extension_range {K d p : ℕ} (hd : d ≠ 0)
    (hp : p ∈ extensionPrimes K d) :
    K < d * p ∧ d * p ≤ 50 * K + 50 * d := by
  have hp' := mem_extensionPrimes.mp hp
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  constructor
  · exact (Nat.lt_mul_div_succ K hdpos).trans_le
      (Nat.mul_le_mul_left d (Nat.succ_le_iff.mpr hp'.1))
  · calc
      d * p ≤ d * (50 * (K / d + 1)) :=
        Nat.mul_le_mul_left d hp'.2.1
      _ = 50 * (d * (K / d) + d) := by ring
      _ ≤ 50 * (K + d) := by
        exact Nat.mul_le_mul_left 50
          (Nat.add_le_add_right (Nat.mul_div_le K d) d)
      _ = 50 * K + 50 * d := by ring

/-- Five applications of Bertrand's postulate give five distinct primes in
every interval `[a,50a]` with `a ≥ 1`.  This uniform finite fact is enough
for every extension step, since the partial base has at most three distinct
prime factors. -/
lemma five_le_card_primesOneFifty {a : ℕ} (ha : 1 ≤ a) :
    5 ≤ (primesOneFifty a).card := by
  obtain ⟨p₁, hp₁, hp₁lo, hp₁hi⟩ := Nat.bertrand a (by omega)
  obtain ⟨p₂, hp₂, hp₂lo, hp₂hi⟩ := Nat.bertrand (2 * a) (by omega)
  obtain ⟨p₃, hp₃, hp₃lo, hp₃hi⟩ := Nat.bertrand (4 * a) (by omega)
  obtain ⟨p₄, hp₄, hp₄lo, hp₄hi⟩ := Nat.bertrand (8 * a) (by omega)
  obtain ⟨p₅, hp₅, hp₅lo, hp₅hi⟩ := Nat.bertrand (16 * a) (by omega)
  let five : Finset ℕ := {p₁, p₂, p₃, p₄, p₅}
  have hsub : five ⊆ primesOneFifty a := by
    intro p hp
    simp only [five, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact mem_primesOneFifty.mpr ⟨hp₁lo.le, by omega, hp₁⟩
    · exact mem_primesOneFifty.mpr ⟨by omega, by omega, hp₂⟩
    · exact mem_primesOneFifty.mpr ⟨by omega, by omega, hp₃⟩
    · exact mem_primesOneFifty.mpr ⟨by omega, by omega, hp₄⟩
    · exact mem_primesOneFifty.mpr ⟨by omega, by omega, hp₅⟩
  have hp₁₂ : p₁ ≠ p₂ := by omega
  have hp₁₃ : p₁ ≠ p₃ := by omega
  have hp₁₄ : p₁ ≠ p₄ := by omega
  have hp₁₅ : p₁ ≠ p₅ := by omega
  have hp₂₃ : p₂ ≠ p₃ := by omega
  have hp₂₄ : p₂ ≠ p₄ := by omega
  have hp₂₅ : p₂ ≠ p₅ := by omega
  have hp₃₄ : p₃ ≠ p₄ := by omega
  have hp₃₅ : p₃ ≠ p₅ := by omega
  have hp₄₅ : p₄ ≠ p₅ := by omega
  have hcard : five.card = 5 := by
    simp [five, hp₁₂, hp₁₃, hp₁₄, hp₁₅, hp₂₃, hp₂₄, hp₂₅,
      hp₃₄, hp₃₅, hp₄₅]
  rw [← hcard]
  exact Finset.card_le_card hsub

lemma five_le_card_extensionPrimes {K d : ℕ} :
    5 ≤ (extensionPrimes K d).card := by
  exact five_le_card_primesOneFifty (by simp [extensionPrimes])

lemma eventually_five_le_card_primesHalfFull :
    ∀ᶠ S : ℕ in atTop, 5 ≤ (primesHalfFull S).card := by
  have hsmall :=
    tendsto_natCast_atTop_atTop.eventually
      (Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 100))
  filter_upwards [eventually_div_ten_log_le_card_primesHalfFull, hsmall,
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (1 : ℝ))]
      with S hcard hlogsmall hS
  have hlog : 0 < Real.log (S : ℝ) := Real.log_pos hS
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hlog.le] at hlogsmall
  rw [abs_of_nonneg (show (0 : ℝ) ≤ (S : ℝ) by positivity)] at hlogsmall
  have hfive : (5 : ℝ) ≤ (S : ℝ) / (10 * Real.log S) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 10 * Real.log S)]
    nlinarith
  exact_mod_cast hfive.trans hcard

lemma tendsto_S_atTop : Tendsto S atTop atTop := by
  have hpow : Tendsto almostOnePower atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (9999 : ℝ) / 10000)).comp
      tendsto_natCast_atTop_atTop
  have hnat : Tendsto (fun N : ℕ ↦ (S N : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop eventually_almostOnePower_le_natS hpow
  exact (tendsto_natCast_atTop_iff (R := ℝ)).mp hnat

lemma eventually_five_le_card_primesHalfFull_S :
    ∀ᶠ N : ℕ in atTop, 5 ≤ (primesHalfFull (S N)).card :=
  tendsto_S_atTop.eventually eventually_five_le_card_primesHalfFull

/-- Multiplication by a fresh prime preserves smoothness and the exponent
bound and adds exactly one to `Omega` and `omega`. -/
lemma factorization_data_mul_fresh_prime {N S d p : ℕ}
    (hd : d ≠ 0) (hp : p.Prime) (hpd : ¬p ∣ d) (hpS : p ≤ S)
    (hE : 1 ≤ exponentBound N)
    (hdSmooth : PrimePowerSmooth S d)
    (hdExp : maxPrimeExponent d ≤ exponentBound N) :
    PrimePowerSmooth S (d * p) ∧
      maxPrimeExponent (d * p) ≤ exponentBound N ∧
      Ω (d * p) = Ω d + 1 ∧ ω (d * p) = ω d + 1 := by
  refine ⟨primePowerSmooth_mul_prime_of_not_dvd hd hp hpd hdSmooth hpS,
    maxPrimeExponent_mul_prime_of_not_dvd hd hp hpd hE hdExp, ?_, ?_⟩
  · rw [ArithmeticFunction.cardFactors_mul hd hp.ne_zero,
      ArithmeticFunction.cardFactors_apply_prime hp]
  · rw [ArithmeticFunction.cardDistinctFactors_mul
      (hp.coprime_iff_not_dvd.mpr hpd).symm,
      ArithmeticFunction.cardDistinctFactors_apply_prime hp]

/-- A base modulus produced from an active prime power and at most three
fresh primes (`p'` and the one- or two-prime extension). -/
structure BaseExtension (N S K q : ℕ) where
  base : ℕ
  smallPrime : ℕ
  source_dvd : q * smallPrime ∣ base
  q_dvd : q ∣ base
  lower : K < base
  upper : base ≤ 100 * K
  smooth : PrimePowerSmooth S base
  exponent : maxPrimeExponent base ≤ exponentBound N
  factors : Ω base ≤ exponentBound N + 3
  distinct : ω base ≤ 4

/-- Exact finite cardinal hypotheses used by the one/two-prime extension. -/
def ExtensionCardConditions (S K d : ℕ) : Prop :=
  d.primeFactors.card < (extensionPrimes K d).card ∧
    d.primeFactors.card < (primesHalfFull S).card ∧
    ∀ r ∈ primesHalfFull S, ¬r ∣ d → d * r ≤ K →
      50 * K + 50 * (d * r) ≤ (d * r) * S ∧
        (d * r).primeFactors.card < (extensionPrimes K (d * r)).card

lemma card_primeFactors_eq_omega {n : ℕ} : n.primeFactors.card = ω n := by
  rw [ArithmeticFunction.cardDistinctFactors_apply,
    Nat.primeFactors, List.card_toFinset]

/-- Uniform finite discharge of the extension-cardinality hypotheses.  The
quadratic inequality is the scale relation actually used here; it holds for
the source parameters even though `S ≤ K`. -/
lemma extensionCardConditions_of_quadratic_bounds {S K d : ℕ}
    (hS : 200 ≤ S) (hKS : 100 * K ≤ S * S) (hd : 4 ≤ d) (hdω : ω d ≤ 2)
    (hhalf : 5 ≤ (primesHalfFull S).card) :
    ExtensionCardConditions S K d := by
  refine ⟨?_, ?_, ?_⟩
  · rw [card_primeFactors_eq_omega]
    exact hdω.trans_lt (five_le_card_extensionPrimes.trans_lt' (by omega))
  · rw [card_primeFactors_eq_omega]
    exact hdω.trans_lt (hhalf.trans_lt' (by omega))
  · intro r hr hrd hdrange
    have hrData := mem_primesHalfFull.mp hr
    have hrPrime := hrData.2.2
    have hd0 : d ≠ 0 := by omega
    have hωmul : ω (d * r) = ω d + 1 := by
      rw [ArithmeticFunction.cardDistinctFactors_mul
        (hrPrime.coprime_iff_not_dvd.mpr hrd).symm,
        ArithmeticFunction.cardDistinctFactors_apply_prime hrPrime]
    have hdr : S ≤ d * r := by
      have hrLower := hrData.1
      calc
        S ≤ 4 * (S / 2) := by omega
        _ ≤ d * r := Nat.mul_le_mul hd hrLower
    constructor
    · have hleft : 50 * K + 50 * (d * r) ≤ 100 * K := by omega
      have hright : 100 * K ≤ (d * r) * S := by
        calc
          100 * K ≤ S * S := hKS
          _ ≤ (d * r) * S := Nat.mul_le_mul_right S hdr
      exact hleft.trans hright
    · rw [card_primeFactors_eq_omega, hωmul]
      exact (by omega : ω d + 1 < 5) |>.trans_le
        five_le_card_extensionPrimes

/-- Simpler sufficient form retained for callers which happen to have
`K ≤ S`. -/
lemma extensionCardConditions_of_bounds {S K d : ℕ}
    (hS : 200 ≤ S) (hKS : K ≤ S) (hd : 4 ≤ d) (hdω : ω d ≤ 2)
    (hhalf : 5 ≤ (primesHalfFull S).card) :
    ExtensionCardConditions S K d := by
  apply extensionCardConditions_of_quadratic_bounds hS _ hd hdω hhalf
  calc
    100 * K ≤ 100 * S := Nat.mul_le_mul_left 100 hKS
    _ ≤ S * S := Nat.mul_le_mul_right S (by omega)

/-- Finite one/two-prime construction of the source's base modulus.

The active prime power is written explicitly as `a^k`; the eventual
application obtains this data from `ActiveLcm.activePrimePower_exponent_le`.
All analytic work is confined to `ExtensionCardConditions` and to the
displayed inequality `100*K/d ≤ S` which chooses the branch.
-/
theorem exists_baseExtension_of_card_conditions
    {N S K q p' a k : ℕ}
    (ha : a.Prime) (hk : 1 ≤ k) (hq : q = a ^ k)
    (hkE : k ≤ exponentBound N) (hE : 1 ≤ exponentBound N)
    (hqS : q ≤ S) (hp' : p'.Prime) (hp'q : p'.Coprime q)
    (hp'S : p' ≤ S) (hqpK : q * p' ≤ K)
    (hcards : ExtensionCardConditions S K (q * p')) :
    ∃ base : BaseExtension N S K q, base.smallPrime = p' := by
  have hq0 : q ≠ 0 := by
    rw [hq]
    exact pow_ne_zero _ ha.ne_zero
  have hd0 : q * p' ≠ 0 := mul_ne_zero hq0 hp'.ne_zero
  have hqSmooth : PrimePowerSmooth S q :=
    primePowerSmooth_mono hqS (primePowerSmooth_self q)
  have hqOmega : Ω q = k := by
    rw [hq, ArithmeticFunction.cardFactors_apply_prime_pow ha]
  have hqomega : ω q = 1 := by
    rw [hq, ArithmeticFunction.cardDistinctFactors_apply_prime_pow ha (by omega)]
  have hqExp : maxPrimeExponent q ≤ exponentBound N := by
    exact (maxPrimeExponent_le_Omega q).trans (hqOmega.le.trans hkE)
  have hp'not : ¬p' ∣ q := hp'.coprime_iff_not_dvd.mp hp'q
  obtain ⟨hdSmooth, hdExp, hdOmega, hdomega⟩ :=
    factorization_data_mul_fresh_prime hq0 hp' hp'not hp'S hE hqSmooth hqExp
  let d := q * p'
  have hdOmega' : Ω d = k + 1 := by simpa [d, hqOmega] using hdOmega
  have hdomega' : ω d = 2 := by simpa [d, hqomega] using hdomega
  by_cases hdirect : 50 * (K / d + 1) ≤ S
  · obtain ⟨r, hrPrime, hrLower, hrUpper, hrd⟩ :=
      exists_prime_in_interval_not_dvd hd0 hcards.1
    have hrmem : r ∈ extensionPrimes K d := by
      rw [mem_extensionPrimes]
      have hlo : K / d + 1 ≤ r := by simpa only [d] using hrLower
      exact ⟨Nat.lt_of_succ_le hlo, hrUpper, hrPrime⟩
    have hrS : r ≤ S :=
      (mem_extensionPrimes.mp hrmem).2.1.trans hdirect
    obtain ⟨hbaseSmooth, hbaseExp, hbaseOmega, hbaseomega⟩ :=
      factorization_data_mul_fresh_prime hd0 hrPrime hrd hrS hE hdSmooth hdExp
    have hrange := mul_mem_extension_range hd0 hrmem
    refine ⟨⟨d * r, p', dvd_mul_right d r, ?_, hrange.1, ?_,
      hbaseSmooth, hbaseExp, ?_, ?_⟩, rfl⟩
    · exact dvd_trans (dvd_mul_right q p') (dvd_mul_right d r)
    · exact hrange.2.trans (by omega)
    · rw [hbaseOmega, hdOmega']
      omega
    · rw [hbaseomega, hdomega']
      omega
  · obtain ⟨r₁, hr₁Prime, hr₁Lower, hr₁Upper, hr₁d⟩ :=
      exists_prime_in_interval_not_dvd hd0 hcards.2.1
    have hr₁mem : r₁ ∈ primesHalfFull S := by
      rw [mem_primesHalfFull]
      exact ⟨hr₁Lower, hr₁Upper, hr₁Prime⟩
    obtain ⟨hd₁Smooth, hd₁Exp, hd₁Omega, hd₁omega⟩ :=
      factorization_data_mul_fresh_prime hd0 hr₁Prime hr₁d hr₁Upper hE hdSmooth hdExp
    have hd₁0 : d * r₁ ≠ 0 := mul_ne_zero hd0 hr₁Prime.ne_zero
    have hd₁Upper : d * r₁ ≤ 100 * K := by
      have hSlt : S < 50 * (K / d + 1) := Nat.lt_of_not_ge hdirect
      calc
        d * r₁ ≤ d * S := Nat.mul_le_mul_left d hr₁Upper
        _ ≤ d * (50 * (K / d + 1)) :=
          Nat.mul_le_mul_left d (Nat.le_of_lt hSlt)
        _ = 50 * (d * (K / d) + d) := by ring
        _ ≤ 50 * (K + d) := by
          exact Nat.mul_le_mul_left 50
            (Nat.add_le_add_right (Nat.mul_div_le K d) d)
        _ ≤ 100 * K := by omega
    by_cases hd₁Lower : K < d * r₁
    · refine ⟨⟨d * r₁, p', dvd_mul_right d r₁, ?_, hd₁Lower, hd₁Upper,
        hd₁Smooth, hd₁Exp, ?_, ?_⟩, rfl⟩
      · exact dvd_trans (dvd_mul_right q p') (dvd_mul_right d r₁)
      · rw [hd₁Omega, hdOmega']
        omega
      · rw [hd₁omega, hdomega']
        omega
    · have hd₁lt : d * r₁ ≤ K := Nat.le_of_not_gt hd₁Lower
      obtain ⟨r₂, hr₂Prime, hr₂Lower, hr₂Upper, hr₂d₁⟩ :=
        exists_prime_in_interval_not_dvd hd₁0
          (hcards.2.2 r₁ hr₁mem hr₁d hd₁lt).2
      have hr₂mem : r₂ ∈ extensionPrimes K (d * r₁) := by
        rw [mem_extensionPrimes]
        have hlo : K / (d * r₁) + 1 ≤ r₂ := by
          simpa only [d] using hr₂Lower
        exact ⟨Nat.lt_of_succ_le hlo, hr₂Upper, hr₂Prime⟩
      have hbS : 50 * (K / (d * r₁) + 1) ≤ S := by
        have hscale := (hcards.2.2 r₁ hr₁mem hr₁d hd₁lt).1
        have hmul : (d * r₁) * (50 * (K / (d * r₁) + 1)) ≤
            50 * K + 50 * (d * r₁) := by
          calc
            (d * r₁) * (50 * (K / (d * r₁) + 1)) =
                50 * ((d * r₁) * (K / (d * r₁)) + d * r₁) := by ring
            _ ≤ 50 * (K + d * r₁) := by
              exact Nat.mul_le_mul_left 50
                (Nat.add_le_add_right (Nat.mul_div_le K (d * r₁)) (d * r₁))
            _ = 50 * K + 50 * (d * r₁) := by ring
        exact Nat.le_of_mul_le_mul_left (hmul.trans hscale)
          (Nat.pos_of_ne_zero hd₁0)
      have hr₂S : r₂ ≤ S := (mem_extensionPrimes.mp hr₂mem).2.1.trans hbS
      obtain ⟨hbaseSmooth, hbaseExp, hbaseOmega, hbaseomega⟩ :=
        factorization_data_mul_fresh_prime hd₁0 hr₂Prime hr₂d₁ hr₂S hE
          hd₁Smooth hd₁Exp
      have hrange := mul_mem_extension_range hd₁0 hr₂mem
      refine ⟨⟨(d * r₁) * r₂, p',
        dvd_trans (dvd_mul_right d r₁) (dvd_mul_right (d * r₁) r₂),
        ?_, hrange.1, ?_, hbaseSmooth, hbaseExp, ?_, ?_⟩, rfl⟩
      · exact dvd_trans (dvd_mul_right q p')
          (dvd_trans (dvd_mul_right d r₁) (dvd_mul_right (d * r₁) r₂))
      · exact hrange.2.trans (by omega)
      · rw [hbaseOmega, hd₁Omega, hdOmega']
        omega
      · rw [hbaseomega, hd₁omega, hdomega']

lemma eventually_exponentBound_add_five_le_factorBound :
    ∀ᶠ N : ℕ in atTop, exponentBound N + 5 ≤ factorBound N := by
  filter_upwards [tendsto_logLogScale.eventually_ge_atTop 1] with N hLL
  change (1 : ℝ) ≤ Real.log (Real.log (N : ℝ)) at hLL
  have hfiveNonneg : 0 ≤ 5 * logLogScale N := by positivity
  have htenNonneg : 0 ≤ 10 * logLogScale N := by positivity
  rw [exponentBound, factorBound]
  apply Nat.le_floor
  have hfloor : ((⌊5 * logLogScale N⌋₊ : ℕ) : ℝ) ≤
      5 * logLogScale N := Nat.floor_le hfiveNonneg
  change ((⌊5 * Real.log (Real.log (N : ℝ))⌋₊ : ℕ) : ℝ) ≤
    5 * Real.log (Real.log (N : ℝ)) at hfloor
  norm_num only [Nat.cast_add, Nat.cast_ofNat]
  linarith

lemma eventually_auxiliaryPrime_le_S :
    ∀ᶠ N : ℕ in atTop, ∀ p ∈ auxiliaryPrimes N, p ≤ S N := by
  filter_upwards [eventually_log_pow_ten_le_almostOnePower,
    eventually_almostOnePower_le_natS,
    tendsto_logScale.eventually_ge_atTop 2, eventually_pos_scales]
      with N hpow hNS hL hpos
  rcases hpos with ⟨hNpos, hLone, hLL, hLLL⟩
  intro p hp
  have hp' := mem_auxiliaryPrimes.mp hp
  have hpR : (p : ℝ) ≤ 40 * logScale N := by
    have hpFloorR : (p : ℝ) ≤ (⌊40 * Real.log (N : ℝ)⌋₊ : ℝ) := by
      exact_mod_cast hp'.2.1
    exact hpFloorR.trans (by
      simpa [logScale] using
        (Nat.floor_le (show 0 ≤ 40 * Real.log (N : ℝ) by positivity)))
  have hpow9 : (40 : ℝ) ≤ logScale N ^ 9 := by
    calc
      (40 : ℝ) ≤ 2 ^ 9 := by norm_num
      _ ≤ logScale N ^ 9 := pow_le_pow_left₀ (by norm_num) hL 9
  have hforty : 40 * logScale N ≤ logScale N ^ 10 := by
    calc
      40 * logScale N ≤ logScale N ^ 9 * logScale N :=
        mul_le_mul_of_nonneg_right hpow9 (by positivity)
      _ = logScale N ^ 10 := by ring
  have hpS : (p : ℝ) ≤ (S N : ℝ) := hpR.trans (hforty.trans (hpow.trans hNS))
  exact_mod_cast hpS

/-- Every eligible auxiliary prime has a genuine good multiple.  This is
the nonvacuity step missing from a purely set-theoretic sieve. -/
theorem eventually_good_multiple_of_baseExtension :
    ∀ᶠ N : ℕ in atTop, ∀ {q : ℕ}
      (base : BaseExtension N (S N) (KSafe N) q)
      {p : ℕ}, p ∈ auxiliaryPrimes N → p.Coprime base.base →
      ∃ n ∈ goodDenominators N (M N) (S N),
        N / 2 ≤ n ∧ n ≤ N ∧ base.base * p ∣ n := by
  filter_upwards [eventually_exists_goodDenominator_multiple_KSafe,
    eventually_exponentBound_add_five_le_factorBound,
    eventually_auxiliaryPrime_le_S,
    tendsto_logLogScale.eventually_ge_atTop 1, eventually_pos_scales]
      with N hmultiple hbudget hpS hLL hpos
  rcases hpos with ⟨hNpos, hLpos, hLLpos, hLLLpos⟩
  intro q base p hpP hcop
  have hpData := mem_auxiliaryPrimes.mp hpP
  have hpPrime := hpData.2.2
  have hpNot : ¬p ∣ base.base := hpPrime.coprime_iff_not_dvd.mp hcop
  have hE : 1 ≤ exponentBound N := by
    rw [exponentBound]
    apply Nat.le_floor
    simpa [logLogScale, logScale] using
      (show (1 : ℝ) ≤ 5 * logLogScale N by linarith)
  obtain ⟨hdSmooth, hdExp, hdOmega, hdomega⟩ :=
    factorization_data_mul_fresh_prime
      (by have := base.lower; omega) hpPrime hpNot (hpS p hpP) hE
      base.smooth base.exponent
  let d := base.base * p
  apply hmultiple d
  · have hpPos := hpPrime.pos
    dsimp [d]
    nlinarith [base.lower]
  · have hpUpper : (p : ℝ) ≤ 40 * logScale N := by
      have hpFloorR : (p : ℝ) ≤ (⌊40 * Real.log (N : ℝ)⌋₊ : ℝ) := by
        exact_mod_cast hpData.2.1
      exact hpFloorR.trans (by
        simpa [logScale] using
          (Nat.floor_le (show 0 ≤ 40 * Real.log (N : ℝ) by positivity)))
    have hbaseR : (base.base : ℝ) ≤ 100 * (KSafe N : ℝ) := by
      exact_mod_cast base.upper
    calc
      (d : ℝ) = (base.base : ℝ) * p := by simp [d]
      _ ≤ (100 * (KSafe N : ℝ)) * (40 * logScale N) := by
        exact mul_le_mul hbaseR hpUpper (Nat.cast_nonneg _) (by positivity)
      _ = 4000 * (KSafe N : ℝ) * logScale N := by ring
  · rw [card_primeFactors_eq_omega]
    calc
      ω d = ω base.base + 1 := by simpa [d] using hdomega
      _ ≤ 4 + 1 := Nat.add_le_add_right base.distinct 1
      _ = 5 := by norm_num
  · exact hdSmooth
  · exact hdExp
  · dsimp [d]
    rw [hdOmega]
    exact (Nat.add_le_add_right base.factors 2).trans hbudget

/-- The exceptional part of `A_{qp}` relative to a proposed nearby set
`Uq`. -/
def badPrimeFiber (A Uq : Finset ℕ) (q p : ℕ) : Finset ℕ :=
  divisiblePart A (q * p) \ Uq

lemma badPrimeFiber_subset_divisiblePart_sdiff (A Uq : Finset ℕ)
    (q p : ℕ) :
    badPrimeFiber A Uq q p ⊆
      divisiblePart (divisiblePart A q \ Uq) p := by
  intro n hn
  rw [badPrimeFiber, Finset.mem_sdiff, mem_divisiblePart] at hn
  rw [mem_divisiblePart, Finset.mem_sdiff, mem_divisiblePart]
  exact ⟨⟨⟨hn.1.1, dvd_trans (dvd_mul_right q p) hn.1.2⟩, hn.2⟩,
    dvd_trans (dvd_mul_left p q) hn.1.2⟩

/-- Exact incidence budget for the repaired `p'` averaging. -/
lemma sum_card_badPrimeFiber_le {A Uq : Finset ℕ} {q X F : ℕ}
    (hA0 : ∀ n ∈ A, n ≠ 0) (hAF : ∀ n ∈ A, Ω n ≤ F) :
    ∑ p ∈ smallPrimeCandidates X q,
        (badPrimeFiber A Uq q p).card ≤
      (divisiblePart A q \ Uq).card * F := by
  calc
    ∑ p ∈ smallPrimeCandidates X q, (badPrimeFiber A Uq q p).card ≤
        ∑ p ∈ smallPrimeCandidates X q,
          (divisiblePart (divisiblePart A q \ Uq) p).card := by
      apply Finset.sum_le_sum
      intro p hp
      exact Finset.card_le_card
        (badPrimeFiber_subset_divisiblePart_sdiff A Uq q p)
    _ ≤ (divisiblePart A q \ Uq).card * F := by
      apply sum_card_divisiblePart_primes_le
      · intro p hp
        exact (mem_smallPrimeCandidates.mp hp).2.2.1
      · intro n hn
        exact hA0 n (mem_divisiblePart.mp (Finset.mem_sdiff.mp hn).1).1
      · intro n hn
        exact hAF n (mem_divisiblePart.mp (Finset.mem_sdiff.mp hn).1).1

/-- Exact pigeonhole form of the repaired averaging step. -/
lemma exists_smallPrimeCandidate_badFiber_le {A Uq : Finset ℕ}
    {q X F B : ℕ}
    (hA0 : ∀ n ∈ A, n ≠ 0) (hAF : ∀ n ∈ A, Ω n ≤ F)
    (hbudget : (divisiblePart A q \ Uq).card * F <
      (smallPrimeCandidates X q).card * (B + 1)) :
    ∃ p ∈ smallPrimeCandidates X q,
      (badPrimeFiber A Uq q p).card ≤ B := by
  by_contra h
  push_neg at h
  have hlower : (smallPrimeCandidates X q).card * (B + 1) ≤
      ∑ p ∈ smallPrimeCandidates X q,
        (badPrimeFiber A Uq q p).card := by
    calc
      (smallPrimeCandidates X q).card * (B + 1) =
          ∑ p ∈ smallPrimeCandidates X q, (B + 1) := by simp
      _ ≤ _ := Finset.sum_le_sum fun p hp ↦ h p hp
  exact (not_le_of_gt hbudget)
    (hlower.trans (sum_card_badPrimeFiber_le hA0 hAF))

/-- Auxiliary primes which are fresh for `d` and whose entire `A_{dp}`
fiber lies in `Uq`. -/
def eligibleAuxiliaryPrimes (P A Uq : Finset ℕ) (d : ℕ) : Finset ℕ :=
  P.filter fun p ↦ p.Coprime d ∧ divisiblePart A (d * p) ⊆ Uq

@[simp] lemma mem_eligibleAuxiliaryPrimes {P A Uq : Finset ℕ} {d p : ℕ} :
    p ∈ eligibleAuxiliaryPrimes P A Uq d ↔
      p ∈ P ∧ p.Coprime d ∧ divisiblePart A (d * p) ⊆ Uq := by
  simp [eligibleAuxiliaryPrimes]

lemma eligibleAuxiliaryPrimes_subset (P A Uq : Finset ℕ) (d : ℕ) :
    eligibleAuxiliaryPrimes P A Uq d ⊆ P :=
  Finset.filter_subset _ _

lemma auxiliaryPrimes_sdiff_subset_divisorPrimes
    (P A Uq : Finset ℕ) (d : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    P \ eligibleAuxiliaryPrimes P A Uq d ⊆
      divisorPrimes P (divisiblePart A d \ Uq) ∪ divisorPrimes P {d} := by
  intro p hp
  rw [Finset.mem_sdiff] at hp
  have hpP := hp.1
  have hpNot : ¬(p.Coprime d ∧ divisiblePart A (d * p) ⊆ Uq) := by
    intro hpEligible
    exact hp.2 (mem_eligibleAuxiliaryPrimes.mpr
      ⟨hpP, hpEligible.1, hpEligible.2⟩)
  rw [Finset.mem_union]
  by_cases hcop : p.Coprime d
  · left
    have hnsub : ¬divisiblePart A (d * p) ⊆ Uq :=
      fun hsub ↦ hpNot ⟨hcop, hsub⟩
    obtain ⟨n, hnPart, hnU⟩ := SetLike.not_le_iff_exists.mp hnsub
    rw [divisorPrimes, Finset.mem_filter]
    exact ⟨hpP, n, Finset.mem_sdiff.mpr
      ⟨mem_divisiblePart.mpr
        ⟨(mem_divisiblePart.mp hnPart).1,
          dvd_trans (dvd_mul_right d p) (mem_divisiblePart.mp hnPart).2⟩,
        hnU⟩,
      dvd_trans (dvd_mul_left p d) (mem_divisiblePart.mp hnPart).2⟩
  · right
    rw [divisorPrimes, Finset.mem_filter]
    refine ⟨hpP, d, Finset.mem_singleton.mpr rfl, ?_⟩
    by_contra hpd
    exact hcop ((hP p hpP).coprime_iff_not_dvd.mpr hpd)

/-- The number of auxiliary primes removed is at most the bad-incidence
budget plus the multiplicity budget for the base. -/
lemma card_auxiliaryPrimes_sdiff_le {P A Uq : Finset ℕ} {d F B R : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hA0 : ∀ n ∈ A, n ≠ 0)
    (hAF : ∀ n ∈ A, Ω n ≤ F) (hd0 : d ≠ 0) (hdR : Ω d ≤ R)
    (hbad : (divisiblePart A d \ Uq).card ≤ B) :
    (P \ eligibleAuxiliaryPrimes P A Uq d).card ≤ F * B + R := by
  have hE0 : ∀ n ∈ divisiblePart A d \ Uq, n ≠ 0 := by
    intro n hn
    exact hA0 n (mem_divisiblePart.mp (Finset.mem_sdiff.mp hn).1).1
  have hEF : ∀ n ∈ divisiblePart A d \ Uq, Ω n ≤ F := by
    intro n hn
    exact hAF n (mem_divisiblePart.mp (Finset.mem_sdiff.mp hn).1).1
  calc
    (P \ eligibleAuxiliaryPrimes P A Uq d).card ≤
        (divisorPrimes P (divisiblePart A d \ Uq) ∪
          divisorPrimes P {d}).card :=
      Finset.card_le_card
        (auxiliaryPrimes_sdiff_subset_divisorPrimes P A Uq d hP)
    _ ≤ (divisorPrimes P (divisiblePart A d \ Uq)).card +
          (divisorPrimes P {d}).card :=
      Finset.card_union_le (divisorPrimes P (divisiblePart A d \ Uq))
        (divisorPrimes P {d})
    _ ≤ (divisiblePart A d \ Uq).card * F + 1 * R :=
      Nat.add_le_add (card_divisorPrimes_le hP hE0 hEF)
        (card_divisorPrimes_le hP (by simpa using hd0) (by simpa using hdR))
    _ ≤ B * F + R := by
      exact Nat.add_le_add (Nat.mul_le_mul_right F hbad) (by simp)
    _ = F * B + R := by ac_rfl

/-- A tenfold margin in the common interval leaves at least ninety percent
of its primes eligible. -/
lemma nine_mul_card_le_ten_mul_card_eligibleAuxiliaryPrimes
    {P A Uq : Finset ℕ} {d F B R : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hA0 : ∀ n ∈ A, n ≠ 0)
    (hAF : ∀ n ∈ A, Ω n ≤ F) (hd0 : d ≠ 0) (hdR : Ω d ≤ R)
    (hbad : (divisiblePart A d \ Uq).card ≤ B)
    (hdensity : 10 * (F * B + R) ≤ P.card) :
    9 * P.card ≤
      10 * (eligibleAuxiliaryPrimes P A Uq d).card := by
  have hexcl := card_auxiliaryPrimes_sdiff_le hP hA0 hAF hd0 hdR hbad
  have hsubset := eligibleAuxiliaryPrimes_subset P A Uq d
  have hsplit :
      (P \ eligibleAuxiliaryPrimes P A Uq d).card +
          (eligibleAuxiliaryPrimes P A Uq d).card = P.card := by
    exact Finset.card_sdiff_add_card_eq_card hsubset
  omega

end

end Erdos297.AuxiliarySupply
