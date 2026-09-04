import ErdosProblems.Erdos387.AnalyticInputs
import ErdosProblems.Erdos980.ElliottTail.NumberFieldLargerSieve
import ErdosProblems.Erdos980.ElliottTail.OddMediumParameters
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.Primorial
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Inert auxiliary primes for odd-prime conductors

For a fixed prime `ell`, choose a generator of `(ZMod ell)ˣ`, and let `a` be its
standard natural representative.  This file packages the primes

`q < t`,  `q ≡ a (mod ell)`.

Their residue class has order `ell - 1`.  Consequently `q` is inert in every
cyclotomic field `K = ℚ(ζ_ell)`: the extended ideal `(q)` in `𝓞 K` is prime,
its inertia degree is `ell - 1`, and its residue field has cardinality
`q ^ (ell - 1)`.  The unit group of this field is cyclic and has cardinality
divisible by `ell`.

The fixed-modulus PNT also gives a positive multiple of `t / log t` such
primes, while Chebyshev's primorial bound controls their product by `4 ^ t`.
-/

open scoped BigOperators NumberField

namespace Erdos980.ElliottTail.OddInertAuxiliaryPrimes

open Filter Finset Real NumberField Ideal IsCyclotomicExtension

noncomputable section

variable (ell : ℕ) [Fact ell.Prime]

/-! ## The primitive residue class -/

/-- A fixed generator of the cyclic group `(ZMod ell)ˣ`. -/
noncomputable def inertResidueUnit : (ZMod ell)ˣ :=
  Classical.choose
    (isCyclic_iff_exists_orderOf_eq_natCard.mp
      (ZMod.isCyclic_units_prime (Fact.out : ell.Prime)))

/-- The chosen generator has full order `ell - 1`. -/
theorem inertResidueUnit_order : orderOf (inertResidueUnit ell) = ell - 1 := by
  calc
    orderOf (inertResidueUnit ell) = Nat.card (ZMod ell)ˣ :=
      Classical.choose_spec
        (isCyclic_iff_exists_orderOf_eq_natCard.mp
          (ZMod.isCyclic_units_prime (Fact.out : ell.Prime)))
    _ = Fintype.card (ZMod ell)ˣ := Nat.card_eq_fintype_card
    _ = ell - 1 := ZMod.card_units ell

/-- The standard natural representative of the chosen primitive unit. -/
def inertResidue : ℕ := ((inertResidueUnit ell : (ZMod ell)ˣ) : ZMod ell).val

theorem inertResidue_lt : inertResidue ell < ell := ZMod.val_lt _

theorem inertResidue_coprime : Nat.Coprime (inertResidue ell) ell :=
  ZMod.val_coe_unit_coprime (inertResidueUnit ell)

theorem inertResidue_order :
    orderOf (inertResidue ell : ZMod ell) = ell - 1 := by
  have hv : (inertResidue ell : ZMod ell) = (inertResidueUnit ell : ZMod ell) := by
    simp [inertResidue]
  rw [hv]
  exact (orderOf_injective (Units.coeHom (ZMod ell)) Units.val_injective
    (inertResidueUnit ell)).trans (inertResidueUnit_order ell)

theorem zmod_order_eq_sub_one_of_modEq {q : ℕ}
    (hq : q % ell = inertResidue ell) :
    orderOf (q : ZMod ell) = ell - 1 := by
  have hcast : (q : ZMod ell) = (inertResidue ell : ZMod ell) := by
    rw [← ZMod.natCast_mod q ell, hq]
  rw [hcast]
  exact inertResidue_order ell

/-! ## The finite family -/

/-- Primes below `t` in the fixed primitive residue class modulo `ell`. -/
def inertAuxiliaryPrimes (t : ℕ) : Finset ℕ :=
  (Finset.range t).filter fun q =>
    q.Prime ∧ q % ell = inertResidue ell

@[simp] theorem mem_inertAuxiliaryPrimes {t q : ℕ} :
    q ∈ inertAuxiliaryPrimes ell t ↔
      q < t ∧ q.Prime ∧ q % ell = inertResidue ell := by
  simp [inertAuxiliaryPrimes]

theorem inertAuxiliaryPrimes_prime {t q : ℕ}
    (hq : q ∈ inertAuxiliaryPrimes ell t) : q.Prime :=
  ((mem_inertAuxiliaryPrimes (ell := ell)).mp hq).2.1

theorem inertAuxiliaryPrimes_lt {t q : ℕ}
    (hq : q ∈ inertAuxiliaryPrimes ell t) : q < t :=
  ((mem_inertAuxiliaryPrimes (ell := ell)).mp hq).1

theorem inertAuxiliaryPrimes_modEq {t q : ℕ}
    (hq : q ∈ inertAuxiliaryPrimes ell t) :
    q % ell = inertResidue ell :=
  ((mem_inertAuxiliaryPrimes (ell := ell)).mp hq).2.2

theorem coprime_ell_of_modEq {q : ℕ}
    (hqmod : q % ell = inertResidue ell) : Nat.Coprime q ell := by
  rw [Nat.coprime_comm, Nat.coprime_iff_gcd_eq_one, Nat.gcd_rec, hqmod]
  exact inertResidue_coprime ell

theorem inertAuxiliaryPrimes_ne_ell {t q : ℕ}
    (hq : q ∈ inertAuxiliaryPrimes ell t) : q ≠ ell := by
  intro h
  subst q
  exact ((Fact.out : ell.Prime).coprime_iff_not_dvd.mp
    (coprime_ell_of_modEq ell (inertAuxiliaryPrimes_modEq ell hq))) dvd_rfl

theorem inertAuxiliaryPrimes_coprime_ell {t q : ℕ}
    (hq : q ∈ inertAuxiliaryPrimes ell t) : Nat.Coprime q ell :=
  coprime_ell_of_modEq ell (inertAuxiliaryPrimes_modEq ell hq)

theorem inertAuxiliaryPrimes_coprime_ell_pow {t q n : ℕ}
    (hq : q ∈ inertAuxiliaryPrimes ell t) : Nat.Coprime q (ell ^ n) :=
  (inertAuxiliaryPrimes_coprime_ell ell hq).pow_right n

theorem inertAuxiliaryPrimes_coprime_primaryRaySupport {t q : ℕ}
    (hq : q ∈ inertAuxiliaryPrimes ell t) :
    Nat.Coprime q (ell ^ (2 * ell)) :=
  inertAuxiliaryPrimes_coprime_ell_pow ell hq

theorem inertAuxiliaryPrimes_pairwise_coprime (t : ℕ) :
    (inertAuxiliaryPrimes ell t : Set ℕ).Pairwise Nat.Coprime := by
  intro q hq r hr hne
  have hqprime := inertAuxiliaryPrimes_prime ell hq
  have hrprime := inertAuxiliaryPrimes_prime ell hr
  rw [hqprime.coprime_iff_not_dvd]
  intro hdiv
  rcases (Nat.dvd_prime hrprime).mp hdiv with hq1 | hqr
  · exact hqprime.ne_one hq1
  · exact hne hqr

theorem inertAuxiliaryPrimes_mono {s t : ℕ} (hst : s ≤ t) :
    inertAuxiliaryPrimes ell s ⊆ inertAuxiliaryPrimes ell t := by
  intro q hq
  rw [mem_inertAuxiliaryPrimes] at hq ⊢
  exact ⟨hq.1.trans_le hst, hq.2⟩

/-! ## Canonical tensor-sized subfamily -/

/-- The least `oddTensorDepth t` inert auxiliary primes below `t`, or all
available ones when there are fewer.  Sorting makes this choice canonical. -/
def selectedInertAuxiliaryPrimes (t : ℕ) : Finset ℕ :=
  (((inertAuxiliaryPrimes ell t).sort (· ≤ ·)).take
    (OddMediumParameters.oddTensorDepth t)).toFinset

theorem selectedInertAuxiliaryPrimes_subset (t : ℕ) :
    selectedInertAuxiliaryPrimes ell t ⊆ inertAuxiliaryPrimes ell t := by
  intro q hq
  have hqTake :
      q ∈ ((inertAuxiliaryPrimes ell t).sort (· ≤ ·)).take
        (OddMediumParameters.oddTensorDepth t) := by
    simpa [selectedInertAuxiliaryPrimes] using hq
  exact (Finset.mem_sort (· ≤ ·)).mp (List.mem_of_mem_take hqTake)

theorem selectedInertAuxiliaryPrimes_card_le (t : ℕ) :
    (selectedInertAuxiliaryPrimes ell t).card ≤
      OddMediumParameters.oddTensorDepth t := by
  rw [selectedInertAuxiliaryPrimes,
    List.toFinset_card_of_nodup
      ((inertAuxiliaryPrimes ell t).sort_nodup (· ≤ ·)).take,
    List.length_take, (inertAuxiliaryPrimes ell t).length_sort]
  exact Nat.min_le_left _ _

theorem selectedInertAuxiliaryPrimes_card
    (havailable : OddMediumParameters.oddTensorDepth t ≤
      (inertAuxiliaryPrimes ell t).card) :
    (selectedInertAuxiliaryPrimes ell t).card =
      OddMediumParameters.oddTensorDepth t := by
  rw [selectedInertAuxiliaryPrimes,
    List.toFinset_card_of_nodup
      ((inertAuxiliaryPrimes ell t).sort_nodup (· ≤ ·)).take,
    List.length_take, (inertAuxiliaryPrimes ell t).length_sort]
  exact Nat.min_eq_left havailable

theorem selectedInertAuxiliaryPrimes_prime {t q : ℕ}
    (hq : q ∈ selectedInertAuxiliaryPrimes ell t) : q.Prime :=
  inertAuxiliaryPrimes_prime ell (selectedInertAuxiliaryPrimes_subset ell t hq)

theorem selectedInertAuxiliaryPrimes_lt {t q : ℕ}
    (hq : q ∈ selectedInertAuxiliaryPrimes ell t) : q < t :=
  inertAuxiliaryPrimes_lt ell (selectedInertAuxiliaryPrimes_subset ell t hq)

theorem selectedInertAuxiliaryPrimes_modEq {t q : ℕ}
    (hq : q ∈ selectedInertAuxiliaryPrimes ell t) :
    q % ell = inertResidue ell :=
  inertAuxiliaryPrimes_modEq ell (selectedInertAuxiliaryPrimes_subset ell t hq)

theorem selectedInertAuxiliaryPrimes_coprime_primaryRaySupport {t q : ℕ}
    (hq : q ∈ selectedInertAuxiliaryPrimes ell t) :
    Nat.Coprime q (ell ^ (2 * ell)) :=
  inertAuxiliaryPrimes_coprime_primaryRaySupport ell
    (selectedInertAuxiliaryPrimes_subset ell t hq)

theorem selectedInertAuxiliaryPrimes_pairwise_coprime (t : ℕ) :
    (selectedInertAuxiliaryPrimes ell t : Set ℕ).Pairwise Nat.Coprime :=
  (inertAuxiliaryPrimes_pairwise_coprime ell t).mono
    (selectedInertAuxiliaryPrimes_subset ell t)

/-! ## Product bound -/

theorem inertAuxiliaryPrimes_subset_primesLE (t : ℕ) :
    inertAuxiliaryPrimes ell t ⊆ Nat.primesLE t := by
  intro q hq
  exact Nat.mem_primesLE.mpr
    ⟨(inertAuxiliaryPrimes_lt ell hq).le,
      inertAuxiliaryPrimes_prime ell hq⟩

theorem inertAuxiliaryPrimes_prod_le_four_pow (t : ℕ) :
    (inertAuxiliaryPrimes ell t).prod id ≤ 4 ^ t := by
  calc
    (inertAuxiliaryPrimes ell t).prod id ≤ (Nat.primesLE t).prod id := by
      apply Finset.prod_le_prod_of_subset_of_one_le
        (inertAuxiliaryPrimes_subset_primesLE ell t)
      · intro q hq
        exact Nat.zero_le q
      · intro q hq _
        exact (Nat.mem_primesLE.mp hq).2.one_le
    _ = primorial t := (primorial_eq_prod_primesLE t).symm
    _ ≤ 4 ^ t := primorial_le_four_pow t

theorem selectedInertAuxiliaryPrimes_prod_le_four_pow (t : ℕ) :
    (selectedInertAuxiliaryPrimes ell t).prod id ≤ 4 ^ t := by
  calc
    (selectedInertAuxiliaryPrimes ell t).prod id ≤
        (inertAuxiliaryPrimes ell t).prod id := by
      apply Finset.prod_le_prod_of_subset_of_one_le
        (selectedInertAuxiliaryPrimes_subset ell t)
      · intro q hq
        exact Nat.zero_le q
      · intro q hq _
        exact (inertAuxiliaryPrimes_prime ell hq).one_le
    _ ≤ 4 ^ t := inertAuxiliaryPrimes_prod_le_four_pow ell t

theorem selectedInertAuxiliaryPrimes_prod_le_modulusBound (t : ℕ) :
    (selectedInertAuxiliaryPrimes ell t).prod id ≤
      OddMediumParameters.oddAuxiliaryModulusBound t := by
  apply OddMediumParameters.prod_auxiliaryPrimes_le_modulusBound
    (selectedInertAuxiliaryPrimes ell t)
    (selectedInertAuxiliaryPrimes_card_le ell t)
  intro q hq
  exact (selectedInertAuxiliaryPrimes_lt ell hq).le

/-! ## Fixed-modulus PNT lower bound -/

/-- The dyadic subfamily in `((t-1)/2, t-1]`. -/
def inertAuxiliaryDyadicPrimes (t : ℕ) : Finset ℕ :=
  Erdos387.primeIntervalAP ell (inertResidue ell)
    (((t - 1 : ℕ) : ℝ) / 2) ((t - 1 : ℕ) : ℝ)

theorem inertAuxiliaryDyadicPrimes_subset (t : ℕ) :
    inertAuxiliaryDyadicPrimes ell t ⊆ inertAuxiliaryPrimes ell t := by
  intro q hq
  rw [inertAuxiliaryDyadicPrimes, Erdos387.primeIntervalAP] at hq
  simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.floor_natCast] at hq
  rw [mem_inertAuxiliaryPrimes]
  exact ⟨by omega, hq.2⟩

/-- An explicit positive lower-density constant for the fixed progression. -/
def inertAuxiliaryPrimeDensity : ℝ :=
  1 / (8 * Nat.totient ell : ℝ)

theorem inertAuxiliaryPrimeDensity_pos : 0 < inertAuxiliaryPrimeDensity ell := by
  have hφ : 0 < Nat.totient ell := Nat.totient_pos.mpr (Fact.out : ell.Prime).pos
  unfold inertAuxiliaryPrimeDensity
  positivity

private theorem tendsto_half_pred_atTop :
    Tendsto (fun t : ℕ => ((t - 1 : ℕ) : ℝ) / 2) atTop atTop := by
  have hpred : Tendsto (fun t : ℕ => t - 1) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro n
    refine ⟨n + 1, ?_⟩
    intro b hb
    omega
  exact (tendsto_natCast_atTop_atTop.comp hpred).atTop_div_const (by norm_num)

/-- There are eventually at least
`inertAuxiliaryPrimeDensity ell * t / log t` inert auxiliary primes below `t`. -/
theorem eventually_inertAuxiliaryPrimeDensity_mul_div_log_le_card :
    ∀ᶠ t : ℕ in atTop,
      inertAuxiliaryPrimeDensity ell * (t : ℝ) / Real.log (t : ℝ) ≤
        ((inertAuxiliaryPrimes ell t).card : ℝ) := by
  let a := inertResidue ell
  have hM : 1 ≤ ell := (Fact.out : ell.Prime).pos
  have haM : a < ell := inertResidue_lt ell
  have hacop : Nat.Coprime a ell := inertResidue_coprime ell
  obtain ⟨x₀, hx₀, hPNT⟩ :=
    Erdos387.PNT_fixed_modulus ell a hM haM hacop
      1 (by norm_num) (1 / 2) (by norm_num)
  have hxevent : ∀ᶠ t : ℕ in atTop,
      x₀ ≤ ((t - 1 : ℕ) : ℝ) / 2 :=
    tendsto_half_pred_atTop.eventually (eventually_ge_atTop x₀)
  filter_upwards [hxevent, eventually_ge_atTop 5] with t htx ht5
  let y : ℝ := ((t - 1 : ℕ) : ℝ) / 2
  have hy3 : 3 ≤ y := hx₀.trans htx
  have hypos : 0 < y := by linarith
  have htpos : 0 < (t : ℝ) := by positivity
  have ht1 : 1 ≤ t := by omega
  have hcastpred : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
    simpa using (Nat.cast_sub (R := ℝ) ht1)
  have htwo_y : 2 * y = ((t - 1 : ℕ) : ℝ) := by
    dsimp [y]
    ring
  have hyv : y < ((t - 1 : ℕ) : ℝ) := by
    rw [← htwo_y]
    linarith
  have hlen : (1 : ℝ) * y ≤ ((t - 1 : ℕ) : ℝ) - y := by
    rw [← htwo_y]
    linarith
  have hestimate := hPNT y htx y ((t - 1 : ℕ) : ℝ)
    le_rfl hyv (by rw [htwo_y]) hlen
  change
    |((inertAuxiliaryDyadicPrimes ell t).card : ℝ) -
        (((t - 1 : ℕ) : ℝ) - y) /
          ((Nat.totient ell : ℝ) * Real.log y)| ≤
      (1 / 2 : ℝ) * (((t - 1 : ℕ) : ℝ) - y) /
        ((Nat.totient ell : ℝ) * Real.log y) at hestimate
  have hφnat : 0 < Nat.totient ell := Nat.totient_pos.mpr (Fact.out : ell.Prime).pos
  have hφ : (0 : ℝ) < Nat.totient ell := by exact_mod_cast hφnat
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hmain :
      (((t - 1 : ℕ) : ℝ) - y) /
          ((Nat.totient ell : ℝ) * Real.log y) =
        y / ((Nat.totient ell : ℝ) * Real.log y) := by
    rw [← htwo_y]
    ring
  rw [hmain] at hestimate
  have hlower :
      y / (2 * ((Nat.totient ell : ℝ) * Real.log y)) ≤
        ((inertAuxiliaryDyadicPrimes ell t).card : ℝ) := by
    have hneg := (abs_le.mp hestimate).1
    have herr : (1 / 2 : ℝ) * (((t - 1 : ℕ) : ℝ) - y) /
        ((Nat.totient ell : ℝ) * Real.log y) =
      y / (2 * ((Nat.totient ell : ℝ) * Real.log y)) := by
      rw [← htwo_y]
      ring
    rw [herr] at hneg
    have htwice :
        y / ((Nat.totient ell : ℝ) * Real.log y) =
          2 * (y / (2 * ((Nat.totient ell : ℝ) * Real.log y))) := by
      ring
    rw [htwice] at hneg
    linarith
  have hyt : (t : ℝ) / 4 ≤ y := by
    have hyformula : y = ((t : ℝ) - 1) / 2 := by
      dsimp [y]
      rw [hcastpred]
    rw [hyformula]
    linarith
  have hy_le_t : y ≤ (t : ℝ) := by
    have hyformula : y = ((t : ℝ) - 1) / 2 := by
      dsimp [y]
      rw [hcastpred]
    rw [hyformula]
    linarith
  have hlogt : 0 < Real.log (t : ℝ) := Real.log_pos (by norm_num; omega)
  have hlogle : Real.log y ≤ Real.log (t : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hypos htpos hy_le_t
  have hcompare :
      inertAuxiliaryPrimeDensity ell * (t : ℝ) / Real.log (t : ℝ) ≤
        y / (2 * ((Nat.totient ell : ℝ) * Real.log y)) := by
    rw [inertAuxiliaryPrimeDensity]
    have hleft :
        (1 / (8 * (Nat.totient ell : ℝ))) * (t : ℝ) /
            Real.log (t : ℝ) =
          (t : ℝ) /
            (8 * (Nat.totient ell : ℝ) * Real.log (t : ℝ)) := by
      ring
    rw [hleft]
    calc
      (t : ℝ) / (8 * (Nat.totient ell : ℝ) * Real.log (t : ℝ)) ≤
          y / (2 * (Nat.totient ell : ℝ) * Real.log (t : ℝ)) := by
        have hfactor :
            0 < 2 * (Nat.totient ell : ℝ) * Real.log (t : ℝ) := by
          positivity
        have hrewrite :
            (t : ℝ) /
                (8 * (Nat.totient ell : ℝ) * Real.log (t : ℝ)) =
              ((t : ℝ) / 4) /
                (2 * (Nat.totient ell : ℝ) * Real.log (t : ℝ)) := by
          ring
        rw [hrewrite]
        exact (div_le_div_iff_of_pos_right hfactor).2 hyt
      _ ≤ y / (2 * ((Nat.totient ell : ℝ) * Real.log y)) := by
        apply div_le_div_of_nonneg_left hypos.le (by positivity)
        nlinarith
  exact hcompare.trans (hlower.trans (by
    exact_mod_cast Finset.card_le_card
      (inertAuxiliaryDyadicPrimes_subset ell t)))

/-- After deleting any fixed finite set of auxiliary primes, the inert
progression still eventually supplies all coordinates required by the
logarithmic tensor depth. -/
theorem eventually_add_oddTensorDepth_le_inertAuxiliaryPrimes_card (B : ℕ) :
    ∀ᶠ t : ℕ in atTop,
      B + OddMediumParameters.oddTensorDepth t ≤
        (inertAuxiliaryPrimes ell t).card := by
  have hconstant : 0 < inertAuxiliaryPrimeDensity ell / 64 :=
    div_pos (inertAuxiliaryPrimeDensity_pos ell) (by norm_num)
  have hlogSquareSmall :
      ∀ᶠ t : ℕ in atTop,
        ‖Real.log (t : ℝ) ^ 2‖ ≤
          (inertAuxiliaryPrimeDensity ell / 64) * ‖(t : ℝ)‖ :=
    ((Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
      tendsto_natCast_atTop_atTop).bound hconstant
  have hBLog :
      ∀ᶠ t : ℕ in atTop, (B : ℝ) ≤ 16 * Real.log (t : ℝ) :=
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      (by norm_num : (0 : ℝ) < 16)).eventually
        (eventually_ge_atTop (B : ℝ))
  filter_upwards
      [eventually_inertAuxiliaryPrimeDensity_mul_div_log_le_card ell,
        hlogSquareSmall, hBLog, eventually_ge_atTop 4]
      with t hdensity hlogSquare hB ht
  have htpos : (0 : ℝ) < t := by positivity
  have hlogt : 0 < Real.log (t : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < t by omega))
  have hclog :
      Nat.clog 2 (t + 1) ≤ 2 * Nat.log 2 (t + 1) := by
    have h₁ : Nat.clog 2 (t + 1) ≤ Nat.log 2 (t + 1) + 1 :=
      Nat.clog_le_of_le_pow
        (le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) (t + 1)))
    have h₂ : 1 ≤ Nat.log 2 (t + 1) :=
      Nat.log_pos (by norm_num) (by omega)
    omega
  have hdepthNat :
      OddMediumParameters.oddTensorDepth t ≤
        8 * Nat.log 2 (t + 1) := by
    simp only [OddMediumParameters.oddTensorDepth]
    omega
  have hnatLog :
      (Nat.log 2 (t + 1) : ℝ) ≤
        Real.log ((t + 1 : ℕ) : ℝ) / Real.log 2 := by
    simpa [Real.logb] using Real.natLog_le_logb (t + 1) 2
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwoHalf : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlogSuccPos : 0 < Real.log ((t + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < t + 1 by omega))
  have hdivLog :
      Real.log ((t + 1 : ℕ) : ℝ) / Real.log 2 ≤
        2 * Real.log ((t + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hlogTwoPos]
    nlinarith
  have hsuccLeSq : t + 1 ≤ t ^ 2 := by nlinarith
  have hlogSucc :
      Real.log ((t + 1 : ℕ) : ℝ) ≤ 2 * Real.log (t : ℝ) := by
    calc
      Real.log ((t + 1 : ℕ) : ℝ) ≤ Real.log ((t : ℝ) ^ 2) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast hsuccLeSq
      _ = 2 * Real.log (t : ℝ) := by
        rw [Real.log_pow]
        norm_num
  have hdepthReal :
      (OddMediumParameters.oddTensorDepth t : ℝ) ≤
        32 * Real.log (t : ℝ) := by
    calc
      (OddMediumParameters.oddTensorDepth t : ℝ) ≤
          (8 * Nat.log 2 (t + 1) : ℕ) := by exact_mod_cast hdepthNat
      _ = 8 * (Nat.log 2 (t + 1) : ℝ) := by norm_num
      _ ≤ 8 * (Real.log ((t + 1 : ℕ) : ℝ) / Real.log 2) := by
        gcongr
      _ ≤ 8 * (2 * Real.log ((t + 1 : ℕ) : ℝ)) := by
        gcongr
      _ ≤ 32 * Real.log (t : ℝ) := by nlinarith
  have hlogSquare :
      Real.log (t : ℝ) ^ 2 ≤
        (inertAuxiliaryPrimeDensity ell / 64) * (t : ℝ) := by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (Real.log (t : ℝ))),
      Real.norm_eq_abs, abs_of_pos htpos] at hlogSquare
    exact hlogSquare
  have htotalReal :
      ((B + OddMediumParameters.oddTensorDepth t : ℕ) : ℝ) ≤
        64 * Real.log (t : ℝ) := by
    push_cast
    linarith
  have htotalLeDensity :
      64 * Real.log (t : ℝ) ≤
        inertAuxiliaryPrimeDensity ell * (t : ℝ) /
          Real.log (t : ℝ) := by
    rw [le_div_iff₀ hlogt]
    calc
      64 * Real.log (t : ℝ) * Real.log (t : ℝ) =
          64 * Real.log (t : ℝ) ^ 2 := by ring
      _ ≤ 64 * ((inertAuxiliaryPrimeDensity ell / 64) * (t : ℝ)) := by
        gcongr
      _ = inertAuxiliaryPrimeDensity ell * (t : ℝ) := by ring
  exact_mod_cast htotalReal.trans (htotalLeDensity.trans hdensity)

/-- Eventually the fixed inert progression supplies all coordinates required
by the logarithmic tensor depth used in the odd-prime medium sieve. -/
theorem eventually_oddTensorDepth_le_inertAuxiliaryPrimes_card :
    ∀ᶠ t : ℕ in atTop,
      OddMediumParameters.oddTensorDepth t ≤
        (inertAuxiliaryPrimes ell t).card := by
  simpa using
    (eventually_add_oddTensorDepth_le_inertAuxiliaryPrimes_card ell 0)

/-- The canonical selected inert family eventually has exactly the requested
tensor depth. -/
theorem eventually_selectedInertAuxiliaryPrimes_card :
    ∀ᶠ t : ℕ in atTop,
      (selectedInertAuxiliaryPrimes ell t).card =
        OddMediumParameters.oddTensorDepth t := by
  filter_upwards [eventually_oddTensorDepth_le_inertAuxiliaryPrimes_card ell]
    with t ht
  exact selectedInertAuxiliaryPrimes_card ell ht

/-! ## Inertness in the prime-conductor cyclotomic field -/

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {ell} ℚ K]

/-- An auxiliary prime is coprime, in `𝓞 K`, to the cyclotomic prime
generated by `ζ_ell - 1`.  This is the correction/ray-support avoidance
property used by primary-generator constructions. -/
theorem inertAuxiliaryPrimes_coprime_zetaSubOne {t q : ℕ}
    (hq : q ∈ inertAuxiliaryPrimes ell t) :
    Ideal.span {(q : 𝓞 K)} ⊔
        Ideal.span {((IsCyclotomicExtension.zeta_spec ell ℚ K).toInteger - 1)} = ⊤ := by
  let hζ := IsCyclotomicExtension.zeta_spec ell ℚ K
  let P : Ideal (𝓞 K) := Ideal.span {hζ.toInteger - 1}
  let Q : Ideal (𝓞 K) := Ideal.span {(q : 𝓞 K)}
  have hnotNat : ¬ ell ∣ q :=
    (Fact.out : ell.Prime).coprime_iff_not_dvd.mp
      (inertAuxiliaryPrimes_coprime_ell ell hq).symm
  have hnotInt : ¬ (ell : ℤ) ∣ (q : ℤ) := by
    exact_mod_cast hnotNat
  have hnotZeta : ¬ hζ.toInteger - 1 ∣ (q : 𝓞 K) := by
    intro hdiv
    apply hnotInt
    exact (IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff'
      ell hζ).mp (by simpa using hdiv)
  have hnotMem : (q : 𝓞 K) ∉ P := by
    simpa [P, Ideal.mem_span_singleton] using hnotZeta
  have hPprime : P.IsPrime := by
    simpa [P] using
      (Ideal.isPrime_span_singleton_of_prime hζ.zeta_sub_one_prime')
  have hPne : P ≠ ⊥ := by
    simpa [P, Ideal.span_singleton_eq_bot] using hζ.zeta_sub_one_prime'.ne_zero
  have hPmax : P.IsMaximal := hPprime.isMaximal hPne
  have hsup : P ⊔ Q = ⊤ := by
    by_contra hsupne
    have hEq : P = P ⊔ Q := hPmax.eq_of_le hsupne le_sup_left
    have hQP : Q ≤ P := le_sup_right.trans_eq hEq.symm
    exact hnotMem (hQP (by simp [Q]))
  simpa [P, Q, hζ, sup_comm] using hsup

theorem selectedInertAuxiliaryPrimes_coprime_zetaSubOne {t q : ℕ}
    (hq : q ∈ selectedInertAuxiliaryPrimes ell t) :
    Ideal.span {(q : 𝓞 K)} ⊔
        Ideal.span {((IsCyclotomicExtension.zeta_spec ell ℚ K).toInteger - 1)} = ⊤ :=
  inertAuxiliaryPrimes_coprime_zetaSubOne ell
    (selectedInertAuxiliaryPrimes_subset ell t hq)

/-- The global inertia degree at an auxiliary prime is the full cyclotomic
degree `ell - 1`. -/
theorem inertiaDegIn_eq_sub_one_of_prime_modEq {q : ℕ}
    (hqprime : q.Prime) (hqmod : q % ell = inertResidue ell) :
    (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 K) = ell - 1 := by
  let : Fact q.Prime := ⟨hqprime⟩
  rw [IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd q K
    (hqprime.coprime_iff_not_dvd.mp (coprime_ell_of_modEq ell hqmod))]
  exact zmod_order_eq_sub_one_of_modEq ell hqmod

theorem ramificationIdxIn_eq_one_of_prime_modEq {q : ℕ}
    (hqprime : q.Prime) (hqmod : q % ell = inertResidue ell) :
    (Ideal.span {(q : ℤ)}).ramificationIdxIn (𝓞 K) = 1 := by
  let : Fact q.Prime := ⟨hqprime⟩
  exact IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd q K
    (hqprime.coprime_iff_not_dvd.mp (coprime_ell_of_modEq ell hqmod))

/-- There is exactly one prime of `𝓞 K` over an auxiliary rational prime. -/
theorem ncard_primesOver_eq_one_of_prime_modEq {q : ℕ}
    (hqprime : q.Prime) (hqmod : q % ell = inertResidue ell) :
    ((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)).ncard = 1 := by
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {ell} ℚ K
  let : Fact q.Prime := ⟨hqprime⟩
  let p : Ideal ℤ := Ideal.span {(q : ℤ)}
  have hpmax : p.IsMaximal := by
    simpa [p] using Int.ideal_span_isMaximal_of_prime q
  have : p.IsPrime := hpmax.isPrime
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    p (𝓞 K) Gal(K/ℚ)
  have hram : p.ramificationIdxIn (𝓞 K) = 1 := by
    simpa [p] using
      ramificationIdxIn_eq_one_of_prime_modEq ell (K := K) hqprime hqmod
  have hinert : p.inertiaDegIn (𝓞 K) = ell - 1 := by
    simpa [p] using inertiaDegIn_eq_sub_one_of_prime_modEq ell (K := K) hqprime hqmod
  have hgal : Nat.card Gal(K/ℚ) = ell - 1 := by
    rw [IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K,
      IsCyclotomicExtension.finrank K
        (Polynomial.cyclotomic.irreducible_rat (Fact.out : ell.Prime).pos),
      Nat.totient_prime (Fact.out : ell.Prime)]
  rw [hram, hinert, one_mul, hgal] at hfund
  have hell2 : 2 ≤ ell := (Fact.out : ell.Prime).two_le
  apply Nat.eq_of_mul_eq_mul_right (by omega : 0 < ell - 1)
  simpa using hfund

/-- **Inertness theorem.** The extended rational-prime ideal `(q)` is itself
prime in the prime-conductor cyclotomic field. -/
theorem span_nat_isPrime_of_prime_modEq {q : ℕ}
    (hqprime : q.Prime) (hqmod : q % ell = inertResidue ell) :
    (Ideal.span {(q : 𝓞 K)}).IsPrime := by
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {ell} ℚ K
  let : Fact q.Prime := ⟨hqprime⟩
  let p : Ideal ℤ := Ideal.span {(q : ℤ)}
  have hpmax : p.IsMaximal := by
    simpa [p] using Int.ideal_span_isMaximal_of_prime q
  have hpne : p ≠ ⊥ := by
    simpa [p, Ideal.span_singleton_eq_bot] using hqprime.ne_zero
  obtain ⟨P, hPset⟩ := Set.ncard_eq_one.mp (by
    simpa [p] using
      ncard_primesOver_eq_one_of_prime_modEq ell (K := K) hqprime hqmod)
  have hPmem : P ∈ p.primesOver (𝓞 K) := by
    rw [show p.primesOver (𝓞 K) = {P} by simpa [p] using hPset]
    simp
  have hPprime : P.IsPrime := hPmem.1
  have hPlies : P.LiesOver p := hPmem.2
  have hqNotDvd : ¬ q ∣ ell :=
    hqprime.coprime_iff_not_dvd.mp (coprime_ell_of_modEq ell hqmod)
  have hramP : P.ramificationIdx ℤ = 1 := by
    simpa [p] using
      (IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd q K P hqNotDvd)
  have hmap := Ideal.map_algebraMap_eq_finsetProd_pow (R := 𝓞 K) hpne
  have hPset' : p.primesOver (𝓞 K) = {P} := by
    simpa [p] using hPset
  have hPfinset : (p.primesOver (𝓞 K)).toFinset = {P} := by
    ext Q
    simp [hPset']
  rw [hPfinset] at hmap
  simp [hramP] at hmap
  have hmapSpan :
      Ideal.map (algebraMap ℤ (𝓞 K)) p = Ideal.span {(q : 𝓞 K)} := by
    simp [p, Ideal.map_span]
  rw [← algebraMap_int_eq] at hmap
  rw [hmapSpan] at hmap
  rw [hmap]
  exact hPprime

theorem span_nat_liesOver_of_prime_modEq {q : ℕ}
    (hqprime : q.Prime) (hqmod : q % ell = inertResidue ell) :
    (Ideal.span {(q : 𝓞 K)}).LiesOver (Ideal.span {(q : ℤ)}) := by
  let : Fact q.Prime := ⟨hqprime⟩
  let : (Ideal.span {(q : ℤ)}).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime q
  have hprime := span_nat_isPrime_of_prime_modEq ell (K := K) hqprime hqmod
  rw [Ideal.liesOver_iff_dvd_map hprime.ne_top]
  simp [Ideal.map_span]

theorem span_nat_inertiaDeg_of_prime_modEq {q : ℕ}
    (hqprime : q.Prime) (hqmod : q % ell = inertResidue ell) :
    (Ideal.span {(q : 𝓞 K)}).inertiaDeg ℤ = ell - 1 := by
  let : Fact q.Prime := ⟨hqprime⟩
  let P : Ideal (𝓞 K) := Ideal.span {(q : 𝓞 K)}
  have : P.IsPrime := by
    simpa [P] using span_nat_isPrime_of_prime_modEq ell (K := K) hqprime hqmod
  have : P.LiesOver (Ideal.span {(q : ℤ)}) := by
    simpa [P] using span_nat_liesOver_of_prime_modEq ell (K := K) hqprime hqmod
  simpa [P, zmod_order_eq_sub_one_of_modEq ell hqmod] using
    (IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd q K P
      (hqprime.coprime_iff_not_dvd.mp (coprime_ell_of_modEq ell hqmod)))

/-- The residue-field unit group at an inert auxiliary prime is cyclic. -/
theorem quotient_units_isCyclic_of_prime_modEq {q : ℕ}
    (hqprime : q.Prime) (hqmod : q % ell = inertResidue ell) :
    IsCyclic ((𝓞 K ⧸ Ideal.span {(q : 𝓞 K)})ˣ) := by
  let P : Ideal (𝓞 K) := Ideal.span {(q : 𝓞 K)}
  have hPprime : P.IsPrime := by
    simpa [P] using span_nat_isPrime_of_prime_modEq ell (K := K) hqprime hqmod
  have hPne : P ≠ ⊥ := by
    simpa [P, Ideal.span_singleton_eq_bot] using
      (Nat.cast_ne_zero.mpr hqprime.ne_zero : (q : 𝓞 K) ≠ 0)
  let : P.IsMaximal := hPprime.isMaximal hPne
  let : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  infer_instance

theorem quotient_natCard_eq_pow_of_prime_modEq {q : ℕ}
    (hqprime : q.Prime) (hqmod : q % ell = inertResidue ell) :
    Nat.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) = q ^ (ell - 1) := by
  let : Fact q.Prime := ⟨hqprime⟩
  let p : Ideal ℤ := Ideal.span {(q : ℤ)}
  let P : Ideal (𝓞 K) := Ideal.span {(q : 𝓞 K)}
  have hpmax : p.IsMaximal := by
    simpa [p] using Int.ideal_span_isMaximal_of_prime q
  have hPprime : P.IsPrime := by
    simpa [P] using span_nat_isPrime_of_prime_modEq ell (K := K) hqprime hqmod
  have hPne : P ≠ ⊥ := by
    simpa [P, Ideal.span_singleton_eq_bot] using
      (Nat.cast_ne_zero.mpr hqprime.ne_zero : (q : 𝓞 K) ≠ 0)
  have hPmax : P.IsMaximal := hPprime.isMaximal hPne
  have hPlies : P.LiesOver p := by
    simpa [p, P] using span_nat_liesOver_of_prime_modEq ell (K := K) hqprime hqmod
  calc
    Nat.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) = Submodule.cardQuot P := by
      simpa [P] using (Submodule.cardQuot_apply P).symm
    _ = Ideal.absNorm P := (Ideal.absNorm_apply P).symm
    _ = q ^ p.inertiaDeg' P := Ideal.absNorm_eq_pow_inertiaDeg' P hqprime
    _ = q ^ P.inertiaDeg ℤ := by rw [Ideal.inertiaDeg'_eq_inertiaDeg]
    _ = q ^ (ell - 1) := by
      rw [show P.inertiaDeg ℤ = ell - 1 by
        simpa [P] using
          span_nat_inertiaDeg_of_prime_modEq ell (K := K) hqprime hqmod]

theorem quotient_units_natCard_eq_pow_sub_one_of_prime_modEq {q : ℕ}
    (hqprime : q.Prime) (hqmod : q % ell = inertResidue ell) :
    Nat.card ((𝓞 K ⧸ Ideal.span {(q : 𝓞 K)})ˣ) = q ^ (ell - 1) - 1 := by
  let P : Ideal (𝓞 K) := Ideal.span {(q : 𝓞 K)}
  have hPprime : P.IsPrime := by
    simpa [P] using span_nat_isPrime_of_prime_modEq ell (K := K) hqprime hqmod
  have hPne : P ≠ ⊥ := by
    simpa [P, Ideal.span_singleton_eq_bot] using
      (Nat.cast_ne_zero.mpr hqprime.ne_zero : (q : 𝓞 K) ≠ 0)
  let : P.IsMaximal := hPprime.isMaximal hPne
  let : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  rw [Nat.card_units,
    quotient_natCard_eq_pow_of_prime_modEq ell (K := K) hqprime hqmod]

theorem ell_dvd_quotient_units_natCard_of_prime_modEq {q : ℕ}
    (hqprime : q.Prime) (hqmod : q % ell = inertResidue ell) :
    ell ∣ Nat.card ((𝓞 K ⧸ Ideal.span {(q : 𝓞 K)})ˣ) := by
  rw [quotient_units_natCard_eq_pow_sub_one_of_prime_modEq
    ell (K := K) hqprime hqmod]
  have hmod : 1 ≡ q ^ (ell - 1) [MOD ell] := by
    simpa [Nat.totient_prime (Fact.out : ell.Prime)] using
      (Nat.ModEq.pow_totient (coprime_ell_of_modEq ell hqmod)).symm
  exact hmod.dvd'

/-- The local quotient by `ell`-th powers has exactly `ell` classes. -/
theorem natCard_powerClass_quotient_units_of_prime_modEq {q : ℕ}
    (hqprime : q.Prime) (hqmod : q % ell = inertResidue ell) :
    Nat.card (NumberFieldLargerSieve.PowerClass
      ((𝓞 K ⧸ Ideal.span {(q : 𝓞 K)})ˣ) ell) = ell := by
  let P : Ideal (𝓞 K) := Ideal.span {(q : 𝓞 K)}
  have hPprime : P.IsPrime := by
    simpa [P] using span_nat_isPrime_of_prime_modEq ell (K := K) hqprime hqmod
  have hPne : P ≠ ⊥ := by
    simpa [P, Ideal.span_singleton_eq_bot] using
      (Nat.cast_ne_zero.mpr hqprime.ne_zero : (q : 𝓞 K) ≠ 0)
  let : P.IsMaximal := hPprime.isMaximal hPne
  let : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  apply NumberFieldLargerSieve.natCard_powerClass_eq
  exact ell_dvd_quotient_units_natCard_of_prime_modEq ell (K := K) hqprime hqmod

/-! Membership-specialized forms for direct use by the sieve. -/

theorem inertAuxiliaryPrimes_span_isPrime {t q : ℕ}
    (hq : q ∈ inertAuxiliaryPrimes ell t) :
    (Ideal.span {(q : 𝓞 K)}).IsPrime :=
  span_nat_isPrime_of_prime_modEq ell (K := K)
    (inertAuxiliaryPrimes_prime ell hq) (inertAuxiliaryPrimes_modEq ell hq)

theorem inertAuxiliaryPrimes_inertiaDeg {t q : ℕ}
    (hq : q ∈ inertAuxiliaryPrimes ell t) :
    (Ideal.span {(q : 𝓞 K)}).inertiaDeg ℤ = ell - 1 :=
  span_nat_inertiaDeg_of_prime_modEq ell (K := K)
    (inertAuxiliaryPrimes_prime ell hq) (inertAuxiliaryPrimes_modEq ell hq)

theorem inertAuxiliaryPrimes_quotient_units_isCyclic {t q : ℕ}
    (hq : q ∈ inertAuxiliaryPrimes ell t) :
    IsCyclic ((𝓞 K ⧸ Ideal.span {(q : 𝓞 K)})ˣ) :=
  quotient_units_isCyclic_of_prime_modEq ell (K := K)
    (inertAuxiliaryPrimes_prime ell hq) (inertAuxiliaryPrimes_modEq ell hq)

theorem inertAuxiliaryPrimes_quotient_natCard {t q : ℕ}
    (hq : q ∈ inertAuxiliaryPrimes ell t) :
    Nat.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) = q ^ (ell - 1) :=
  quotient_natCard_eq_pow_of_prime_modEq ell (K := K)
    (inertAuxiliaryPrimes_prime ell hq) (inertAuxiliaryPrimes_modEq ell hq)

theorem inertAuxiliaryPrimes_ell_dvd_quotient_units_natCard {t q : ℕ}
    (hq : q ∈ inertAuxiliaryPrimes ell t) :
    ell ∣ Nat.card ((𝓞 K ⧸ Ideal.span {(q : 𝓞 K)})ˣ) :=
  ell_dvd_quotient_units_natCard_of_prime_modEq ell (K := K)
    (inertAuxiliaryPrimes_prime ell hq) (inertAuxiliaryPrimes_modEq ell hq)

theorem inertAuxiliaryPrimes_natCard_powerClass {t q : ℕ}
    (hq : q ∈ inertAuxiliaryPrimes ell t) :
    Nat.card (NumberFieldLargerSieve.PowerClass
      ((𝓞 K ⧸ Ideal.span {(q : 𝓞 K)})ˣ) ell) = ell :=
  natCard_powerClass_quotient_units_of_prime_modEq ell (K := K)
    (inertAuxiliaryPrimes_prime ell hq) (inertAuxiliaryPrimes_modEq ell hq)

/-! The selected-family versions used by the finite tensor product. -/

theorem selectedInertAuxiliaryPrimes_span_isPrime {t q : ℕ}
    (hq : q ∈ selectedInertAuxiliaryPrimes ell t) :
    (Ideal.span {(q : 𝓞 K)}).IsPrime :=
  inertAuxiliaryPrimes_span_isPrime ell (K := K)
    (selectedInertAuxiliaryPrimes_subset ell t hq)

theorem selectedInertAuxiliaryPrimes_quotient_units_isCyclic {t q : ℕ}
    (hq : q ∈ selectedInertAuxiliaryPrimes ell t) :
    IsCyclic ((𝓞 K ⧸ Ideal.span {(q : 𝓞 K)})ˣ) :=
  inertAuxiliaryPrimes_quotient_units_isCyclic ell (K := K)
    (selectedInertAuxiliaryPrimes_subset ell t hq)

theorem selectedInertAuxiliaryPrimes_natCard_powerClass {t q : ℕ}
    (hq : q ∈ selectedInertAuxiliaryPrimes ell t) :
    Nat.card (NumberFieldLargerSieve.PowerClass
      ((𝓞 K ⧸ Ideal.span {(q : 𝓞 K)})ˣ) ell) = ell :=
  inertAuxiliaryPrimes_natCard_powerClass ell (K := K)
    (selectedInertAuxiliaryPrimes_subset ell t hq)

end

end Erdos980.ElliottTail.OddInertAuxiliaryPrimes
