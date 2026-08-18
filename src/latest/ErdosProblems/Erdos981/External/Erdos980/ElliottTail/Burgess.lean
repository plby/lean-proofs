import ErdosProblems.Erdos981.External.Erdos980.Basic
import BoundedGaps.BombieriVinogradov.Analytic.PrimitivePolyaVinogradov
import Mathlib.NumberTheory.MulChar.Duality

/-!
# A pointwise bound for the least power nonresidue

The tail argument for Erdős Problem 980 only needs a pointwise estimate with
an exponent strictly below one.  The primitive Pólya--Vinogradov theorem
already available in `BoundedGaps` gives the stronger elementary bound

`n_k(p) < 1 + sqrt p * log p`.

This file constructs, for every eligible prime, a nonprincipal character
which is trivial on all `k`-th powers, proves that it is primitive, and applies
Pólya--Vinogradov to the initial interval preceding the least nonresidue.
-/

namespace Erdos980

open Filter
open scoped BigOperators Classical

/-- Every nonprincipal character of prime level is primitive. -/
theorem dirichletCharacter_isPrimitive_of_prime_of_ne_one
    {p : ℕ} (hp : p.Prime) (chi : DirichletCharacter ℂ p) (hchi : chi ≠ 1) :
    chi.IsPrimitive := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rcases (Nat.dvd_prime hp).mp chi.conductor_dvd_level with hcond | hcond
  · exfalso
    apply hchi
    exact DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hcond
  · exact hcond

/-- At an eligible prime there is a complex character of exact order `k`
which is trivial on all nonzero `k`-th powers. -/
theorem exists_exactOrder_powerDetectingCharacter {k p : ℕ} (hk : 2 ≤ k)
    (hp : Eligible k p) :
    ∃ chi : DirichletCharacter ℂ p,
      chi ≠ 1 ∧ orderOf chi = k ∧ chi.IsPrimitive ∧
        ∀ b : ZMod p, IsUnit b → chi (b ^ k) = 1 := by
  letI : Fact p.Prime := ⟨hp.1⟩
  letI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp.1
  letI : IsCyclic (DirichletCharacter ℂ p) :=
    (MulChar.mulEquiv_units (ZMod p) ℂ).some.isCyclic.mpr inferInstance
  let H : Subgroup (ZMod p)ˣ := (powMonoidHom k : (ZMod p)ˣ →* (ZMod p)ˣ).range
  let X : Subgroup (DirichletCharacter ℂ p) :=
    (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod p) ℂ H).ofDual
  letI : IsCyclic X := Subgroup.isCyclic X
  have hdiv : k ∣ Nat.card (ZMod p)ˣ := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
    exact dvd_prime_sub_one_of_eligible hp
  have hgcd : (Nat.card (ZMod p)ˣ).gcd k = k :=
    Nat.gcd_eq_right_iff_dvd.mpr hdiv
  have hcardNat : Nat.card X = k := by
    calc
      Nat.card X = H.index := by
        rw [Subgroup.index_eq_card]
        exact MulChar.card_subgroupOrderIsoSubgroupMulChar
      _ = (Nat.card (ZMod p)ˣ).gcd k := by
        exact IsCyclic.index_powMonoidHom_range (ZMod p)ˣ k
      _ = k := hgcd
  have hcard : Fintype.card X = k := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardNat
  obtain ⟨chiX, horderX⟩ :=
    isCyclic_iff_exists_orderOf_eq_natCard.mp (by infer_instance : IsCyclic X)
  let chi : DirichletCharacter ℂ p := chiX
  have horder : orderOf chi = k := by
    exact (Subgroup.orderOf_coe chiX).trans (horderX.trans hcardNat)
  have hchi : chi ≠ 1 := by
    intro h
    have : k = 1 := by simpa [h] using horder.symm
    omega
  refine ⟨chi, hchi, horder,
    dirichletCharacter_isPrimitive_of_prime_of_ne_one hp.1 chi hchi, ?_⟩
  intro b hb
  let u : (ZMod p)ˣ := hb.unit
  have hu : u ^ k ∈ H := ⟨u, rfl⟩
  have hmem : chi ∈ X := chiX.property
  have htriv :=
    (MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff.mp hmem) (u ^ k) hu
  simpa [chi, u, IsUnit.unit_spec] using htriv

/-- The nonprincipal primitive form used by Pólya--Vinogradov. -/
theorem exists_powerDetectingCharacter {k p : ℕ} (hk : 2 ≤ k)
    (hp : Eligible k p) :
    ∃ chi : DirichletCharacter ℂ p,
      chi ≠ 1 ∧ chi.IsPrimitive ∧
        ∀ b : ZMod p, IsUnit b → chi (b ^ k) = 1 := by
  obtain ⟨chi, hchi, _horder, hprimitive, hpow⟩ :=
    exists_exactOrder_powerDetectingCharacter hk hp
  exact ⟨chi, hchi, hprimitive, hpow⟩

/-- Every positive integer below the least nonresidue is sent to one by a
power-detecting character. -/
theorem powerDetectingCharacter_nat_eq_one_of_lt_least
    {k p a : ℕ} (hk : 2 ≤ k) (hp : Eligible k p)
    (chi : DirichletCharacter ℂ p)
    (hpow : ∀ b : ZMod p, IsUnit b → chi (b ^ k) = 1)
    (ha0 : 0 < a) (ha : a < leastKthPowerNonresidue k p) :
    chi (a : ZMod p) = 1 := by
  have hap : a < p := ha.trans (leastKthPowerNonresidue_lt_modulus hk hp)
  have hunit : IsUnit (a : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.symm
    rw [hp.1.coprime_iff_not_dvd]
    intro hdvd
    exact (not_le_of_gt hap) (Nat.le_of_dvd ha0 hdvd)
  have hex : ∃ b : ZMod p, b ^ k = (a : ZMod p) := by
    by_contra hn
    exact not_kthPowerNonresidue_of_lt_least hk hp ha ⟨hunit, hn⟩
  obtain ⟨b, hb⟩ := hex
  have hbunit : IsUnit b := by
    rw [← isUnit_pow_iff (show k ≠ 0 by omega), hb]
    exact hunit
  rw [← hb]
  exact hpow b hbunit

/-- Pólya--Vinogradov gives a uniform pointwise bound for every fixed power
order `k`; no Burgess estimate is needed for the mean-value tail. -/
theorem leastKthPowerNonresidue_lt_one_add_sqrt_mul_log
    {k p : ℕ} (hk : 2 ≤ k) (hp : Eligible k p) :
    (leastKthPowerNonresidue k p : ℝ) <
      1 + Real.sqrt (p : ℝ) * Real.log (p : ℝ) := by
  let L := leastKthPowerNonresidue k p
  obtain ⟨chi, hchi, hprimitive, hpow⟩ := exists_powerDetectingCharacter hk hp
  letI : NeZero p := ⟨hp.1.ne_zero⟩
  have hp1 : 1 < p := hp.1.one_lt
  have hsum :
      (∑ n ∈ Finset.Ioc (0 : ℤ) (L - 1 : ℕ), chi (n : ZMod p)) =
        (L - 1 : ℕ) := by
    calc
      (∑ n ∈ Finset.Ioc (0 : ℤ) (L - 1 : ℕ), chi (n : ZMod p)) =
          ∑ _n ∈ Finset.Ioc (0 : ℤ) (L - 1 : ℕ), (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mem_Ioc] at hn
        have hn0 : 0 < n.toNat := by omega
        have hnL : n.toNat < L := by omega
        have hncast : (n.toNat : ℤ) = n := by omega
        rw [← hncast]
        simpa only [Int.cast_natCast] using
          powerDetectingCharacter_nat_eq_one_of_lt_least hk hp chi hpow hn0 hnL
      _ = (L - 1 : ℕ) := by simp
  have hPV := BoundedGaps.Maynard.norm_sum_dirichletCharacter_Ioc_lt_sqrt_mul_log
    hp1 chi hprimitive 0 (L - 1)
  simp only [zero_add] at hPV
  rw [hsum, Complex.norm_natCast] at hPV
  have hLpos : 0 < L := leastKthPowerNonresidue_pos hk hp
  have hcast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hLpos.ne')]
    norm_num
  rw [hcast] at hPV
  dsimp [L] at hPV ⊢
  linarith

/-- The Pólya--Vinogradov majorant is eventually bounded by the fixed
sublinear power `x^(3/4)`. -/
theorem eventually_one_add_sqrt_mul_log_le_threeQuarter_rpow :
    ∀ᶠ x : ℝ in atTop,
      1 + Real.sqrt x * Real.log x ≤ x ^ (3 / 4 : ℝ) := by
  have hlog :=
    (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).bound
      (show (0 : ℝ) < 1 / 2 by norm_num)
  have hpow := (tendsto_rpow_atTop (show (0 : ℝ) < 3 / 4 by norm_num)).eventually
    (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hlog, hpow, eventually_gt_atTop (1 : ℝ)] with x hxlog hxpow hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hquarter : 0 < x ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hthree : 0 < x ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx.le
  rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hquarter.le] at hxlog
  have hrpow : Real.sqrt x * x ^ (1 / 4 : ℝ) = x ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
    congr 2
    norm_num
  have hmain : Real.sqrt x * Real.log x ≤
      (1 / 2 : ℝ) * x ^ (3 / 4 : ℝ) := by
    calc
      Real.sqrt x * Real.log x ≤
          Real.sqrt x * ((1 / 2 : ℝ) * x ^ (1 / 4 : ℝ)) := by
        gcongr
      _ = (1 / 2 : ℝ) * x ^ (3 / 4 : ℝ) := by
        rw [← hrpow]
        ring
  have hone : 1 ≤ (1 / 2 : ℝ) * x ^ (3 / 4 : ℝ) := by
    nlinarith
  nlinarith

/-- More generally, `1 + sqrt x * log x` is eventually bounded by `x^β`
for every exponent strictly larger than `1/2`. -/
theorem eventually_one_add_sqrt_mul_log_le_rpow {β : ℝ}
    (hβ : 1 / 2 < β) :
    ∀ᶠ x : ℝ in atTop,
      1 + Real.sqrt x * Real.log x ≤ x ^ β := by
  have hdelta : 0 < β - 1 / 2 := sub_pos.mpr hβ
  have hβpos : 0 < β := (by norm_num : (0 : ℝ) < 1 / 2).trans hβ
  have hlog := (isLittleO_log_rpow_atTop hdelta).bound
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hpow := (tendsto_rpow_atTop hβpos).eventually
    (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hlog, hpow, eventually_gt_atTop (1 : ℝ)] with x hxlog hxpow hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hdeltaPow : 0 < x ^ (β - 1 / 2) := Real.rpow_pos_of_pos hx0 _
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx.le
  rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hdeltaPow.le] at hxlog
  have hrpow : Real.sqrt x * x ^ (β - 1 / 2) = x ^ β := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
    congr 2
    ring
  have hmain : Real.sqrt x * Real.log x ≤ (1 / 2 : ℝ) * x ^ β := by
    calc
      Real.sqrt x * Real.log x ≤
          Real.sqrt x * ((1 / 2 : ℝ) * x ^ (β - 1 / 2)) := by
        gcongr
      _ = (1 / 2 : ℝ) * x ^ β := by
        rw [← hrpow]
        ring
  have hone : 1 ≤ (1 / 2 : ℝ) * x ^ β := by
    nlinarith
  nlinarith

/-- Uniform eventual sublinear bound in the natural prime variable.  The
implication keeps the theorem total, matching Elliott's zero normalization at
ineligible primes. -/
theorem eventually_leastKthPowerNonresidue_le_threeQuarter_rpow (k : ℕ)
    (hk : 2 ≤ k) :
    ∀ᶠ p : ℕ in atTop,
      Eligible k p →
        (leastKthPowerNonresidue k p : ℝ) ≤ (p : ℝ) ^ (3 / 4 : ℝ) := by
  have hevent := tendsto_natCast_atTop_atTop.eventually
    eventually_one_add_sqrt_mul_log_le_threeQuarter_rpow
  filter_upwards [hevent] with p hp
  intro helig
  exact (leastKthPowerNonresidue_lt_one_add_sqrt_mul_log hk helig).le.trans hp

/-- The tail-ready pointwise estimate with any prescribed exponent above
`1/2`. -/
theorem eventually_leastKthPowerNonresidue_le_rpow (k : ℕ) (hk : 2 ≤ k)
    {β : ℝ} (hβ : 1 / 2 < β) :
    ∀ᶠ p : ℕ in atTop,
      Eligible k p →
        (leastKthPowerNonresidue k p : ℝ) ≤ (p : ℝ) ^ β := by
  have hevent := tendsto_natCast_atTop_atTop.eventually
    (eventually_one_add_sqrt_mul_log_le_rpow hβ)
  filter_upwards [hevent] with p hp
  intro helig
  exact (leastKthPowerNonresidue_lt_one_add_sqrt_mul_log hk helig).le.trans hp

end Erdos980
