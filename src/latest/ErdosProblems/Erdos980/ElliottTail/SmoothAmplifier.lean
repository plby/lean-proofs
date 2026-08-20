import ErdosProblems.Erdos980.Basic
import ErdosProblems.Erdos980.ElliottTail.Burgess
import ErdosProblems.Erdos980.ElliottTail.CharacterEncoding
import ErdosProblems.Erdos980.ElliottTail.LargeSieve
import Mathlib.Data.Nat.Choose.Bounds
import PrimeNumberTheoremAnd.Consequences

/-!
# A long smooth-number amplifier for Elliott's tail

For natural numbers `y` and `r`, `smoothAmplifier y r` is the set of products
of `r` distinct primes at most `y`.  Unique factorization identifies this set
with the `r`-element subsets of the primes up to `y`; in particular its exact
cardinality is `choose (pi y) r`.  Every member is positive, at most `y ^ r`,
and `(y + 1)`-smooth.

The final theorem applies the exact-order large sieve to eligible prime
moduli whose least `k`-th-power nonresidue exceeds `y`.  The detecting
character has exact order `k`, is primitive because its level is prime, and
is one on the whole smooth amplifier.
-/

namespace Erdos980.ElliottTail

open Filter Real
open BoundedGaps.Maynard
open scoped BigOperators Classical Topology

noncomputable section

/-- Products of `r` distinct rational primes at most `y`. -/
def smoothAmplifier (y r : ℕ) : Finset ℕ :=
  (Nat.primesLE y).powersetCard r |>.image fun S ↦ S.prod id

/-- A member of the smooth amplifier has a set of `r` distinct prime
factors, all at most `y`, whose product is the member. -/
lemma mem_smoothAmplifier_source {y r n : ℕ} (hn : n ∈ smoothAmplifier y r) :
    ∃ S ⊆ Nat.primesLE y, S.card = r ∧ n = S.prod id := by
  rw [smoothAmplifier, Finset.mem_image] at hn
  obtain ⟨S, hS, rfl⟩ := hn
  exact ⟨S, (Finset.mem_powersetCard.mp hS).1,
    (Finset.mem_powersetCard.mp hS).2, rfl⟩

private lemma product_of_primes_factors_toFinset {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) :
    (S.prod id).primeFactorsList.toFinset = S := by
  have hprod : (S.sort (· ≤ ·)).prod = S.prod id := by
    calc
      (S.sort (· ≤ ·)).prod = (S.sort (· ≤ ·)).toFinset.prod id := by
        simpa using (List.prod_toFinset id (S.sort_nodup (· ≤ ·))).symm
      _ = S.prod id := by rw [Finset.sort_toFinset]
  have hprime : ∀ p ∈ S.sort (· ≤ ·), p.Prime := by
    intro p hp
    exact hS p ((Finset.mem_sort (· ≤ ·)).mp hp)
  have hperm : List.Perm (S.sort (· ≤ ·)) (S.prod id).primeFactorsList :=
    Nat.primeFactorsList_unique hprod hprime
  exact (List.toFinset_eq_of_perm _ _ hperm).symm.trans (Finset.sort_toFinset _ _)

/-- Products distinguish subsets of the primes up to `y`. -/
lemma smoothAmplifier_prod_injective (y : ℕ) :
    Set.InjOn (fun S : Finset ℕ ↦ S.prod id) (Nat.primesLE y).powerset := by
  intro A hA B hB hprod
  have hAprime : ∀ p ∈ A, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primesLE (Finset.mem_powerset.mp hA hp)
  have hBprime : ∀ p ∈ B, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primesLE (Finset.mem_powerset.mp hB hp)
  change A.prod id = B.prod id at hprod
  calc
    A = (A.prod id).primeFactorsList.toFinset :=
      (product_of_primes_factors_toFinset hAprime).symm
    _ = (B.prod id).primeFactorsList.toFinset := by rw [hprod]
    _ = B := product_of_primes_factors_toFinset hBprime

/-- Exact cardinality of the smooth amplifier. -/
theorem smoothAmplifier_card (y r : ℕ) :
    (smoothAmplifier y r).card = (Nat.primeCounting y).choose r := by
  rw [smoothAmplifier, Finset.card_image_iff.mpr]
  · rw [Finset.card_powersetCard, Nat.primesLE_card_eq_primeCounting]
  · apply (smoothAmplifier_prod_injective y).mono
    intro S hS
    exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hS).1

/-- Every amplifier element is positive. -/
lemma smoothAmplifier_pos {y r n : ℕ} (hn : n ∈ smoothAmplifier y r) : 0 < n := by
  obtain ⟨S, hS, _hcard, rfl⟩ := mem_smoothAmplifier_source hn
  exact Finset.prod_pos fun p hp ↦
    (Nat.prime_of_mem_primesLE (hS hp)).pos

/-- Every amplifier element is bounded by the formal product length. -/
lemma smoothAmplifier_le_pow {y r n : ℕ} (hn : n ∈ smoothAmplifier y r) :
    n ≤ y ^ r := by
  obtain ⟨S, hS, hcard, rfl⟩ := mem_smoothAmplifier_source hn
  calc
    S.prod id ≤ S.prod (fun _ ↦ y) := by
      exact Finset.prod_le_prod (fun p _hp ↦ Nat.zero_le p)
        (fun p hp ↦ Nat.le_of_mem_primesLE (hS hp))
    _ = y ^ S.card := by simp
    _ = y ^ r := by rw [hcard]

/-- The amplifier is supported in the interval required by the sparse
large-sieve theorem. -/
theorem smoothAmplifier_subset_Ioc (y r : ℕ) :
    smoothAmplifier y r ⊆ Finset.Ioc 0 (y ^ r) := by
  intro n hn
  exact Finset.mem_Ioc.mpr ⟨smoothAmplifier_pos hn, smoothAmplifier_le_pow hn⟩

/-- Every prime divisor of an amplifier element is at most `y`. -/
lemma prime_dvd_smoothAmplifier_le {y r n q : ℕ}
    (hn : n ∈ smoothAmplifier y r) (hq : q.Prime) (hqn : q ∣ n) :
    q ≤ y := by
  obtain ⟨S, hS, _hcard, rfl⟩ := mem_smoothAmplifier_source hn
  have hprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primesLE (hS hp)
  have hqmem : q ∈ S := by
    have hqfac : q ∈ (S.prod id).primeFactorsList :=
      (Nat.mem_primeFactorsList (Finset.prod_ne_zero_iff.mpr
        (fun p hp ↦ (hprime p hp).ne_zero))).mpr ⟨hq, hqn⟩
    have hqfin : q ∈ (S.prod id).primeFactorsList.toFinset :=
      List.mem_toFinset.mpr hqfac
    rw [product_of_primes_factors_toFinset hprime] at hqfin
    exact hqfin
  exact Nat.le_of_mem_primesLE (hS hqmem)

/-- Amplifier elements are positive `(y + 1)`-smooth numbers. -/
theorem smoothAmplifier_mem_smoothNumbers {y r n : ℕ}
    (hn : n ∈ smoothAmplifier y r) :
    n ∈ Nat.smoothNumbers (y + 1) := by
  rw [Nat.mem_smoothNumbers']
  intro q hq hqn
  exact Nat.lt_succ_iff.mpr (prime_dvd_smoothAmplifier_le hn hq hqn)

/-- The standard binomial lower bound, rewritten for the smooth amplifier. -/
theorem smoothAmplifier_card_lower (y r : ℕ) :
    ((((Nat.primeCounting y + 1 - r : ℕ) : ℝ) ^ r) /
        (r.factorial : ℝ)) ≤
      ((smoothAmplifier y r).card : ℝ) := by
  rw [smoothAmplifier_card]
  exact Nat.pow_le_choose r (Nat.primeCounting y)

/-- The amplifier is nonempty exactly in the range in which an `r`-element
subset of the primes up to `y` exists. -/
theorem smoothAmplifier_nonempty_iff (y r : ℕ) :
    (smoothAmplifier y r).Nonempty ↔ r ≤ Nat.primeCounting y := by
  constructor
  · intro h
    apply Nat.choose_ne_zero_iff.mp
    rw [← smoothAmplifier_card]
    exact Finset.card_ne_zero.mpr h
  · intro h
    apply Finset.card_pos.mp
    rw [smoothAmplifier_card]
    exact Nat.choose_pos h

/-! ## Exact-order detecting characters -/

/-- At an eligible prime there is a primitive character of exact order `k`
which is one on every nonzero `k`-th power. -/
theorem exists_exactOrderPrimitive_powerDetectingCharacter
    {k p : ℕ} (hk : 2 ≤ k) (hp : Eligible k p) :
    ∃ ψ : primitiveCharacters p,
      orderOf ψ.1 = k ∧
        ∀ b : ZMod p, IsUnit b → ψ.1 (b ^ k) = 1 := by
  obtain ⟨χ, horder, hkernel⟩ :=
    exists_dirichletCharacter_exactOrder_kernel_powRange hp.1
      (dvd_prime_sub_one_of_eligible hp)
  have hχne : χ ≠ 1 := by
    intro hχ
    subst χ
    simp at horder
    omega
  let ψ : primitiveCharacters p :=
    ⟨χ, dirichletCharacter_isPrimitive_of_prime_of_ne_one hp.1 χ hχne⟩
  refine ⟨ψ, horder, ?_⟩
  intro b hb
  let u : (ZMod p)ˣ := hb.unit
  have hu : u ^ k ∈ (powMonoidHom k : (ZMod p)ˣ →* (ZMod p)ˣ).range :=
    ⟨u, rfl⟩
  have hχu : χ (u ^ k) = 1 := (hkernel (u ^ k)).mpr hu
  simpa [ψ, u, IsUnit.unit_spec] using hχu

/-- The exact-order detecting character is one on a smooth amplifier when
the least nonresidue exceeds the smoothness threshold. -/
theorem exists_exactOrderPrimitive_trivialOn_smoothAmplifier
    {k p y r : ℕ} (hk : 2 ≤ k) (hp : Eligible k p)
    (hy : y < leastKthPowerNonresidue k p) :
    ∃ ψ : primitiveCharacters p,
      orderOf ψ.1 = k ∧ ∀ n ∈ smoothAmplifier y r, ψ.1 n = 1 := by
  obtain ⟨ψ, horder, hpow⟩ :=
    exists_exactOrderPrimitive_powerDetectingCharacter hk hp
  refine ⟨ψ, horder, ?_⟩
  intro n hn
  have hsmooth : n ∈ Nat.smoothNumbers (y + 1) :=
    smoothAmplifier_mem_smoothNumbers hn
  simpa using DirichletCharacter.eq_one_of_mem_smoothNumbers ψ.1 hsmooth
    (fun q hq hqy ↦
      powerDetectingCharacter_nat_eq_one_of_lt_least hk hp ψ.1 hpow
        hq.pos (lt_of_le_of_lt hqy hy))

/-! ## The finite Elliott rarity estimate -/

/-- Eligible prime moduli up to `Q` whose least `k`-th-power nonresidue is
larger than `y`. -/
def largeLeastKthPowerNonresiduePrimes (k Q y : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 Q).filter fun p ↦
    Eligible k p ∧ y < leastKthPowerNonresidue k p

@[simp] theorem mem_largeLeastKthPowerNonresiduePrimes
    {k Q y p : ℕ} :
    p ∈ largeLeastKthPowerNonresiduePrimes k Q y ↔
      0 < p ∧ p ≤ Q ∧ Eligible k p ∧
        y < leastKthPowerNonresidue k p := by
  simp [largeLeastKthPowerNonresiduePrimes, and_assoc]

theorem largeLeastKthPowerNonresiduePrimes_subset_Ioc (k Q y : ℕ) :
    largeLeastKthPowerNonresiduePrimes k Q y ⊆ Finset.Ioc 0 Q :=
  Finset.filter_subset _ _

/-- Exact finite rarity bound obtained from the long smooth amplifier. -/
theorem largeLeastKthPowerNonresiduePrimes_card_le
    (k Q y r : ℕ) (hk : 2 ≤ k) (hr : r ≤ Nat.primeCounting y) :
    ((largeLeastKthPowerNonresiduePrimes k Q y).card : ℝ) ≤
      (((y ^ r : ℕ) : ℝ) + (Q : ℝ) ^ 2) /
        ((Nat.primeCounting y).choose r : ℝ) := by
  have h := exactOrder_trivialOnSet_moduli_card_le
    Q 0 (y ^ r) k (smoothAmplifier y r)
    ((smoothAmplifier_nonempty_iff y r).mpr hr)
    (by simpa using smoothAmplifier_subset_Ioc y r)
    (largeLeastKthPowerNonresiduePrimes k Q y)
    (largeLeastKthPowerNonresiduePrimes_subset_Ioc k Q y)
    (fun p hp ↦ by
      have hmem := mem_largeLeastKthPowerNonresiduePrimes.mp hp
      exact exists_exactOrderPrimitive_trivialOn_smoothAmplifier
        hk hmem.2.2.1 hmem.2.2.2)
  simpa [smoothAmplifier_card] using h

/-- Multiplication form of the same estimate, convenient when a lower bound
for the binomial coefficient is available. -/
theorem largeLeastKthPowerNonresiduePrimes_card_mul_choose_le
    (k Q y r : ℕ) (hk : 2 ≤ k) (hr : r ≤ Nat.primeCounting y) :
    ((Nat.primeCounting y).choose r : ℝ) *
        ((largeLeastKthPowerNonresiduePrimes k Q y).card : ℝ) ≤
      ((y ^ r : ℕ) : ℝ) + (Q : ℝ) ^ 2 := by
  simpa [smoothAmplifier_card] using
    exactOrder_trivialOnSet_moduli_card_mul_card_le
      Q 0 (y ^ r) k (smoothAmplifier y r)
      ((smoothAmplifier_nonempty_iff y r).mpr hr)
      (by simpa using smoothAmplifier_subset_Ioc y r)
      (largeLeastKthPowerNonresiduePrimes k Q y)
      (largeLeastKthPowerNonresiduePrimes_subset_Ioc k Q y)
      (fun p hp ↦ by
        have hmem := mem_largeLeastKthPowerNonresiduePrimes.mp hp
        exact exists_exactOrderPrimitive_trivialOn_smoothAmplifier
          hk hmem.2.2.1 hmem.2.2.2)

/-- The multiplication bound with any larger interval length `N`.  This is
the form used after choosing `r` so that `y ^ r ≤ N`. -/
theorem largeLeastKthPowerNonresiduePrimes_card_mul_choose_le_of_pow_le
    (k Q y r N : ℕ) (hk : 2 ≤ k) (hr : r ≤ Nat.primeCounting y)
    (hpow : y ^ r ≤ N) :
    ((Nat.primeCounting y).choose r : ℝ) *
        ((largeLeastKthPowerNonresiduePrimes k Q y).card : ℝ) ≤
      (N : ℝ) + (Q : ℝ) ^ 2 := by
  calc
    ((Nat.primeCounting y).choose r : ℝ) *
          ((largeLeastKthPowerNonresiduePrimes k Q y).card : ℝ) ≤
        ((y ^ r : ℕ) : ℝ) + (Q : ℝ) ^ 2 :=
      largeLeastKthPowerNonresiduePrimes_card_mul_choose_le k Q y r hk hr
    _ ≤ (N : ℝ) + (Q : ℝ) ^ 2 := by
      gcongr

/-- A packaged finite power-saving interface.  Any positive lower bound `L`
for the binomial amplifier length may be substituted directly. -/
theorem largeLeastKthPowerNonresiduePrimes_card_le_of_parameters
    (k Q y r N : ℕ) (L : ℝ) (hk : 2 ≤ k)
    (hr : r ≤ Nat.primeCounting y) (hpow : y ^ r ≤ N)
    (hL : 0 < L) (hcard : L ≤ ((Nat.primeCounting y).choose r : ℝ)) :
    ((largeLeastKthPowerNonresiduePrimes k Q y).card : ℝ) ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) / L := by
  rw [le_div_iff₀ hL]
  calc
    ((largeLeastKthPowerNonresiduePrimes k Q y).card : ℝ) * L ≤
        ((largeLeastKthPowerNonresiduePrimes k Q y).card : ℝ) *
          ((Nat.primeCounting y).choose r : ℝ) := by
      exact mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = ((Nat.primeCounting y).choose r : ℝ) *
          ((largeLeastKthPowerNonresiduePrimes k Q y).card : ℝ) := by ring
    _ ≤ (N : ℝ) + (Q : ℝ) ^ 2 :=
      largeLeastKthPowerNonresiduePrimes_card_mul_choose_le_of_pow_le
        k Q y r N hk hr hpow

/-- The concrete power-saving consequence used in the large tail.  Thus the
remaining parameter problem is exactly to arrange `y ^ r ≤ x ^ 2` and an
amplifier of size at least `x ^ (7/4)`. -/
theorem largeLeastKthPowerNonresiduePrimes_card_le_two_mul_rpow_quarter
    (k x y r : ℕ) (hk : 2 ≤ k) (hx : 0 < x)
    (hr : r ≤ Nat.primeCounting y) (hpow : y ^ r ≤ x ^ 2)
    (hcard : (x : ℝ) ^ (7 / 4 : ℝ) ≤
      ((Nat.primeCounting y).choose r : ℝ)) :
    ((largeLeastKthPowerNonresiduePrimes k x y).card : ℝ) ≤
      2 * (x : ℝ) ^ (1 / 4 : ℝ) := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hLpos : 0 < (x : ℝ) ^ (7 / 4 : ℝ) :=
    Real.rpow_pos_of_pos hxR _
  have hmain := largeLeastKthPowerNonresiduePrimes_card_le_of_parameters
    k x y r (x ^ 2) ((x : ℝ) ^ (7 / 4 : ℝ))
    hk hr hpow hLpos hcard
  refine hmain.trans_eq ?_
  rw [div_eq_iff hLpos.ne']
  have hrpow :
      (x : ℝ) ^ (1 / 4 : ℝ) * (x : ℝ) ^ (7 / 4 : ℝ) =
        (x : ℝ) ^ 2 := by
    rw [← Real.rpow_add hxR]
    norm_num
  push_cast
  nlinarith

/-! ## Concrete integer parameters

Using the binary logarithm avoids floor estimates in the support calculation.
The exponent `100` and denominator `51` leave a fixed amount of room on both
sides: the support fits below `x²`, while its binomial cardinality has exponent
strictly larger than `7/4` once the prime-number-theorem estimate is inserted.
-/

/-- Smoothness scale for the concrete long amplifier. -/
def smoothAmplifierScale (x : ℕ) : ℕ := (Nat.log 2 x) ^ 100

/-- Product length for the concrete long amplifier. -/
def smoothAmplifierLength (x : ℕ) : ℕ :=
  Nat.log 2 x / (51 * (Nat.log 2 (Nat.log 2 x) + 1))

/-- The concrete smooth amplifier is always supported below `x²` (apart
from the irrelevant input `x = 0`). -/
theorem smoothAmplifierScale_pow_length_le_square (x : ℕ) (hx : x ≠ 0) :
    smoothAmplifierScale x ^ smoothAmplifierLength x ≤ x ^ 2 := by
  let m := Nat.log 2 x
  let d := Nat.log 2 m + 1
  have hmd : m ≤ 2 ^ d := by
    exact (Nat.lt_pow_succ_log_self (by omega : 1 < 2) m).le
  have hr : smoothAmplifierLength x * (51 * d) ≤ m := by
    exact Nat.div_mul_le_self m (51 * d)
  have hexp : d * (100 * smoothAmplifierLength x) ≤ 2 * m := by
    calc
      d * (100 * smoothAmplifierLength x) =
          100 * (smoothAmplifierLength x * d) := by ring
      _ ≤ 102 * (smoothAmplifierLength x * d) := by
        gcongr
        norm_num
      _ = 2 * (smoothAmplifierLength x * (51 * d)) := by ring
      _ ≤ 2 * m := Nat.mul_le_mul_left 2 hr
  have hmx : 2 ^ m ≤ x := Nat.pow_log_le_self 2 hx
  calc
    smoothAmplifierScale x ^ smoothAmplifierLength x =
        m ^ (100 * smoothAmplifierLength x) := by
      simp [smoothAmplifierScale, m, pow_mul]
    _ ≤ (2 ^ d) ^ (100 * smoothAmplifierLength x) := by gcongr
    _ = 2 ^ (d * (100 * smoothAmplifierLength x)) := by
      simp only [← pow_mul]
    _ ≤ 2 ^ (2 * m) := by
      exact Nat.pow_le_pow_right (by omega) hexp
    _ = (2 ^ m) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ x ^ 2 := by gcongr

/-! ## Logarithmic parameters with a power-saving cardinality

The preceding binary-logarithm parameters give a particularly short support
calculation.  For the cardinality estimate it is more convenient to work over
the reals.  We take `y = ⌊(log x)^32⌋` and
`r = ⌊log x / (16 log log x)⌋`. -/

private lemma half_primeCounting_le_sub {y r : ℕ}
    (hr : 2 * r ≤ Nat.primeCounting y) :
    (Nat.primeCounting y : ℝ) / 2 ≤
      ((Nat.primeCounting y + 1 - r : ℕ) : ℝ) := by
  have hrR : 2 * (r : ℝ) ≤ (Nat.primeCounting y : ℝ) := by exact_mod_cast hr
  rw [Nat.cast_sub (by omega)]
  push_cast
  linarith

private lemma choose_ge_of_mul_factorial_le_pow_sub
    {m r : ℕ} {z target : ℝ} (hz : 0 ≤ z)
    (hbase : z ≤ ((m + 1 - r : ℕ) : ℝ))
    (htarget : target * (r.factorial : ℝ) ≤ z ^ r) :
    target ≤ (m.choose r : ℝ) := by
  have hfac : (0 : ℝ) < r.factorial := by positivity
  calc
    target ≤ z ^ r / (r.factorial : ℝ) :=
      (le_div_iff₀ hfac).2 htarget
    _ ≤ (((m + 1 - r : ℕ) : ℝ) ^ r) / (r.factorial : ℝ) := by
      gcongr
    _ ≤ (m.choose r : ℝ) := Nat.pow_le_choose r m

/-- A finite cardinality reduction tailored to the chosen logarithmic
scale. -/
theorem choose_primeCounting_ge_of_log_scale
    {y r : ℕ} {t target : ℝ} (ht : 1 ≤ t)
    (hpiPower : 2 * t ^ (30 : ℕ) ≤ Nat.primeCounting y)
    (hrpi : 2 * r ≤ Nat.primeCounting y)
    (hrScale : (r : ℝ) ≤ t)
    (hgrowth : target ≤ t ^ ((29 : ℕ) * r)) :
    target ≤ ((Nat.primeCounting y).choose r : ℝ) := by
  let z : ℝ := t ^ (30 : ℕ)
  have hz : 0 ≤ z := by positivity
  have hbase : z ≤ ((Nat.primeCounting y + 1 - r : ℕ) : ℝ) := by
    apply le_trans ?_ (half_primeCounting_le_sub hrpi)
    dsimp only [z]
    linarith
  apply choose_ge_of_mul_factorial_le_pow_sub hz hbase
  have hfac : (r.factorial : ℝ) ≤ t ^ r := by
    calc
      (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by exact_mod_cast Nat.factorial_le_pow r
      _ ≤ t ^ r := by gcongr
  calc
    target * (r.factorial : ℝ)
        ≤ t ^ ((29 : ℕ) * r) * t ^ r :=
      mul_le_mul hgrowth hfac (by positivity) (by positivity)
    _ = z ^ r := by
      dsimp only [z]
      rw [← pow_add, ← pow_mul]
      congr 1
      omega

/-- The smoothness cutoff at logarithmic height `t`. -/
noncomputable def logarithmicCutoff (t : ℝ) : ℕ :=
  ⌊t ^ (32 : ℝ)⌋₊

/-- The variable product length at logarithmic height `t`. -/
noncomputable def logarithmicLength (t : ℝ) : ℕ :=
  ⌊t / (16 * Real.log t)⌋₊

lemma logarithmicCutoff_pow_logarithmicLength_le_exp_two_mul
    {t : ℝ} (ht : 1 < t) :
    ((logarithmicCutoff t ^ logarithmicLength t : ℕ) : ℝ) ≤
      Real.exp (2 * t) := by
  have hlog : 0 < Real.log t := Real.log_pos ht
  have ht0 : 0 ≤ t := (zero_lt_one.trans ht).le
  have hpow : 0 ≤ t ^ (32 : ℝ) := Real.rpow_nonneg ht0 _
  have hy : (logarithmicCutoff t : ℝ) ≤ t ^ (32 : ℝ) := Nat.floor_le hpow
  have hr : (logarithmicLength t : ℝ) ≤ t / (16 * Real.log t) := by
    exact Nat.floor_le (div_nonneg ht0 (mul_nonneg (by norm_num) hlog.le))
  calc
    ((logarithmicCutoff t ^ logarithmicLength t : ℕ) : ℝ)
        = (logarithmicCutoff t : ℝ) ^ logarithmicLength t := by norm_cast
    _ ≤ (t ^ (32 : ℝ)) ^ logarithmicLength t := by gcongr
    _ = Real.exp ((32 : ℝ) * logarithmicLength t * Real.log t) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht0,
        Real.rpow_def_of_pos (zero_lt_one.trans ht)]
      congr 1
      ring
    _ ≤ Real.exp (2 * t) := by
      apply Real.exp_le_exp.mpr
      have hmul := (le_div_iff₀ (show 0 < 16 * Real.log t by positivity)).mp hr
      nlinarith

lemma logarithmicCutoff_pow_logarithmicLength_le_sq {x : ℕ}
    (hx : 3 ≤ x) :
    logarithmicCutoff (Real.log x) ^ logarithmicLength (Real.log x) ≤ x ^ 2 := by
  have hxR : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have ht : 1 < Real.log (x : ℝ) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    calc
      Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      _ ≤ 3 := by norm_num
      _ ≤ (x : ℝ) := by exact_mod_cast hx
  have h := logarithmicCutoff_pow_logarithmicLength_le_exp_two_mul ht
  rw [show 2 * Real.log (x : ℝ) = Real.log (x : ℝ) + Real.log (x : ℝ) by ring,
    Real.exp_add, Real.exp_log (by positivity)] at h
  have hn : logarithmicCutoff (Real.log x) ^ logarithmicLength (Real.log x) ≤
      x * x := by exact_mod_cast h
  simpa [pow_two] using hn

lemma tendsto_logarithmicCutoff_atTop :
    Tendsto logarithmicCutoff atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 32))

/-- The PNT supplies far more primes than the variable product length needs. -/
theorem eventually_logarithmic_primeCounting_lower :
    ∀ᶠ t : ℝ in atTop,
      2 * t ^ (30 : ℕ) ≤ (Nat.primeCounting (logarithmicCutoff t) : ℝ) := by
  obtain ⟨c, hc, hpi⟩ := pi_alt
  have hcBound := hc.bound (show (0 : ℝ) < 1 / 2 by norm_num)
  have hpow : Tendsto (fun t : ℝ ↦ t ^ (32 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hcScaled := hpow.eventually hcBound
  have hlogSmall :=
    (isLittleO_log_rpow_atTop (r := (2 : ℝ)) (by norm_num)).bound
      (show (0 : ℝ) < 1 / 128 by norm_num)
  filter_upwards [hcScaled, hlogSmall, eventually_gt_atTop 1] with t hct hlt ht
  have ht0 : 0 ≤ t := (zero_lt_one.trans ht).le
  have hlog : 0 < Real.log t := Real.log_pos ht
  have hcLower : (1 / 2 : ℝ) ≤ 1 + c (t ^ (32 : ℝ)) := by
    have := (abs_le.mp (show |c (t ^ (32 : ℝ))| ≤ (1 / 2 : ℝ) by
      simpa using hct)).1
    linarith
  have hlogSmall' : 128 * Real.log t ≤ t ^ (2 : ℕ) := by
    have habs : |Real.log t| ≤ (1 / 128 : ℝ) * |t ^ (2 : ℝ)| := by
      simpa only [Real.norm_eq_abs] using hlt
    rw [abs_of_pos hlog, abs_of_nonneg (Real.rpow_nonneg ht0 _)] at habs
    have hpow2 : t ^ (2 : ℝ) = t ^ (2 : ℕ) := Real.rpow_natCast t 2
    rw [hpow2] at habs
    calc
      128 * Real.log t ≤ 128 * ((1 / 128 : ℝ) * t ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left habs (by norm_num)
      _ = t ^ (2 : ℕ) := by ring
  simp only [logarithmicCutoff]
  rw [hpi (t ^ (32 : ℝ))]
  rw [Real.log_rpow (zero_lt_one.trans ht)]
  have hpow32 : t ^ (32 : ℝ) = t ^ (32 : ℕ) := Real.rpow_natCast t 32
  have hden : 0 < (32 : ℝ) * Real.log t := by positivity
  calc
    2 * t ^ (30 : ℕ) ≤ ((1 / 2 : ℝ) * t ^ (32 : ℝ)) /
        ((32 : ℝ) * Real.log t) := by
      rw [hpow32]
      rw [le_div_iff₀ hden]
      have hm := mul_le_mul_of_nonneg_left hlogSmall' (pow_nonneg ht0 30)
      nlinarith [show t ^ (32 : ℕ) = t ^ (30 : ℕ) * t ^ (2 : ℕ) by ring]
    _ ≤ (1 + c (t ^ (32 : ℝ))) * (t ^ (32 : ℝ)) /
        ((32 : ℝ) * Real.log t) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcLower (Real.rpow_nonneg ht0 _)) hden.le

theorem eventually_logarithmicLength_le_scale :
    ∀ᶠ t : ℝ in atTop, (logarithmicLength t : ℝ) ≤ t := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (1 / 16 : ℝ),
    eventually_ge_atTop (1 : ℝ)] with t hlog ht
  have hlog0 : 0 ≤ Real.log t := le_trans (by norm_num) hlog
  calc
    (logarithmicLength t : ℝ) ≤ t / (16 * Real.log t) := by
      exact Nat.floor_le (div_nonneg (by positivity) (mul_nonneg (by norm_num) hlog0))
    _ ≤ t := div_le_self (by positivity) (by nlinarith)

theorem eventually_exp_nine_fifths_le_logarithmic_power :
    ∀ᶠ t : ℝ in atTop,
      Real.exp ((9 / 5 : ℝ) * t) ≤
        t ^ ((29 : ℕ) * logarithmicLength t) := by
  have hlogSmall := Real.isLittleO_log_id_atTop.bound
    (show (0 : ℝ) < 1 / 2320 by norm_num)
  filter_upwards [hlogSmall, eventually_gt_atTop (1 : ℝ)] with t hsmall ht
  have ht0 : 0 ≤ t := (zero_lt_one.trans ht).le
  have hlog : 0 < Real.log t := Real.log_pos ht
  have hlogBound : 2320 * Real.log t ≤ t := by
    have habs : |Real.log t| ≤ (1 / 2320 : ℝ) * |t| := by
      simpa only [Real.norm_eq_abs, id_eq] using hsmall
    rw [abs_of_pos hlog, abs_of_pos (zero_lt_one.trans ht)] at habs
    calc
      2320 * Real.log t ≤ 2320 * ((1 / 2320 : ℝ) * t) :=
        mul_le_mul_of_nonneg_left habs (by norm_num)
      _ = t := by ring
  have hfloor := Nat.lt_floor_add_one (t / (16 * Real.log t))
  have hden : 0 < 16 * Real.log t := by positivity
  have hfloor' : t < ((logarithmicLength t : ℝ) + 1) *
      (16 * Real.log t) := by
    exact (div_lt_iff₀ hden).mp (by simpa [logarithmicLength] using hfloor)
  have hexponent : (9 / 5 : ℝ) * t ≤
      ((29 : ℕ) * logarithmicLength t : ℕ) * Real.log t := by
    push_cast
    nlinarith
  let n : ℕ := (29 : ℕ) * logarithmicLength t
  have hrhs : t ^ n = Real.exp ((n : ℝ) * Real.log t) := by
    calc
      t ^ n = t ^ (n : ℝ) := (Real.rpow_natCast t n).symm
      _ = Real.exp (Real.log t * (n : ℝ)) :=
        Real.rpow_def_of_pos (zero_lt_one.trans ht) _
      _ = Real.exp ((n : ℝ) * Real.log t) := by ring_nf
  change Real.exp ((9 / 5 : ℝ) * t) ≤ t ^ n
  rw [hrhs]
  exact Real.exp_le_exp.mpr (by simpa [n, mul_comm] using hexponent)

theorem eventually_logarithmic_parameters_real :
    ∀ᶠ t : ℝ in atTop,
      logarithmicLength t ≤ Nat.primeCounting (logarithmicCutoff t) ∧
      Real.exp ((9 / 5 : ℝ) * t) ≤
        ((Nat.primeCounting (logarithmicCutoff t)).choose
          (logarithmicLength t) : ℝ) := by
  filter_upwards [eventually_logarithmic_primeCounting_lower,
    eventually_logarithmicLength_le_scale,
    eventually_exp_nine_fifths_le_logarithmic_power,
    eventually_ge_atTop (1 : ℝ)] with t hpi hrScale hgrowth ht
  have htPower : t ≤ t ^ (30 : ℕ) := by
    simpa using pow_le_pow_right₀ ht (by norm_num : (1 : ℕ) ≤ 30)
  have hrpiR : (2 * logarithmicLength t : ℕ) ≤
      Nat.primeCounting (logarithmicCutoff t) := by
    have hrpiR' : (2 * logarithmicLength t : ℕ) ≤
        (Nat.primeCounting (logarithmicCutoff t) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hrpiR'
  refine ⟨by omega, ?_⟩
  exact choose_primeCounting_ge_of_log_scale ht hpi hrpiR hrScale hgrowth

/-- Concrete smoothness parameter at modulus scale `x`. -/
noncomputable def smoothParameterY (x : ℕ) : ℕ :=
  logarithmicCutoff (Real.log (x : ℝ))

/-- Concrete product length at modulus scale `x`. -/
noncomputable def smoothParameterR (x : ℕ) : ℕ :=
  logarithmicLength (Real.log (x : ℝ))

/-- In particular, the smoothness cutoff tends to infinity. -/
theorem tendsto_smoothParameterY_atTop :
    Tendsto smoothParameterY atTop atTop := by
  exact tendsto_logarithmicCutoff_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- The complete eventual parameter package.  The amplifier fits in
`Ioc 0 (x²)` and has the stronger-than-needed cardinality `x^(9/5)`. -/
theorem eventually_smooth_parameters :
    ∀ᶠ x : ℕ in atTop,
      smoothParameterR x ≤ Nat.primeCounting (smoothParameterY x) ∧
      smoothParameterY x ^ smoothParameterR x ≤ x ^ 2 ∧
      (x : ℝ) ^ (9 / 5 : ℝ) ≤
        ((Nat.primeCounting (smoothParameterY x)).choose
          (smoothParameterR x) : ℝ) := by
  have hlogNat : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hparams := hlogNat.eventually eventually_logarithmic_parameters_real
  filter_upwards [hparams, eventually_ge_atTop 3] with x hp hx
  have hxpos : (0 : ℝ) < x := by positivity
  have hchoose : (x : ℝ) ^ (9 / 5 : ℝ) ≤
      ((Nat.primeCounting (smoothParameterY x)).choose (smoothParameterR x) : ℝ) := by
    calc
      (x : ℝ) ^ (9 / 5 : ℝ) =
          Real.exp (Real.log (x : ℝ) * (9 / 5 : ℝ)) :=
        Real.rpow_def_of_pos hxpos _
      _ = Real.exp ((9 / 5 : ℝ) * Real.log (x : ℝ)) := by ring_nf
      _ ≤ ((Nat.primeCounting (smoothParameterY x)).choose
          (smoothParameterR x) : ℝ) := by
        simpa only [smoothParameterY, smoothParameterR] using hp.2
  refine ⟨by simpa only [smoothParameterY, smoothParameterR] using hp.1,
    ?_, hchoose⟩
  simpa only [smoothParameterY, smoothParameterR] using
    (logarithmicCutoff_pow_logarithmicLength_le_sq hx)

/-- Unconditional power-saving rarity for the concrete logarithmic cutoff.
This is the direct Elliott large-sieve output: only `O(x^(1/5))` eligible
prime moduli up to `x` can have least nonresidue above `smoothParameterY x`. -/
theorem eventually_largeLeastKthPowerNonresiduePrimes_card_le
    (k : ℕ) (hk : 2 ≤ k) :
    ∀ᶠ x : ℕ in atTop,
      ((largeLeastKthPowerNonresiduePrimes
          k x (smoothParameterY x)).card : ℝ) ≤
        2 * (x : ℝ) ^ (1 / 5 : ℝ) := by
  filter_upwards [eventually_smooth_parameters, eventually_ge_atTop 1]
      with x hp hx
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hLpos : 0 < (x : ℝ) ^ (9 / 5 : ℝ) :=
    Real.rpow_pos_of_pos hxR _
  have hmain := largeLeastKthPowerNonresiduePrimes_card_le_of_parameters
    k x (smoothParameterY x) (smoothParameterR x) (x ^ 2)
    ((x : ℝ) ^ (9 / 5 : ℝ)) hk hp.1 hp.2.1 hLpos hp.2.2
  refine hmain.trans_eq ?_
  rw [div_eq_iff hLpos.ne']
  have hrpow :
      (x : ℝ) ^ (1 / 5 : ℝ) * (x : ℝ) ^ (9 / 5 : ℝ) =
        (x : ℝ) ^ 2 := by
    rw [← Real.rpow_add hxR]
    norm_num
  push_cast
  nlinarith

end

end Erdos980.ElliottTail
