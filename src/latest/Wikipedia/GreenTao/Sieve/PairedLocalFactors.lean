import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Squarefree
import Wikipedia.GreenTao.Sieve.LocalFactors
import Wikipedia.GreenTao.Sieve.LocalEulerFactors
import Wikipedia.GreenTao.Sieve.PairedDivisibilityCRT

/-!
# Squarefree paired divisors and finite-family local factors

The Selberg expansion only receives a contribution from squarefree divisor
choices: a nonzero Möbius coefficient forces each of the two divisors attached
to every form to be squarefree.  Consequently all local least common multiples,
and their global least common multiple, are squarefree.  The canonical
prime-power CRT from `PairedDivisibilityCRT` therefore has exponent one at
every prime.

This file records that reduction exactly.  It also packages the local
intersection density of an arbitrary finite subfamily of affine forms.  The
empty, singleton, and two-element cases reduce to the exact APIs in
`LocalFactors`; the full avoidance factor is their finite
inclusion--exclusion sum.  Higher intersections require an additional
arithmetic input, so the final interface exposes that input as a hypothesis
rather than asserting an unavailable estimate.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Squarefree divisor choices -/

/-- Both divisor choices attached to every form are squarefree. -/
def SquarefreePairedDivisorChoice
    {κ : Type*} (z : κ → ℕ × ℕ) : Prop :=
  ∀ q, Squarefree (z q).1 ∧ Squarefree (z q).2

/-- A nonzero coefficient in the Selberg divisor expansion has squarefree
support.  This is the precise way in which the Möbius factors eliminate
nonsquarefree divisor choices. -/
theorem squarefreePairedDivisorChoice_of_coefficient_ne_zero
    {κ : Type*} [Fintype κ]
    (χ : ℝ → ℝ) (R : ℕ) (z : κ → ℕ × ℕ)
    (hz : smoothDivisorFamilyCoefficient χ R z ≠ 0) :
    SquarefreePairedDivisorChoice z := by
  intro q
  have hzq :
      smoothDivisorSummand χ R (z q).1 *
          smoothDivisorSummand χ R (z q).2 ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hz) q (Finset.mem_univ q)
  have hleftR :
      (ArithmeticFunction.moebius (z q).1 : ℝ) ≠ 0 := by
    intro hzero
    apply (mul_ne_zero_iff.mp hzq).1
    simp [smoothDivisorSummand, hzero]
  have hrightR :
      (ArithmeticFunction.moebius (z q).2 : ℝ) ≠ 0 := by
    intro hzero
    apply (mul_ne_zero_iff.mp hzq).2
    simp [smoothDivisorSummand, hzero]
  have hleft :
      ArithmeticFunction.moebius (z q).1 ≠ 0 := by
    exact_mod_cast hleftR
  have hright :
      ArithmeticFunction.moebius (z q).2 ≠ 0 := by
    exact_mod_cast hrightR
  exact
    ⟨ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hleft,
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hright⟩

/-- The least common multiple of two squarefree naturals is squarefree. -/
theorem squarefree_nat_lcm
    {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  have hab0 : Nat.lcm a b ≠ 0 := by
    rw [← lcm_eq_nat_lcm]
    exact lcm_ne_zero_iff.mpr ⟨ha.ne_zero, hb.ne_zero⟩
  rw [Nat.squarefree_iff_factorization_le_one hab0]
  intro p
  rw [Nat.factorization_lcm ha.ne_zero hb.ne_zero]
  exact sup_le
    (ha.natFactorization_le_one p)
    (hb.natFactorization_le_one p)

/-- Every per-form modulus of a squarefree paired choice is squarefree. -/
theorem squarefree_pairedLocalModulus
    {κ : Type*} {z : κ → ℕ × ℕ}
    (hz : SquarefreePairedDivisorChoice z) (q : κ) :
    Squarefree (pairedLocalModulus z q) := by
  exact squarefree_nat_lcm (hz q).1 (hz q).2

/-- A finite least common multiple of squarefree naturals is squarefree. -/
theorem squarefree_finset_lcm
    {κ : Type*} [DecidableEq κ]
    (s : Finset κ) (f : κ → ℕ)
    (hf : ∀ q ∈ s, Squarefree (f q)) :
    Squarefree (s.lcm f) := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert q s hqs ih =>
      rw [Finset.lcm_insert]
      exact squarefree_nat_lcm
        (hf q (Finset.mem_insert_self q s))
        (ih fun r hr => hf r (Finset.mem_insert_of_mem hr))

/-- The global LCM of a squarefree paired choice is squarefree. -/
theorem squarefree_pairedDivisorLcm
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {z : κ → ℕ × ℕ}
    (hz : SquarefreePairedDivisorChoice z) :
    Squarefree (pairedDivisorLcm z) := by
  rw [pairedDivisorLcm_eq_lcm_pairedLocalModulus]
  exact squarefree_finset_lcm Finset.univ
    (pairedLocalModulus z)
    (fun q _hq => squarefree_pairedLocalModulus hz q)

/-- Every canonical exponent of the global paired LCM is one. -/
theorem pairedDivisorLcm_factorization_eq_one
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {z : κ → ℕ × ℕ}
    (hz : SquarefreePairedDivisorChoice z)
    (p : (pairedDivisorLcm z).primeFactors) :
    (pairedDivisorLcm z).factorization p = 1 := by
  exact Nat.factorization_eq_one_of_squarefree
    (squarefree_pairedDivisorLcm hz)
    (Nat.prime_of_mem_primeFactors p.2)
    (Nat.dvd_of_mem_primeFactors p.2)

/-- Thus the canonical prime-power modulus is literally the prime modulus. -/
theorem pairedDivisorLcm_primePower_eq_prime
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {z : κ → ℕ × ℕ}
    (hz : SquarefreePairedDivisorChoice z)
    (p : (pairedDivisorLcm z).primeFactors) :
    (p : ℕ) ^ (pairedDivisorLcm z).factorization p = p := by
  rw [pairedDivisorLcm_factorization_eq_one hz p, pow_one]

/-! ## Exact prime support and the squarefree indicator product -/

/-- Forms whose paired local modulus contains the prime `p`. -/
def pairedPrimeSupport
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (z : κ → ℕ × ℕ) (p : ℕ) : Finset κ :=
  Finset.univ.filter fun q => p ∣ pairedLocalModulus z q

@[simp]
theorem mem_pairedPrimeSupport
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (z : κ → ℕ × ℕ) (p : ℕ) (q : κ) :
    q ∈ pairedPrimeSupport z p ↔ p ∣ pairedLocalModulus z q := by
  simp [pairedPrimeSupport]

/-- The prime support of the global paired LCM is the union of the prime
supports of its per-form local moduli. -/
theorem mem_primeFactors_pairedDivisorLcm_iff
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {z : κ → ℕ × ℕ}
    (hz : SquarefreePairedDivisorChoice z) (p : ℕ) :
    p ∈ (pairedDivisorLcm z).primeFactors ↔
      p.Prime ∧ (pairedPrimeSupport z p).Nonempty := by
  have hD0 : pairedDivisorLcm z ≠ 0 :=
    (squarefree_pairedDivisorLcm hz).ne_zero
  rw [Nat.mem_primeFactors_of_ne_zero hD0]
  constructor
  · rintro ⟨hp, hpD⟩
    have hpProd :
        p ∣ ∏ q, pairedLocalModulus z q :=
      hpD.trans (by
        rw [pairedDivisorLcm_eq_lcm_pairedLocalModulus]
        exact Finset.lcm_dvd_prod Finset.univ
          (pairedLocalModulus z))
    obtain ⟨q, _hq, hpq⟩ :=
      (hp.prime.dvd_finsetProd_iff
        (pairedLocalModulus z)).mp hpProd
    exact ⟨hp, ⟨q, by simp [hpq]⟩⟩
  · rintro ⟨hp, ⟨q, hq⟩⟩
    rw [pairedDivisorLcm_eq_lcm_pairedLocalModulus]
    exact ⟨hp, (mem_pairedPrimeSupport z p q).mp hq |>.trans
      (Finset.dvd_lcm (f := pairedLocalModulus z)
        (Finset.mem_univ q))⟩

/-- The local factor carried by a prime in the squarefree paired indicator:
every form in the prime support contributes one divisibility indicator. -/
noncomputable def squarefreePairedPrimeIndicator
    {κ X : Type*} [Fintype κ] [DecidableEq κ]
    (values : κ → X → ℕ) (z : κ → ℕ × ℕ)
    (p : ℕ) (x : X) : ℝ :=
  ∏ q ∈ pairedPrimeSupport z p,
    natDivisibilityIndicator p (values q x)

/-- For squarefree choices, the paired indicator is exactly a product over
the primes of the global LCM, with one factor for every form containing that
prime. -/
theorem pairedDivisibilityIndicator_eq_squarefreePrimeProduct
    {κ X : Type*} [Fintype κ] [DecidableEq κ]
    (values : κ → X → ℕ) (z : κ → ℕ × ℕ)
    (hz : SquarefreePairedDivisorChoice z) (x : X) :
    pairedDivisibilityIndicator values z x =
      ∏ p : (pairedDivisorLcm z).primeFactors,
        squarefreePairedPrimeIndicator values z p x := by
  classical
  by_cases hx :
      ∀ q, pairedLocalModulus z q ∣ values q x
  · have hleft :
        pairedDivisibilityIndicator values z x = 1 := by
      rw [pairedDivisibilityIndicator_eq_lcmProduct]
      apply Finset.prod_eq_one
      intro q _hq
      simp [natDivisibilityIndicator, hx q]
    have hright :
        (∏ p : (pairedDivisorLcm z).primeFactors,
          squarefreePairedPrimeIndicator values z p x) = 1 := by
      apply Finset.prod_eq_one
      intro p _hp
      unfold squarefreePairedPrimeIndicator
      apply Finset.prod_eq_one
      intro q hq
      have hpq :
          (p : ℕ) ∣ pairedLocalModulus z q :=
        (mem_pairedPrimeSupport z p q).mp hq
      simp [natDivisibilityIndicator, hpq.trans (hx q)]
    rw [hleft, hright]
  · simp only [not_forall] at hx
    obtain ⟨q, hq⟩ := hx
    have hm0 : pairedLocalModulus z q ≠ 0 :=
      (squarefree_pairedLocalModulus hz q).ne_zero
    have hprimePower :
        ¬ ∀ p : (pairedLocalModulus z q).primeFactors,
          (p : ℕ) ^
              (pairedLocalModulus z q).factorization p ∣
            values q x := by
      exact fun h => hq ((dvd_iff_primePower_dvd hm0).mpr h)
    simp only [not_forall] at hprimePower
    obtain ⟨p, hpvalue⟩ := hprimePower
    have hpexponent :
        (pairedLocalModulus z q).factorization p = 1 :=
      Nat.factorization_eq_one_of_squarefree
        (squarefree_pairedLocalModulus hz q)
        (Nat.prime_of_mem_primeFactors p.2)
        (Nat.dvd_of_mem_primeFactors p.2)
    have hpnot : ¬ (p : ℕ) ∣ values q x := by
      simpa [hpexponent] using hpvalue
    have hpD :
        (p : ℕ) ∈ (pairedDivisorLcm z).primeFactors := by
      rw [mem_primeFactors_pairedDivisorLcm_iff hz]
      exact
        ⟨Nat.prime_of_mem_primeFactors p.2,
          ⟨q, by
            exact (mem_pairedPrimeSupport z p q).mpr
              (Nat.dvd_of_mem_primeFactors p.2)⟩⟩
    let pD : (pairedDivisorLcm z).primeFactors :=
      ⟨p, hpD⟩
    have hleft :
        pairedDivisibilityIndicator values z x = 0 := by
      rw [pairedDivisibilityIndicator_eq_lcmProduct]
      apply Finset.prod_eq_zero (Finset.mem_univ q)
      simp [natDivisibilityIndicator, hq]
    have hright :
        (∏ r : (pairedDivisorLcm z).primeFactors,
          squarefreePairedPrimeIndicator values z r x) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ pD)
      unfold squarefreePairedPrimeIndicator
      apply Finset.prod_eq_zero
      · exact (mem_pairedPrimeSupport z pD q).mpr
          (Nat.dvd_of_mem_primeFactors p.2)
      · simp [natDivisibilityIndicator, pD, hpnot]
    rw [hleft, hright]

/-! ## Arbitrary finite-family intersection densities -/

/-- Product of zero-congruence indicators over a selected subfamily. -/
noncomputable def affineFamilyZeroProduct
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (s : Finset κ) (x : ι → ZMod p) : ℝ :=
  ∏ q ∈ s, finsetIndicator ((forms q).zeroFinsetZMod p) x

/-- The exact normalized density of the common zero set of a selected finite
subfamily. -/
noncomputable def affineFamilyZeroDensity
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (s : Finset κ) : ℝ :=
  mean (affineFamilyZeroProduct p forms s)

/-- Explicit common-zero support of a selected finite subfamily. -/
def affineFamilyCommonZeroFinset
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (s : Finset κ) : Finset (ι → ZMod p) :=
  Finset.univ.filter fun x =>
    ∀ q ∈ s, (forms q).evalZMod p x = 0

@[simp]
theorem mem_affineFamilyCommonZeroFinset
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (s : Finset κ) (x : ι → ZMod p) :
    x ∈ affineFamilyCommonZeroFinset p forms s ↔
      ∀ q ∈ s, (forms q).evalZMod p x = 0 := by
  simp [affineFamilyCommonZeroFinset]

/-- The product definition is the indicator of the simultaneous zero set. -/
theorem affineFamilyZeroProduct_eq_indicator
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (s : Finset κ) :
    affineFamilyZeroProduct p forms s =
      finsetIndicator (affineFamilyCommonZeroFinset p forms s) := by
  classical
  funext x
  by_cases hx : ∀ q ∈ s, (forms q).evalZMod p x = 0
  · have hmem :
        x ∈ affineFamilyCommonZeroFinset p forms s := by
      exact (mem_affineFamilyCommonZeroFinset p forms s x).mpr hx
    rw [show
      finsetIndicator (affineFamilyCommonZeroFinset p forms s) x = 1 by
        simp [finsetIndicator, hmem]]
    unfold affineFamilyZeroProduct
    apply Finset.prod_eq_one
    intro q hq
    have hqmem : x ∈ (forms q).zeroFinsetZMod p := by
      exact AffineForm.mem_zeroFinsetZMod p (forms q) x |>.mpr
        (hx q hq)
    simp [finsetIndicator, hqmem]
  · push Not at hx
    obtain ⟨q, hqs, hqzero⟩ := hx
    have hnotmem :
        x ∉ affineFamilyCommonZeroFinset p forms s := by
      intro hmem
      exact hqzero
        ((mem_affineFamilyCommonZeroFinset p forms s x).mp
          hmem q hqs)
    rw [show
      finsetIndicator (affineFamilyCommonZeroFinset p forms s) x = 0 by
        simp [finsetIndicator, hnotmem]]
    unfold affineFamilyZeroProduct
    apply Finset.prod_eq_zero hqs
    have hqnotmem : x ∉ (forms q).zeroFinsetZMod p := by
      simpa using hqzero
    simp [finsetIndicator, hqnotmem]

/-- Cardinality formula for an arbitrary finite-family common-zero density. -/
theorem affineFamilyZeroDensity_eq_card
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (s : Finset κ) :
    affineFamilyZeroDensity p forms s =
      ((affineFamilyCommonZeroFinset p forms s).card : ℝ) /
        Fintype.card (ι → ZMod p) := by
  rw [affineFamilyZeroDensity,
    affineFamilyZeroProduct_eq_indicator]
  exact mean_finsetIndicator _

@[simp]
theorem affineFamilyZeroDensity_empty
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ) :
    affineFamilyZeroDensity p forms ∅ = 1 := by
  unfold affineFamilyZeroDensity
  rw [show affineFamilyZeroProduct p forms ∅ =
      fun _x => (1 : ℝ) by
    funext x
    simp [affineFamilyZeroProduct]]
  exact mean_const (α := ι → ZMod p) 1

/-- A singleton family is the existing one-form zero density. -/
theorem affineFamilyZeroDensity_singleton
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (q : κ) :
    affineFamilyZeroDensity p forms {q} =
      mean (finsetIndicator ((forms q).zeroFinsetZMod p)) := by
  unfold affineFamilyZeroDensity
  congr 1
  funext x
  simp [affineFamilyZeroProduct]

/-- A two-element family is the existing mixed zero-indicator moment. -/
theorem affineFamilyZeroDensity_pair
    {κ ι : Type*} [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    {q r : κ} (hqr : q ≠ r) :
    affineFamilyZeroDensity p forms {q, r} =
      mean (fun x =>
        finsetIndicator ((forms q).zeroFinsetZMod p) x *
          finsetIndicator ((forms r).zeroFinsetZMod p) x) := by
  unfold affineFamilyZeroDensity
  congr 1
  funext x
  simp [affineFamilyZeroProduct, hqr]

/-- Exact singleton density outside the exceptional-prime range. -/
theorem affineFamilyZeroDensity_singleton_of_bound
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hforms : NonzeroCoefficientVectors forms)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p) (q : κ) :
    affineFamilyZeroDensity p forms {q} = (1 : ℝ) / p := by
  rw [affineFamilyZeroDensity_singleton]
  exact mean_zeroFinsetZMod_of_bound hforms hp hlarge q

/-- Exact two-form density outside the exceptional-prime range. -/
theorem affineFamilyZeroDensity_pair_of_bound
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hforms : PairwiseIndependentCoefficients forms)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p)
    {q r : κ} (hqr : q ≠ r) :
    affineFamilyZeroDensity p forms {q, r} =
      (1 : ℝ) / (p : ℝ) ^ 2 := by
  rw [affineFamilyZeroDensity_pair p forms hqr]
  exact mean_zeroFinsetZMod_mul_of_bound
    hforms hp hlarge hqr

/-- Existing local-factor APIs determine every selected-family density of
cardinality at most two. -/
theorem affineFamilyZeroDensity_of_card_le_two
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p)
    (s : Finset κ) (hs : s.card ≤ 2) :
    affineFamilyZeroDensity p forms s =
      (1 : ℝ) / (p : ℝ) ^ s.card := by
  rcases Nat.eq_zero_or_pos s.card with hzero | hpos
  · have hs0 : s = ∅ := Finset.card_eq_zero.mp hzero
    subst s
    simp
  · have hcard : s.card = 1 ∨ s.card = 2 := by
      omega
    rcases hcard with hone | htwo
    · obtain ⟨q, rfl⟩ := Finset.card_eq_one.mp hone
      simpa using
        affineFamilyZeroDensity_singleton_of_bound
          hnonzero hp hlarge q
    · obtain ⟨q, r, hqr, rfl⟩ :=
        Finset.card_eq_two.mp htwo
      have hcard : ({q, r} : Finset κ).card = 2 :=
        Finset.card_eq_two.mpr ⟨q, r, hqr, rfl⟩
      rw [hcard]
      exact affineFamilyZeroDensity_pair_of_bound
        hindependent hp hlarge hqr

/-! ## Exact arbitrary-family local factor formula -/

/-- Pointwise inclusion--exclusion for the local avoidance product. -/
theorem localAvoidanceProduct_eq_inclusionExclusion
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (x : ι → ZMod p) :
    localAvoidanceProduct p forms x =
      ∑ s ∈ (Finset.univ : Finset κ).powerset,
        (-1 : ℝ) ^ s.card *
          affineFamilyZeroProduct p forms s x := by
  let I : κ → ℝ :=
    fun q => finsetIndicator ((forms q).zeroFinsetZMod p) x
  have h :=
    Finset.prod_sub (fun _q : κ => (1 : ℝ)) I
      (Finset.univ : Finset κ)
  simpa [localAvoidanceProduct, affineFamilyZeroProduct, I]
    using h

/-- The exact local avoidance density is the inclusion--exclusion sum of all
finite-family common-zero densities. -/
theorem mean_localAvoidanceProduct_eq_inclusionExclusion
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ) :
    mean (localAvoidanceProduct p forms) =
      ∑ s ∈ (Finset.univ : Finset κ).powerset,
        (-1 : ℝ) ^ s.card *
          affineFamilyZeroDensity p forms s := by
  rw [show localAvoidanceProduct p forms =
      fun x =>
        ∑ s ∈ (Finset.univ : Finset κ).powerset,
          (-1 : ℝ) ^ s.card *
            affineFamilyZeroProduct p forms s x by
    funext x
    exact localAvoidanceProduct_eq_inclusionExclusion
      p forms x]
  calc
    mean (fun x =>
        ∑ s ∈ (Finset.univ : Finset κ).powerset,
          (-1 : ℝ) ^ s.card *
            affineFamilyZeroProduct p forms s x) =
        ∑ s ∈ (Finset.univ : Finset κ).powerset,
          mean (fun x =>
            (-1 : ℝ) ^ s.card *
              affineFamilyZeroProduct p forms s x) :=
      mean_finset_sum
        (Finset.univ : Finset κ).powerset
        (fun s x =>
          (-1 : ℝ) ^ s.card *
            affineFamilyZeroProduct p forms s x)
    _ = ∑ s ∈ (Finset.univ : Finset κ).powerset,
          (-1 : ℝ) ^ s.card *
            affineFamilyZeroDensity p forms s := by
      apply Finset.sum_congr rfl
      intro s _hs
      exact mean_smul _ _

/-- Exact arbitrary finite-system formula for the normalized local Euler
factor. -/
theorem mean_systemLocalCoprimeWeight_eq_inclusionExclusion
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ) :
    mean (systemLocalCoprimeWeight p forms) =
      ((p : ℝ) / (p - 1 : ℕ)) ^ Fintype.card κ *
        ∑ s ∈ (Finset.univ : Finset κ).powerset,
          (-1 : ℝ) ^ s.card *
            affineFamilyZeroDensity p forms s := by
  rw [mean_systemLocalCoprimeWeight_eq,
    mean_localAvoidanceProduct_eq_inclusionExclusion]

/-- The additional input needed beyond the exact zero-, one-, and two-form
calculations: a user-supplied bound for every higher common-zero density at
good primes.  No such bound is asserted here. -/
def HasGoodPrimeHigherOrderDensityEstimate
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (forms : κ → AffineForm ι ℤ)
    (majorant : ℕ → Finset κ → ℝ) : Prop :=
  ∀ (p : ℕ) [NeZero p], p.Prime →
    exceptionalPrimeBound forms < p →
    ∀ s : Finset κ, 3 ≤ s.card →
      |affineFamilyZeroDensity p forms s| ≤ majorant p s

/-! ## Localization of the canonical CRT factors -/

/-- For a squarefree global LCM, transport a canonical prime-power residue
vector to the corresponding prime residue vector. -/
def squarefreePrimePowerEquiv
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    {z : κ → ℕ × ℕ}
    (hz : SquarefreePairedDivisorChoice z)
    (p : (pairedDivisorLcm z).primeFactors) :
    (ι → ZMod
        ((p : ℕ) ^
          (pairedDivisorLcm z).factorization p)) ≃
      (ι → ZMod (p : ℕ)) :=
  Equiv.cast (by
    rw [pairedDivisorLcm_primePower_eq_prime hz p])

/-- The canonical CRT component, viewed modulo the underlying prime after
the squarefree exponent-one reduction. -/
noncomputable def squarefreeCanonicalPrimeComponent
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    {z : κ → ℕ × ℕ}
    (hz : SquarefreePairedDivisorChoice z)
    (p : (pairedDivisorLcm z).primeFactors)
    (x : ι → ZMod (pairedDivisorLcm z)) :
    ι → ZMod (p : ℕ) := by
  letI : NeZero (pairedDivisorLcm z) :=
    ⟨(squarefree_pairedDivisorLcm hz).ne_zero⟩
  exact squarefreePrimePowerEquiv hz p
    (coordinatePrimePowerEquiv x p)

/-- The canonical prime-local factor attached to an affine system and a
squarefree paired divisor choice. -/
noncomputable def affinePairedPrimeFactor
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (forms : κ → AffineForm ι ℤ)
    (z : κ → ℕ × ℕ)
    (hz : SquarefreePairedDivisorChoice z)
    (p : (pairedDivisorLcm z).primeFactors)
    (x : ι → ZMod
      ((p : ℕ) ^
        (pairedDivisorLcm z).factorization p)) : ℝ :=
  affineFamilyZeroProduct (p : ℕ) forms
    (pairedPrimeSupport z p)
    (squarefreePrimePowerEquiv hz p x)

/-- The mean of the transported canonical prime-power factor is exactly the
finite-family density over the forms containing that prime. -/
theorem mean_affinePairedPrimeFactor_eq
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (forms : κ → AffineForm ι ℤ)
    (z : κ → ℕ × ℕ)
    (hz : SquarefreePairedDivisorChoice z)
    (p : (pairedDivisorLcm z).primeFactors) :
    mean (affinePairedPrimeFactor forms z hz p) =
      affineFamilyZeroDensity (p : ℕ) forms
        (pairedPrimeSupport z p) := by
  unfold affinePairedPrimeFactor affineFamilyZeroDensity mean
  apply Fintype.expect_equiv
    (squarefreePrimePowerEquiv hz p)
  intro x
  rfl

/-- Concrete sufficient condition connecting natural-valued divisibility
conditions on the global CRT space with the affine zero congruences on each
canonical prime component. -/
def PairedDivisibilityHasAffinePrimeModels
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (z : κ → ℕ × ℕ)
    (values :
      κ → (ι → ZMod (pairedDivisorLcm z)) → ℕ)
    (forms : κ → AffineForm ι ℤ)
    (hz : SquarefreePairedDivisorChoice z) : Prop :=
  ∀ (x : ι → ZMod (pairedDivisorLcm z))
      (p : (pairedDivisorLcm z).primeFactors)
      (q : κ), q ∈ pairedPrimeSupport z p →
    ((p : ℕ) ∣ values q x ↔
        (forms q).evalZMod (p : ℕ)
          (squarefreeCanonicalPrimeComponent hz p x) = 0)

/-- Under the explicit affine-model hypothesis, the paired indicator
separates into the canonical affine prime factors. -/
theorem pairedDivisibilityIndicator_eq_affinePrimeProduct
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (values :
      κ → (ι → ZMod (pairedDivisorLcm z)) → ℕ)
    (forms : κ → AffineForm ι ℤ)
    (hz : SquarefreePairedDivisorChoice z)
    (hmodel :
      PairedDivisibilityHasAffinePrimeModels
        z values forms hz)
    (x : ι → ZMod (pairedDivisorLcm z)) :
    pairedDivisibilityIndicator values z x =
      ∏ p : (pairedDivisorLcm z).primeFactors,
        affinePairedPrimeFactor forms z hz p
          (coordinatePrimePowerEquiv x p) := by
  rw [pairedDivisibilityIndicator_eq_squarefreePrimeProduct
    values z hz x]
  apply Finset.prod_congr rfl
  intro p _hp
  unfold squarefreePairedPrimeIndicator
    affinePairedPrimeFactor affineFamilyZeroProduct
  apply Finset.prod_congr rfl
  intro q hq
  have hiff := hmodel x p q hq
  change natDivisibilityIndicator (p : ℕ) (values q x) =
    finsetIndicator ((forms q).zeroFinsetZMod (p : ℕ))
      (squarefreePrimePowerEquiv hz p
        (coordinatePrimePowerEquiv x p))
  by_cases hpvalue : (p : ℕ) ∣ values q x
  · have heval := hiff.mp hpvalue
    simp [natDivisibilityIndicator, hpvalue, finsetIndicator,
      squarefreeCanonicalPrimeComponent] at heval ⊢
    exact heval
  · have heval : ¬
        (forms q).evalZMod (p : ℕ)
          (squarefreeCanonicalPrimeComponent hz p x) = 0 :=
      fun hzero => hpvalue (hiff.mpr hzero)
    simp [natDivisibilityIndicator, hpvalue, finsetIndicator,
      squarefreeCanonicalPrimeComponent] at heval ⊢
    exact heval

/-- Squarefree paired divisor densities localize exactly to the arbitrary
finite-family affine densities, one for the forms containing each prime. -/
theorem pairedDivisibilityDensity_eq_prod_affineFamilyZeroDensity
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (values :
      κ → (ι → ZMod (pairedDivisorLcm z)) → ℕ)
    (forms : κ → AffineForm ι ℤ)
    (hz : SquarefreePairedDivisorChoice z)
    (hmodel :
      PairedDivisibilityHasAffinePrimeModels
        z values forms hz) :
    pairedDivisibilityDensity values z =
      ∏ p : (pairedDivisorLcm z).primeFactors,
          affineFamilyZeroDensity (p : ℕ) forms
            (pairedPrimeSupport z p) := by
  calc
    pairedDivisibilityDensity values z =
        ∏ p : (pairedDivisorLcm z).primeFactors,
          mean (affinePairedPrimeFactor forms z hz p) := by
      apply pairedDivisibilityDensity_eq_prod_primePowerMeans
        values z (affinePairedPrimeFactor forms z hz)
      intro x
      exact pairedDivisibilityIndicator_eq_affinePrimeProduct
        z values forms hz hmodel x
    _ = ∏ p : (pairedDivisorLcm z).primeFactors,
          affineFamilyZeroDensity (p : ℕ) forms
            (pairedPrimeSupport z p) := by
      apply Finset.prod_congr rfl
      intro p _hp
      exact mean_affinePairedPrimeFactor_eq forms z hz p

/-- If at most two forms contain a prime, the mean of its canonical
prime-power factor is completely determined by the existing one- and
two-form local-density theorems. -/
theorem mean_affinePairedPrimeFactor_eq_of_support_card_le_two
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (forms : κ → AffineForm ι ℤ)
    (z : κ → ℕ × ℕ)
    (hz : SquarefreePairedDivisorChoice z)
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    (p : (pairedDivisorLcm z).primeFactors)
    (hlarge : exceptionalPrimeBound forms < (p : ℕ))
    (hsupport : (pairedPrimeSupport z p).card ≤ 2) :
    mean (affinePairedPrimeFactor forms z hz p) =
      (1 : ℝ) / (p : ℝ) ^
        (pairedPrimeSupport z p).card := by
  rw [mean_affinePairedPrimeFactor_eq]
  exact affineFamilyZeroDensity_of_card_le_two
    hnonzero hindependent
    (Nat.prime_of_mem_primeFactors p.2)
    hlarge (pairedPrimeSupport z p) hsupport

/-- Concrete low-support specialization of the squarefree CRT formula.
When every prime occurs in at most two paired local moduli, every canonical
factor reduces to the exact `1`, `1 / p`, or `1 / p²` API already proved in
`LocalFactors`. -/
theorem pairedDivisibilityDensity_eq_prod_primeSupportDensity_of_card_le_two
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (values :
      κ → (ι → ZMod (pairedDivisorLcm z)) → ℕ)
    (forms : κ → AffineForm ι ℤ)
    (hz : SquarefreePairedDivisorChoice z)
    (hmodel :
      PairedDivisibilityHasAffinePrimeModels
        z values forms hz)
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    (hlarge :
      ∀ p : (pairedDivisorLcm z).primeFactors,
        exceptionalPrimeBound forms < (p : ℕ))
    (hsupport :
      ∀ p : (pairedDivisorLcm z).primeFactors,
        (pairedPrimeSupport z p).card ≤ 2) :
    pairedDivisibilityDensity values z =
      ∏ p : (pairedDivisorLcm z).primeFactors,
        (1 : ℝ) / (p : ℝ) ^
          (pairedPrimeSupport z p).card := by
  rw [pairedDivisibilityDensity_eq_prod_affineFamilyZeroDensity
    z values forms hz hmodel]
  apply Finset.prod_congr rfl
  intro p _hp
  exact affineFamilyZeroDensity_of_card_le_two
    hnonzero hindependent
    (Nat.prime_of_mem_primeFactors p.2)
    (hlarge p) (pairedPrimeSupport z p) (hsupport p)

end Wikipedia.SzemeredisTheorem
