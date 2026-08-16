import Wikipedia.GreenTao.Sieve.CFZCongruenceBoundary
import Wikipedia.GreenTao.Sieve.PairedLocalFactors
import Wikipedia.GreenTao.Sieve.WTrickedGoodPrime

/-!
# Exact squarefree CRT products for selected CFZ affine families

This file connects the natural representative
`cfzWTrickedAffineResidueValue` to the canonical squarefree CRT interface in
`PairedLocalFactors`.  The resulting factorization is exact for every finite
reindexing of the CFZ family, and hence for every selected CFZ family.

The prime factors are then specialized in the two regimes needed by the
W-trick.  At primes dividing `W`, reduced residues make every nonempty
common-zero density vanish.  At primes outside `W` and above the ambient
CFZ exceptional cutoff, direct modular good-prime geometry gives the exact
empty, singleton, and pair densities and the uniform `p⁻²` bound for every
nontrivial support.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## The squarefree CRT component is ordinary reduction modulo `p` -/

/-- Casting a vector of residues along an equality of moduli is the
coordinatewise cast. -/
theorem equivCast_zmodPi_apply
    {ι : Type*} {m n : ℕ} (h : m = n)
    (x : ι → ZMod m) (i : ι) :
    Equiv.cast (congrArg (fun d => ι → ZMod d) h) x i =
      Equiv.cast (congrArg ZMod h) (x i) := by
  subst n
  rfl

/-- The type-theoretic cast between two equal `ZMod` moduli agrees with the
canonical congruence ring equivalence. -/
theorem equivCast_zmod_eq_ringEquivCongr
    {m n : ℕ} (h : m = n) (x : ZMod m) :
    Equiv.cast (congrArg ZMod h) x =
      ZMod.ringEquivCongr h x := by
  subst n
  simp

/-- On each coordinate, the canonical squarefree CRT component is ordinary
reduction from the global modulus to the underlying prime. -/
theorem squarefreeCanonicalPrimeComponent_apply_eq_castHom
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    {z : κ → ℕ × ℕ}
    (hz : SquarefreePairedDivisorChoice z)
    (p : (pairedDivisorLcm z).primeFactors)
    (x : ι → ZMod (pairedDivisorLcm z))
    (i : ι) :
    squarefreeCanonicalPrimeComponent hz p x i =
      ZMod.castHom (Nat.dvd_of_mem_primeFactors p.2)
        (ZMod (p : ℕ)) (x i) := by
  classical
  letI : NeZero (pairedDivisorLcm z) :=
    ⟨(squarefree_pairedDivisorLcm hz).ne_zero⟩
  let hpow :
      (p : ℕ) ^ (pairedDivisorLcm z).factorization p = p :=
    pairedDivisorLcm_primePower_eq_prime hz p
  have htransport :
      squarefreePrimePowerEquiv hz p
          (coordinatePrimePowerEquiv x p) i =
        (ZMod.ringEquivCongr hpow).toFun
          (coordinatePrimePowerEquiv x p i) := by
    unfold squarefreePrimePowerEquiv
    change
      Equiv.cast
          (congrArg (fun d => ι → ZMod d) hpow)
          (coordinatePrimePowerEquiv x p) i =
        (ZMod.ringEquivCongr hpow).toFun
          (coordinatePrimePowerEquiv x p i)
    rw [equivCast_zmodPi_apply,
      equivCast_zmod_eq_ringEquivCongr]
    · rfl
    all_goals exact hpow
  rw [show
      squarefreeCanonicalPrimeComponent hz p x i =
        squarefreePrimePowerEquiv hz p
          (coordinatePrimePowerEquiv x p) i by
      rfl,
    htransport]
  change
    (ZMod.ringEquivCongr hpow).toFun
        (ZMod.equivPi (pairedDivisorLcm z)
          (NeZero.ne (pairedDivisorLcm z)) (x i) p) =
      ZMod.castHom (Nat.dvd_of_mem_primeFactors p.2)
        (ZMod (p : ℕ)) (x i)
  let componentHom : ZMod (pairedDivisorLcm z) →+* ZMod (p : ℕ) :=
    (ZMod.ringEquivCongr hpow).toRingHom.comp
      ((Pi.evalRingHom
        (fun r : (pairedDivisorLcm z).primeFactors =>
          ZMod ((r : ℕ) ^
            (pairedDivisorLcm z).factorization r)) p).comp
        (ZMod.equivPi (pairedDivisorLcm z)
          (NeZero.ne (pairedDivisorLcm z))).toRingHom)
  have hhom :
      componentHom =
        ZMod.castHom (Nat.dvd_of_mem_primeFactors p.2)
          (ZMod (p : ℕ)) :=
    Subsingleton.elim _ _
  simpa [componentHom] using
    RingHom.congr_fun hhom (x i)

/-! ## The exact natural-valued affine prime model -/

/-- Evaluation of an integer affine form commutes with reduction from a
larger `ZMod` modulus to a divisor modulus. -/
theorem castHom_affineForm_evalZMod
    {ι : Type*} [Fintype ι] {p D : ℕ}
    (hpD : p ∣ D) (ψ : AffineForm ι ℤ)
    (x : ι → ZMod D) :
    ZMod.castHom hpD (ZMod p) (ψ.evalZMod D x) =
      ψ.evalZMod p
        (fun i => ZMod.castHom hpD (ZMod p) (x i)) := by
  unfold AffineForm.evalZMod AffineForm.linearMapZMod
  change
    ZMod.castHom hpD (ZMod p)
        ((ψ.constant : ZMod D) +
          ∑ i, (ψ.coefficient i : ZMod D) * x i) =
      (ψ.constant : ZMod p) +
        ∑ i, (ψ.coefficient i : ZMod p) *
          ZMod.castHom hpD (ZMod p) (x i)
  rw [map_add]
  congr 1
  · simp
  · rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [map_mul]
    simp

/-- The natural representatives of W-tricked CFZ affine values satisfy the
prime-model predicate required by the exact squarefree paired CRT theorem. -/
theorem
    pairedDivisibilityHasAffinePrimeModels_cfzWTrickedAffineResidueValue
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k W b : ℕ} (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ) [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z) :
    PairedDivisibilityHasAffinePrimeModels z
      (fun q =>
        cfzWTrickedAffineResidueValue
          (D := pairedDivisorLcm z) W b (forms q))
      (fun q =>
        wTrickedAffineForm W b (cfzAffineForm (forms q)))
      hz := by
  intro x p q _hq
  let ψ : AffineForm (CFZVariable k) ℤ :=
    wTrickedAffineForm W b (cfzAffineForm (forms q))
  have hpD :
      (p : ℕ) ∣ pairedDivisorLcm z :=
    Nat.dvd_of_mem_primeFactors p.2
  have hvalue :
      (cfzWTrickedAffineResidueValue
          (D := pairedDivisorLcm z) W b (forms q) x :
          ZMod (p : ℕ)) =
        ψ.evalZMod (p : ℕ)
          (squarefreeCanonicalPrimeComponent hz p x) := by
    calc
      (cfzWTrickedAffineResidueValue
          (D := pairedDivisorLcm z) W b (forms q) x :
          ZMod (p : ℕ)) =
          ZMod.castHom hpD (ZMod (p : ℕ))
            (cfzWTrickedAffineResidueValue
              (D := pairedDivisorLcm z) W b (forms q) x :
              ZMod (pairedDivisorLcm z)) := by
            symm
            exact
              map_natCast
                (ZMod.castHom hpD (ZMod (p : ℕ)))
                (cfzWTrickedAffineResidueValue
                  (D := pairedDivisorLcm z) W b (forms q) x)
      _ = ZMod.castHom hpD (ZMod (p : ℕ))
            (ψ.evalZMod (pairedDivisorLcm z) x) := by
          rw [natCast_cfzWTrickedAffineResidueValue]
      _ = ψ.evalZMod (p : ℕ)
            (fun i =>
              ZMod.castHom hpD (ZMod (p : ℕ)) (x i)) :=
          castHom_affineForm_evalZMod hpD ψ x
      _ = ψ.evalZMod (p : ℕ)
            (squarefreeCanonicalPrimeComponent hz p x) := by
          congr 1
          funext i
          exact
            (squarefreeCanonicalPrimeComponent_apply_eq_castHom
              hz p x i).symm
  rw [← ZMod.natCast_eq_zero_iff, hvalue]

/-! ## Exact CRT products for arbitrary finite and selected CFZ families -/

/-- Exact squarefree CRT factorization for an arbitrary finite family
reindexed into the ambient CFZ system. -/
theorem
    pairedDivisibilityDensity_cfzWTrickedAffineResidueValue_eq_prod
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k W b : ℕ} (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ) [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z) :
    pairedDivisibilityDensity
        (fun q =>
          cfzWTrickedAffineResidueValue
            (D := pairedDivisorLcm z) W b (forms q))
        z =
      ∏ p : (pairedDivisorLcm z).primeFactors,
        affineFamilyZeroDensity (p : ℕ)
          (fun q =>
            wTrickedAffineForm W b
              (cfzAffineForm (forms q)))
          (pairedPrimeSupport z p) := by
  exact
    pairedDivisibilityDensity_eq_prod_affineFamilyZeroDensity
      z
      (fun q =>
        cfzWTrickedAffineResidueValue
          (D := pairedDivisorLcm z) W b (forms q))
      (fun q =>
        wTrickedAffineForm W b (cfzAffineForm (forms q)))
      hz
      (pairedDivisibilityHasAffinePrimeModels_cfzWTrickedAffineResidueValue
        forms z hz)

/-- Selected-family specialization of the exact squarefree CRT product. -/
theorem
    pairedDivisibilityDensity_selectedCFZWTrickedAffineResidueValue_eq_prod
    {k W b : ℕ} (e : LinearFormsExponent k)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z) :
    pairedDivisibilityDensity
        (fun q : SelectedCFZFormIndex e =>
          cfzWTrickedAffineResidueValue
            (D := pairedDivisorLcm z) W b q.1)
        z =
      ∏ p : (pairedDivisorLcm z).primeFactors,
        affineFamilyZeroDensity (p : ℕ)
          (fun q : SelectedCFZFormIndex e =>
            wTrickedAffineForm W b (cfzAffineForm q.1))
          (pairedPrimeSupport z p) := by
  exact
    pairedDivisibilityDensity_cfzWTrickedAffineResidueValue_eq_prod
      (fun q : SelectedCFZFormIndex e => q.1) z hz

/-! ## Prime factors dividing `W` -/

/-- A nonempty common-zero density of W-tricked forms is zero at a prime
dividing `W` when `b` is reduced modulo `W`. -/
theorem affineFamilyZeroDensity_wTricked_eq_zero_of_prime_dvd
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq κ]
    {W b p : ℕ} [NeZero p]
    (hp : p.Prime) (hpW : p ∣ W) (hWb : W.Coprime b)
    (forms : κ → AffineForm ι ℤ)
    (s : Finset κ) (hs : s.Nonempty) :
    affineFamilyZeroDensity p
        (fun q => wTrickedAffineForm W b (forms q)) s = 0 := by
  unfold affineFamilyZeroDensity
  rw [show
      affineFamilyZeroProduct p
          (fun q => wTrickedAffineForm W b (forms q)) s =
        fun _x => 0 by
      funext x
      obtain ⟨q, hq⟩ := hs
      unfold affineFamilyZeroProduct
      apply Finset.prod_eq_zero hq
      simp [finsetIndicator,
        wTrickedAffineForm_zeroFinsetZMod_eq_empty
          hp hpW hWb]]
  exact mean_const (α := ι → ZMod p) 0

/-- Every canonical paired prime factor supported at a divisor of `W`
vanishes for an arbitrary finite CFZ reindexing. -/
theorem cfzWTrickedAffinePrimeLocalDensity_eq_zero_of_dvd
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k W b : ℕ} (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ)
    (hz : SquarefreePairedDivisorChoice z)
    (p : (pairedDivisorLcm z).primeFactors)
    (hpW : (p : ℕ) ∣ W) (hWb : W.Coprime b) :
    affineFamilyZeroDensity (p : ℕ)
        (fun q =>
          wTrickedAffineForm W b (cfzAffineForm (forms q)))
        (pairedPrimeSupport z p) = 0 := by
  have hpSupport :
      (p : ℕ).Prime ∧
        (pairedPrimeSupport z (p : ℕ)).Nonempty :=
    (mem_primeFactors_pairedDivisorLcm_iff hz (p : ℕ)).mp p.2
  exact
    affineFamilyZeroDensity_wTricked_eq_zero_of_prime_dvd
      hpSupport.1 hpW hWb
      (fun q => cfzAffineForm (forms q))
      (pairedPrimeSupport z p) hpSupport.2

/-- Selected-CFZ specialization of the reduced-residue small-prime local
factor. -/
theorem selectedCFZWTrickedAffinePrimeLocalDensity_eq_zero_of_dvd
    {k W b : ℕ} (e : LinearFormsExponent k)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    (hz : SquarefreePairedDivisorChoice z)
    (p : (pairedDivisorLcm z).primeFactors)
    (hpW : (p : ℕ) ∣ W) (hWb : W.Coprime b) :
    affineFamilyZeroDensity (p : ℕ)
        (fun q : SelectedCFZFormIndex e =>
          wTrickedAffineForm W b (cfzAffineForm q.1))
        (pairedPrimeSupport z p) = 0 := by
  exact
    cfzWTrickedAffinePrimeLocalDensity_eq_zero_of_dvd
      (fun q : SelectedCFZFormIndex e => q.1)
      z hz p hpW hWb

/-! ## Prime factors outside `W` above the ambient CFZ cutoff -/

/-- Direct modular one-form and rank-two hypotheses determine every
W-tricked common-zero density of cardinality at most two. -/
theorem affineFamilyZeroDensity_wTricked_eq_inv_pow_card_of_card_le_two
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {p W : ℕ} [NeZero p]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : AffineNonzeroGoodPrime p forms)
    (hrankTwo : AffineRankTwoGoodPrime p forms)
    (hpW : ¬p ∣ W) (b : ℕ)
    (s : Finset κ) (hs : s.card ≤ 2) :
    affineFamilyZeroDensity p
        (fun q => wTrickedAffineForm W b (forms q)) s =
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
        affineFamilyZeroDensity_singleton_wTricked
          hnonzero hpW (fun _q : κ => b) q
    · obtain ⟨q, r, hqr, rfl⟩ :=
        Finset.card_eq_two.mp htwo
      have hcard : ({q, r} : Finset κ).card = 2 :=
        Finset.card_eq_two.mpr ⟨q, r, hqr, rfl⟩
      rw [hcard]
      exact
        affineFamilyZeroDensity_pair_wTricked
          hrankTwo hpW (fun _q : κ => b) hqr

/-- For an injectively reindexed finite CFZ family, a prime outside `W`
above the ambient k-only cutoff has the exact local density whenever at
most two forms contain the prime. -/
theorem
    cfzWTrickedAffinePrimeLocalDensity_eq_inv_pow_card_of_card_le_two
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k W b : ℕ} (hk : 2 ≤ k)
    (forms : κ → CFZFormIndex k)
    (hforms : Function.Injective forms)
    (z : κ → ℕ × ℕ)
    (p : (pairedDivisorLcm z).primeFactors)
    (hpW : ¬(p : ℕ) ∣ W)
    (hlarge :
      wTrickedCFZComplexExceptionalBound k < (p : ℕ))
    (hsupport : (pairedPrimeSupport z p).card ≤ 2) :
    affineFamilyZeroDensity (p : ℕ)
        (fun q =>
          wTrickedAffineForm W b (cfzAffineForm (forms q)))
        (pairedPrimeSupport z p) =
      (1 : ℝ) / (p : ℝ) ^
        (pairedPrimeSupport z p).card := by
  have hp : (p : ℕ).Prime :=
    Nat.prime_of_mem_primeFactors p.2
  have horiginal :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) <
        (p : ℕ) :=
    (Nat.le_max_left _ _).trans_lt hlarge
  have hnonzero :
      AffineNonzeroGoodPrime (p : ℕ)
        (fun q => cfzAffineForm (forms q)) :=
    (affineNonzeroGoodPrime_of_exceptionalPrimeBound
      (cfzAffineForms_nonzero hk) hp horiginal).comp forms
  have hrankTwo :
      AffineRankTwoGoodPrime (p : ℕ)
        (fun q => cfzAffineForm (forms q)) :=
    (affineRankTwoGoodPrime_of_exceptionalPrimeBound
      (cfzAffineForms_pairwiseIndependent hk)
      hp horiginal).comp forms hforms
  exact
    affineFamilyZeroDensity_wTricked_eq_inv_pow_card_of_card_le_two
      hnonzero hrankTwo hpW b
      (pairedPrimeSupport z p) hsupport

/-- For the same arbitrary finite CFZ family, every nontrivial prime support
has common-zero density at most `p⁻²`. -/
theorem cfzWTrickedAffinePrimeLocalDensity_le_inv_sq_of_nontrivial
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k W b : ℕ} (hk : 2 ≤ k)
    (forms : κ → CFZFormIndex k)
    (hforms : Function.Injective forms)
    (z : κ → ℕ × ℕ)
    (p : (pairedDivisorLcm z).primeFactors)
    (hpW : ¬(p : ℕ) ∣ W)
    (hlarge :
      wTrickedCFZComplexExceptionalBound k < (p : ℕ))
    (hsupport : (pairedPrimeSupport z p).Nontrivial) :
    affineFamilyZeroDensity (p : ℕ)
        (fun q =>
          wTrickedAffineForm W b (cfzAffineForm (forms q)))
        (pairedPrimeSupport z p) ≤
      (1 : ℝ) / (p : ℝ) ^ 2 := by
  have hp : (p : ℕ).Prime :=
    Nat.prime_of_mem_primeFactors p.2
  have horiginal :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) <
        (p : ℕ) :=
    (Nat.le_max_left _ _).trans_lt hlarge
  have hrankTwo :
      AffineRankTwoGoodPrime (p : ℕ)
        (fun q => cfzAffineForm (forms q)) :=
    (affineRankTwoGoodPrime_of_exceptionalPrimeBound
      (cfzAffineForms_pairwiseIndependent hk)
      hp horiginal).comp forms hforms
  exact
    affineFamilyZeroDensity_le_inv_sq_wTricked
      hrankTwo hpW (fun _q : κ => b)
      (pairedPrimeSupport z p) hsupport

/-- Selected-CFZ exact local factor above the same ambient k-only cutoff. -/
theorem
    selectedCFZWTrickedAffinePrimeLocalDensity_eq_inv_pow_card_of_card_le_two
    {k W b : ℕ} (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    (p : (pairedDivisorLcm z).primeFactors)
    (hpW : ¬(p : ℕ) ∣ W)
    (hlarge :
      wTrickedCFZComplexExceptionalBound k < (p : ℕ))
    (hsupport : (pairedPrimeSupport z p).card ≤ 2) :
    affineFamilyZeroDensity (p : ℕ)
        (fun q : SelectedCFZFormIndex e =>
          wTrickedAffineForm W b (cfzAffineForm q.1))
        (pairedPrimeSupport z p) =
      (1 : ℝ) / (p : ℝ) ^
        (pairedPrimeSupport z p).card := by
  have hp : (p : ℕ).Prime :=
    Nat.prime_of_mem_primeFactors p.2
  have horiginal :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) <
        (p : ℕ) :=
    (Nat.le_max_left _ _).trans_lt hlarge
  exact
    affineFamilyZeroDensity_wTricked_eq_inv_pow_card_of_card_le_two
      (selectedCFZAffineNonzeroGoodPrime
        hk hp horiginal e)
      (selectedCFZAffineRankTwoGoodPrime
        hk hp horiginal e)
      hpW b (pairedPrimeSupport z p) hsupport

/-- In particular, a selected local factor supported on exactly one form is
exactly `1 / p`. -/
theorem selectedCFZWTrickedAffinePrimeLocalDensity_eq_inv_of_card_eq_one
    {k W b : ℕ} (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    (p : (pairedDivisorLcm z).primeFactors)
    (hpW : ¬(p : ℕ) ∣ W)
    (hlarge :
      wTrickedCFZComplexExceptionalBound k < (p : ℕ))
    (hsupport : (pairedPrimeSupport z p).card = 1) :
    affineFamilyZeroDensity (p : ℕ)
        (fun q : SelectedCFZFormIndex e =>
          wTrickedAffineForm W b (cfzAffineForm q.1))
        (pairedPrimeSupport z p) =
      (1 : ℝ) / (p : ℝ) := by
  have hle : (pairedPrimeSupport z p).card ≤ 2 := by
    omega
  simpa [hsupport] using
    selectedCFZWTrickedAffinePrimeLocalDensity_eq_inv_pow_card_of_card_le_two
      hk e z p hpW hlarge hle

/-- A selected local factor supported on exactly two forms is exactly
`1 / p²`. -/
theorem selectedCFZWTrickedAffinePrimeLocalDensity_eq_inv_sq_of_card_eq_two
    {k W b : ℕ} (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    (p : (pairedDivisorLcm z).primeFactors)
    (hpW : ¬(p : ℕ) ∣ W)
    (hlarge :
      wTrickedCFZComplexExceptionalBound k < (p : ℕ))
    (hsupport : (pairedPrimeSupport z p).card = 2) :
    affineFamilyZeroDensity (p : ℕ)
        (fun q : SelectedCFZFormIndex e =>
          wTrickedAffineForm W b (cfzAffineForm q.1))
        (pairedPrimeSupport z p) =
      (1 : ℝ) / (p : ℝ) ^ 2 := by
  have hle : (pairedPrimeSupport z p).card ≤ 2 := by
    omega
  simpa [hsupport] using
    selectedCFZWTrickedAffinePrimeLocalDensity_eq_inv_pow_card_of_card_le_two
      hk e z p hpW hlarge hle

/-- Selected-CFZ `p⁻²` bound for every nontrivial prime support above the
ambient k-only cutoff. -/
theorem
    selectedCFZWTrickedAffinePrimeLocalDensity_le_inv_sq_of_nontrivial
    {k W b : ℕ} (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    (p : (pairedDivisorLcm z).primeFactors)
    (hpW : ¬(p : ℕ) ∣ W)
    (hlarge :
      wTrickedCFZComplexExceptionalBound k < (p : ℕ))
    (hsupport : (pairedPrimeSupport z p).Nontrivial) :
    affineFamilyZeroDensity (p : ℕ)
        (fun q : SelectedCFZFormIndex e =>
          wTrickedAffineForm W b (cfzAffineForm q.1))
        (pairedPrimeSupport z p) ≤
      (1 : ℝ) / (p : ℝ) ^ 2 := by
  have hp : (p : ℕ).Prime :=
    Nat.prime_of_mem_primeFactors p.2
  have horiginal :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) <
        (p : ℕ) :=
    (Nat.le_max_left _ _).trans_lt hlarge
  exact
    affineFamilyZeroDensity_le_inv_sq_wTricked
      (selectedCFZAffineRankTwoGoodPrime
        hk hp horiginal e)
      hpW (fun _q : SelectedCFZFormIndex e => b)
      (pairedPrimeSupport z p) hsupport

end Wikipedia.SzemeredisTheorem
