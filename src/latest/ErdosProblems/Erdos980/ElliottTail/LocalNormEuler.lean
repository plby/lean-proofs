import ErdosProblems.Erdos980.ElliottTail.PrimeIdealMertens
import ErdosProblems.Erdos980.ElliottTail.RayNormPrimeSieve
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Local norm Euler factors

This file identifies the proportion of units modulo a rational prime in the ring of integers of
a number field with the product of the corresponding prime-ideal Euler factors.  It then compares
the rational-prime norm-sieve product with the all-prime-ideal Mertens product.
-/

noncomputable section

open NumberField
open scoped BigOperators nonZeroDivisors

namespace Erdos980.ElliottTail.LocalNormEuler

private lemma isUnit_of_factor_isUnit {R : Type*} [CommRing R]
    (P : Ideal R) [P.IsMaximal] (n : ℕ) (hn : n ≠ 0)
    (x : R ⧸ P ^ n)
    (hx : IsUnit (Ideal.Quotient.factor (Ideal.pow_le_self hn) x)) : IsUnit x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.factor_mk] at hx
  exact (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P hn).mpr hx

private noncomputable def unitKerEquivAddKer {A B : Type*}
    [CommRing A] [CommRing B] (f : A →+* B)
    (hlift : ∀ x : A, IsUnit (f x) → IsUnit x) :
    (Units.map f.toMonoidHom).ker ≃ f.toAddMonoidHom.ker where
  toFun u := ⟨(u.1.1 : A) - 1, by
    change f ((u.1.1 : A) - 1) = 0
    have hu : Units.map f.toMonoidHom u.1 = 1 := u.2
    have huval : f (u.1.1 : A) = 1 := congrArg Units.val hu
    rw [map_sub, map_one, huval, sub_self]⟩
  invFun x := by
    have hxzero : f (x.1 : A) = 0 := x.2
    have hxmap : IsUnit (f ((x.1 : A) + 1)) := by
      rw [map_add, map_one, hxzero, zero_add]
      exact isUnit_one
    let hx : IsUnit ((x.1 : A) + 1) := hlift _ hxmap
    exact ⟨hx.unit, by
      apply Units.ext
      rw [Units.coe_map, hx.unit_spec]
      simp [hxzero]⟩
  left_inv u := by
    apply Subtype.ext
    apply Units.ext
    simp only [IsUnit.unit_spec]
    ring
  right_inv x := by
    apply Subtype.ext
    simp only [IsUnit.unit_spec]
    ring

private lemma card_ker_mul_card_of_surjective {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (f : G →* H) (hf : Function.Surjective f) :
    Nat.card f.ker * Nat.card H = Nat.card G := by
  calc
    Nat.card f.ker * Nat.card H = Nat.card f.ker * f.ker.index := by
      rw [Subgroup.index_ker, (MonoidHom.range_eq_top.mpr hf)]
      simp
    _ = Nat.card G := f.ker.card_mul_index

private lemma card_addKer_mul_card_of_surjective {G H : Type*} [AddGroup G] [AddGroup H]
    [Finite G] [Finite H] (f : G →+ H) (hf : Function.Surjective f) :
    Nat.card f.ker * Nat.card H = Nat.card G := by
  calc
    Nat.card f.ker * Nat.card H = Nat.card f.ker * f.ker.index := by
      rw [AddSubgroup.index_ker, (AddMonoidHom.range_eq_top.mpr hf)]
      simp
    _ = Nat.card G := f.ker.card_mul_index

private theorem primePowerQuotient_unit_ratio
    {K : Type*} [Field K] [NumberField K]
    (P : Ideal (RingOfIntegers K)) (hP : P.IsPrime) (hP₀ : P ≠ ⊥)
    (n : ℕ) (hn : n ≠ 0) :
    (Nat.card ((RingOfIntegers K ⧸ P ^ n)ˣ) : ℝ) /
        Nat.card (RingOfIntegers K ⧸ P ^ n) =
      1 - (Ideal.absNorm P : ℝ)⁻¹ := by
  let : P.IsPrime := hP
  let : P.IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hP₀ hP
  have hPn₀ : P ^ n ≠ ⊥ := by
    exact pow_ne_zero n hP₀
  let : Finite (RingOfIntegers K ⧸ P ^ n) :=
    (Ideal.absNorm_ne_zero_iff (P ^ n)).mp (fun h ↦ hPn₀ (Ideal.absNorm_eq_zero_iff.mp h))
  let : Finite (RingOfIntegers K ⧸ P) :=
    (Ideal.absNorm_ne_zero_iff P).mp (fun h ↦ hP₀ (Ideal.absNorm_eq_zero_iff.mp h))
  let : Field (RingOfIntegers K ⧸ P) := Ideal.Quotient.field P
  let f : (RingOfIntegers K ⧸ P ^ n) →+* (RingOfIntegers K ⧸ P) :=
    Ideal.Quotient.factor (Ideal.pow_le_self hn)
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective _
  have hfu : Function.Surjective (Units.map f.toMonoidHom) := by
    intro u
    obtain ⟨x, hxrep⟩ := Ideal.Quotient.mk_surjective (u : RingOfIntegers K ⧸ P)
    have hxP : x ∉ P := by
      intro hmem
      have hz : (Ideal.Quotient.mk P x : RingOfIntegers K ⧸ P) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      exact Units.ne_zero u (by rw [← hxrep, hz])
    let v : (RingOfIntegers K ⧸ P ^ n)ˣ :=
      (Ideal.Quotient.isUnit_mk_pow_of_notMem P hxP).unit
    refine ⟨v, ?_⟩
    apply Units.ext
    rw [Units.coe_map]
    simp only [v, IsUnit.unit_spec]
    change Ideal.Quotient.factor (Ideal.pow_le_self hn)
      (Ideal.Quotient.mk (P ^ n) x) = (u : RingOfIntegers K ⧸ P)
    rw [Ideal.Quotient.factor_mk, hxrep]
  have hker : Nat.card (Units.map f.toMonoidHom).ker =
      Nat.card f.toAddMonoidHom.ker :=
    Nat.card_congr (unitKerEquivAddKer f
      (isUnit_of_factor_isUnit P n hn))
  have huCard := card_ker_mul_card_of_surjective (Units.map f.toMonoidHom) hfu
  have haCard := card_addKer_mul_card_of_surjective f.toAddMonoidHom hf
  have hPcard : Nat.card (RingOfIntegers K ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hPncard : Nat.card (RingOfIntegers K ⧸ P ^ n) = Ideal.absNorm P ^ n := by
    rw [← Submodule.cardQuot_apply, cardQuot_pow_of_prime hP₀,
      ← Ideal.absNorm_apply]
  have hPunits : Nat.card (RingOfIntegers K ⧸ P)ˣ = Ideal.absNorm P - 1 := by
    rw [Nat.card_units, hPcard]
  rw [hker, hPunits] at huCard
  rw [hPcard] at haCard
  have hkerpos : 0 < Nat.card f.toAddMonoidHom.ker := Nat.card_pos
  have hnormpos : 0 < Ideal.absNorm P :=
    Nat.pos_of_ne_zero (fun h ↦ hP₀ (Ideal.absNorm_eq_zero_iff.mp h))
  rw [← huCard, ← haCard]
  push_cast
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hnormpos))]
  have hkR : (0 : ℝ) < Nat.card f.toAddMonoidHom.ker := by exact_mod_cast hkerpos
  have hnormR : (0 : ℝ) < Ideal.absNorm P := by exact_mod_cast hnormpos
  field_simp
  ring

/-- The Euler-factor identity for the unit density modulo a nonzero integral ideal. -/
theorem idealQuotient_unitRatio_eq_prod_factors
    {K : Type*} [Field K] [NumberField K]
    (I : Ideal (RingOfIntegers K)) (hI : I ≠ ⊥) :
    (Nat.card ((RingOfIntegers K ⧸ I)ˣ) : ℝ) /
        Nat.card (RingOfIntegers K ⧸ I) =
      ∏ P ∈ (UniqueFactorizationMonoid.factors I).toFinset,
        (1 - (Ideal.absNorm P : ℝ)⁻¹) := by
  let F := (UniqueFactorizationMonoid.factors I).toFinset
  let C : F → Type _ := fun P ↦
    RingOfIntegers K ⧸ (P : Ideal (RingOfIntegers K)) ^
      Multiset.count (P : Ideal (RingOfIntegers K))
        (UniqueFactorizationMonoid.factors I)
  have hmem (P : F) : (P : Ideal (RingOfIntegers K)) ∈
      UniqueFactorizationMonoid.factors I := Multiset.mem_toFinset.mp P.2
  have hPprime (P : F) : Prime (P : Ideal (RingOfIntegers K)) :=
    UniqueFactorizationMonoid.prime_of_factor _ (hmem P)
  have hP₀ (P : F) : (P : Ideal (RingOfIntegers K)) ≠ ⊥ := (hPprime P).ne_zero
  have hn (P : F) : Multiset.count (P : Ideal (RingOfIntegers K))
      (UniqueFactorizationMonoid.factors I) ≠ 0 :=
    Multiset.count_ne_zero.mpr (hmem P)
  let (P : F) : (P : Ideal (RingOfIntegers K)).IsPrime :=
    Ideal.isPrime_of_prime (hPprime P)
  let (P : F) : Finite (C P) :=
    (Ideal.absNorm_ne_zero_iff
      ((P : Ideal (RingOfIntegers K)) ^
        Multiset.count (P : Ideal (RingOfIntegers K))
          (UniqueFactorizationMonoid.factors I))).mp (by
      intro hz
      exact pow_ne_zero _ (hP₀ P) (Ideal.absNorm_eq_zero_iff.mp hz))
  let : Finite (RingOfIntegers K ⧸ I) :=
    (Ideal.absNorm_ne_zero_iff I).mp (by
      intro hz
      exact hI (Ideal.absNorm_eq_zero_iff.mp hz))
  let e : (RingOfIntegers K ⧸ I) ≃+* ((P : F) → C P) :=
    IsDedekindDomain.quotientEquivPiFactors hI
  have hRingCard : Nat.card (RingOfIntegers K ⧸ I) =
      ∏ P : F, Nat.card (C P) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_pi]
  have hUnitCard : Nat.card ((RingOfIntegers K ⧸ I)ˣ) =
      ∏ P : F, Nat.card ((C P)ˣ) := by
    calc
      Nat.card ((RingOfIntegers K ⧸ I)ˣ) =
          Nat.card (((P : F) → C P)ˣ) :=
        Nat.card_congr (Units.mapEquiv e.toMulEquiv).toEquiv
      _ = Nat.card ((P : F) → (C P)ˣ) :=
        Nat.card_congr (MulEquiv.piUnits :
          (((P : F) → C P)ˣ) ≃* ((P : F) → (C P)ˣ)).toEquiv
      _ = ∏ P : F, Nat.card ((C P)ˣ) := Nat.card_pi
  rw [hUnitCard, hRingCard]
  push_cast
  rw [← Finset.prod_div_distrib]
  change (∏ P : F, ((Nat.card ((C P)ˣ) : ℝ) / Nat.card (C P))) = _
  let g : Ideal (RingOfIntegers K) → ℝ := fun P ↦
    (Nat.card ((RingOfIntegers K ⧸ P ^
      Multiset.count P (UniqueFactorizationMonoid.factors I))ˣ) : ℝ) /
      Nat.card (RingOfIntegers K ⧸ P ^
        Multiset.count P (UniqueFactorizationMonoid.factors I))
  change (∏ P : F, g P) = _
  rw [Finset.prod_coe_sort]
  dsimp only [F]
  apply Finset.prod_congr rfl
  intro P hP
  exact primePowerQuotient_unit_ratio P
    (Ideal.isPrime_of_prime
      (UniqueFactorizationMonoid.prime_of_factor _ (Multiset.mem_toFinset.mp hP)))
    (UniqueFactorizationMonoid.prime_of_factor _
      (Multiset.mem_toFinset.mp hP)).ne_zero _
    (Multiset.count_ne_zero.mpr (Multiset.mem_toFinset.mp hP))

/-- The ideal generated in `ᵒ K` by a rational integer. -/
def rationalModulusIdeal (K : Type*) [Field K] [NumberField K] (s : ℕ) :
    Ideal (RingOfIntegers K) :=
  Ideal.span {(s : RingOfIntegers K)}

lemma rationalModulusIdeal_ne_bot
    {K : Type*} [Field K] [NumberField K] {s : ℕ} (hs : s ≠ 0) :
    rationalModulusIdeal K s ≠ ⊥ := by
  intro hbot
  have hmem : (s : RingOfIntegers K) ∈ (⊥ : Ideal (RingOfIntegers K)) := by
    rw [← hbot]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hzero : (s : RingOfIntegers K) = 0 := by simpa using hmem
  exact hs (Nat.cast_eq_zero.mp hzero)

/-- Exact local Euler factor for reduction modulo a rational prime. -/
theorem rationalPrime_unitRatio_eq_prod_factors
    {K : Type*} [Field K] [NumberField K]
    (s : ℕ) (hs : s.Prime) :
    (Nat.card ((RingOfIntegers K ⧸ rationalModulusIdeal K s)ˣ) : ℝ) /
        Nat.card (RingOfIntegers K ⧸ rationalModulusIdeal K s) =
      ∏ P ∈ (UniqueFactorizationMonoid.factors
          (rationalModulusIdeal K s)).toFinset,
        (1 - (Ideal.absNorm P : ℝ)⁻¹) :=
  idealQuotient_unitRatio_eq_prod_factors _
    (rationalModulusIdeal_ne_bot hs.ne_zero)

/-- The finite product of local unit densities at rational primes below `w`. -/
def rationalPrimeNormSieveProduct
    (K : Type*) [Field K] [NumberField K] (w : ℕ) : ℝ :=
  ∏ s ∈ Nat.primesBelow w,
    (Nat.card ((RingOfIntegers K ⧸ rationalModulusIdeal K s)ˣ) : ℝ) /
      Nat.card (RingOfIntegers K ⧸ rationalModulusIdeal K s)

/-- The rational-prime norm-sieve product expanded into its prime-ideal Euler factors. -/
theorem rationalPrimeNormSieveProduct_eq_prod_factors
    (K : Type*) [Field K] [NumberField K] (w : ℕ) :
    rationalPrimeNormSieveProduct K w =
      ∏ s ∈ Nat.primesBelow w,
        ∏ P ∈ (UniqueFactorizationMonoid.factors
            (rationalModulusIdeal K s)).toFinset,
          (1 - (Ideal.absNorm P : ℝ)⁻¹) := by
  apply Finset.prod_congr rfl
  intro s hs
  exact rationalPrime_unitRatio_eq_prod_factors s
    (Nat.prime_of_mem_primesBelow hs)

/-- The prime-ideal factors lying above the rational prime `s`. -/
def rationalPrimeIdealFactors
    (K : Type*) [Field K] [NumberField K] (s : ℕ) :
    Finset (Ideal (RingOfIntegers K)) :=
  (UniqueFactorizationMonoid.factors (rationalModulusIdeal K s)).toFinset

/-- All prime-ideal factors above rational primes strictly below `w`. -/
def rationalPrimeIdealFactorsBelow
    (K : Type*) [Field K] [NumberField K] (w : ℕ) :
    Finset (Ideal (RingOfIntegers K)) :=
  (Nat.primesBelow w).biUnion (rationalPrimeIdealFactors K)

private lemma rationalPrimeIdealFactors_disjoint
    {K : Type*} [Field K] [NumberField K]
    {s t : ℕ} (hs : s.Prime) (ht : t.Prime) (hst : s ≠ t) :
    Disjoint (rationalPrimeIdealFactors K s)
      (rationalPrimeIdealFactors K t) := by
  rw [Finset.disjoint_left]
  intro P hPs hPt
  have hPs' : P ∈ UniqueFactorizationMonoid.factors
      (rationalModulusIdeal K s) := Multiset.mem_toFinset.mp hPs
  have hPt' : P ∈ UniqueFactorizationMonoid.factors
      (rationalModulusIdeal K t) := Multiset.mem_toFinset.mp hPt
  have hsle : rationalModulusIdeal K s ≤ P :=
    Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_factors hPs')
  have htle : rationalModulusIdeal K t ≤ P :=
    Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_factors hPt')
  have hcopNat : s.Coprime t := (Nat.coprime_primes hs ht).mpr hst
  have hcopInt : IsCoprime (s : ℤ) (t : ℤ) :=
    Nat.Coprime.isCoprime hcopNat
  have hcop : IsCoprime (rationalModulusIdeal K s)
      (rationalModulusIdeal K t) := by
    rw [rationalModulusIdeal, rationalModulusIdeal,
      Ideal.isCoprime_span_singleton_iff]
    simpa using hcopInt.map (algebraMap ℤ (RingOfIntegers K))
  have htop : P = ⊤ := by
    apply top_unique
    rw [← Ideal.isCoprime_iff_sup_eq.mp hcop]
    exact sup_le hsle htle
  have hPprime : Prime P :=
    UniqueFactorizationMonoid.prime_of_factor _ hPs'
  exact hPprime.not_unit (Ideal.isUnit_iff.mpr htop)

private lemma rationalPrimeIdealFactors_pairwiseDisjoint
    (K : Type*) [Field K] [NumberField K] (w : ℕ) :
    ((Nat.primesBelow w : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (rationalPrimeIdealFactors K) := by
  intro s hs t ht hst
  exact rationalPrimeIdealFactors_disjoint
    (Nat.prime_of_mem_primesBelow hs)
    (Nat.prime_of_mem_primesBelow ht) hst

/-- The nested rational/prime-ideal product has no duplicate prime-ideal factors. -/
theorem rationalPrimeNormSieveProduct_eq_primeIdealFactorsBelow
    (K : Type*) [Field K] [NumberField K] (w : ℕ) :
    rationalPrimeNormSieveProduct K w =
      ∏ P ∈ rationalPrimeIdealFactorsBelow K w,
        (1 - (Ideal.absNorm P : ℝ)⁻¹) := by
  rw [rationalPrimeNormSieveProduct_eq_prod_factors]
  exact (Finset.prod_biUnion
    (rationalPrimeIdealFactors_pairwiseDisjoint K w)).symm

private lemma primeIdealsBelow_subset_rationalPrimeIdealFactorsBelow
    (K : Type*) [Field K] [NumberField K] (w : ℕ) :
    PrimeIdealMertens.primeIdealsBelow K w ⊆
      rationalPrimeIdealFactorsBelow K w := by
  intro P hP
  rw [PrimeIdealMertens.mem_primeIdealsBelow] at hP
  let : P.IsPrime := hP.1
  let : P.IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hP.2.1 hP.1
  obtain ⟨p, n, hn, hpP, hp, hnorm⟩ :=
    Ideal.exists_prime_and_absNorm_eq_pow P
  have hp_le_norm : p ≤ Ideal.absNorm P := by
    rw [hnorm]
    exact Nat.le_pow hn
  have hpw : p < w := hp_le_norm.trans_lt hP.2.2
  have hp_mem : p ∈ Nat.primesBelow w :=
    Nat.mem_primesBelow.mpr ⟨hpw, hp⟩
  rw [rationalPrimeIdealFactorsBelow, Finset.mem_biUnion]
  refine ⟨p, hp_mem, ?_⟩
  rw [rationalPrimeIdealFactors, Multiset.mem_toFinset]
  have hspanle : rationalModulusIdeal K p ≤ P := by
    rw [rationalModulusIdeal, Ideal.span_le]
    intro x hx
    simpa only [Set.mem_singleton_iff] using hx ▸ hpP
  have hdvd : P ∣ rationalModulusIdeal K p :=
    Ideal.dvd_iff_le.mpr hspanle
  have hPprime : Prime P := Ideal.prime_of_isPrime hP.2.1 hP.1
  obtain ⟨Q, hQ, hPQ⟩ :=
    UniqueFactorizationMonoid.exists_mem_factors_of_dvd
      (rationalModulusIdeal_ne_bot hp.ne_zero) hPprime.irreducible hdvd
  have hQP : Q = P := (associated_iff_eq.mp hPQ).symm
  simpa [hQP] using hQ

private lemma rationalPrimeIdealFactor_bounds
    {K : Type*} [Field K] [NumberField K] {w : ℕ}
    {P : Ideal (RingOfIntegers K)}
    (hP : P ∈ rationalPrimeIdealFactorsBelow K w) :
    0 ≤ 1 - (Ideal.absNorm P : ℝ)⁻¹ ∧
      1 - (Ideal.absNorm P : ℝ)⁻¹ ≤ 1 := by
  rw [rationalPrimeIdealFactorsBelow, Finset.mem_biUnion] at hP
  obtain ⟨s, _hs, hPs⟩ := hP
  have hPs' : P ∈ UniqueFactorizationMonoid.factors
      (rationalModulusIdeal K s) :=
    Multiset.mem_toFinset.mp hPs
  have hPprime : Prime P :=
    UniqueFactorizationMonoid.prime_of_factor _ hPs'
  have hP₀ : P ≠ ⊥ := hPprime.ne_zero
  have hnorm₀ : Ideal.absNorm P ≠ 0 := fun h ↦
    hP₀ (Ideal.absNorm_eq_zero_iff.mp h)
  have hnormPosNat : 0 < Ideal.absNorm P := Nat.pos_of_ne_zero hnorm₀
  have hnormPos : (0 : ℝ) < Ideal.absNorm P := by exact_mod_cast hnormPosNat
  have hnormOne : (1 : ℝ) ≤ Ideal.absNorm P := by exact_mod_cast hnormPosNat
  constructor
  · have hinv : (Ideal.absNorm P : ℝ)⁻¹ ≤ 1 :=
      (inv_le_one₀ hnormPos).mpr hnormOne
    linarith
  · exact sub_le_self _ (inv_nonneg.mpr hnormPos.le)

/-- The rational-prime local-unit product is bounded by the all-prime-ideal Mertens product. -/
theorem rationalPrimeNormSieveProduct_le_primeIdealMertensProduct
    (K : Type*) [Field K] [NumberField K] (w : ℕ) :
    rationalPrimeNormSieveProduct K w ≤
      PrimeIdealMertens.primeIdealMertensProduct K w := by
  rw [rationalPrimeNormSieveProduct_eq_primeIdealFactorsBelow,
    PrimeIdealMertens.primeIdealMertensProduct]
  apply Finset.prod_le_prod_of_subset_of_le_one
    (primeIdealsBelow_subset_rationalPrimeIdealFactorsBelow K w)
  · intro P hP
    exact (rationalPrimeIdealFactor_bounds hP).1
  · intro P hP _
    exact (rationalPrimeIdealFactor_bounds hP).2

/-- Concrete Mertens upper bound for the rational-prime local-unit product. -/
theorem eventually_rationalPrimeNormSieveProduct_le
    (K : Type*) [Field K] [NumberField K] :
    ∀ᶠ w : ℕ in Filter.atTop,
      rationalPrimeNormSieveProduct K w ≤
        (8 / NumberField.dedekindZeta_residue K) / Real.log (w : ℝ) := by
  filter_upwards
    [PrimeIdealMertens.eventually_primeIdealMertensProduct_le K] with w hw
  exact (rationalPrimeNormSieveProduct_le_primeIdealMertensProduct K w).trans hw

/-! ## Adapter from norm-zero coordinate cells to local units -/

/-- Abstract finite adapter used for a coordinate presentation of `ᵒ K / sᵒ K`.
If the zero set of a supplied norm form corresponds exactly to the nonunits of the quotient,
then its complementary density is the unit density. -/
theorem one_sub_badResidueDensity_eq_unitRatio
    {X R : Type*} [Fintype X] [CommRing R] [Finite R]
    (e : X ≃ R) (bad : Finset X)
    (hbad : ∀ x : X, x ∈ bad ↔ ¬ IsUnit (e x)) :
    1 - (bad.card : ℝ) / Nat.card X =
      (Nat.card Rˣ : ℝ) / Nat.card R := by
  classical
  let Good := {x : X // x ∉ bad}
  let eu : Rˣ ≃ Good :=
    { toFun := fun u ↦ ⟨e.symm (u : R), by
        intro hmem
        have hnonunit : ¬ IsUnit (e (e.symm (u : R))) :=
          (hbad _).mp hmem
        exact hnonunit (by simpa using u.isUnit)⟩
      invFun := fun x ↦ by
        have hxunit : IsUnit (e (x : X)) := by
          by_contra hnonunit
          exact x.2 ((hbad x).mpr hnonunit)
        exact hxunit.unit
      left_inv := fun u ↦ by
        apply Units.ext
        simp only [IsUnit.unit_spec]
        exact e.apply_symm_apply (u : R)
      right_inv := fun x ↦ by
        apply Subtype.ext
        simp only [IsUnit.unit_spec]
        exact e.symm_apply_apply (x : X) }
  have hGoodCard : Nat.card Good = (badᶜ).card := by
    exact Nat.subtype_card badᶜ (fun x ↦ Finset.mem_compl)
  have hUnitsCard : Nat.card Rˣ = Nat.card Good :=
    Nat.card_congr eu
  have hbadle : bad.card ≤ Nat.card X := by
    rw [Nat.card_eq_fintype_card]
    exact Finset.card_le_univ bad
  have hXcard : Nat.card X = Fintype.card X := Nat.card_eq_fintype_card
  have hsum : bad.card + Nat.card Rˣ = Nat.card X := by
    rw [hUnitsCard, hGoodCard, Finset.card_compl]
    rw [hXcard]
    omega
  have hcard : Nat.card X = Nat.card R := Nat.card_congr e
  have : Nonempty X := ⟨e.symm 0⟩
  have hXpos : (0 : ℝ) < Nat.card X := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card X)
  rw [← hcard]
  have hsumR : (bad.card : ℝ) + Nat.card Rˣ = Nat.card X := by
    exact_mod_cast hsum
  field_simp
  linarith

/-- Function-zero-set form of `one_sub_badResidueDensity_eq_unitRatio`, matching the local
norm-form interface used by the conductor-norm sieve. -/
theorem one_sub_zeroResidueDensity_eq_unitRatio
    {X R A : Type*} [Fintype X] [CommRing R] [Finite R] [Zero A] [DecidableEq A]
    (e : X ≃ R) (normMod : X → A)
    (hzero : ∀ x : X, normMod x = 0 ↔ ¬ IsUnit (e x)) :
    1 - (((Finset.univ.filter fun x ↦ normMod x = 0).card : ℕ) : ℝ) /
        Nat.card X =
      (Nat.card Rˣ : ℝ) / Nat.card R := by
  apply one_sub_badResidueDensity_eq_unitRatio e
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hzero x

/-- Coordinate-vector specialization: the denominator is literally `d^[K:ℚ]`.  Taking
`R = ᵒ K / dᵒ K` gives the exact adapter required by the conductor-norm sieve once a
coordinate equivalence and the standard `norm = 0 ↔ nonunit` lemma are supplied. -/
theorem one_sub_coordinateNormResidueDensity_eq_unitRatio
    (K : Type*) [Field K] [NumberField K]
    {d : ℕ} [NeZero d] {R : Type*} [CommRing R] [Finite R]
    (e : (NumberField.mixedEmbedding.index K → ZMod d) ≃ R)
    (normMod : (NumberField.mixedEmbedding.index K → ZMod d) → ZMod d)
    (hzero : ∀ x, normMod x = 0 ↔ ¬ IsUnit (e x)) :
    1 - (Nat.card {x : NumberField.mixedEmbedding.index K → ZMod d //
          normMod x = 0} : ℝ) /
        (d : ℝ) ^ Nat.card (NumberField.mixedEmbedding.index K) =
      (Nat.card Rˣ : ℝ) / Nat.card R := by
  classical
  let := Fintype.ofFinite (NumberField.mixedEmbedding.index K)
  have hcard : Nat.card (NumberField.mixedEmbedding.index K → ZMod d) =
      d ^ Nat.card (NumberField.mixedEmbedding.index K) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_pi]
    simp
  have h := one_sub_zeroResidueDensity_eq_unitRatio e normMod hzero
  have hzeroCard : Nat.card {x : NumberField.mixedEmbedding.index K → ZMod d //
      normMod x = 0} =
      (Finset.univ.filter fun x ↦ normMod x = 0).card :=
    Nat.subtype_card _ (by simp)
  rw [← hzeroCard] at h
  rw [hcard] at h
  push_cast at h
  exact h

private noncomputable def rationalPrimeQuotientFinite
    (K : Type*) [Field K] [NumberField K]
    (p : ℕ) (hp : p.Prime) :
    Finite (RingOfIntegers K ⧸ rationalModulusIdeal K p) :=
  (Ideal.absNorm_ne_zero_iff (rationalModulusIdeal K p)).mp (by
    rw [rationalModulusIdeal, Ideal.absNorm_span_natCast]
    exact pow_ne_zero _ hp.ne_zero)

private lemma mixedEmbedding_index_natCard
    (K : Type*) [Field K] [NumberField K] :
    Nat.card (NumberField.mixedEmbedding.index K) =
      Module.finrank ℤ (RingOfIntegers K) := by
  let := Fintype.ofFinite (NumberField.mixedEmbedding.index K)
  rw [Nat.card_eq_fintype_card,
    ← Module.finrank_eq_card_basis (NumberField.mixedEmbedding.stdBasis K),
    NumberField.mixedEmbedding.finrank, ← RingOfIntegers.rank]

/-! ## The fixed-ideal coordinates used by the ray norm sieve -/

private theorem rationalModulusIdeal_isCoprime_of_absNorm_coprime
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) (p : ℕ)
    (hcop : p.Coprime (Ideal.absNorm (J : Ideal (RingOfIntegers K)))) :
    IsCoprime (J : Ideal (RingOfIntegers K)) (rationalModulusIdeal K p) := by
  rw [Ideal.isCoprime_iff_sup_eq]
  apply Ideal.absNorm_eq_one_iff.mp
  have hJdiv : Ideal.absNorm
      ((J : Ideal (RingOfIntegers K)) ⊔ rationalModulusIdeal K p) ∣
      Ideal.absNorm (J : Ideal (RingOfIntegers K)) :=
    Ideal.absNorm_dvd_absNorm_of_le le_sup_left
  have hpdiv : Ideal.absNorm
      ((J : Ideal (RingOfIntegers K)) ⊔ rationalModulusIdeal K p) ∣
      p ^ Module.finrank ℤ (RingOfIntegers K) := by
    have := Ideal.absNorm_dvd_absNorm_of_le
      (show rationalModulusIdeal K p ≤
        (J : Ideal (RingOfIntegers K)) ⊔ rationalModulusIdeal K p from le_sup_right)
    simpa only [rationalModulusIdeal, Ideal.absNorm_span_natCast] using this
  have hnormCop : (Ideal.absNorm (J : Ideal (RingOfIntegers K))).Coprime
      (p ^ Module.finrank ℤ (RingOfIntegers K)) :=
    hcop.symm.pow_right _
  apply Nat.dvd_one.mp
  rw [← hnormCop.gcd_eq_one]
  exact Nat.dvd_gcd hJdiv hpdiv

private theorem fixedIdealCoordinateQuotientMap_injective
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) (p : ℕ) (hp : p.Prime)
    (hcop : p.Coprime (Ideal.absNorm (J : Ideal (RingOfIntegers K)))) :
    Function.Injective (fun k : NumberField.mixedEmbedding.index K → ZMod p ↦
      Ideal.Quotient.mk (rationalModulusIdeal K p)
        (RayNormPrimeSieve.generatorOfCoordinate K J k)) := by
  classical
  let : NeZero p := ⟨hp.ne_zero⟩
  intro k₁ k₂ hk
  let a₁ := RayNormPrimeSieve.generatorOfCoordinate K J k₁
  let a₂ := RayNormPrimeSieve.generatorOfCoordinate K J k₂
  have hmod : a₁ - a₂ ∈ rationalModulusIdeal K p :=
    Ideal.Quotient.eq.mp hk
  have hJ : a₁ - a₂ ∈ (J : Ideal (RingOfIntegers K)) :=
    (J : Ideal (RingOfIntegers K)).sub_mem
      (RayNormPrimeSieve.generatorOfCoordinate_mem K J k₁)
      (RayNormPrimeSieve.generatorOfCoordinate_mem K J k₂)
  have hcopIdeals := rationalModulusIdeal_isCoprime_of_absNorm_coprime K J p hcop
  have hprod : a₁ - a₂ ∈
      rationalModulusIdeal K p * (J : Ideal (RingOfIntegers K)) := by
    rw [mul_comm, Ideal.mul_eq_inf_of_isCoprime hcopIdeals]
    exact ⟨hJ, hmod⟩
  rw [rationalModulusIdeal, Ideal.mem_span_singleton_mul] at hprod
  obtain ⟨z, hzJ, hz⟩ := hprod
  have hzLat : NumberField.mixedEmbedding K (z : K) ∈
      (NumberField.mixedEmbedding.idealLattice K
        (FractionalIdeal.mk0 K J) :
          Set (NumberField.mixedEmbedding.mixedSpace K)) := by
    rw [SetLike.mem_coe, NumberField.mixedEmbedding.mem_idealLattice]
    refine ⟨(z : K), ?_, rfl⟩
    simp only [FractionalIdeal.coe_mk0]
    exact ⟨z, hzJ, rfl⟩
  have hzChart :
      (NumberField.mixedEmbedding.stdBasis K).equivFunL
          (NumberField.mixedEmbedding K (z : K)) ∈
        IdealGeneratorCongruenceCount.idealLatticeChart J ''
          (Submodule.span ℤ (Set.range
            (Pi.basisFun ℝ (NumberField.mixedEmbedding.index K))) :
              Set (NumberField.mixedEmbedding.index K → ℝ)) := by
    rw [IdealGeneratorCongruenceCount.idealLatticeChart_image]
    exact ⟨NumberField.mixedEmbedding K (z : K), hzLat, rfl⟩
  obtain ⟨v, hvInt, hvChart⟩ := hzChart
  have hvCoord : ∀ i, ∃ n : ℤ, v i = (n : ℝ) := by
    change v ∈ Submodule.span ℤ (Set.range
      (Pi.basisFun ℝ (NumberField.mixedEmbedding.index K))) at hvInt
    simpa only [
      (Pi.basisFun ℝ (NumberField.mixedEmbedding.index K)).mem_span_iff_repr_mem ℤ v,
      Pi.basisFun_repr, Set.mem_range, eq_intCast, eq_comm] using hvInt
  have hreal :
      IdealGeneratorCongruenceCount.idealLatticeChart J
          (fun i ↦ ((k₁ i).val : ℝ)) -
        IdealGeneratorCongruenceCount.idealLatticeChart J
          (fun i ↦ ((k₂ i).val : ℝ)) =
      p • IdealGeneratorCongruenceCount.idealLatticeChart J v := by
    calc
      IdealGeneratorCongruenceCount.idealLatticeChart J
            (fun i ↦ ((k₁ i).val : ℝ)) -
          IdealGeneratorCongruenceCount.idealLatticeChart J
            (fun i ↦ ((k₂ i).val : ℝ)) =
          (NumberField.mixedEmbedding.stdBasis K).equivFunL
              (NumberField.mixedEmbedding K (a₁ : K)) -
            (NumberField.mixedEmbedding.stdBasis K).equivFunL
              (NumberField.mixedEmbedding K (a₂ : K)) := by
        rw [RayNormPrimeSieve.embedding_generatorOfCoordinate,
          RayNormPrimeSieve.embedding_generatorOfCoordinate]
        rfl
      _ = (NumberField.mixedEmbedding.stdBasis K).equivFunL
          (NumberField.mixedEmbedding K ((a₁ - a₂ : RingOfIntegers K) : K)) := by
        push_cast
        rw [map_sub, map_sub]
      _ = (NumberField.mixedEmbedding.stdBasis K).equivFunL
          (NumberField.mixedEmbedding K
            (((p : RingOfIntegers K) * z : RingOfIntegers K) : K)) := by
        rw [hz]
      _ = p • (NumberField.mixedEmbedding.stdBasis K).equivFunL
          (NumberField.mixedEmbedding K (z : K)) := by
        rw [show (p : RingOfIntegers K) * z = p • z by rw [nsmul_eq_mul]]
        push_cast
        rw [map_nsmul, map_nsmul]
      _ = p • IdealGeneratorCongruenceCount.idealLatticeChart J v := by rw [hvChart]
  have hvectors :
      (fun i ↦ ((k₁ i).val : ℝ)) - (fun i ↦ ((k₂ i).val : ℝ)) = p • v := by
    apply (IdealGeneratorCongruenceCount.idealLatticeChart J).injective
    simpa only [map_sub, map_nsmul] using hreal
  funext i
  obtain ⟨n, hn⟩ := hvCoord i
  have hireal : ((k₁ i).val : ℝ) - ((k₂ i).val : ℝ) = (p : ℝ) * n := by
    have := congrFun hvectors i
    simpa only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, hn, Int.cast_ofNat] using this
  have hiint : ((k₁ i).val : ℤ) - ((k₂ i).val : ℤ) = (p : ℤ) * n := by
    exact_mod_cast hireal
  apply sub_eq_zero.mp
  calc
    k₁ i - k₂ i =
        ((((k₁ i).val : ℤ) - ((k₂ i).val : ℤ) : ℤ) : ZMod p) := by
      rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
        ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    _ = (((p : ℤ) * n : ℤ) : ZMod p) := by rw [hiint]
    _ = 0 := by simp

/-- The actual fixed-ideal coordinate vectors used by `RayNormPrimeSieve`, reduced in
`ᵒ K / pᵒ K`.  Coprimality of `p` and `N(J)` is exactly what makes reduction of the
index-`N(J)` lattice `J` onto the ambient quotient bijective. -/
noncomputable def fixedIdealCoordinateQuotientEquiv
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) (p : ℕ) (hp : p.Prime)
    (hcop : p.Coprime (Ideal.absNorm (J : Ideal (RingOfIntegers K)))) :
    (NumberField.mixedEmbedding.index K → ZMod p) ≃
      (RingOfIntegers K ⧸ rationalModulusIdeal K p) := by
  letI : Finite (RingOfIntegers K ⧸ rationalModulusIdeal K p) :=
    rationalPrimeQuotientFinite K p hp
  let f := fun k : NumberField.mixedEmbedding.index K → ZMod p ↦
    Ideal.Quotient.mk (rationalModulusIdeal K p)
      (RayNormPrimeSieve.generatorOfCoordinate K J k)
  apply Equiv.ofBijective f
  apply (Nat.bijective_iff_injective_and_card f).mpr
  refine ⟨fixedIdealCoordinateQuotientMap_injective K J p hp hcop, ?_⟩
  calc
    Nat.card (NumberField.mixedEmbedding.index K → ZMod p) =
        p ^ Nat.card (NumberField.mixedEmbedding.index K) := by
      rw [Nat.card_fun]
      simp
    _ = p ^ Module.finrank ℤ (RingOfIntegers K) := by
      rw [mixedEmbedding_index_natCard]
    _ = Nat.card (RingOfIntegers K ⧸ rationalModulusIdeal K p) := by
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
        rationalModulusIdeal, Ideal.absNorm_span_natCast]

@[simp]
theorem fixedIdealCoordinateQuotientEquiv_apply
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) (p : ℕ) (hp : p.Prime)
    (hcop : p.Coprime (Ideal.absNorm (J : Ideal (RingOfIntegers K))))
    (k : NumberField.mixedEmbedding.index K → ZMod p) :
    fixedIdealCoordinateQuotientEquiv K J p hp hcop k =
      Ideal.Quotient.mk (rationalModulusIdeal K p)
        (RayNormPrimeSieve.generatorOfCoordinate K J k) := rfl

private theorem prime_dvd_absNorm_span_iff_nonunit_mod
    (K : Type*) [Field K] [NumberField K]
    (p : ℕ) (hp : p.Prime) (a : RingOfIntegers K) :
    p ∣ Ideal.absNorm (Ideal.span ({a} : Set (RingOfIntegers K))) ↔
      ¬ IsUnit (Ideal.Quotient.mk (rationalModulusIdeal K p) a) := by
  constructor
  · intro hdiv hunit
    obtain ⟨P, hPmax, _hPunder, hPdvd⟩ :=
      Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp
        (Ideal.span ({a} : Set (RingOfIntegers K))) hdiv
    have hspanP : Ideal.span ({a} : Set (RingOfIntegers K)) ≤ P := by
      exact Ideal.dvd_iff_le.mp hPdvd
    have haP : a ∈ P := hspanP (Ideal.subset_span (Set.mem_singleton a))
    have hpP : (p : RingOfIntegers K) ∈ P := by
      have hpUnder : (p : ℤ) ∈ P.under ℤ := by
        rw [_hPunder]
        exact Ideal.subset_span (Set.mem_singleton _)
      rw [Ideal.under, Ideal.mem_comap] at hpUnder
      simpa using hpUnder
    have hmodP : rationalModulusIdeal K p ≤ P := by
      rw [rationalModulusIdeal, Ideal.span_le]
      intro x hx
      simpa only [Set.mem_singleton_iff] using hx ▸ hpP
    let : P.IsMaximal := hPmax
    let f : (RingOfIntegers K ⧸ rationalModulusIdeal K p) →+*
        (RingOfIntegers K ⧸ P) := Ideal.Quotient.factor hmodP
    have hzero : f (Ideal.Quotient.mk (rationalModulusIdeal K p) a) = 0 := by
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr haP]
    have hu := hunit.map f
    rw [hzero] at hu
    simpa using hu
  · intro hnonunit
    obtain ⟨M, hMmax, haM⟩ := exists_max_ideal_of_mem_nonunits hnonunit
    let P : Ideal (RingOfIntegers K) :=
      M.comap (Ideal.Quotient.mk (rationalModulusIdeal K p))
    let : M.IsMaximal := hMmax
    have hPmax : P.IsMaximal := by
      exact Ideal.comap_isMaximal_of_surjective
        (Ideal.Quotient.mk (rationalModulusIdeal K p))
        Ideal.Quotient.mk_surjective
    have haP : a ∈ P := haM
    have hmodP : rationalModulusIdeal K p ≤ P := by
      intro x hx
      change Ideal.Quotient.mk (rationalModulusIdeal K p) x ∈ M
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact M.zero_mem
    let : P.IsMaximal := hPmax
    obtain ⟨q, n, hn, _hqP, hq, hPnorm⟩ :=
      Ideal.exists_prime_and_absNorm_eq_pow P
    have hPnormDiv : Ideal.absNorm P ∣ p ^ Module.finrank ℤ (RingOfIntegers K) := by
      have := Ideal.absNorm_dvd_absNorm_of_le hmodP
      simpa only [rationalModulusIdeal, Ideal.absNorm_span_natCast] using this
    have hqDivPow : q ∣ p ^ Module.finrank ℤ (RingOfIntegers K) := by
      exact (dvd_pow_self q hn.ne').trans (by simpa only [hPnorm] using hPnormDiv)
    have hqp : q = p :=
      (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqDivPow)
    have hPdivA : Ideal.absNorm P ∣
        Ideal.absNorm (Ideal.span ({a} : Set (RingOfIntegers K))) :=
      Ideal.absNorm_dvd_absNorm_of_le
        ((Ideal.span_singleton_le_iff_mem P).mpr haP)
    exact (by
      rw [hPnorm, hqp] at hPdivA
      exact (dvd_pow_self p hn.ne').trans hPdivA)

/-- For the genuine fixed-ideal coordinates, the signed norm is zero modulo `p` exactly on
the nonunits of the ambient quotient. -/
theorem fixedIdeal_coordinateAlgebraNormMod_eq_zero_iff_nonunit
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) (p : ℕ) (hp : p.Prime)
    (hcop : p.Coprime (Ideal.absNorm (J : Ideal (RingOfIntegers K))))
    (k : NumberField.mixedEmbedding.index K → ZMod p) :
    RayNormPrimeSieve.coordinateAlgebraNormMod K J p k = 0 ↔
      ¬ IsUnit (fixedIdealCoordinateQuotientEquiv K J p hp hcop k) := by
  rw [fixedIdealCoordinateQuotientEquiv_apply,
    RayNormPrimeSieve.coordinateAlgebraNormMod,
    ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd,
    ← Ideal.absNorm_span_singleton]
  exact prime_dvd_absNorm_span_iff_nonunit_mod K p hp _

/-- Existential packaging convenient for consumers which only need a coordinate presentation
and the zero/nonunit criterion. -/
theorem exists_fixedIdealCoordinateQuotientEquiv
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) (p : ℕ) (hp : p.Prime)
    (hcop : p.Coprime (Ideal.absNorm (J : Ideal (RingOfIntegers K)))) :
    ∃ e : (NumberField.mixedEmbedding.index K → ZMod p) ≃
        (RingOfIntegers K ⧸ rationalModulusIdeal K p),
      ∀ k, RayNormPrimeSieve.coordinateAlgebraNormMod K J p k = 0 ↔
        ¬ IsUnit (e k) :=
  ⟨fixedIdealCoordinateQuotientEquiv K J p hp hcop,
    fixedIdeal_coordinateAlgebraNormMod_eq_zero_iff_nonunit K J p hp hcop⟩

/-- Exact complementary density for the norm form attached to the fixed ideal `J`. -/
theorem one_sub_fixedIdeal_coordinateNormResidueDensity_eq_unitRatio
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) (p : ℕ) (hp : p.Prime)
    (hcop : p.Coprime (Ideal.absNorm (J : Ideal (RingOfIntegers K)))) :
    1 - (Nat.card {k : NumberField.mixedEmbedding.index K → ZMod p //
          RayNormPrimeSieve.coordinateAlgebraNormMod K J p k = 0} : ℝ) /
        (p : ℝ) ^ Nat.card (NumberField.mixedEmbedding.index K) =
      (Nat.card ((RingOfIntegers K ⧸ rationalModulusIdeal K p)ˣ) : ℝ) /
        Nat.card (RingOfIntegers K ⧸ rationalModulusIdeal K p) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Finite (RingOfIntegers K ⧸ rationalModulusIdeal K p) :=
    rationalPrimeQuotientFinite K p hp
  exact one_sub_coordinateNormResidueDensity_eq_unitRatio K
    (fixedIdealCoordinateQuotientEquiv K J p hp hcop)
    (RayNormPrimeSieve.coordinateAlgebraNormMod K J p)
    (fixedIdeal_coordinateAlgebraNormMod_eq_zero_iff_nonunit K J p hp hcop)

end Erdos980.ElliottTail.LocalNormEuler
