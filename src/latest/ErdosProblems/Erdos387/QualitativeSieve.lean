/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.BrunMainTerm
import ErdosProblems.Erdos387.QualitativeCover
import ErdosProblems.Erdos387.SieveInstantiation
import Mathlib.Data.ZMod.Basic

/-!
# The fixed-parameter sieve on an unconditional absorber progression

The quantitative BNPZ argument needs estimates uniform while `k` grows.  For
Erdős Problem 387 we may instead freeze one unconditional absorber cover and
let only its progression parameter grow.  This file records the exact local
density and endpoint-error interface for that qualitative sieve.
-/

namespace Erdos387

open scoped BigOperators

namespace CoverBPZ.AbsorberCoverValid

/-- The absorber modulus has no prime factor among the sieving primes, hence
is coprime to every divisor of their squarefree product. -/
theorem coprime_Mk_of_dvd_sievePrimeProduct {m k z d : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (hd : d ∣ sievePrimeProduct k z) :
    Nat.Coprime C.toAbsorberCover.Mk d := by
  by_contra hcop
  obtain ⟨p, hp, hpM, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hple : p ≤ k := C.Mk_smooth p hp hpM
  have hpProd : p ∣ sievePrimeProduct k z := hpd.trans hd
  have hmem := prime_mem_sievePrimes_of_dvd_product hp hpProd
  exact (Nat.not_lt_of_ge hple) (mem_sievePrimes.mp hmem).2.1

/-- The unique progression-parameter residue which sends `N₀ + Mₖ t` to
the residue `a` modulo `d`. -/
noncomputable def parameterResidue {m k z d : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (hd : d ∣ sievePrimeProduct k z) (a : ℕ) : ℕ := by
  let u : (ZMod d)ˣ :=
    ZMod.unitOfCoprime C.toAbsorberCover.Mk
      (C.coprime_Mk_of_dvd_sievePrimeProduct hd)
  exact (u⁻¹.mulLeft ((a : ZMod d) - (C.toAbsorberCover.N₀ : ZMod d))).val

theorem parameterResidue_lt {m k z d : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (hd : d ∣ sievePrimeProduct k z) (a : ℕ) :
    C.parameterResidue hd a < d := by
  letI : NeZero d := ⟨(pos_of_dvd_sievePrimeProduct hd).ne'⟩
  unfold parameterResidue
  exact ZMod.val_lt _

theorem nNat_zmod {m k z d : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (hd : d ∣ sievePrimeProduct k z) (t : ℕ) :
    (C.nNat t : ZMod d) =
      (C.toAbsorberCover.N₀ : ZMod d) +
        (C.toAbsorberCover.Mk : ZMod d) * (t : ZMod d) := by
  have h := C.nNat_cast t
  have hz := congrArg (fun x : ℤ => (x : ZMod d)) h
  simpa [CoverBPZ.AbsorberCover.N, Int.cast_add, Int.cast_mul,
    Int.cast_natCast, Nat.cast_mul] using hz

theorem parameterResidue_zmod {m k z d : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (hd : d ∣ sievePrimeProduct k z) (a : ℕ) :
    (C.parameterResidue hd a : ZMod d) =
      (((ZMod.unitOfCoprime C.toAbsorberCover.Mk
          (C.coprime_Mk_of_dvd_sievePrimeProduct hd))⁻¹ : (ZMod d)ˣ) : ZMod d) *
        ((a : ZMod d) - (C.toAbsorberCover.N₀ : ZMod d)) := by
  have hdpos : 0 < d := pos_of_dvd_sievePrimeProduct hd
  letI : NeZero d := ⟨hdpos.ne'⟩
  unfold parameterResidue
  rw [ZMod.natCast_zmod_val]
  rfl

/-- The chosen parameter residue really maps to `a` under the absorber's
affine progression. -/
theorem affine_parameterResidue {m k z d : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (hd : d ∣ sievePrimeProduct k z) (a : ℕ) :
    (C.toAbsorberCover.N₀ : ZMod d) +
        (C.toAbsorberCover.Mk : ZMod d) *
          (C.parameterResidue hd a : ZMod d) = (a : ZMod d) := by
  rw [C.parameterResidue_zmod hd a]
  let u : (ZMod d)ˣ :=
    ZMod.unitOfCoprime C.toAbsorberCover.Mk
      (C.coprime_Mk_of_dvd_sievePrimeProduct hd)
  rw [show (C.toAbsorberCover.Mk : ZMod d) = (u : ZMod d) by rfl]
  rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    one_mul, add_sub_cancel]

/-- The inverse-affine change of residue is injective on canonical
representatives. -/
theorem parameterResidue_injective_on {m k z d : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (hd : d ∣ sievePrimeProduct k z) {a b : ℕ}
    (ha : a < d) (hb : b < d)
    (h : C.parameterResidue hd a = C.parameterResidue hd b) : a = b := by
  have haffA := C.affine_parameterResidue hd a
  have haffB := C.affine_parameterResidue hd b
  rw [h] at haffA
  have hz : (a : ZMod d) = (b : ZMod d) := haffA.symm.trans haffB
  have hm := (ZMod.natCast_eq_natCast_iff' a b d).mp hz
  simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hm

/-- Affine transport converts the canonical forbidden residue `a` for the
binomial argument into a canonical residue for the progression parameter. -/
theorem nNat_mod_eq_iff_parameter_mod_eq {m k z d t a : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (hd : d ∣ sievePrimeProduct k z) (ha : a < d) :
    C.nNat t % d = a ↔ t % d = C.parameterResidue hd a := by
  have hr : C.parameterResidue hd a < d := C.parameterResidue_lt hd a
  let u : (ZMod d)ˣ :=
    ZMod.unitOfCoprime C.toAbsorberCover.Mk
      (C.coprime_Mk_of_dvd_sievePrimeProduct hd)
  have hunit : (C.toAbsorberCover.Mk : ZMod d) = (u : ZMod d) := rfl
  constructor
  · intro hna
    have hnz : (C.nNat t : ZMod d) = (a : ZMod d) := by
      apply (ZMod.natCast_eq_natCast_iff' (C.nNat t) a d).2
      simpa [Nat.mod_eq_of_lt ha] using hna
    have haff := C.affine_parameterResidue hd a
    rw [C.nNat_zmod hd t] at hnz
    have hsum :
        (C.toAbsorberCover.N₀ : ZMod d) +
            (C.toAbsorberCover.Mk : ZMod d) * (t : ZMod d) =
          (C.toAbsorberCover.N₀ : ZMod d) +
            (C.toAbsorberCover.Mk : ZMod d) *
              (C.parameterResidue hd a : ZMod d) := hnz.trans haff.symm
    have hmul := add_left_cancel hsum
    rw [hunit] at hmul
    have ht : (t : ZMod d) = (C.parameterResidue hd a : ZMod d) := by
      exact u.mulLeft.injective hmul
    have hm := (ZMod.natCast_eq_natCast_iff' t
      (C.parameterResidue hd a) d).mp ht
    simpa [Nat.mod_eq_of_lt hr] using hm
  · intro htr
    have ht : (t : ZMod d) = (C.parameterResidue hd a : ZMod d) := by
      apply (ZMod.natCast_eq_natCast_iff' t
        (C.parameterResidue hd a) d).2
      simpa [Nat.mod_eq_of_lt hr] using htr
    have hnz := C.nNat_zmod hd t
    rw [ht] at hnz
    have haff := C.affine_parameterResidue hd a
    have hz : (C.nNat t : ZMod d) = (a : ZMod d) := hnz.trans haff
    have hm := (ZMod.natCast_eq_natCast_iff' (C.nNat t) a d).mp hz
    simpa [Nat.mod_eq_of_lt ha] using hm

/-- The transported set of all forbidden parameter residues modulo `d`. -/
noncomputable def parameterResidues {m k z d : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (hd : d ∣ sievePrimeProduct k z) : Finset ℕ := by
  classical
  exact (localAssignmentResidues d k).image (C.parameterResidue hd)

theorem parameterResidues_lt {m k z d : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (hd : d ∣ sievePrimeProduct k z) :
    ∀ a ∈ C.parameterResidues hd, a < d := by
  intro a ha
  rw [parameterResidues, Finset.mem_image] at ha
  obtain ⟨b, _, rfl⟩ := ha
  exact C.parameterResidue_lt hd b

/-- Affine transport preserves the exact `k ^ ω(d)` multiplicity. -/
theorem card_parameterResidues {m k z d : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (hd : d ∣ sievePrimeProduct k z) (hsq : Squarefree d)
    (hlarge : ∀ p ∈ d.primeFactors, k < p) :
    (C.parameterResidues hd).card = k ^ d.primeFactors.card := by
  classical
  unfold parameterResidues
  rw [(Finset.card_image_iff).mpr]
  · exact card_localAssignmentResidues hlarge
  · intro a ha b hb hab
    apply C.parameterResidue_injective_on hd _ _ hab
    · change a ∈ localAssignmentResidues d k at ha
      rw [localAssignmentResidues, Finset.mem_image] at ha
      obtain ⟨A, _, rfl⟩ := ha
      exact localAssignmentResidue_lt hsq A
    · change b ∈ localAssignmentResidues d k at hb
      rw [localAssignmentResidues, Finset.mem_image] at hb
      obtain ⟨A, _, rfl⟩ := hb
      exact localAssignmentResidue_lt hsq A

/-- Membership in the transported residue set is exactly local binomial
divisibility after evaluating the absorber progression. -/
theorem mod_mem_parameterResidues_iff {m k z d t : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (hd : d ∣ sievePrimeProduct k z) (hsq : Squarefree d) :
    t % d ∈ C.parameterResidues hd ↔
      C.nNat t % d ∈ localAssignmentResidues d k := by
  classical
  constructor
  · intro ht
    rw [parameterResidues, Finset.mem_image] at ht
    obtain ⟨a, ha, hat⟩ := ht
    have halt : a < d := by
      rw [localAssignmentResidues, Finset.mem_image] at ha
      obtain ⟨A, _, rfl⟩ := ha
      exact localAssignmentResidue_lt hsq A
    have hn := (C.nNat_mod_eq_iff_parameter_mod_eq hd halt).2 hat.symm
    simpa [hn] using ha
  · intro hn
    rw [parameterResidues, Finset.mem_image]
    refine ⟨C.nNat t % d, hn, ?_⟩
    have halt : C.nNat t % d < d :=
      Nat.mod_lt _ (pos_of_dvd_sievePrimeProduct hd)
    exact (C.nNat_mod_eq_iff_parameter_mod_eq hd halt).1 rfl |>.symm

/-- A squarefree sieve divisor divides the progression binomial coefficient
exactly on the transported parameter classes. -/
theorem dvd_choose_iff_mod_mem_parameterResidues {m k z d t : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (hd : d ∣ sievePrimeProduct k z) :
    d ∣ (C.nNat t).choose k ↔ t % d ∈ C.parameterResidues hd := by
  have hsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd (sievePrimeProduct_squarefree k z)
  have hlarge : ∀ p ∈ d.primeFactors, k < p :=
    fun p hp => primeFactor_large_of_dvd_sievePrimeProduct hd hp
  rw [C.mod_mem_parameterResidues_iff hd hsq,
    ← squarefree_dvd_choose_iff_mod_mem_localAssignmentResidues
      hsq hlarge (C.k_lt_nNat t).le]

end CoverBPZ.AbsorberCoverValid

/-- A dyadic interval of parameters on one fixed absorber progression. -/
def AbsorberParameterCandidates (T : ℕ) : Finset ℕ :=
  Finset.Ioc (T / 2) T

/-- Parameters in the dyadic interval at which a modulus divides the
binomial coefficient. -/
noncomputable def DivisibleAbsorberParameterCandidates {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (T d : ℕ) : Finset ℕ := by
  classical
  exact (AbsorberParameterCandidates T).filter fun t =>
    d ∣ (C.nNat t).choose k

/-- The divisibility subset is exactly a union of transported residue
classes modulo `d`. -/
theorem divisibleAbsorberParameterCandidates_eq_modularPreimageIoc
    {m k T z d : ℕ} (C : CoverBPZ.AbsorberCoverValid m k)
    (hd : d ∣ sievePrimeProduct k z) :
    DivisibleAbsorberParameterCandidates C T d =
      modularPreimageIoc (T / 2) T d (C.parameterResidues hd) := by
  classical
  ext t
  simp only [DivisibleAbsorberParameterCandidates,
    AbsorberParameterCandidates, modularPreimageIoc, Finset.mem_filter,
    Finset.mem_Ioc]
  exact and_congr_right fun _ => C.dvd_choose_iff_mod_mem_parameterResidues hd

/-- Exact local-density discrepancy on the fixed absorber progression.  The
only error comes from the two endpoints of the parameter interval. -/
theorem abs_card_divisibleAbsorberParameterCandidates_sub_density
    {m k T z d : ℕ} (C : CoverBPZ.AbsorberCoverValid m k)
    (hd : d ∣ sievePrimeProduct k z) :
    |((DivisibleAbsorberParameterCandidates C T d).card : ℝ) -
        (k : ℝ) ^ d.primeFactors.card * ((T - T / 2 : ℕ) : ℝ) / d| ≤
      2 * (k : ℝ) ^ d.primeFactors.card := by
  have hsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd (sievePrimeProduct_squarefree k z)
  have hlarge : ∀ p ∈ d.primeFactors, k < p :=
    fun p hp => primeFactor_large_of_dvd_sievePrimeProduct hd hp
  have h := abs_card_modularPreimageIoc_sub_density
    (L := T / 2) (U := T) (g := d) (Nat.div_le_self T 2)
    (pos_of_dvd_sievePrimeProduct hd) (C.parameterResidues hd)
    (C.parameterResidues_lt hd)
  rw [← divisibleAbsorberParameterCandidates_eq_modularPreimageIoc C hd,
    C.card_parameterResidues hd hsq hlarge] at h
  simpa using h

theorem card_absorberParameterCandidates (T : ℕ) :
    (AbsorberParameterCandidates T).card = T - T / 2 := by
  simp [AbsorberParameterCandidates]

/-- Multiplicative local density with exact squarefree value
`k ^ ω(d) / d`, now attached to the parameter interval. -/
noncomputable def absorberBoundingSieve {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (hk : 0 < k)
    (T z : ℕ) : BoundingSieve := by
  classical
  let A := AbsorberParameterCandidates T
  exact
    { support := A.image fun t => (C.nNat t).choose k
      prodPrimes := sievePrimeProduct k z
      prodPrimes_squarefree := sievePrimeProduct_squarefree k z
      weights := fun q =>
        ((A.filter fun t => (C.nNat t).choose k = q).card : ℝ)
      weights_nonneg := fun _ => by positivity
      totalMass := A.card
      nu := binomialSieveNu k
      nu_mult := binomialSieveNu_mult k
      nu_pos_of_prime := by
        intro p hp hdiv
        rw [binomialSieveNu_prime hp]
        have hmem := prime_mem_sievePrimes_of_dvd_product hp hdiv
        exact div_pos (by exact_mod_cast hk) (by exact_mod_cast hp.pos)
      nu_lt_one_of_prime := by
        intro p hp hdiv
        rw [binomialSieveNu_prime hp]
        have hmem := prime_mem_sievePrimes_of_dvd_product hp hdiv
        have hkp : k < p := (mem_sievePrimes.mp hmem).2.1
        exact (div_lt_one (by exact_mod_cast hp.pos)).mpr
          (by exact_mod_cast hkp) }

theorem absorberBoundingSieve_totalMass {m k T z : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (hk : 0 < k) :
    (absorberBoundingSieve C hk T z).totalMass =
      (T - T / 2 : ℕ) := by
  change ((AbsorberParameterCandidates T).card : ℝ) = _
  rw [card_absorberParameterCandidates]

/-- The fixed finite local Euler product of the absorber sieve. -/
noncomputable def absorberEulerProduct (k z : ℕ) : ℝ :=
  finiteEulerProduct (sievePrimeProduct k z).primeFactors
    (fun p => binomialSieveNu k p)

/-- Elementary pointwise majorant for the ratio between the powers-of-two
moment factor and the sieve Euler factor.  Only the finitely many primes up
to `2k` pay the constant `4k`; all larger primes pay `1 + 6k/p`. -/
noncomputable def binomialMomentMajorant (k p : ℕ) : ℝ :=
  if p ≤ 2 * k then 4 * k else 1 + (6 * k : ℝ) / p

theorem binomial_moment_le_small_majorant {k p : ℕ}
    (hk : 0 < k) (hp : p.Prime) (hkp : k < p) (hpk : p ≤ 2 * k) :
    1 + 2 * binomialSieveNu k p ≤
      (4 * k : ℝ) * (1 - binomialSieveNu k p) := by
  rw [binomialSieveNu_prime hp]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hkpR : (k : ℝ) < p := by exact_mod_cast hkp
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hgap : (1 : ℝ) ≤ (p : ℝ) - k := by
    have hkplusR : (k : ℝ) + 1 ≤ p := by
      exact_mod_cast (show k + 1 ≤ p by omega)
    linarith
  have hcoef : (3 : ℝ) * k ≤ 4 * k - 1 := by
    linarith
  have hcoefNonneg : (0 : ℝ) ≤ 4 * k - 1 := by linarith
  have hmul : 3 * (k : ℝ) ≤ (4 * k - 1) * ((p : ℝ) - k) :=
    hcoef.trans (by
      simpa using mul_le_mul_of_nonneg_left hgap hcoefNonneg)
  field_simp
  nlinarith

theorem binomial_moment_le_large_majorant {k p : ℕ}
    (hp : p.Prime) (hpk : 2 * k < p) :
    1 + 2 * binomialSieveNu k p ≤
      (1 + (6 * k : ℝ) / p) * (1 - binomialSieveNu k p) := by
  rw [binomialSieveNu_prime hp]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpkR : (2 * k : ℝ) < p := by exact_mod_cast hpk
  have hdiff : (0 : ℝ) ≤ (p : ℝ) - 2 * k := (sub_pos.mpr hpkR).le
  have hnonneg : 0 ≤ (3 : ℝ) * k * ((p : ℝ) - 2 * k) := by positivity
  field_simp
  nlinarith

theorem binomial_moment_le_majorant {k p : ℕ}
    (hk : 0 < k) (hp : p.Prime) (hkp : k < p) :
    1 + 2 * binomialSieveNu k p ≤
      binomialMomentMajorant k p * (1 - binomialSieveNu k p) := by
  unfold binomialMomentMajorant
  by_cases hpk : p ≤ 2 * k
  · rw [if_pos hpk]
    exact binomial_moment_le_small_majorant hk hp hkp hpk
  · rw [if_neg hpk]
    exact binomial_moment_le_large_majorant hp (Nat.lt_of_not_ge hpk)

/-- The product of the elementary local majorants grows only polynomially in
the roughness threshold.  This deliberately crude bound uses no PNT or
Mertens theorem. -/
theorem prod_binomialMomentMajorant_le {k z : ℕ} (hk : 0 < k) :
    (∏ p ∈ (sievePrimeProduct k z).primeFactors,
        binomialMomentMajorant k p) ≤
      (4 * k : ℝ) ^ (2 * k + 1) *
        ((z + 1 : ℕ) : ℝ) ^ (6 * k) := by
  let P := (sievePrimeProduct k z).primeFactors
  let S := P.filter fun p => p ≤ 2 * k
  let G := P.filter fun p => ¬p ≤ 2 * k
  have hsplit :
      (∏ p ∈ P, binomialMomentMajorant k p) =
        (∏ _p ∈ S, (4 * k : ℝ)) *
          ∏ p ∈ G, (1 + (6 * k : ℝ) / p) := by
    simpa [binomialMomentMajorant, S, G] using
      (Finset.prod_ite (s := P) (p := fun p => p ≤ 2 * k)
        (fun _p => (4 * k : ℝ))
        (fun p => 1 + (6 * k : ℝ) / p))
  have hSsub : S ⊆ Finset.range (2 * k + 1) := by
    intro p hp
    have hp' : p ∈ P ∧ p ≤ 2 * k := by simpa [S] using hp
    rw [Finset.mem_range]
    omega
  have hScard : S.card ≤ 2 * k + 1 := by
    simpa using Finset.card_le_card hSsub
  have hbase : (1 : ℝ) ≤ 4 * k := by
    exact_mod_cast (by omega : 1 ≤ 4 * k)
  have hsmall :
      (∏ _p ∈ S, (4 * k : ℝ)) ≤ (4 * k : ℝ) ^ (2 * k + 1) := by
    simp only [Finset.prod_const]
    exact pow_le_pow_right₀ hbase hScard
  have hGpos : ∀ p ∈ G, 0 < p := by
    intro p hpG
    have hpP := (Finset.mem_filter.mp hpG).1
    exact (Nat.prime_of_mem_primeFactors hpP).pos
  have hGle : ∀ p ∈ G, p ≤ z := by
    intro p hpG
    have hpP := (Finset.mem_filter.mp hpG).1
    have hpPrime := Nat.prime_of_mem_primeFactors hpP
    have hpProd := Nat.dvd_of_mem_primeFactors hpP
    exact (mem_sievePrimes.mp
      (prime_mem_sievePrimes_of_dvd_product hpPrime hpProd)).2.2.le
  have hlarge :
      (∏ p ∈ G, (1 + (6 * k : ℝ) / p)) ≤
        ((z + 1 : ℕ) : ℝ) ^ (6 * k) :=
    by simpa [Nat.cast_mul] using
      prod_one_add_nat_div_le_pow G (6 * k) z hGpos hGle
  rw [show (sievePrimeProduct k z).primeFactors = P by rfl, hsplit]
  exact mul_le_mul hsmall hlarge
    (Finset.prod_nonneg fun p hp => by
      exact add_nonneg (by norm_num) (div_nonneg (by positivity) (by positivity)))
    (by positivity)

theorem absorberEulerProduct_pos {m k z : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (hk : 0 < k) :
    0 < absorberEulerProduct k z := by
  have h := boundingSieve_finiteEulerProduct_pos
    (absorberBoundingSieve C hk 0 z)
  exact h

/-- Polynomial comparison between the complete powers-of-two moment and the
finite binomial Euler product. -/
theorem absorberMomentProduct_le_majorant_mul_euler {m k z : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (hk : 0 < k) :
    (∏ p ∈ (sievePrimeProduct k z).primeFactors,
        (1 + 2 * binomialSieveNu k p)) ≤
      ((4 * k : ℝ) ^ (2 * k + 1) *
          ((z + 1 : ℕ) : ℝ) ^ (6 * k)) *
        absorberEulerProduct k z := by
  let P := (sievePrimeProduct k z).primeFactors
  have hlocal : ∀ p ∈ P,
      1 + 2 * binomialSieveNu k p ≤
        binomialMomentMajorant k p * (1 - binomialSieveNu k p) := by
    intro p hpP
    have hpPrime := Nat.prime_of_mem_primeFactors hpP
    have hpProd := Nat.dvd_of_mem_primeFactors hpP
    have hmem := mem_sievePrimes.mp
      (prime_mem_sievePrimes_of_dvd_product hpPrime hpProd)
    exact binomial_moment_le_majorant hk hpPrime hmem.2.1
  have hmajorant := prod_binomialMomentMajorant_le (z := z) hk
  have hV := (absorberEulerProduct_pos C hk (z := z)).le
  calc
    (∏ p ∈ (sievePrimeProduct k z).primeFactors,
        (1 + 2 * binomialSieveNu k p)) ≤
        ∏ p ∈ P, (binomialMomentMajorant k p *
          (1 - binomialSieveNu k p)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hpPrime := Nat.prime_of_mem_primeFactors hp
        rw [binomialSieveNu_prime hpPrime]
        positivity
      · exact hlocal
    _ = (∏ p ∈ P, binomialMomentMajorant k p) *
          absorberEulerProduct k z := by
      rw [Finset.prod_mul_distrib]
      rfl
    _ ≤ ((4 * k : ℝ) ^ (2 * k + 1) *
          ((z + 1 : ℕ) : ℝ) ^ (6 * k)) *
        absorberEulerProduct k z := by
      exact mul_le_mul_of_nonneg_right (by simpa [P] using hmajorant) hV

/-- Crude but completely elementary polynomial lower bound for the local
Euler product, written without division. -/
theorem one_le_elementaryMajorant_mul_absorberEulerProduct {m k z : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (hk : 0 < k) :
    1 ≤ ((4 * k : ℝ) ^ (2 * k + 1) *
          ((z + 1 : ℕ) : ℝ) ^ (6 * k)) *
        absorberEulerProduct k z := by
  have hmoment := absorberMomentProduct_le_majorant_mul_euler C hk (z := z)
  have hone :
      1 ≤ ∏ p ∈ (sievePrimeProduct k z).primeFactors,
          (1 + 2 * binomialSieveNu k p) := by
    apply Finset.one_le_prod
    intro p hpP
    have hpPrime := Nat.prime_of_mem_primeFactors hpP
    rw [binomialSieveNu_prime hpPrime]
    exact le_add_of_nonneg_right
      (mul_nonneg (by norm_num) (div_nonneg (by positivity) (by positivity)))
  exact hone.trans hmoment

/-- A fully elementary numerical condition implying that the odd Brun main
sum lies above half the Euler product.  Its required depth is logarithmic in
`z`, because the right-hand coefficient above is polynomial in `z`. -/
theorem absorber_brunTail_le_half_of_pow_bound {m k z L : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (hk : 0 < k)
    (hpow :
      2 * ((4 * k : ℝ) ^ (2 * k + 1) *
          ((z + 1 : ℕ) : ℝ) ^ (6 * k)) ≤
        (2 : ℝ) ^ (L + 1)) :
    2 * brunSubsetTail (sievePrimeProduct k z).primeFactors
          (fun p => binomialSieveNu k p) L ≤
      absorberEulerProduct k z := by
  apply two_mul_brunSubsetTail_le_of_moment
  · intro p hpP
    have hpPrime := Nat.prime_of_mem_primeFactors hpP
    rw [binomialSieveNu_prime hpPrime]
    positivity
  · have hmoment := absorberMomentProduct_le_majorant_mul_euler C hk (z := z)
    have hV := (absorberEulerProduct_pos C hk (z := z)).le
    calc
      2 * (∏ p ∈ (sievePrimeProduct k z).primeFactors,
          (1 + 2 * binomialSieveNu k p)) ≤
          2 * (((4 * k : ℝ) ^ (2 * k + 1) *
            ((z + 1 : ℕ) : ℝ) ^ (6 * k)) *
              absorberEulerProduct k z) := by gcongr
      _ = (2 * ((4 * k : ℝ) ^ (2 * k + 1) *
            ((z + 1 : ℕ) : ℝ) ^ (6 * k))) *
              absorberEulerProduct k z := by ring
      _ ≤ (2 : ℝ) ^ (L + 1) * absorberEulerProduct k z :=
        mul_le_mul_of_nonneg_right hpow hV
      _ = (2 : ℝ) ^ (L + 1) *
          finiteEulerProduct (sievePrimeProduct k z).primeFactors
            (fun p => binomialSieveNu k p) := by rfl

/-- Natural coefficient appearing in the elementary moment bound. -/
def elementaryBrunCoefficient (k z : ℕ) : ℕ :=
  2 * (4 * k) ^ (2 * k + 1) * (z + 1) ^ (6 * k)

/-- An explicit odd truncation depth.  It is twice a base-two logarithm of
the moment coefficient, plus one. -/
def elementaryBrunDepth (k z : ℕ) : ℕ :=
  2 * Nat.log 2 (elementaryBrunCoefficient k z) + 1

/-- Polynomial coefficient in the Euler-product reciprocal bound. -/
def elementaryMomentCoefficient (k z : ℕ) : ℕ :=
  (4 * k) ^ (2 * k + 1) * (z + 1) ^ (6 * k)

/-- Natural version of the explicit endpoint-error bound at the elementary
Brun depth. -/
def elementaryBrunEndpointError (k z : ℕ) : ℕ :=
  2 * (z ^ elementaryBrunDepth k z + 1) *
    k ^ elementaryBrunDepth k z

/-- Explicit parameter scale at which the elementary main term dominates
the endpoint errors. -/
def elementaryBrunScale (T₀ k z : ℕ) : ℕ :=
  T₀ + 2 * elementaryBrunEndpointError k z *
    elementaryMomentCoefficient k z + 1

theorem elementaryBrunDepth_odd (k z : ℕ) :
    Odd (elementaryBrunDepth k z) := by
  refine ⟨Nat.log 2 (elementaryBrunCoefficient k z), ?_⟩
  simp [elementaryBrunDepth]

theorem elementaryBrunCoefficient_le_pow_depth (k z : ℕ) :
    elementaryBrunCoefficient k z ≤
      2 ^ (elementaryBrunDepth k z + 1) := by
  let A := elementaryBrunCoefficient k z
  have hlog : A < 2 ^ (Nat.log 2 A + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) A
  have hexp : Nat.log 2 A + 1 ≤ elementaryBrunDepth k z + 1 := by
    simp [elementaryBrunDepth, A]
    omega
  exact hlog.le.trans (Nat.pow_le_pow_right (by norm_num) hexp)

/-- The explicit logarithmic-depth truncation satisfies the half-Euler-
product tail estimate. -/
theorem absorber_brunTail_le_half_elementaryDepth {m k z : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (hk : 0 < k) :
    2 * brunSubsetTail (sievePrimeProduct k z).primeFactors
          (fun p => binomialSieveNu k p) (elementaryBrunDepth k z) ≤
      absorberEulerProduct k z := by
  apply absorber_brunTail_le_half_of_pow_bound C hk
  have hnat := elementaryBrunCoefficient_le_pow_depth k z
  have hreal :
      (elementaryBrunCoefficient k z : ℝ) ≤
        (2 : ℝ) ^ (elementaryBrunDepth k z + 1) := by
    exact_mod_cast hnat
  simp [elementaryBrunCoefficient, Nat.cast_mul, Nat.cast_pow] at hreal
  convert hreal using 1 <;> push_cast <;> ring

theorem absorberBoundingSieve_mainSum_eq_euler_of_card_le
    {m k T z L : ℕ} (C : CoverBPZ.AbsorberCoverValid m k)
    (hk : 0 < k) (hcard : (sievePrimeProduct k z).primeFactors.card ≤ L) :
    (absorberBoundingSieve C hk T z).mainSum (brunLowerWeight L) =
      absorberEulerProduct k z := by
  exact boundingSieve_mainSum_brunLowerWeight_eq_euler_of_card_le
    (absorberBoundingSieve C hk T z) hcard

/-- The literal parameter set left after sieving the binomial coefficient by
all primes in `(k,z)`. -/
noncomputable def SiftedAbsorberParameterCandidates {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (T z : ℕ) : Finset ℕ := by
  classical
  exact (AbsorberParameterCandidates T).filter fun t =>
    Nat.Coprime (sievePrimeProduct k z) ((C.nNat t).choose k)

/-- Sifting the binomial coefficient by all primes in `(k,z)` makes the
large-prime part of each individual residual `z`-rough.  Small primes are
intentionally absent from this conclusion; they are frozen separately. -/
theorem largePrimePart_isZRough_of_coprime_sievePrimeProduct
    {m k t z : ℕ} (C : CoverBPZ.AbsorberCoverValid m k)
    (hcop : Nat.Coprime (sievePrimeProduct k z) ((C.nNat t).choose k))
    (j : Fin k) :
    IsZRough z
      (CoverBPZ.AbsorberCoverValid.largePrimePart k (C.residual t j)) := by
  intro p hp hpz hpLarge
  have hkp : k < p :=
    CoverBPZ.AbsorberCoverValid.lt_of_prime_dvd_largePrimePart hp hpLarge
  have hpMem : p ∈ sievePrimes k z :=
    mem_sievePrimes.mpr ⟨hp, hkp, hpz⟩
  have hpProd : p ∣ sievePrimeProduct k z := by
    unfold sievePrimeProduct
    exact Finset.dvd_prod_of_mem id hpMem
  have hresNe : C.residual t j ≠ 0 := (C.residual_pos t j).ne'
  have hpChoose : p ∣ (C.nNat t).choose k :=
    hpLarge.trans
      ((CoverBPZ.AbsorberCoverValid.largePrimePart_dvd hresNe).trans
        (C.residual_dvd_choose t j))
  have hpCop : Nat.Coprime p ((C.nNat t).choose k) :=
    Nat.Coprime.of_dvd_left hpProd hcop
  exact (hp.coprime_iff_not_dvd.mp hpCop) hpChoose

theorem largePrimePart_isZRough_of_mem_siftedAbsorberParameters
    {m k T z t : ℕ} (C : CoverBPZ.AbsorberCoverValid m k)
    (ht : t ∈ SiftedAbsorberParameterCandidates C T z) (j : Fin k) :
    IsZRough z
      (CoverBPZ.AbsorberCoverValid.largePrimePart k (C.residual t j)) := by
  have hcop :
      Nat.Coprime (sievePrimeProduct k z) ((C.nNat t).choose k) := by
    simpa [SiftedAbsorberParameterCandidates] using
      (Finset.mem_filter.mp ht).2
  exact largePrimePart_isZRough_of_coprime_sievePrimeProduct C hcop j

/-- On the frozen subprogression, every sifted residual is a fixed
small-prime coefficient times a `z`-rough factor. -/
theorem frozen_residual_eq_fixedSmallPart_mul_rough
    {m k T z t₀ t : ℕ} (C : CoverBPZ.AbsorberCoverValid m k)
    (ht : t ∈ SiftedAbsorberParameterCandidates (C.frozen t₀) T z)
    (j : Fin k) :
    (C.frozen t₀).residual t j =
        CoverBPZ.AbsorberCoverValid.smallPrimePart k (C.residual t₀ j) *
          CoverBPZ.AbsorberCoverValid.largePrimePart k
            ((C.frozen t₀).residual t j) ∧
      IsZRough z
        (CoverBPZ.AbsorberCoverValid.largePrimePart k
          ((C.frozen t₀).residual t j)) := by
  constructor
  · exact C.frozen_residual_eq_smallPrimePart_mul_largePrimePart t₀ t j
  · exact largePrimePart_isZRough_of_mem_siftedAbsorberParameters
      (C.frozen t₀) ht j

/-- The abstract sieve's weighted sifted sum is literally the cardinality of
the sifted parameter set. -/
theorem absorberBoundingSieve_siftedSum {m k T z : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (hk : 0 < k) :
    (absorberBoundingSieve C hk T z).siftedSum =
      ((SiftedAbsorberParameterCandidates C T z).card : ℝ) := by
  classical
  let A := AbsorberParameterCandidates T
  let f : ℕ → ℕ := fun t => (C.nNat t).choose k
  rw [BoundingSieve.siftedSum]
  change (∑ q ∈ A.image f,
      if Nat.Coprime (sievePrimeProduct k z) q then
        ((A.filter fun t => f t = q).card : ℝ) else 0) = _
  simp_rw [← Finset.sum_filter]
  have hcard :
      (∑ q ∈ (A.image f).filter fun q =>
          Nat.Coprime (sievePrimeProduct k z) q,
          (A.filter fun t => f t = q).card) =
        (A.filter fun t =>
          Nat.Coprime (sievePrimeProduct k z) (f t)).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcard]
  norm_cast

/-- The abstract multiple sum is the literal divisibility-subset
cardinality. -/
theorem absorberBoundingSieve_multSum {m k T z d : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (hk : 0 < k) :
    (absorberBoundingSieve C hk T z).multSum d =
      ((DivisibleAbsorberParameterCandidates C T d).card : ℝ) := by
  classical
  let A := AbsorberParameterCandidates T
  let f : ℕ → ℕ := fun t => (C.nNat t).choose k
  rw [BoundingSieve.multSum]
  change (∑ q ∈ A.image f,
      if d ∣ q then ((A.filter fun t => f t = q).card : ℝ) else 0) = _
  simp_rw [← Finset.sum_filter]
  have hcard :
      (∑ q ∈ (A.image f).filter fun q => d ∣ q,
          (A.filter fun t => f t = q).card) =
        (A.filter fun t => d ∣ f t).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcard]
  norm_cast

/-- The abstract remainder has a completely explicit endpoint bound. -/
theorem absorberBoundingSieve_abs_rem_le {m k T z d : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (hk : 0 < k)
    (hd : d ∣ sievePrimeProduct k z) :
    |(absorberBoundingSieve C hk T z).rem d| ≤
      2 * (k : ℝ) ^ d.primeFactors.card := by
  have hsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd (sievePrimeProduct_squarefree k z)
  rw [BoundingSieve.rem, absorberBoundingSieve_multSum C hk]
  change |((DivisibleAbsorberParameterCandidates C T d).card : ℝ) -
      binomialSieveNu k d *
        (AbsorberParameterCandidates T).card| ≤ _
  rw [binomialSieveNu_squarefree hsq]
  change |((DivisibleAbsorberParameterCandidates C T d).card : ℝ) -
      ((k : ℝ) ^ d.primeFactors.card / d) *
        (AbsorberParameterCandidates T).card| ≤ _
  rw [card_absorberParameterCandidates]
  convert abs_card_divisibleAbsorberParameterCandidates_sub_density C hd
    using 1 <;> ring

/-- Every divisor retained by a level-`L` Brun truncation is at most `z^L`.
This is the elementary support bound behind the qualitative error estimate. -/
theorem divisor_le_pow_of_dvd_sievePrimeProduct {k z d L : ℕ}
    (hz : 1 ≤ z) (hd : d ∣ sievePrimeProduct k z)
    (homega : d.primeFactors.card ≤ L) : d ≤ z ^ L := by
  have hsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd (sievePrimeProduct_squarefree k z)
  calc
    d = ∏ p ∈ d.primeFactors, p :=
      (Nat.prod_primeFactors_of_squarefree hsq).symm
    _ ≤ ∏ _p ∈ d.primeFactors, z := by
      apply Finset.prod_le_prod'
      intro p hp
      have hpPrime := (Nat.mem_primeFactors.mp hp).1
      have hpProd : p ∣ sievePrimeProduct k z :=
        (Nat.dvd_of_mem_primeFactors hp).trans hd
      exact (mem_sievePrimes.mp
        (prime_mem_sievePrimes_of_dvd_product hpPrime hpProd)).2.2.le
    _ = z ^ d.primeFactors.card := by simp
    _ ≤ z ^ L := by gcongr

theorem abs_brunLowerWeight_le_one (L d : ℕ) :
    |brunLowerWeight L d| ≤ 1 := by
  unfold brunLowerWeight
  split_ifs
  · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  · simp

theorem abs_brunUpperWeight_le_one (L d : ℕ) :
    |brunUpperWeight L d| ≤ 1 := by
  unfold brunUpperWeight
  split_ifs
  · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  · simp

/-- The number of sieve divisors retained through level `L` is at most the
number of natural numbers below `z^L + 1`. -/
theorem card_brunSupport_le {k z L : ℕ} (hz : 1 ≤ z) :
    ((sievePrimeProduct k z).divisors.filter fun d =>
      d.primeFactors.card ≤ L).card ≤ z ^ L + 1 := by
  have hsub :
      ((sievePrimeProduct k z).divisors.filter fun d =>
          d.primeFactors.card ≤ L) ⊆ Finset.range (z ^ L + 1) := by
    intro d hdmem
    rw [Finset.mem_filter] at hdmem
    rw [Finset.mem_range]
    have hddiv := (Nat.mem_divisors.mp hdmem.1).1
    have hle := divisor_le_pow_of_dvd_sievePrimeProduct hz hddiv hdmem.2
    omega
  exact (Finset.card_le_card hsub).trans_eq (Finset.card_range _)

/-- Explicit total endpoint-error bound for either Brun truncation. -/
theorem absorberBoundingSieve_brunErrSum_le {m k T z L : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (hk : 0 < k) (hz : 1 ≤ z) :
    (absorberBoundingSieve C hk T z).errSum (brunLowerWeight L) ≤
      (2 : ℝ) * (z ^ L + 1 : ℕ) * (k : ℝ) ^ L := by
  let s := absorberBoundingSieve C hk T z
  rw [BoundingSieve.errSum]
  calc
    (∑ d ∈ (sievePrimeProduct k z).divisors,
        |brunLowerWeight L d| * |s.rem d|) ≤
        ∑ d ∈ (sievePrimeProduct k z).divisors,
          if d.primeFactors.card ≤ L then
            2 * (k : ℝ) ^ L else 0 := by
      apply Finset.sum_le_sum
      intro d hdmem
      by_cases hdL : d.primeFactors.card ≤ L
      · rw [if_pos hdL]
        have hddiv := (Nat.mem_divisors.mp hdmem).1
        have hrem := absorberBoundingSieve_abs_rem_le
          (T := T) C hk hddiv
        calc
          |brunLowerWeight L d| * |s.rem d| ≤ 1 * |s.rem d| := by
            gcongr
            exact abs_brunLowerWeight_le_one L d
          _ ≤ 2 * (k : ℝ) ^ d.primeFactors.card := by simpa using hrem
          _ ≤ 2 * (k : ℝ) ^ L := by
            gcongr
            exact_mod_cast hk
      · rw [if_neg hdL]
        have hzero : brunLowerWeight L d = 0 := by
          unfold brunLowerWeight
          rw [if_neg]
          simpa [cardDistinctFactors_eq_primeFactors_card] using hdL
        simp [hzero]
    _ = (((sievePrimeProduct k z).divisors.filter fun d =>
          d.primeFactors.card ≤ L).card : ℝ) *
          (2 * (k : ℝ) ^ L) := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (z ^ L + 1 : ℕ) * (2 * (k : ℝ) ^ L) := by
      gcongr
      exact_mod_cast card_brunSupport_le (k := k) hz
    _ = (2 : ℝ) * (z ^ L + 1 : ℕ) * (k : ℝ) ^ L := by ring

theorem absorberBoundingSieve_brunUpperErrSum_le {m k T z L : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (hk : 0 < k) (hz : 1 ≤ z) :
    (absorberBoundingSieve C hk T z).errSum (brunUpperWeight L) ≤
      (2 : ℝ) * (z ^ L + 1 : ℕ) * (k : ℝ) ^ L := by
  change (absorberBoundingSieve C hk T z).errSum (brunLowerWeight L) ≤ _
  exact absorberBoundingSieve_brunErrSum_le C hk hz (L := L)

/-- Ready-to-use lower Brun bound for the unconditional fixed absorber
progression. -/
theorem siftedAbsorberParameters_brunLowerBound {m k T z L : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (hk : 0 < k) (hL : Odd L) :
    (absorberBoundingSieve C hk T z).totalMass *
          (absorberBoundingSieve C hk T z).mainSum (brunLowerWeight L) -
        (absorberBoundingSieve C hk T z).errSum (brunLowerWeight L) ≤
      ((SiftedAbsorberParameterCandidates C T z).card : ℝ) := by
  rw [← absorberBoundingSieve_siftedSum C hk]
  exact brunLowerBound (absorberBoundingSieve C hk T z) hL

/-- Matching upper Brun bound for the same progression. -/
theorem siftedAbsorberParameters_brunUpperBound {m k T z L : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (hk : 0 < k) (hL : Even L) :
    ((SiftedAbsorberParameterCandidates C T z).card : ℝ) ≤
      (absorberBoundingSieve C hk T z).totalMass *
          (absorberBoundingSieve C hk T z).mainSum (brunUpperWeight L) +
        (absorberBoundingSieve C hk T z).errSum (brunUpperWeight L) := by
  rw [← absorberBoundingSieve_siftedSum C hk]
  exact brunUpperBound (absorberBoundingSieve C hk T z) hL

/-- Completely explicit lower bound for the number of sifted absorber
parameters.  The first term is half of the finite Euler-product main term;
the second is the elementary CRT endpoint-error bound. -/
theorem siftedAbsorberParameters_card_lowerBound
    {m k T z L : ℕ} (C : CoverBPZ.AbsorberCoverValid m k)
    (hk : 0 < k) (hz : 1 ≤ z) (hL : Odd L)
    (htail :
      2 * brunSubsetTail (sievePrimeProduct k z).primeFactors
          (fun p => binomialSieveNu k p) L ≤
        absorberEulerProduct k z) :
    (absorberBoundingSieve C hk T z).totalMass *
          (absorberEulerProduct k z / 2) -
        (2 : ℝ) * (z ^ L + 1 : ℕ) * (k : ℝ) ^ L ≤
      ((SiftedAbsorberParameterCandidates C T z).card : ℝ) := by
  let s := absorberBoundingSieve C hk T z
  have hwindow := boundingSieve_brunMainSums_half_threeHalves s L htail
  have hbrun := siftedAbsorberParameters_brunLowerBound
    (T := T) (z := z) C hk hL
  have herr := absorberBoundingSieve_brunErrSum_le
    (T := T) C hk hz (L := L)
  have hmass : 0 ≤ s.totalMass := by
    rw [absorberBoundingSieve_totalMass]
    positivity
  have hmain :
      s.totalMass * (absorberEulerProduct k z / 2) ≤
        s.totalMass * s.mainSum (brunLowerWeight L) :=
    mul_le_mul_of_nonneg_left hwindow.1 hmass
  exact le_trans (by linarith) hbrun

/-- Moment-product form of the preceding explicit cardinal lower bound. -/
theorem siftedAbsorberParameters_card_lowerBound_of_moment
    {m k T z L : ℕ} (C : CoverBPZ.AbsorberCoverValid m k)
    (hk : 0 < k) (hz : 1 ≤ z) (hL : Odd L)
    (hmoment :
      2 * (∏ p ∈ (sievePrimeProduct k z).primeFactors,
            (1 + 2 * binomialSieveNu k p)) ≤
        (2 : ℝ) ^ (L + 1) * absorberEulerProduct k z) :
    (absorberBoundingSieve C hk T z).totalMass *
          (absorberEulerProduct k z / 2) -
        (2 : ℝ) * (z ^ L + 1 : ℕ) * (k : ℝ) ^ L ≤
      ((SiftedAbsorberParameterCandidates C T z).card : ℝ) := by
  apply siftedAbsorberParameters_card_lowerBound C hk hz hL
  apply two_mul_brunSubsetTail_le_of_moment
  · intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    rw [binomialSieveNu_prime hpPrime]
    positivity
  · simpa [absorberEulerProduct] using hmoment

/-- A finite positivity criterion separating the two remaining numerical
tasks: control the omitted Brun main-term tail and dominate the summed CRT
endpoint errors by the resulting positive main term. -/
theorem siftedAbsorberParameters_card_pos_of_brun
    {m k T z L : ℕ} (C : CoverBPZ.AbsorberCoverValid m k)
    (hk : 0 < k) (hL : Odd L)
    (htail :
      2 * brunSubsetTail (sievePrimeProduct k z).primeFactors
          (fun p => binomialSieveNu k p) L ≤
        absorberEulerProduct k z)
    (hdom :
      (absorberBoundingSieve C hk T z).errSum (brunLowerWeight L) <
        (absorberBoundingSieve C hk T z).totalMass *
          (absorberEulerProduct k z / 2)) :
    0 < (SiftedAbsorberParameterCandidates C T z).card := by
  let s := absorberBoundingSieve C hk T z
  have hwindow := boundingSieve_brunMainSums_half_threeHalves s L htail
  have hlower := siftedAbsorberParameters_brunLowerBound
    (T := T) (z := z) C hk hL
  have hmass : 0 ≤ s.totalMass := by
    rw [absorberBoundingSieve_totalMass]
    positivity
  have hpositive :
      0 < s.totalMass * s.mainSum (brunLowerWeight L) -
        s.errSum (brunLowerWeight L) := by
    have hmul : s.totalMass * (absorberEulerProduct k z / 2) ≤
        s.totalMass * s.mainSum (brunLowerWeight L) := by
      exact mul_le_mul_of_nonneg_left hwindow.1 hmass
    linarith
  have hreal :
      0 < ((SiftedAbsorberParameterCandidates C T z).card : ℝ) :=
    lt_of_lt_of_le hpositive hlower
  exact_mod_cast hreal

/-- Arbitrarily large sifted parameters from any odd Brun level whose
omitted main-term tail is at most half the Euler product. -/
theorem exists_siftedAbsorberParameter_above_of_brunTail
    {m k z L : ℕ} (C : CoverBPZ.AbsorberCoverValid m k)
    (hk : 0 < k) (hz : 1 ≤ z) (hL : Odd L)
    (htail :
      2 * brunSubsetTail (sievePrimeProduct k z).primeFactors
          (fun p => binomialSieveNu k p) L ≤
        absorberEulerProduct k z)
    (T₀ : ℕ) :
    ∃ t : ℕ, T₀ < t ∧
      Nat.Coprime (sievePrimeProduct k z) ((C.nNat t).choose k) := by
  let V := absorberEulerProduct k z
  let E : ℝ := 2 * (z ^ L + 1 : ℕ) * (k : ℝ) ^ L
  have hV : 0 < V := by
    simpa [V] using absorberEulerProduct_pos C hk (z := z)
  obtain ⟨N, hN⟩ :=
    exists_nat_gt (max (T₀ : ℝ) ((2 * E) / V))
  have hT₀N : T₀ < N := by
    exact_mod_cast lt_of_le_of_lt
      (le_max_left (T₀ : ℝ) ((2 * E) / V)) hN
  have hENV : E < (N : ℝ) * (V / 2) := by
    have hdiv : (2 * E) / V < (N : ℝ) :=
      lt_of_le_of_lt (le_max_right (T₀ : ℝ) ((2 * E) / V)) hN
    have hmul : 2 * E < (N : ℝ) * V := (div_lt_iff₀ hV).mp hdiv
    linarith
  have hbound := siftedAbsorberParameters_card_lowerBound
    (T := 2 * N) C hk hz hL htail
  have hmass :
      (absorberBoundingSieve C hk (2 * N) z).totalMass = (N : ℝ) := by
    rw [absorberBoundingSieve_totalMass]
    norm_num
    omega
  rw [hmass] at hbound
  have hpositive :
      0 < ((SiftedAbsorberParameterCandidates C (2 * N) z).card : ℝ) := by
    apply lt_of_lt_of_le (show 0 < (N : ℝ) * (V / 2) - E by linarith) hbound
  have hcard :
      0 < (SiftedAbsorberParameterCandidates C (2 * N) z).card := by
    exact_mod_cast hpositive
  obtain ⟨t, ht⟩ := Finset.card_pos.mp hcard
  simp only [SiftedAbsorberParameterCandidates, Finset.mem_filter,
    AbsorberParameterCandidates, Finset.mem_Ioc] at ht
  refine ⟨t, hT₀N.trans ?_, ht.2⟩
  omega

/-- The logarithmic-depth elementary Brun estimate already suffices for
arbitrarily large parameters at every fixed threshold. -/
theorem exists_siftedAbsorberParameter_above_elementaryDepth
    {m k z : ℕ} (C : CoverBPZ.AbsorberCoverValid m k)
    (hk : 0 < k) (hz : 1 ≤ z) (T₀ : ℕ) :
    ∃ t : ℕ, T₀ < t ∧
      Nat.Coprime (sievePrimeProduct k z) ((C.nNat t).choose k) := by
  apply exists_siftedAbsorberParameter_above_of_brunTail C hk hz
    (elementaryBrunDepth_odd k z)
    (absorber_brunTail_le_half_elementaryDepth C hk)

/-- Quantitative version: a sifted parameter already occurs in the explicit
dyadic interval based at `elementaryBrunScale`.  Thus the elementary Brun
argument gives a fully finite roughness-versus-size relation, not merely an
unbounded-existence statement. -/
theorem exists_siftedAbsorberParameter_in_elementaryScale
    {m k z : ℕ} (C : CoverBPZ.AbsorberCoverValid m k)
    (hk : 0 < k) (hz : 1 ≤ z) (T₀ : ℕ) :
    ∃ t : ℕ,
      t ∈ Finset.Ioc (elementaryBrunScale T₀ k z)
          (2 * elementaryBrunScale T₀ k z) ∧
      Nat.Coprime (sievePrimeProduct k z) ((C.nNat t).choose k) := by
  let L := elementaryBrunDepth k z
  let E := elementaryBrunEndpointError k z
  let A := elementaryMomentCoefficient k z
  let N := elementaryBrunScale T₀ k z
  let V := absorberEulerProduct k z
  have hV : 0 < V := by
    simpa [V] using absorberEulerProduct_pos C hk (z := z)
  have hrecip : (1 : ℝ) ≤ (A : ℝ) * V := by
    simpa [A, V, elementaryMomentCoefficient, Nat.cast_mul, Nat.cast_pow] using
      one_le_elementaryMajorant_mul_absorberEulerProduct C hk (z := z)
  have hscaleNat : 2 * E * A < N := by
    simp [E, A, N, elementaryBrunScale]
  have hscale : (2 : ℝ) * E * A < N := by exact_mod_cast hscaleNat
  have hEA_nonneg : (0 : ℝ) ≤ 2 * E := by positivity
  have hEV : (2 : ℝ) * E ≤ (2 * E) * (A * V) := by
    simpa using mul_le_mul_of_nonneg_left hrecip hEA_nonneg
  have hscaleV : (2 : ℝ) * E * A * V < (N : ℝ) * V := by
    exact mul_lt_mul_of_pos_right hscale hV
  have hdom : (E : ℝ) < (N : ℝ) * (V / 2) := by
    have htwo : (2 : ℝ) * E < (N : ℝ) * V := by
      apply lt_of_le_of_lt
      · convert hEV using 1 <;> ring
      · simpa [mul_assoc] using hscaleV
    linarith
  have htail := absorber_brunTail_le_half_elementaryDepth C hk (z := z)
  have hbound := siftedAbsorberParameters_card_lowerBound
    (T := 2 * N) C hk hz (elementaryBrunDepth_odd k z) htail
  have hmass :
      (absorberBoundingSieve C hk (2 * N) z).totalMass = (N : ℝ) := by
    rw [absorberBoundingSieve_totalMass]
    norm_num
    omega
  have hEcast :
      (E : ℝ) = (2 : ℝ) * (z ^ L + 1 : ℕ) * (k : ℝ) ^ L := by
    simp [E, L, elementaryBrunEndpointError, Nat.cast_mul, Nat.cast_pow]
  rw [hmass, ← hEcast] at hbound
  have hcardReal :
      0 < ((SiftedAbsorberParameterCandidates C (2 * N) z).card : ℝ) := by
    apply lt_of_lt_of_le (show 0 < (N : ℝ) * (V / 2) - E by linarith) hbound
  have hcardNat :
      0 < (SiftedAbsorberParameterCandidates C (2 * N) z).card := by
    exact_mod_cast hcardReal
  obtain ⟨t, ht⟩ := Finset.card_pos.mp hcardNat
  simp only [SiftedAbsorberParameterCandidates, Finset.mem_filter,
    AbsorberParameterCandidates, Finset.mem_Ioc] at ht
  exact ⟨t, by simpa [N] using ht.1, ht.2⟩

/-- For every fixed roughness threshold, the unconditional absorber
progression contains arbitrarily large parameters whose binomial coefficient
has no prime divisor in `(k,z)`.  This is full finite inclusion--exclusion:
after fixing `z`, its error is constant while the parameter interval grows. -/
theorem exists_siftedAbsorberParameter_above {m k z : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (hk : 0 < k) (hz : 1 ≤ z)
    (T₀ : ℕ) :
    ∃ t : ℕ, T₀ < t ∧
      Nat.Coprime (sievePrimeProduct k z) ((C.nNat t).choose k) := by
  let r := (sievePrimeProduct k z).primeFactors.card
  let L := 2 * r + 1
  let V := absorberEulerProduct k z
  let E : ℝ := 2 * (z ^ L + 1 : ℕ) * (k : ℝ) ^ L
  have hV : 0 < V := by
    simpa [V] using absorberEulerProduct_pos C hk (z := z)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (T₀ : ℝ) (E / V))
  have hT₀N : T₀ < N := by
    exact_mod_cast lt_of_le_of_lt (le_max_left (T₀ : ℝ) (E / V)) hN
  have hENV : E < (N : ℝ) * V := by
    have hdiv : E / V < (N : ℝ) :=
      lt_of_le_of_lt (le_max_right (T₀ : ℝ) (E / V)) hN
    exact (div_lt_iff₀ hV).mp hdiv
  have hLodd : Odd L := by
    refine ⟨r, ?_⟩
    simp [L]
  have hcard : (sievePrimeProduct k z).primeFactors.card ≤ L := by
    dsimp [r, L]
    omega
  let s := absorberBoundingSieve C hk (2 * N) z
  have hmain : s.mainSum (brunLowerWeight L) = V := by
    simpa [s, V] using
      absorberBoundingSieve_mainSum_eq_euler_of_card_le
        (T := 2 * N) C hk hcard
  have hmass : s.totalMass = (N : ℝ) := by
    rw [show s.totalMass = ((2 * N - (2 * N) / 2 : ℕ) : ℝ) by
      simpa [s] using absorberBoundingSieve_totalMass
        (T := 2 * N) (z := z) C hk]
    norm_num
    omega
  have herr : s.errSum (brunLowerWeight L) ≤ E := by
    simpa [s, E] using absorberBoundingSieve_brunErrSum_le
      (T := 2 * N) C hk hz (L := L)
  have hpositive :
      0 < s.totalMass * s.mainSum (brunLowerWeight L) -
        s.errSum (brunLowerWeight L) := by
    rw [hmass, hmain]
    linarith
  have hlower := siftedAbsorberParameters_brunLowerBound
    (T := 2 * N) (z := z) C hk hLodd
  have hcardReal :
      0 < ((SiftedAbsorberParameterCandidates C (2 * N) z).card : ℝ) :=
    lt_of_lt_of_le hpositive hlower
  have hcardNat :
      0 < (SiftedAbsorberParameterCandidates C (2 * N) z).card := by
    exact_mod_cast hcardReal
  obtain ⟨t, ht⟩ := Finset.card_pos.mp hcardNat
  simp only [SiftedAbsorberParameterCandidates, Finset.mem_filter,
    AbsorberParameterCandidates, Finset.mem_Ioc] at ht
  refine ⟨t, hT₀N.trans ?_, ht.2⟩
  omega

end Erdos387
