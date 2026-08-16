/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.QualitativeSieve
import ErdosProblems.Erdos851.ShiftCandidates

/-!
# One- and two-shift interval sieves for Erdős problem 851

This file instantiates Mathlib's `BoundingSieve` on the dyadic interval
`(X, 2X]`.  A point `a` is represented by the product of its shifted
residuals.  For a squarefree divisor `d`, divisibility of that product is a
union of exactly `nuClasses shifts d` residue classes modulo `d`.

The interval has length exactly `X`.  We retain the sharp endpoint estimate
with error at most one per residue class; this is the finite input required
for both the one-shift and two-shift moment sieves.
-/

namespace Erdos851

open scoped BigOperators ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction

namespace ShiftSieve

/-- The distinct residues modulo `p` represented by a finite shift set. -/
def shiftResidues (shifts : Finset ℕ) (p : ℕ) : Finset ℕ :=
  shifts.image fun s ↦ s % p

/-- Number of distinct local bad classes at a modulus. -/
def localNu (shifts : Finset ℕ) (p : ℕ) : ℕ :=
  (shiftResidues shifts p).card

theorem localNu_pos {shifts : Finset ℕ} (hshifts : shifts.Nonempty)
    (p : ℕ) : 0 < localNu shifts p := by
  obtain ⟨s, hs⟩ := hshifts
  exact Finset.card_pos.mpr ⟨s % p, Finset.mem_image.mpr ⟨s, hs, rfl⟩⟩

theorem localNu_le_card (shifts : Finset ℕ) (p : ℕ) :
    localNu shifts p ≤ shifts.card := by
  exact Finset.card_image_le

theorem localNu_singleton (s p : ℕ) : localNu {s} p = 1 := by
  simp [localNu, shiftResidues]

theorem localNu_pair_le_two (s t p : ℕ) : localNu {s, t} p ≤ 2 := by
  exact (localNu_le_card ({s, t} : Finset ℕ) p).trans Finset.card_le_two

theorem localNu_pair_eq_one_iff {s t p : ℕ} :
    localNu {s, t} p = 1 ↔ s % p = t % p := by
  classical
  simp only [localNu, shiftResidues, Finset.image_insert,
    Finset.image_singleton]
  by_cases h : s % p = t % p
  · simp [h]
  · simp [h]

theorem localNu_pair_eq_two_iff {s t p : ℕ} :
    localNu {s, t} p = 2 ↔ s % p ≠ t % p := by
  classical
  simp only [localNu, shiftResidues, Finset.image_insert,
    Finset.image_singleton]
  by_cases h : s % p = t % p
  · simp [h]
  · simp [h]

/-- The number of simultaneous CRT classes for a squarefree modulus. -/
def nuClasses (shifts : Finset ℕ) (d : ℕ) : ℕ :=
  ∏ p ∈ d.primeFactors, localNu shifts p

/-- Multiplicative real local density. -/
noncomputable def shiftNu (shifts : Finset ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors fun p ↦ (localNu shifts p : ℝ) / p

theorem shiftNu_mult (shifts : Finset ℕ) :
    (shiftNu shifts).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

theorem shiftNu_prime {shifts : Finset ℕ} {p : ℕ} (hp : p.Prime) :
    shiftNu shifts p = (localNu shifts p : ℝ) / p := by
  rw [shiftNu, ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero]
  simp [hp]

theorem shiftNu_squarefree {shifts : Finset ℕ} {d : ℕ}
    (hd : Squarefree d) :
    shiftNu shifts d = (nuClasses shifts d : ℝ) / d := by
  rw [shiftNu, ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero,
    Finset.prod_div_distrib]
  unfold nuClasses
  rw [← Nat.cast_prod]
  congr 1
  rw [← Nat.cast_prod]
  norm_cast
  exact Nat.prod_primeFactors_of_squarefree hd

/-- A local choice is one of the distinct shift residues modulo `p`. -/
abbrev LocalChoice (shifts : Finset ℕ) (p : ℕ) :=
  {r : ℕ // r ∈ shiftResidues shifts p}

theorem localChoice_lt {shifts : Finset ℕ} {p : ℕ}
    (hp : 0 < p) (r : LocalChoice shifts p) : (r : ℕ) < p := by
  have hr := r.property
  change (r : ℕ) ∈ shifts.image (fun s ↦ s % p) at hr
  rw [Finset.mem_image] at hr
  obtain ⟨s, _hs, hrs⟩ := hr
  rw [← hrs]
  exact Nat.mod_lt _ hp

/-- CRT representative attached to one allowed local residue at every prime
factor of `d`. -/
noncomputable def assignmentResidue (shifts : Finset ℕ) (d : ℕ)
    (A : (p : ↑d.primeFactors) → LocalChoice shifts p) : ℕ :=
  Nat.chineseRemainderOfFinset
    (fun p : ↑d.primeFactors ↦ (A p : ℕ))
    (fun p : ↑d.primeFactors ↦ (p : ℕ)) Finset.univ
    (by intro p _; exact (Nat.mem_primeFactors.mp p.property).1.ne_zero)
    (by
      intro p _ q _ hpq
      exact Erdos387.primeFactors_pairwise_coprime d p.property q.property
        (fun h ↦ hpq (Subtype.ext h)))

theorem assignmentResidue_mod (shifts : Finset ℕ) (d : ℕ)
    (A : (p : ↑d.primeFactors) → LocalChoice shifts p)
    (p : ↑d.primeFactors) :
    assignmentResidue shifts d A ≡ (A p : ℕ) [MOD (p : ℕ)] := by
  exact (Nat.chineseRemainderOfFinset
    (fun p : ↑d.primeFactors ↦ (A p : ℕ))
    (fun p : ↑d.primeFactors ↦ (p : ℕ)) Finset.univ
    (by intro p _; exact (Nat.mem_primeFactors.mp p.property).1.ne_zero)
    (by
      intro p _ q _ hpq
      exact Erdos387.primeFactors_pairwise_coprime d p.property q.property
        (fun h ↦ hpq (Subtype.ext h)))).prop p (Finset.mem_univ p)

theorem assignmentResidue_injective (shifts : Finset ℕ) (d : ℕ) :
    Function.Injective (assignmentResidue shifts d) := by
  intro A B hAB
  funext p
  apply Subtype.ext
  have hA := assignmentResidue_mod shifts d A p
  have hB := assignmentResidue_mod shifts d B p
  have hp : 0 < (p : ℕ) := (Nat.mem_primeFactors.mp p.property).1.pos
  have hAlt := Nat.mod_eq_of_modEq hA (localChoice_lt hp (A p))
  have hBlt := Nat.mod_eq_of_modEq hB (localChoice_lt hp (B p))
  rw [hAB] at hAlt
  omega

/-- The finite set of simultaneous shifted residue classes modulo `d`. -/
noncomputable def assignmentResidues (shifts : Finset ℕ) (d : ℕ) :
    Finset ℕ := by
  classical
  exact Finset.univ.image (assignmentResidue shifts d)

theorem card_assignmentResidues (shifts : Finset ℕ) (d : ℕ) :
    (assignmentResidues shifts d).card = nuClasses shifts d := by
  classical
  rw [assignmentResidues, Finset.card_image_of_injective _
    (assignmentResidue_injective shifts d), Finset.card_univ,
    Fintype.card_pi]
  unfold nuClasses localNu
  rw [Finset.univ_eq_attach]
  simp only [Fintype.card_coe]
  exact Finset.prod_attach d.primeFactors
    (fun p ↦ (shiftResidues shifts p).card)

theorem assignmentResidue_lt {shifts : Finset ℕ} {d : ℕ}
    (hd : Squarefree d)
    (A : (p : ↑d.primeFactors) → LocalChoice shifts p) :
    assignmentResidue shifts d A < d := by
  have hlt :=
    Nat.chineseRemainderOfFinset_lt_prod
      (fun p : ↑d.primeFactors ↦ (A p : ℕ))
      (fun p : ↑d.primeFactors ↦ (p : ℕ)) (t := Finset.univ)
      (by intro p _; exact (Nat.mem_primeFactors.mp p.property).1.ne_zero)
      (by
        intro p _ q _ hpq
        exact Erdos387.primeFactors_pairwise_coprime d p.property q.property
          (fun h ↦ hpq (Subtype.ext h)))
  calc
    assignmentResidue shifts d A < ∏ p : ↑d.primeFactors, (p : ℕ) := by
      simpa [assignmentResidue] using hlt
    _ = ∏ p ∈ d.primeFactors, p := by
      simpa using Finset.prod_attach d.primeFactors (fun p : ℕ ↦ p)
    _ = d := Nat.prod_primeFactors_of_squarefree hd

theorem assignmentResidues_lt {shifts : Finset ℕ} {d : ℕ}
    (hd : Squarefree d) {r : ℕ} (hr : r ∈ assignmentResidues shifts d) :
    r < d := by
  classical
  rw [assignmentResidues, Finset.mem_image] at hr
  obtain ⟨A, _hA, rfl⟩ := hr
  exact assignmentResidue_lt hd A

/-- For a squarefree modulus, the number of simultaneous bad residue
classes is at most the modulus itself. -/
theorem nuClasses_le {shifts : Finset ℕ} {d : ℕ}
    (hd : Squarefree d) : nuClasses shifts d ≤ d := by
  rw [← card_assignmentResidues]
  simpa only [Finset.card_range] using
    Finset.card_le_card (show assignmentResidues shifts d ⊆ Finset.range d by
      intro r hr
      exact Finset.mem_range.mpr (assignmentResidues_lt hd hr))

/-- A prime divides the product of shifted residuals exactly when the point
lies in one of the corresponding residue classes. -/
theorem prime_dvd_shiftedProduct_iff {shifts : Finset ℕ} {a p : ℕ}
    (hp : p.Prime) (hsa : ∀ s ∈ shifts, s ≤ a) :
    p ∣ shiftedProduct shifts a ↔ ∃ s ∈ shifts, a % p = s % p := by
  rw [shiftedProduct, Erdos387.prime_dvd_finset_prod_iff hp]
  constructor
  · rintro ⟨s, hs, hdiv⟩
    have hmod : s ≡ a [MOD p] :=
      (Nat.modEq_iff_dvd' (hsa s hs)).mpr hdiv
    exact ⟨s, hs, hmod.symm⟩
  · rintro ⟨s, hs, hmod⟩
    refine ⟨s, hs, ?_⟩
    exact (Nat.modEq_iff_dvd' (hsa s hs)).mp hmod.symm

/-- Squarefree divisibility by the shifted product is membership in the
explicit set of simultaneous CRT classes. -/
theorem squarefree_dvd_shiftedProduct_iff_mod_mem
    {shifts : Finset ℕ} {a d : ℕ} (hd : Squarefree d)
    (hsa : ∀ s ∈ shifts, s ≤ a) :
    d ∣ shiftedProduct shifts a ↔
      a % d ∈ assignmentResidues shifts d := by
  classical
  constructor
  · intro hdiv
    have hlocal : ∀ p : ↑d.primeFactors,
        a % (p : ℕ) ∈ shiftResidues shifts p := by
      intro p
      have hpPrime := (Nat.mem_primeFactors.mp p.property).1
      have hpDiv : (p : ℕ) ∣ shiftedProduct shifts a :=
        (Nat.dvd_of_mem_primeFactors p.property).trans hdiv
      obtain ⟨s, hs, has⟩ :=
        (prime_dvd_shiftedProduct_iff hpPrime hsa).mp hpDiv
      exact Finset.mem_image.mpr ⟨s, hs, has.symm⟩
    let A : (p : ↑d.primeFactors) → LocalChoice shifts p :=
      fun p ↦ ⟨a % (p : ℕ), hlocal p⟩
    have hmod : a ≡ assignmentResidue shifts d A [MOD d] := by
      have hmod' :
          a ≡ assignmentResidue shifts d A
            [MOD ∏ p ∈ d.primeFactors, p] := by
        rw [Erdos387.modEq_prod_primeFactors_iff]
        intro p hp
        let p' : ↑d.primeFactors := ⟨p, hp⟩
        exact (Nat.mod_modEq a p).symm.trans
          (assignmentResidue_mod shifts d A p').symm
      simpa only [Nat.prod_primeFactors_of_squarefree hd] using hmod'
    have heq : a % d = assignmentResidue shifts d A :=
      Nat.mod_eq_of_modEq hmod (assignmentResidue_lt hd A)
    rw [assignmentResidues, Finset.mem_image]
    exact ⟨A, Finset.mem_univ A, heq.symm⟩
  · intro hmem
    rw [assignmentResidues, Finset.mem_image] at hmem
    obtain ⟨A, _hA, hAeq⟩ := hmem
    apply (Erdos387.squarefree_dvd_iff_primeFactors_dvd hd).mpr
    intro p hp
    have hpPrime := (Nat.mem_primeFactors.mp hp).1
    let p' : ↑d.primeFactors := ⟨p, hp⟩
    have hmodD : a ≡ assignmentResidue shifts d A [MOD d] := by
      change a % d = assignmentResidue shifts d A % d
      rw [Nat.mod_eq_of_lt (assignmentResidue_lt hd A)]
      exact hAeq.symm
    have hmodP : a ≡ (A p' : ℕ) [MOD p] :=
      (hmodD.of_dvd (Nat.dvd_of_mem_primeFactors hp)).trans
        (assignmentResidue_mod shifts d A p')
    have hp' := (A p').property
    change (A p' : ℕ) ∈ shifts.image (fun s ↦ s % p) at hp'
    rw [Finset.mem_image] at hp'
    obtain ⟨s, hs, hsA⟩ := hp'
    apply (prime_dvd_shiftedProduct_iff hpPrime hsa).mpr
    refine ⟨s, hs, ?_⟩
    have hAltp : (A p' : ℕ) < p :=
      localChoice_lt hpPrime.pos (A p')
    have hsmod : s % p = (A p' : ℕ) := by
      exact hsA
    exact (Nat.mod_eq_of_modEq hmodP hAltp).trans hsmod.symm

/-! ### A sharp interval-counting lemma -/

/-- Translate canonical residues by `-c` in `ZMod d`, returning their
canonical natural representatives. -/
noncomputable def translatedResidues (c d : ℕ) (A : Finset ℕ) :
    Finset ℕ := by
  classical
  exact (A.image fun r : ℕ ↦ (r : ZMod d) - (c : ZMod d)).image ZMod.val

theorem card_translatedResidues {c d : ℕ} {A : Finset ℕ}
    (hA : ∀ r ∈ A, r < d) :
    (translatedResidues c d A).card = A.card := by
  classical
  by_cases hd : d = 0
  · subst d
    have hAempty : A = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨r, hr⟩
      exact (Nat.not_lt_zero r) (hA r hr)
    simp [hAempty, translatedResidues]
  · letI : NeZero d := ⟨hd⟩
    rw [translatedResidues]
    rw [Finset.card_image_of_injOn]
    · rw [Finset.card_image_of_injOn]
      intro r hr s hs hrs
      have hrs' : (r : ZMod d) = (s : ZMod d) := sub_left_inj.mp hrs
      have hv := congrArg ZMod.val hrs'
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (hA r hr),
        Nat.mod_eq_of_lt (hA s hs)] using hv
    · intro r hr s hs hrs
      apply ZMod.val_injective
      exact hrs

theorem translatedResidues_lt {c d : ℕ} (hd : 0 < d)
    {A : Finset ℕ} {r : ℕ} (hr : r ∈ translatedResidues c d A) :
    r < d := by
  classical
  letI : NeZero d := ⟨hd.ne'⟩
  rw [translatedResidues, Finset.mem_image] at hr
  obtain ⟨x, _hx, rfl⟩ := hr
  exact ZMod.val_lt x

theorem mod_mem_translatedResidues_iff {c d t : ℕ} (hd : 0 < d)
    {A : Finset ℕ} (hA : ∀ r ∈ A, r < d) :
    t % d ∈ translatedResidues c d A ↔ (c + t) % d ∈ A := by
  classical
  letI : NeZero d := ⟨hd.ne'⟩
  constructor
  · intro ht
    rw [translatedResidues, Finset.mem_image] at ht
    obtain ⟨x, hx, hxt⟩ := ht
    rw [Finset.mem_image] at hx
    obtain ⟨r, hr, hrx⟩ := hx
    subst x
    have hcast : (t : ZMod d) = (r : ZMod d) - (c : ZMod d) := by
      rw [← ZMod.natCast_zmod_val
        ((r : ZMod d) - (c : ZMod d)), hxt]
      simp
    have hsum : ((c + t : ℕ) : ZMod d) = (r : ZMod d) := by
      push_cast
      rw [hcast]
      ring
    have hmod := (ZMod.natCast_eq_natCast_iff (c + t) r d).mp hsum
    have hreduced : (c + t) % d = r := by
      simpa [Nat.ModEq, Nat.mod_eq_of_lt (hA r hr)] using hmod
    simpa [hreduced] using hr
  · intro hct
    let r := (c + t) % d
    have hr : r ∈ A := hct
    have hrlt : r < d := Nat.mod_lt _ hd
    rw [translatedResidues, Finset.mem_image]
    refine ⟨(r : ZMod d) - (c : ZMod d), ?_, ?_⟩
    · rw [Finset.mem_image]
      exact ⟨r, hr, rfl⟩
    · have hcastR : (r : ZMod d) = c + t := by
        dsimp [r]
        simp
      have hz : ((r : ZMod d) - (c : ZMod d)) = (t : ZMod d) := by
        rw [hcastR]
        ring
      simpa only [hz, ZMod.val_natCast]

/-- Translation by `X+1` identifies `(X,2X]` with an initial interval of
length `X`, while rotating the selected residue classes. -/
theorem card_modularPreimageIoc_dyadic_eq
    {X d : ℕ} (hd : 0 < d) (A : Finset ℕ)
    (hA : ∀ r ∈ A, r < d) :
    (Erdos387.modularPreimageIoc X (2 * X) d A).card =
      (Erdos387.modularPreimage X d
        (translatedResidues (X + 1) d A)).card := by
  classical
  apply Finset.card_bij (fun a _ ↦ a - (X + 1))
  · intro a ha
    rw [Erdos387.modularPreimageIoc, Finset.mem_filter,
      Finset.mem_Ioc] at ha
    rw [Erdos387.modularPreimage, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · rw [mod_mem_translatedResidues_iff hd hA]
      have haLower : X + 1 ≤ a := by omega
      rw [Nat.add_sub_of_le haLower]
      exact ha.2
  · intro a ha b hb hab
    rw [Erdos387.modularPreimageIoc, Finset.mem_filter,
      Finset.mem_Ioc] at ha hb
    omega
  · intro t ht
    rw [Erdos387.modularPreimage, Finset.mem_filter] at ht
    refine ⟨X + 1 + t, ?_, ?_⟩
    · rw [Erdos387.modularPreimageIoc, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_Ioc]
        rw [Finset.mem_range] at ht
        omega
      · exact (mod_mem_translatedResidues_iff hd hA).mp ht.2
    · omega

/-- A union of canonical residue classes in `(X,2X]` differs from its exact
density main term by at most one point per class. -/
theorem abs_card_modularPreimageIoc_dyadic_sub_density
    {X d : ℕ} (hd : 0 < d) (A : Finset ℕ)
    (hA : ∀ r ∈ A, r < d) :
    |↑(Erdos387.modularPreimageIoc X (2 * X) d A).card -
        (A.card : ℝ) * X / d| ≤ A.card := by
  rw [card_modularPreimageIoc_dyadic_eq hd A hA,
    ← card_translatedResidues hA]
  exact Erdos387.abs_card_modularPreimage_sub_density hd _
    (fun r hr ↦ translatedResidues_lt hd hr)

/-! ### `BoundingSieve` specialization -/

/-- Points in the dyadic interval for which a sieve divisor divides the
product of shifted residuals. -/
def divisibleShiftCandidates (shifts : Finset ℕ) (X d : ℕ) : Finset ℕ :=
  (Finset.Ioc X (2 * X)).filter fun a ↦ d ∣ shiftedProduct shifts a

/-- The interval sieve attached to at most two shifted residuals.  Fiber
weights avoid any injectivity requirement for the product map. -/
noncomputable def boundingSieve (shifts : Finset ℕ)
    (hshifts : shifts.Nonempty) (hcard : shifts.card ≤ 2)
    (X z Y : ℕ) (hz : 2 ≤ z) : BoundingSieve := by
  classical
  let I := Finset.Ioc X (2 * X)
  exact
    { support := I.image (shiftedProduct shifts)
      prodPrimes := Erdos387.sievePrimeProduct z Y
      prodPrimes_squarefree := Erdos387.sievePrimeProduct_squarefree z Y
      weights := fun q ↦
        ((I.filter fun a ↦ shiftedProduct shifts a = q).card : ℝ)
      weights_nonneg := fun _ ↦ by positivity
      totalMass := X
      nu := shiftNu shifts
      nu_mult := shiftNu_mult shifts
      nu_pos_of_prime := by
        intro p hp _hpDiv
        rw [shiftNu_prime hp]
        exact div_pos (by exact_mod_cast localNu_pos hshifts p)
          (by exact_mod_cast hp.pos)
      nu_lt_one_of_prime := by
        intro p hp hpDiv
        rw [shiftNu_prime hp]
        have hpMem := Erdos387.prime_mem_sievePrimes_of_dvd_product hp hpDiv
        have hzp : z < p := (Erdos387.mem_sievePrimes.mp hpMem).2.1
        have hlocal : localNu shifts p < p :=
          (localNu_le_card shifts p).trans_lt
            (hcard.trans_lt (hz.trans_lt hzp))
        exact (div_lt_one (by exact_mod_cast hp.pos)).mpr
          (by exact_mod_cast hlocal) }

theorem boundingSieve_totalMass {shifts : Finset ℕ}
    {hshifts : shifts.Nonempty} {hcard : shifts.card ≤ 2}
    {X z Y : ℕ} {hz : 2 ≤ z} :
    (boundingSieve shifts hshifts hcard X z Y hz).totalMass = X := rfl

/-- The abstract multiple sum is exactly the cardinality of the corresponding
divisibility subset of `(X,2X]`. -/
theorem boundingSieve_multSum {shifts : Finset ℕ}
    {hshifts : shifts.Nonempty} {hcard : shifts.card ≤ 2}
    {X z Y d : ℕ} {hz : 2 ≤ z} :
    (boundingSieve shifts hshifts hcard X z Y hz).multSum d =
      ((divisibleShiftCandidates shifts X d).card : ℝ) := by
  classical
  let I := Finset.Ioc X (2 * X)
  let f := shiftedProduct shifts
  rw [BoundingSieve.multSum]
  change (∑ q ∈ I.image f,
      if d ∣ q then ((I.filter fun a ↦ f a = q).card : ℝ) else 0) = _
  simp_rw [← Finset.sum_filter]
  have hcount :
      (∑ q ∈ (I.image f).filter fun q ↦ d ∣ q,
          (I.filter fun a ↦ f a = q).card) =
        (I.filter fun a ↦ d ∣ f a).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcount]
  norm_cast

/-- The weighted sifted sum is exactly the number of interval points for
which every shifted residual avoids all sieving primes. -/
theorem boundingSieve_siftedSum {shifts : Finset ℕ}
    {hshifts : shifts.Nonempty} {hcard : shifts.card ≤ 2}
    {X z Y : ℕ} {hz : 2 ≤ z} :
    (boundingSieve shifts hshifts hcard X z Y hz).siftedSum =
      ((siftedShiftCandidates shifts X z Y).card : ℝ) := by
  classical
  let I := Finset.Ioc X (2 * X)
  let f := shiftedProduct shifts
  rw [BoundingSieve.siftedSum]
  change (∑ q ∈ I.image f,
      if Nat.Coprime (Erdos387.sievePrimeProduct z Y) q then
        ((I.filter fun a ↦ f a = q).card : ℝ) else 0) = _
  simp_rw [← Finset.sum_filter]
  have hcount :
      (∑ q ∈ (I.image f).filter fun q ↦
          Nat.Coprime (Erdos387.sievePrimeProduct z Y) q,
          (I.filter fun a ↦ f a = q).card) =
        (I.filter fun a ↦
          Nat.Coprime (Erdos387.sievePrimeProduct z Y) (f a)).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcount]
  norm_cast

/-- Exact CRT interpretation of the multiple subset. -/
theorem divisibleShiftCandidates_eq_modularPreimage
    {shifts : Finset ℕ} {X z Y d : ℕ}
    (hshiftX : ∀ s ∈ shifts, s ≤ X)
    (hd : d ∣ Erdos387.sievePrimeProduct z Y) :
    divisibleShiftCandidates shifts X d =
      Erdos387.modularPreimageIoc X (2 * X) d
        (assignmentResidues shifts d) := by
  classical
  have hsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd
      (Erdos387.sievePrimeProduct_squarefree z Y)
  ext a
  simp only [divisibleShiftCandidates, Erdos387.modularPreimageIoc,
    Finset.mem_filter, Finset.mem_Ioc]
  refine and_congr_right fun ha ↦ ?_
  apply squarefree_dvd_shiftedProduct_iff_mod_mem hsq
  intro s hs
  exact (hshiftX s hs).trans ha.1.le

/-- The interval multiple count has the expected local-density main term and
sharp error: at most one point per simultaneous CRT class. -/
theorem abs_card_divisibleShiftCandidates_sub_density
    {shifts : Finset ℕ} {X z Y d : ℕ}
    (hshiftX : ∀ s ∈ shifts, s ≤ X)
    (hd : d ∣ Erdos387.sievePrimeProduct z Y) :
    |↑(divisibleShiftCandidates shifts X d).card -
        (nuClasses shifts d : ℝ) * X / d| ≤ nuClasses shifts d := by
  have hsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd
      (Erdos387.sievePrimeProduct_squarefree z Y)
  have hdPos : 0 < d := Erdos387.pos_of_dvd_sievePrimeProduct hd
  rw [divisibleShiftCandidates_eq_modularPreimage hshiftX hd,
    ← card_assignmentResidues shifts d]
  exact abs_card_modularPreimageIoc_dyadic_sub_density hdPos _
    (fun _r hr ↦ assignmentResidues_lt hsq hr)

/-- The `BoundingSieve` remainder is exactly the endpoint discrepancy and is
bounded by the number of simultaneous bad classes. -/
theorem boundingSieve_abs_rem_le_nuClasses
    {shifts : Finset ℕ} {hshifts : shifts.Nonempty}
    {hcard : shifts.card ≤ 2} {X z Y d : ℕ} {hz : 2 ≤ z}
    (hshiftX : ∀ s ∈ shifts, s ≤ X)
    (hd : d ∣ Erdos387.sievePrimeProduct z Y) :
    |(boundingSieve shifts hshifts hcard X z Y hz).rem d| ≤
      nuClasses shifts d := by
  have hsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd
      (Erdos387.sievePrimeProduct_squarefree z Y)
  rw [BoundingSieve.rem, boundingSieve_multSum,
    boundingSieve_totalMass]
  change
    |↑(divisibleShiftCandidates shifts X d).card -
        shiftNu shifts d * (X : ℝ)| ≤ (nuClasses shifts d : ℝ)
  rw [shiftNu_squarefree hsq]
  simpa [mul_div_assoc, mul_comm, mul_left_comm] using
    abs_card_divisibleShiftCandidates_sub_density hshiftX hd

/-- The requested exact decomposition of the multiple sum into its main term
and explicit bounded remainder. -/
theorem boundingSieve_multSum_eq_main_add_rem
    {shifts : Finset ℕ} {hshifts : shifts.Nonempty}
    {hcard : shifts.card ≤ 2} {X z Y d : ℕ} {hz : 2 ≤ z}
    (hd : d ∣ Erdos387.sievePrimeProduct z Y) :
    (boundingSieve shifts hshifts hcard X z Y hz).multSum d =
      (X : ℝ) * (nuClasses shifts d : ℝ) / d +
        (boundingSieve shifts hshifts hcard X z Y hz).rem d := by
  have hsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd
      (Erdos387.sievePrimeProduct_squarefree z Y)
  rw [BoundingSieve.rem]
  change _ = _ + (_ - shiftNu shifts d * X)
  rw [shiftNu_squarefree hsq]
  ring

/-! ### Named one- and two-shift constructors -/

noncomputable def oneShiftBoundingSieve
    (s X z Y : ℕ) (hz : 2 ≤ z) : BoundingSieve :=
  boundingSieve {s} (by simp) (by simp) X z Y hz

noncomputable def twoShiftBoundingSieve
    (s t X z Y : ℕ) (hz : 2 ≤ z) : BoundingSieve :=
  boundingSieve {s, t} (by simp) Finset.card_le_two X z Y hz

theorem oneShiftBoundingSieve_abs_rem_le_one
    {s X z Y d : ℕ} {hz : 2 ≤ z} (hsX : s ≤ X)
    (hd : d ∣ Erdos387.sievePrimeProduct z Y) :
    |(oneShiftBoundingSieve s X z Y hz).rem d| ≤ 1 := by
  simpa [oneShiftBoundingSieve, nuClasses, localNu_singleton] using
    boundingSieve_abs_rem_le_nuClasses
      (shifts := ({s} : Finset ℕ)) (X := X) (z := z) (Y := Y)
      (d := d) (fun q hq ↦ by
        simp only [Finset.mem_singleton] at hq
        subst q
        exact hsX) hd

theorem twoShiftBoundingSieve_abs_rem_le_nuClasses
    {s t X z Y d : ℕ} {hz : 2 ≤ z}
    (hsX : s ≤ X) (htX : t ≤ X)
    (hd : d ∣ Erdos387.sievePrimeProduct z Y) :
    |(twoShiftBoundingSieve s t X z Y hz).rem d| ≤
      nuClasses {s, t} d := by
  simpa [twoShiftBoundingSieve] using
    boundingSieve_abs_rem_le_nuClasses
      (shifts := ({s, t} : Finset ℕ)) (X := X) (z := z) (Y := Y)
      (d := d) (by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl
        · exact hsX
        · exact htX) hd

theorem oneShiftBoundingSieve_siftedSum
    {s X z Y : ℕ} {hz : 2 ≤ z} :
    (oneShiftBoundingSieve s X z Y hz).siftedSum =
      ((siftedShiftCandidates {s} X z Y).card : ℝ) := by
  simpa [oneShiftBoundingSieve] using
    (boundingSieve_siftedSum
      (shifts := ({s} : Finset ℕ)) (X := X) (z := z) (Y := Y))

theorem twoShiftBoundingSieve_siftedSum
    {s t X z Y : ℕ} {hz : 2 ≤ z} :
    (twoShiftBoundingSieve s t X z Y hz).siftedSum =
      ((siftedShiftCandidates {s, t} X z Y).card : ℝ) := by
  simpa [twoShiftBoundingSieve] using
    (boundingSieve_siftedSum
      (shifts := ({s, t} : Finset ℕ)) (X := X) (z := z) (Y := Y))

/-! ### Finite lower- and upper-sieve cardinality interfaces -/

/-- The abstract error sum of any lower weight is controlled by the explicit
number of simultaneous CRT classes.  This is the finite error estimate used
when a Rosser or beta-sieve weight is installed. -/
theorem boundingSieve_errSum_le_nuClasses
    {shifts : Finset ℕ} {hshifts : shifts.Nonempty}
    {hcard : shifts.card ≤ 2} {X z Y : ℕ} {hz : 2 ≤ z}
    (hshiftX : ∀ s ∈ shifts, s ≤ X) (mu : ℕ → ℝ) :
    (boundingSieve shifts hshifts hcard X z Y hz).errSum mu ≤
      ∑ d ∈ (Erdos387.sievePrimeProduct z Y).divisors,
        |mu d| * nuClasses shifts d := by
  rw [BoundingSieve.errSum]
  apply Finset.sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left
    (boundingSieve_abs_rem_le_nuClasses hshiftX
      (Nat.mem_divisors.mp hd).1)
    (abs_nonneg (mu d))

/-- Finite lower-sieve application to the actual cardinality of the sifted
dyadic candidate set.  Once a combinatorial lower weight has been certified
by `IsLowerMoebiusOnProdPrimes`, its main term and the explicit CRT error
bound give this cardinal estimate with no asymptotic passage. -/
theorem boundingSieve_lower_cardinality_bound
    {shifts : Finset ℕ} {hshifts : shifts.Nonempty}
    {hcard : shifts.card ≤ 2} {X z Y : ℕ} {hz : 2 ≤ z}
    (hshiftX : ∀ s ∈ shifts, s ≤ X) (muMinus : ℕ → ℝ)
    (hmu : BoundingSieve.IsLowerMoebiusOnProdPrimes
      (s := boundingSieve shifts hshifts hcard X z Y hz) muMinus) :
    (X : ℝ) *
          (boundingSieve shifts hshifts hcard X z Y hz).mainSum muMinus -
        ∑ d ∈ (Erdos387.sievePrimeProduct z Y).divisors,
          |muMinus d| * nuClasses shifts d ≤
      ((siftedShiftCandidates shifts X z Y).card : ℝ) := by
  let sieve := boundingSieve shifts hshifts hcard X z Y hz
  have herr := boundingSieve_errSum_le_nuClasses
    (shifts := shifts) (hshifts := hshifts) (hcard := hcard)
    (X := X) (z := z) (Y := Y) (hz := hz) hshiftX muMinus
  calc
    (X : ℝ) * sieve.mainSum muMinus -
          ∑ d ∈ (Erdos387.sievePrimeProduct z Y).divisors,
            |muMinus d| * nuClasses shifts d ≤
        sieve.totalMass * sieve.mainSum muMinus - sieve.errSum muMinus := by
      rw [show sieve.totalMass = (X : ℝ) by
        exact boundingSieve_totalMass]
      linarith
    _ ≤ sieve.siftedSum :=
      sieve.totalMass_mainSum_sub_errSum_le_siftedSum muMinus hmu
    _ = ((siftedShiftCandidates shifts X z Y).card : ℝ) := by
      exact boundingSieve_siftedSum

/-- Finite upper-sieve application to the actual cardinality of the sifted
dyadic candidate set.  This is the form used for the two-shift second moment:
an upper Möbius weight contributes its main sum plus the same explicit CRT
error bound. -/
theorem boundingSieve_upper_cardinality_bound
    {shifts : Finset ℕ} {hshifts : shifts.Nonempty}
    {hcard : shifts.card ≤ 2} {X z Y : ℕ} {hz : 2 ≤ z}
    (hshiftX : ∀ s ∈ shifts, s ≤ X) (muPlus : ℕ → ℝ)
    (hmu : BoundingSieve.IsUpperMoebiusOnProdPrimes
      (s := boundingSieve shifts hshifts hcard X z Y hz) muPlus) :
    ((siftedShiftCandidates shifts X z Y).card : ℝ) ≤
      (X : ℝ) *
          (boundingSieve shifts hshifts hcard X z Y hz).mainSum muPlus +
        ∑ d ∈ (Erdos387.sievePrimeProduct z Y).divisors,
          |muPlus d| * nuClasses shifts d := by
  let sieve := boundingSieve shifts hshifts hcard X z Y hz
  have herr := boundingSieve_errSum_le_nuClasses
    (shifts := shifts) (hshifts := hshifts) (hcard := hcard)
    (X := X) (z := z) (Y := Y) (hz := hz) hshiftX muPlus
  calc
    ((siftedShiftCandidates shifts X z Y).card : ℝ) =
        sieve.siftedSum := by
      exact boundingSieve_siftedSum.symm
    _ ≤ sieve.totalMass * sieve.mainSum muPlus + sieve.errSum muPlus :=
      sieve.siftedSum_le_totalMass_mainSum_add_errSum muPlus hmu
    _ ≤ (X : ℝ) * sieve.mainSum muPlus +
          ∑ d ∈ (Erdos387.sievePrimeProduct z Y).divisors,
            |muPlus d| * nuClasses shifts d := by
      rw [show sieve.totalMass = (X : ℝ) by
        exact boundingSieve_totalMass]
      linarith

end ShiftSieve

end Erdos851
