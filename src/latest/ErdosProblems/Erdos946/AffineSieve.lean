/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos822.AffineSieve
import ErdosProblems.Erdos851.SieveSpecialization

/-!
# The finite sieve datum for eight affine forms

This file contains the elementary local part of the weighted sieve used for
Erdős 946.  It deliberately makes no asymptotic assertion: it identifies the
bad residue classes modulo every squarefree sieve divisor, proves their CRT
multiplicativity, and packages the dyadic interval as a `BoundingSieve` with
the sharp endpoint error (one point per bad residue class).
-/

open scoped BigOperators ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction

namespace Erdos946.AffineSieve

noncomputable section

/-- Product of a finite family of positive affine forms. -/
def affineProduct {ι : Type*} [Fintype ι]
    (a b : ι → ℕ) (n : ℕ) : ℕ :=
  ∏ i, (a i * n + b i)

/-- Residue classes modulo `d` on which the affine product vanishes. -/
def affineResidues {ι : Type*} [Fintype ι]
    (a b : ι → ℕ) (d : ℕ) : Finset ℕ :=
  (Finset.range d).filter fun r ↦ d ∣ affineProduct a b r

@[simp] theorem mem_affineResidues {ι : Type*} [Fintype ι]
    {a b : ι → ℕ} {d r : ℕ} :
    r ∈ affineResidues a b d ↔ r < d ∧ d ∣ affineProduct a b r := by
  simp [affineResidues]

theorem affineResidues_lt {ι : Type*} [Fintype ι]
    {a b : ι → ℕ} {d r : ℕ} (hr : r ∈ affineResidues a b d) : r < d :=
  (mem_affineResidues.mp hr).1

/-- Number of roots modulo a prime (the definition is useful for all
moduli, although only prime values enter the Euler product). -/
def localNu {ι : Type*} [Fintype ι]
    (a b : ι → ℕ) (p : ℕ) : ℕ :=
  (affineResidues a b p).card

/-- Product of local root counts over the prime factors of `d`. -/
def nuClasses {ι : Type*} [Fintype ι]
    (a b : ι → ℕ) (d : ℕ) : ℕ :=
  ∏ p ∈ d.primeFactors, localNu a b p

/-- Multiplicative density of the bad residue classes. -/
noncomputable def affineNu {ι : Type*} [Fintype ι]
    (a b : ι → ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors fun p ↦ (localNu a b p : ℝ) / p

theorem affineNu_mult {ι : Type*} [Fintype ι] (a b : ι → ℕ) :
    (affineNu a b).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

theorem affineNu_prime {ι : Type*} [Fintype ι]
    {a b : ι → ℕ} {p : ℕ} (hp : p.Prime) :
    affineNu a b p = (localNu a b p : ℝ) / p := by
  rw [affineNu, ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero]
  simp [hp]

theorem affineNu_squarefree {ι : Type*} [Fintype ι]
    {a b : ι → ℕ} {d : ℕ} (hd : Squarefree d) :
    affineNu a b d = (nuClasses a b d : ℝ) / d := by
  rw [affineNu, ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero,
    Finset.prod_div_distrib]
  unfold nuClasses
  rw [← Nat.cast_prod]
  congr 1
  rw [← Nat.cast_prod]
  norm_cast
  exact Nat.prod_primeFactors_of_squarefree hd

/-- One bad class at a prime factor of `d`. -/
abbrev LocalChoice {ι : Type*} [Fintype ι]
    (a b : ι → ℕ) (p : ℕ) :=
  {r : ℕ // r ∈ affineResidues a b p}

theorem localChoice_lt {ι : Type*} [Fintype ι]
    {a b : ι → ℕ} {p : ℕ} (r : LocalChoice a b p) : (r : ℕ) < p :=
  affineResidues_lt r.property

/-- CRT representative attached to one bad class at every prime factor. -/
noncomputable def assignmentResidue {ι : Type*} [Fintype ι]
    (a b : ι → ℕ) (d : ℕ)
    (C : (p : ↑d.primeFactors) → LocalChoice a b p) : ℕ :=
  Nat.chineseRemainderOfFinset
    (fun p : ↑d.primeFactors ↦ (C p : ℕ))
    (fun p : ↑d.primeFactors ↦ (p : ℕ)) Finset.univ
    (by intro p _; exact (Nat.mem_primeFactors.mp p.property).1.ne_zero)
    (by
      intro p _ q _ hpq
      exact Erdos387.primeFactors_pairwise_coprime d p.property q.property
        (fun h ↦ hpq (Subtype.ext h)))

theorem assignmentResidue_mod {ι : Type*} [Fintype ι]
    (a b : ι → ℕ) (d : ℕ)
    (C : (p : ↑d.primeFactors) → LocalChoice a b p)
    (p : ↑d.primeFactors) :
    assignmentResidue a b d C ≡ (C p : ℕ) [MOD (p : ℕ)] := by
  exact (Nat.chineseRemainderOfFinset
    (fun p : ↑d.primeFactors ↦ (C p : ℕ))
    (fun p : ↑d.primeFactors ↦ (p : ℕ)) Finset.univ
    (by intro q _; exact (Nat.mem_primeFactors.mp q.property).1.ne_zero)
    (by
      intro q _ r _ hqr
      exact Erdos387.primeFactors_pairwise_coprime d q.property r.property
        (fun h ↦ hqr (Subtype.ext h)))).prop p (Finset.mem_univ p)

theorem assignmentResidue_injective {ι : Type*} [Fintype ι]
    (a b : ι → ℕ) (d : ℕ) :
    Function.Injective (assignmentResidue a b d) := by
  intro C D hCD
  funext p
  apply Subtype.ext
  have hC := assignmentResidue_mod a b d C p
  have hD := assignmentResidue_mod a b d D p
  rw [hCD] at hC
  exact (hC.symm.trans hD).eq_of_lt_of_lt (localChoice_lt (C p))
    (localChoice_lt (D p))

/-- The CRT set of simultaneous bad classes modulo a squarefree `d`. -/
noncomputable def assignmentResidues {ι : Type*} [Fintype ι]
    (a b : ι → ℕ) (d : ℕ) : Finset ℕ := by
  classical
  exact Finset.univ.image (assignmentResidue a b d)

theorem card_assignmentResidues {ι : Type*} [Fintype ι]
    (a b : ι → ℕ) (d : ℕ) :
    (assignmentResidues a b d).card = nuClasses a b d := by
  classical
  rw [assignmentResidues, Finset.card_image_of_injective _
    (assignmentResidue_injective a b d), Finset.card_univ,
    Fintype.card_pi]
  unfold nuClasses localNu
  rw [Finset.univ_eq_attach]
  simp only [Fintype.card_coe]
  exact Finset.prod_attach d.primeFactors
    (fun p ↦ (affineResidues a b p).card)

theorem assignmentResidue_lt {ι : Type*} [Fintype ι]
    {a b : ι → ℕ} {d : ℕ} (hd : Squarefree d)
    (C : (p : ↑d.primeFactors) → LocalChoice a b p) :
    assignmentResidue a b d C < d := by
  have hlt :=
    Nat.chineseRemainderOfFinset_lt_prod
      (fun p : ↑d.primeFactors ↦ (C p : ℕ))
      (fun p : ↑d.primeFactors ↦ (p : ℕ)) (t := Finset.univ)
      (by intro p _; exact (Nat.mem_primeFactors.mp p.property).1.ne_zero)
      (by
        intro p _ q _ hpq
        exact Erdos387.primeFactors_pairwise_coprime d p.property q.property
          (fun h ↦ hpq (Subtype.ext h)))
  calc
    assignmentResidue a b d C < ∏ p : ↑d.primeFactors, (p : ℕ) := by
      simpa [assignmentResidue] using hlt
    _ = ∏ p ∈ d.primeFactors, p := by
      simpa using Finset.prod_attach d.primeFactors (fun p : ℕ ↦ p)
    _ = d := Nat.prod_primeFactors_of_squarefree hd

theorem assignmentResidues_lt {ι : Type*} [Fintype ι]
    {a b : ι → ℕ} {d r : ℕ} (hd : Squarefree d)
    (hr : r ∈ assignmentResidues a b d) : r < d := by
  classical
  rw [assignmentResidues, Finset.mem_image] at hr
  obtain ⟨C, _hC, rfl⟩ := hr
  exact assignmentResidue_lt hd C

theorem prime_dvd_affineProduct_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι → ℕ} {p n : ℕ} (hp : p.Prime) :
    p ∣ affineProduct a b n ↔ ∃ i : ι, p ∣ a i * n + b i := by
  unfold affineProduct
  simpa using
    (Erdos387.prime_dvd_finset_prod_iff hp (Finset.univ : Finset ι)
      (fun i ↦ a i * n + b i))

/-- Divisibility by a squarefree modulus is exactly membership in the CRT
root set assembled from the local roots. -/
theorem squarefree_dvd_affineProduct_iff_mod_mem
    {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ι → ℕ} {n d : ℕ}
    (hd : Squarefree d) :
    d ∣ affineProduct a b n ↔ n % d ∈ assignmentResidues a b d := by
  classical
  constructor
  · intro hdiv
    have hlocal : ∀ p : ↑d.primeFactors,
        n % (p : ℕ) ∈ affineResidues a b p := by
      intro p
      have hpPrime := (Nat.mem_primeFactors.mp p.property).1
      have hpPos := hpPrime.pos
      rw [mem_affineResidues]
      refine ⟨Nat.mod_lt _ hpPos, ?_⟩
      rw [prime_dvd_affineProduct_iff hpPrime]
      obtain ⟨i, hi⟩ := (prime_dvd_affineProduct_iff hpPrime).mp
        ((Nat.dvd_of_mem_primeFactors p.property).trans hdiv)
      refine ⟨i, ?_⟩
      have hmod : a i * (n % p) + b i ≡ a i * n + b i [MOD p] := by
        exact ((Nat.mod_modEq n p).mul_left (a i)).add_right (b i)
      exact Nat.modEq_zero_iff_dvd.mp
        (hmod.trans (Nat.modEq_zero_iff_dvd.mpr hi))
    let C : (p : ↑d.primeFactors) → LocalChoice a b p :=
      fun p ↦ ⟨n % (p : ℕ), hlocal p⟩
    have hmod : n ≡ assignmentResidue a b d C [MOD d] := by
      have hmod' : n ≡ assignmentResidue a b d C
          [MOD ∏ p ∈ d.primeFactors, p] := by
        rw [Erdos387.modEq_prod_primeFactors_iff]
        intro p hp
        let p' : ↑d.primeFactors := ⟨p, hp⟩
        exact (Nat.mod_modEq n p).symm.trans
          (assignmentResidue_mod a b d C p').symm
      simpa only [Nat.prod_primeFactors_of_squarefree hd] using hmod'
    have heq : n % d = assignmentResidue a b d C :=
      Nat.mod_eq_of_modEq hmod (assignmentResidue_lt hd C)
    rw [assignmentResidues, Finset.mem_image]
    exact ⟨C, Finset.mem_univ C, heq.symm⟩
  · intro hmem
    rw [assignmentResidues, Finset.mem_image] at hmem
    obtain ⟨C, _hC, hCeq⟩ := hmem
    apply (Erdos387.squarefree_dvd_iff_primeFactors_dvd hd).mpr
    intro p hp
    let p' : ↑d.primeFactors := ⟨p, hp⟩
    have hmodD : n ≡ assignmentResidue a b d C [MOD d] := by
      change n % d = assignmentResidue a b d C % d
      rw [Nat.mod_eq_of_lt (assignmentResidue_lt hd C)]
      exact hCeq.symm
    have hmodP : n ≡ (C p' : ℕ) [MOD p] :=
      (hmodD.of_dvd (Nat.dvd_of_mem_primeFactors hp)).trans
        (assignmentResidue_mod a b d C p')
    have hchoice := (C p').property
    rw [mem_affineResidues] at hchoice
    have hpPrime := (Nat.mem_primeFactors.mp hp).1
    rw [prime_dvd_affineProduct_iff hpPrime] at hchoice ⊢
    obtain ⟨i, hi⟩ := hchoice.2
    refine ⟨i, ?_⟩
    have hmod : a i * n + b i ≡ a i * (C p' : ℕ) + b i [MOD p] :=
      (hmodP.mul_left (a i)).add_right (b i)
    exact Nat.modEq_zero_iff_dvd.mp
      (hmod.trans (Nat.modEq_zero_iff_dvd.mpr hi))

theorem affineResidues_eq_assignmentResidues
    {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ι → ℕ} {d : ℕ}
    (hd : Squarefree d) :
    affineResidues a b d = assignmentResidues a b d := by
  ext r
  constructor
  · intro hr
    have hrlt := affineResidues_lt hr
    have hmem := (squarefree_dvd_affineProduct_iff_mod_mem hd).mp
      (mem_affineResidues.mp hr).2
    simpa [Nat.mod_eq_of_lt hrlt] using hmem
  · intro hr
    have hrlt := assignmentResidues_lt hd hr
    have hdiv := (squarefree_dvd_affineProduct_iff_mod_mem
      (a := a) (b := b) (n := r) hd).mpr
      (by simpa [Nat.mod_eq_of_lt hrlt] using hr)
    exact mem_affineResidues.mpr ⟨hrlt, hdiv⟩

theorem card_affineResidues_of_squarefree
    {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ι → ℕ} {d : ℕ}
    (hd : Squarefree d) :
    (affineResidues a b d).card = nuClasses a b d := by
  rw [affineResidues_eq_assignmentResidues hd,
    card_assignmentResidues]

theorem affineNu_eq_residueDensity_of_squarefree
    {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ι → ℕ} {d : ℕ}
    (hd : Squarefree d) :
    affineNu a b d = ((affineResidues a b d).card : ℝ) / d := by
  rw [affineNu_squarefree hd, card_affineResidues_of_squarefree hd]

/-! ## Prime-local bounds -/

theorem affineResidues_eq_biUnion_of_prime
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι → ℕ} {p : ℕ} (hp : p.Prime) :
    affineResidues a b p =
      Finset.univ.biUnion fun i ↦ Erdos822.affineRootResidues (a i) (b i) p := by
  ext r
  simp only [mem_affineResidues, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Erdos822.affineRootResidues, Finset.mem_filter,
    Finset.mem_range]
  rw [prime_dvd_affineProduct_iff hp]
  tauto

theorem localNu_le_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι → ℕ} {p : ℕ} (hp : p.Prime)
    (hcop : ∀ i, (a i).Coprime p) :
    localNu a b p ≤ Fintype.card ι := by
  rw [localNu, affineResidues_eq_biUnion_of_prime hp]
  calc
    (Finset.univ.biUnion fun i ↦
        Erdos822.affineRootResidues (a i) (b i) p).card ≤
        ∑ i : ι, (Erdos822.affineRootResidues (a i) (b i) p).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i : ι, 1 := Finset.sum_le_sum fun i _ ↦
      Erdos822.affineRootResidues_card_le_one_of_not_dvd hp
        ((hp.coprime_iff_not_dvd).mp (hcop i).symm)
    _ = Fintype.card ι := by simp

theorem localNu_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    {a b : ι → ℕ} {p : ℕ} (hp : p.Prime)
    (hcop : ∀ i, (a i).Coprime p) :
    0 < localNu a b p := by
  classical
  let i : ι := Classical.choice inferInstance
  rw [localNu, Finset.card_pos]
  obtain ⟨r, hr⟩ := Erdos822.affineRootResidues_nonempty_of_not_dvd hp
    ((hp.coprime_iff_not_dvd).mp (hcop i).symm)
  refine ⟨r, ?_⟩
  rw [affineResidues_eq_biUnion_of_prime hp, Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ i, hr⟩

/-- A unit-slope affine form has exactly one root modulo a prime. -/
theorem card_affineRootResidues_eq_one {A s p : ℕ}
    (hp : p.Prime) (hA : A.Coprime p) :
    (Erdos822.affineRootResidues A s p).card = 1 := by
  apply Nat.le_antisymm
  · exact Erdos822.affineRootResidues_card_le_one_of_not_dvd hp
      ((hp.coprime_iff_not_dvd).mp hA.symm)
  · rw [Nat.one_le_iff_ne_zero, Finset.card_ne_zero]
    exact Erdos822.affineRootResidues_nonempty_of_not_dvd hp
      ((hp.coprime_iff_not_dvd).mp hA.symm)

/-- Distinct affine forms whose cross-determinant is nonzero modulo `p`
have disjoint root sets modulo `p`. -/
theorem affineRootResidues_disjoint_of_not_modEq
    {a b : ι → ℕ} {p : ℕ} {i j : ι}
    (hdet : ¬a i * b j ≡ a j * b i [MOD p]) :
    Disjoint (Erdos822.affineRootResidues (a i) (b i) p)
      (Erdos822.affineRootResidues (a j) (b j) p) := by
  rw [Finset.disjoint_left]
  intro r hri hrj
  rw [Erdos822.affineRootResidues, Finset.mem_filter] at hri hrj
  apply hdet
  have hi : a i * r + b i ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr hri.2
  have hj : a j * r + b j ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr hrj.2
  have hi' := hi.mul_left (a j)
  have hj' := hj.mul_left (a i)
  have hcross : a j * b i ≡ a i * b j [MOD p] := by
    apply Nat.ModEq.add_left_cancel' (a i * a j * r)
    calc
      a i * a j * r + a j * b i =
          a j * (a i * r + b i) := by ring
      _ ≡ a j * 0 [MOD p] := hi'
      _ = 0 := by simp
      _ ≡ a i * 0 [MOD p] := Nat.ModEq.rfl
      _ ≡ a i * (a j * r + b j) [MOD p] := hj'.symm
      _ = a i * a j * r + a i * b j := by ring
  exact hcross.symm

/-- Away from the slopes and cross-determinants, the product of `k`
affine forms has exactly `k` roots modulo `p`. -/
theorem localNu_eq_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι → ℕ} {p : ℕ} (hp : p.Prime)
    (hcop : ∀ i, (a i).Coprime p)
    (hdet : ∀ i j, i ≠ j → ¬a i * b j ≡ a j * b i [MOD p]) :
    localNu a b p = Fintype.card ι := by
  rw [localNu, affineResidues_eq_biUnion_of_prime hp,
    Finset.card_biUnion]
  · simp only [card_affineRootResidues_eq_one hp (hcop _),
      Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  · intro i hi j hj hij
    exact affineRootResidues_disjoint_of_not_modEq (hdet i j hij)

/-! ## Dyadic interval and `BoundingSieve` -/

def divisibleCandidates {ι : Type*} [Fintype ι]
    (a b : ι → ℕ) (X d : ℕ) : Finset ℕ :=
  (Finset.Ioc X (2 * X)).filter fun n ↦ d ∣ affineProduct a b n

def siftedCandidates {ι : Type*} [Fintype ι]
    (a b : ι → ℕ) (X z Y : ℕ) : Finset ℕ :=
  (Finset.Ioc X (2 * X)).filter fun n ↦
    Nat.Coprime (Erdos387.sievePrimeProduct z Y) (affineProduct a b n)

noncomputable def boundingSieve
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a b : ι → ℕ) (X z Y : ℕ)
    (hz : Fintype.card ι ≤ z)
    (hcop : ∀ p : ℕ, p.Prime →
      p ∣ Erdos387.sievePrimeProduct z Y → ∀ i, (a i).Coprime p) :
    BoundingSieve := by
  classical
  let I := Finset.Ioc X (2 * X)
  let f := affineProduct a b
  exact
    { support := I.image f
      prodPrimes := Erdos387.sievePrimeProduct z Y
      prodPrimes_squarefree := Erdos387.sievePrimeProduct_squarefree z Y
      weights := fun q ↦ ((I.filter fun n ↦ f n = q).card : ℝ)
      weights_nonneg := fun _ ↦ by positivity
      totalMass := X
      nu := affineNu a b
      nu_mult := affineNu_mult a b
      nu_pos_of_prime := by
        intro p hp hpDiv
        rw [affineNu_prime hp]
        exact div_pos (by exact_mod_cast localNu_pos hp (hcop p hp hpDiv))
          (by exact_mod_cast hp.pos)
      nu_lt_one_of_prime := by
        intro p hp hpDiv
        rw [affineNu_prime hp]
        have hpMem := Erdos387.prime_mem_sievePrimes_of_dvd_product hp hpDiv
        have hzp : z < p := (Erdos387.mem_sievePrimes.mp hpMem).2.1
        have hlocal : localNu a b p < p :=
          (localNu_le_card hp (hcop p hp hpDiv)).trans_lt (hz.trans_lt hzp)
        exact (div_lt_one (by exact_mod_cast hp.pos)).mpr
          (by exact_mod_cast hlocal) }

theorem boundingSieve_totalMass
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {a b : ι → ℕ} {X z Y : ℕ} {hz : Fintype.card ι ≤ z}
    {hcop : ∀ p : ℕ, p.Prime →
      p ∣ Erdos387.sievePrimeProduct z Y → ∀ i, (a i).Coprime p} :
    (boundingSieve a b X z Y hz hcop).totalMass = X := rfl

theorem boundingSieve_multSum
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {a b : ι → ℕ} {X z Y d : ℕ} {hz : Fintype.card ι ≤ z}
    {hcop : ∀ p : ℕ, p.Prime →
      p ∣ Erdos387.sievePrimeProduct z Y → ∀ i, (a i).Coprime p} :
    (boundingSieve a b X z Y hz hcop).multSum d =
      ((divisibleCandidates a b X d).card : ℝ) := by
  classical
  let I := Finset.Ioc X (2 * X)
  let f := affineProduct a b
  rw [BoundingSieve.multSum]
  change (∑ q ∈ I.image f,
      if d ∣ q then ((I.filter fun n ↦ f n = q).card : ℝ) else 0) = _
  simp_rw [← Finset.sum_filter]
  have hcount :
      (∑ q ∈ (I.image f).filter fun q ↦ d ∣ q,
          (I.filter fun n ↦ f n = q).card) =
        (I.filter fun n ↦ d ∣ f n).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcount]
  norm_cast

theorem boundingSieve_siftedSum
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {a b : ι → ℕ} {X z Y : ℕ} {hz : Fintype.card ι ≤ z}
    {hcop : ∀ p : ℕ, p.Prime →
      p ∣ Erdos387.sievePrimeProduct z Y → ∀ i, (a i).Coprime p} :
    (boundingSieve a b X z Y hz hcop).siftedSum =
      ((siftedCandidates a b X z Y).card : ℝ) := by
  classical
  let I := Finset.Ioc X (2 * X)
  let f := affineProduct a b
  rw [BoundingSieve.siftedSum]
  change (∑ q ∈ I.image f,
      if Nat.Coprime (Erdos387.sievePrimeProduct z Y) q then
        ((I.filter fun n ↦ f n = q).card : ℝ) else 0) = _
  simp_rw [← Finset.sum_filter]
  have hcount :
      (∑ q ∈ (I.image f).filter fun q ↦
          Nat.Coprime (Erdos387.sievePrimeProduct z Y) q,
          (I.filter fun n ↦ f n = q).card) =
        (I.filter fun n ↦
          Nat.Coprime (Erdos387.sievePrimeProduct z Y) (f n)).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcount]
  norm_cast

theorem divisibleCandidates_eq_modularPreimage
    {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ι → ℕ}
    {X z Y d : ℕ} (hd : d ∣ Erdos387.sievePrimeProduct z Y) :
    divisibleCandidates a b X d =
      Erdos387.modularPreimageIoc X (2 * X) d
        (assignmentResidues a b d) := by
  classical
  have hsq : Squarefree d := Squarefree.squarefree_of_dvd hd
    (Erdos387.sievePrimeProduct_squarefree z Y)
  ext n
  simp only [divisibleCandidates, Erdos387.modularPreimageIoc,
    Finset.mem_filter, Finset.mem_Ioc]
  refine and_congr_right fun _hn ↦ ?_
  exact squarefree_dvd_affineProduct_iff_mod_mem hsq

theorem abs_card_divisibleCandidates_sub_density
    {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ι → ℕ}
    {X z Y d : ℕ} (hd : d ∣ Erdos387.sievePrimeProduct z Y) :
    |((divisibleCandidates a b X d).card : ℝ) -
        (nuClasses a b d : ℝ) * X / d| ≤ nuClasses a b d := by
  have hsq : Squarefree d := Squarefree.squarefree_of_dvd hd
    (Erdos387.sievePrimeProduct_squarefree z Y)
  have hdPos : 0 < d := Erdos387.pos_of_dvd_sievePrimeProduct hd
  rw [divisibleCandidates_eq_modularPreimage hd,
    ← card_assignmentResidues a b d]
  exact Erdos851.ShiftSieve.abs_card_modularPreimageIoc_dyadic_sub_density hdPos _
    (fun _r hr ↦ assignmentResidues_lt hsq hr)

theorem boundingSieve_abs_rem_le_nuClasses
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {a b : ι → ℕ} {X z Y d : ℕ} {hz : Fintype.card ι ≤ z}
    {hcop : ∀ p : ℕ, p.Prime →
      p ∣ Erdos387.sievePrimeProduct z Y → ∀ i, (a i).Coprime p}
    (hd : d ∣ Erdos387.sievePrimeProduct z Y) :
    |(boundingSieve a b X z Y hz hcop).rem d| ≤ nuClasses a b d := by
  have hsq : Squarefree d := Squarefree.squarefree_of_dvd hd
    (Erdos387.sievePrimeProduct_squarefree z Y)
  rw [BoundingSieve.rem, boundingSieve_multSum,
    boundingSieve_totalMass]
  change |((divisibleCandidates a b X d).card : ℝ) -
      affineNu a b d * X| ≤ nuClasses a b d
  rw [affineNu_squarefree hsq]
  have h := abs_card_divisibleCandidates_sub_density
    (a := a) (b := b) (X := X) hd
  convert h using 1 <;> ring_nf

theorem nuClasses_le_card_pow_primeFactors
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι → ℕ} {d : ℕ} (hd : Squarefree d)
    (hcop : ∀ p ∈ d.primeFactors, ∀ i, (a i).Coprime p) :
    nuClasses a b d ≤ (Fintype.card ι) ^ d.primeFactors.card := by
  unfold nuClasses
  calc
    (∏ p ∈ d.primeFactors, localNu a b p) ≤
        ∏ _p ∈ d.primeFactors, Fintype.card ι := by
      apply Finset.prod_le_prod
      · intro p hp
        exact Nat.zero_le _
      · intro p hp
        exact localNu_le_card (Nat.prime_of_mem_primeFactors hp) (hcop p hp)
    _ = (Fintype.card ι) ^ d.primeFactors.card := by
      simp

/-! ## A finite pre-sieving progression -/

/-- An affine family is admissible when its product has no fixed prime
divisor.  The witness is kept as a canonical natural residue. -/
def Admissible {ι : Type*} [Fintype ι]
    (a b : ι → ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ℕ, r < p ∧ ∀ i, ¬p ∣ a i * r + b i

noncomputable def avoidingResidue {ι : Type*} [Fintype ι]
    {a b : ι → ℕ} (h : Admissible a b) (p : ℕ) (hp : p.Prime) : ℕ :=
  Classical.choose (h p hp)

theorem avoidingResidue_lt {ι : Type*} [Fintype ι]
    {a b : ι → ℕ} (h : Admissible a b) (p : ℕ) (hp : p.Prime) :
    avoidingResidue h p hp < p :=
  (Classical.choose_spec (h p hp)).1

theorem avoidingResidue_spec {ι : Type*} [Fintype ι]
    {a b : ι → ℕ} (h : Admissible a b) (p : ℕ) (hp : p.Prime)
    (i : ι) :
    ¬p ∣ a i * avoidingResidue h p hp + b i :=
  (Classical.choose_spec (h p hp)).2 i

/-- A simultaneous representative avoiding every prime at most `z`. -/
noncomputable def preSieveResidue {ι : Type*} [Fintype ι]
    {a b : ι → ℕ} (h : Admissible a b) (z : ℕ) : ℕ :=
  Nat.chineseRemainderOfFinset
    (fun p : ↑z.factorial.primeFactors ↦
      avoidingResidue h p (Nat.prime_of_mem_primeFactors p.property))
    (fun p : ↑z.factorial.primeFactors ↦ (p : ℕ)) Finset.univ
    (by intro p _; exact (Nat.prime_of_mem_primeFactors p.property).ne_zero)
    (by
      intro p _ q _ hpq
      exact Erdos387.primeFactors_pairwise_coprime z.factorial
        p.property q.property (fun h ↦ hpq (Subtype.ext h)))

theorem preSieveResidue_modEq {ι : Type*} [Fintype ι]
    {a b : ι → ℕ} (h : Admissible a b) (z : ℕ)
    (p : ↑z.factorial.primeFactors) :
    preSieveResidue h z ≡
      avoidingResidue h p (Nat.prime_of_mem_primeFactors p.property)
        [MOD (p : ℕ)] := by
  exact (Nat.chineseRemainderOfFinset
    (fun q : ↑z.factorial.primeFactors ↦
      avoidingResidue h q (Nat.prime_of_mem_primeFactors q.property))
    (fun q : ↑z.factorial.primeFactors ↦ (q : ℕ)) Finset.univ
    (by intro q _; exact (Nat.prime_of_mem_primeFactors q.property).ne_zero)
    (by
      intro q _ r _ hqr
      exact Erdos387.primeFactors_pairwise_coprime z.factorial
        q.property r.property (fun h ↦ hqr (Subtype.ext h)))).prop p
          (Finset.mem_univ p)

/-- Slope after restricting the parameter to
`z! * u + preSieveResidue`. -/
def preSievedSlope {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (z : ℕ) (i : ι) : ℕ := a i * z.factorial

/-- Constant term after the same restriction. -/
noncomputable def preSievedConstant {ι : Type*} [Fintype ι]
    (a b : ι → ℕ) (h : Admissible a b) (z : ℕ) (i : ι) : ℕ :=
  a i * preSieveResidue h z + b i

theorem preSieved_form_identity {ι : Type*} [Fintype ι]
    {a b : ι → ℕ} (h : Admissible a b) (z : ℕ) (i : ι) (u : ℕ) :
    preSievedSlope a z i * u + preSievedConstant a b h z i =
      a i * (z.factorial * u + preSieveResidue h z) + b i := by
  simp [preSievedSlope, preSievedConstant]
  ring

theorem prime_mem_factorial_primeFactors {p z : ℕ}
    (hp : p.Prime) (hpz : p ≤ z) : p ∈ z.factorial.primeFactors := by
  rw [Nat.mem_primeFactors]
  exact ⟨hp, hp.dvd_factorial.mpr hpz, Nat.factorial_ne_zero z⟩

/-- Every prime at most the pre-sieving threshold is absent from every
transformed form. -/
theorem not_dvd_preSievedForm_of_le {ι : Type*} [Fintype ι]
    {a b : ι → ℕ} (h : Admissible a b) {z p : ℕ}
    (hp : p.Prime) (hpz : p ≤ z) (i : ι) (u : ℕ) :
    ¬p ∣ preSievedSlope a z i * u + preSievedConstant a b h z i := by
  let p' : ↑z.factorial.primeFactors :=
    ⟨p, prime_mem_factorial_primeFactors hp hpz⟩
  have hres := preSieveResidue_modEq h z p'
  have hav := avoidingResidue_spec h p hp i
  intro hdvd
  have hpfac : p ∣ z.factorial := hp.dvd_factorial.mpr hpz
  have hslope : preSievedSlope a z i * u ≡ 0 [MOD p] := by
    apply Nat.modEq_zero_iff_dvd.mpr
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpfac (a i)) u
  have hconst : preSievedConstant a b h z i ≡
      a i * avoidingResidue h p hp + b i [MOD p] := by
    unfold preSievedConstant
    exact (hres.mul_left (a i)).add_right (b i)
  have hzero : preSievedSlope a z i * u +
      preSievedConstant a b h z i ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr hdvd
  have : a i * avoidingResidue h p hp + b i ≡ 0 [MOD p] :=
    by simpa using ((hslope.add hconst).symm.trans hzero)
  exact hav (Nat.modEq_zero_iff_dvd.mp this)

/-- Above a threshold containing every positive original slope, all
pre-sieved slopes are units modulo the sieving primes. -/
theorem preSievedSlope_coprime_of_lt
    {ι : Type*} [Fintype ι] {a : ι → ℕ} {z p : ℕ}
    (haPos : ∀ i, 0 < a i) (haLe : ∀ i, a i ≤ z)
    (hp : p.Prime) (hzp : z < p) (i : ι) :
    (preSievedSlope a z i).Coprime p := by
  apply Nat.Coprime.symm
  rw [hp.coprime_iff_not_dvd]
  intro hpd
  rw [preSievedSlope, hp.dvd_mul] at hpd
  rcases hpd with hpa | hpfac
  · exact (not_lt_of_ge (Nat.le_of_dvd (haPos i) hpa |>.trans (haLe i))) hzp
  · exact (not_lt_of_ge (hp.dvd_factorial.mp hpfac)) hzp

end

end Erdos946.AffineSieve
