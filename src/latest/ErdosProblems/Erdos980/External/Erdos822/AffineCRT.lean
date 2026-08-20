/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.AffineSieve
import ErdosProblems.Erdos387.QualitativeSieve

/-!
# CRT classes for the two-affine-form sieve

For a squarefree modulus, divisibility of a product of two affine forms is
the union of one independently chosen bad class at every prime factor.  This
file makes those classes explicit and counts them.  It is the affine analogue
of the finite CRT layer in Erdos851.SieveSpecialization.
-/

namespace Erdos822

open scoped BigOperators ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction

/-- Number of simultaneous bad CRT classes for the two affine forms. -/
def twoAffineNuClasses (a s b t d : ℕ) : ℕ :=
  ∏ p ∈ d.primeFactors, twoAffineLocalNu a s b t p

/-- On a squarefree modulus the multiplicative density is exactly the number
of CRT classes divided by the modulus. -/
theorem twoAffineNu_squarefree {a s b t d : ℕ} (hd : Squarefree d) :
    twoAffineNu a s b t d = (twoAffineNuClasses a s b t d : ℝ) / d := by
  rw [twoAffineNu, ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero,
    Finset.prod_div_distrib]
  unfold twoAffineNuClasses
  rw [← Nat.cast_prod]
  congr 1
  rw [← Nat.cast_prod]
  norm_cast
  exact Nat.prod_primeFactors_of_squarefree hd

/-- A local choice is one of the bad affine residues modulo p. -/
abbrev AffineLocalChoice (a s b t p : ℕ) :=
  {r : ℕ // r ∈ twoAffineBadResidues a s b t p}

theorem affineLocalChoice_lt {a s b t p : ℕ}
    (r : AffineLocalChoice a s b t p) : (r : ℕ) < p :=
  lt_of_mem_twoAffineBadResidues r.property

/-- CRT representative attached to one bad local residue at every prime
factor of d. -/
noncomputable def affineAssignmentResidue (a s b t d : ℕ)
    (A : (p : ↑d.primeFactors) → AffineLocalChoice a s b t p) : ℕ :=
  Nat.chineseRemainderOfFinset
    (fun p : ↑d.primeFactors ↦ (A p : ℕ))
    (fun p : ↑d.primeFactors ↦ (p : ℕ)) Finset.univ
    (by intro p _; exact (Nat.mem_primeFactors.mp p.property).1.ne_zero)
    (by
      intro p _ q _ hpq
      exact Erdos387.primeFactors_pairwise_coprime d p.property q.property
        (fun h ↦ hpq (Subtype.ext h)))

theorem affineAssignmentResidue_mod (a s b t d : ℕ)
    (A : (p : ↑d.primeFactors) → AffineLocalChoice a s b t p)
    (p : ↑d.primeFactors) :
    affineAssignmentResidue a s b t d A ≡ (A p : ℕ) [MOD (p : ℕ)] := by
  exact (Nat.chineseRemainderOfFinset
    (fun p : ↑d.primeFactors ↦ (A p : ℕ))
    (fun p : ↑d.primeFactors ↦ (p : ℕ)) Finset.univ
    (by intro p _; exact (Nat.mem_primeFactors.mp p.property).1.ne_zero)
    (by
      intro p _ q _ hpq
      exact Erdos387.primeFactors_pairwise_coprime d p.property q.property
        (fun h ↦ hpq (Subtype.ext h)))).prop p (Finset.mem_univ p)

theorem affineAssignmentResidue_injective (a s b t d : ℕ) :
    Function.Injective (affineAssignmentResidue a s b t d) := by
  intro A B hAB
  funext p
  apply Subtype.ext
  have hA := affineAssignmentResidue_mod a s b t d A p
  have hB := affineAssignmentResidue_mod a s b t d B p
  have hAlt := Nat.mod_eq_of_modEq hA (affineLocalChoice_lt (A p))
  have hBlt := Nat.mod_eq_of_modEq hB (affineLocalChoice_lt (B p))
  rw [hAB] at hAlt
  omega

/-- Finite set of simultaneous affine bad residue classes modulo d. -/
noncomputable def affineAssignmentResidues (a s b t d : ℕ) : Finset ℕ := by
  classical
  exact Finset.univ.image (affineAssignmentResidue a s b t d)

theorem card_affineAssignmentResidues (a s b t d : ℕ) :
    (affineAssignmentResidues a s b t d).card =
      twoAffineNuClasses a s b t d := by
  classical
  rw [affineAssignmentResidues, Finset.card_image_of_injective _
    (affineAssignmentResidue_injective a s b t d), Finset.card_univ,
    Fintype.card_pi]
  unfold twoAffineNuClasses twoAffineLocalNu
  rw [Finset.univ_eq_attach]
  simp only [Fintype.card_coe]
  exact Finset.prod_attach d.primeFactors
    (fun p ↦ (twoAffineBadResidues a s b t p).card)

theorem affineAssignmentResidue_lt {a s b t d : ℕ} (hd : Squarefree d)
    (A : (p : ↑d.primeFactors) → AffineLocalChoice a s b t p) :
    affineAssignmentResidue a s b t d A < d := by
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
    affineAssignmentResidue a s b t d A <
        ∏ p : ↑d.primeFactors, (p : ℕ) := by
      simpa [affineAssignmentResidue] using hlt
    _ = ∏ p ∈ d.primeFactors, p := by
      simpa using Finset.prod_attach d.primeFactors (fun p : ℕ ↦ p)
    _ = d := Nat.prod_primeFactors_of_squarefree hd

theorem affineAssignmentResidues_lt {a s b t d r : ℕ} (hd : Squarefree d)
    (hr : r ∈ affineAssignmentResidues a s b t d) : r < d := by
  classical
  rw [affineAssignmentResidues, Finset.mem_image] at hr
  obtain ⟨A, _hA, rfl⟩ := hr
  exact affineAssignmentResidue_lt hd A

theorem twoAffineNuClasses_le {a s b t d : ℕ} (hd : Squarefree d) :
    twoAffineNuClasses a s b t d ≤ d := by
  rw [← card_affineAssignmentResidues]
  simpa only [Finset.card_range] using
    Finset.card_le_card (show affineAssignmentResidues a s b t d ⊆ Finset.range d by
      intro r hr
      exact Finset.mem_range.mpr (affineAssignmentResidues_lt hd hr))

/-- The product whose prime divisors encode simultaneous affine primality
obstructions. -/
def twoAffineProduct (a s b t n : ℕ) : ℕ :=
  (a * n + s) * (b * n + t)

/-- Divisibility of one affine form depends only on the parameter modulo the
modulus. -/
theorem dvd_affineForm_iff_dvd_mod {a s n p : ℕ} :
    p ∣ a * n + s ↔ p ∣ a * (n % p) + s := by
  have hmod : a * n + s ≡ a * (n % p) + s [MOD p] :=
    ((Nat.mod_modEq n p).symm.mul_left a).add_right s
  constructor
  · intro h
    exact Nat.modEq_zero_iff_dvd.mp
      (hmod.symm.trans h.modEq_zero_nat)
  · intro h
    exact Nat.modEq_zero_iff_dvd.mp
      (hmod.trans h.modEq_zero_nat)

/-- A prime divides the product of two affine forms exactly when the
parameter lies in one of the explicit local bad classes. -/
theorem prime_dvd_twoAffineProduct_iff_mod_mem
    {a s b t n p : ℕ} (hp : p.Prime) :
    p ∣ twoAffineProduct a s b t n ↔
      n % p ∈ twoAffineBadResidues a s b t p := by
  rw [mem_twoAffineBadResidues_iff]
  constructor
  · intro h
    rw [twoAffineProduct] at h
    rcases hp.dvd_mul.mp h with hleft | hright
    · exact Or.inl ⟨Nat.mod_lt _ hp.pos,
        (dvd_affineForm_iff_dvd_mod).mp hleft⟩
    · exact Or.inr ⟨Nat.mod_lt _ hp.pos,
        (dvd_affineForm_iff_dvd_mod).mp hright⟩
  · rintro (⟨_hlt, hleft⟩ | ⟨_hlt, hright⟩)
    · rw [twoAffineProduct]
      exact dvd_mul_of_dvd_left
        ((dvd_affineForm_iff_dvd_mod).mpr hleft) _
    · rw [twoAffineProduct]
      exact dvd_mul_of_dvd_right
        ((dvd_affineForm_iff_dvd_mod).mpr hright) _

/-- Squarefree divisibility by the two-affine product is membership in the
explicit set of simultaneous CRT classes. -/
theorem squarefree_dvd_twoAffineProduct_iff_mod_mem
    {a s b t n d : ℕ} (hd : Squarefree d) :
    d ∣ twoAffineProduct a s b t n ↔
      n % d ∈ affineAssignmentResidues a s b t d := by
  classical
  constructor
  · intro hdiv
    have hlocal : ∀ p : ↑d.primeFactors,
        n % (p : ℕ) ∈ twoAffineBadResidues a s b t p := by
      intro p
      have hpPrime := (Nat.mem_primeFactors.mp p.property).1
      have hpDiv : (p : ℕ) ∣ twoAffineProduct a s b t n :=
        (Nat.dvd_of_mem_primeFactors p.property).trans hdiv
      exact (prime_dvd_twoAffineProduct_iff_mod_mem hpPrime).mp hpDiv
    let A : (p : ↑d.primeFactors) → AffineLocalChoice a s b t p :=
      fun p ↦ ⟨n % (p : ℕ), hlocal p⟩
    have hmod : n ≡ affineAssignmentResidue a s b t d A [MOD d] := by
      have hmod' :
          n ≡ affineAssignmentResidue a s b t d A
            [MOD ∏ p ∈ d.primeFactors, p] := by
        rw [Erdos387.modEq_prod_primeFactors_iff]
        intro p hp
        let p' : ↑d.primeFactors := ⟨p, hp⟩
        exact (Nat.mod_modEq n p).symm.trans
          (affineAssignmentResidue_mod a s b t d A p').symm
      simpa only [Nat.prod_primeFactors_of_squarefree hd] using hmod'
    have heq : n % d = affineAssignmentResidue a s b t d A :=
      Nat.mod_eq_of_modEq hmod (affineAssignmentResidue_lt hd A)
    rw [affineAssignmentResidues, Finset.mem_image]
    exact ⟨A, Finset.mem_univ A, heq.symm⟩
  · intro hmem
    rw [affineAssignmentResidues, Finset.mem_image] at hmem
    obtain ⟨A, _hA, hAeq⟩ := hmem
    apply (Erdos387.squarefree_dvd_iff_primeFactors_dvd hd).mpr
    intro p hp
    have hpPrime := (Nat.mem_primeFactors.mp hp).1
    let p' : ↑d.primeFactors := ⟨p, hp⟩
    have hmodD : n ≡ affineAssignmentResidue a s b t d A [MOD d] := by
      change n % d = affineAssignmentResidue a s b t d A % d
      rw [Nat.mod_eq_of_lt (affineAssignmentResidue_lt hd A)]
      exact hAeq.symm
    have hmodP : n ≡ (A p' : ℕ) [MOD p] :=
      (hmodD.of_dvd (Nat.dvd_of_mem_primeFactors hp)).trans
        (affineAssignmentResidue_mod a s b t d A p')
    have hAltp : (A p' : ℕ) < p := affineLocalChoice_lt (A p')
    have hnmod : n % p = (A p' : ℕ) :=
      Nat.mod_eq_of_modEq hmodP hAltp
    apply (prime_dvd_twoAffineProduct_iff_mod_mem hpPrime).mpr
    rw [hnmod]
    exact (A p').property

end Erdos822
