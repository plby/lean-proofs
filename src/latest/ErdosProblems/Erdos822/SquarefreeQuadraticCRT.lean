/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.QuadraticRootResidues
import ErdosProblems.Erdos822.AffineCRT

/-!
# Squarefree CRT classes for the quadratic cofactor relation

The quadratic congruence forced by a supported common divisor has at most
two classes at each prime.  This file combines those honest prime-field
bounds across a squarefree modulus.  Prime powers are deliberately excluded:
repeated roots modulo a prime power require a separate estimate.
-/

namespace Erdos822

open scoped BigOperators
open Finset Nat

/-- A chosen natural representative of one quadratic root modulo a prime. -/
abbrev QuadraticLocalChoice (u v p : ℕ) :=
  {r : ℕ // r ∈ quadraticRootResidues p u v}

theorem quadraticLocalChoice_lt {u v p : ℕ}
    (r : QuadraticLocalChoice u v p) : (r : ℕ) < p :=
  (mem_quadraticRootResidues_iff.mp r.property).1

/-- CRT representative attached to one quadratic root at each prime factor
of a squarefree modulus. -/
noncomputable def quadraticAssignmentResidue (u v d : ℕ)
    (A : (p : ↑d.primeFactors) → QuadraticLocalChoice u v p) : ℕ :=
  Nat.chineseRemainderOfFinset
    (fun p : ↑d.primeFactors ↦ (A p : ℕ))
    (fun p : ↑d.primeFactors ↦ (p : ℕ)) Finset.univ
    (by intro p _; exact (Nat.mem_primeFactors.mp p.property).1.ne_zero)
    (by
      intro p _ q _ hpq
      exact Erdos387.primeFactors_pairwise_coprime d p.property q.property
        (fun h ↦ hpq (Subtype.ext h)))

theorem quadraticAssignmentResidue_mod (u v d : ℕ)
    (A : (p : ↑d.primeFactors) → QuadraticLocalChoice u v p)
    (p : ↑d.primeFactors) :
    quadraticAssignmentResidue u v d A ≡ (A p : ℕ) [MOD (p : ℕ)] := by
  exact (Nat.chineseRemainderOfFinset
    (fun p : ↑d.primeFactors ↦ (A p : ℕ))
    (fun p : ↑d.primeFactors ↦ (p : ℕ)) Finset.univ
    (by intro p _; exact (Nat.mem_primeFactors.mp p.property).1.ne_zero)
    (by
      intro p _ q _ hpq
      exact Erdos387.primeFactors_pairwise_coprime d p.property q.property
        (fun h ↦ hpq (Subtype.ext h)))).prop p (Finset.mem_univ p)

theorem quadraticAssignmentResidue_injective (u v d : ℕ) :
    Function.Injective (quadraticAssignmentResidue u v d) := by
  intro A B hAB
  funext p
  apply Subtype.ext
  have hA := quadraticAssignmentResidue_mod u v d A p
  have hB := quadraticAssignmentResidue_mod u v d B p
  have hAlt := Nat.mod_eq_of_modEq hA (quadraticLocalChoice_lt (A p))
  have hBlt := Nat.mod_eq_of_modEq hB (quadraticLocalChoice_lt (B p))
  rw [hAB] at hAlt
  omega

/-- Simultaneous quadratic-root representatives modulo all prime factors. -/
noncomputable def quadraticAssignmentResidues (u v d : ℕ) : Finset ℕ := by
  classical
  exact Finset.univ.image (quadraticAssignmentResidue u v d)

theorem quadraticAssignmentResidue_lt {u v d : ℕ} (hd : Squarefree d)
    (A : (p : ↑d.primeFactors) → QuadraticLocalChoice u v p) :
    quadraticAssignmentResidue u v d A < d := by
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
    quadraticAssignmentResidue u v d A <
        ∏ p : ↑d.primeFactors, (p : ℕ) := by
      simpa [quadraticAssignmentResidue] using hlt
    _ = ∏ p ∈ d.primeFactors, p := by
      simpa using Finset.prod_attach d.primeFactors (fun p : ℕ ↦ p)
    _ = d := Nat.prod_primeFactors_of_squarefree hd

theorem quadraticAssignmentResidues_lt {u v d r : ℕ} (hd : Squarefree d)
    (hr : r ∈ quadraticAssignmentResidues u v d) : r < d := by
  classical
  rw [quadraticAssignmentResidues, Finset.mem_image] at hr
  obtain ⟨A, _hA, rfl⟩ := hr
  exact quadraticAssignmentResidue_lt hd A

theorem quadraticAssignmentResidues_card_le_two_pow
    {u v d : ℕ} (hd : Squarefree d) :
    (quadraticAssignmentResidues u v d).card ≤
      2 ^ d.primeFactors.card := by
  classical
  rw [quadraticAssignmentResidues,
    Finset.card_image_of_injective _
      (quadraticAssignmentResidue_injective u v d),
    Finset.card_univ, Fintype.card_pi]
  calc
    ∏ p : ↑d.primeFactors,
        Fintype.card (QuadraticLocalChoice u v p) ≤
        ∏ _p : ↑d.primeFactors, 2 := by
      apply Finset.prod_le_prod
      · intro p hp
        exact Nat.zero_le _
      · intro p hp
        simpa only [Fintype.card_coe] using
          quadraticRootResidues_card_le_two_of_prime
            (Nat.mem_primeFactors.mp p.property).1 u v
    _ = 2 ^ d.primeFactors.card := by
      simp

theorem quadratic_modEq_of_modEq
    {n a u v p : ℕ} (hna : n ≡ a [MOD p])
    (ha : a ^ 2 + u ≡ v * a [MOD p]) :
    n ^ 2 + u ≡ v * n [MOD p] := by
  exact (hna.pow 2).add_right u |>.trans
    (ha.trans (hna.mul_left v).symm)

/-- A squarefree quadratic congruence is equivalent to membership in the
explicit CRT family of prime-local root classes. -/
theorem squarefree_quadratic_modEq_iff_mod_mem
    {n u v d : ℕ} (hd : Squarefree d) :
    n ^ 2 + u ≡ v * n [MOD d] ↔
      n % d ∈ quadraticAssignmentResidues u v d := by
  classical
  constructor
  · intro hquad
    have hlocal : ∀ p : ↑d.primeFactors,
        n % (p : ℕ) ∈ quadraticRootResidues (p : ℕ) u v := by
      intro p
      have hpDiv : (p : ℕ) ∣ d :=
        Nat.dvd_of_mem_primeFactors p.property
      have hpquad : n ^ 2 + u ≡ v * n [MOD (p : ℕ)] :=
        hquad.of_dvd hpDiv
      rw [mem_quadraticRootResidues_iff]
      refine ⟨Nat.mod_lt _ (Nat.mem_primeFactors.mp p.property).1.pos, ?_⟩
      exact quadratic_modEq_of_modEq (Nat.mod_modEq n (p : ℕ))
        hpquad
    let A : (p : ↑d.primeFactors) → QuadraticLocalChoice u v p :=
      fun p ↦ ⟨n % (p : ℕ), hlocal p⟩
    have hmod : n ≡ quadraticAssignmentResidue u v d A [MOD d] := by
      have hmod' :
          n ≡ quadraticAssignmentResidue u v d A
            [MOD ∏ p ∈ d.primeFactors, p] := by
        rw [Erdos387.modEq_prod_primeFactors_iff]
        intro p hp
        let p' : ↑d.primeFactors := ⟨p, hp⟩
        exact (Nat.mod_modEq n p).symm.trans
          (quadraticAssignmentResidue_mod u v d A p').symm
      simpa only [Nat.prod_primeFactors_of_squarefree hd] using hmod'
    have heq : n % d = quadraticAssignmentResidue u v d A :=
      Nat.mod_eq_of_modEq hmod (quadraticAssignmentResidue_lt hd A)
    rw [quadraticAssignmentResidues, Finset.mem_image]
    exact ⟨A, Finset.mem_univ A, heq.symm⟩
  · intro hmem
    rw [quadraticAssignmentResidues, Finset.mem_image] at hmem
    obtain ⟨A, _hA, hAeq⟩ := hmem
    have hprime : ∀ p ∈ d.primeFactors,
        n ^ 2 + u ≡ v * n [MOD p] := by
      intro p hp
      let p' : ↑d.primeFactors := ⟨p, hp⟩
      have hmodD : n ≡ quadraticAssignmentResidue u v d A [MOD d] := by
        change n % d = quadraticAssignmentResidue u v d A % d
        rw [Nat.mod_eq_of_lt (quadraticAssignmentResidue_lt hd A)]
        exact hAeq.symm
      have hmodP : n ≡ (A p' : ℕ) [MOD p] :=
        (hmodD.of_dvd (Nat.dvd_of_mem_primeFactors hp)).trans
          (quadraticAssignmentResidue_mod u v d A p')
      have hroot :
          (A p' : ℕ) ^ 2 + u ≡ v * (A p' : ℕ) [MOD p] :=
        (mem_quadraticRootResidues_iff.mp (A p').property).2
      exact quadratic_modEq_of_modEq hmodP hroot
    have hprod :
        n ^ 2 + u ≡ v * n [MOD ∏ p ∈ d.primeFactors, p] := by
      rw [Erdos387.modEq_prod_primeFactors_iff]
      exact hprime
    simpa only [Nat.prod_primeFactors_of_squarefree hd] using hprod

end Erdos822
