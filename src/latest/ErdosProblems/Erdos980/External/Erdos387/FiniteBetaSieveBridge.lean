/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos980.External.Erdos387.LevelSupportedSieve
import ErdosProblems.Erdos851.FiniteSieveApplication

/-!
# A level-preserving finite beta-sieve bridge for Erdős 387

The generic Rosser application in `Erdos851.FiniteSieveApplication` bounds
all admissible remainders by `D ^ 2`.  At the lower sieve level used by BNPZ,
`D = X ^ (1 / 2)`, that deliberately coarse estimate is not useful.  The
binomial congruence problem has the sharper individual remainder
`4 * k ^ omega(d)`.  This file retains that information while summing the
Rosser chains, giving a loss of size

`4 * D * product_{p in P} (1 + k / p)`.

This is precisely the endpoint estimate needed by a beta-sieve whose
coefficients are supported on products at most `D`; in particular no
`z ^ L` support loss occurs.
-/

open scoped BigOperators

namespace Erdos387.FiniteBetaSieveBridge

open Erdos851.FiniteCombinatorialSieve
open Erdos851.FiniteSieveApplication

private theorem sum_sublists_cons (f : List ℕ → ℝ) (p : ℕ) (P : List ℕ) :
    ((p :: P).sublists.map f).sum =
      (P.sublists.map f).sum + (P.sublists.map fun s => f (p :: s)).sum := by
  have hp := (List.sublists_cons_perm_append p P).map f
  simpa [List.map_append, Function.comp_def] using hp.sum_eq

/-- The harmonic generating function of all squarefree subproducts of a
list.  This list form is convenient for the Rosser-chain implementation. -/
theorem sum_sublists_pow_length_div_prod_eq_prod_one_add
    (k : ℕ) (P : List ℕ) :
    (P.sublists.map fun t => (k : ℝ) ^ t.length / (t.prod : ℝ)).sum =
      (P.map fun p => 1 + (k : ℝ) / p).prod := by
  induction P with
  | nil => simp
  | cons p P ih =>
      rw [sum_sublists_cons]
      change
        (P.sublists.map fun t => (k : ℝ) ^ t.length / (t.prod : ℝ)).sum +
            (P.sublists.map fun s =>
              (k : ℝ) ^ (p :: s).length / ((p :: s).prod : ℝ)).sum =
          (1 + (k : ℝ) / p) *
            (P.map fun q => 1 + (k : ℝ) / q).prod
      have hfactor :
          (P.sublists.map fun s =>
              (k : ℝ) ^ (p :: s).length / ((p :: s).prod : ℝ)).sum =
            ((k : ℝ) / p) *
              (P.sublists.map fun s =>
                (k : ℝ) ^ s.length / (s.prod : ℝ)).sum := by
        calc
          (P.sublists.map fun s =>
              (k : ℝ) ^ (p :: s).length / ((p :: s).prod : ℝ)).sum =
              (P.sublists.map fun s =>
                ((k : ℝ) / p) *
                  ((k : ℝ) ^ s.length / (s.prod : ℝ))).sum := by
            congr 1
            apply List.map_congr_left
            intro s hs
            simp only [List.length_cons, List.prod_cons, Nat.cast_mul, pow_succ']
            ring
          _ = ((k : ℝ) / p) *
              (P.sublists.map fun s =>
                (k : ℝ) ^ s.length / (s.prod : ℝ)).sum := by
            rw [List.sum_map_mul_left]
      rw [hfactor, ih]
      ring

/-- Summing an endpoint remainder `C * k ^ |t|` over level-supported
admissible chains costs only `C * D` times the full harmonic Euler product. -/
theorem admissibleRemainderAbs_le_level_mul_euler
    (P : List ℕ) (Adm : List ℕ → Prop) (R : List ℕ → ℝ)
    (C : ℝ) (k D : ℕ)
    (hC : 0 ≤ C)
    (hprime : ∀ p ∈ P, p.Prime)
    (hsupport : ∀ t ∈ P.sublists, Adm t → t.prod ≤ D)
    (hrem : ∀ t ∈ P.sublists, Adm t →
      |R t| ≤ C * (k : ℝ) ^ t.length) :
    admissibleRemainderAbs Adm R P ≤
      C * D * (P.map fun p => 1 + (k : ℝ) / p).prod := by
  classical
  unfold admissibleRemainderAbs
  calc
    (P.sublists.map fun t => if Adm t then |R t| else 0).sum ≤
        (P.sublists.map fun t =>
          C * D * ((k : ℝ) ^ t.length / (t.prod : ℝ))).sum := by
      apply List.sum_le_sum
      intro t ht
      by_cases hadm : Adm t
      · rw [if_pos hadm]
        have htsub := List.mem_sublists.mp ht
        have htprime : ∀ p ∈ t, p.Prime := by
          intro p hp
          exact hprime p (htsub.subset hp)
        have htprodPos : 0 < t.prod := by
          apply List.prod_pos
          intro p hp
          exact (htprime p hp).pos
        have hprodD : (t.prod : ℝ) ≤ D := by
          exact_mod_cast hsupport t ht hadm
        have hkpow : 0 ≤ (k : ℝ) ^ t.length := by positivity
        calc
          |R t| ≤ C * (k : ℝ) ^ t.length := hrem t ht hadm
          _ ≤ C * D * ((k : ℝ) ^ t.length / (t.prod : ℝ)) := by
            rw [show C * D * ((k : ℝ) ^ t.length / (t.prod : ℝ)) =
                C * (k : ℝ) ^ t.length *
                  ((D : ℝ) / (t.prod : ℝ)) by ring]
            have hratio : 1 ≤ (D : ℝ) / (t.prod : ℝ) :=
              (le_div_iff₀ (by exact_mod_cast htprodPos)).mpr (by simpa using hprodD)
            exact le_mul_of_one_le_right (mul_nonneg hC hkpow) hratio
      · rw [if_neg hadm]
        positivity
    _ = C * D *
        (P.sublists.map fun t =>
          (k : ℝ) ^ t.length / (t.prod : ℝ)).sum := by
      rw [List.sum_map_mul_left]
    _ = C * D * (P.map fun p => 1 + (k : ℝ) / p).prod := by
      rw [sum_sublists_pow_length_div_prod_eq_prod_one_add]

/-- Lower Rosser application retaining the true endpoint remainder instead
of replacing it by the generic `D ^ 2` bound. -/
theorem boundingSieve_lowerMain_sub_levelEuler_le_siftedSum
    (s : BoundingSieve) (P : List ℕ) (A : List ℕ → Prop)
    (C : ℝ) (k D : ℕ)
    (hprod : P.prod = s.prodPrimes)
    (hnodup : P.Nodup) (hprime : ∀ p ∈ P, p.Prime)
    (hsupport : ∀ t ∈ P.sublists, LowerAdmissible A t → t.prod ≤ D)
    (hrem : ∀ d : ℕ, d ∣ s.prodPrimes →
      |s.rem d| ≤ C * (k : ℝ) ^ d.primeFactors.card)
    (hC : 0 ≤ C) :
    s.totalMass * lowerMainTerm A (fun p => s.nu p) P -
        C * D * (P.map fun p => 1 + (k : ℝ) / p).prod ≤
      s.siftedSum := by
  have happrox : ∀ t ∈ P.sublists,
      intersectionMass s.support s.weights (fun n p => p ∣ n) t =
        s.totalMass * chainWeight (fun p => s.nu p) t + s.rem t.prod := by
    intro t ht
    have htsub := List.mem_sublists.mp ht
    have htnodup := hnodup.sublist htsub
    have htprime : ∀ p ∈ t, p.Prime := by
      intro p hp
      exact hprime p (htsub.subset hp)
    rw [intersectionMass_dvd_eq_multSum s t htnodup htprime,
      s.multSum_eq_main_err, nu_prod_eq_chainWeight s t htnodup htprime]
    ring
  have hbase := lowerMain_sub_remainder_le_siftedMass
    s.support s.weights s.weights_nonneg (fun n p => p ∣ n) A
    (fun p => s.nu p) s.totalMass (fun t => s.rem t.prod) P happrox
  have herror :
      admissibleRemainderAbs (LowerAdmissible A) (fun t => s.rem t.prod) P ≤
        C * D * (P.map fun p => 1 + (k : ℝ) / p).prod := by
    apply admissibleRemainderAbs_le_level_mul_euler P (LowerAdmissible A)
      (fun t => s.rem t.prod) C k D hC hprime hsupport
    intro t ht hadm
    have htsub := List.mem_sublists.mp ht
    have htnodup := hnodup.sublist htsub
    have htprime : ∀ p ∈ t, p.Prime := by
      intro p hp
      exact hprime p (htsub.subset hp)
    have hpf : t.prod.primeFactors = t.toFinset := by
      have htprod : t.toFinset.prod id = t.prod := by
        simpa using List.prod_toFinset id htnodup
      rw [← htprod]
      simpa using Nat.primeFactors_prod
        (s := t.toFinset) (fun p hp => htprime p (List.mem_toFinset.mp hp))
    have hcard : t.prod.primeFactors.card = t.length := by
      rw [hpf, List.toFinset_card_of_nodup htnodup]
    rw [← hcard]
    apply hrem t.prod
    rw [← hprod]
    exact htsub.prod_dvd_prod
  have hsift := siftedMass_dvd_eq_siftedSum s P hprod hprime
  rw [hsift] at hbase
  linarith

/-- Upper counterpart of
`boundingSieve_lowerMain_sub_levelEuler_le_siftedSum`. -/
theorem boundingSieve_siftedSum_le_upperMain_add_levelEuler
    (s : BoundingSieve) (P : List ℕ) (A : List ℕ → Prop)
    (C : ℝ) (k D : ℕ)
    (hprod : P.prod = s.prodPrimes)
    (hnodup : P.Nodup) (hprime : ∀ p ∈ P, p.Prime)
    (hsupport : ∀ t ∈ P.sublists, UpperAdmissible A t → t.prod ≤ D)
    (hrem : ∀ d : ℕ, d ∣ s.prodPrimes →
      |s.rem d| ≤ C * (k : ℝ) ^ d.primeFactors.card)
    (hC : 0 ≤ C) :
    s.siftedSum ≤
      s.totalMass * upperMainTerm A (fun p => s.nu p) P +
        C * D * (P.map fun p => 1 + (k : ℝ) / p).prod := by
  have happrox : ∀ t ∈ P.sublists,
      intersectionMass s.support s.weights (fun n p => p ∣ n) t =
        s.totalMass * chainWeight (fun p => s.nu p) t + s.rem t.prod := by
    intro t ht
    have htsub := List.mem_sublists.mp ht
    have htnodup := hnodup.sublist htsub
    have htprime : ∀ p ∈ t, p.Prime := by
      intro p hp
      exact hprime p (htsub.subset hp)
    rw [intersectionMass_dvd_eq_multSum s t htnodup htprime,
      s.multSum_eq_main_err, nu_prod_eq_chainWeight s t htnodup htprime]
    ring
  have hbase := siftedMass_le_upperMain_add_remainder
    s.support s.weights s.weights_nonneg (fun n p => p ∣ n) A
    (fun p => s.nu p) s.totalMass (fun t => s.rem t.prod) P happrox
  have herror :
      admissibleRemainderAbs (UpperAdmissible A) (fun t => s.rem t.prod) P ≤
        C * D * (P.map fun p => 1 + (k : ℝ) / p).prod := by
    apply admissibleRemainderAbs_le_level_mul_euler P (UpperAdmissible A)
      (fun t => s.rem t.prod) C k D hC hprime hsupport
    intro t ht hadm
    have htsub := List.mem_sublists.mp ht
    have htnodup := hnodup.sublist htsub
    have htprime : ∀ p ∈ t, p.Prime := by
      intro p hp
      exact hprime p (htsub.subset hp)
    have hpf : t.prod.primeFactors = t.toFinset := by
      have htprod : t.toFinset.prod id = t.prod := by
        simpa using List.prod_toFinset id htnodup
      rw [← htprod]
      simpa using Nat.primeFactors_prod
        (s := t.toFinset) (fun p hp => htprime p (List.mem_toFinset.mp hp))
    have hcard : t.prod.primeFactors.card = t.length := by
      rw [hpf, List.toFinset_card_of_nodup htnodup]
    rw [← hcard]
    apply hrem t.prod
    rw [← hprod]
    exact htsub.prod_dvd_prod
  have hsift := siftedMass_dvd_eq_siftedSum s P hprod hprime
  rw [hsift] at hbase
  linarith

/-- Turn the generic lower endpoint theorem into a Rosser beta-sieve bound.
All coefficient and support bookkeeping is discharged here; only a lower
bound for the displayed stopped main term remains analytic. -/
theorem boundingSieve_rosserLowerMain_sub_levelEuler_le_siftedSum
    (s : BoundingSieve) (P : List ℕ) (C : ℝ) (k β D : ℕ)
    (hprod : P.prod = s.prodPrimes)
    (hsort : P.Pairwise (· ≤ ·)) (hnodup : P.Nodup)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : ∀ p ∈ P, p ≤ D)
    (hβ : 1 ≤ β) (hD : 1 ≤ D)
    (hrem : ∀ d : ℕ, d ∣ s.prodPrimes →
      |s.rem d| ≤ C * (k : ℝ) ^ d.primeFactors.card)
    (hC : 0 ≤ C) :
    s.totalMass *
          lowerMainTerm (rosserStoppingPredicate β D) (fun p => s.nu p) P -
        C * D * (P.map fun p => 1 + (k : ℝ) / p).prod ≤
      s.siftedSum := by
  apply boundingSieve_lowerMain_sub_levelEuler_le_siftedSum
    s P (rosserStoppingPredicate β D) C k D hprod hnodup hprime
  · intro t ht hadm
    have hsub := List.mem_sublists.mp ht
    exact prod_le_of_lowerAdmissible_rosserStoppingPredicate hβ hD
      (hsort.sublist hsub)
      (fun p hp => (hprime p (hsub.subset hp)).one_le)
      (fun p hp => hlevel p (hsub.subset hp)) hadm
  · exact hrem
  · exact hC

/-- Upper Rosser beta-sieve bound with the same level-preserving endpoint
loss.  Unlike the lower odd-chain case, its support proof needs no separate
prime-by-prime `p ≤ D` hypothesis. -/
theorem boundingSieve_siftedSum_le_rosserUpperMain_add_levelEuler
    (s : BoundingSieve) (P : List ℕ) (C : ℝ) (k β D : ℕ)
    (hprod : P.prod = s.prodPrimes)
    (hsort : P.Pairwise (· ≤ ·)) (hnodup : P.Nodup)
    (hprime : ∀ p ∈ P, p.Prime)
    (hβ : 1 ≤ β) (hD : 1 ≤ D)
    (hrem : ∀ d : ℕ, d ∣ s.prodPrimes →
      |s.rem d| ≤ C * (k : ℝ) ^ d.primeFactors.card)
    (hC : 0 ≤ C) :
    s.siftedSum ≤
      s.totalMass *
          upperMainTerm (rosserStoppingPredicate β D) (fun p => s.nu p) P +
        C * D * (P.map fun p => 1 + (k : ℝ) / p).prod := by
  apply boundingSieve_siftedSum_le_upperMain_add_levelEuler
    s P (rosserStoppingPredicate β D) C k D hprod hnodup hprime
  · intro t ht hadm
    have hsub := List.mem_sublists.mp ht
    exact prod_le_of_upperAdmissible_rosserStoppingPredicate hβ hD
      (hsort.sublist hsub)
      (fun p hp => (hprime p (hsub.subset hp)).one_le) hadm
  · exact hrem
  · exact hC

end Erdos387.FiniteBetaSieveBridge
