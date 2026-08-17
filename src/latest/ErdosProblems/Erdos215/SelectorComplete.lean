/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.SelectorConflictRoot
import ErdosProblems.Erdos215.SelectorReconstruct

/-!
The canonical complete list of primary components of a nonzero denominator.

For every prime in `d.primeFactors` we retain its full power in `d`; its
complement is `ordCompl[p] d`.  Mathlib's factorization product and pairwise
coprimality theorems then give precisely the `CompleteComponents` package
used by the selector reconstruction.
-/

namespace Erdos215.Selector.Complete

open Erdos215.Selector.Modular
open Erdos215.Selector.Final
open Erdos215.Selector.Separation

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The full primary component of `d` indexed by a prime factor of `d`. -/
def canonicalPrimaryComponent (d : ℕ) (hd : d ≠ 0)
    (p : d.primeFactors) : PrimaryComponent d where
  p := p
  a := d.factorization p
  D := ordCompl[(p : ℕ)] d
  prime := Nat.prime_of_mem_primeFactors p.2
  exp_pos := (Nat.prime_of_mem_primeFactors p.2).factorization_pos_of_dvd hd
    (Nat.dvd_of_mem_primeFactors p.2)
  factor := (Nat.ordProj_mul_ordCompl_eq_self d p).symm
  coprime := (Nat.coprime_ordCompl (Nat.prime_of_mem_primeFactors p.2) hd).pow_left _

@[simp] theorem canonicalPrimaryComponent_q (d : ℕ) (hd : d ≠ 0)
    (p : d.primeFactors) :
    (canonicalPrimaryComponent d hd p).q =
      (p : ℕ) ^ d.factorization p := rfl

/-- The primary components, in the canonical order inherited from the finite
set of prime factors. -/
def canonicalComponentList (d : ℕ) (hd : d ≠ 0) :
    List (PrimaryComponent d) :=
  (Finset.univ : Finset d.primeFactors).toList.map
    (canonicalPrimaryComponent d hd)

/-- Every nonzero natural has a canonical complete primary decomposition. -/
def canonicalCompleteComponents (d : ℕ) (hd : d ≠ 0) :
    CompleteComponents d where
  components := canonicalComponentList d hd
  pairwise := by
    rw [canonicalComponentList, List.pairwise_map]
    apply List.Nodup.pairwise_of_forall_ne (Finset.nodup_toList _)
    intro p hp q hq hpq
    simpa only [canonicalPrimaryComponent_q] using
      d.pairwise_coprime_pow_primeFactors_factorization hpq
  product_eq := by
    simp only [canonicalComponentList, List.map_map, Finset.prod_map_toList,
      Function.comp_apply, canonicalPrimaryComponent_q]
    exact (Nat.prod_primeFactors_coe_pow_factorization hd).symm

/-- Membership in the canonical list remembers the prime-factor index from
which the component was built. -/
theorem mem_canonicalComponentList_iff {d : ℕ} {hd : d ≠ 0}
    (c : PrimaryComponent d) :
    c ∈ canonicalComponentList d hd ↔
      ∃ p : d.primeFactors, canonicalPrimaryComponent d hd p = c := by
  simp [canonicalComponentList]

/-- A hypothesis on all prime divisors of `d` transfers to every prime in
the canonical primary decomposition. -/
theorem canonical_component_mod_four_eq_one {d : ℕ} (hd : d ≠ 0)
    (hp1 : ∀ p : ℕ, p.Prime → p ∣ d → p % 4 = 1)
    (c : PrimaryComponent d)
    (hc : c ∈ (canonicalCompleteComponents d hd).components) :
    c.p % 4 = 1 := by
  change c ∈ canonicalComponentList d hd at hc
  obtain ⟨p, rfl⟩ := (mem_canonicalComponentList_iff
    (hd := hd) c).mp hc
  exact hp1 p (Nat.prime_of_mem_primeFactors p.2)
    (Nat.dvd_of_mem_primeFactors p.2)

/-- Complete `1 mod 4` primary data in particular supplies a global root of
`-1`.  This public wrapper avoids exposing the private CRT implementation in
`SelectorConflictRoot`: apply its full-conflict conclusion to the zero
quadruple. -/
theorem root_nonempty_of_complete {d : ℕ} (hd : d ≠ 0)
    (C : CompleteComponents d)
    (hp1 : ∀ c ∈ C.components, c.p % 4 = 1) : Nonempty (Root d) := by
  have hrootLine :=
    ConflictRoot.conflictRootLineProperty_of_complete hd C hp1
  obtain ⟨lam, _⟩ := hrootLine 0 0 0 0 (by simp)
  exact ⟨lam⟩

/-- The canonical decomposition supplies the full-conflict root-line
property when every prime divisor is `1 mod 4`. -/
theorem canonical_conflictRootLineProperty {d : ℕ} (hd : d ≠ 0)
    (hp1 : ∀ p : ℕ, p.Prime → p ∣ d → p % 4 = 1) :
    ConflictRootLineProperty d :=
  ConflictRoot.conflictRootLineProperty_of_complete hd
    (canonicalCompleteComponents d hd)
    (canonical_component_mod_four_eq_one hd hp1)

/-- Canonical global root existence for a pure nontrivial denominator. -/
theorem canonical_root_nonempty {d : ℕ} (hd : d ≠ 0)
    (hp1 : ∀ p : ℕ, p.Prime → p ∣ d → p % 4 = 1) :
    Nonempty (Root d) :=
  root_nonempty_of_complete hd (canonicalCompleteComponents d hd)
    (canonical_component_mod_four_eq_one hd hp1)

/-- Canonical pure-nontrivial reconstruction: a good consistent family over
an odd denominator all of whose prime divisors are `1 mod 4` is induced by
separated integral lift data. -/
theorem exists_separated_liftData_of_good_consistent
    {d : ℕ} (hd : d ≠ 0) (hodd : Nat.Coprime 2 d)
    (hp1 : ∀ p : ℕ, p.Prime → p ∣ d → p % 4 = 1)
    (F : RawLineFamily d) (hgood : FamilyGood F)
    (hcons : FamilyConsistent F) (lam₀ : Root d) :
    ∃ s : LiftData d, inducedFamily hd s = F ∧ s.Separated :=
  Reconstruct.exists_separated_liftData_of_good_consistent hd hodd
    (canonicalCompleteComponents d hd)
    (canonical_conflictRootLineProperty hd hp1)
    F hgood hcons lam₀

end

end Erdos215.Selector.Complete
