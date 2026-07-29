import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import PrivateName

attribute [local instance] Classical.propDecidable

axiom shiu_consecutive_primes
    (l : ℕ) (hl : 1 ≤ l) (a q : ℕ) (hq : 1 ≤ q) (haq : Nat.Coprime a q) (N : ℕ) :
    ∃ m, N ≤ m ∧ ∀ i, i < l → Nat.nth Nat.Prime (m + i) ≡ a [MOD q]

noncomputable abbrev _private.ErdosProblems.Erdos427.«0».Erdos427.nthPrime :
    Nat → Nat :=
  Nat.nth Nat.Prime

comparator_copy_declaration
  _private.ErdosProblems.Erdos427.«0».Erdos427.nthPrime
  as "_private.ErdosProblems.Erdos427.0.Erdos427.nthPrime"

theorem Erdos427.erdos427 :
    ∀ (n d : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d →
        @Exists.{1} Nat fun (k : Nat) ↦
          And (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
            (@Dvd.dvd.{0} Nat Nat.instDvd d
              (@Finset.sum.{0, 0} Nat Nat Nat.instAddCommMonoid (Finset.range k) fun (i : Nat) ↦
                (comparator_private_ref
                  "_private.ErdosProblems.Erdos427.0.Erdos427.nthPrime")
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n i)))
  := by
  sorry
