import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Chapter VII, Section 9: finite quotient reductions

The proof of the existence theorem repeatedly uses elementary facts about
nested finite-index subgroups and quotients of exponent `p`.  These facts are
independent of the missing idelic norm-group and Kummer-theory interfaces and
are recorded here exactly.

Lemma 9.1 and Theorem 9.5 additionally identify the relevant subgroups with
norm groups via global reciprocity and Galois correspondence.  Proposition
9.2 and Lemmas 9.3--9.4 require the local-global power theorem, Kummer
extensions, and idele norm maps, so those arithmetic conclusions are not
asserted here.
-/

namespace Towers.CField.NLimita

variable {C : Type*} [CommGroup C]

/-- The index factorization used throughout Lemma 9.1 and the induction in
Theorem 9.5. -/
theorem nested_index_factorization
    (U V : Subgroup C) (hUV : U ≤ V) :
    U.relIndex V * V.index = U.index :=
  Subgroup.relIndex_mul_index hUV

/-- If `C/V` is killed by `p`, every `p`th power in `C` belongs to `V`.
This is the group-theoretic containment used in Lemma 9.3. -/
theorem pow_quotient_exponent
    (V : Subgroup C) (p : ℕ)
    (hexp : ∀ q : C ⧸ V, q ^ p = 1) (x : C) :
    x ^ p ∈ V := by
  rw [← QuotientGroup.eq_one_iff]
  simpa using hexp (QuotientGroup.mk' V x)

/-- Conversely, containment of all `p`th powers in `V` says exactly that the
quotient is killed by `p`. -/
theorem quotient_exponent_pow
    (V : Subgroup C) (p : ℕ)
    (hpow : ∀ x : C, x ^ p ∈ V) :
    ∀ q : C ⧸ V, q ^ p = 1 := by
  intro q
  induction q using Quotient.inductionOn with
  | _ x =>
      change QuotientGroup.mk' V (x ^ p) = 1
      exact (QuotientGroup.eq_one_iff _).2 (hpow x)

end Towers.CField.NLimita
