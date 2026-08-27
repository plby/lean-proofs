/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAssignmentRecovery
import Lean.Elab.Tactic.Omega

/-!
# The complete finite prime universe for the common coefficients

All primes up to `R` outside the forbidden modulus are included. Every
squarefree coprime tuple with product at most `R` is represented.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def commonPrimeUniverse (M R : ℕ) : Finset ℕ :=
  (Finset.range (R + 1)).filter (fun p => p.Prime ∧ ¬p ∣ M)

theorem mem_commonPrimeUniverse {M R p : ℕ} :
    p ∈ commonPrimeUniverse M R ↔ p.Prime ∧ p ≤ R ∧ ¬p ∣ M := by
  simp only [commonPrimeUniverse, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hR, hp, hM⟩
    exact ⟨hp, by omega, hM⟩
  · rintro ⟨hp, hR, hM⟩
    exact ⟨by omega, hp, hM⟩

theorem commonPrimeUniverse_prime {M R : ℕ} (q : commonPrimeUniverse M R) :
    q.val.Prime := (mem_commonPrimeUniverse.mp q.property).1

theorem commonPrimeUniverse_not_dvd {M R : ℕ} (q : commonPrimeUniverse M R) :
    ¬q.val ∣ M := (mem_commonPrimeUniverse.mp q.property).2.2

theorem commonPrimeUniverse_large {k M R : ℕ}
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ k → p ∣ M) (q : commonPrimeUniverse M R) :
    k < q.val := by
  by_contra hq
  exact commonPrimeUniverse_not_dvd q (hsmall q.val (commonPrimeUniverse_prime q) (by omega))

theorem commonPrimeUniverse_covers_tuple {ι : Type*} [Fintype ι] {M R : ℕ} {r : ι → ℕ}
    (hr : Squarefree (∏ i, r i)) (hcop : (∏ i, r i).Coprime M)
    (hR : (∏ i, r i) ≤ R) :
    AssignmentTupleSupported (fun q : commonPrimeUniverse M R => q.val) r := by
  refine ⟨hr, ?_⟩
  intro l hl hld
  have hlR : l ≤ R := (Nat.le_of_dvd (Nat.pos_of_ne_zero hr.ne_zero) hld).trans hR
  have hlM : ¬l ∣ M := fun hlM => hl.ne_one (Nat.eq_one_of_dvd_coprimes hcop hld hlM)
  exact ⟨⟨l, mem_commonPrimeUniverse.mpr ⟨hl, hlR, hlM⟩⟩, rfl⟩

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonPrimeUniverse_covers_tuple
