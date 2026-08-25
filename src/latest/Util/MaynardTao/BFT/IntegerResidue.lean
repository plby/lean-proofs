import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.GCD

/-! # A natural representative of a coprime integer residue -/

namespace MaynardBFT

theorem exists_nat_coprime_residue {q : ℕ} (hq : 0 < q) (a : ℤ)
    (ha : Int.gcd a (q : ℤ) = 1) :
    ∃ b : ℕ, b.Coprime q ∧ (b : ℤ) ≡ a [ZMOD (q : ℤ)] := by
  let b := (a % (q : ℤ)).toNat
  have hnonneg : 0 ≤ a % (q : ℤ) := Int.emod_nonneg a (by exact_mod_cast hq.ne')
  have hcast : (b : ℤ) = a % (q : ℤ) := Int.toNat_of_nonneg hnonneg
  refine ⟨b, ?_, ?_⟩
  · rw [Nat.coprime_iff_gcd_eq_one, ← Int.gcd_natCast_natCast, hcast, Int.gcd_emod]
    exact ha
  · rw [hcast]
    change (a % (q : ℤ)) % (q : ℤ) = a % (q : ℤ)
    exact Int.emod_emod a q

end MaynardBFT
