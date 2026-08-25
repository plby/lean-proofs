import Util.MaynardBFT.Extraction
import BoundedGaps.Proof.TupleBridge
import Mathlib.Tactic

/-! # From isolated prime shifts to the exact BFT prime indices -/

namespace MaynardBFT

theorem interval_prime_count_ge_of_shiftCount
    {H : Finset ℕ} {m n M : ℕ}
    (hpos : ∀ h ∈ H, 0 < h) (hbound : ∀ h ∈ H, h ≤ M)
    (hcount : m ≤ BoundedGaps.primeShiftCount H n) :
    m ≤ ((Finset.Icc (n + 1) (n + M)).filter Nat.Prime).card := by
  have hinj : (H.filter fun h => (n + h).Prime).card ≤
      ((Finset.Icc (n + 1) (n + M)).filter Nat.Prime).card := by
    apply Finset.card_le_card_of_injOn (fun h => n + h)
    · intro h hh
      obtain ⟨hhH, hprime⟩ := Finset.mem_filter.mp hh
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hprime⟩
      · have := hpos h hhH
        dsimp only
        omega
      · exact Nat.add_le_add_left (hbound h hhH) n
    · intro a ha b hb hab
      dsimp only at hab
      omega
  exact hcount.trans hinj

theorem consecutive_run_of_isolated_tuple
    {H : Finset ℕ} {m q C N n M : ℕ} {a : ℤ}
    (hm : 0 < m) (hlate : Nat.nth Nat.Prime N ≤ n + 1)
    (hpos : ∀ h ∈ H, 0 < h) (hbound : ∀ h ∈ H, h ≤ M)
    (hcount : m ≤ BoundedGaps.primeShiftCount H n)
    (hresidue : (n : ℤ) ≡ a [ZMOD (q : ℤ)])
    (hdiv : ∀ h ∈ H, q ∣ h)
    (hisolated : ∀ p, n < p → p ≤ n + M → p.Prime → ∃ h ∈ H, p = n + h)
    (hspan : M ≤ q * C) :
    ∃ r : ℕ, N ≤ r ∧
      (∀ j, j < m → (Nat.nth Nat.Prime (r + j) : ℤ) ≡ a [ZMOD (q : ℤ)]) ∧
      Nat.nth Nat.Prime (r + m - 1) - Nat.nth Nat.Prime r ≤ q * C := by
  apply consecutive_run_of_interval hm hlate
    (interval_prime_count_ge_of_shiftCount hpos hbound hcount)
  · intro p hp hprime
    have hpI := Finset.mem_Icc.mp hp
    obtain ⟨h, hh, rfl⟩ := hisolated p (by omega) hpI.2 hprime
    have hhmod : (h : ℤ) ≡ 0 [ZMOD (q : ℤ)] :=
      Int.modEq_zero_iff_dvd.mpr (by exact_mod_cast hdiv h hh)
    simpa only [Nat.cast_add, Int.add_zero] using hresidue.add hhmod
  · omega

end MaynardBFT
