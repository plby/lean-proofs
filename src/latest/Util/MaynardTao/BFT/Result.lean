import Util.MaynardTao.BFT.Excess
import Util.MaynardTao.BFT.Isolation
import Util.MaynardTao.BFT.IntervalExtraction
import Util.MaynardTao.BFT.PowerTuple
import Util.MaynardTao.BFT.IntegerResidue

/-!
# Consecutive primes in a coprime residue class with uniform bounded span

The product candidate's dimension is selected from `m` alone.  Multiplying
the power tuple by `q` gives span at most `q * C`.  The enlarged pre-sieve
modulus imposes the requested residue and isolates all primes in that span;
the final extraction uses the exact zero-based `Nat.nth Nat.Prime` indices.
-/

namespace MaynardBFT

open Filter

theorem consecutive_primes :
    ∀ m : ℕ, 0 < m → ∃ C : ℕ, 0 < C ∧ ∀ q : ℕ, 0 < q → ∀ a : ℤ,
      Int.gcd a (q : ℤ) = 1 →
      ∀ N : ℕ, ∃ r : ℕ, N ≤ r ∧
        (∀ j, j < m → (Nat.nth Nat.Prime (r + j) : ℤ) ≡ a [ZMOD (q : ℤ)]) ∧
        Nat.nth Nat.Prime (r + m - 1) - Nat.nth Nat.Prime r ≤ q * C := by
  intro m hm
  letI P : Sieve.Parameters := Sieve.parametersOfLength m hm
  let K := Sieve.largeK
  let C := 2 ^ K
  have hC : 0 < C := pow_pos (by norm_num) K
  refine ⟨C, hC, ?_⟩
  intro q hq a ha N
  letI T : Sieve.ShiftTuple := {
    shifts := powerTuple K q
    card_shifts := powerTuple_card K hq }
  let H := Sieve.largePowerTuple
  let M := q * C
  obtain ⟨b, hb, hba⟩ := exists_nat_coprime_residue hq a ha
  have hH : BoundedGaps.IsAdmissible H := powerTuple_admissible K q
  have hdiv : ∀ h ∈ H, q ∣ h := fun _ hh => powerTuple_divisible hh
  have hbound : ∀ h ∈ H, h ≤ M := fun _ hh => powerTuple_le_span hh
  have hpos : ∀ h ∈ H, 0 < h := fun _ hh => powerTuple_pos hq hh
  have hqM : q ≤ M := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left q (Nat.succ_le_iff.mpr hC)
  have hdata := eventually_isolationResidue_data hq hb hH hdiv hbound hqM
  let v := isolationResidue H q b M
  have hv : ∀ᶠ N' : ℕ in atTop, ∀ h ∈ H,
      Nat.Coprime (v N' + h) (progressionModulus q N') :=
    hdata.mono fun _ hN' => hN'.2.1
  have hA : 1024 * ((m - 1 : ℕ) : ℝ) ≤ Sieve.largeA := by
    change 1024 * ((m - 1 : ℕ) : ℝ) ≤ 1024 * (m : ℝ)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le m 1) (by norm_num)
  have hexcess := Sieve.eventually_progression_excess_pos hq v hv
    (Nat.cast_nonneg (m - 1)) hA
  obtain ⟨n, hnlate, hcount, hnmod, hisolated⟩ :=
    isolated_clusters_of_eventually_positive_excess hdata hexcess (Nat.nth Nat.Prime N)
  have hnresidue : (n : ℤ) ≡ a [ZMOD (q : ℤ)] :=
    (Int.natCast_modEq_iff.mpr hnmod).trans hba
  exact consecutive_run_of_isolated_tuple hm (by omega) hpos hbound hcount
    hnresidue hdiv hisolated (le_refl M)

end MaynardBFT

#print axioms MaynardBFT.consecutive_primes
-- 'MaynardBFT.consecutive_primes' depends on axioms: [propext, Classical.choice, Quot.sound]
