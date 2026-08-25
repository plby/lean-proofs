import ErdosProblems.Erdos964.CharacterReduction
import ErdosProblems.Erdos964.SemiprimeDistribution

/-!
# Recovering prime character sums from progression counts

For logarithmic conductors, the polynomial loss from summing the residue
classes can be absorbed by taking a stronger logarithmic saving in the
existing prime-distribution theorem. This avoids redoing partial summation.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

theorem finiteCharacterSum_residue_expansion (S : Finset ℕ) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    finiteCharacterSum S q χ =
      ∑ a : ZMod q, χ a * (finiteResidueCount S q a.val : ℂ) := by
  classical
  have hfilter (a : ZMod q) : S.filter (fun (n : ℕ) => (n : ZMod q) = a) =
      S.filter (fun n => n ≡ a.val [MOD q]) := by
    ext n
    simp only [Finset.mem_filter, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  calc
    _ = ∑ a : ZMod q, ∑ n ∈ S.filter (fun (n : ℕ) => (n : ZMod q) = a), χ a :=
      (Finset.sum_fiberwise' S (fun (n : ℕ) => (n : ZMod q)) χ).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hfilter]
      simp only [finiteResidueCount, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- Any constant may be subtracted inside the residue expansion of a
nonprincipal character; its complete residue sum vanishes. -/
theorem finiteCharacterSum_centered_residue_expansion (S : Finset ℕ) {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (c : ℂ) :
    finiteCharacterSum S q χ =
      ∑ a : ZMod q, χ a * ((finiteResidueCount S q a.val : ℂ) - c) := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← finiteCharacterSum_residue_expansion S χ, ← Finset.sum_mul,
    MulChar.sum_eq_zero_of_ne_one hχ, zero_mul, sub_zero]

/-- A finite nonprincipal character sum is bounded by the modulus times a
uniform discrepancy bound over the reduced residue classes. -/
theorem norm_finiteCharacterSum_le_modulus_mul (S : Finset ℕ) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (c B : ℝ) (hB : 0 ≤ B)
    (herror : ∀ a : ℕ, a < q → a.Coprime q →
      |(finiteResidueCount S q a : ℝ) - c| ≤ B) :
    ‖finiteCharacterSum S q χ‖ ≤ q * B := by
  classical
  rw [finiteCharacterSum_centered_residue_expansion S χ hχ (c : ℂ)]
  calc
    _ ≤ ∑ a : ZMod q, ‖χ a * ((finiteResidueCount S q a.val : ℂ) - (c : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _a : ZMod q, B := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases hunit : IsUnit a
      · have hcop : a.val.Coprime q := by
          have hcast : IsUnit (a.val : ZMod q) := by simpa only [ZMod.natCast_zmod_val] using hunit
          simpa only [ZMod.isUnit_iff_coprime] using hcast
        have hnorm : ‖(finiteResidueCount S q a.val : ℂ) - (c : ℂ)‖ ≤ B := by
          have hcast : (((finiteResidueCount S q a.val : ℝ) - c : ℝ) : ℂ) =
              (finiteResidueCount S q a.val : ℂ) - (c : ℂ) := by push_cast; rfl
          rw [← hcast, Complex.norm_real, Real.norm_eq_abs]
          exact herror a.val a.val_lt hcop
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one a)).trans hnorm
      · rw [MulChar.map_nonunit χ hunit, zero_mul, norm_zero]
        exact hB
    _ = _ := by simp

theorem finiteResidueCount_primesLE (x q a : ℕ) :
    finiteResidueCount x.primesLE q a = primeCountUpTo x q a := by
  classical
  unfold finiteResidueCount primeCountUpTo
  apply congrArg Finset.card
  apply Finset.ext
  intro n
  constructor
  · intro hn
    obtain ⟨hnprime, hnmod⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnle, hp⟩ := Nat.mem_primesLE.mp hnprime
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp, hnmod⟩
  · intro hn
    obtain ⟨hnrange, hp, hnmod⟩ := Finset.mem_filter.mp hn
    have hnle : n ≤ x := by have := Finset.mem_range.mp hnrange; omega
    exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hnle, hp⟩, hnmod⟩

/-- Prime character sums inherit arbitrary logarithmic savings from the
prime-counting distribution theorem at small moduli. -/
theorem norm_primeCharacterSum_le_progressionDiscrepancy (x : ℕ) {q : ℕ}
    (hq : 0 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ‖finiteCharacterSum x.primesLE q χ‖ ≤ (q : ℝ) * maxProgressionDiscrepancy x q := by
  let : NeZero q := ⟨hq.ne'⟩
  apply norm_finiteCharacterSum_le_modulus_mul x.primesLE χ hχ
    ((primeCountTotal x : ℝ) / q.totient) _ (maxProgressionDiscrepancy_nonneg x q)
  intro a ha hcop
  rw [finiteResidueCount_primesLE]
  exact progressionDiscrepancy_le_max_of_coprime x q a hq hcop

theorem finiteCharacterSum_primeInterval (l u : ℕ) (hlu : l ≤ u) (q : ℕ)
    (χ : DirichletCharacter ℂ q) :
    finiteCharacterSum ((Finset.Ioc l u).filter Nat.Prime) q χ =
      finiteCharacterSum u.primesLE q χ - finiteCharacterSum l.primesLE q χ := by
  have hinterval : Finset.Ioc l u = Finset.Ico (l + 1) (u + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  simp only [finiteCharacterSum, Nat.primesLE_eq_filter_range, Finset.sum_filter]
  rw [hinterval]
  exact Finset.sum_Ico_eq_sub _ (by omega)

theorem norm_primeIntervalCharacterSum_le_progressionDiscrepancy (l u : ℕ)
    (hlu : l ≤ u) {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ‖finiteCharacterSum ((Finset.Ioc l u).filter Nat.Prime) q χ‖ ≤
      (q : ℝ) * (maxProgressionDiscrepancy u q + maxProgressionDiscrepancy l q) := by
  rw [finiteCharacterSum_primeInterval l u hlu q χ]
  calc
    _ ≤ ‖finiteCharacterSum u.primesLE q χ‖ + ‖finiteCharacterSum l.primesLE q χ‖ := norm_sub_le _ _
    _ ≤ (q : ℝ) * maxProgressionDiscrepancy u q + (q : ℝ) * maxProgressionDiscrepancy l q :=
      add_le_add (norm_primeCharacterSum_le_progressionDiscrepancy u hq χ hχ)
        (norm_primeCharacterSum_le_progressionDiscrepancy l hq χ hχ)
    _ = _ := by ring

end Erdos964
