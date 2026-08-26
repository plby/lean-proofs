import ErdosProblems.Erdos117.ClassTwoSharp
import ErdosProblems.Erdos117.ClassTwoReduction
import ErdosProblems.Erdos117.FiniteReduction

/-!
# The unconditional sharp upper bound

The centralizer-triple reduction replaces the general BFC derived-order
estimate from the selected writeup. It gives a class-two subgroup with a
quadratic logarithmic index exponent. The already-proved class-two covers
and polynomial coset extension then apply.
-/

namespace Erdos117

open Filter

universe u

theorem exists_class_two_subgroup_logScale {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : NoncommutingBound G n) :
    ∃ F : Subgroup G, commutator F ≤ Subgroup.center F ∧
      F.index ≤ 2 ^ ((16 * logScale n ^ 2) ^ 2) := by
  obtain ⟨d, F, hd, hF, hindex⟩ := exists_class_two_subgroup_small_index hn
    (fun x => centralizerIndex_le hn x)
  have hdT : d ≤ logScale n :=
    (Nat.le_log_of_pow_le (by decide) hd).trans (floor_log_le_logScale n)
  have hB : (2 * n) ^ 2 ≤ 2 ^ (4 * logScale n) :=
    (Nat.le_pow_clog (by decide) _).trans
      (Nat.pow_le_pow_right (by decide) (conjugacy_clog_le_logScale n))
  have hpow : logScale n ^ 2 ≤ logScale n ^ 4 :=
    Nat.pow_le_pow_right (logScale_pos n) (by decide)
  have hexp : 4 * logScale n * (3 * d) ≤ (16 * logScale n ^ 2) ^ 2 := by
    have hmul := Nat.mul_le_mul_left (12 * logScale n) hdT
    nlinarith
  refine ⟨F, hF, hindex.trans ?_⟩
  calc
    ((2 * n) ^ 2) ^ (3 * d) ≤ (2 ^ (4 * logScale n)) ^ (3 * d) :=
      Nat.pow_le_pow_left hB _
    _ = 2 ^ (4 * logScale n * (3 * d)) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ ((16 * logScale n ^ 2) ^ 2) := Nat.pow_le_pow_right (by decide) hexp

/-- Every finite group with clique bound `n` has an actual cover whose
entire error lies in the proved quadratic logarithmic envelope. -/
theorem exists_finite_cover_logScale {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : NoncommutingBound G n) :
    ∃ K : ℕ, HasAbelianCover G K ∧
      Real.log K ≤ Real.log 2 / 2 * n + finiteCoverError n (16 * logScale n ^ 2) := by
  classical
  let q := 16 * logScale n ^ 2
  let ell := Nat.clog 2 ((2 * n) ^ 2)
  let C := coverExtensionPolynomial n
  obtain ⟨F, hF, hindex⟩ := exists_class_two_subgroup_logScale hn
  obtain ⟨k, hk, hlog⟩ := exists_class_two_cover_logScale hF (hn.subgroup F)
  have hcover : HasAbelianCover G (2 ^ (q ^ 2) * (C * k)) :=
    hasAbelianCover_mono (hasAbelianCover_extension_polynomial F hn hk)
      (Nat.mul_le_mul_right _ hindex)
  have hn1 := one_le_of_noncommutingBound hn
  have hn0 : 0 < n := by omega
  have hC : 0 < C :=
    Nat.mul_pos (Nat.mul_pos (by decide) (pow_pos (Nat.mul_pos (by decide) hn0) _))
      (Nat.succ_pos _)
  have hk1 := one_le_of_noncommutingBound (noncommutingBound_of_abelianCover hk)
  have hC' : (C : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hC)
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hcost : Real.log (2 ^ (q ^ 2) * (C * k) : ℕ) =
      (q : ℝ) ^ 2 * Real.log 2 + Real.log C + Real.log k := by
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.log_mul (pow_ne_zero _ (show (2 : ℝ) ≠ 0 by norm_num)) (mul_ne_zero hC' hk'),
      Real.log_mul hC' hk', Real.log_pow, Nat.cast_pow]
    ring
  refine ⟨2 ^ (q ^ 2) * (C * k), hcover, ?_⟩
  rw [hcost]
  change _ ≤ Real.log 2 / 2 * n + finiteCoverError n q
  unfold finiteCoverError
  dsimp [C, ell] at hlog ⊢
  linarith only [hlog]

/-- The sharp upper estimate for all finite groups, uniformly in the group. -/
theorem finite_sharp_upper :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (G : Type u) [Group G] [Finite G], NoncommutingBound G n →
        ∃ k : ℕ, HasAbelianCover G k ∧
          Real.log k ≤ Real.log 2 / 2 * n +
            C * (Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3) := by
  refine ⟨errorCoefficient 16 * (2 / Real.log 2) ^ 3, ?_, ?_⟩
  · exact mul_nonneg (errorCoefficient_nonneg _) (by positivity)
  filter_upwards [eventually_finiteCoverError_le_log 16] with n hn
  intro G _ _ hG
  obtain ⟨k, hk, hlog⟩ := exists_finite_cover_logScale hG
  have herr := hn (16 * logScale n ^ 2) le_rfl
  refine ⟨k, hk, hlog.trans ?_⟩
  simpa only [mul_assoc] using add_le_add (le_refl (Real.log 2 / 2 * n)) herr

/-- Finite reduction transports the same numerical envelope to arbitrary
groups, including infinite ones. -/
theorem exists_cover_logScale {G : Type u} [Group G]
    {n : ℕ} (hn : NoncommutingBound G n) :
    ∃ K : ℕ, HasAbelianCover G K ∧
      Real.log K ≤ Real.log 2 / 2 * n + finiteCoverError n (16 * logScale n ^ 2) := by
  obtain ⟨H, hHgroup, hHfinite, hclique, hcover⟩ := finite_reduction hn
  obtain ⟨K, hK, hlog⟩ := exists_finite_cover_logScale ((hclique n).mpr hn)
  exact ⟨K, (hcover K).mp hK, hlog⟩

end Erdos117
