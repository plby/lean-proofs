/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPrimeIntervalLower

/-! # Bounded admissible tuples from the proved upper-half prime count -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem primeTuple_admissible {k : ℕ} (h : Fin k → ℕ)
    (hprime : ∀ i, (h i).Prime) (hlarge : ∀ i, k < h i) :
    BoundedGaps.IsAdmissible (Finset.univ.image h) := by
  classical
  intro p hp
  rw [Finset.image_image]
  by_cases hpk : p ≤ k
  · have hsub : Finset.univ.image (fun i => h i % p) ⊆ Finset.range p := by
      intro a ha
      obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_range.mpr (Nat.mod_lt _ hp.pos)
    have hzero : 0 ∉ Finset.univ.image (fun i => h i % p) := by
      intro hz
      obtain ⟨i, _hi, hmod⟩ := Finset.mem_image.mp hz
      have hdiv : p ∣ h i := Nat.dvd_of_mod_eq_zero hmod
      rcases (Nat.dvd_prime (hprime i)).mp hdiv with h1 | heq
      · exact hp.ne_one h1
      · have hi := hlarge i
        omega
    have hne : Finset.univ.image (fun i => h i % p) ≠ Finset.range p := by
      intro heq
      apply hzero
      rw [heq]
      exact Finset.mem_range.mpr hp.pos
    simpa only [Finset.card_range, Function.comp_def] using
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  · have hcard : (Finset.univ.image (fun i => h i % p)).card ≤ k := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        (Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := fun i => h i % p))
    exact hcard.trans_lt (by omega)

theorem eventually_squarePrimeSet_card_ge :
    ∀ᶠ k : ℕ in atTop, k ≤ (commonPinnedPrimeSet (k ^ 2 / 2) (k ^ 2)).card := by
  obtain ⟨X0, hcount⟩ := eventually_atTop.mp eventually_commonPinnedPrimeSet_half_card_lower
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).def (by norm_num : (0 : ℝ) < 1 / 16)
  filter_upwards [hsmall, eventually_ge_atTop (max 2 X0)] with k hsmall hk
  have hk2 : 2 ≤ k := (le_max_left _ _).trans hk
  have hkX : X0 ≤ k := (le_max_right _ _).trans hk
  have hks : k ≤ k ^ 2 := by nlinarith
  have hC := hcount (k ^ 2) (hkX.trans hks)
  have hkR : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos hkR
  have hlogeq : Real.log (k ^ 2 : ℕ) = 2 * Real.log (k : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hs : Real.log (k : ℝ) ≤ (1 / 16 : ℝ) * k := by
    simpa only [Function.comp_apply, Real.rpow_one, Real.norm_eq_abs, abs_of_pos hlog,
      abs_of_nonneg (show (0 : ℝ) ≤ k from Nat.cast_nonneg k)] using hsmall
  have hbound : (k : ℝ) ≤ (k ^ 2 : ℕ) / (8 * Real.log (k ^ 2 : ℕ)) := by
    rw [hlogeq, Nat.cast_pow]
    apply (le_div_iff₀ (by positivity : 0 < 8 * (2 * Real.log (k : ℝ)))).mpr
    nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ k)]
  exact_mod_cast hbound.trans hC

theorem eventually_exists_bounded_admissible_tuple :
    ∀ᶠ k : ℕ in atTop, ∃ h : Fin k → ℕ,
      Function.Injective h ∧ BoundedGaps.IsAdmissible (Finset.univ.image h) ∧
      (∀ i, (h i).Prime ∧ k < h i ∧ h i < 2 * k ^ 2) := by
  classical
  filter_upwards [eventually_squarePrimeSet_card_ge, eventually_ge_atTop (2 : ℕ)] with k hcount hk
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcount
  let h : Fin k → ℕ := T.orderEmbOfFin hTcard
  have hmem (i : Fin k) : h i ∈ commonPinnedPrimeSet (k ^ 2 / 2) (k ^ 2) :=
    hTsub (T.orderEmbOfFin_mem hTcard i)
  have hhalf : k ≤ k ^ 2 / 2 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr (by nlinarith)
  have hlarge (i : Fin k) : k < h i := hhalf.trans_lt (mem_commonPinnedPrimeSet.mp (hmem i)).1
  have hprime (i : Fin k) : (h i).Prime := (mem_commonPinnedPrimeSet.mp (hmem i)).2.2
  refine ⟨h, (T.orderEmbOfFin hTcard).injective, primeTuple_admissible h hprime hlarge, ?_⟩
  intro i
  have hhi := (mem_commonPinnedPrimeSet.mp (hmem i)).2.1
  exact ⟨hprime i, hlarge i, by nlinarith⟩

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.primeTuple_admissible
#print axioms Erdos4b.FGKMT.eventually_exists_bounded_admissible_tuple
