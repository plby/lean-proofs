import Util.Bernays.SmoothDecomposition
import Mathlib.Data.Finset.Sigma

/-!
# Exact counting by the unique discriminant-prime part
-/

open scoped Classical

namespace Bernays

noncomputable def positiveValues (R : ℕ → Prop) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter R

noncomputable def smoothValues (P : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun m => m ∈ Nat.factoredNumbers P

noncomputable def coprimeSliceValues (R : ℕ → Prop) (M m N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun k => k.Coprime M ∧ R (m * k)

theorem coprime_avoids_primeFactors {k M : ℕ} (hk : k.Coprime M) :
    ∀ p ∈ M.primeFactors, p.Prime → ¬ p ∣ k := by
  intro p hp hprime hpk
  exact hprime.not_dvd_one (hk.gcd_eq_one ▸ Nat.dvd_gcd hpk (Nat.mem_primeFactors.mp hp).2.1)

theorem positiveValues_card_smooth_sum (R : ℕ → Prop) {M : ℕ} (hM : M ≠ 0) (N : ℕ) :
    (positiveValues R N).card = ∑ m ∈ smoothValues M.primeFactors N,
      (coprimeSliceValues R M m (N / m)).card := by
  rw [← Finset.card_sigma]
  symm
  apply Finset.card_bij (fun a _ => a.1 * a.2)
  · intro a ha
    obtain ⟨hm, hk⟩ := Finset.mem_sigma.mp ha
    obtain ⟨hmI, hms⟩ := Finset.mem_filter.mp hm
    obtain ⟨hkI, hkc, hR⟩ := Finset.mem_filter.mp hk
    obtain ⟨hmpos, hmN⟩ := Finset.mem_Icc.mp hmI
    obtain ⟨hkpos, hkN⟩ := Finset.mem_Icc.mp hkI
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hmpos hkpos, ?_⟩, hR⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hmpos).mp hkN
  · intro a ha b hb heq
    obtain ⟨ham, hak⟩ := Finset.mem_sigma.mp ha
    obtain ⟨hbm, hbk⟩ := Finset.mem_sigma.mp hb
    have ham' := (Finset.mem_filter.mp ham).2
    have hbm' := (Finset.mem_filter.mp hbm).2
    have hak' := (Finset.mem_filter.mp hak).2.1
    have hbk' := (Finset.mem_filter.mp hbk).2.1
    have h := smooth_decomposition_unique ham' hbm'
      (coprime_avoids_primeFactors hak') (coprime_avoids_primeFactors hbk') heq
    cases a
    cases b
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · intro n hn
    obtain ⟨hnI, hnR⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnpos, hnN⟩ := Finset.mem_Icc.mp hnI
    let m := smoothPart M.primeFactors n
    let k := avoidingPart M.primeFactors n
    have hms : m ∈ Nat.factoredNumbers M.primeFactors := smoothPart_mem _ _
    have hmpos : 0 < m := Nat.pos_of_ne_zero hms.1
    have hkpos : 0 < k := avoidingPart_pos _ _
    have hmk : m * k = n := smoothPart_mul_avoidingPart _ (by omega)
    have hmN : m ≤ N := by nlinarith
    have hkN : k ≤ N / m := by
      apply (Nat.le_div_iff_mul_le hmpos).mpr
      rw [Nat.mul_comm k m, hmk]
      exact hnN
    refine ⟨⟨m, k⟩, Finset.mem_sigma.mpr ⟨?_, ?_⟩, hmk⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hmpos, hmN⟩, hms⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hkpos, hkN⟩,
        avoidingPart_coprime hM n, hmk.symm ▸ hnR⟩

end Bernays
