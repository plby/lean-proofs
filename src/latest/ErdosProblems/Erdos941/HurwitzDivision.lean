import ErdosProblems.Erdos941.HurwitzApproximation
import Mathlib.RingTheory.Ideal.Span

/-! # Euclidean division and principal left ideals in the Hurwitz order -/

namespace Erdos941

open scoped Quaternion

theorem hurwitz_division (a b : hurwitzOrder) (hb : b ≠ 0) :
    ∃ q r : hurwitzOrder, a = q * b + r ∧ hurwitzNorm r < hurwitzNorm b := by
  have hb' : (b : ℍ[ℚ]) ≠ 0 := fun h => hb (Subtype.ext h)
  have hnb : 0 < Quaternion.normSq (b : ℍ[ℚ]) := by
    exact lt_of_le_of_ne Quaternion.normSq_nonneg
      (Ne.symm (Quaternion.normSq_eq_zero.not.mpr hb'))
  obtain ⟨q, hq⟩ := hurwitz_approximation ((a : ℍ[ℚ]) / (b : ℍ[ℚ]))
  refine ⟨q, a - q * b, by abel, ?_⟩
  have heq : ((a - q * b : hurwitzOrder) : ℍ[ℚ]) =
      ((a : ℍ[ℚ]) / (b : ℍ[ℚ]) - (q : ℍ[ℚ])) * (b : ℍ[ℚ]) := by
    change (a : ℍ[ℚ]) - (q : ℍ[ℚ]) * (b : ℍ[ℚ]) = _
    rw [sub_mul, div_mul_cancel₀ _ hb']
  have hn : (hurwitzNorm (a - q * b) : ℚ) < (hurwitzNorm b : ℚ) := by
    rw [hurwitzNorm_cast, hurwitzNorm_cast, heq, map_mul]
    simpa only [one_mul] using mul_lt_mul_of_pos_right hq hnb
  exact_mod_cast hn

theorem hurwitz_left_ideal_principal (I : Ideal hurwitzOrder) :
    ∃ q : hurwitzOrder, I = Ideal.span {q} := by
  classical
  by_cases hnonzero : ∃ q : hurwitzOrder, q ∈ I ∧ q ≠ 0
  · have hex : ∃ k : ℕ, ∃ q : hurwitzOrder, q ∈ I ∧ q ≠ 0 ∧ hurwitzNorm q = k := by
      obtain ⟨q, hq, hq0⟩ := hnonzero
      exact ⟨hurwitzNorm q, q, hq, hq0, rfl⟩
    obtain ⟨q, hqI, hq0, hqn⟩ := Nat.find_spec hex
    refine ⟨q, le_antisymm ?_ ?_⟩
    · intro a ha
      obtain ⟨s, r, heq, hrn⟩ := hurwitz_division a q hq0
      have hrI : r ∈ I := by
        have hr : r = a - s * q := by rw [heq]; abel
        rw [hr]
        exact I.sub_mem ha (I.mul_mem_left s hqI)
      have hr0 : r = 0 := by
        by_contra hne
        have hmin := Nat.find_min' hex ⟨r, hrI, hne, rfl⟩
        omega
      apply Ideal.mem_span_singleton'.mpr
      exact ⟨s, by simpa only [hr0, add_zero] using heq.symm⟩
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hqI)
  · refine ⟨0, ?_⟩
    have hI : I = ⊥ := by
      apply le_antisymm _ bot_le
      intro q hq
      exact (Submodule.mem_bot _).mpr (by
        by_contra hq0
        exact hnonzero ⟨q, hq, hq0⟩)
    rw [hI, Ideal.span_singleton_eq_bot.mpr rfl]

end Erdos941
