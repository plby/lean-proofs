/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite-coordinate interpretations of the truncated prime moments.
Informal source: BBMST's score-ordered arithmetic frames.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.TruncatedCountingMoments
import ErdosProblems.Erdos1189.CountingEntropy

namespace Erdos1189

open Finset

lemma countingCoordinates_fibre (x : ℝ) (e : ℕ) :
    (countingCoordinates x).filter (fun c => c.2 = e) =
      (Nat.primesLE (Nat.ceil (x * logIncrement e))).image (fun p => (p, e)) := by
  classical
  ext ⟨p, f⟩
  constructor
  · intro h
    obtain ⟨h, hfe⟩ := mem_filter.mp h
    dsimp only at hfe
    subst f
    exact mem_image.mpr ⟨p, coordinate_mem_iff_prime_cutoff.mp h, rfl⟩
  · intro h
    obtain ⟨q, hq, hqp⟩ := mem_image.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hqp
    exact mem_filter.mpr ⟨coordinate_mem_iff_prime_cutoff.mpr hq, rfl⟩

lemma sum_countingCoordinates_truncated (x : ℝ) (T : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ c ∈ countingCoordinates x with c.2 < T, f c) =
      ∑ e ∈ range T, ∑ p ∈ Nat.primesLE (Nat.ceil (x * logIncrement e)), f (p, e) := by
  classical
  have hf := sum_fiberwise_eq_sum_filter (countingCoordinates x) (range T) Prod.snd f
  simp only [mem_range] at hf
  rw [← hf]
  apply sum_congr rfl
  intro e _
  rw [countingCoordinates_fibre, sum_image]
  intro p _ q _ hpq
  exact (Prod.mk.inj hpq).1

lemma truncatedPrimeMass_eq (T : ℕ) (x : ℝ) :
    truncatedPrimeMass T x =
      ∑ c ∈ countingCoordinates x with c.2 < T, logIncrement c.2 := by
  rw [sum_countingCoordinates_truncated]
  simp only [truncatedPrimeMass, sum_const, nsmul_eq_mul, Nat.primesLE_card_eq_primeCounting]

lemma truncatedScoreMoment_eq (T : ℕ) (x : ℝ) :
    truncatedScoreMoment T x = ∑ c ∈ countingCoordinates x with c.2 < T,
      ((c.1 - 1 : ℕ) : ℝ) * coordinateScore c.1 c.2 := by
  rw [sum_countingCoordinates_truncated]
  unfold truncatedScoreMoment
  apply sum_congr rfl
  intro e _
  rw [sum_div]
  apply sum_congr rfl
  intro p hp
  rw [Nat.cast_sub (Nat.prime_of_mem_primesLE hp).one_lt.le, Nat.cast_one]
  dsimp [coordinateScore]
  ring

lemma same_prime_log_mass_le (T p : ℕ) (x : ℝ) :
    (∑ c ∈ (countingCoordinates x).filter (fun c => c.2 < T) with c.1 = p,
      logIncrement c.2) ≤ Real.log (T + 1 : ℝ) := by
  classical
  let S := ((countingCoordinates x).filter (fun c => c.2 < T)).filter (fun c => c.1 = p)
  have hinj : Set.InjOn (fun c : ℕ × ℕ => c.2) S := by
    intro c hc d hd hcd
    apply Prod.ext
    · exact (mem_filter.mp hc).2.trans (mem_filter.mp hd).2.symm
    · exact hcd
  have hsub : S.image Prod.snd ⊆ range T := by
    intro e he
    obtain ⟨c, hc, rfl⟩ := mem_image.mp he
    exact mem_range.mpr (mem_filter.mp (mem_filter.mp hc).1).2
  change (∑ c ∈ S, logIncrement c.2) ≤ _
  rw [← sum_image (f := logIncrement) (fun c hc d hd h => hinj hc hd h), ← sum_logIncrement]
  exact sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => (logIncrement_pos e).le)

lemma truncatedPrimeMass_le_entropy_inner {x : ℝ} {c : ℕ × ℕ}
    (hc : c ∈ countingCoordinates x) (T : ℕ) :
    truncatedPrimeMass T (coordinateScore c.1 c.2) ≤
      (∑ i ∈ countingCoordinates x with i.1 ≠ c.1 ∧
        coordinateScore i.1 i.2 < coordinateScore c.1 c.2, logIncrement i.2) +
          Real.log (T + 1 : ℝ) := by
  classical
  let S := (countingCoordinates (coordinateScore c.1 c.2)).filter (fun i => i.2 < T)
  have hdiff : (∑ i ∈ S with i.1 ≠ c.1, logIncrement i.2) ≤
      ∑ i ∈ countingCoordinates x with i.1 ≠ c.1 ∧
        coordinateScore i.1 i.2 < coordinateScore c.1 c.2, logIncrement i.2 := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro i hi
      obtain ⟨hi, hne⟩ := mem_filter.mp hi
      have his := (mem_filter.mp hi).1
      have hiScore := (mem_countingCoordinates.mp his).2
      exact mem_filter.mpr ⟨countingCoordinates_mono
        (mem_countingCoordinates.mp hc).2.le his, hne, hiScore⟩
    · intro i _ _
      exact (logIncrement_pos i.2).le
  have hsame := same_prime_log_mass_le T c.1 (coordinateScore c.1 c.2)
  have hsplit := sum_filter_add_sum_filter_not S (fun i => i.1 ≠ c.1) (fun i => logIncrement i.2)
  simp only [not_not] at hsplit
  rw [truncatedPrimeMass_eq]
  change (∑ i ∈ S, logIncrement i.2) ≤ _
  rw [← hsplit]
  exact add_le_add hdiff hsame

end Erdos1189
