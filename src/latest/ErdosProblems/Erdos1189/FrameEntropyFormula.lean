/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Writing arithmetic-frame entropy as a sum over preceding prime-adic coordinates.
Informal source: BBMST Lemma 5.3, equations (17) and (19).
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.FrameEntropy
import ErdosProblems.Erdos1189.Tau

namespace Erdos1189

open Finset

lemma sum_preceding_logIncrement {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    (hrank : IsArithmeticRank rank) (c : PrimeCoordinate N) (p : N.primeFactors) :
    (∑ e : Fin (N.factorization p) with rank ⟨p, e⟩ < rank c, logIncrement e.val) =
      Real.log ((precedingExponent rank c p : ℝ) + 1) := by
  let S := (univ : Finset (Fin (N.factorization p))).filter
    (fun e => rank ⟨p, e⟩ < rank c)
  have himage : S.image Fin.val = range (precedingExponent rank c p) := by
    ext e
    simp only [mem_image, mem_range]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (lt_precedingExponent_iff hrank c p f).mpr (mem_filter.mp hf).2
    · intro he
      have heN := he.trans_le (precedingExponent_le rank c p)
      exact ⟨⟨e, heN⟩, mem_filter.mpr ⟨mem_univ _,
        (lt_precedingExponent_iff hrank c p ⟨e, heN⟩).mp he⟩, rfl⟩
  have hsum : (∑ e ∈ S, logIncrement e.val) =
      ∑ e ∈ range (precedingExponent rank c p), logIncrement e := by
    rw [← himage, sum_image (fun _ _ _ _ h => Fin.ext h)]
  exact hsum.trans (sum_logIncrement _)

lemma log_profile_count_eq {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    (hrank : IsArithmeticRank rank) (c : PrimeCoordinate N) :
    Real.log (profileModuli rank c).card =
      ∑ i : PrimeCoordinate N with i.1 ≠ c.1 ∧ rank i < rank c, logIncrement i.2.val := by
  have hsub : (∑ p : OtherPrime c, Real.log ((precedingExponent rank c p.val : ℝ) + 1)) =
      ∑ p : N.primeFactors, if p ≠ c.1 then
        Real.log ((precedingExponent rank c p : ℝ) + 1) else 0 := by
    rw [← sum_filter]
    exact (sum_subtype (univ.filter (fun p : N.primeFactors => p ≠ c.1))
      (fun p => by simp) (fun p => Real.log ((precedingExponent rank c p : ℝ) + 1))).symm
  calc
    _ = ∑ p : OtherPrime c, Real.log ((precedingExponent rank c p.val : ℝ) + 1) := by
      rw [card_profileModuli, Nat.cast_prod, Real.log_prod (fun _ _ => by positivity)]
      simp only [Nat.cast_add, Nat.cast_one]
    _ = _ := by
      rw [hsub, sum_filter, Fintype.sum_sigma]
      apply sum_congr rfl
      intro p _
      by_cases hp : p = c.1
      · simp only [hp, ne_eq, not_true_eq_false, false_and, ite_false, sum_const_zero]
      · simp only [hp, ne_eq, not_false_eq_true, true_and, ite_true]
        rw [← sum_filter]
        exact (sum_preceding_logIncrement hrank c p).symm

theorem frameEntropy_eq {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    (hrank : IsArithmeticRank rank) :
    frameEntropy rank =
      ∑ c : PrimeCoordinate N, ((coordinateSize c - 1 : ℕ) : ℝ) *
        ∑ i : PrimeCoordinate N with i.1 ≠ c.1 ∧ rank i < rank c, logIncrement i.2.val := by
  unfold frameEntropy
  apply sum_congr rfl
  intro c _
  rw [log_profile_count_eq hrank]

end Erdos1189
