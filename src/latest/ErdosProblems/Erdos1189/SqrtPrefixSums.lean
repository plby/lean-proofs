/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The convexity estimate underlying the sharp frame-entropy summation.
Informal source: BBMST Lemmas 7.4 and 7.6.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.CoordinateKnapsack

namespace Erdos1189

open Finset

lemma sqrt_power_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    3 * Real.sqrt a * (b - a) ≤ 2 * (b * Real.sqrt b - a * Real.sqrt a) := by
  have hb : 0 ≤ b := ha.trans hab
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hnonneg : 0 ≤ (Real.sqrt b - Real.sqrt a) ^ 2 * (2 * Real.sqrt b + Real.sqrt a) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  nlinarith [congrArg (fun z => z * Real.sqrt a) hsa,
    congrArg (fun z => z * Real.sqrt b) hsb, congrArg (fun z => z * Real.sqrt a) hsb]

def prefixWeight {β : Type*} (S : Finset β) (rank w : β → ℕ) (i : β) : ℕ :=
  ∑ j ∈ S with rank j < rank i, w j

lemma sum_sqrt_prefixWeight_le {β : Type*} (S : Finset β) (rank w : β → ℕ)
    (hinj : Set.InjOn rank S) :
    (∑ i ∈ S, (w i : ℝ) * Real.sqrt (prefixWeight S rank w i)) ≤
      (2 / 3 : ℝ) * (∑ i ∈ S, w i) * Real.sqrt ((∑ i ∈ S, w i : ℕ) : ℝ) := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hS : S.Nonempty
    · obtain ⟨i, hi, hmax⟩ := S.exists_max_image rank hS
      let T := S.erase i
      have hTsub : T ⊆ S := erase_subset _ _
      have hTproper : T ⊂ S := erase_ssubset hi
      have hTinj : Set.InjOn rank T := fun a ha b hb hab => hinj (hTsub ha) (hTsub hb) hab
      have hbound := ih T hTproper hTinj
      have hbefore : ∀ j ∈ T, rank j < rank i := by
        intro j hj
        exact lt_of_le_of_ne (hmax j (hTsub hj))
          (fun heq => (mem_erase.mp hj).1 (hinj (hTsub hj) hi heq))
      have hprefixI : prefixWeight S rank w i = ∑ j ∈ T, w j := by
        unfold prefixWeight
        congr 1
        ext j
        constructor
        · intro hj
          obtain ⟨hjS, hjlt⟩ := mem_filter.mp hj
          exact mem_erase.mpr ⟨fun hji => by subst j; exact Nat.lt_irrefl _ hjlt, hjS⟩
        · intro hj
          exact mem_filter.mpr ⟨hTsub hj, hbefore j hj⟩
      have hprefix : ∀ j ∈ T, prefixWeight S rank w j = prefixWeight T rank w j := by
        intro j hj
        unfold prefixWeight
        congr 1
        ext t
        simp only [mem_filter, T, mem_erase]
        have hji := hbefore j hj
        constructor
        · rintro ⟨htS, htj⟩
          exact ⟨⟨fun hti => by subst t; omega, htS⟩, htj⟩
        · exact fun h => ⟨h.1.2, h.2⟩
      have hsum : (∑ j ∈ S, w j) = (∑ j ∈ T, w j) + w i := (sum_erase_add _ _ hi).symm
      have hleft : (∑ j ∈ S, (w j : ℝ) * Real.sqrt (prefixWeight S rank w j)) =
          (∑ j ∈ T, (w j : ℝ) * Real.sqrt (prefixWeight T rank w j)) +
            w i * Real.sqrt ((∑ j ∈ T, w j : ℕ) : ℝ) := by
        rw [← sum_erase_add _ _ hi, hprefixI]
        congr 1
        exact sum_congr rfl (fun j hj => by rw [hprefix j hj])
      rw [hleft, hsum]
      have ht0 : (0 : ℝ) ≤ ((∑ j ∈ T, w j : ℕ) : ℝ) := by positivity
      have hinc := sqrt_power_increment ht0
        (le_add_of_nonneg_right (Nat.cast_nonneg (w i) (α := ℝ)))
      push_cast at hinc hbound ⊢
      nlinarith
    · rw [not_nonempty_iff_eq_empty.mp hS]
      simp

end Erdos1189
