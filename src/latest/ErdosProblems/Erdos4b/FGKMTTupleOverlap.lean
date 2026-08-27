/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTWeightedResidueConcentration

/-! # The exact overlap budget for translates of a finite tuple -/

namespace Erdos4b.FGKMT

open scoped BigOperators

def translatedResidueTuple (H : Finset ℤ) (n : ℤ) : Finset ℤ :=
  H.image (fun h => n + h)

theorem translatedResidueTuple_card (H : Finset ℤ) (n : ℤ) :
    (translatedResidueTuple H n).card = H.card := by
  exact Finset.card_image_of_injective H (add_right_injective n)

theorem translatedResidueTuple_overlap_card_le (H J : Finset ℤ) (n : ℤ) :
    (J.filter fun m => ¬Disjoint (translatedResidueTuple H n)
      (translatedResidueTuple H m)).card ≤ H.card ^ 2 := by
  classical
  have hsubset : (J.filter fun m => ¬Disjoint (translatedResidueTuple H n)
      (translatedResidueTuple H m)) ⊆
      (H ×ˢ H).image (fun hh => n + hh.1 - hh.2) := by
    intro m hm
    obtain ⟨q, hqn, hqm⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hm).2
    obtain ⟨h, hh, hq⟩ := Finset.mem_image.mp hqn
    obtain ⟨h', hh', hq'⟩ := Finset.mem_image.mp hqm
    exact Finset.mem_image.mpr ⟨(h, h'), Finset.mem_product.mpr ⟨hh, hh'⟩, by
      dsimp
      omega⟩
  exact (Finset.card_le_card hsubset).trans (Finset.card_image_le.trans (by
    simp only [Finset.card_product, pow_two, le_refl]))

theorem translatedResidueTuple_overlap_mass_le (H J : Finset ℤ) (b : ℤ → ℝ)
    (hb : ∀ n ∈ J, 0 ≤ b n) (hsum : ∑ n ∈ J, b n = 1)
    {a : ℝ} (ha : 0 ≤ a) (hcap : ∀ n ∈ J, b n ≤ a) :
    residueTupleOverlapMass J b (translatedResidueTuple H) ≤ (H.card : ℝ) ^ 2 * a := by
  classical
  have hrow (n : ℤ) (hn : n ∈ J) :
      (∑ m ∈ J, if Disjoint (translatedResidueTuple H n) (translatedResidueTuple H m)
        then 0 else b n * b m) ≤ b n * ((H.card : ℝ) ^ 2 * a) := by
    let B := J.filter fun m => ¬Disjoint (translatedResidueTuple H n) (translatedResidueTuple H m)
    have hcard : (B.card : ℝ) ≤ (H.card : ℝ) ^ 2 := by
      exact_mod_cast translatedResidueTuple_overlap_card_le H J n
    have hsumB : (∑ m ∈ B, b m) ≤ (H.card : ℝ) ^ 2 * a := by
      calc
        _ ≤ ∑ _m ∈ B, a := Finset.sum_le_sum fun m hm => hcap m (Finset.mem_filter.mp hm).1
        _ = (B.card : ℝ) * a := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hcard ha
    calc
      _ = b n * ∑ m ∈ B, b m := by
        rw [Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro m _hm
        by_cases hd : Disjoint (translatedResidueTuple H n) (translatedResidueTuple H m) <;>
          simp [hd]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsumB (hb n hn)
  calc
    _ ≤ ∑ n ∈ J, b n * ((H.card : ℝ) ^ 2 * a) := Finset.sum_le_sum hrow
    _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.translatedResidueTuple_overlap_card_le
#print axioms Erdos4b.FGKMT.translatedResidueTuple_overlap_mass_le
