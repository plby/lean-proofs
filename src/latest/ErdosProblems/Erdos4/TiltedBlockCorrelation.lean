import ErdosProblems.Erdos4.TiltedBlockProbability
import ErdosProblems.Erdos4.TiltedLocalRatios

/-! Exact local block correlations, with the shared zero residue isolated. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT

theorem localLaw_prob_avoid_erase (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (E : Finset (ZMod s)) :
    (localLaw s hs u hu0 hu1).prob (fun a => a ∉ E) =
      if 0 ∈ E then beta s u * (1 - ((E.erase 0).card : ℝ) / ((s : ℝ) - 1))
      else 1 - beta s u * (((E.erase 0).card : ℝ) / ((s : ℝ) - 1)) := by
  classical
  rw [localLaw_prob_avoid]
  by_cases hz : (0 : ZMod s) ∈ E
  · simp only [if_pos hz]
    have hc : ((E.erase 0).card : ℝ) + 1 = E.card := by
      exact_mod_cast Finset.card_erase_add_one hz
    rw [show (E.card : ℝ) - 1 = (E.erase 0).card by linarith]
  · simp only [if_neg hz, Finset.erase_eq_of_notMem hz]
    have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
    unfold beta
    field_simp [show (s : ℝ) - 1 ≠ 0 by linarith]

theorem localLaw_pair_ratio_le (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (E F : Finset (ZMod s))
    (hE : 2 * E.card ≤ s - 1) (hF : 2 * F.card ≤ s - 1) :
    (localLaw s hs u hu0.le hu1).prob (fun a => a ∉ E ∪ F) /
        ((localLaw s hs u hu0.le hu1).prob (fun a => a ∉ E) *
          (localLaw s hs u hu0.le hu1).prob (fun a => a ∉ F)) ≤
      (if (0 : ZMod s) ∈ E ∧ (0 : ZMod s) ∈ F then 1 / beta s u else 1) *
        (1 + 4 * (((E.erase 0 ∩ F.erase 0).card : ℝ) / ((s : ℝ) - 1))) := by
  classical
  let D := (s : ℝ) - 1
  let a := ((E.erase 0).card : ℝ) / D
  let b := ((F.erase 0).card : ℝ) / D
  let c := ((E.erase 0 ∩ F.erase 0).card : ℝ) / D
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hD : 0 < D := by dsimp [D]; linarith
  have ha0 : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) hD.le
  have hb0 : 0 ≤ b := div_nonneg (Nat.cast_nonneg _) hD.le
  have hc0 : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) hD.le
  have hE' : (2 : ℝ) * E.card ≤ D := by
    have hh : (2 : ℝ) * E.card + 1 ≤ s := by exact_mod_cast (show 2 * E.card + 1 ≤ s by omega)
    dsimp [D]
    linarith
  have hF' : (2 : ℝ) * F.card ≤ D := by
    have hh : (2 : ℝ) * F.card + 1 ≤ s := by exact_mod_cast (show 2 * F.card + 1 ≤ s by omega)
    dsimp [D]
    linarith
  have ha : a ≤ 1 / 2 := by
    apply (div_le_iff₀ hD).mpr
    have hh : ((E.erase 0).card : ℝ) ≤ E.card := by exact_mod_cast Finset.card_erase_le
    linarith
  have hb : b ≤ 1 / 2 := by
    apply (div_le_iff₀ hD).mpr
    have hh : ((F.erase 0).card : ℝ) ≤ F.card := by exact_mod_cast Finset.card_erase_le
    linarith
  have hU : (((E ∪ F).erase 0).card : ℝ) / D = a + b - c := by
    rw [Finset.erase_union_distrib]
    have hh : ((E.erase 0 ∪ F.erase 0).card : ℝ) + (E.erase 0 ∩ F.erase 0).card =
        (E.erase 0).card + (F.erase 0).card := by
      exact_mod_cast Finset.card_union_add_card_inter (E.erase 0) (F.erase 0)
    dsimp [a, b, c]
    apply (div_eq_iff hD.ne').mpr
    field_simp
    linarith
  have hβ0 : 0 < beta s u := beta_pos hs hu0
  have hβ1 : beta s u ≤ 1 := beta_le_one hs hu0.le hu1
  have ha1 : 0 < 1 - a := by linarith
  have hb1 : 0 < 1 - b := by linarith
  have hβa1 : 0 < 1 - beta s u * a := by
    have hh := mul_le_of_le_one_left ha0 hβ1
    linarith
  have hβb1 : 0 < 1 - beta s u * b := by
    have hh := mul_le_of_le_one_left hb0 hβ1
    linarith
  rw [localLaw_prob_avoid_erase, localLaw_prob_avoid_erase, localLaw_prob_avoid_erase]
  change (if 0 ∈ E ∪ F then beta s u * (1 - (((E ∪ F).erase 0).card : ℝ) / D)
      else 1 - beta s u * ((((E ∪ F).erase 0).card : ℝ) / D)) /
    ((if 0 ∈ E then beta s u * (1 - a) else 1 - beta s u * a) *
      (if 0 ∈ F then beta s u * (1 - b) else 1 - beta s u * b)) ≤
    (if (0 : ZMod s) ∈ E ∧ (0 : ZMod s) ∈ F then 1 / beta s u else 1) * (1 + 4 * c)
  rw [hU]
  by_cases he : (0 : ZMod s) ∈ E <;> by_cases hf : (0 : ZMod s) ∈ F
  · simp only [Finset.mem_union, he, hf, or_self, and_self, if_true]
    calc
      _ = (1 / beta s u) * ((1 - (a + b - c)) / ((1 - a) * (1 - b))) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (avoidance_ratio_le ha0 hb0 ha hb hc0) (by positivity)
  · simp only [Finset.mem_union, he, hf, true_or, and_false, if_true, if_false, one_mul]
    calc
      _ = (1 - (a + b - c)) / ((1 - a) * (1 - beta s u * b)) := by field_simp
      _ ≤ _ := mixed_avoidance_ratio_le hβ0.le hβ1 ha0 hb0 ha hb hc0
  · simp only [Finset.mem_union, he, hf, or_true, false_and, if_true, if_false, one_mul]
    calc
      _ = (1 - (b + a - c)) / ((1 - b) * (1 - beta s u * a)) := by field_simp; ring
      _ ≤ _ := mixed_avoidance_ratio_le hβ0.le hβ1 hb0 ha0 hb ha hc0
  · simp only [Finset.mem_union, he, hf, or_self, and_self, if_false, one_mul]
    exact tilted_avoidance_ratio_le hβ0.le hβ1 ha0 hb0 ha hb hc0

end Erdos4.Tilted
