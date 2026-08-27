import ErdosProblems.Erdos4.TiltedBlockCorrelation
import ErdosProblems.Erdos4.TiltedConditioning

/-! Exact avoidance factors after conditioning on a surviving root. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT

theorem beta_div_modulus_sub_one {s : ℕ} (hs : 2 ≤ s) (u : ℝ) :
    beta s u / ((s : ℝ) - 1) = atom s u := by
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  unfold beta
  exact mul_div_cancel_left₀ _ (show (s : ℝ) - 1 ≠ 0 by linarith)

theorem baseline_eq_one_sub_beta_div {s : ℕ} (hs : 2 ≤ s) {u : ℝ} (hu : 0 ≤ u) :
    baseline s u = 1 - beta s u / ((s : ℝ) - 1) := by
  rw [beta_div_modulus_sub_one hs, baseline_eq_one_sub_atom hs hu]

theorem rootedLocalLaw_prob_avoid_insert (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (v : ZMod s) (E : Finset (ZMod s)) :
    (rootedLocalLaw s hs u hu0 hu1 v).prob (fun a => a ∉ E) =
      (localLaw s hs u hu0.le hu1).prob (fun a => a ∉ insert v E) /
        (if v = 0 then beta s u else baseline s u) := by
  classical
  rw [rootedLocalLaw, FiniteLaw.condition_prob _ _ _ _ (localLaw_prob_ne_pos s hs u hu0 hu1 v).ne',
    localLaw_prob_ne]
  have heq : (fun o : ZMod s => o ≠ v ∧ o ∉ E) = (fun a => a ∉ insert v E) := by
    funext a
    apply propext
    simp
  rw [heq]

theorem rootedLocalLaw_prob_avoid_erase (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (v : ZMod s) (E : Finset (ZMod s)) (hvE : v ∉ E) :
    (rootedLocalLaw s hs u hu0 hu1 v).prob (fun a => a ∉ E) =
      if v = 0 then 1 - ((E.erase 0).card : ℝ) / ((s : ℝ) - 1)
      else if 0 ∈ E then (beta s u / baseline s u) *
        (1 - (1 + ((E.erase 0).card : ℝ)) / ((s : ℝ) - 1))
      else (1 - beta s u * ((1 + ((E.erase 0).card : ℝ)) / ((s : ℝ) - 1))) / baseline s u := by
  classical
  rw [rootedLocalLaw_prob_avoid_insert, localLaw_prob_avoid_erase]
  have hβ : beta s u ≠ 0 := (beta_pos hs hu0).ne'
  by_cases hv : v = 0
  · subst v
    simp only [if_true, Finset.mem_insert_self, Finset.erase_insert_eq_erase]
    exact mul_div_cancel_left₀ _ hβ
  simp only [if_neg hv]
  have hvE' : v ∉ E.erase 0 := fun h => hvE (Finset.mem_of_mem_erase h)
  have hcard : ((insert v E).erase 0).card = (E.erase 0).card + 1 := by
    rw [Finset.erase_insert_of_ne hv, Finset.card_insert_of_notMem hvE']
  rw [hcard, Nat.cast_add, Nat.cast_one]
  have hzero : (0 : ZMod s) ∈ insert v E ↔ 0 ∈ E := by simp [Ne.symm hv]
  simp only [hzero]
  by_cases hz : (0 : ZMod s) ∈ E
  · simp only [if_pos hz]
    ring
  · simp only [if_neg hz]
    ring

theorem rooted_tilted_avoidance_ratio_le {a b c d β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hd0 : 0 ≤ d)
    (ha : d + a ≤ 1 / 2) (hb : d + b ≤ 1 / 2) (hc : 0 ≤ c) :
    ((1 - β * d) * (1 - β * (d + a + b - c))) /
        ((1 - β * (d + a)) * (1 - β * (d + b))) ≤ 1 + 4 * c := by
  have hβa : β * (d + a) ≤ 1 / 2 := (mul_le_of_le_one_left (add_nonneg hd0 ha0) hβ1).trans ha
  have hβb : β * (d + b) ≤ 1 / 2 := (mul_le_of_le_one_left (add_nonneg hd0 hb0) hβ1).trans hb
  have hh := rooted_avoidance_ratio_le (mul_nonneg hβ0 ha0) (mul_nonneg hβ0 hb0)
    (mul_nonneg hβ0 hd0) (by nlinarith : β * d + β * a ≤ 1 / 2)
    (by nlinarith : β * d + β * b ≤ 1 / 2) (mul_nonneg hβ0 hc)
  have heq :
      ((1 - β * d) * (1 - β * (d + a + b - c))) /
          ((1 - β * (d + a)) * (1 - β * (d + b))) =
      ((1 - β * d) * (1 - β * d - β * a - β * b + β * c)) /
          ((1 - β * d - β * a) * (1 - β * d - β * b)) := by ring
  rw [heq]
  have hβc : β * c ≤ c := mul_le_of_le_one_left hc hβ1
  exact hh.trans (by linarith)

theorem rootedLocalLaw_prob_avoid_fraction (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (v : ZMod s) (E : Finset (ZMod s)) (hvE : v ∉ E) :
    (rootedLocalLaw s hs u hu0 hu1 v).prob (fun a => a ∉ E) =
      if v = 0 then 1 - ((E.erase 0).card : ℝ) / ((s : ℝ) - 1)
      else if 0 ∈ E then (beta s u / baseline s u) *
        (1 - 1 / ((s : ℝ) - 1) - ((E.erase 0).card : ℝ) / ((s : ℝ) - 1))
      else (1 - beta s u * (1 / ((s : ℝ) - 1) + ((E.erase 0).card : ℝ) / ((s : ℝ) - 1))) /
        baseline s u := by
  rw [rootedLocalLaw_prob_avoid_erase s hs u hu0 hu1 v E hvE]
  split_ifs <;> ring

/-- In the rooted correlation, the large inverse tilt occurs only for a shared companion zero. -/
theorem rootedLocalLaw_pair_ratio_le (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (v : ZMod s) (E F : Finset (ZMod s))
    (hvE : v ∉ E) (hvF : v ∉ F)
    (hE : 2 * (E.card + 1) ≤ s - 1) (hF : 2 * (F.card + 1) ≤ s - 1) :
    (rootedLocalLaw s hs u hu0 hu1 v).prob (fun a => a ∉ E ∪ F) /
        ((rootedLocalLaw s hs u hu0 hu1 v).prob (fun a => a ∉ E) *
          (rootedLocalLaw s hs u hu0 hu1 v).prob (fun a => a ∉ F)) ≤
      (if (0 : ZMod s) ∈ E ∧ (0 : ZMod s) ∈ F then 1 / u else 1) *
        (1 + 4 * ((((E.erase 0 ∩ F.erase 0).card : ℝ) +
          if (0 : ZMod s) ∈ E ∧ (0 : ZMod s) ∈ F then 1 else 0) / ((s : ℝ) - 1))) := by
  classical
  let D := (s : ℝ) - 1
  let d := 1 / D
  let a := ((E.erase 0).card : ℝ) / D
  let b := ((F.erase 0).card : ℝ) / D
  let c := ((E.erase 0 ∩ F.erase 0).card : ℝ) / D
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hD : 0 < D := by dsimp [D]; linarith
  have hd0 : 0 ≤ d := div_nonneg zero_le_one hD.le
  have ha0 : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) hD.le
  have hb0 : 0 ≤ b := div_nonneg (Nat.cast_nonneg _) hD.le
  have hc0 : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) hD.le
  have ha : d + a ≤ 1 / 2 := by
    change 1 / D + ((E.erase 0).card : ℝ) / D ≤ _
    rw [← add_div]
    apply (div_le_iff₀ hD).mpr
    have hh : ((E.erase 0).card : ℝ) ≤ E.card := by exact_mod_cast Finset.card_erase_le
    have hsize : (2 : ℝ) * (E.card + 1) + 1 ≤ s := by
      exact_mod_cast (show 2 * (E.card + 1) + 1 ≤ s by omega)
    dsimp [D]
    linarith
  have hb : d + b ≤ 1 / 2 := by
    change 1 / D + ((F.erase 0).card : ℝ) / D ≤ _
    rw [← add_div]
    apply (div_le_iff₀ hD).mpr
    have hh : ((F.erase 0).card : ℝ) ≤ F.card := by exact_mod_cast Finset.card_erase_le
    have hsize : (2 : ℝ) * (F.card + 1) + 1 ≤ s := by
      exact_mod_cast (show 2 * (F.card + 1) + 1 ≤ s by omega)
    dsimp [D]
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
  have hβ : 0 < beta s u := beta_pos hs hu0
  have hβ1 : beta s u ≤ 1 := beta_le_one hs hu0.le hu1
  have hB : 0 < baseline s u := baseline_pos hs hu0.le
  have hBform : baseline s u = 1 - beta s u * d := by
    rw [baseline_eq_one_sub_beta_div hs hu0.le]
    dsimp [d, D]
    ring
  have hBβ : baseline s u / beta s u = 1 / u := by
    rw [beta_eq_baseline_mul]
    field_simp
  have ha1 : 0 < 1 - d - a := by linarith
  have hb1 : 0 < 1 - d - b := by linarith
  have hβa1 : 0 < 1 - beta s u * (d + a) := by
    have hh := mul_le_of_le_one_left (add_nonneg hd0 ha0) hβ1
    linarith
  have hβb1 : 0 < 1 - beta s u * (d + b) := by
    have hh := mul_le_of_le_one_left (add_nonneg hd0 hb0) hβ1
    linarith
  have hvU : v ∉ E ∪ F := by simp [hvE, hvF]
  rw [rootedLocalLaw_prob_avoid_fraction s hs u hu0 hu1 v (E ∪ F) hvU,
    rootedLocalLaw_prob_avoid_fraction s hs u hu0 hu1 v E hvE,
    rootedLocalLaw_prob_avoid_fraction s hs u hu0 hu1 v F hvF]
  change (if v = 0 then 1 - (((E ∪ F).erase 0).card : ℝ) / D
      else if 0 ∈ E ∪ F then beta s u / baseline s u * (1 - d - (((E ∪ F).erase 0).card : ℝ) / D)
      else (1 - beta s u * (d + (((E ∪ F).erase 0).card : ℝ) / D)) / baseline s u) /
    ((if v = 0 then 1 - a else if 0 ∈ E then beta s u / baseline s u * (1 - d - a)
        else (1 - beta s u * (d + a)) / baseline s u) *
      (if v = 0 then 1 - b else if 0 ∈ F then beta s u / baseline s u * (1 - d - b)
        else (1 - beta s u * (d + b)) / baseline s u)) ≤ _
  rw [hU]
  by_cases hv : v = 0
  · subst v
    simp only [if_true, hvE, hvF, false_and, if_false, add_zero, one_mul]
    exact avoidance_ratio_le ha0 hb0 (by linarith) (by linarith) hc0
  simp only [if_neg hv]
  by_cases he : (0 : ZMod s) ∈ E <;> by_cases hf : (0 : ZMod s) ∈ F
  · simp only [Finset.mem_union, he, hf, or_self, and_self, if_true]
    calc
      _ = (baseline s u / beta s u) *
          ((1 - ((d + a) + (d + b) - (d + c))) / ((1 - (d + a)) * (1 - (d + b)))) := by
        simp only [sub_add_eq_sub_sub]
        field_simp [ha1.ne', hb1.ne', hβ.ne', hB.ne']
        ring
      _ ≤ (baseline s u / beta s u) * (1 + 4 * (d + c)) :=
        mul_le_mul_of_nonneg_left
          (avoidance_ratio_le (add_nonneg hd0 ha0) (add_nonneg hd0 hb0) ha hb (add_nonneg hd0 hc0))
          (div_nonneg hB.le hβ.le)
      _ = _ := by rw [hBβ]; dsimp [d, c, D]; ring
  · simp only [Finset.mem_union, he, hf, true_or, and_false, if_true, if_false, add_zero, one_mul]
    calc
      _ = ((1 - beta s u * d) * (1 - d - a - b + c)) /
          ((1 - d - a) * (1 - beta s u * (d + b))) := by
        rw [← hBform]
        field_simp
        ring
      _ ≤ _ := rooted_mixed_avoidance_ratio_le hβ.le hβ1 ha0 hb0 hd0 ha hb hc0
  · simp only [Finset.mem_union, he, hf, or_true, false_and, if_true, if_false, add_zero, one_mul]
    calc
      _ = ((1 - beta s u * d) * (1 - d - b - a + c)) /
          ((1 - d - b) * (1 - beta s u * (d + a))) := by
        rw [← hBform]
        field_simp
        ring
      _ ≤ _ := rooted_mixed_avoidance_ratio_le hβ.le hβ1 hb0 ha0 hd0 hb ha hc0
  · simp only [Finset.mem_union, he, hf, or_self, and_self, if_false, add_zero, one_mul]
    calc
      _ = ((1 - beta s u * d) * (1 - beta s u * (d + a + b - c))) /
          ((1 - beta s u * (d + a)) * (1 - beta s u * (d + b))) := by
        rw [← hBform]
        field_simp
        ring
      _ ≤ _ := rooted_tilted_avoidance_ratio_le hβ.le hβ1 ha0 hb0 hd0 ha hb hc0

end Erdos4.Tilted
