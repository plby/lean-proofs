import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.Preamble


open Classical
noncomputable section

-- [TABLET NODE: ThreeCoordinateOutsideToOutsideSideCountEven]
lemma ThreeCoordinateOutsideToOutsideSideCountEven
    (u v : Fin 3 → ℝ)
    (huneg : ∃ i : Fin 3, u i < 0)
    (hvneg : ∃ i : Fin 3, v i < 0)
    (hNoDouble :
      ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ i j : Fin 3, i ≠ j →
          ¬ (((1 - t) * u i + t * v i = 0) ∧
              ((1 - t) * u j + t * v j = 0)))
    (hfinite :
      ∀ i : Fin 3,
        Set.Finite
          {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
            (1 - t) * u i + t * v i = 0 ∧
              ∀ j : Fin 3, j ≠ i → 0 < (1 - t) * u j + t * v j})
    (hNonconstant :
      ∀ i : Fin 3,
        ({t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
          (1 - t) * u i + t * v i = 0 ∧
            ∀ j : Fin 3, j ≠ i → 0 < (1 - t) * u j + t * v j} :
          Set ℝ).Nonempty → u i ≠ v i) :
    Even
      (Set.ncard
          {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
            (1 - t) * u 2 + t * v 2 = 0 ∧
              ∀ j : Fin 3, j ≠ 2 → 0 < (1 - t) * u j + t * v j} +
        Set.ncard
          {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
            (1 - t) * u 0 + t * v 0 = 0 ∧
              ∀ j : Fin 3, j ≠ 0 → 0 < (1 - t) * u j + t * v j} +
          Set.ncard
            {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
              (1 - t) * u 1 + t * v 1 = 0 ∧
                ∀ j : Fin 3, j ≠ 1 → 0 < (1 - t) * u j + t * v j}) := by
-- BODY

  let L (u v : Fin 3 → ℝ) (i : Fin 3) (t : ℝ) : ℝ :=
    (1 - t) * u i + t * v i

  let Side (u v : Fin 3 → ℝ) (i : Fin 3) : Set ℝ :=
    {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧
      L u v i t = 0 ∧ ∀ j : Fin 3, j ≠ i → 0 < L u v j t}

  let root (u v : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
    u i / (u i - v i)

  let NoDouble (u v : Fin 3 → ℝ) : Prop :=
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ i j : Fin 3, i ≠ j → ¬ (L u v i t = 0 ∧ L u v j t = 0)

  have root_mem_Ioo_of_pos_neg
      {u v : Fin 3 → ℝ} {i : Fin 3}
      (hu : 0 < u i) (hv : v i < 0) :
      root u v i ∈ Set.Ioo (0 : ℝ) 1 := by
    unfold root
    have hden : 0 < u i - v i := by linarith
    constructor
    · exact div_pos hu hden
    · exact (div_lt_one hden).2 (by linarith)

  have L_root_eq_zero_of_pos_neg
      {u v : Fin 3 → ℝ} {i : Fin 3}
      (hu : 0 < u i) (hv : v i < 0) :
      L u v i (root u v i) = 0 := by
    unfold L root
    have hden : u i - v i ≠ 0 := by linarith
    field_simp [hden]
    ring

  have L_zero_iff_eq_root_of_ne
      {u v : Fin 3 → ℝ} {i : Fin 3} {t : ℝ}
      (hden : u i - v i ≠ 0) :
      L u v i t = 0 ↔ t = root u v i := by
    unfold L root
    constructor
    · intro h
      field_simp [hden]
      field_simp [hden] at h
      ring_nf at h ⊢
      linarith
    · intro ht
      subst t
      field_simp [hden]
      ring

  have L_eq_den_mul_root_sub
      {u v : Fin 3 → ℝ} {i : Fin 3}
      (hden : u i - v i ≠ 0) (t : ℝ) :
      L u v i t = (u i - v i) * (root u v i - t) := by
    unfold L root
    field_simp [hden]
    ring

  have L_pos_before_root_of_pos_neg
      {u v : Fin 3 → ℝ} {i : Fin 3} {t : ℝ}
      (hu : 0 < u i) (hv : v i < 0) (ht : t < root u v i) :
      0 < L u v i t := by
    have hdenpos : 0 < u i - v i := by linarith
    have hden : u i - v i ≠ 0 := ne_of_gt hdenpos
    rw [L_eq_den_mul_root_sub (u := u) (v := v) (i := i) hden t]
    exact mul_pos hdenpos (sub_pos.mpr ht)

  have L_neg_after_root_of_pos_neg
      {u v : Fin 3 → ℝ} {i : Fin 3} {t : ℝ}
      (hu : 0 < u i) (hv : v i < 0) (ht : root u v i < t) :
      L u v i t < 0 := by
    have hdenpos : 0 < u i - v i := by linarith
    have hden : u i - v i ≠ 0 := ne_of_gt hdenpos
    rw [L_eq_den_mul_root_sub (u := u) (v := v) (i := i) hden t]
    exact mul_neg_of_pos_of_neg hdenpos (sub_neg.mpr ht)

  have root_mem_Ioo_of_neg_pos
      {u v : Fin 3 → ℝ} {i : Fin 3}
      (hu : u i < 0) (hv : 0 < v i) :
      root u v i ∈ Set.Ioo (0 : ℝ) 1 := by
    unfold root
    have hdenneg : u i - v i < 0 := by linarith
    constructor
    · exact div_pos_of_neg_of_neg hu hdenneg
    · rw [div_lt_one_of_neg hdenneg]
      linarith

  have L_root_eq_zero_of_neg_pos
      {u v : Fin 3 → ℝ} {i : Fin 3}
      (hu : u i < 0) (hv : 0 < v i) :
      L u v i (root u v i) = 0 := by
    unfold L root
    have hden : u i - v i ≠ 0 := by linarith
    field_simp [hden]
    ring

  have L_pos_after_root_of_neg_pos
      {u v : Fin 3 → ℝ} {i : Fin 3} {t : ℝ}
      (hu : u i < 0) (hv : 0 < v i) (ht : root u v i < t) :
      0 < L u v i t := by
    have hdenneg : u i - v i < 0 := by linarith
    have hden : u i - v i ≠ 0 := ne_of_lt hdenneg
    rw [L_eq_den_mul_root_sub (u := u) (v := v) (i := i) hden t]
    exact mul_pos_of_neg_of_neg hdenneg (sub_neg.mpr ht)

  have root_gt_of_L_pos_v_neg
      {u v : Fin 3 → ℝ} {i : Fin 3} {r : ℝ}
      (hr : r ∈ Set.Ioo (0 : ℝ) 1)
      (hLr : 0 < L u v i r) (hv : v i < 0) :
      r < root u v i := by
    have hu : 0 < u i := by
      unfold L at hLr
      nlinarith [hr.1, hr.2]
    have hdenpos : 0 < u i - v i := by linarith
    unfold L at hLr
    unfold root
    have hmul : r * (u i - v i) < u i := by nlinarith
    exact (lt_div_iff₀ hdenpos).2 hmul

  have root_lt_of_u_neg_L_pos
      {u v : Fin 3 → ℝ} {i : Fin 3} {r : ℝ}
      (hr : r ∈ Set.Ioo (0 : ℝ) 1)
      (hu : u i < 0) (hLr : 0 < L u v i r) :
      root u v i < r := by
    have hv : 0 < v i := by
      unfold L at hLr
      nlinarith [hr.1, hr.2]
    have hdenneg : u i - v i < 0 := by linarith
    unfold L at hLr
    unfold root
    rw [div_lt_iff_of_neg hdenneg]
    nlinarith

  have L_pos_between_param_and_endpoint_nonneg
      {u v : Fin 3 → ℝ} {i : Fin 3} {r t : ℝ}
      (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hrt : r < t) (ht1 : t < 1)
      (hrpos : 0 < L u v i r) (hv : 0 ≤ v i) :
      0 < L u v i t := by
    unfold L at hrpos ⊢
    have hden : 1 - r ≠ 0 := by linarith
    have hconv :
        (1 - t) * u i + t * v i =
          ((1 - t) / (1 - r)) * ((1 - r) * u i + r * v i) +
            ((t - r) / (1 - r)) * v i := by
      field_simp [hden]
      ring
    rw [hconv]
    have hleft : 0 < (1 - t) / (1 - r) := by
      exact div_pos (sub_pos.mpr ht1) (sub_pos.mpr hr.2)
    have hright : 0 < (t - r) / (1 - r) := by
      exact div_pos (sub_pos.mpr hrt) (sub_pos.mpr hr.2)
    nlinarith

  have L_pos_between_endpoint_nonneg_and_param
      {u v : Fin 3 → ℝ} {i : Fin 3} {t r : ℝ}
      (hr : r ∈ Set.Ioo (0 : ℝ) 1) (ht0 : 0 < t) (htr : t < r)
      (hu : 0 ≤ u i) (hrpos : 0 < L u v i r) :
      0 < L u v i t := by
    unfold L at hrpos ⊢
    have hden : r ≠ 0 := by linarith
    have hconv :
        (1 - t) * u i + t * v i =
          ((r - t) / r) * u i +
            (t / r) * ((1 - r) * u i + r * v i) := by
      field_simp [hden]
      ring
    rw [hconv]
    have hleft : 0 < (r - t) / r := by
      exact div_pos (sub_pos.mpr htr) hr.1
    have hright : 0 < t / r := by
      exact div_pos ht0 hr.1
    nlinarith

  have L_eq_of_two_roots
      (u v : Fin 3 → ℝ) (i : Fin 3) {s t : ℝ}
      (hst : s ≠ t) (hs : L u v i s = 0) (ht : L u v i t = 0) :
      u i = 0 ∧ v i = 0 := by
    unfold L at hs ht
    have hlin : (t - s) * (v i - u i) = 0 := by
      linarith
    have hvu : v i - u i = 0 := by
      exact mul_eq_zero.mp hlin |>.resolve_left (sub_ne_zero.mpr (Ne.symm hst))
    have huv : v i = u i := by linarith
    have hui : u i = 0 := by
      rw [huv] at hs
      linarith
    exact ⟨hui, by simpa [hui] using huv⟩

  have Side_subsingleton
      (u v : Fin 3 → ℝ) (i : Fin 3)
      (hfinite : (Side u v i).Finite) :
      (Side u v i).Subsingleton := by
    intro s hs t ht
    by_contra hst
    have hzero := L_eq_of_two_roots u v i hst hs.2.1 ht.2.1
    have hbetween : Set.Ioo s t ∪ Set.Ioo t s ⊆ Side u v i := by
      intro r hr
      have hrI : r ∈ Set.Ioo (0 : ℝ) 1 := by
        rcases hr with hst' | hts'
        · exact ⟨lt_trans hs.1.1 hst'.1, lt_trans hst'.2 ht.1.2⟩
        · exact ⟨lt_trans ht.1.1 hts'.1, lt_trans hts'.2 hs.1.2⟩
      refine ⟨hrI, ?_, ?_⟩
      · simp [L, hzero.1, hzero.2]
      · intro j hji
        rcases hr with hst' | hts'
        · have hsj := hs.2.2 j hji
          have htj := ht.2.2 j hji
          unfold L at hsj htj ⊢
          have hstlt : s < t := lt_trans hst'.1 hst'.2
          have hconv :
              ((t - r) / (t - s)) * ((1 - s) * u j + s * v j) +
                  ((r - s) / (t - s)) * ((1 - t) * u j + t * v j) =
                (1 - r) * u j + r * v j := by
            field_simp [sub_ne_zero.mpr (ne_of_gt hstlt)]
            ring
          have hlambda0 : 0 < (r - s) / (t - s) := by
            exact div_pos (sub_pos.mpr hst'.1) (sub_pos.mpr hstlt)
          have hlambdaT : 0 < (t - r) / (t - s) := by
            exact div_pos (sub_pos.mpr hst'.2) (sub_pos.mpr hstlt)
          have hpos :
              0 <
                ((t - r) / (t - s)) * ((1 - s) * u j + s * v j) +
                  ((r - s) / (t - s)) * ((1 - t) * u j + t * v j) := by
            nlinarith
          linarith
        · have hsj := hs.2.2 j hji
          have htj := ht.2.2 j hji
          unfold L at hsj htj ⊢
          have htslt : t < s := lt_trans hts'.1 hts'.2
          have hconv :
              ((s - r) / (s - t)) * ((1 - t) * u j + t * v j) +
                  ((r - t) / (s - t)) * ((1 - s) * u j + s * v j) =
                (1 - r) * u j + r * v j := by
            field_simp [sub_ne_zero.mpr (ne_of_gt htslt)]
            ring
          have hlambda0 : 0 < (r - t) / (s - t) := by
            exact div_pos (sub_pos.mpr hts'.1) (sub_pos.mpr htslt)
          have hlambdaT : 0 < (s - r) / (s - t) := by
            exact div_pos (sub_pos.mpr hts'.2) (sub_pos.mpr htslt)
          have hpos :
              0 <
                ((s - r) / (s - t)) * ((1 - t) * u j + t * v j) +
                  ((r - t) / (s - t)) * ((1 - s) * u j + s * v j) := by
            nlinarith
          linarith
    have hinfinite_interval : (Set.Ioo (min s t) (max s t)).Infinite := by
      have hminlt : min s t < max s t := by
        rcases lt_or_gt_of_ne hst with hlt | hgt
        · simpa [min_eq_left hlt.le, max_eq_right hlt.le] using hlt
        · simpa [min_eq_right hgt.le, max_eq_left hgt.le] using hgt
      exact Set.Ioo_infinite hminlt
    have hsubset_minmax :
        Set.Ioo (min s t) (max s t) ⊆ Set.Ioo s t ∪ Set.Ioo t s := by
      intro r hr
      by_cases hstlt : s < t
      · left
        simpa [min_eq_left hstlt.le, max_eq_right hstlt.le] using hr
      · have htslt : t < s := lt_of_le_of_ne (le_of_not_gt hstlt) (Ne.symm hst)
        right
        simpa [min_eq_right htslt.le, max_eq_left htslt.le] using hr
    exact hinfinite_interval.not_finite (hfinite.subset (fun r hr => hbetween (hsubset_minmax hr)))

  have Side_eq_singleton_of_mem
      {u v : Fin 3 → ℝ} {i : Fin 3} {r : ℝ}
      (hfinite : (Side u v i).Finite)
      (hr : r ∈ Side u v i) :
      Side u v i = {r} := by
    have hsub := Side_subsingleton u v i hfinite
    ext t
    constructor
    · intro ht
      exact hsub ht hr
    · intro ht
      rw [Set.mem_singleton_iff] at ht
      subst t
      exact hr

  have L_pos_of_between_pos
      (u v : Fin 3 → ℝ) (i : Fin 3) {s r t : ℝ}
      (hsr : s < r) (hrt : r < t)
      (hs : 0 < L u v i s) (ht : 0 < L u v i t) :
      0 < L u v i r := by
    unfold L at hs ht ⊢
    have hst : s < t := lt_trans hsr hrt
    have hconv :
        ((t - r) / (t - s)) * ((1 - s) * u i + s * v i) +
            ((r - s) / (t - s)) * ((1 - t) * u i + t * v i) =
          (1 - r) * u i + r * v i := by
      field_simp [sub_ne_zero.mpr (ne_of_gt hst)]
      ring
    have hleft : 0 < (t - r) / (t - s) := by
      exact div_pos (sub_pos.mpr hrt) (sub_pos.mpr hst)
    have hright : 0 < (r - s) / (t - s) := by
      exact div_pos (sub_pos.mpr hsr) (sub_pos.mpr hst)
    have hpos :
        0 <
          ((t - r) / (t - s)) * ((1 - s) * u i + s * v i) +
            ((r - s) / (t - s)) * ((1 - t) * u i + t * v i) := by
      nlinarith
    linarith

  have not_three_side_roots
      (u v : Fin 3 → ℝ)
      {r0 r1 r2 : ℝ}
      (hr0 : r0 ∈ Side u v 0)
      (hr1 : r1 ∈ Side u v 1)
      (hr2 : r2 ∈ Side u v 2) :
      False := by
    have h01 : r0 ≠ r1 := by
      intro h
      have hpos := hr0.2.2 1 (by decide)
      have hzero := hr1.2.1
      simpa [h, hzero] using hpos
    have h02 : r0 ≠ r2 := by
      intro h
      have hpos := hr0.2.2 2 (by decide)
      have hzero := hr2.2.1
      simpa [h, hzero] using hpos
    have h12 : r1 ≠ r2 := by
      intro h
      have hpos := hr1.2.2 2 (by decide)
      have hzero := hr2.2.1
      simpa [h, hzero] using hpos
    rcases lt_or_gt_of_ne h01 with h01lt | h10lt
    · rcases lt_or_gt_of_ne h02 with h02lt | h20lt
      · rcases lt_or_gt_of_ne h12 with h12lt | h21lt
        · have hpos0 := hr0.2.2 1 (by decide)
          have hpos2 := hr2.2.2 1 (by decide)
          have hpos1 := L_pos_of_between_pos u v 1 h01lt h12lt hpos0 hpos2
          simpa [hr1.2.1] using hpos1
        · have hpos0 := hr0.2.2 2 (by decide)
          have hpos1 := hr1.2.2 2 (by decide)
          have hpos2 := L_pos_of_between_pos u v 2 h02lt h21lt hpos0 hpos1
          simpa [hr2.2.1] using hpos2
      · have hpos2 := hr2.2.2 0 (by decide)
        have hpos1 := hr1.2.2 0 (by decide)
        have hpos0 := L_pos_of_between_pos u v 0 h20lt h01lt hpos2 hpos1
        simpa [hr0.2.1] using hpos0
    · rcases lt_or_gt_of_ne h02 with h02lt | h20lt
      · have hpos1 := hr1.2.2 0 (by decide)
        have hpos2 := hr2.2.2 0 (by decide)
        have hpos0 := L_pos_of_between_pos u v 0 h10lt h02lt hpos1 hpos2
        simpa [hr0.2.1] using hpos0
      · rcases lt_or_gt_of_ne h12 with h12lt | h21lt
        · have hpos1 := hr1.2.2 2 (by decide)
          have hpos0 := hr0.2.2 2 (by decide)
          have hpos2 := L_pos_of_between_pos u v 2 h12lt h20lt hpos1 hpos0
          simpa [hr2.2.1] using hpos2
        · have hpos2 := hr2.2.2 1 (by decide)
          have hpos0 := hr0.2.2 1 (by decide)
          have hpos1 := L_pos_of_between_pos u v 1 h21lt h10lt hpos2 hpos0
          simpa [hr1.2.1] using hpos1

  have side_root_sign_cases
      {u v : Fin 3 → ℝ} {i : Fin 3} {r : ℝ}
      (hr : r ∈ Side u v i)
      (hNonconstant : u i ≠ v i) :
      (u i < 0 ∧ 0 < v i) ∨ (0 < u i ∧ v i < 0) := by
    unfold Side at hr
    simp only [Set.mem_setOf_eq] at hr
    rcases hr with ⟨hrI, hzero, _hpos⟩
    unfold L at hzero
    by_cases hui_neg : u i < 0
    · have hv_pos : 0 < v i := by
        by_contra hv_not_pos
        have hv_nonpos : v i ≤ 0 := le_of_not_gt hv_not_pos
        nlinarith [hrI.1, hrI.2, hzero, hui_neg, hv_nonpos]
      exact Or.inl ⟨hui_neg, hv_pos⟩
    · have hu_nonneg : 0 ≤ u i := le_of_not_gt hui_neg
      have hv_neg : v i < 0 := by
        by_contra hv_not_neg
        have hv_nonneg : 0 ≤ v i := le_of_not_gt hv_not_neg
        have hu_zero : u i = 0 := by
          nlinarith [hrI.1, hrI.2, hzero, hu_nonneg, hv_nonneg]
        have hv_zero : v i = 0 := by
          nlinarith [hrI.1, hrI.2, hzero, hu_nonneg, hv_nonneg]
        exact hNonconstant (by linarith)
      have hu_pos : 0 < u i := by
        by_contra hu_not_pos
        have hu_nonpos : u i ≤ 0 := le_of_not_gt hu_not_pos
        have hu_zero : u i = 0 := le_antisymm hu_nonpos hu_nonneg
        nlinarith [hrI.1, hrI.2, hzero, hu_zero, hv_neg]
      exact Or.inr ⟨hu_pos, hv_neg⟩

  have side_root_has_later_companion
      {u v : Fin 3 → ℝ} {i : Fin 3} {r : ℝ}
      (hrSide : r ∈ Side u v i)
      (hui : u i < 0) (hvi : 0 < v i)
      (hvneg : ∃ j : Fin 3, v j < 0)
      (hNoDouble : NoDouble u v) :
      ∃ j : Fin 3, j ≠ i ∧ (Side u v j).Nonempty := by
    have hdeni : u i - v i ≠ 0 := by linarith
    have hri : r = root u v i :=
      (L_zero_iff_eq_root_of_ne (u := u) (v := v) (i := i) (t := r) hdeni).1
        hrSide.2.1
    let negs : Finset (Fin 3) := Finset.univ.filter (fun j : Fin 3 => v j < 0)
    have hnegs : negs.Nonempty := by
      rcases hvneg with ⟨j, hj⟩
      exact ⟨j, by simp [negs, hj]⟩
    obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image negs (fun j => root u v j) hnegs
    have hvk : v k < 0 := by
      simpa [negs] using (Finset.mem_filter.mp hk).2
    have hki : k ≠ i := by
      intro h
      subst k
      linarith
    have hLkr : 0 < L u v k r := hrSide.2.2 k hki
    have huk : 0 < u k := by
      unfold L at hLkr
      nlinarith [hrSide.1.1, hrSide.1.2, hvk]
    have hkr : r < root u v k :=
      root_gt_of_L_pos_v_neg (u := u) (v := v) (i := k) hrSide.1 hLkr hvk
    have hkI : root u v k ∈ Set.Ioo (0 : ℝ) 1 :=
      root_mem_Ioo_of_pos_neg (u := u) (v := v) (i := k) huk hvk
    refine ⟨k, hki, ⟨root u v k, ?_⟩⟩
    refine ⟨hkI, L_root_eq_zero_of_pos_neg (u := u) (v := v) (i := k) huk hvk, ?_⟩
    intro j hjk
    by_cases hji : j = i
    · subst j
      exact
        L_pos_after_root_of_neg_pos (u := u) (v := v) (i := i) hui hvi
          (by simpa [hri] using hkr)
    · have hLjr : 0 < L u v j r := hrSide.2.2 j hji
      by_cases hvj : v j < 0
      · have hle : root u v k ≤ root u v j := hmin j (by simp [negs, hvj])
        have huj : 0 < u j := by
          unfold L at hLjr
          nlinarith [hrSide.1.1, hrSide.1.2, hvj]
        have hroot_ne : root u v k ≠ root u v j := by
          intro hroot
          have hzj : L u v j (root u v k) = 0 := by
            simpa [hroot] using
              L_root_eq_zero_of_pos_neg (u := u) (v := v) (i := j) huj hvj
          exact hNoDouble (root u v k) hkI k j (Ne.symm hjk)
            ⟨L_root_eq_zero_of_pos_neg (u := u) (v := v) (i := k) huk hvk, hzj⟩
        have hlt : root u v k < root u v j := lt_of_le_of_ne hle hroot_ne
        exact L_pos_before_root_of_pos_neg (u := u) (v := v) (i := j) huj hvj hlt
      · have hvj_nonneg : 0 ≤ v j := le_of_not_gt hvj
        exact
          L_pos_between_param_and_endpoint_nonneg (u := u) (v := v) (i := j)
            hrSide.1 hkr hkI.2 hLjr hvj_nonneg

  have side_root_has_earlier_companion
      {u v : Fin 3 → ℝ} {i : Fin 3} {r : ℝ}
      (hrSide : r ∈ Side u v i)
      (hui : 0 < u i) (hvi : v i < 0)
      (huneg : ∃ j : Fin 3, u j < 0)
      (hNoDouble : NoDouble u v) :
      ∃ j : Fin 3, j ≠ i ∧ (Side u v j).Nonempty := by
    have hdeni : u i - v i ≠ 0 := by linarith
    have hri : r = root u v i :=
      (L_zero_iff_eq_root_of_ne (u := u) (v := v) (i := i) (t := r) hdeni).1
        hrSide.2.1
    let negs : Finset (Fin 3) := Finset.univ.filter (fun j : Fin 3 => u j < 0)
    have hnegs : negs.Nonempty := by
      rcases huneg with ⟨j, hj⟩
      exact ⟨j, by simp [negs, hj]⟩
    obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image negs (fun j => root u v j) hnegs
    have huk : u k < 0 := by
      simpa [negs] using (Finset.mem_filter.mp hk).2
    have hki : k ≠ i := by
      intro h
      subst k
      linarith
    have hLkr : 0 < L u v k r := hrSide.2.2 k hki
    have hvk : 0 < v k := by
      unfold L at hLkr
      nlinarith [hrSide.1.1, hrSide.1.2, huk]
    have hkr : root u v k < r :=
      root_lt_of_u_neg_L_pos (u := u) (v := v) (i := k) hrSide.1 huk hLkr
    have hkI : root u v k ∈ Set.Ioo (0 : ℝ) 1 :=
      root_mem_Ioo_of_neg_pos (u := u) (v := v) (i := k) huk hvk
    refine ⟨k, hki, ⟨root u v k, ?_⟩⟩
    refine ⟨hkI, L_root_eq_zero_of_neg_pos (u := u) (v := v) (i := k) huk hvk, ?_⟩
    intro j hjk
    by_cases hji : j = i
    · subst j
      exact
        L_pos_before_root_of_pos_neg (u := u) (v := v) (i := i) hui hvi
          (by simpa [hri] using hkr)
    · have hLjr : 0 < L u v j r := hrSide.2.2 j hji
      by_cases huj : u j < 0
      · have hle : root u v j ≤ root u v k := hmax j (by simp [negs, huj])
        have hvj : 0 < v j := by
          unfold L at hLjr
          nlinarith [hrSide.1.1, hrSide.1.2, huj]
        have hroot_ne : root u v j ≠ root u v k := by
          intro hroot
          have hzj : L u v j (root u v k) = 0 := by
            simpa [hroot] using
              L_root_eq_zero_of_neg_pos (u := u) (v := v) (i := j) huj hvj
          exact hNoDouble (root u v k) hkI k j (Ne.symm hjk)
            ⟨L_root_eq_zero_of_neg_pos (u := u) (v := v) (i := k) huk hvk, hzj⟩
        have hlt : root u v j < root u v k := lt_of_le_of_ne hle hroot_ne
        exact L_pos_after_root_of_neg_pos (u := u) (v := v) (i := j) huj hvj hlt
      · have huj_nonneg : 0 ≤ u j := le_of_not_gt huj
        exact
          L_pos_between_endpoint_nonneg_and_param (u := u) (v := v) (i := j)
            hrSide.1 hkI.1 hkr huj_nonneg hLjr

  have outside_to_outside_side_sum_even
      {u v : Fin 3 → ℝ}
      (huneg : ∃ i : Fin 3, u i < 0)
      (hvneg : ∃ i : Fin 3, v i < 0)
      (hNoDouble : NoDouble u v)
      (hfinite : ∀ i : Fin 3, (Side u v i).Finite)
      (hNonconstant : ∀ i : Fin 3, (Side u v i).Nonempty → u i ≠ v i) :
      Even (Set.ncard (Side u v 2) + Set.ncard (Side u v 0) + Set.ncard (Side u v 1)) := by
    have hcompanion :
        ∀ i : Fin 3, (Side u v i).Nonempty →
          ∃ j : Fin 3, j ≠ i ∧ (Side u v j).Nonempty := by
      intro i hSi
      rcases hSi with ⟨r, hr⟩
      rcases side_root_sign_cases (u := u) (v := v) (i := i) (r := r) hr
          (hNonconstant i ⟨r, hr⟩) with hnegpos | hposneg
      · exact
          side_root_has_later_companion (u := u) (v := v) (i := i) (r := r)
            hr hnegpos.1 hnegpos.2 hvneg hNoDouble
      · exact
          side_root_has_earlier_companion (u := u) (v := v) (i := i) (r := r)
            hr hposneg.1 hposneg.2 huneg hNoDouble
    have hncard_one :
        ∀ i : Fin 3, (Side u v i).Nonempty → Set.ncard (Side u v i) = 1 := by
      intro i hSi
      rcases hSi with ⟨r, hr⟩
      rw [Side_eq_singleton_of_mem (u := u) (v := v) (i := i) (hfinite i) hr]
      simp
    have hncard_zero :
        ∀ i : Fin 3, ¬ (Side u v i).Nonempty → Set.ncard (Side u v i) = 0 := by
      intro i hSi
      have hempty : Side u v i = ∅ := by
        ext t
        constructor
        · intro ht
          exact False.elim (hSi ⟨t, ht⟩)
        · intro ht
          cases ht
      rw [hempty]
      simp
    by_cases h0 : (Side u v 0).Nonempty
    · by_cases h1 : (Side u v 1).Nonempty
      · by_cases h2 : (Side u v 2).Nonempty
        · exfalso
          rcases h0 with ⟨r0, hr0⟩
          rcases h1 with ⟨r1, hr1⟩
          rcases h2 with ⟨r2, hr2⟩
          exact not_three_side_roots u v hr0 hr1 hr2
        · have h0n := hncard_one 0 h0
          have h1n := hncard_one 1 h1
          have h2n := hncard_zero 2 h2
          rw [h2n, h0n, h1n]
          norm_num
      · by_cases h2 : (Side u v 2).Nonempty
        · have h0n := hncard_one 0 h0
          have h1n := hncard_zero 1 h1
          have h2n := hncard_one 2 h2
          rw [h2n, h0n, h1n]
          norm_num
        · exfalso
          rcases hcompanion 0 h0 with ⟨j, hji, hjnon⟩
          fin_cases j
          · exact hji rfl
          · exact h1 hjnon
          · exact h2 hjnon
    · by_cases h1 : (Side u v 1).Nonempty
      · by_cases h2 : (Side u v 2).Nonempty
        · have h0n := hncard_zero 0 h0
          have h1n := hncard_one 1 h1
          have h2n := hncard_one 2 h2
          rw [h2n, h0n, h1n]
          norm_num
        · exfalso
          rcases hcompanion 1 h1 with ⟨j, hji, hjnon⟩
          fin_cases j
          · exact h0 hjnon
          · exact hji rfl
          · exact h2 hjnon
      · by_cases h2 : (Side u v 2).Nonempty
        · exfalso
          rcases hcompanion 2 h2 with ⟨j, hji, hjnon⟩
          fin_cases j
          · exact h0 hjnon
          · exact h1 hjnon
          · exact hji rfl
        · have h0n := hncard_zero 0 h0
          have h1n := hncard_zero 1 h1
          have h2n := hncard_zero 2 h2
          rw [h2n, h0n, h1n]
          norm_num

  change
    Even (Set.ncard (Side u v 2) + Set.ncard (Side u v 0) + Set.ncard (Side u v 1))
  change NoDouble u v at hNoDouble
  change ∀ i : Fin 3, (Side u v i).Finite at hfinite
  change ∀ i : Fin 3, (Side u v i).Nonempty → u i ≠ v i at hNonconstant
  exact outside_to_outside_side_sum_even huneg hvneg hNoDouble hfinite hNonconstant
