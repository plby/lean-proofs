import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.Preamble


open Classical
noncomputable section

-- [TABLET NODE: ThreeCoordinateInsideToOutsideSideCountOdd]
lemma ThreeCoordinateInsideToOutsideSideCountOdd
    (u v : Fin 3 → ℝ)
    (hu : ∀ i : Fin 3, 0 < u i)
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
              ∀ j : Fin 3, j ≠ i → 0 < (1 - t) * u j + t * v j}) :
    Odd
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

  have L_pos_of_pos_nonneg
      {u v : Fin 3 → ℝ} {i : Fin 3} {t : ℝ}
      (hu : 0 < u i) (hv : 0 ≤ v i) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
      0 < L u v i t := by
    unfold L
    nlinarith [ht.1, ht.2]

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

  have root_side_of_min_negative
      {u v : Fin 3 → ℝ} {k : Fin 3}
      (hu : ∀ i : Fin 3, 0 < u i)
      (hvk : v k < 0)
      (hmin : ∀ j : Fin 3, v j < 0 → root u v k ≤ root u v j)
      (hNoDouble : NoDouble u v) :
      root u v k ∈ Side u v k := by
    have hkI := root_mem_Ioo_of_pos_neg (u := u) (v := v) (i := k) (hu k) hvk
    refine ⟨hkI, L_root_eq_zero_of_pos_neg (u := u) (v := v) (i := k) (hu k) hvk, ?_⟩
    intro j hjk
    by_cases hvj : v j < 0
    · have hjI := root_mem_Ioo_of_pos_neg (u := u) (v := v) (i := j) (hu j) hvj
      have hle := hmin j hvj
      have hne : root u v k ≠ root u v j := by
        intro hroot
        have hzj :
            L u v j (root u v k) = 0 := by
          simpa [hroot] using
            L_root_eq_zero_of_pos_neg (u := u) (v := v) (i := j) (hu j) hvj
        exact hNoDouble (root u v k) hkI k j (Ne.symm hjk)
          ⟨L_root_eq_zero_of_pos_neg (u := u) (v := v) (i := k) (hu k) hvk, hzj⟩
      have hlt : root u v k < root u v j := lt_of_le_of_ne hle hne
      exact L_pos_before_root_of_pos_neg (u := u) (v := v) (i := j) (hu j) hvj hlt
    · have hvj_nonneg : 0 ≤ v j := le_of_not_gt hvj
      exact L_pos_of_pos_nonneg (u := u) (v := v) (i := j) (hu j) hvj_nonneg hkI

  have Side_empty_of_not_min_negative
      {u v : Fin 3 → ℝ} {k j : Fin 3}
      (hu : ∀ i : Fin 3, 0 < u i)
      (hvk : v k < 0)
      (hmin : ∀ i : Fin 3, v i < 0 → root u v k ≤ root u v i)
      (hNoDouble : NoDouble u v)
      (hjk : j ≠ k) :
      Side u v j = ∅ := by
    ext t
    constructor
    · intro ht
      by_cases hvj : v j < 0
      · have hdenj : u j - v j ≠ 0 := by linarith [hu j, hvj]
        have htroot : t = root u v j :=
          (L_zero_iff_eq_root_of_ne (u := u) (v := v) (i := j) (t := t) hdenj).1 ht.2.1
        have hle := hmin j hvj
        have hne : root u v k ≠ root u v j := by
          intro hroot
          have hzk := L_root_eq_zero_of_pos_neg (u := u) (v := v) (i := k) (hu k) hvk
          have hzj : L u v j (root u v k) = 0 := by
            simpa [hroot] using
              L_root_eq_zero_of_pos_neg (u := u) (v := v) (i := j) (hu j) hvj
          exact hNoDouble (root u v k)
            (root_mem_Ioo_of_pos_neg (u := u) (v := v) (i := k) (hu k) hvk)
            k j (Ne.symm hjk) ⟨hzk, hzj⟩
        have hlt : root u v k < root u v j := lt_of_le_of_ne hle hne
        have hkneg : L u v k t < 0 := by
          subst t
          exact L_neg_after_root_of_pos_neg (u := u) (v := v) (i := k) (hu k) hvk hlt
        have hkpos := ht.2.2 k (Ne.symm hjk)
        linarith
      · have hvj_nonneg : 0 ≤ v j := le_of_not_gt hvj
        have hjpos := L_pos_of_pos_nonneg (u := u) (v := v) (i := j) (hu j) hvj_nonneg ht.1
        rw [ht.2.1] at hjpos
        exact (lt_irrefl (0 : ℝ) hjpos).elim
    · intro h
      exact False.elim h

  have inside_to_outside_side_sum_one
      {u v : Fin 3 → ℝ}
      (hu : ∀ i : Fin 3, 0 < u i)
      (hneg : ∃ i : Fin 3, v i < 0)
      (hNoDouble : NoDouble u v)
      (hfinite : ∀ i : Fin 3, (Side u v i).Finite) :
      Set.ncard (Side u v 2) + Set.ncard (Side u v 0) + Set.ncard (Side u v 1) = 1 := by
    let negs : Finset (Fin 3) := Finset.univ.filter (fun i : Fin 3 => v i < 0)
    have hnegs : negs.Nonempty := by
      rcases hneg with ⟨i, hi⟩
      exact ⟨i, by simp [negs, hi]⟩
    obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image negs (fun i => root u v i) hnegs
    have hvk : v k < 0 := by
      simpa [negs] using (Finset.mem_filter.mp hk).2
    have hmin' : ∀ j : Fin 3, v j < 0 → root u v k ≤ root u v j := by
      intro j hvj
      exact hmin j (by simp [negs, hvj])
    have hrootSide : root u v k ∈ Side u v k :=
      root_side_of_min_negative (u := u) (v := v) (k := k) hu hvk hmin' hNoDouble
    have hSidek : Side u v k = {root u v k} :=
      Side_eq_singleton_of_mem (u := u) (v := v) (i := k) (hfinite k) hrootSide
    fin_cases k
    · have hSide0 : Side u v 0 = {root u v 0} := by
        simpa using hSidek
      have hSide1 : Side u v 1 = ∅ :=
        Side_empty_of_not_min_negative (u := u) (v := v) (k := 0) (j := 1)
          hu hvk hmin' hNoDouble (by decide)
      have hSide2 : Side u v 2 = ∅ :=
        Side_empty_of_not_min_negative (u := u) (v := v) (k := 0) (j := 2)
          hu hvk hmin' hNoDouble (by decide)
      simp [hSide0, hSide1, hSide2]
    · have hSide1 : Side u v 1 = {root u v 1} := by
        simpa using hSidek
      have hSide0 : Side u v 0 = ∅ :=
        Side_empty_of_not_min_negative (u := u) (v := v) (k := 1) (j := 0)
          hu hvk hmin' hNoDouble (by decide)
      have hSide2 : Side u v 2 = ∅ :=
        Side_empty_of_not_min_negative (u := u) (v := v) (k := 1) (j := 2)
          hu hvk hmin' hNoDouble (by decide)
      simp [hSide1, hSide0, hSide2]
    · have hSide2 : Side u v 2 = {root u v 2} := by
        simpa using hSidek
      have hSide0 : Side u v 0 = ∅ :=
        Side_empty_of_not_min_negative (u := u) (v := v) (k := 2) (j := 0)
          hu hvk hmin' hNoDouble (by decide)
      have hSide1 : Side u v 1 = ∅ :=
        Side_empty_of_not_min_negative (u := u) (v := v) (k := 2) (j := 1)
          hu hvk hmin' hNoDouble (by decide)
      simp [hSide2, hSide0, hSide1]

  change
    Odd (Set.ncard (Side u v 2) + Set.ncard (Side u v 0) + Set.ncard (Side u v 1))
  change NoDouble u v at hNoDouble
  change ∀ i : Fin 3, (Side u v i).Finite at hfinite
  have hsum := inside_to_outside_side_sum_one hu hvneg hNoDouble hfinite
  rw [hsum]
  norm_num
