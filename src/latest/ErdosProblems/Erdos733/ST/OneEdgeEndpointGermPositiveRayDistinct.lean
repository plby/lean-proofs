import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: OneEdgeEndpointGermPositiveRayDistinct]
lemma OneEdgeEndpointGermPositiveRayDistinct
    (A : Set (EuclideanSpace ℝ (Fin 2)))
    (V : Finset (EuclideanSpace ℝ (Fin 2)))
    (E : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (p q : EuclideanSpace ℝ (Fin 2))
    (hA :
      A =
        (V : Set (EuclideanSpace ℝ (Fin 2))) ∪
          ⋃ e : {e // e ∈ E}, segment ℝ e.1.1 e.1.2)
    (hEdgeNondegenerate :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ≠ e.2)
    (hEdgeOpenInteriorsDisjoint :
      ∀ e f : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → f ∈ E → e ≠ f →
          Disjoint (openSegment ℝ e.1 e.2) (openSegment ℝ f.1 f.2))
    (hpq : p ≠ q)
    (hNewInteriorDisjoint : Disjoint (openSegment ℝ p q) A) :
    let Incident :=
      {e : {e // e ∈ E} // e.1.1 = p ∨ e.1.2 = p}
    let u : Option Incident → EuclideanSpace ℝ (Fin 2) :=
      fun i =>
        match i with
        | none => q - p
        | some e =>
            if e.1.1.1 = p then e.1.1.2 - p else e.1.1.1 - p
    (∀ i : Option Incident, u i ≠ 0) ∧
      (∀ {i j : Option Incident},
        (∃ t : ℝ, 0 < t ∧ u j = t • u i) → i = j) := by
-- BODY
  classical
  intro Incident u
  have hnew_ne : q - p ≠ 0 := by
    intro h
    exact hpq (sub_eq_zero.mp h).symm
  have incident_other_eq
      (e : Incident) (hsrc_neg : ¬ e.1.1.1 = p) : e.1.1.2 = p := by
    rcases e.2 with hsrc | htgt
    · exact False.elim (hsrc_neg hsrc)
    · exact htgt
  have oldDir_ne_zero : ∀ e : Incident,
      (if e.1.1.1 = p then e.1.1.2 - p else e.1.1.1 - p) ≠ 0 := by
    intro e
    by_cases hsrc : e.1.1.1 = p
    · simp [hsrc, sub_eq_zero]
      intro htgt
      exact hEdgeNondegenerate e.1.1 e.1.2 (by simp [hsrc, htgt])
    · simp [hsrc, sub_eq_zero]
  have oldDir_open_mem
      (e : Incident) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
      p + c • (if e.1.1.1 = p then e.1.1.2 - p else e.1.1.1 - p) ∈
        openSegment ℝ e.1.1.1 e.1.1.2 := by
    by_cases hsrc : e.1.1.1 = p
    · have hx :
          AffineMap.lineMap p e.1.1.2 c ∈ openSegment ℝ p e.1.1.2 :=
        lineMap_mem_openSegment ℝ p e.1.1.2 ⟨hc0, hc1⟩
      have hpoint :
          p + c • (if e.1.1.1 = p then e.1.1.2 - p else e.1.1.1 - p) =
            AffineMap.lineMap p e.1.1.2 c := by
        rw [AffineMap.lineMap_apply_module]
        simp [hsrc]
        module
      rw [hpoint]
      simpa [hsrc] using hx
    · have htgt : e.1.1.2 = p := incident_other_eq e hsrc
      have hx :
          AffineMap.lineMap p e.1.1.1 c ∈ openSegment ℝ p e.1.1.1 :=
        lineMap_mem_openSegment ℝ p e.1.1.1 ⟨hc0, hc1⟩
      have hx' :
          AffineMap.lineMap p e.1.1.1 c ∈ openSegment ℝ e.1.1.1 p := by
        simpa [openSegment_symm] using hx
      have hpoint :
          p + c • (if e.1.1.1 = p then e.1.1.2 - p else e.1.1.1 - p) =
            AffineMap.lineMap p e.1.1.1 c := by
        rw [AffineMap.lineMap_apply_module]
        simp [hsrc]
        module
      rw [hpoint]
      simpa [htgt] using hx'
  have oldDir_segment_mem
      (e : Incident) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
      p + c • (if e.1.1.1 = p then e.1.1.2 - p else e.1.1.1 - p) ∈
        segment ℝ e.1.1.1 e.1.1.2 := by
    by_cases hsrc : e.1.1.1 = p
    · have hx :
          AffineMap.lineMap p e.1.1.2 c ∈ segment ℝ p e.1.1.2 := by
        rw [segment_eq_image_lineMap]
        exact ⟨c, ⟨hc0, hc1⟩, rfl⟩
      have hpoint :
          p + c • (if e.1.1.1 = p then e.1.1.2 - p else e.1.1.1 - p) =
            AffineMap.lineMap p e.1.1.2 c := by
        rw [AffineMap.lineMap_apply_module]
        simp [hsrc]
        module
      rw [hpoint]
      simpa [hsrc] using hx
    · have htgt : e.1.1.2 = p := incident_other_eq e hsrc
      have hx :
          AffineMap.lineMap p e.1.1.1 c ∈ segment ℝ p e.1.1.1 := by
        rw [segment_eq_image_lineMap]
        exact ⟨c, ⟨hc0, hc1⟩, rfl⟩
      have hx' :
          AffineMap.lineMap p e.1.1.1 c ∈ segment ℝ e.1.1.1 p := by
        simpa [segment_symm] using hx
      have hpoint :
          p + c • (if e.1.1.1 = p then e.1.1.2 - p else e.1.1.1 - p) =
            AffineMap.lineMap p e.1.1.1 c := by
        rw [AffineMap.lineMap_apply_module]
        simp [hsrc]
        module
      rw [hpoint]
      simpa [htgt] using hx'
  have oldDir_A_mem
      (e : Incident) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
      p + c • (if e.1.1.1 = p then e.1.1.2 - p else e.1.1.1 - p) ∈ A := by
    rw [hA]
    right
    exact Set.mem_iUnion.2
      ⟨e.1, oldDir_segment_mem e hc0 hc1⟩
  have old_new_forbidden :
      ∀ e : Incident,
        ¬ ∃ t : ℝ, 0 < t ∧
          (if e.1.1.1 = p then e.1.1.2 - p else e.1.1.1 - p) =
            t • (q - p) := by
    intro e
    rintro ⟨t, ht, hsame⟩
    let c : ℝ := min 1 t / 2
    have hc_pos : 0 < c := by
      dsimp [c]
      positivity
    have hc_lt_one : c < 1 := by
      dsimp [c]
      have hmin_le : min 1 t ≤ 1 := min_le_left 1 t
      nlinarith [lt_min zero_lt_one ht]
    have hc_le_t : c ≤ t := by
      dsimp [c]
      have hmin_le : min 1 t ≤ t := min_le_right 1 t
      nlinarith [lt_min zero_lt_one ht]
    have hc_div_nonneg : 0 ≤ c / t := div_nonneg (le_of_lt hc_pos) (le_of_lt ht)
    have hc_div_le_one : c / t ≤ 1 := (div_le_one ht).2 hc_le_t
    let x : EuclideanSpace ℝ (Fin 2) := p + (c / t) •
      (if e.1.1.1 = p then e.1.1.2 - p else e.1.1.1 - p)
    have hx_open_new : x ∈ openSegment ℝ p q := by
      rw [openSegment_eq_image_lineMap]
      refine ⟨c, ⟨hc_pos, hc_lt_one⟩, ?_⟩
      rw [AffineMap.lineMap_apply_module]
      dsimp [x]
      rw [hsame, smul_smul]
      have hcoeff : c / t * t = c := by field_simp [ne_of_gt ht]
      rw [hcoeff]
      module
    have hxA : x ∈ A := by
      dsimp [x]
      exact oldDir_A_mem e hc_div_nonneg hc_div_le_one
    exact (Set.disjoint_left.mp hNewInteriorDisjoint) hx_open_new hxA
  have new_old_forbidden :
      ∀ e : Incident,
        ¬ ∃ t : ℝ, 0 < t ∧
          q - p =
            t • (if e.1.1.1 = p then e.1.1.2 - p else e.1.1.1 - p) := by
    intro e
    rintro ⟨t, ht, hsame⟩
    let c : ℝ := min 1 t / 2
    have hc_pos : 0 < c := by
      dsimp [c]
      positivity
    have hc_lt_one : c < 1 := by
      dsimp [c]
      have hmin_le : min 1 t ≤ 1 := min_le_left 1 t
      nlinarith [lt_min zero_lt_one ht]
    have hct : c < t := by
      dsimp [c]
      have hmin_le : min 1 t ≤ t := min_le_right 1 t
      nlinarith [lt_min zero_lt_one ht]
    have hc_div_pos : 0 < c / t := div_pos hc_pos ht
    have hc_div_lt_one : c / t < 1 := (div_lt_one ht).2 hct
    let x : EuclideanSpace ℝ (Fin 2) := p + c •
      (if e.1.1.1 = p then e.1.1.2 - p else e.1.1.1 - p)
    have hx_open_new : x ∈ openSegment ℝ p q := by
      rw [openSegment_eq_image_lineMap]
      refine ⟨c / t, ⟨hc_div_pos, hc_div_lt_one⟩, ?_⟩
      rw [AffineMap.lineMap_apply_module]
      dsimp [x]
      have hq_eq : q = p + t •
          (if e.1.1.1 = p then e.1.1.2 - p else e.1.1.1 - p) := by
        calc
          q = (q - p) + p := by abel
          _ = t • (if e.1.1.1 = p then e.1.1.2 - p else e.1.1.1 - p) + p := by
            rw [hsame]
          _ = p + t • (if e.1.1.1 = p then e.1.1.2 - p else e.1.1.1 - p) := by
            abel
      rw [hq_eq]
      have hcoeff : c / t * t = c := by field_simp [ne_of_gt ht]
      rw [smul_add, smul_smul, hcoeff]
      module
    have hxA : x ∈ A := by
      dsimp [x]
      exact oldDir_A_mem e (le_of_lt hc_pos) (le_of_lt hc_lt_one)
    exact (Set.disjoint_left.mp hNewInteriorDisjoint) hx_open_new hxA
  have old_old_forbidden :
      ∀ e f : Incident, e.1.1 ≠ f.1.1 →
        ¬ ∃ t : ℝ, 0 < t ∧
          (if f.1.1.1 = p then f.1.1.2 - p else f.1.1.1 - p) =
            t • (if e.1.1.1 = p then e.1.1.2 - p else e.1.1.1 - p) := by
    intro e f hef
    rintro ⟨t, ht, hsame⟩
    let c : ℝ := min 1 t / 2
    have hc_pos : 0 < c := by
      dsimp [c]
      positivity
    have hc_lt_one : c < 1 := by
      dsimp [c]
      have hmin_le : min 1 t ≤ 1 := min_le_left 1 t
      nlinarith [lt_min zero_lt_one ht]
    have hct : c < t := by
      dsimp [c]
      have hmin_le : min 1 t ≤ t := min_le_right 1 t
      nlinarith [lt_min zero_lt_one ht]
    have hc_div_pos : 0 < c / t := div_pos hc_pos ht
    have hc_div_lt_one : c / t < 1 := (div_lt_one ht).2 hct
    let x : EuclideanSpace ℝ (Fin 2) := p + c •
      (if e.1.1.1 = p then e.1.1.2 - p else e.1.1.1 - p)
    have hx_e : x ∈ openSegment ℝ e.1.1.1 e.1.1.2 := by
      dsimp [x]
      exact oldDir_open_mem e hc_pos hc_lt_one
    have hx_f : x ∈ openSegment ℝ f.1.1.1 f.1.1.2 := by
      have hx' :
          p + (c / t) •
              (if f.1.1.1 = p then f.1.1.2 - p else f.1.1.1 - p) ∈
            openSegment ℝ f.1.1.1 f.1.1.2 :=
        oldDir_open_mem f hc_div_pos hc_div_lt_one
      convert hx' using 1
      dsimp [x]
      rw [hsame, smul_smul]
      have hcoeff : c / t * t = c := by field_simp [ne_of_gt ht]
      rw [hcoeff]
    exact (Set.disjoint_left.mp
      (hEdgeOpenInteriorsDisjoint e.1.1 f.1.1 e.1.2 f.1.2 hef)) hx_e hx_f
  refine ⟨?_, ?_⟩
  · intro i
    cases i with
    | none =>
        exact hnew_ne
    | some e =>
        exact oldDir_ne_zero e
  · intro i j hsame
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some e =>
            exfalso
            exact old_new_forbidden e hsame
    | some e =>
        cases j with
        | none =>
            exfalso
            exact new_old_forbidden e hsame
        | some f =>
            by_cases hef : e.1.1 = f.1.1
            · have hsub : e.1 = f.1 := Subtype.ext hef
              exact congrArg some (Subtype.ext hsub)
            · exfalso
              exact old_old_forbidden e f hef hsame
