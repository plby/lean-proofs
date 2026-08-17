/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# The Elekes--Sharir line construction

This file develops the elementary coordinate geometry used in the reduction
of the planar equal-distance problem to incidences of lines in three-space.
-/

namespace Erdos95.ES

/-- A point of the Euclidean plane. -/
abbrev PlanePoint := EuclideanSpace ℝ (Fin 2)

/-- Coordinate three-space.  Its topology is not needed for the algebraic
Elekes--Sharir correspondence. -/
abbrev Space3 := Fin 3 → ℝ

/-- Squared Euclidean distance in coordinates. -/
noncomputable def sqDist (p q : PlanePoint) : ℝ :=
  (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2

theorem sqDist_eq_dist_sq (p q : PlanePoint) : sqDist p q = dist p q ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [sqDist, Fin.sum_univ_two, Real.dist_eq]
  rw [abs_sub_comm (p 0), abs_sub_comm (p 1), sq_abs, sq_abs]
  ring

theorem sqDist_eq_iff_dist_eq {p q r s : PlanePoint} :
    sqDist p q = sqDist r s ↔ dist p q = dist r s := by
  rw [sqDist_eq_dist_sq, sqDist_eq_dist_sq]
  exact sq_eq_sq_iff_eq_or_eq_neg.trans <| by
    constructor
    · rintro (h | h)
      · exact h
      · nlinarith [dist_nonneg (x := p) (y := q), dist_nonneg (x := r) (y := s)]
    · exact Or.inl

/-- The normalized parametrization of the Elekes--Sharir line indexed by
`(p,q)`.  The third coordinate is the line parameter. -/
noncomputable def linePoint (p q : PlanePoint) (t : ℝ) : Space3 :=
  ![(p 0 + q 0) / 2 + t * (q 1 - p 1) / 2,
    (p 1 + q 1) / 2 + t * (p 0 - q 0) / 2,
    t]

/-- The normalized line parameter is recovered from the third coordinate. -/
theorem linePoint_parameter_injective (p q : PlanePoint) :
    Function.Injective (linePoint p q) := by
  intro t u h
  simpa [linePoint] using congrFun h (2 : Fin 3)

/-- Two normalized Elekes--Sharir lines which agree at two distinct
parameters have the same pair of indices. -/
theorem eq_of_linePoint_eq_at_two
    {p q r s : PlanePoint} {t u : ℝ} (htu : t ≠ u)
    (ht : linePoint p q t = linePoint r s t)
    (hu : linePoint p q u = linePoint r s u) :
    p = r ∧ q = s := by
  have ht0 := congrFun ht (0 : Fin 3)
  have ht1 := congrFun ht (1 : Fin 3)
  have hu0 := congrFun hu (0 : Fin 3)
  have hu1 := congrFun hu (1 : Fin 3)
  simp [linePoint] at ht0 ht1 hu0 hu1
  have hprod1 :
      (t - u) * ((q 1 - p 1) - (s 1 - r 1)) = 0 := by
    nlinarith [ht0, hu0]
  have hprod0 :
      (t - u) * ((p 0 - q 0) - (r 0 - s 0)) = 0 := by
    nlinarith [ht1, hu1]
  have htu' : t - u ≠ 0 := sub_ne_zero.mpr htu
  have hslope1 : q 1 - p 1 = s 1 - r 1 := by
    exact sub_eq_zero.mp (mul_eq_zero.mp hprod1 |>.resolve_left htu')
  have hslope0 : p 0 - q 0 = r 0 - s 0 := by
    exact sub_eq_zero.mp (mul_eq_zero.mp hprod0 |>.resolve_left htu')
  have hintercept0 : p 0 + q 0 = r 0 + s 0 := by
    rw [hslope1] at ht0
    linarith [ht0]
  have hintercept1 : p 1 + q 1 = r 1 + s 1 := by
    rw [hslope0] at ht1
    linarith [ht1]
  have hp0 : p 0 = r 0 := by linarith
  have hq0 : q 0 = s 0 := by linarith
  have hp1 : p 1 = r 1 := by linarith
  have hq1 : q 1 = s 1 := by linarith
  constructor
  · apply PiLp.ext
    intro i
    fin_cases i
    · exact hp0
    · exact hp1
  · apply PiLp.ext
    intro i
    fin_cases i
    · exact hq0
    · exact hq1

/-- Incidence with an Elekes--Sharir line. -/
def OnLine (p q : PlanePoint) (x : Space3) : Prop :=
  ∃ t : ℝ, x = linePoint p q t

/-- Two Elekes--Sharir lines have a common point. -/
def Intersects (p q r s : PlanePoint) : Prop :=
  ∃ x : Space3, OnLine p q x ∧ OnLine r s x

/-- Distinct indexed Elekes--Sharir lines have at most one common point. -/
theorem intersection_unique {p q r s : PlanePoint}
    (hne : (p, q) ≠ (r, s)) {x y : Space3}
    (hx₁ : OnLine p q x) (hx₂ : OnLine r s x)
    (hy₁ : OnLine p q y) (hy₂ : OnLine r s y) : x = y := by
  obtain ⟨t, rfl⟩ := hx₁
  obtain ⟨u, htu⟩ := hx₂
  have htu' : t = u := by
    simpa [linePoint] using congrFun htu (2 : Fin 3)
  subst u
  obtain ⟨v, hyv⟩ := hy₁
  obtain ⟨w, hyw⟩ := hy₂
  have hvw : v = w := by
    have := hyv.symm.trans hyw
    simpa [linePoint] using congrFun this (2 : Fin 3)
  subst w
  have htv : t = v := by
    by_contra htv
    apply hne
    exact Prod.ext
      (eq_of_linePoint_eq_at_two htv htu (hyv.symm.trans hyw)).1
      (eq_of_linePoint_eq_at_two htv htu (hyv.symm.trans hyw)).2
  rw [htv]
  exact hyv.symm

/-- The two segments differ by a common translation.  In the
Elekes--Sharir model this is exactly the parallel-line case. -/
def IsTranslation (a b c d : PlanePoint) : Prop :=
  c 0 - a 0 = d 0 - b 0 ∧ c 1 - a 1 = d 1 - b 1

private theorem exists_parameter_of_equal_squares
    {ux uy vx vy : ℝ}
    (h : ux ^ 2 + uy ^ 2 = vx ^ 2 + vy ^ 2)
    (hne : ux ≠ vx ∨ uy ≠ vy) :
    ∃ t : ℝ,
      t * (uy - vy) = ux + vx ∧
      t * (vx - ux) = uy + vy := by
  let den := (uy - vy) ^ 2 + (vx - ux) ^ 2
  have hdenpos : 0 < den := by
    rcases hne with hux | huy
    · have hs : 0 < (vx - ux) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hux.symm)
      dsimp [den]
      nlinarith [sq_nonneg (uy - vy)]
    · have hs : 0 < (uy - vy) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr huy)
      dsimp [den]
      nlinarith [sq_nonneg (vx - ux)]
  have hparallel :
      (uy - vy) * (uy + vy) = (vx - ux) * (ux + vx) := by
    ring_nf at h ⊢
    linarith
  refine ⟨((ux + vx) * (uy - vy) + (uy + vy) * (vx - ux)) / den, ?_, ?_⟩
  · field_simp [hdenpos.ne']
    dsimp [den]
    calc
      (uy - vy) * ((ux + vx) * (uy - vy) + (uy + vy) * (vx - ux)) =
          (ux + vx) * (uy - vy) ^ 2 +
            ((uy - vy) * (uy + vy)) * (vx - ux) := by ring
      _ = (ux + vx) * (uy - vy) ^ 2 +
            ((vx - ux) * (ux + vx)) * (vx - ux) := by rw [hparallel]
      _ = (ux + vx) * ((uy - vy) ^ 2 + (vx - ux) ^ 2) := by ring
  · field_simp [hdenpos.ne']
    dsimp [den]
    calc
      (vx - ux) * ((ux + vx) * (uy - vy) + (uy + vy) * (vx - ux)) =
          ((vx - ux) * (ux + vx)) * (uy - vy) +
            (uy + vy) * (vx - ux) ^ 2 := by ring
      _ = ((uy - vy) * (uy + vy)) * (uy - vy) +
            (uy + vy) * (vx - ux) ^ 2 := by rw [hparallel]
      _ = (uy + vy) * ((uy - vy) ^ 2 + (vx - ux) ^ 2) := by ring

/-- Incidence of the two lines forces equality of the corresponding planar
segment lengths. -/
theorem sqDist_eq_of_intersects {a b c d : PlanePoint}
    (h : Intersects a c b d) : sqDist a b = sqDist c d := by
  rcases h with ⟨x, ⟨t, hact⟩, ⟨u, hbud⟩⟩
  have hlines : linePoint a c t = linePoint b d u := hact.symm.trans hbud
  have h2 : t = u := by
    simpa [linePoint] using congrFun hlines (2 : Fin 3)
  subst u
  have h0 := congrFun hlines (0 : Fin 3)
  have h1 := congrFun hlines (1 : Fin 3)
  simp [linePoint] at h0 h1
  have heq0 :
      (a 0 - b 0) + (c 0 - d 0) =
        t * ((a 1 - b 1) - (c 1 - d 1)) := by
    linarith
  have heq1 :
      (a 1 - b 1) + (c 1 - d 1) =
        t * ((c 0 - d 0) - (a 0 - b 0)) := by
    linarith
  dsimp [sqDist]
  linear_combination
    ((a 0 - b 0) - (c 0 - d 0)) * heq0 +
      ((a 1 - b 1) - (c 1 - d 1)) * heq1

/-- Equal nonzero segment lengths give either a common translation or an
intersection of the associated Elekes--Sharir lines. -/
theorem intersects_of_sqDist_eq_of_not_translation {a b c d : PlanePoint}
    (hdist : sqDist a b = sqDist c d)
    (htrans : ¬IsTranslation a b c d) : Intersects a c b d := by
  have hne : a 0 - b 0 ≠ c 0 - d 0 ∨ a 1 - b 1 ≠ c 1 - d 1 := by
    by_contra h
    push Not at h
    apply htrans
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  obtain ⟨t, ht0, ht1⟩ := exists_parameter_of_equal_squares hdist hne
  refine ⟨linePoint a c t, ⟨t, rfl⟩, ⟨t, ?_⟩⟩
  funext i
  fin_cases i
  · simp [linePoint]
    linarith
  · simp [linePoint]
    linarith
  · simp [linePoint]

/-- The precise Elekes--Sharir correspondence used in the distance-energy
argument. -/
theorem intersects_iff_sqDist_eq_and_not_translation {a b c d : PlanePoint}
    (htrans : ¬IsTranslation a b c d) :
    Intersects a c b d ↔ sqDist a b = sqDist c d := by
  exact ⟨sqDist_eq_of_intersects, fun h ↦
    intersects_of_sqDist_eq_of_not_translation h htrans⟩

/-- Parallel Elekes--Sharir lines which meet are the same indexed line.  In
the affine chart used here, `IsTranslation` says precisely that their
direction vectors agree. -/
theorem eq_of_intersects_of_translation {a b c d : PlanePoint}
    (hint : Intersects a c b d) (htrans : IsTranslation a b c d) :
    a = b ∧ c = d := by
  rcases hint with ⟨x, ⟨t, hact⟩, ⟨u, hbud⟩⟩
  have hlines : linePoint a c t = linePoint b d u := hact.symm.trans hbud
  have htu : t = u := by
    simpa [linePoint] using congrFun hlines (2 : Fin 3)
  subst u
  have h0 := congrFun hlines (0 : Fin 3)
  have h1 := congrFun hlines (1 : Fin 3)
  simp [linePoint] at h0 h1
  dsimp [IsTranslation] at htrans
  have hdir1 : a 0 - c 0 = b 0 - d 0 := by linarith [htrans.1]
  rw [htrans.2] at h0
  rw [hdir1] at h1
  have ha0 : a 0 = b 0 := by linarith [h0, htrans.1]
  have ha1 : a 1 = b 1 := by linarith [h1, htrans.2]
  have hc0 : c 0 = d 0 := by linarith [htrans.1, ha0]
  have hc1 : c 1 = d 1 := by linarith [htrans.2, ha1]
  constructor
  · apply PiLp.ext
    intro i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · exact ha0
    · exact ha1
  · apply PiLp.ext
    intro i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · exact hc0
    · exact hc1

end Erdos95.ES
