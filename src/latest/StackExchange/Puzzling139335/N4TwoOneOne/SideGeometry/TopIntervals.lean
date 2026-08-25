import StackExchange.Puzzling139335.N4TwoOneOne.BoundaryIntervals
import StackExchange.Puzzling139335.N4TwoOneOne.TopGap

/-!
# The exact top-side contacts

The two singleton pieces have reflected contacts on the top side.  Their
strict separation from its midpoint and Jordan noninterlacing give one
cutoff on each half.  The fourth piece occupies precisely the interval
between these cutoffs.  All cutoffs are actual contacts of the closed pieces.
-/

open Set

namespace Puzzling139335.N4TwoOneOne

theorem rightMap_outgoingEnd (θ u v T : ℝ) :
    rightMap θ u v (outgoingEnd θ u v T) = (!₂[1 - T, 1] : Plane) := by
  have he : eCoord θ (outgoingEnd θ u v T) = u - T := by
    dsimp [eCoord, outgoingEnd, sourceCorner]
    linear_combination (u - T) * (Real.sin_sq_add_cos_sq θ)
  have hf : fCoord θ (outgoingEnd θ u v T) = v := by
    dsimp [fCoord, outgoingEnd, sourceCorner]
    linear_combination v * (Real.sin_sq_add_cos_sq θ)
  ext i
  fin_cases i <;> simp [rightMap, he, hf]

namespace SourceData

variable {d : SquareDissection} {θ u v : ℝ}

private theorem vertical_top_point (x : ℝ) :
    ReflectionSeparation.vertical (!₂[x, 1] : Plane) = (!₂[1 - x, 1] : Plane) := by
  ext i
  fin_cases i <;> simp

/-- Top membership in the right singleton is the reflection of top membership
in the left singleton. -/
theorem top_right_mem_iff_reflected_left (h : SourceData d θ u v) (x : ℝ) :
    (!₂[x, 1] : Plane) ∈ d.piece 1 ↔ (!₂[1 - x, 1] : Plane) ∈ d.piece 2 := by
  constructor
  · intro hp
    rw [← h.singleton_reflection]
    exact ⟨!₂[x, 1], hp, vertical_top_point x⟩
  · intro hp
    obtain ⟨q, hq, hqp⟩ := h.singleton_reflection.symm ▸ hp
    have heq : q = (!₂[x, 1] : Plane) :=
      ReflectionSeparation.vertical.injective (hqp.trans (vertical_top_point x).symm)
    exact heq ▸ hq

private theorem top_left_half_cover (h : SourceData d θ u v)
    (hcfg : Configuration d) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
    (!₂[x, 1] : Plane) ∈ d.piece 2 ∨ (!₂[x, 1] : Plane) ∈ d.piece 3 := by
  obtain ⟨j, hj⟩ := d.exists_piece_mem
    (show (!₂[x, 1] : Plane) ∈ unitSquare by
      change (0 ≤ x ∧ x ≤ 1) ∧ (0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 1)
      exact ⟨⟨hx.1, by linarith [hx.2]⟩, by norm_num⟩)
  fin_cases j
  · have hh := h.height_le_half hj
    norm_num at hh
  · have hh := h.right_top_contact_gt_half hcfg hj rfl
    change (1 / 2 : ℝ) < x at hh
    linarith [hx.2]
  · exact Or.inl hj
  · exact Or.inr hj

private theorem top_right_half_cover (h : SourceData d θ u v)
    (hcfg : Configuration d) {x : ℝ} (hx : x ∈ Icc (1 / 2 : ℝ) 1) :
    (!₂[x, 1] : Plane) ∈ d.piece 3 ∨ (!₂[x, 1] : Plane) ∈ d.piece 1 := by
  obtain ⟨j, hj⟩ := d.exists_piece_mem
    (show (!₂[x, 1] : Plane) ∈ unitSquare by
      change (0 ≤ x ∧ x ≤ 1) ∧ (0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 1)
      exact ⟨⟨by linarith [hx.1], hx.2⟩, by norm_num⟩)
  fin_cases j
  · have hh := h.height_le_half hj
    norm_num at hh
  · exact Or.inr hj
  · have hh := h.left_top_contact_lt_half hcfg hj rfl
    change x < (1 / 2 : ℝ) at hh
    linarith [hx.1]
  · exact Or.inl hj

private theorem exists_top_left_half_cutoff (h : SourceData d θ u v)
    (hcfg : Configuration d) :
    ∃ T ∈ Ioo (0 : ℝ) (1 / 2), ∀ x ∈ Icc (0 : ℝ) (1 / 2),
      ((!₂[x, 1] : Plane) ∈ d.piece 2 ↔ x ≤ T) ∧
      ((!₂[x, 1] : Plane) ∈ d.piece 3 ↔ T ≤ x) := by
  have hcover : ∀ t ∈ Icc (0 : ℝ) 1,
      BoundaryIntervals.sidePoint 2 (0 + (1 / 2 - 0) * t) ∈ d.piece 2 ∨
      BoundaryIntervals.sidePoint 2 (0 + (1 / 2 - 0) * t) ∈ d.piece 3 := by
    intro t ht
    exact h.top_left_half_cover hcfg ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨l, hl, hparts⟩ := BoundaryIntervals.exists_subside_cutoff 2
    (d.jordan 2) (d.jordan 3) (d.piece_subset 2) (d.piece_subset 3)
    (d.disjoint_interiors (by decide : (2 : Fin 4) ≠ 3))
    (a := 0) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by simpa [BoundaryIntervals.sidePoint, corner, Fin.ext_iff] using hcfg.top_left)
    (by simpa [BoundaryIntervals.sidePoint, corner, Fin.ext_iff] using hcfg.cornerless 3)
    (h.top_midpoint_unique hcfg 2 (by decide)) (h.top_midpoint_mem hcfg) hcover
  refine ⟨l / 2, ⟨by linarith [hl.1], by linarith [hl.2]⟩, ?_⟩
  intro x hx
  have hparts' := hparts (2 * x) ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have harg : (0 : ℝ) + (1 / 2 - 0) * (2 * x) = x := by ring
  rw [harg] at hparts'
  change ((!₂[x, 1] : Plane) ∈ d.piece 2 ↔ 2 * x ≤ l) ∧
    ((!₂[x, 1] : Plane) ∈ d.piece 3 ↔ l ≤ 2 * x) at hparts'
  exact ⟨hparts'.1.trans (by constructor <;> intro hh <;> linarith),
    hparts'.2.trans (by constructor <;> intro hh <;> linarith)⟩

private theorem exists_top_right_half_cutoff (h : SourceData d θ u v)
    (hcfg : Configuration d) :
    ∃ R ∈ Ioo (1 / 2 : ℝ) 1, ∀ x ∈ Icc (1 / 2 : ℝ) 1,
      ((!₂[x, 1] : Plane) ∈ d.piece 3 ↔ x ≤ R) ∧
      ((!₂[x, 1] : Plane) ∈ d.piece 1 ↔ R ≤ x) := by
  have hcover : ∀ t ∈ Icc (0 : ℝ) 1,
      BoundaryIntervals.sidePoint 2 (1 / 2 + (1 - 1 / 2) * t) ∈ d.piece 3 ∨
      BoundaryIntervals.sidePoint 2 (1 / 2 + (1 - 1 / 2) * t) ∈ d.piece 1 := by
    intro t ht
    exact h.top_right_half_cover hcfg ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨l, hl, hparts⟩ := BoundaryIntervals.exists_subside_cutoff 2
    (d.jordan 3) (d.jordan 1) (d.piece_subset 3) (d.piece_subset 1)
    (d.disjoint_interiors (by decide : (3 : Fin 4) ≠ 1))
    (a := 1 / 2) (b := 1) (by norm_num) (by norm_num) (by norm_num)
    (h.top_midpoint_mem hcfg) (h.top_midpoint_unique hcfg 1 (by decide))
    (by simpa [BoundaryIntervals.sidePoint, corner, Fin.ext_iff] using hcfg.cornerless 2)
    (by simpa [BoundaryIntervals.sidePoint, corner, Fin.ext_iff] using hcfg.top_right) hcover
  refine ⟨1 / 2 + l / 2, ⟨by linarith [hl.1], by linarith [hl.2]⟩, ?_⟩
  intro x hx
  have hparts' := hparts (2 * x - 1) ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have harg : (1 / 2 : ℝ) + (1 - 1 / 2) * (2 * x - 1) = x := by ring
  rw [harg] at hparts'
  change ((!₂[x, 1] : Plane) ∈ d.piece 3 ↔ 2 * x - 1 ≤ l) ∧
    ((!₂[x, 1] : Plane) ∈ d.piece 1 ↔ l ≤ 2 * x - 1) at hparts'
  exact ⟨hparts'.1.trans (by constructor <;> intro hh <;> linarith),
    hparts'.2.trans (by constructor <;> intro hh <;> linarith)⟩

/-- The three exact contact intervals on the top side.  No hypothesis about
the fourth piece's contacts on either vertical side is used. -/
theorem exists_top_contact_intervals (h : SourceData d θ u v)
    (hcfg : Configuration d) :
    ∃ T ∈ Ioo (0 : ℝ) (1 / 2), ∀ x ∈ Icc (0 : ℝ) 1,
      ((!₂[x, 1] : Plane) ∈ d.piece 2 ↔ x ≤ T) ∧
      ((!₂[x, 1] : Plane) ∈ d.piece 1 ↔ 1 - T ≤ x) ∧
      ((!₂[x, 1] : Plane) ∈ d.piece 3 ↔ T ≤ x ∧ x ≤ 1 - T) := by
  obtain ⟨T, hT, hleft⟩ := h.exists_top_left_half_cutoff hcfg
  have hQL : ∀ x ∈ Icc (0 : ℝ) 1,
      (!₂[x, 1] : Plane) ∈ d.piece 2 ↔ x ≤ T := by
    intro x hx
    constructor
    · intro hp
      have hxhalf := h.left_top_contact_lt_half hcfg hp rfl
      exact (hleft x ⟨hx.1, hxhalf.le⟩).1.mp hp
    · intro hxT
      exact (hleft x ⟨hx.1, hxT.trans hT.2.le⟩).1.mpr hxT
  have hQR : ∀ x ∈ Icc (0 : ℝ) 1,
      (!₂[x, 1] : Plane) ∈ d.piece 1 ↔ 1 - T ≤ x := by
    intro x hx
    refine (h.top_right_mem_iff_reflected_left x).trans ?_
    exact (hQL (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩).trans
      (by constructor <;> intro hh <;> linarith)
  obtain ⟨R, hR, hright⟩ := h.exists_top_right_half_cutoff hcfg
  have hRunit : R ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hR.1], hR.2.le⟩
  have hRhalf : R ∈ Icc (1 / 2 : ℝ) 1 := ⟨hR.1.le, hR.2.le⟩
  have hTunit : 1 - T ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [hT.2], by linarith [hT.1]⟩
  have hThalf : 1 - T ∈ Icc (1 / 2 : ℝ) 1 :=
    ⟨by linarith [hT.2], by linarith [hT.1]⟩
  have hReq : R = 1 - T := le_antisymm
    ((hright (1 - T) hThalf).2.mp ((hQR (1 - T) hTunit).mpr le_rfl))
    ((hQR R hRunit).mp ((hright R hRhalf).2.mpr le_rfl))
  refine ⟨T, hT, ?_⟩
  intro x hx
  refine ⟨hQL x hx, hQR x hx, ?_⟩
  by_cases hxhalf : x ≤ 1 / 2
  · have hpart := (hleft x ⟨hx.1, hxhalf⟩).2
    constructor
    · intro hp
      exact ⟨hpart.mp hp, by linarith [hT.2]⟩
    · intro hp
      exact hpart.mpr hp.1
  · have hpart := (hright x ⟨le_of_lt (lt_of_not_ge hxhalf), hx.2⟩).1
    rw [hReq] at hpart
    constructor
    · intro hp
      exact ⟨by linarith [hT.2], hpart.mp hp⟩
    · intro hp
      exact hpart.mpr hp.2

/-- A right top contact pulls back to the actual outgoing source endpoint. -/
theorem outgoingEnd_mem_of_top_contact (h : SourceData d θ u v) {T : ℝ}
    (hp : (!₂[1 - T, 1] : Plane) ∈ d.piece 1) :
    outgoingEnd θ u v T ∈ d.piece 0 := by
  obtain ⟨p, hp, hpe⟩ := h.right_image.symm ▸ hp
  have heq : p = outgoingEnd θ u v T :=
    rightMap_injective θ u v (hpe.trans (rightMap_outgoingEnd θ u v T).symm)
  exact heq ▸ hp

/-- The contact intervals together with both actual fourth-piece endpoints
and the corresponding outgoing source endpoint. -/
theorem exists_top_geometry (h : SourceData d θ u v) (hcfg : Configuration d) :
    ∃ T ∈ Ioo (0 : ℝ) (1 / 2),
      (∀ x ∈ Icc (0 : ℝ) 1,
        ((!₂[x, 1] : Plane) ∈ d.piece 2 ↔ x ≤ T) ∧
        ((!₂[x, 1] : Plane) ∈ d.piece 1 ↔ 1 - T ≤ x) ∧
        ((!₂[x, 1] : Plane) ∈ d.piece 3 ↔ T ≤ x ∧ x ≤ 1 - T)) ∧
      (!₂[T, 1] : Plane) ∈ d.piece 3 ∧
      (!₂[1 - T, 1] : Plane) ∈ d.piece 3 ∧
      outgoingEnd θ u v T ∈ d.piece 0 := by
  obtain ⟨T, hT, hparts⟩ := h.exists_top_contact_intervals hcfg
  have hTunit : T ∈ Icc (0 : ℝ) 1 := ⟨hT.1.le, by linarith [hT.2]⟩
  have hTunit' : 1 - T ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [hT.2], by linarith [hT.1]⟩
  refine ⟨T, hT, hparts, ?_, ?_, ?_⟩
  · exact (hparts T hTunit).2.2.mpr ⟨le_rfl, by linarith [hT.2]⟩
  · exact (hparts (1 - T) hTunit').2.2.mpr ⟨by linarith [hT.2], le_rfl⟩
  · exact h.outgoingEnd_mem_of_top_contact
      ((hparts (1 - T) hTunit').2.1.mpr le_rfl)

end SourceData

end Puzzling139335.N4TwoOneOne
