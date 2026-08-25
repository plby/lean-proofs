import StackExchange.Puzzling139335.RectangularHull.HeightBarrier
import StackExchange.Puzzling139335.N4OuterPair.Midline

/-!
# Side contacts of the lower outer piece are initial intervals

An interior crosscut joining two points on a vertical square side traps any
other piece touching strictly between them below the lower piece's height
bound.  If every other piece rises above that bound, the whole side segment
belongs to the lower piece.
-/

open Set Schoenflies

namespace Puzzling139335.RectangularHull

private theorem vertical_side_mem_frontier {x y : ℝ}
    (hx : x = 0 ∨ x = 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Schoenflies.Plane.mk x y ∈ frontier unitSquare := by
  rw [unitSquare_eq_closedSquare]
  apply Schoenflies.Plane.mem_frontier_closedSquare_of_fst
  · rcases hx with rfl | rfl <;> norm_num [squareCenter]
  · change |y - (1 / 2 : ℝ)| ≤ 1 / 2
    rw [abs_le]
    constructor <;> linarith

/-- A second Jordan region touching strictly between two contacts of `P`
with a vertical square side inherits the upper height bound of `P`. -/
theorem vertical_contact_height_bound {P Q : Set Plane} {x y h r : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (hx : x = 0 ∨ x = 1)
    (hbase : Schoenflies.Plane.mk x 0 ∈ P)
    (htop : Schoenflies.Plane.mk x y ∈ P)
    (hheight : ∀ p ∈ P, p 1 ≤ h)
    (hr0 : 0 < r) (hry : r < y)
    (hrQ : Schoenflies.Plane.mk x r ∈ Q) :
    ∀ p ∈ Q, p 1 ≤ h := by
  have hy0 : 0 < y := hr0.trans hry
  have hy1 : y ≤ 1 := (hPS htop).2.2
  have hbaseS : Schoenflies.Plane.mk x 0 ∈ frontier unitSquare :=
    vertical_side_mem_frontier hx (by norm_num) (by norm_num)
  have htopS : Schoenflies.Plane.mk x y ∈ frontier unitSquare :=
    vertical_side_mem_frontier hx hy0.le hy1
  have hne : Schoenflies.Plane.mk x 0 ≠ Schoenflies.Plane.mk x y := by
    intro heq
    exact (ne_of_lt hy0) (congrArg (fun p : Plane => p 1) heq)
  obtain ⟨X, hXarc, hXP, hXi⟩ := hP.exists_arc_between_frontier
    (mem_frontier_of_subset hPS hbase hbaseS)
    (mem_frontier_of_subset hPS htop htopS) hne
  have hX : JordanCrosscut (frontier unitSquare) X
      (Schoenflies.Plane.mk x 0) (Schoenflies.Plane.mk x y) := by
    refine ⟨isJordanCurve_frontier_unitSquare, hXarc, hbaseS, htopS, ?_⟩
    rw [inside_frontier_unitSquare]
    exact hXi.trans (interior_mono hPS)
  let A : Set Plane := segment ℝ
    (Schoenflies.Plane.mk x 0) (Schoenflies.Plane.mk x y)
  have hA : IsArcBetween A
      (Schoenflies.Plane.mk x 0) (Schoenflies.Plane.mk x y) :=
    isArcBetween_segment hne
  have hAS : A ⊆ frontier unitSquare := by
    intro p hp
    rw [Schoenflies.mem_segment_vert, segment_eq_Icc hy0.le] at hp
    have heq : p = Schoenflies.Plane.mk x (p 1) := by
      ext i
      fin_cases i
      · exact hp.1
      · rfl
    rw [heq]
    exact vertical_side_mem_frontier hx hp.2.1 (hp.2.2.trans hy1)
  obtain ⟨B, hcut⟩ :=
    isJordanCurve_frontier_unitSquare.exists_cutPair_of_subset_arc hA hAS
  have hrA : Schoenflies.Plane.mk x r ∈ A := by
    rw [Schoenflies.mem_segment_vert, segment_eq_Icc hy0.le]
    exact ⟨rfl, hr0.le, hry.le⟩
  have hrB : Schoenflies.Plane.mk x r ∉ B := by
    intro hrB
    have hends := hcut.inter_eq ▸
      (show Schoenflies.Plane.mk x r ∈ A ∩ B from ⟨hrA, hrB⟩)
    rcases mem_insert_iff.mp hends with hleft | hright
    · exact (ne_of_gt hr0) (congrArg (fun p : Plane => p 1) hleft)
    · exact (ne_of_lt hry)
        (congrArg (fun p : Plane => p 1) (mem_singleton_iff.mp hright))
  have hQX : Disjoint (interior Q) X :=
    (hP.disjoint_interior_left hdis.symm).mono_right hXP
  have hQi : interior Q ⊆ inside (frontier unitSquare) := by
    rw [inside_frontier_unitSquare]
    exact interior_mono hQS
  have hside : interior Q ⊆ inside (A ∪ X) :=
    subset_crosscut_side_of_boundary_contact hX hcut
      hQ.isConnected_interior.isPreconnected hQi hQX
      (hQ.closure_interior.symm ▸ hrQ) hrA hrB
  have hcap : ∀ p ∈ A ∪ X, p 1 ≤ h := by
    intro p hp
    rcases hp with hp | hp
    · rw [Schoenflies.mem_segment_vert, segment_eq_Icc hy0.le] at hp
      exact hp.2.2.trans (hheight _ htop)
    · exact hheight p (hXP hp)
  have hQcap : Q ⊆ closure (inside (A ∪ X)) := by
    rw [← hQ.closure_interior]
    exact closure_mono hside
  intro p hp
  exact closure_inside_coord_one_le hcap (hQcap hp)

/-- If every other dissection piece rises above the height bound, a contact
on either vertical side forces all lower contacts on that side. -/
theorem squareDissection_vertical_side_forced (d : SquareDissection)
    {i : Fin 4} {x y h : ℝ} (hx : x = 0 ∨ x = 1)
    (hbase : Schoenflies.Plane.mk x 0 ∈ d.piece i)
    (htop : Schoenflies.Plane.mk x y ∈ d.piece i)
    (hheight : ∀ p ∈ d.piece i, p 1 ≤ h)
    (habove : ∀ j, j ≠ i → ∃ p ∈ interior (d.piece j), h < p 1) :
    ∀ r ∈ Icc (0 : ℝ) y, Schoenflies.Plane.mk x r ∈ d.piece i := by
  intro r hr
  rcases eq_or_lt_of_le hr.1 with hr0 | hr0
  · simpa only [← hr0] using hbase
  rcases eq_or_lt_of_le hr.2 with hry | hry
  · simpa only [hry] using htop
  have hrS : Schoenflies.Plane.mk x r ∈ unitSquare := by
    refine ⟨?_, hr.1, hr.2.trans (d.piece_subset i htop).2.2⟩
    rcases hx with rfl | rfl <;> norm_num
  obtain ⟨j, hj⟩ := d.exists_piece_mem hrS
  by_cases hji : j = i
  · simpa only [hji] using hj
  obtain ⟨p, hp, hph⟩ := habove j hji
  have hcap := vertical_contact_height_bound (d.jordan i) (d.jordan j)
    (d.piece_subset i) (d.piece_subset j)
    (d.disjoint_interiors (fun hij => hji hij.symm)) hx hbase htop hheight hr0 hry hj
  exact False.elim ((not_le_of_gt hph) (hcap p (interior_subset hp)))

end Puzzling139335.RectangularHull

namespace Puzzling139335.N4OuterPair

namespace Configuration

variable {d : SquareDissection}

/-- A side contact of the lower outer piece contains every lower point of
the same vertical square side. -/
theorem side_downward (h : Configuration d) (hc : d.HasProtectedCenter)
    {x y : ℝ} (hx : x = 0 ∨ x = 1)
    (htop : Schoenflies.Plane.mk x y ∈ d.piece 0) :
    ∀ r ∈ Icc (0 : ℝ) y, Schoenflies.Plane.mk x r ∈ d.piece 0 := by
  apply RectangularHull.squareDissection_vertical_side_forced d hx _ htop
    (fun _ hp => (h.outer_halves.1 hp).2.2)
    (fun _ hi => h.other_above hc hi)
  rcases hx with rfl | rfl
  · exact h.bottom_left_mk
  · exact h.bottom_right_mk

/-- Left-side contacts form an initial interval. -/
theorem left_side_downward (h : Configuration d) (hc : d.HasProtectedCenter)
    {y : ℝ} (htop : Schoenflies.Plane.mk 0 y ∈ d.piece 0) :
    ∀ r ∈ Icc (0 : ℝ) y, Schoenflies.Plane.mk 0 r ∈ d.piece 0 :=
  h.side_downward hc (Or.inl rfl) htop

/-- Right-side contacts form an initial interval. -/
theorem right_side_downward (h : Configuration d) (hc : d.HasProtectedCenter)
    {y : ℝ} (htop : Schoenflies.Plane.mk 1 y ∈ d.piece 0) :
    ∀ r ∈ Icc (0 : ℝ) y, Schoenflies.Plane.mk 1 r ∈ d.piece 0 :=
  h.side_downward hc (Or.inr rfl) htop

/-- The actual segment below a vertical-side contact belongs to the lower
outer piece; no convexity of that piece is assumed. -/
theorem side_segment (h : Configuration d) (hc : d.HasProtectedCenter)
    {x y : ℝ} (hx : x = 0 ∨ x = 1)
    (htop : Schoenflies.Plane.mk x y ∈ d.piece 0) :
    segment ℝ (Schoenflies.Plane.mk x 0) (Schoenflies.Plane.mk x y) ⊆ d.piece 0 := by
  have hy0 : 0 ≤ y := (d.piece_subset 0 htop).2.1
  intro p hp
  rw [Schoenflies.mem_segment_vert, segment_eq_Icc hy0] at hp
  have heq : p = Schoenflies.Plane.mk x (p 1) := by
    ext i
    fin_cases i
    · exact hp.1
    · rfl
  rw [heq]
  exact h.side_downward hc hx htop (p 1) hp.2

/-- Compactness supplies a terminal height for each actual vertical-side
contact interval of the lower outer piece. -/
theorem side_contact_interval (h : Configuration d) (hc : d.HasProtectedCenter)
    {x : ℝ} (hx : x = 0 ∨ x = 1) :
    ∃ b ∈ Icc (0 : ℝ) (1 / 2),
      ∀ y : ℝ, Schoenflies.Plane.mk x y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) b := by
  have hbase : Schoenflies.Plane.mk x 0 ∈ d.piece 0 := by
    rcases hx with rfl | rfl
    · exact h.bottom_left_mk
    · exact h.bottom_right_mk
  let K : Set Plane := d.piece 0 ∩ {p : Plane | p 0 = x}
  have hKcompact : IsCompact K :=
    (d.jordan 0).isCompact.inter_right
      (isClosed_eq (Schoenflies.Plane.continuous_coord 0) continuous_const)
  have hKnonempty : K.Nonempty := ⟨Schoenflies.Plane.mk x 0, hbase, rfl⟩
  obtain ⟨p, hp, hmax⟩ := hKcompact.exists_isMaxOn hKnonempty
    (Schoenflies.Plane.continuous_coord 1).continuousOn
  have heq : p = Schoenflies.Plane.mk x (p 1) := by
    ext i
    fin_cases i
    · exact hp.2
    · rfl
  have htop : Schoenflies.Plane.mk x (p 1) ∈ d.piece 0 := heq ▸ hp.1
  refine ⟨p 1, (h.outer_halves.1 hp.1).2, ?_⟩
  intro y
  constructor
  · intro hy
    exact ⟨(d.piece_subset 0 hy).2.1, (isMaxOn_iff.mp hmax) _ ⟨hy, rfl⟩⟩
  · intro hy
    exact h.side_downward hc hx htop y hy

end Configuration

end Puzzling139335.N4OuterPair
