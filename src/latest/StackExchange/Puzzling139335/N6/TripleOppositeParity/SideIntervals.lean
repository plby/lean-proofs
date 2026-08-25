import StackExchange.Puzzling139335.N4OuterPair.SideIntervals
import StackExchange.Puzzling139335.ReflectionSeparation.Maps
import StackExchange.Puzzling139335.N7Geometry.TripleCornerBounds

/-!
# Actual side intervals in the opposite-parity triple-corner case

The right side is covered by the lower outer piece and the remaining piece.
The lower piece lies below a height strictly less than one, while the
remaining piece contains the top-right corner.  Jordan crosscut separation
therefore makes the lower contacts an initial interval.  Closedness supplies
the shared endpoint of the terminal interval of the remaining piece.

Reflection in the diagonal gives the same endpoint on the top side.  These
are statements about the pieces themselves, not about their convex hulls.
-/

open Set Schoenflies

namespace Puzzling139335.N6.TripleOppositeParity

noncomputable section

/-- Under the two-piece side cover, a right-side contact of the lower piece
forces every lower right-side point into that piece. -/
theorem right_contact_downward {P D : Set Plane} {h y : ℝ}
    (hP : IsJordanRegion P) (hD : IsJordanRegion D)
    (hPS : P ⊆ unitSquare) (hDS : D ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior D))
    (hbase : Schoenflies.Plane.mk 1 0 ∈ P)
    (htop : Schoenflies.Plane.mk 1 y ∈ P)
    (hheight : ∀ p ∈ P, p 1 ≤ h) (hh : h < 1)
    (htr : Schoenflies.Plane.mk 1 1 ∈ D)
    (hcover : ∀ t ∈ Icc (0 : ℝ) 1,
      Schoenflies.Plane.mk 1 t ∈ P ∨ Schoenflies.Plane.mk 1 t ∈ D) :
    ∀ t ∈ Icc (0 : ℝ) y, Schoenflies.Plane.mk 1 t ∈ P := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with ht0 | ht0
  · simpa only [← ht0] using hbase
  rcases eq_or_lt_of_le ht.2 with hty | hty
  · simpa only [hty] using htop
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans (hPS htop).2.2⟩
  rcases hcover t htI with htP | htD
  · exact htP
  · have hcap := RectangularHull.vertical_contact_height_bound
      hP hD hPS hDS hdis (Or.inr rfl) hbase htop hheight ht0 hty htD
    have hbad : (1 : ℝ) ≤ h := hcap _ htr
    exact False.elim ((not_le_of_gt hh) hbad)

/-- Compactness turns the downward-closed actual contacts into an exact
closed interval with a terminal height at most the source height bound. -/
theorem right_contact_interval {P D : Set Plane} {h : ℝ}
    (hP : IsJordanRegion P) (hD : IsJordanRegion D)
    (hPS : P ⊆ unitSquare) (hDS : D ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior D))
    (hbase : Schoenflies.Plane.mk 1 0 ∈ P)
    (hheight : ∀ p ∈ P, p 1 ≤ h) (hh : h < 1)
    (htr : Schoenflies.Plane.mk 1 1 ∈ D)
    (hcover : ∀ t ∈ Icc (0 : ℝ) 1,
      Schoenflies.Plane.mk 1 t ∈ P ∨ Schoenflies.Plane.mk 1 t ∈ D) :
    ∃ r ∈ Icc (0 : ℝ) h,
      ∀ t : ℝ, Schoenflies.Plane.mk 1 t ∈ P ↔ t ∈ Icc (0 : ℝ) r := by
  let K : Set Plane := P ∩ {p : Plane | p 0 = 1}
  have hKcompact : IsCompact K := hP.isCompact.inter_right
    (isClosed_eq (Schoenflies.Plane.continuous_coord 0) continuous_const)
  have hKnonempty : K.Nonempty := ⟨Schoenflies.Plane.mk 1 0, hbase, rfl⟩
  obtain ⟨p, hp, hmax⟩ := hKcompact.exists_isMaxOn hKnonempty
    (Schoenflies.Plane.continuous_coord 1).continuousOn
  have heq : p = Schoenflies.Plane.mk 1 (p 1) := by
    ext i
    fin_cases i
    · exact hp.2
    · rfl
  have htop : Schoenflies.Plane.mk 1 (p 1) ∈ P := heq ▸ hp.1
  refine ⟨p 1, ⟨(hPS hp.1).2.1, hheight _ hp.1⟩, ?_⟩
  intro t
  constructor
  · intro ht
    exact ⟨(hPS ht).2.1, (isMaxOn_iff.mp hmax) _ ⟨ht, rfl⟩⟩
  · exact right_contact_downward hP hD hPS hDS hdis hbase htop hheight hh htr hcover t

/-- A closed second owner contains the full terminal interval, including
the cutoff, once the first owner's contacts are known exactly. -/
theorem terminal_interval_of_initial_cover {X : Type*} [TopologicalSpace X]
    {P D : Set X} {γ : ℝ → X} {r : ℝ}
    (hγ : Continuous γ) (hD : IsClosed D) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hP : ∀ t : ℝ, γ t ∈ P ↔ t ∈ Icc (0 : ℝ) r)
    (hcover : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ P ∨ γ t ∈ D) :
    ∀ t ∈ Icc r 1, γ t ∈ D := by
  have htail : Ioc r 1 ⊆ γ ⁻¹' D := by
    intro t ht
    rcases hcover t ⟨hr0.trans ht.1.le, ht.2⟩ with htP | htD
    · exact False.elim ((not_le_of_gt ht.1) ((hP t).mp htP).2)
    · exact htD
  have hcl := closure_minimal htail (hD.preimage hγ)
  rw [closure_Ioc hr1.ne] at hcl
  exact fun _ ht => hcl ht

/-- Diagonal reflection transports actual right-side membership to actual
top-side membership. -/
theorem diagonal_top_mem_iff {P : Set Plane} (t : ℝ) :
    Schoenflies.Plane.mk t 1 ∈ ReflectionSeparation.diagonal '' P ↔
      Schoenflies.Plane.mk 1 t ∈ P := by
  constructor
  · rintro ⟨p, hp, heq⟩
    have hcoord : p = Schoenflies.Plane.mk 1 t := by
      ext i
      fin_cases i
      · exact congrArg (fun q : Plane => q 1) heq
      · exact congrArg (fun q : Plane => q 0) heq
    exact hcoord ▸ hp
  · intro ht
    refine ⟨_, ht, ?_⟩
    ext i
    fin_cases i <;> rfl

/-- The outer reflected pair has equal initial contact lengths, and the
remaining Jordan region contains both terminal square-side intervals. -/
theorem opposite_pair_side_intervals {P D : Set Plane} {h : ℝ}
    (hP : IsJordanRegion P) (hD : IsJordanRegion D)
    (hPS : P ⊆ unitSquare) (hDS : D ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior D))
    (hbase : Schoenflies.Plane.mk 1 0 ∈ P)
    (hheight : ∀ p ∈ P, p 1 ≤ h) (hh : h < 1)
    (htr : Schoenflies.Plane.mk 1 1 ∈ D)
    (hright : ∀ t ∈ Icc (0 : ℝ) 1,
      Schoenflies.Plane.mk 1 t ∈ P ∨ Schoenflies.Plane.mk 1 t ∈ D)
    (htop : ∀ t ∈ Icc (0 : ℝ) 1,
      Schoenflies.Plane.mk t 1 ∈ ReflectionSeparation.diagonal '' P ∨
      Schoenflies.Plane.mk t 1 ∈ D) :
    ∃ r ∈ Icc (0 : ℝ) h,
      (∀ t : ℝ, Schoenflies.Plane.mk 1 t ∈ P ↔ t ∈ Icc (0 : ℝ) r) ∧
      (∀ t : ℝ, Schoenflies.Plane.mk t 1 ∈ ReflectionSeparation.diagonal '' P ↔
        t ∈ Icc (0 : ℝ) r) ∧
      (∀ t ∈ Icc r 1, Schoenflies.Plane.mk 1 t ∈ D) ∧
      (∀ t ∈ Icc r 1, Schoenflies.Plane.mk t 1 ∈ D) := by
  obtain ⟨r, hr, hPr⟩ := right_contact_interval hP hD hPS hDS hdis
    hbase hheight hh htr hright
  have hQr : ∀ t : ℝ,
      Schoenflies.Plane.mk t 1 ∈ ReflectionSeparation.diagonal '' P ↔
        t ∈ Icc (0 : ℝ) r := by
    intro t
    rw [diagonal_top_mem_iff, hPr]
  refine ⟨r, hr, hPr, hQr, ?_, ?_⟩
  · exact terminal_interval_of_initial_cover (by fun_prop) hD.isClosed
      hr.1 (hr.2.trans_lt hh) hPr hright
  · exact terminal_interval_of_initial_cover (by fun_prop) hD.isClosed
      hr.1 (hr.2.trans_lt hh) hQr htop

/-- The triangular source bound and the actual four-piece cover provide
the two-owner side covers.  The only remaining geometric input is that the
middle rotated piece misses the top side; missing the right side is already
a consequence of the exact triangular bound. -/
theorem side_intervals_of_triangle_cover {P D : Set Plane}
    (hP : IsJordanRegion P) (hD : IsJordanRegion D)
    (htriangle : P ⊆ TripleCornerBounds.triangle) (hDS : D ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior D))
    (hbase : Schoenflies.Plane.mk 1 0 ∈ P)
    (htr : Schoenflies.Plane.mk 1 1 ∈ D)
    (hcover : unitSquare ⊆
      P ∪ TripleCornerBounds.R30 '' P ∪ ReflectionSeparation.diagonal '' P ∪ D)
    (hmiddle : ∀ t ∈ Icc (0 : ℝ) 1,
      Schoenflies.Plane.mk t 1 ∉ TripleCornerBounds.R30 '' P) :
    ∃ r ∈ Icc (0 : ℝ) (1 / Real.sqrt 3),
      (∀ t : ℝ, Schoenflies.Plane.mk 1 t ∈ P ↔ t ∈ Icc (0 : ℝ) r) ∧
      (∀ t : ℝ, Schoenflies.Plane.mk t 1 ∈ ReflectionSeparation.diagonal '' P ↔
        t ∈ Icc (0 : ℝ) r) ∧
      (∀ t ∈ Icc r 1, Schoenflies.Plane.mk 1 t ∈ D) ∧
      (∀ t ∈ Icc r 1, Schoenflies.Plane.mk t 1 ∈ D) := by
  have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : 1 < Real.sqrt (3 : ℝ) := by
    nlinarith only [hs, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hh : 1 / Real.sqrt (3 : ℝ) < 1 := by
    apply (div_lt_iff₀ hs).mpr
    simpa only [one_mul] using hs1
  have hheight : ∀ p ∈ P, p 1 ≤ 1 / Real.sqrt 3 := by
    intro p hp
    apply (le_div_iff₀ hs).mpr
    simpa only [mul_comm] using (htriangle hp).2.1.trans (htriangle hp).2.2
  have hPS : P ⊆ unitSquare := by
    intro p hp
    have hpT := htriangle hp
    refine ⟨⟨?_, hpT.2.2⟩, hpT.1, (hheight p hp).trans hh.le⟩
    exact (mul_nonneg hs.le hpT.1).trans hpT.2.1
  apply opposite_pair_side_intervals hP hD hPS hDS hdis hbase hheight hh htr
  · intro t ht
    have hpoint : Schoenflies.Plane.mk 1 t ∈ unitSquare :=
      ⟨⟨by norm_num, by norm_num⟩, ht⟩
    rcases hcover hpoint with ((htP | htM) | htQ) | htD
    · exact Or.inl htP
    · exact False.elim
        (TripleCornerBounds.not_mem_rotated_image_of_x_eq_one htriangle rfl htM)
    · rcases htQ with ⟨p, hp, heq⟩
      have hp1 : p 1 = 1 := congrArg (fun q : Plane => q 0) heq
      exact False.elim ((ne_of_lt ((hheight p hp).trans_lt hh)) hp1)
    · exact Or.inr htD
  · intro t ht
    have hpoint : Schoenflies.Plane.mk t 1 ∈ unitSquare :=
      ⟨ht, ⟨by norm_num, by norm_num⟩⟩
    rcases hcover hpoint with ((htP | htM) | htQ) | htD
    · have hbad : (1 : ℝ) ≤ 1 / Real.sqrt 3 := hheight _ htP
      exact False.elim ((not_le_of_gt hh) hbad)
    · exact False.elim (hmiddle t ht htM)
    · exact Or.inl htQ
    · exact Or.inr htD

/-- The terminal interval on the right side is an actual segment of the
remaining region. -/
theorem right_segment_of_terminal_interval {D : Set Plane} {r : ℝ}
    (hr : r ≤ 1)
    (hD : ∀ t ∈ Icc r 1, Schoenflies.Plane.mk 1 t ∈ D) :
    segment ℝ (Schoenflies.Plane.mk 1 r) (Schoenflies.Plane.mk 1 1) ⊆ D := by
  intro p hp
  rw [Schoenflies.mem_segment_vert, segment_eq_Icc hr] at hp
  have heq : p = Schoenflies.Plane.mk 1 (p 1) := by
    ext i
    fin_cases i
    · exact hp.1
    · rfl
  exact heq.symm ▸ hD _ hp.2

/-- The terminal interval on the top side is an actual segment of the
remaining region. -/
theorem top_segment_of_terminal_interval {D : Set Plane} {r : ℝ}
    (hr : r ≤ 1)
    (hD : ∀ t ∈ Icc r 1, Schoenflies.Plane.mk t 1 ∈ D) :
    segment ℝ (Schoenflies.Plane.mk r 1) (Schoenflies.Plane.mk 1 1) ⊆ D := by
  intro p hp
  rw [Schoenflies.mem_segment_horiz, segment_eq_Icc hr] at hp
  have heq : p = Schoenflies.Plane.mk (p 0) 1 := by
    ext i
    fin_cases i
    · rfl
    · exact hp.1
  exact heq.symm ▸ hD _ hp.2

end

end Puzzling139335.N6.TripleOppositeParity
