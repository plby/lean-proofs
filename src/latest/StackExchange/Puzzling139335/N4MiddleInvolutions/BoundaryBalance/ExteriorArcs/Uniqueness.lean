import StackExchange.Puzzling139335.N4OuterPair.SideGaps
import StackExchange.Puzzling139335.InterfacePairing

/-!
# Unique outer-piece ownership away from terminal side contacts

The side height barrier rules out any other piece at a strict lower contact.
Reflection gives the upper statement.  These are statements about actual
closed pieces, and hence exclude extended triple junctions at such points.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.BoundaryBalance

variable {d : SquareDissection}

/-- No other actual piece touches strictly inside an initial vertical
contact interval of the lower outer piece. -/
theorem other_not_mem_strict_lower_side
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    {x c y : ℝ} (hx : x = 0 ∨ x = 1)
    (hcontact : ∀ z : ℝ,
      Schoenflies.Plane.mk x z ∈ d.piece 0 ↔ z ∈ Icc (0 : ℝ) c)
    (hy : y ∈ Ioo (0 : ℝ) c) {i : Fin 4} (hi : i ≠ 0) :
    Schoenflies.Plane.mk x y ∉ d.piece i := by
  intro hmem
  have hc0 : 0 ≤ c := (hy.1.trans hy.2).le
  have hbase : Schoenflies.Plane.mk x 0 ∈ d.piece 0 :=
    (hcontact 0).mpr ⟨le_rfl, hc0⟩
  have htop : Schoenflies.Plane.mk x c ∈ d.piece 0 :=
    (hcontact c).mpr ⟨hc0, le_rfl⟩
  have hcap := RectangularHull.vertical_contact_height_bound
    (d.jordan 0) (d.jordan i) (d.piece_subset 0) (d.piece_subset i)
    (d.disjoint_interiors hi.symm) hx hbase htop
    (fun _ hp => (h.outer_halves.1 hp).2.2) hy.1 hy.2 hmem
  obtain ⟨p, hp, hpy⟩ := h.other_above hc hi
  exact (not_le_of_gt hpy) (hcap p (interior_subset hp))

/-- No other actual piece touches strictly inside a terminal vertical
contact interval of the upper outer piece.  The interval is specified by
the reflected lower contact data. -/
theorem other_not_mem_strict_upper_side
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    {x c y : ℝ} (hx : x = 0 ∨ x = 1)
    (hcontact : ∀ z : ℝ,
      Schoenflies.Plane.mk x z ∈ d.piece 0 ↔ z ∈ Icc (0 : ℝ) c)
    (hy : y ∈ Ioo (1 - c) (1 : ℝ)) {i : Fin 4} (hi : i ≠ 1) :
    Schoenflies.Plane.mk x y ∉ d.piece i := by
  intro hmem
  let H := ReflectionSeparation.horizontal
  have hQ : IsJordanRegion (H '' d.piece i) :=
    (d.jordan i).image_homeomorph H.toHomeomorph
  have hQS : H '' d.piece i ⊆ unitSquare := by
    rintro _ ⟨p, hp, rfl⟩
    exact ReflectionSeparation.horizontal_mem_unitSquare.mpr (d.piece_subset i hp)
  have hdis : Disjoint (interior (d.piece 0)) (interior (H '' d.piece i)) := by
    have hdis := RectangularHull.disjoint_interiors_image_homeomorph
      (d.disjoint_interiors hi.symm) H.toHomeomorph
    change Disjoint (interior (H '' d.piece 1)) (interior (H '' d.piece i)) at hdis
    rw [show H '' d.piece 1 = d.piece 0 from h.reflection_back] at hdis
    exact hdis
  have hc0 : 0 ≤ c := by linarith only [hy.1, hy.2]
  have hbase : Schoenflies.Plane.mk x 0 ∈ d.piece 0 :=
    (hcontact 0).mpr ⟨le_rfl, hc0⟩
  have htop : Schoenflies.Plane.mk x c ∈ d.piece 0 :=
    (hcontact c).mpr ⟨hc0, le_rfl⟩
  have hmemH : Schoenflies.Plane.mk x (1 - y) ∈ H '' d.piece i := by
    refine ⟨Schoenflies.Plane.mk x y, hmem, ?_⟩
    ext j
    fin_cases j <;> simp [H]
  have hcap := RectangularHull.vertical_contact_height_bound
    (d.jordan 0) hQ (d.piece_subset 0) hQS hdis hx hbase htop
    (fun _ hp => (h.outer_halves.1 hp).2.2)
    (by linarith only [hy.2] : 0 < 1 - y)
    (by linarith only [hy.1] : 1 - y < c) hmemH
  obtain ⟨p, hp, hpy⟩ := h.other_below hc hi
  have hbound := hcap (H p) (mem_image_of_mem H (interior_subset hp))
  change ReflectionSeparation.horizontal p 1 ≤ (1 / 2 : ℝ) at hbound
  rw [ReflectionSeparation.horizontal_apply_one] at hbound
  linarith only [hbound, hpy]

/-- The complete bottom side has only the lower outer tile as an owner. -/
theorem other_not_mem_bottom
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    (x : ℝ) {i : Fin 4} (hi : i ≠ 0) :
    Schoenflies.Plane.mk x 0 ∉ d.piece i := by
  intro hp
  fin_cases i
  · exact hi rfl
  · have hbound := (h.outer_halves.2 hp).2.1
    norm_num at hbound
  · have hbound := h.middle_y_pos hc (Or.inl rfl) hp
    norm_num at hbound
  · have hbound := h.middle_y_pos hc (Or.inr rfl) hp
    norm_num at hbound

/-- The complete top side has only the upper outer tile as an owner. -/
theorem other_not_mem_top
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    (x : ℝ) {i : Fin 4} (hi : i ≠ 1) :
    Schoenflies.Plane.mk x 1 ∉ d.piece i := by
  intro hp
  fin_cases i
  · have hbound := (h.outer_halves.1 hp).2.2
    norm_num at hbound
  · exact hi rfl
  · have hbound := h.middle_y_lt_one hc (Or.inl rfl) hp
    norm_num at hbound
  · have hbound := h.middle_y_lt_one hc (Or.inr rfl) hp
    norm_num at hbound

/-- A point with at most one bounded-piece owner cannot be an extended
triple junction, even if it belongs to the exterior. -/
theorem not_mem_junctions_of_unique_tile {p : Plane} {i : Fin 4}
    (hunique : ∀ j : Fin 4, j ≠ i → p ∉ d.piece j) :
    p ∉ tripleContactSet d.extendedPiece := by
  have hallowed (j : ExtendedPieceIndex) (hj : p ∈ d.extendedPiece j) :
      j = Sum.inl i ∨ j = Sum.inr () := by
    cases j with
    | inl j =>
      by_cases hji : j = i
      · exact Or.inl (congrArg Sum.inl hji)
      · exact (hunique j hji hj).elim
    | inr u => exact Or.inr (congrArg Sum.inr (Subsingleton.elim u ()))
  rintro ⟨j, k, l, hjk, hjl, hkl, hj, hk, hl⟩
  rcases hallowed j hj with rfl | rfl <;>
    rcases hallowed k hk with rfl | rfl <;>
    rcases hallowed l hl with rfl | rfl <;> simp_all

end Puzzling139335.N4MiddleInvolutions.BoundaryBalance
