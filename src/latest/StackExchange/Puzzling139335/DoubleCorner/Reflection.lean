import StackExchange.Puzzling139335.DoubleCorner.LocalCover
import StackExchange.Puzzling139335.DoubleCorner.Reflection.Conjugation
import StackExchange.Puzzling139335.SquareSymmetry.CornerRigidity
import StackExchange.Puzzling139335.ReflectionSeparation
import StackExchange.Puzzling139335.AcuteCorner.Cone

/-!
# An involution at a corner shared by exactly two tiles

The two actual closed tiles cover a relative neighborhood of their common
corner. If an involution exchanges them, that neighborhood is mapped into
the square. The rigidity of a square corner forces diagonal reflection.
No straight-boundary or angular-germ assumption is used here.
-/

open Set Metric

namespace Puzzling139335.DoubleCorner.Reflection

noncomputable section

open ReflectionSeparation

/-- An involution exchanging two subsets preserves their union. -/
theorem image_union_of_involutive {P Q : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hi : Function.Involutive e)
    (he : e '' P = Q) : e '' (P ∪ Q) = P ∪ Q := by
  have hQ : e '' Q = P := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rw [← he] at hq
      obtain ⟨r, hr, rfl⟩ := hq
      rw [hi]
      exact hr
    · intro hp
      refine ⟨e p, ?_, hi p⟩
      rw [← he]
      exact Set.mem_image_of_mem e hp
  rw [Set.image_union, he, hQ, Set.union_comm]

/-- Local coverage by the two sets makes their swapping involution a
square symmetry. The nonempty interior excludes the identity option. -/
theorem eq_diagonal_of_involutive_local_cover {P Q : Set Plane}
    (hP : IsJordanRegion P) (hPsub : P ⊆ unitSquare) (hQsub : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0)
    (hi : Function.Involutive e) (he : e '' P = Q)
    {ε : ℝ} (hε : 0 < ε) (hcover : ball 0 ε ∩ unitSquare ⊆ P ∪ Q) :
    e = ReflectionSeparation.diagonal := by
  have hlocal : e '' (ball 0 ε ∩ unitSquare) ⊆ unitSquare := by
    calc
      e '' (ball 0 ε ∩ unitSquare) ⊆ e '' (P ∪ Q) := Set.image_mono hcover
      _ = P ∪ Q := image_union_of_involutive e hi he
      _ ⊆ unitSquare := Set.union_subset hPsub hQsub
  rcases SquareSymmetry.coordinate_form_of_origin_neighborhood e he0 hε hlocal with
    hid | hdiag
  · have hPQ : P = Q := by simpa only [hid, Set.image_id'] using he
    obtain ⟨p, hp⟩ := hP.interior_nonempty
    exact False.elim (Set.disjoint_left.mp hdis hp (hPQ ▸ hp))
  · apply AffineIsometryEquiv.ext
    intro p
    rw [hdiag]
    ext j
    fin_cases j <;> rfl

/-- Containment in the square and on one side of its main diagonal
provides an actual forty-five-degree support cone at the origin. -/
theorem supports45_of_diagonal_side {P : Set Plane} (hP : P ⊆ unitSquare)
    (hside : P ⊆ {p | p 0 ≤ p 1} ∨ P ⊆ {p | p 1 ≤ p 0}) :
    AcuteCorner.Supports45 P (corner 0) := by
  rcases hside with hside | hside
  · refine ⟨ReflectionSeparation.diagonal, ?_, ?_⟩
    · ext j
      fin_cases j <;> norm_num [corner, Fin.ext_iff]
    · rintro _ ⟨p, hp, rfl⟩
      change 0 ≤ p 0 ∧ p 0 ≤ p 1
      exact ⟨(hP hp).1.1, hside hp⟩
  · refine ⟨AffineIsometryEquiv.refl ℝ Plane, ?_, ?_⟩
    · ext j
      fin_cases j <;> norm_num [corner, Fin.ext_iff]
    · rintro _ ⟨p, hp, rfl⟩
      change 0 ≤ p 1 ∧ p 1 ≤ p 0
      exact ⟨(hP hp).2.1, hside hp⟩

/-- Once the exchanging map is diagonal reflection, both actual tiles
have a supporting cone of angle at most forty-five degrees. -/
theorem supports45_pair_of_diagonal {P Q : Set Plane}
    (hP : IsJordanRegion P) (hPsub : P ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (he : ReflectionSeparation.diagonal '' P = Q) :
    AcuteCorner.Supports45 P (corner 0) ∧
      AcuteCorner.Supports45 Q (corner 0) := by
  have hfirst := supports45_of_diagonal_side hPsub (diagonal_side hP he hdis)
  have hcorner : ReflectionSeparation.diagonal (corner 0) = corner 0 := by
    apply diagonal_fixed
    norm_num [corner, Fin.ext_iff]
  exact ⟨hfirst, by simpa only [he, hcorner] using hfirst.image ReflectionSeparation.diagonal⟩

end

end Puzzling139335.DoubleCorner.Reflection

namespace Puzzling139335.SquareDissection

noncomputable section

/-- At any square corner, the involution exchanging the only two nearby
tiles preserves the whole square. -/
theorem involution_at_double_corner_preserves_square (d : SquareDissection)
    {i k : Fin 4} (e : Plane ≃ᵃⁱ[ℝ] Plane) (hi : Function.Involutive e)
    (he : e '' d.piece i = d.piece k) (v : Fin 4)
    (hfix : e (corner v) = corner v)
    (hother : ∀ j, j ≠ i → j ≠ k → corner v ∉ d.piece j) :
    e '' unitSquare = unitSquare := by
  obtain ⟨ε, hε, hcover⟩ := d.two_piece_relative_neighborhood hother
  have hlocal : e '' (ball (corner v) ε ∩ unitSquare) ⊆ unitSquare := by
    calc
      e '' (ball (corner v) ε ∩ unitSquare) ⊆
          e '' (d.piece i ∪ d.piece k) := Set.image_mono hcover
      _ = d.piece i ∪ d.piece k :=
        DoubleCorner.Reflection.image_union_of_involutive e hi he
      _ ⊆ unitSquare := Set.union_subset (d.piece_subset i) (d.piece_subset k)
  exact SquareSymmetry.preserves_square_of_corner_neighborhood e v v hfix hε hlocal

/-- The center is excluded from both incident tiles for an exchanging
involution at any double corner. -/
theorem involution_at_double_corner_center_excluded (d : SquareDissection)
    {i k : Fin 4} (hik : i ≠ k)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hi : Function.Involutive e)
    (he : e '' d.piece i = d.piece k) (v : Fin 4)
    (hfix : e (corner v) = corner v)
    (hother : ∀ j, j ≠ i → j ≠ k → corner v ∉ d.piece j) :
    squareCenter ∉ interior (d.piece i) ∧ squareCenter ∉ interior (d.piece k) :=
  d.center_not_mem_fixed_pair hik e he
    (SquareSymmetry.center_fixed_of_preserves_square e
      (d.involution_at_double_corner_preserves_square e hi he v hfix hother))

/-- The orientation-reversing version at an arbitrary square corner. -/
theorem reflection_at_double_corner_center_excluded (d : SquareDissection)
    {i k : Fin 4} (hik : i ≠ k)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hdet : (PlaneIsometries.linearMatrix e).det = -1)
    (he : e '' d.piece i = d.piece k) (v : Fin 4)
    (hfix : e (corner v) = corner v)
    (hother : ∀ j, j ≠ i → j ≠ k → corner v ∉ d.piece j) :
    squareCenter ∉ interior (d.piece i) ∧ squareCenter ∉ interior (d.piece k) :=
  d.involution_at_double_corner_center_excluded hik e
    (PlaneIsometries.involutive_of_det_neg_one_of_fixed_point e hdet hfix) he v hfix hother

/-- The actual local-cover theorem for a pair incident at the origin.
The only map hypothesis here is involutivity, not a boundary-germ model. -/
theorem involution_at_double_corner_zero (d : SquareDissection)
    {i k : Fin 4} (hik : i ≠ k)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0)
    (hi : Function.Involutive e) (he : e '' d.piece i = d.piece k)
    (hother : ∀ j, j ≠ i → j ≠ k → (0 : Plane) ∉ d.piece j) :
    e = ReflectionSeparation.diagonal := by
  obtain ⟨ε, hε, hcover⟩ := d.two_piece_relative_neighborhood hother
  exact DoubleCorner.Reflection.eq_diagonal_of_involutive_local_cover (d.jordan i)
    (d.piece_subset i) (d.piece_subset k) (d.disjoint_interiors hik)
    e he0 hi he hε hcover

/-- An involution at a double corner supplies both support cones and
excludes the center from the interior of either exchanged tile. -/
theorem involution_at_double_corner_zero_consequences (d : SquareDissection)
    {i k : Fin 4} (hik : i ≠ k)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0)
    (hi : Function.Involutive e) (he : e '' d.piece i = d.piece k)
    (hother : ∀ j, j ≠ i → j ≠ k → (0 : Plane) ∉ d.piece j) :
    AcuteCorner.Supports45 (d.piece i) (corner 0) ∧
      AcuteCorner.Supports45 (d.piece k) (corner 0) ∧
      squareCenter ∉ interior (d.piece i) ∧
      squareCenter ∉ interior (d.piece k) := by
  have heq := d.involution_at_double_corner_zero hik e he0 hi he hother
  have hdiag : ReflectionSeparation.diagonal '' d.piece i = d.piece k := by
    simpa only [heq] using he
  have hsupports := DoubleCorner.Reflection.supports45_pair_of_diagonal (d.jordan i)
    (d.piece_subset i) (d.disjoint_interiors hik) hdiag
  have hcenter := d.center_not_mem_fixed_pair hik ReflectionSeparation.diagonal
    hdiag ReflectionSeparation.diagonal_center
  exact ⟨hsupports.1, hsupports.2, hcenter.1, hcenter.2⟩

/-- An orientation-reversing congruence fixing the double corner is the
main diagonal reflection, with orientation expressed by its determinant. -/
theorem reflection_at_double_corner_zero (d : SquareDissection)
    {i k : Fin 4} (hik : i ≠ k)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0)
    (hdet : (PlaneIsometries.linearMatrix e).det = -1)
    (he : e '' d.piece i = d.piece k)
    (hother : ∀ j, j ≠ i → j ≠ k → (0 : Plane) ∉ d.piece j) :
    e = ReflectionSeparation.diagonal :=
  d.involution_at_double_corner_zero hik e he0
    (PlaneIsometries.involutive_of_det_neg_one_of_fixed_point e hdet he0) he hother

/-- The support and center conclusions for an orientation-reversing
same-corner congruence, without any polygonal boundary assumptions. -/
theorem reflection_at_double_corner_zero_consequences (d : SquareDissection)
    {i k : Fin 4} (hik : i ≠ k)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0)
    (hdet : (PlaneIsometries.linearMatrix e).det = -1)
    (he : e '' d.piece i = d.piece k)
    (hother : ∀ j, j ≠ i → j ≠ k → (0 : Plane) ∉ d.piece j) :
    AcuteCorner.Supports45 (d.piece i) (corner 0) ∧
      AcuteCorner.Supports45 (d.piece k) (corner 0) ∧
      squareCenter ∉ interior (d.piece i) ∧
      squareCenter ∉ interior (d.piece k) :=
  d.involution_at_double_corner_zero_consequences hik e he0
    (PlaneIsometries.involutive_of_det_neg_one_of_fixed_point e hdet he0) he hother

/-- The same normalized reflection rigidity theorem with the reversing
coordinate branch supplied directly by plane-isometry classification. -/
theorem reversing_coordinates_at_double_corner_zero (d : SquareDissection)
    {i k : Fin 4} (hik : i ≠ k)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0) {c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1)
    (hform : ∀ p, e p = PlaneIsometries.reversingCoordinates c s (e 0) p)
    (he : e '' d.piece i = d.piece k)
    (hother : ∀ j, j ≠ i → j ≠ k → (0 : Plane) ∉ d.piece j) :
    e = ReflectionSeparation.diagonal :=
  d.involution_at_double_corner_zero hik e he0
    (PlaneIsometries.involutive_of_reversing_coordinates e hcs he0 hform) he hother

/-- Support cones and center exclusion for the raw reversing-coordinate
branch, still referring only to the actual dissection. -/
theorem reversing_coordinates_at_double_corner_zero_consequences (d : SquareDissection)
    {i k : Fin 4} (hik : i ≠ k)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0) {c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1)
    (hform : ∀ p, e p = PlaneIsometries.reversingCoordinates c s (e 0) p)
    (he : e '' d.piece i = d.piece k)
    (hother : ∀ j, j ≠ i → j ≠ k → (0 : Plane) ∉ d.piece j) :
    AcuteCorner.Supports45 (d.piece i) (corner 0) ∧
      AcuteCorner.Supports45 (d.piece k) (corner 0) ∧
      squareCenter ∉ interior (d.piece i) ∧
      squareCenter ∉ interior (d.piece k) :=
  d.involution_at_double_corner_zero_consequences hik e he0
    (PlaneIsometries.involutive_of_reversing_coordinates e hcs he0 hform) he hother

end

end Puzzling139335.SquareDissection
