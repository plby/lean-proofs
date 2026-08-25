import StackExchange.Puzzling139335.DoubleCorner.MixedCorner.AxisContact
import StackExchange.Puzzling139335.DoubleCorner.MixedCorner.ConePosition
import StackExchange.Puzzling139335.Transform

/-!
# A supported mixed corner cannot protect the square center

For two actual Jordan pieces covering the square near a corner, a piece
incident at that corner has contact with an outer axis.  A forty-five-degree
support then places the whole piece on one side of the square's diagonal.
The proof uses arbitrary small Jordan arcs and imposes no straightness or
local sector assumption.
-/

open Set Metric

namespace Puzzling139335.DoubleCorner.MixedCorner

open AcuteCorner

/-- The supporting-cone inequality and actual outer-axis contact force a
diagonal support, with no additional boundary regularity. -/
theorem diagonal_support_of_mem_zero
    {P Q : Set Plane} (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPsub : P ⊆ unitSquare) (hQsub : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (hzero : (0 : Plane) ∈ P) (hsupport : Supports45 P 0)
    {ε : ℝ} (hε : 0 < ε) (hcover : ball 0 ε ∩ unitSquare ⊆ P ∪ Q) :
    (∀ p ∈ P, p 0 ≤ p 1) ∨ (∀ p ∈ P, p 1 ≤ p 0) := by
  obtain ⟨x, hxP, hxne, hxaxis⟩ := exists_axis_contact_of_mem_zero
    hP hQ hPsub hQsub hdis hzero hε hcover
  have hxS := hPsub hxP
  exact diagonal_support_of_positive_axis_contact hsupport hxP hxne
    hxS.1.1 hxS.2.1 hxaxis

/-- A forty-five-degree-supported Jordan piece at a double corner cannot
contain an interior neighborhood of the square center. -/
theorem center_excluded_of_support
    {P Q : Set Plane} (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPsub : P ⊆ unitSquare) (hQsub : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (hzero : (0 : Plane) ∈ P) (hsupport : Supports45 P 0)
    {ε : ℝ} (hε : 0 < ε) (hcover : ball 0 ε ∩ unitSquare ⊆ P ∪ Q) :
    squareCenter ∉ interior P :=
  squareCenter_not_mem_interior_of_diagonal_support
    (diagonal_support_of_mem_zero hP hQ hPsub hQsub hdis hzero hsupport hε hcover)

/-- A straight frontier branch and a forty-five-degree support force an
actual diagonal support at a corner covered locally by two Jordan pieces. -/
theorem diagonal_support_of_straight_frontier
    {P Q : Set Plane} (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPsub : P ⊆ unitSquare) (hQsub : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (hsupport : Supports45 P 0) (hstraight : IsStraightAt (frontier P) 0)
    {ε : ℝ} (hε : 0 < ε) (hcover : ball 0 ε ∩ unitSquare ⊆ P ∪ Q) :
    (∀ p ∈ P, p 0 ≤ p 1) ∨ (∀ p ∈ P, p 1 ≤ p 0) := by
  obtain ⟨x, hxP, hxne, hxaxis⟩ := exists_axis_contact_of_straight_frontier
    hP hQ hPsub hQsub hdis hstraight hε hcover
  have hxS := hPsub hxP
  exact diagonal_support_of_positive_axis_contact hsupport hxP hxne
    hxS.1.1 hxS.2.1 hxaxis

/-- Such a supported piece has no interior neighborhood of the square center. -/
theorem center_excluded_of_straight_frontier
    {P Q : Set Plane} (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPsub : P ⊆ unitSquare) (hQsub : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (hsupport : Supports45 P 0) (hstraight : IsStraightAt (frontier P) 0)
    {ε : ℝ} (hε : 0 < ε) (hcover : ball 0 ε ∩ unitSquare ⊆ P ∪ Q) :
    squareCenter ∉ interior P :=
  squareCenter_not_mem_interior_of_diagonal_support
    (diagonal_support_of_straight_frontier hP hQ hPsub hQsub hdis
      hsupport hstraight hε hcover)

/-- The full filled-cone-germ formulation allows any origin-fixing
Euclidean isometry, including reflections.  The germ supplies membership
at the vertex; the stronger theorem handles the remaining geometry. -/
theorem center_excluded_of_cone_germ
    {P Q : Set Plane} (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPsub : P ⊆ unitSquare) (hQsub : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0)
    (hsupport : P ⊆ e '' cone45) (hgerm : SameBoundaryGerm P (e '' cone45) 0)
    {ε : ℝ} (hε : 0 < ε) (hcover : ball 0 ε ∩ unitSquare ⊆ P ∪ Q) :
    squareCenter ∉ interior P := by
  have hzeroCone : (0 : Plane) ∈ cone45 := by simp [cone45]
  have hzeroImage : (0 : Plane) ∈ e '' cone45 := ⟨0, hzeroCone, he0⟩
  obtain ⟨r, hr, hgerm⟩ := hgerm
  have hzeroP : (0 : Plane) ∈ P :=
    ((Set.ext_iff.mp hgerm 0).mpr ⟨mem_ball_self hr, hzeroImage⟩).2
  have hsupportP : Supports45 P 0 := by
    obtain ⟨f, hf0, hf⟩ := supports45_image_cone45 e he0
    exact ⟨f, hf0, (Set.image_mono hsupport).trans hf⟩
  exact center_excluded_of_support hP hQ hPsub hQsub hdis hzeroP hsupportP hε hcover

end Puzzling139335.DoubleCorner.MixedCorner

namespace Puzzling139335.SquareDissection

open AcuteCorner SquareSymmetry

/-- The normalized two-owner specialization uses only actual membership
at the corner and a global support cone. -/
theorem center_excluded_at_double_corner_zero_of_support (d : SquareDissection)
    {i k : Fin 4} (hik : i ≠ k) (hi : (0 : Plane) ∈ d.piece i)
    (hother : ∀ j, j ≠ i → j ≠ k → (0 : Plane) ∉ d.piece j)
    (hsupport : Supports45 (d.piece i) 0) :
    squareCenter ∉ interior (d.piece i) := by
  obtain ⟨ε, hε, hcover⟩ := d.two_piece_relative_neighborhood hother
  exact DoubleCorner.MixedCorner.center_excluded_of_support
    (d.jordan i) (d.jordan k) (d.piece_subset i) (d.piece_subset k)
    (d.disjoint_interiors hik) hi hsupport hε hcover

/-- Any square corner occupied by two pieces excludes the center from a
piece having a supporting cone of at most forty-five degrees there.  All
normalization is by a genuine symmetry of the original square. -/
theorem center_excluded_at_double_corner_of_support (d : SquareDissection)
    {i k j : Fin 4} (hik : i ≠ k)
    (hi : corner j ∈ d.piece i) (_hk : corner j ∈ d.piece k)
    (hother : ∀ l, l ≠ i → l ≠ k → corner j ∉ d.piece l)
    (hsupport : Supports45 (d.piece i) (corner j)) :
    squareCenter ∉ interior (d.piece i) := by
  let f := cornerFlip j
  let d' := d.map f (cornerFlip_image_unitSquare j)
  have hi0 : (0 : Plane) ∈ d'.piece i :=
    ⟨corner j, hi, cornerFlip_corner j⟩
  have hother' : ∀ l, l ≠ i → l ≠ k → (0 : Plane) ∉ d'.piece l := by
    intro l hli hlk hl
    obtain ⟨p, hp, hfp⟩ := hl
    have hpj : p = corner j := by
      apply f.injective
      exact hfp.trans (cornerFlip_corner j).symm
    exact hother l hli hlk (hpj ▸ hp)
  have hsupport' : Supports45 (d'.piece i) 0 := by
    change Supports45 (f '' d.piece i) 0
    simpa only [f, cornerFlip_corner] using hsupport.image f
  have hnot := d'.center_excluded_at_double_corner_zero_of_support
    hik hi0 hother' hsupport'
  intro hp
  apply hnot
  change squareCenter ∈ interior (f '' d.piece i)
  simpa only [f, cornerFlip_center] using
    (mem_interior_image_affineIsometry f (P := d.piece i) (p := squareCenter)).mpr hp

/-- The actual two-owner specialization requires no assumed local sector:
closedness of the other pieces supplies the required local cover. -/
theorem center_excluded_at_double_corner_of_straight_support (d : SquareDissection)
    {i k : Fin 4} (hik : i ≠ k)
    (hsupport : Supports45 (d.piece i) 0)
    (hstraight : IsStraightAt (frontier (d.piece i)) 0)
    (hother : ∀ j, j ≠ i → j ≠ k → (0 : Plane) ∉ d.piece j) :
    squareCenter ∉ interior (d.piece i) := by
  obtain ⟨ε, hε, hcover⟩ := d.two_piece_relative_neighborhood hother
  exact DoubleCorner.MixedCorner.center_excluded_of_straight_frontier
    (d.jordan i) (d.jordan k) (d.piece_subset i) (d.piece_subset k)
    (d.disjoint_interiors hik) hsupport hstraight hε hcover

end Puzzling139335.SquareDissection
