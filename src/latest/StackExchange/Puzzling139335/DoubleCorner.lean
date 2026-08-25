import StackExchange.Puzzling139335.DoubleCorner.Normalized
import StackExchange.Puzzling139335.DoubleCorner.MixedCorner
import StackExchange.Puzzling139335.IntrinsicCorners
import StackExchange.Puzzling139335.Transform

/-!
# A repeated intrinsic point at a double square corner

If exactly two pieces occur at a square corner and a congruence between
them fixes that corner, their actual germs are the two half-quadrants.
In particular they have global 45-degree supports and neither contains the
square center in its interior. No straightness assumption is made.
-/

open Set Metric

namespace Puzzling139335.SquareDissection

noncomputable section

open SquareSymmetry DoubleCorner AcuteCorner

/-- Normalize the common corner by the actual coordinate reflection of
the square. The two pieces then fill opposite 45-degree cones locally. -/
theorem double_corner_normalized_halfCones (d : SquareDissection)
    {i k j : Fin 4} (hik : i ≠ k)
    (hi : corner j ∈ d.piece i) (hk : corner j ∈ d.piece k)
    (hother : ∀ l, l ≠ i → l ≠ k → corner j ∉ d.piece l)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece i = d.piece k)
    (hfix : e (corner j) = corner j) :
    ((cornerFlip j '' d.piece i) ⊆ cone45 ∧
      (cornerFlip j '' d.piece k) ⊆ upperCone45 ∧
      SameBoundaryGerm (cornerFlip j '' d.piece i) cone45 0 ∧
      SameBoundaryGerm (cornerFlip j '' d.piece k) upperCone45 0) ∨
    ((cornerFlip j '' d.piece i) ⊆ upperCone45 ∧
      (cornerFlip j '' d.piece k) ⊆ cone45 ∧
      SameBoundaryGerm (cornerFlip j '' d.piece i) upperCone45 0 ∧
      SameBoundaryGerm (cornerFlip j '' d.piece k) cone45 0) := by
  let f := cornerFlip j
  let d' := d.map f (cornerFlip_image_unitSquare j)
  let e' := (f.trans e).trans f
  have hi0 : (0 : Plane) ∈ d'.piece i :=
    ⟨corner j, hi, cornerFlip_corner j⟩
  have hk0 : (0 : Plane) ∈ d'.piece k :=
    ⟨corner j, hk, cornerFlip_corner j⟩
  have hother' : ∀ l, l ≠ i → l ≠ k → (0 : Plane) ∉ d'.piece l := by
    intro l hli hlk hl
    obtain ⟨p, hp, hfp⟩ := hl
    have hpj : p = corner j := by
      apply f.injective
      exact hfp.trans (cornerFlip_corner j).symm
    exact hother l hli hlk (hpj ▸ hp)
  have he0 : e' 0 = 0 := Reflection.cornerFlip_conjugate_zero j e hfix
  have he' : e' '' d'.piece i = d'.piece k := by
    change e' '' (f '' d.piece i) = f '' d.piece k
    calc
      e' '' (f '' d.piece i) = (fun p => f (e p)) '' d.piece i := by
        rw [image_image]
        congr 1
        funext p
        change f (e (f (f p))) = f (e p)
        rw [cornerFlip_involutive]
      _ = f '' (e '' d.piece i) := by rw [image_image]
      _ = f '' d.piece k := by rw [he]
  obtain ⟨ε, hε, hcover⟩ := d'.two_piece_relative_neighborhood hother'
  exact halfCone_germs_of_local_congruence (d'.jordan i) (d'.jordan k)
    (d'.piece_subset i) (d'.piece_subset k) (d'.disjoint_interiors hik)
    hi0 hk0 e' he' he0 hε hcover

private theorem support_of_cornerFlip_lower {P : Set Plane} (j : Fin 4)
    (h : cornerFlip j '' P ⊆ cone45) : Supports45 P (corner j) :=
  ⟨cornerFlip j, cornerFlip_corner j, h⟩

private theorem support_of_cornerFlip_upper {P : Set Plane} (j : Fin 4)
    (h : cornerFlip j '' P ⊆ upperCone45) : Supports45 P (corner j) := by
  refine ⟨(cornerFlip j).trans ReflectionSeparation.diagonal, ?_, ?_⟩
  · change ReflectionSeparation.diagonal (cornerFlip j (corner j)) = 0
    rw [cornerFlip_corner]
    ext r
    fin_cases r <;> simp
  · rintro q ⟨p, hp, rfl⟩
    have hcone := h (mem_image_of_mem (cornerFlip j) hp)
    change 0 ≤ cornerFlip j p 0 ∧ cornerFlip j p 0 ≤ cornerFlip j p 1
    exact hcone

private theorem center_exclusion_of_cornerFlip_diagonal_support
    {P : Set Plane} (j : Fin 4)
    (h : (cornerFlip j '' P) ⊆ cone45 ∨ (cornerFlip j '' P) ⊆ upperCone45) :
    squareCenter ∉ interior P := by
  have hside : (∀ p ∈ cornerFlip j '' P, p 0 ≤ p 1) ∨
      (∀ p ∈ cornerFlip j '' P, p 1 ≤ p 0) := by
    rcases h with hlower | hupper
    · exact Or.inr (fun p hp => (hlower hp).2)
    · exact Or.inl (fun p hp => (hupper hp).2)
  have hnot := squareCenter_not_mem_interior_of_diagonal_support hside
  intro hp
  apply hnot
  simpa only [cornerFlip_center] using
    (mem_interior_image_affineIsometry (cornerFlip j) (P := P) (p := squareCenter)).mpr hp

/-- A congruence fixing a corner occupied by exactly its two pieces
forces both supporting 45-degree wedges and excludes the center. -/
theorem double_corner_support_and_center_exclusion (d : SquareDissection)
    {i k j : Fin 4} (hik : i ≠ k)
    (hi : corner j ∈ d.piece i) (hk : corner j ∈ d.piece k)
    (hother : ∀ l, l ≠ i → l ≠ k → corner j ∉ d.piece l)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece i = d.piece k)
    (hfix : e (corner j) = corner j) :
    Supports45 (d.piece i) (corner j) ∧ Supports45 (d.piece k) (corner j) ∧
      squareCenter ∉ interior (d.piece i) ∧ squareCenter ∉ interior (d.piece k) := by
  rcases d.double_corner_normalized_halfCones hik hi hk hother e he hfix with h | h
  · exact ⟨support_of_cornerFlip_lower j h.1, support_of_cornerFlip_upper j h.2.1,
      center_exclusion_of_cornerFlip_diagonal_support j (Or.inl h.1),
      center_exclusion_of_cornerFlip_diagonal_support j (Or.inr h.2.1)⟩
  · exact ⟨support_of_cornerFlip_upper j h.1, support_of_cornerFlip_lower j h.2.1,
      center_exclusion_of_cornerFlip_diagonal_support j (Or.inr h.1),
      center_exclusion_of_cornerFlip_diagonal_support j (Or.inl h.2.1)⟩

/-- The form used by the incidence reductions: equality of the two
intrinsic corner preimages supplies the actual fixing congruence. -/
theorem same_intrinsic_double_corner (d : SquareDissection)
    {i k j : Fin 4} (hik : i ≠ k)
    (hi : corner j ∈ d.piece i) (hk : corner j ∈ d.piece k)
    (hother : ∀ l, l ≠ i → l ≠ k → corner j ∉ d.piece l)
    (htype : d.intrinsicCorner i j = d.intrinsicCorner k j) :
    Supports45 (d.piece i) (corner j) ∧ Supports45 (d.piece k) (corner j) ∧
      squareCenter ∉ interior (d.piece i) ∧ squareCenter ∉ interior (d.piece k) :=
  d.double_corner_support_and_center_exclusion hik hi hk hother (d.relativePlacement i k)
    (d.relativePlacement_image i k) (d.relativePlacement_corner htype)

/-- The common prototype point inherits the same supporting cone. -/
theorem same_intrinsic_double_corner_prototype_support (d : SquareDissection)
    {i k j : Fin 4} (hik : i ≠ k)
    (hi : corner j ∈ d.piece i) (hk : corner j ∈ d.piece k)
    (hother : ∀ l, l ≠ i → l ≠ k → corner j ∉ d.piece l)
    (htype : d.intrinsicCorner i j = d.intrinsicCorner k j) :
    Supports45 (d.piece 0) (d.intrinsicCorner i j) := by
  have h := (d.same_intrinsic_double_corner hik hi hk hother htype).1
  have h' := h.image (d.placement i).symm
  have himage : (d.placement i).symm '' d.piece i = d.piece 0 := by
    rw [← d.placement_image i, image_image]
    simp
  simpa only [himage, intrinsicCorner] using h'

end

end Puzzling139335.SquareDissection
