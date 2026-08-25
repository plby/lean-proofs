import StackExchange.Puzzling139335.N6.TwoDouble.UnitRay.Transport
import StackExchange.Puzzling139335.N6.TwoDouble.UnitRay.GermPlacement
import StackExchange.Puzzling139335.N6.TwoDouble.UnitRay.Normalized
import StackExchange.Puzzling139335.N6.TwoDouble.UnitRay.Dissection.SideTransport
import StackExchange.Puzzling139335.N5.Transport

/-!
# A singleton copy cannot carry the actual unit ray of a repeated corner

The filled forty-five-degree source germ is derived from the original
two-piece corner cover.  Actual congruences transport both that germ and
the source square-side segment.  At a second double corner, Jordan
separation places the transported germ against a square side.  Its actual
unit boundary ray therefore either reaches a second square corner or
passes through the square center.  Both alternatives contradict the
singleton and protected-center assumptions.
-/

open Set

namespace Puzzling139335.N6.TwoDouble.UnitRay

open AcuteCorner DoubleCorner SquareSymmetry

noncomputable section

/-- A piece with exactly one physical square corner cannot contain two
different corners. -/
theorem corners_eq_of_singleton (d : SquareDissection) {i a b : Fin 4}
    (hcount : d.tileCornerCount i = 1)
    (ha : corner a ∈ d.piece i) (hb : corner b ∈ d.piece i) : a = b := by
  classical
  change (Finset.univ.filter fun j => corner j ∈ d.piece i).card = 1 at hcount
  exact Finset.card_le_one_iff.mp hcount.le
    (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ha)
    (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hb)

/-- In the origin-normalized square, a singleton piece with a filled
forty-five-degree germ cannot contain an actual unit frontier ray. -/
theorem singleton_unit_frontier_ray_impossible (d : SquareDissection)
    (hc : d.HasProtectedCenter) {i : Fin 4} {w : Plane}
    (hcount : d.tileCornerCount i = 1) (hzero : (0 : Plane) ∈ d.piece i)
    (hgerm : SameBoundaryGerm (d.piece i) cone45 0 ∨
      SameBoundaryGerm (d.piece i) upperCone45 0)
    (hseg : segment ℝ 0 w ⊆ frontier (d.piece i)) (hnorm : ‖w‖ = 1) : False := by
  have h0 : corner 0 ∈ d.piece i := by
    convert hzero using 1
    ext j
    fin_cases j <;> norm_num [corner, Fin.ext_iff]
  have hw : w ∈ d.piece i :=
    (d.jordan i).isClosed.frontier_subset (hseg (right_mem_segment ℝ _ _))
  rcases normalized_unitRay_endpoint_or_center hgerm hseg hnorm with h1 | h3 | hcenter
  · have heq : (1 : Fin 4) = 0 := corners_eq_of_singleton d hcount (h1 ▸ hw) h0
    exact (by decide : (1 : Fin 4) ≠ 0) heq
  · have heq : (3 : Fin 4) = 0 := corners_eq_of_singleton d hcount (h3 ▸ hw) h0
    exact (by decide : (3 : Fin 4) ≠ 0) heq
  · obtain ⟨c, hci⟩ := hc
    by_cases hciEq : c = i
    · subst c
      exact hcenter.2 hci
    · exact d.not_mem_other_piece hciEq hci
        ((d.jordan i).isClosed.frontier_subset hcenter)

/-- The same obstruction in coordinates normalized at any physical square
corner. The corner count and the protected center are transported by the
actual symmetry of the whole dissection. -/
theorem singleton_unit_frontier_ray_impossible_at_corner (d : SquareDissection)
    (hc : d.HasProtectedCenter) {i j : Fin 4} {w : Plane}
    (hcount : d.tileCornerCount i = 1) (hj : corner j ∈ d.piece i)
    (hgerm : SameBoundaryGerm (cornerFlip j '' d.piece i) cone45 0 ∨
      SameBoundaryGerm (cornerFlip j '' d.piece i) upperCone45 0)
    (hseg : segment ℝ 0 w ⊆ frontier (cornerFlip j '' d.piece i))
    (hnorm : ‖w‖ = 1) : False := by
  let D := d.map (cornerFlip j) (cornerFlip_image_unitSquare j)
  have hDc : D.HasProtectedCenter :=
    (d.map_hasProtectedCenter (cornerFlip j) (cornerFlip_image_unitSquare j)).mpr hc
  have hDcount : D.tileCornerCount i = 1 :=
    (N5.tileCornerCount_map d (cornerFlip j) (cornerFlip_image_unitSquare j) i).trans hcount
  have hDzero : (0 : Plane) ∈ D.piece i := ⟨corner j, hj, cornerFlip_corner j⟩
  exact singleton_unit_frontier_ray_impossible D hDc hDcount hDzero hgerm hseg hnorm

/-- When the singleton is the other copy at the repeated source corner,
the double-corner theorem directly supplies its normalized filled germ.
This specialization needs no further local placement argument. -/
theorem repeated_corner_singleton_unitRay_impossible (d : SquareDissection)
    (hc : d.HasProtectedCenter) {i k j m : Fin 4}
    (hik : i ≠ k) (hi : corner j ∈ d.piece i) (hk : corner j ∈ d.piece k)
    (hother : ∀ l, l ≠ i → l ≠ k → corner j ∉ d.piece l)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece i = d.piece k)
    (hfix : e (corner j) = corner j)
    (hcount : d.tileCornerCount k = 1)
    (hseg : segment ℝ (corner j) (corner m) ⊆ d.piece i)
    (hadj : m = j + 1 ∨ j = m + 1) : False := by
  have hgerm : SameBoundaryGerm (cornerFlip j '' d.piece k) cone45 0 ∨
      SameBoundaryGerm (cornerFlip j '' d.piece k) upperCone45 0 := by
    rcases d.double_corner_normalized_halfCones hik hi hk hother e he hfix with h | h
    · exact Or.inr h.2.2.2
    · exact Or.inl h.2.2.2
  obtain ⟨hnorm, hfrontier⟩ := transported_unit_side_segment d hseg hadj e he hfix
  exact singleton_unit_frontier_ray_impossible_at_corner d hc hcount hk
    hgerm hfrontier hnorm

/-- A transported filled forty-five-degree germ at an actual two-owner
corner must be one of the two normalized half-quadrants.  The local cover
is obtained from closedness of the other dissection pieces. -/
theorem normalized_germ_of_transported_filled45 (d : SquareDissection)
    {i k j : Fin 4} (hik : i ≠ k) (hi : corner j ∈ d.piece i)
    (hother : ∀ l, l ≠ i → l ≠ k → corner j ∉ d.piece l)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0)
    (hsub : cornerFlip j '' d.piece i ⊆ e '' cone45)
    (hgerm : SameBoundaryGerm (cornerFlip j '' d.piece i) (e '' cone45) 0) :
    (cornerFlip j '' d.piece i ⊆ cone45 ∧
      SameBoundaryGerm (cornerFlip j '' d.piece i) cone45 0) ∨
    (cornerFlip j '' d.piece i ⊆ upperCone45 ∧
      SameBoundaryGerm (cornerFlip j '' d.piece i) upperCone45 0) := by
  let D := d.map (cornerFlip j) (cornerFlip_image_unitSquare j)
  have hi0 : (0 : Plane) ∈ D.piece i := ⟨corner j, hi, cornerFlip_corner j⟩
  have hother' : ∀ l, l ≠ i → l ≠ k → (0 : Plane) ∉ D.piece l := by
    intro l hli hlk hl
    obtain ⟨p, hp, hfp⟩ := hl
    have hpj : p = corner j :=
      (cornerFlip j).injective (hfp.trans (cornerFlip_corner j).symm)
    exact hother l hli hlk (hpj ▸ hp)
  obtain ⟨ε, hε, hcover⟩ := D.two_piece_relative_neighborhood hother'
  exact cone_germ_at_double_corner (D.jordan i) (D.jordan k)
    (D.piece_subset i) (D.piece_subset k) (D.disjoint_interiors hik)
    hi0 e he0 hsub hgerm hε hcover

/-- The actual unit-side obstruction for an arbitrary singleton copy of
the repeated source corner.  Neither the source filled germ nor the target
placement alternatives are assumed: both follow from the two actual
double-corner covers and the given congruences. -/
theorem singleton_unitRay_from_repeated_corner_impossible (d : SquareDissection)
    (hc : d.HasProtectedCenter) {i k j m t u l : Fin 4}
    (hik : i ≠ k) (hi : corner j ∈ d.piece i) (hk : corner j ∈ d.piece k)
    (hsourceOther : ∀ q, q ≠ i → q ≠ k → corner j ∉ d.piece q)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece i = d.piece k)
    (hfix : e (corner j) = corner j)
    (htu : t ≠ u) (ht : corner l ∈ d.piece t)
    (htargetOther : ∀ q, q ≠ t → q ≠ u → corner l ∉ d.piece q)
    (f : Plane ≃ᵃⁱ[ℝ] Plane) (hf : f '' d.piece i = d.piece t)
    (hmap : f (corner j) = corner l)
    (hcount : d.tileCornerCount t = 1)
    (hseg : segment ℝ (corner j) (corner m) ⊆ d.piece i)
    (hadj : m = j + 1 ∨ j = m + 1) : False := by
  obtain ⟨a, haj, hsub, hgerm⟩ :=
    source_normalized_filled45 d hik hi hk hsourceOther e he hfix
  obtain ⟨g, hg0, htargetSub, htargetGerm⟩ :=
    transported_filled45 a haj hsub hgerm f hf l hmap
  have htarget := normalized_germ_of_transported_filled45 d htu ht htargetOther
    g hg0 htargetSub htargetGerm
  have htarget' : SameBoundaryGerm (cornerFlip l '' d.piece t) cone45 0 ∨
      SameBoundaryGerm (cornerFlip l '' d.piece t) upperCone45 0 := by
    rcases htarget with h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
  obtain ⟨hnorm, hfrontier⟩ := transported_unit_side_segment d hseg hadj f hf hmap
  exact singleton_unit_frontier_ray_impossible_at_corner d hc hcount ht
    htarget' hfrontier hnorm

end

end Puzzling139335.N6.TwoDouble.UnitRay
