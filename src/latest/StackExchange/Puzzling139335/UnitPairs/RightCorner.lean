import StackExchange.Puzzling139335.UnitPairs.Defs
import StackExchange.Puzzling139335.SquareSymmetry.CornerRigidity

/-!
# Unit side partners at a full square corner

The placements witnessing the unit side pairs need not agree.  A full
relative corner neighborhood forces each relative placement to preserve
the square, however, and therefore to fix its center.  In one normalized
placement every unit partner is one of the two neighboring square corners.
Two distinct partners consequently form a diameter pair.
-/

open Set Metric

namespace Puzzling139335.UnitPairs

open SquareSymmetry

noncomputable section

private theorem corner_dist_sq_center (j : Fin 4) :
    dist (corner j) squareCenter ^ 2 = (1 / 2 : ℝ) := by
  fin_cases j <;> norm_num [plane_dist_sq, corner, squareCenter, Fin.ext_iff]

/-- The center distance of a unit partner, measured in any placement
witnessing the full corner.  The conclusion follows from actual relative
placement rigidity, not from an assumed support ray. -/
theorem unit_partner_dist_sq_center {P : Set Plane} {a b : Plane}
    (f : Plane ≃ᵃⁱ[ℝ] Plane) (i : Fin 4) {ε : ℝ}
    (hε : 0 < ε) (hfa : f a = corner i)
    (hneighborhood : ball (corner i) ε ∩ unitSquare ⊆ f '' P)
    (hab : IsUnitSidePair P a b) :
    dist (f b) squareCenter ^ 2 = (1 / 2 : ℝ) := by
  obtain ⟨_, _, _, e, j, k, he, hea, heb⟩ := hab
  let g := f.symm.trans e
  have hgc : g (corner i) = corner j := by
    change e (f.symm (corner i)) = corner j
    rw [← hfa, f.symm_apply_apply, hea]
  have hg : g '' (ball (corner i) ε ∩ unitSquare) ⊆ unitSquare := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨p, hp, hpq⟩ := hneighborhood hq
    change e (f.symm q) ∈ unitSquare
    rw [← hpq, f.symm_apply_apply]
    exact he (mem_image_of_mem e hp)
  have hcenter : g squareCenter = squareCenter :=
    center_fixed_of_corner_neighborhood g i j hgc hε hg
  have hgb : g (f b) = corner k := by
    change e (f.symm (f b)) = corner k
    rw [f.symm_apply_apply, heb]
  calc
    dist (f b) squareCenter ^ 2 = dist (g (f b)) (g squareCenter) ^ 2 := by
      rw [g.isometry.dist_eq]
    _ = dist (corner k) squareCenter ^ 2 := by rw [hgb, hcenter]
    _ = (1 / 2 : ℝ) := corner_dist_sq_center k

private theorem axis_point_of_two_distances {p : Plane}
    (hunit : dist p 0 = 1) (hcenter : dist p squareCenter ^ 2 = (1 / 2 : ℝ)) :
    p = (!₂[1, 0] : Plane) ∨ p = (!₂[0, 1] : Plane) := by
  have hnorm : p 0 ^ 2 + p 1 ^ 2 = 1 := by
    have hsq := congrArg (fun r : ℝ => r ^ 2) hunit
    simpa only [plane_dist_sq, PiLp.zero_apply, sub_zero, one_pow] using hsq
  have hsum : p 0 + p 1 = 1 := by
    norm_num [plane_dist_sq, squareCenter] at hcenter
    nlinarith
  have hmul : p 0 * p 1 = 0 := by
    nlinarith [congrArg (fun r : ℝ => r ^ 2) hsum]
  rcases mul_eq_zero.mp hmul with hx | hy
  · right
    have hy : p 1 = 1 := by linarith
    apply PlaneIsometries.plane_ext <;> simp [hx, hy]
  · left
    have hx : p 0 = 1 := by linarith
    apply PlaneIsometries.plane_ext <;> simp [hx, hy]

/-- Distinct unit side partners of an actual full square corner are the
opposite endpoints of a square diagonal. -/
theorem IsFullSquareCorner.dist_sq_two_of_unit_partners
    {P : Set Plane} {a b c : Plane} (hfull : IsFullSquareCorner P a)
    (hab : IsUnitSidePair P a b) (hac : IsUnitSidePair P a c) (hbc : b ≠ c) :
    dist b c ^ 2 = 2 := by
  obtain ⟨f, i, ε, hε, _, hfa, hnear⟩ := hfull
  let g := f.trans (cornerFlip i)
  have hga : g a = 0 := by
    change cornerFlip i (f a) = 0
    rw [hfa, cornerFlip_corner]
  have hpartner {p : Plane} (hap : IsUnitSidePair P a p) :
      g p = (!₂[1, 0] : Plane) ∨ g p = (!₂[0, 1] : Plane) := by
    apply axis_point_of_two_distances
    · rw [← hga, g.isometry.dist_eq, dist_comm]
      exact hap.2.2.1
    · change dist (cornerFlip i (f p)) squareCenter ^ 2 = (1 / 2 : ℝ)
      rw [← cornerFlip_center i, (cornerFlip i).isometry.dist_eq]
      exact unit_partner_dist_sq_center f i hε hfa hnear hap
  have hne : g b ≠ g c := fun h => hbc (g.injective h)
  have hdist : dist (g b) (g c) ^ 2 = 2 := by
    rcases hpartner hab with hb | hb <;> rcases hpartner hac with hc | hc
    · exact (hne (hb.trans hc.symm)).elim
    · rw [hb, hc, plane_dist_sq]
      norm_num
    · rw [hb, hc, plane_dist_sq]
      norm_num
    · exact (hne (hb.trans hc.symm)).elim
  simpa only [g.isometry.dist_eq] using hdist

/-- A full corner of a piece in a protected-center dissection has at most
one unit side partner. -/
theorem unit_partners_eq_of_protected_center (d : SquareDissection)
    (hprotected : d.HasProtectedCenter) (i : Fin 4) {a b c : Plane}
    (hfull : IsFullSquareCorner (d.piece i) a)
    (hab : IsUnitSidePair (d.piece i) a b) (hac : IsUnitSidePair (d.piece i) a c) :
    b = c := by
  by_contra hbc
  exact d.no_diameter_pair hprotected i hab.2.1 hac.2.1
    (hfull.dist_sq_two_of_unit_partners hab hac hbc)

/-- The same uniqueness for a prototype with an actual placement as one
piece of the protected-center dissection. -/
theorem unit_partners_eq_of_placement (d : SquareDissection)
    (hprotected : d.HasProtectedCenter) (i : Fin 4) {P : Set Plane} {a b c : Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = d.piece i)
    (hfull : IsFullSquareCorner P a)
    (hab : IsUnitSidePair P a b) (hac : IsUnitSidePair P a c) : b = c := by
  by_contra hbc
  have hb : e b ∈ d.piece i := he ▸ mem_image_of_mem e hab.2.1
  have hc : e c ∈ d.piece i := he ▸ mem_image_of_mem e hac.2.1
  apply d.no_diameter_pair hprotected i hb hc
  rw [e.isometry.dist_eq]
  exact hfull.dist_sq_two_of_unit_partners hab hac hbc

end

end Puzzling139335.UnitPairs
