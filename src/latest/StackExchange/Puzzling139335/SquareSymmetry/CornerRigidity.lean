import StackExchange.Puzzling139335.SquareSymmetry.Basic
import StackExchange.Puzzling139335.PlaneIsometries

/-!
# A square corner determines the surrounding square

If a Euclidean congruence takes a full relative neighborhood of a square
corner into the square and takes the corner itself to a square corner,
then it is a symmetry of the square.  The neighborhood assumption is
about actual sets, not their convex hulls.
-/

open Set Metric

namespace Puzzling139335.SquareSymmetry

open PlaneIsometries

noncomputable section

private theorem axis_points_near_origin {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧
      (!₂[t, 0] : Plane) ∈ ball 0 ε ∩ unitSquare ∧
      (!₂[0, t] : Plane) ∈ ball 0 ε ∩ unitSquare := by
  let t := min (ε / 2) (1 / 2 : ℝ)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht1 : t ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  have hx : dist (!₂[t, 0] : Plane) 0 = t := by
    apply (sq_eq_sq₀ dist_nonneg ht.le).mp
    rw [plane_dist_sq]
    simp
  have hy : dist (!₂[0, t] : Plane) 0 = t := by
    apply (sq_eq_sq₀ dist_nonneg ht.le).mp
    rw [plane_dist_sq]
    simp
  refine ⟨t, ht, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact mem_ball.mpr (by rw [hx]; exact htε)
  · simpa [unitSquare] using And.intro ht.le ht1
  · exact mem_ball.mpr (by rw [hy]; exact htε)
  · simpa [unitSquare] using And.intro ht.le ht1

/-- At the origin, the two short positive coordinate rays force the
linear part to be either the identity or coordinate interchange. -/
theorem coordinate_form_of_origin_neighborhood
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0)
    {ε : ℝ} (hε : 0 < ε)
    (he : e '' (ball 0 ε ∩ unitSquare) ⊆ unitSquare) :
    (∀ p, e p = p) ∨ (∀ p, e p = !₂[p 1, p 0]) := by
  obtain ⟨t, ht, hx, hy⟩ := axis_points_near_origin hε
  have hex := he (mem_image_of_mem e hx)
  have hey := he (mem_image_of_mem e hy)
  obtain ⟨c, s, hcs, hform | hform⟩ := affine_coordinate_classification e
  · rw [hform _] at hex hey
    norm_num [directCoordinates, unitSquare, he0] at hex hey
    have hs : s = 0 := by
      have hpos : 0 ≤ s := nonneg_of_mul_nonneg_left hex.2.1 ht
      have hneg : s ≤ 0 := by nlinarith [hey.1.1]
      linarith
    have hc : c = 1 := by
      have hpos : 0 ≤ c := nonneg_of_mul_nonneg_left hex.1.1 ht
      nlinarith [hcs]
    have heid (p : Plane) : e p = p := by
      rw [hform p]
      ext i
      fin_cases i <;> simp [directCoordinates, he0, hc, hs]
    exact Or.inl heid
  · rw [hform _] at hex hey
    norm_num [reversingCoordinates, unitSquare, he0] at hex hey
    have hc : c = 0 := by
      have hpos : 0 ≤ c := nonneg_of_mul_nonneg_left hex.1.1 ht
      have hneg : c ≤ 0 := by nlinarith [hey.2.1]
      linarith
    have hs : s = 1 := by
      have hpos : 0 ≤ s := nonneg_of_mul_nonneg_left hex.2.1 ht
      nlinarith [hcs]
    have heswap (p : Plane) : e p = !₂[p 1, p 0] := by
      rw [hform p]
      ext i
      fin_cases i <;> simp [reversingCoordinates, he0, hc, hs]
    exact Or.inr heswap

/-- The normalized local condition therefore preserves the whole square. -/
theorem preserves_square_of_origin_neighborhood
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0)
    {ε : ℝ} (hε : 0 < ε)
    (he : e '' (ball 0 ε ∩ unitSquare) ⊆ unitSquare) :
    e '' unitSquare = unitSquare := by
  rcases coordinate_form_of_origin_neighborhood e he0 hε he with heid | heswap
  · simp only [heid, Set.image_id']
  · ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa [heswap, unitSquare] using And.intro hq.2 hq.1
    · intro hp
      refine ⟨!₂[p 1, p 0], ?_, ?_⟩
      · simpa [unitSquare] using And.intro hp.2 hp.1
      · rw [heswap]
        ext i
        fin_cases i <;> rfl

/-- A congruence taking an actual full square-corner neighborhood into a
square corner preserves the whole square. -/
theorem preserves_square_of_corner_neighborhood
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b : Fin 4)
    (hab : e (corner a) = corner b) {ε : ℝ} (hε : 0 < ε)
    (he : e '' (ball (corner a) ε ∩ unitSquare) ⊆ unitSquare) :
    e '' unitSquare = unitSquare := by
  let g := ((cornerFlip a).trans e).trans (cornerFlip b)
  have hg0 : g 0 = 0 := by
    change cornerFlip b (e (cornerFlip a 0)) = 0
    rw [cornerFlip_zero, hab, cornerFlip_corner]
  have hg : g '' (ball 0 ε ∩ unitSquare) ⊆ unitSquare := by
    rintro _ ⟨p, hp, rfl⟩
    apply (cornerFlip_mem_unitSquare b).mpr
    apply he
    refine ⟨cornerFlip a p, ⟨?_, (cornerFlip_mem_unitSquare a).mpr hp.2⟩, rfl⟩
    have hd : dist (cornerFlip a p) (corner a) = dist p 0 := by
      rw [← cornerFlip_zero a]
      exact (cornerFlip a).isometry.dist_eq p 0
    exact mem_ball.mpr (hd ▸ mem_ball.mp hp.1)
  have hgs := preserves_square_of_origin_neighborhood g hg0 hε hg
  have himage : cornerFlip b '' (e '' unitSquare) = unitSquare := by
    calc
      cornerFlip b '' (e '' unitSquare) =
          cornerFlip b '' (e '' (cornerFlip a '' unitSquare)) := by
            rw [cornerFlip_image_unitSquare]
      _ = g '' unitSquare := by simp [g, Set.image_image, Function.comp_def]
      _ = unitSquare := hgs
  calc
    e '' unitSquare = cornerFlip b '' (cornerFlip b '' (e '' unitSquare)) := by
      rw [Set.image_image]
      simp only [cornerFlip_involutive, Set.image_id']
    _ = cornerFlip b '' unitSquare := by rw [himage]
    _ = unitSquare := cornerFlip_image_unitSquare b

/-- The same local hypothesis fixes the square center. -/
theorem center_fixed_of_corner_neighborhood
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b : Fin 4)
    (hab : e (corner a) = corner b) {ε : ℝ} (hε : 0 < ε)
    (he : e '' (ball (corner a) ε ∩ unitSquare) ⊆ unitSquare) :
    e squareCenter = squareCenter :=
  center_fixed_of_preserves_square e
    (preserves_square_of_corner_neighborhood e a b hab hε he)

end

end Puzzling139335.SquareSymmetry
