import ErdosProblems.Erdos633b.DoubledSupports
import ErdosProblems.Erdos633b.DoubledTrapezoidCoordinates
import ErdosProblems.Erdos633b.TrapezoidConvex
import ErdosProblems.Erdos633b.TrapezoidBarycentric

/-! Four proved rigid vertex placements identify the entire closed trapezoid region. -/

namespace Erdos633b.DoubledPartition.Layout

theorem trapezoid_support_of_vertices (L : Layout) (T : Triangle)
    (d : ℝ) (hd : 0 < d) (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (g : Plane ≃ᵃⁱ[ℝ] Plane)
    (hscale : delta L.u L.v L.r * (x + y) = L.u * L.μ * x)
    (hxs : ∀ i : Fin 4, T.coord 1
      (g (![Sixty.point d 0 0, Sixty.point d (x + y) 0, Sixty.point d x y, Sixty.point d 0 y] i)) =
        ![0, L.ε * L.u, L.u, 1 - L.r] i)
    (hys : ∀ i : Fin 4, T.coord 2
      (g (![Sixty.point d 0 0, Sixty.point d (x + y) 0, Sixty.point d x y, Sixty.point d 0 y] i)) =
        ![L.μ, L.ε * L.v, L.v, L.r] i) :
    g '' TrapezoidPartition.trapezoidSet (Sixty.frame d hd) x y =
      region T L.u L.v L.r L.μ L.height .trapezoid := by
  have hvert (i : Fin 4) :
      g (![Sixty.point d 0 0, Sixty.point d (x + y) 0, Sixty.point d x y, Sixty.point d 0 y] i) ∈
        region T L.u L.v L.r L.μ L.height .trapezoid := by
    rw [mem_region, hxs, hys]
    exact L.trapezoid_vertices i
  have hpre : TrapezoidPartition.trapezoidSet (Sixty.frame d hd) x y ⊆
      g ⁻¹' region T L.u L.v L.r L.μ L.height .trapezoid :=
    Sixty.trapezoid_subset_convex d hd x y hx hy _
      (Convex.affine_preimage g.toAffineMap (region_convex T L.u L.v L.r L.μ L.height .trapezoid))
      (hvert 0) (hvert 1) (hvert 2) (hvert 3)
  let U := Sixty.cornerTriangle d hd (x + y) y (add_pos hx hy) hy
  have hX (z : Plane) : T.coord 1 (g z) =
      L.ε * L.u * U.coord 1 z + (1 - L.r) * U.coord 2 z := by
    have h0 : T.coord 1 (g (U.points 0)) = 0 := hxs 0
    have h1 : T.coord 1 (g (U.points 1)) = L.ε * L.u := hxs 1
    have h2 : T.coord 1 (g (U.points 2)) = 1 - L.r := hxs 3
    have hh := U.affine_scalar_interpolation ((T.coord 1).comp g.toAffineMap) z
    change T.coord 1 (g z) = T.coord 1 (g (U.points 0)) * U.coord 0 z +
      T.coord 1 (g (U.points 1)) * U.coord 1 z + T.coord 1 (g (U.points 2)) * U.coord 2 z at hh
    simpa only [h0, h1, h2, zero_mul, zero_add] using hh
  have hY (z : Plane) : T.coord 2 (g z) =
      L.μ + (L.ε * L.v - L.μ) * U.coord 1 z + (L.r - L.μ) * U.coord 2 z := by
    have h0 : T.coord 2 (g (U.points 0)) = L.μ := hys 0
    have h1 : T.coord 2 (g (U.points 1)) = L.ε * L.v := hys 1
    have h2 : T.coord 2 (g (U.points 2)) = L.r := hys 3
    have hh := U.affine_scalar_interpolation ((T.coord 2).comp g.toAffineMap) z
    change T.coord 2 (g z) = T.coord 2 (g (U.points 0)) * U.coord 0 z +
      T.coord 2 (g (U.points 1)) * U.coord 1 z + T.coord 2 (g (U.points 2)) * U.coord 2 z at hh
    rw [h0, h1, h2] at hh
    linear_combination hh + L.μ * U.coord_sum z
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hpre hz
  · intro hp
    refine ⟨g.symm p, ?_, g.apply_symm_apply p⟩
    have hm := Sixty.mem_trapezoid_iff_corner_coords d hd x y hx hy (g.symm p)
    dsimp only at hm
    rw [hm]
    apply L.trapezoid_coords_nonneg x y _ _ hx hy hscale
    have hp' : g (g.symm p) ∈ region T L.u L.v L.r L.μ L.height .trapezoid := by
      simpa only [g.apply_symm_apply] using hp
    have hh := (mem_region T L.u L.v L.r L.μ L.height .trapezoid (g (g.symm p))).mp hp'
    rw [hX, hY] at hh
    exact hh.2

end Erdos633b.DoubledPartition.Layout
