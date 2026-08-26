import ErdosProblems.Erdos633b.DoubledRegions
import ErdosProblems.Erdos633b.DoubledVertices
import ErdosProblems.Erdos633b.DoubledSupportCoordinates

/-! Exact support identification for the four triangles in the five-piece partition. -/

namespace Erdos633b.DoubledPartition

theorem region_convex (T : Triangle) (u v r μ h : ℝ) (k : Piece) :
    Convex ℝ (region T u v r μ h k) := by
  have hl (a b c : ℝ) : Convex ℝ {p | T.coordForm a b p ≤ c} :=
    Convex.affine_preimage (T.coordForm a b) (convex_Iic c)
  have hg (a b c : ℝ) : Convex ℝ {p | c ≤ T.coordForm a b p} :=
    Convex.affine_preimage (T.coordForm a b) (convex_Ici c)
  cases k
  · exact T.support_convex.inter ((hg _ _ _).inter (hl _ _ _))
  · exact T.support_convex.inter ((hg _ _ _).inter (hg _ _ _))
  · exact T.support_convex.inter ((hl _ _ _).inter ((hl _ _ _).inter (hg _ _ _)))
  · exact T.support_convex.inter ((hl _ _ _).inter ((hl _ _ _).inter (hl _ _ _)))
  · exact T.support_convex.inter ((hl _ _ _).inter ((hg _ _ _).inter
      ((hl _ _ _).inter (hg _ _ _))))

theorem support_subset_region_of_vertices (T S : Triangle) (u v r μ h : ℝ) (k : Piece)
    (hv : ∀ i, S.points i ∈ region T u v r μ h k) : S.support ⊆ region T u v r μ h k := by
  apply convexHull_min
  · rintro p ⟨i, rfl⟩
    exact hv i
  · exact region_convex T u v r μ h k

namespace Layout

theorem abd_support (L : Layout) (T S : Triangle)
    (hx : ∀ i, T.coord 1 (S.points i) = ![0, 1, L.u] i)
    (hy : ∀ i, T.coord 2 (S.points i) = ![0, 0, L.v] i) :
    S.support = region T L.u L.v L.r L.μ L.height .abd := by
  apply Set.Subset.antisymm
  · apply support_subset_region_of_vertices
    intro i
    rw [mem_region, hx, hy]
    exact L.abd_vertices i
  · intro p hp
    have hx' : T.coord 1 p = S.coord 1 p + L.u * S.coord 2 p := by
      simpa [hx] using S.affine_scalar_interpolation (T.coord 1) p
    have hy' : T.coord 2 p = L.v * S.coord 2 p := by
      simpa [hy] using S.affine_scalar_interpolation (T.coord 2) p
    rw [Triangle.mem_support_iff_coords]
    apply L.abd_coords_nonneg
    have h := (mem_region T L.u L.v L.r L.μ L.height .abd p).mp hp
    rwa [hx', hy'] at h

theorem bdg_support (L : Layout) (T S : Triangle)
    (hx : ∀ i, T.coord 1 (S.points i) = ![1, L.u, 1 - L.r] i)
    (hy : ∀ i, T.coord 2 (S.points i) = ![0, L.v, L.r] i) :
    S.support = region T L.u L.v L.r L.μ L.height .bdg := by
  apply Set.Subset.antisymm
  · apply support_subset_region_of_vertices
    intro i
    rw [mem_region, hx, hy]
    exact L.bdg_vertices i
  · intro p hp
    have hx0 : T.coord 1 p = S.coord 0 p + L.u * S.coord 1 p +
        (1 - L.r) * S.coord 2 p := by
      simpa [hx] using S.affine_scalar_interpolation (T.coord 1) p
    have hx' : T.coord 1 p = 1 - (1 - L.u) * S.coord 1 p - L.r * S.coord 2 p := by
      linear_combination hx0 + S.coord_sum p
    have hy' : T.coord 2 p = L.v * S.coord 1 p + L.r * S.coord 2 p := by
      simpa [hy] using S.affine_scalar_interpolation (T.coord 2) p
    rw [Triangle.mem_support_iff_coords]
    apply L.bdg_coords_nonneg
    have h := (mem_region T L.u L.v L.r L.μ L.height .bdg p).mp hp
    rwa [hx', hy'] at h

theorem aef_support (L : Layout) (T S : Triangle)
    (hx : ∀ i, T.coord 1 (S.points i) = ![0, L.ε * L.u, 0] i)
    (hy : ∀ i, T.coord 2 (S.points i) = ![0, L.ε * L.v, L.μ] i) :
    S.support = region T L.u L.v L.r L.μ L.height .aef := by
  apply Set.Subset.antisymm
  · apply support_subset_region_of_vertices
    intro i
    rw [mem_region, hx, hy]
    exact L.aef_vertices i
  · intro p hp
    have hx' : T.coord 1 p = L.ε * L.u * S.coord 1 p := by
      simpa [hx] using S.affine_scalar_interpolation (T.coord 1) p
    have hy' : T.coord 2 p = L.ε * L.v * S.coord 1 p + L.μ * S.coord 2 p := by
      simpa [hy] using S.affine_scalar_interpolation (T.coord 2) p
    rw [Triangle.mem_support_iff_coords]
    apply L.aef_coords_nonneg
    have h := (mem_region T L.u L.v L.r L.μ L.height .aef p).mp hp
    rwa [hx', hy'] at h

theorem cfg_support (L : Layout) (T S : Triangle)
    (hx : ∀ i, T.coord 1 (S.points i) = ![0, 0, 1 - L.r] i)
    (hy : ∀ i, T.coord 2 (S.points i) = ![1, L.μ, L.r] i) :
    S.support = region T L.u L.v L.r L.μ L.height .cfg := by
  apply Set.Subset.antisymm
  · apply support_subset_region_of_vertices
    intro i
    rw [mem_region, hx, hy]
    exact L.cfg_vertices i
  · intro p hp
    have hx' : T.coord 1 p = (1 - L.r) * S.coord 2 p := by
      simpa [hx] using S.affine_scalar_interpolation (T.coord 1) p
    have hy0 : T.coord 2 p = S.coord 0 p + L.μ * S.coord 1 p + L.r * S.coord 2 p := by
      simpa [hy] using S.affine_scalar_interpolation (T.coord 2) p
    have hy' : T.coord 2 p = 1 - (1 - L.μ) * S.coord 1 p - (1 - L.r) * S.coord 2 p := by
      linear_combination hy0 + S.coord_sum p
    rw [Triangle.mem_support_iff_coords]
    apply L.cfg_coords_nonneg
    have h := (mem_region T L.u L.v L.r L.μ L.height .cfg p).mp hp
    rwa [hx', hy'] at h

end Layout
end Erdos633b.DoubledPartition
