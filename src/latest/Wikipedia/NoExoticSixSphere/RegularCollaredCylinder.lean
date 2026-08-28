import Wikipedia.NoExoticSixSphere.CylinderFiberSlab
import Wikipedia.NoExoticSixSphere.RegularFiberManifold

/-!
# Data for a regular cylinder with constant ends

This bundles an actual smooth map, regularity of its specified fiber, its
regular endpoint maps, and exact time-constant end neighborhoods. Existence
of such data for an arbitrary homotopy is not assumed or asserted here.
The bounded fiber slab has a concrete three-piece open cover.
-/

open scoped Manifold ContDiff
open Set Module TopologicalSpace

namespace NoExoticSixSphere

variable {B H M C H' N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  (I : ModelWithCorners ℝ B H) [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  (J : ModelWithCorners ℝ C H') [TopologicalSpace N] [ChartedSpace H' N]

structure RegularCollaredCylinder (b : N) (s t : ℝ) where
  map : C(ℝ × M, N)
  leftMap : C(M, N)
  rightMap : C(M, N)
  smooth_map : ContMDiff ((𝓘(ℝ, ℝ)).prod I) J ∞ map
  smooth_left : ContMDiff I J ∞ leftMap
  smooth_right : ContMDiff I J ∞ rightMap
  regular_map : ∀ p, map p = b → Function.Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod I) J map p)
  regular_left : ∀ x, leftMap x = b → Function.Surjective (mfderiv I J leftMap x)
  regular_right : ∀ x, rightMap x = b → Function.Surjective (mfderiv I J rightMap x)
  time_lt : s < t
  leftTimes : Opens ℝ
  rightTimes : Opens ℝ
  left_mem : s ∈ leftTimes
  right_mem : t ∈ rightTimes
  left_eq : ∀ r ∈ leftTimes, ∀ x, map (r, x) = leftMap x
  right_eq : ∀ r ∈ rightTimes, ∀ x, map (r, x) = rightMap x

namespace RegularCollaredCylinder

inductive Piece
  | left
  | middle
  | right

variable {I J} {b : N} {s t : ℝ} (d : RegularCollaredCylinder (M := M) I J b s t)

def pieceDomain : Piece → Opens (CylinderFiberSlab.slab d.map b s t)
  | .left => CylinderFiberSlab.timeDomain d.map b s t d.leftTimes
  | .middle => CylinderFiberSlab.timeDomain d.map b s t ⟨Ioo s t, isOpen_Ioo⟩
  | .right => CylinderFiberSlab.timeDomain d.map b s t d.rightTimes

theorem pieceDomain_covers (p : CylinderFiberSlab.slab d.map b s t) :
    ∃ i, p ∈ d.pieceDomain i := by
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc p.property with hs | ht | hi
  · refine ⟨.left, ?_⟩
    change p.val.val.1 ∈ d.leftTimes
    rw [hs]
    exact d.left_mem
  · refine ⟨.right, ?_⟩
    change p.val.val.1 ∈ d.rightTimes
    rw [ht]
    exact d.right_mem
  · exact ⟨.middle, hi⟩

end RegularCollaredCylinder

theorem cylinder_finrank_eq {B C : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C]
    {k : ℕ} (hd : finrank ℝ B = finrank ℝ C + k) :
    finrank ℝ (ℝ × B) = finrank ℝ C + (k + 1) := by
  rw [finrank_prod, finrank_self, hd]
  omega

end NoExoticSixSphere
