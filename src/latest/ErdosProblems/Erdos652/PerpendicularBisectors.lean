import ErdosProblems.Erdos652.Circles
import Util.IncidenceGeometry.CircleLineNoThreePoints
import Util.IncidenceGeometry.IsAffineLine
import Mathlib.Geometry.Euclidean.PerpBisector

open scoped Real
noncomputable section

namespace Erdos652

/-- The perpendicular bisector of two distinct points is an affine line in the
Euclidean plane. -/
lemma perpBisector_isAffineLine {x y : Point} (hxy : x ≠ y) :
    IsAffineLine (AffineSubspace.perpBisector x y) := by
  constructor
  · exact AffineSubspace.perpBisector_nonempty
  · have hfinrank : Fact (Module.finrank ℝ Point = 2) := ⟨by simp [Point]⟩
    have hv : (y -ᵥ x : Point) ≠ 0 := vsub_ne_zero.mpr hxy.symm
    rw [AffineSubspace.direction_perpBisector]
    exact Submodule.finrank_orthogonal_span_singleton
      (𝕜 := ℝ) (E := Point) (n := 1) hv

/-- A continuous simple arc from `x` to `y` contains, away from its endpoints,
a point equidistant from `x` and `y`. -/
lemma path_meets_perpBisector_interior
    {x y : Point} (hxy : x ≠ y)
    (γ : Set.Icc (0 : ℝ) 1 → Point)
    (hγ : Continuous γ)
    (hstart : γ ⟨0, by simp⟩ = x)
    (hend : γ ⟨1, by simp⟩ = y) :
    ∃ u : {u : ℝ // 0 < u ∧ u < 1},
      γ ⟨u.1, ⟨le_of_lt u.2.1, le_of_lt u.2.2⟩⟩ ∈
        AffineSubspace.perpBisector x y := by
  let f : Set.Icc (0 : ℝ) 1 → ℝ := fun u => dist (γ u) x - dist (γ u) y
  have hf : Continuous f :=
    (hγ.dist continuous_const).sub (hγ.dist continuous_const)
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hf0 : f ⟨0, by simp⟩ = -dist x y := by
    change dist (γ ⟨0, by simp⟩) x - dist (γ ⟨0, by simp⟩) y = _
    rw [hstart]
    simp
  have hf1 : f ⟨1, by simp⟩ = dist x y := by
    change dist (γ ⟨1, by simp⟩) x - dist (γ ⟨1, by simp⟩) y = _
    rw [hend]
    simp [dist_comm]
  have hz : (0 : ℝ) ∈ Set.Icc (f ⟨0, by simp⟩) (f ⟨1, by simp⟩) := by
    rw [hf0, hf1]
    exact ⟨le_of_lt (neg_lt_zero.mpr hd), le_of_lt hd⟩
  rcases (intermediate_value_univ (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1)
      (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) hf hz) with ⟨u, hfu⟩
  have hu0 : 0 < u.1 := by
    refine lt_of_le_of_ne u.2.1 ?_
    intro hu
    have hueq : u = (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) := Subtype.ext hu.symm
    subst u
    rw [hf0] at hfu
    linarith
  have hu1 : u.1 < 1 := by
    refine lt_of_le_of_ne u.2.2 ?_
    intro hu
    have hueq : u = (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) := Subtype.ext hu
    subst u
    rw [hf1] at hfu
    linarith
  refine ⟨⟨u.1, hu0, hu1⟩, AffineSubspace.mem_perpBisector_iff_dist_eq.mpr ?_⟩
  have : f u = 0 := by simpa using hfu
  dsimp [f] at this
  linarith

/-- Three pairwise distinct points on one affine line cannot all lie on the
same Euclidean circle.  This is the coordinate-free wrapper needed below. -/
lemma affineLine_circle_no_three
    {ℓ : AffineSubspace ℝ Point} (hℓ : IsAffineLine ℓ)
    {c u v w : Point} {r : ℝ}
    (hu : u ∈ ℓ) (hv : v ∈ ℓ) (hw : w ∈ ℓ)
    (hdu : dist u c = r) (hdv : dist v c = r) (hdw : dist w c = r)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) : False := by
  have hline_le : affineSpan ℝ ({u, v} : Set Point) ≤ ℓ :=
    affineSpan_le.mpr (by
      intro z hz
      rcases hz with (rfl | hz)
      · exact hu
      · simpa only [Set.mem_singleton_iff] using hz ▸ hv)
  have hrank : Module.finrank ℝ
      (affineSpan ℝ ({u, v} : Set Point)).direction = 1 := by
    rw [direction_affineSpan, vectorSpan_pair]
    exact finrank_span_singleton (vsub_ne_zero.mpr huv)
  have hdir : (affineSpan ℝ ({u, v} : Set Point)).direction = ℓ.direction :=
    Submodule.eq_of_le_of_finrank_eq
      (AffineSubspace.direction_le hline_le) (hrank.trans hℓ.2.symm)
  have heq : affineSpan ℝ ({u, v} : Set Point) = ℓ :=
    AffineSubspace.ext_of_direction_eq hdir ⟨u,
      subset_affineSpan ℝ _ (by simp), hu⟩
  have hwline : w ∈ line[ℝ, u, v] := by
    rwa [heq]
  exact CircleLineNoThreePoints huv
    (subset_affineSpan ℝ _ (by simp))
    (subset_affineSpan ℝ _ (by simp)) hwline
    hdu hdv hdw huv huw hvw

end Erdos652
