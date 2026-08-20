import ErdosProblems.Erdos957.Basic

open Set Metric

namespace Erdos957

noncomputable section

/-- A point of a set that is farthest from another point of the set is an extreme point of the
convex hull.  This is the convex-hull fact needed for endpoints of a diameter. -/
theorem farthestPoint_mem_extremePoints_convexHull
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : Set E) {x y : E} (hx : x ∈ A) (hxy : x ≠ y)
    (hfar : ∀ z ∈ A, dist z y ≤ dist x y) :
    x ∈ (convexHull ℝ A).extremePoints ℝ := by
  have hsub : convexHull ℝ A ⊆ closedBall y (dist x y) :=
    convexHull_min (fun z hz ↦ mem_closedBall.2 (hfar z hz)) (convex_closedBall _ _)
  have hxHull : x ∈ convexHull ℝ A := subset_convexHull ℝ A hx
  have hxSphere : x ∈ sphere y (dist x y) := mem_sphere.2 rfl
  have hxExtremeBall : x ∈ (closedBall y (dist x y)).extremePoints ℝ :=
    StrictConvexSpace.sphere_subset_extremePoints_closedBall y (dist_ne_zero.mpr hxy) hxSphere
  exact inter_extremePoints_subset_extremePoints_of_subset hsub ⟨hxHull, hxExtremeBall⟩

/-- Both endpoints of a diameter pair are extreme points of the convex hull. -/
theorem diameterPair_mem_extremePoints_convexHull
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : Set E) {x y : E} (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y)
    (hdiam : ∀ u ∈ A, ∀ v ∈ A, dist u v ≤ dist x y) :
    x ∈ (convexHull ℝ A).extremePoints ℝ ∧ y ∈ (convexHull ℝ A).extremePoints ℝ := by
  constructor
  · exact farthestPoint_mem_extremePoints_convexHull A hx hxy (fun z hz ↦ hdiam z hz y hy)
  · exact farthestPoint_mem_extremePoints_convexHull A hy hxy.symm fun z hz ↦ by
      simpa [dist_comm] using hdiam z hz x hx

/-- The vertices of the convex hull of a finite point set, represented as a finset. -/
def hullVertices {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : Finset E) : Finset E := by
  classical
  exact A.filter fun x ↦ x ∈ (convexHull ℝ (A : Set E)).extremePoints ℝ

@[simp]
theorem mem_hullVertices {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A : Finset E} {x : E} :
    x ∈ hullVertices A ↔ x ∈ (convexHull ℝ (A : Set E)).extremePoints ℝ := by
  classical
  constructor
  · exact fun hx ↦ (Finset.mem_filter.mp hx).2
  · intro hx
    exact Finset.mem_filter.mpr ⟨extremePoints_convexHull_subset hx, hx⟩

theorem hullVertices_subset {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : Finset E) : hullVertices A ⊆ A := by
  classical
  exact Finset.filter_subset _ _

theorem card_hullVertices_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : Finset E) : (hullVertices A).card ≤ A.card :=
  Finset.card_le_card (hullVertices_subset A)

/-- Points incident to a pair at distance `r`. -/
def distanceEndpoints {E : Type*} [PseudoMetricSpace E]
    (A : Finset E) (r : ℝ) : Finset E := by
  classical
  exact A.filter fun x ↦ ∃ y ∈ A, x ≠ y ∧ dist x y = r

@[simp]
theorem mem_distanceEndpoints {E : Type*} [PseudoMetricSpace E]
    {A : Finset E} {r : ℝ} {x : E} :
    x ∈ distanceEndpoints A r ↔
      x ∈ A ∧ ∃ y ∈ A, x ≠ y ∧ dist x y = r := by
  classical
  simp [distanceEndpoints]

/-- Endpoints of maximum-distance pairs are hull vertices. -/
theorem distanceEndpoints_subset_hullVertices
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : Finset E) (r : ℝ)
    (hmax : ∀ u ∈ A, ∀ v ∈ A, dist u v ≤ r) :
    distanceEndpoints A r ⊆ hullVertices A := by
  intro x hx
  obtain ⟨hxA, y, hyA, hxy, hdist⟩ := mem_distanceEndpoints.mp hx
  rw [mem_hullVertices]
  apply farthestPoint_mem_extremePoints_convexHull (A : Set E) hxA hxy
  intro z hzA
  simpa [hdist] using hmax z hzA y hyA

/-- Consequently the number of maximum-distance endpoints does not exceed the number of hull
vertices. -/
theorem card_distanceEndpoints_le_card_hullVertices
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : Finset E) (r : ℝ)
    (hmax : ∀ u ∈ A, ∀ v ∈ A, dist u v ≤ r) :
    (distanceEndpoints A r).card ≤ (hullVertices A).card :=
  Finset.card_le_card (distanceEndpoints_subset_hullVertices A r hmax)

end

end Erdos957

