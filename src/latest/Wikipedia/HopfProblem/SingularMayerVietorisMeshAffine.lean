import Wikipedia.HopfProblem.SingularMayerVietorisAffineSimplex
import Wikipedia.HopfProblem.SingularMayerVietorisMeshBarycenter
import Wikipedia.HopfProblem.SingularMayerVietorisMeshLebesgue

/-!
# Metric estimates for actual affine singular simplices

The normalized-vector-sum barycenter estimates apply to the actual
barycentric interpolation maps between standard simplices. In particular,
pairwise vertex bounds control the diameter of the entire affine image.
The actual compact-simplex Lebesgue lemma then makes sufficiently small
affine subsimplices subordinate to either member of a two-set open cover.
-/

noncomputable section

open Set Metric

namespace Wikipedia.HopfProblem.SingularMayerVietoris

open FirstHurewicz

variable {n p : ℕ}

/-- The actual simplex barycenter is the generic normalized vector sum in ambient coordinates. -/
theorem simplexBarycenter_eq_vertexBarycenter (v : Fin (n + 1) → Simplex p) :
    (simplexBarycenter v : Fin (p + 1) → ℝ) =
      vertexBarycenter (fun i => (v i : Fin (p + 1) → ℝ)) := by
  rw [simplexBarycenter_coe]
  simp only [vertexBarycenter, Nat.cast_add, Nat.cast_one, one_div]

/-- The entire actual affine image lies in the ambient convex hull of its vertices. -/
theorem affineSimplex_ambient_range_subset_convexHull (v : Fin (n + 1) → Simplex p) :
    range (fun t => (affineSimplex v t : Fin (p + 1) → ℝ)) ⊆
      convexHull ℝ (range fun i => (v i : Fin (p + 1) → ℝ)) := by
  rintro _ ⟨t, rfl⟩
  exact affineSimplex_mem_convexHull v t

/-- The sharp barycenter estimate in the actual standard-simplex metric. -/
theorem dist_simplexBarycenter_convexHull_le (v : Fin (n + 1) → Simplex p) {D : ℝ}
    (hpair : ∀ i j, dist (v i) (v j) ≤ D) {x : Simplex p}
    (hx : (x : Fin (p + 1) → ℝ) ∈
      convexHull ℝ (range fun i => (v i : Fin (p + 1) → ℝ))) :
    dist (simplexBarycenter v) x ≤ (n : ℝ) / ((n : ℝ) + 1) * D := by
  change dist (simplexBarycenter v : Fin (p + 1) → ℝ) (x : Fin (p + 1) → ℝ) ≤ _
  rw [simplexBarycenter_eq_vertexBarycenter]
  exact dist_vertexBarycenter_convexHull_le (fun i => (v i : Fin (p + 1) → ℝ)) hpair hx

/-- In particular, the sharp estimate applies to every actual affine image point. -/
theorem dist_simplexBarycenter_affineSimplex_le (v : Fin (n + 1) → Simplex p) {D : ℝ}
    (hpair : ∀ i j, dist (v i) (v j) ≤ D) (t : Simplex n) :
    dist (simplexBarycenter v) (affineSimplex v t) ≤
      (n : ℝ) / ((n : ℝ) + 1) * D :=
  dist_simplexBarycenter_convexHull_le v hpair (affineSimplex_mem_convexHull v t)

theorem dist_simplexBarycenter_vertex_le (v : Fin (n + 1) → Simplex p) {D : ℝ}
    (hpair : ∀ i j, dist (v i) (v j) ≤ D) (i : Fin (n + 1)) :
    dist (simplexBarycenter v) (v i) ≤ (n : ℝ) / ((n : ℝ) + 1) * D :=
  dist_simplexBarycenter_convexHull_le v hpair (subset_convexHull ℝ _ (mem_range_self i))

/-- Barycenters of nested vertex families satisfy the same actual metric estimate. -/
theorem dist_simplexBarycenter_simplexBarycenter_le {m : ℕ}
    (v : Fin (n + 1) → Simplex p) (w : Fin (m + 1) → Simplex p) {D : ℝ}
    (hpair : ∀ i j, dist (v i) (v j) ≤ D)
    (hw : ∀ i, (w i : Fin (p + 1) → ℝ) ∈
      convexHull ℝ (range fun j => (v j : Fin (p + 1) → ℝ))) :
    dist (simplexBarycenter v) (simplexBarycenter w) ≤
      (n : ℝ) / ((n : ℝ) + 1) * D := by
  apply dist_simplexBarycenter_convexHull_le v hpair
  exact affineSimplex_mem_of_convex w (convex_convexHull ℝ _) hw _

/-- A pairwise vertex bound controls every pair of actual affine image points. -/
theorem dist_affineSimplex_le (v : Fin (n + 1) → Simplex p) {D : ℝ}
    (hpair : ∀ i j, dist (v i) (v j) ≤ D) (t u : Simplex n) :
    dist (affineSimplex v t) (affineSimplex v u) ≤ D :=
  dist_convexHull_range_le (fun i => (v i : Fin (p + 1) → ℝ)) hpair
    (affineSimplex_mem_convexHull v t) (affineSimplex_mem_convexHull v u)

/-- The diameter is that of the full actual image, not only of its finite vertex set. -/
theorem affineSimplex_diam_le (v : Fin (n + 1) → Simplex p) {D : ℝ}
    (hpair : ∀ i j, dist (v i) (v j) ≤ D) : diam (range (affineSimplex v)) ≤ D := by
  apply diam_le_of_forall_dist_le_of_nonempty (range_nonempty (affineSimplex v))
  rintro _ ⟨t, rfl⟩ _ ⟨u, rfl⟩
  exact dist_affineSimplex_le v hpair t u

section OpenCover

variable {X : Type*} [TopologicalSpace X] {U V : Set X}

/-- Pairwise vertex mesh bounds imply genuine eventual smallness for all
affine subsimplices of a given actual singular simplex. -/
theorem simplex_eventually_small_of_vertices (σ : C(Simplex p, X))
    (hU : IsOpen U) (hV : IsOpen V) (hcover : range σ ⊆ U ∪ V) (D : ℝ) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ (m : ℕ) (v : Fin (m + 1) → Simplex p),
      (∀ i j, dist (v i) (v j) ≤ meshFactor p ^ k * D) →
        range (σ.comp (affineSimplex v)) ⊆ U ∨
          range (σ.comp (affineSimplex v)) ⊆ V := by
  obtain ⟨N, hN⟩ := simplex_eventually_small_of_diameter σ hU hV hcover D
  refine ⟨N, ?_⟩
  intro k hk m v hv
  exact hN k hk m (affineSimplex v) (affineSimplex_diam_le v hv)

/-- A uniform subdivision stage works for a finite family of actual
singular simplices, using only pairwise mesh bounds on affine vertices. -/
theorem finite_family_eventually_small_of_vertices (s : Finset C(Simplex p, X))
    (hU : IsOpen U) (hV : IsOpen V) (hcover : ∀ σ ∈ s, range σ ⊆ U ∪ V) (D : ℝ) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ σ ∈ s, ∀ (m : ℕ) (v : Fin (m + 1) → Simplex p),
      (∀ i j, dist (v i) (v j) ≤ meshFactor p ^ k * D) →
        range (σ.comp (affineSimplex v)) ⊆ U ∨
          range (σ.comp (affineSimplex v)) ⊆ V := by
  obtain ⟨N, hN⟩ := finite_family_eventually_small_of_diameter s hU hV hcover D
  refine ⟨N, ?_⟩
  intro k hk σ hσ m v hv
  exact hN k hk σ hσ m (affineSimplex v) (affineSimplex_diam_le v hv)

end OpenCover

end Wikipedia.HopfProblem.SingularMayerVietoris
