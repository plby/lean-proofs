import Wikipedia.HopfProblem.SingularMayerVietorisFormalChainsSupport
import Wikipedia.HopfProblem.SingularMayerVietorisMeshAffine

/-!
# The actual mesh bound for iterated barycentric subdivision

Every nonzero simplex in the recursive cone subdivision has its vertices
in the original convex hull. Its pairwise vertex distances contract by
`n/(n+1)` in geometric degree `n`. The proof follows the actual finite
chain support: a cone term comes from a subdivided face, and its new apex
is the actual barycenter.

Iterating gives the geometric mesh bound on every nonzero simplex.
Together with the compact-simplex Lebesgue lemma this proves eventual
open-cover smallness, uniformly over finite singular-chain supports,
without assuming a mesh estimate or a Lebesgue-number conclusion.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SingularMayerVietoris

open FirstHurewicz

section Coordinates

variable {V E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
variable (center : FormalCenter V) (coords : V → E)
variable (hcenter : ∀ n (v : Fin (n + 1) → V),
  coords (center n v) = vertexBarycenter (coords ∘ v))

include hcenter

/-- The chosen centers preserve every convex set in ambient coordinates. -/
theorem formalCenter_mem_of_convex {S : Set E} (hS : Convex ℝ S)
    (n : ℕ) (v : Fin (n + 1) → V) (hv : ∀ i, coords (v i) ∈ S) :
    coords (center n v) ∈ S := by
  rw [hcenter]
  exact vertexBarycenter_mem_of_convex (coords ∘ v) hS hv

/-- Every vertex of every actual nonzero subdivision term lies in the
ambient convex hull of the original vertex list. -/
theorem formalSubdivision_simplex_vertices_mem_convexHull {n : ℕ}
    (v : Fin n → V) {w : Fin n → V}
    (hw : w ∈ (formalSubdivision center n (formalSimplex v)).support) (i : Fin n) :
    coords (w i) ∈ convexHull ℝ (range (coords ∘ v)) := by
  let S : Set V := coords ⁻¹' convexHull ℝ (range (coords ∘ v))
  have hv : formalSimplex v ∈ formalChainsSupported S n := by
    apply formalSimplex_mem_supported
    intro j
    exact subset_convexHull ℝ _ (mem_range_self j)
  have hS : ∀ k (u : Fin (k + 1) → V), (∀ j, u j ∈ S) → center k u ∈ S := by
    intro k u hu
    exact formalCenter_mem_of_convex center coords hcenter (convex_convexHull ℝ _) k u hu
  have hsub := formalSubdivision_mem_supported center hS n hv
  exact (mem_formalChainsSupported_iff.mp hsub) w hw i

/-- One actual subdivision contracts every supported simplex by the
sharp dimension-dependent factor. -/
theorem formalSubdivision_simplex_mesh (n : ℕ) :
    ∀ (v : Fin (n + 1) → V) {D : ℝ},
      (∀ i j, dist (coords (v i)) (coords (v j)) ≤ D) →
      ∀ {w : Fin (n + 1) → V},
        w ∈ (formalSubdivision center (n + 1) (formalSimplex v)).support →
        ∀ i j, dist (coords (w i)) (coords (w j)) ≤ meshFactor n * D := by
  induction n with
  | zero =>
    intro v D hpair w hw i j
    let : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp [meshFactor]
  | succ n ih =>
    intro v D hpair w hw
    have hD : 0 ≤ D := by simpa only [dist_self] using hpair 0 0
    have hHull := formalSubdivision_simplex_vertices_mem_convexHull center coords hcenter v hw
    rw [formalSubdivision_simplex_succ] at hw
    obtain ⟨u, hu, rfl⟩ := formalCone_support_exists (center (n + 1) v) hw
    obtain ⟨face, hface, hu⟩ :=
      formalLinearMap_support_exists (formalSubdivision center (n + 1)) hu
    obtain ⟨r, rfl⟩ := formalBoundary_support_exists (n + 1) v hface
    have huMesh := ih (v ∘ r.succAbove) (fun i j => hpair (r.succAbove i) (r.succAbove j)) hu
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa only [Fin.cons_zero, dist_self] using
          mul_nonneg (meshFactor_nonneg (n + 1)) hD
      · change dist (coords (center (n + 1) v)) (coords (u j)) ≤ meshFactor (n + 1) * D
        rw [hcenter]
        exact dist_vertexBarycenter_convexHull_le (coords ∘ v) hpair (hHull j.succ)
    · refine Fin.cases ?_ (fun j => ?_) j
      · change dist (coords (u i)) (coords (center (n + 1) v)) ≤ meshFactor (n + 1) * D
        rw [dist_comm, hcenter]
        exact dist_vertexBarycenter_convexHull_le (coords ∘ v) hpair (hHull i.succ)
      · change dist (coords (u i)) (coords (u j)) ≤ meshFactor (n + 1) * D
        exact (huMesh i j).trans
          (mul_le_mul_of_nonneg_right (meshFactor_mono (Nat.le_succ n)) hD)

/-- Linear extension cannot introduce a support simplex not present in
the subdivision of some actual input generator. -/
theorem formalSubdivision_mesh (n : ℕ) (c : FormalChains V (n + 1)) {D : ℝ}
    (hc : ∀ v ∈ c.support, ∀ i j, dist (coords (v i)) (coords (v j)) ≤ D) :
    ∀ w ∈ (formalSubdivision center (n + 1) c).support,
      ∀ i j, dist (coords (w i)) (coords (w j)) ≤ meshFactor n * D := by
  intro w hw
  obtain ⟨v, hv, hw⟩ := formalLinearMap_support_exists (formalSubdivision center (n + 1)) hw
  exact formalSubdivision_simplex_mesh center coords hcenter n v (hc v hv) hw

/-- The actual `k`th subdivision has the `k`th geometric-power mesh bound
on every simplex with nonzero coefficient. -/
theorem formalSubdivision_iterate_mesh (n k : ℕ) (c : FormalChains V (n + 1)) {D : ℝ}
    (hc : ∀ v ∈ c.support, ∀ i j, dist (coords (v i)) (coords (v j)) ≤ D) :
    ∀ w ∈ ((formalSubdivision center (n + 1))^[k] c).support,
      ∀ i j, dist (coords (w i)) (coords (w j)) ≤ meshFactor n ^ k * D := by
  induction k with
  | zero => simpa only [Function.iterate_zero_apply, pow_zero, one_mul] using hc
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    intro w hw i j
    have h := formalSubdivision_mesh center coords hcenter n
      ((formalSubdivision center (n + 1))^[k] c) ih w hw i j
    simpa only [pow_succ, mul_assoc, mul_left_comm] using h

end Coordinates

section Simplex

variable {p n : ℕ}

/-- The actual standard-simplex sup metric has diameter at most one. -/
theorem simplex_dist_le_one (x y : Simplex p) : dist x y ≤ 1 :=
  (Metric.dist_le_diam_of_mem (bounded_stdSimplex (Fin (p + 1))) x.property y.property).trans
    diam_stdSimplex_le

/-- On actual standard-simplex vertices the normalized-center condition
holds by the proved barycentric interpolation formula. The initial mesh
is at most one for every formal chain in that simplex. -/
theorem simplex_formalSubdivision_iterate_mesh (k : ℕ)
    (c : FormalChains (Simplex p) (n + 1)) :
    ∀ w ∈ ((formalSubdivision (fun _ v => simplexBarycenter v) (n + 1))^[k] c).support,
      ∀ i j, dist (w i) (w j) ≤ meshFactor n ^ k := by
  have h := formalSubdivision_iterate_mesh
    (fun n (v : Fin (n + 1) → Simplex p) => simplexBarycenter v)
    (fun x : Simplex p => (x : Fin (p + 1) → ℝ))
    (fun _ v => simplexBarycenter_eq_vertexBarycenter v) n k c
    (D := 1) (fun v _ i j => simplex_dist_le_one (v i) (v j))
  intro w hw i j
  change dist (w i : Fin (p + 1) → ℝ) (w j : Fin (p + 1) → ℝ) ≤ meshFactor n ^ k
  simpa only [mul_one] using h w hw i j

/-- The whole affine image of every actual iterated subdivision term
obeys the geometric mesh bound, not merely its list of vertices. -/
theorem simplex_formalSubdivision_iterate_diam (k : ℕ)
    (c : FormalChains (Simplex p) (n + 1)) (w : Fin (n + 1) → Simplex p)
    (hw : w ∈ ((formalSubdivision (fun _ v => simplexBarycenter v) (n + 1))^[k] c).support) :
    Metric.diam (range (affineSimplex w)) ≤ meshFactor n ^ k :=
  affineSimplex_diam_le w (simplex_formalSubdivision_iterate_mesh k c w hw)

variable {X : Type*} [TopologicalSpace X] {U V : Set X}

/-- Sufficiently many actual subdivisions make every term lie over one
member of the open cover. There is no remaining mesh assumption. -/
theorem simplex_formalSubdivision_eventually_small (σ : C(Simplex p, X))
    (hU : IsOpen U) (hV : IsOpen V) (hcover : range σ ⊆ U ∪ V) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ c : FormalChains (Simplex p) (p + 1),
      ∀ w ∈ ((formalSubdivision (fun _ v => simplexBarycenter v) (p + 1))^[k] c).support,
        range (σ.comp (affineSimplex w)) ⊆ U ∨
          range (σ.comp (affineSimplex w)) ⊆ V := by
  obtain ⟨N, hN⟩ := simplex_eventually_small_of_vertices σ hU hV hcover 1
  refine ⟨N, ?_⟩
  intro k hk c w hw
  apply hN k hk p w
  simpa only [mul_one] using simplex_formalSubdivision_iterate_mesh k c w hw

/-- One stage works for a finite family of singular simplices and all
later iterations of every formal chain in their standard simplex. -/
theorem finite_family_formalSubdivision_eventually_small (s : Finset C(Simplex p, X))
    (hU : IsOpen U) (hV : IsOpen V) (hcover : ∀ σ ∈ s, range σ ⊆ U ∪ V) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ σ ∈ s, ∀ c : FormalChains (Simplex p) (p + 1),
      ∀ w ∈ ((formalSubdivision (fun _ v => simplexBarycenter v) (p + 1))^[k] c).support,
        range (σ.comp (affineSimplex w)) ⊆ U ∨
          range (σ.comp (affineSimplex w)) ⊆ V := by
  obtain ⟨N, hN⟩ := finite_family_eventually_small_of_vertices s hU hV hcover 1
  refine ⟨N, ?_⟩
  intro k hk σ hσ c w hw
  apply hN k hk σ hσ p w
  simpa only [mul_one] using simplex_formalSubdivision_iterate_mesh k c w hw

end Simplex

end Wikipedia.HopfProblem.SingularMayerVietoris
