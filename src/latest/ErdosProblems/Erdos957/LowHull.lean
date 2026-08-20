import ErdosProblems.Erdos957.Angle
import ErdosProblems.Erdos957.Diameter

/-!
# The degenerate-hull branch of Erdős 957

If a normalized one-separated planar configuration has at most two convex-hull
vertices, its maximum-distance multiplicity is at most two.  The planar
kissing-number bound gives at most six unit neighbours at every point, hence
at most `3 * |A|` unit-distance pairs.  Their product is therefore at most
`6 * |A|`.
-/

open Metric
open scoped BigOperators EuclideanGeometry RealInnerProductSpace SimpleGraph

namespace Erdos957LowHull

noncomputable section

abbrev Point := Erdos957.Point

/-- The standard real-linear isometry between `ℂ` and Mathlib's Euclidean plane. -/
def complexPlaneEquiv : ℂ ≃ₗᵢ[ℝ] Point :=
  Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)

/-- Pull a planar finset back to `ℂ`, where the checked six-neighbour theorem lives. -/
def complexPreimage (A : Finset Point) : Finset ℂ :=
  A.map complexPlaneEquiv.symm.toEmbedding

@[simp]
lemma mem_complexPreimage {A : Finset Point} {z : ℂ} :
    z ∈ complexPreimage A ↔ complexPlaneEquiv z ∈ A := by
  constructor
  · intro hz
    obtain ⟨p, hp, hpz⟩ := Finset.mem_map.mp hz
    have hzp : z = complexPlaneEquiv.symm p := hpz.symm
    rw [hzp, complexPlaneEquiv.apply_symm_apply]
    exact hp
  · intro hz
    exact Finset.mem_map.mpr
      ⟨complexPlaneEquiv z, hz, complexPlaneEquiv.symm_apply_apply z⟩

/-- One-separation is preserved by the complex/Euclidean-plane isometry. -/
lemma complexPreimage_oneSeparated {A : Finset Point}
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ dist x y) :
    Erdos957Angle.IsOneSeparated (complexPreimage A) := by
  intro x hx y hy hxy
  have hxA : complexPlaneEquiv x ∈ A := mem_complexPreimage.mp hx
  have hyA : complexPlaneEquiv y ∈ A := mem_complexPreimage.mp hy
  have hxyA : complexPlaneEquiv x ≠ complexPlaneEquiv y :=
    complexPlaneEquiv.injective.ne hxy
  simpa using hsep (complexPlaneEquiv x) hxA (complexPlaneEquiv y) hyA hxyA

/-- The degree in the public unit-distance graph is the cardinality of the
corresponding complex unit-neighbour finset. -/
lemma degree_eq_complex_unitNeighbors (A : Finset Point) (p : {x // x ∈ A}) :
    (Erdos957.distanceGraph A 1).degree p =
      (Erdos957Angle.unitNeighbors (complexPreimage A)
        (complexPlaneEquiv.symm p)).card := by
  classical
  rw [SimpleGraph.degree]
  apply Finset.card_bij
    (s := (Erdos957.distanceGraph A 1).neighborFinset p)
    (t := Erdos957Angle.unitNeighbors (complexPreimage A)
      (complexPlaneEquiv.symm p))
    (fun (q : {x // x ∈ A}) _ ↦ complexPlaneEquiv.symm q)
  · intro q hq
    have hadj : (Erdos957.distanceGraph A 1).Adj p q :=
      (SimpleGraph.mem_neighborFinset (G := Erdos957.distanceGraph A 1)
        (v := p) q).mp hq
    have hqB : complexPlaneEquiv.symm (q : Point) ∈ complexPreimage A := by
      exact Finset.mem_map.mpr ⟨q, q.property, rfl⟩
    have hdist : dist (complexPlaneEquiv.symm (p : Point))
        (complexPlaneEquiv.symm (q : Point)) = 1 := by
      simpa using hadj.2
    exact Finset.mem_filter.mpr ⟨hqB, hdist⟩
  · intro q _ r _ hqr
    apply Subtype.ext
    exact complexPlaneEquiv.symm.injective hqr
  · intro z hz
    have hzB : z ∈ complexPreimage A := (Finset.mem_filter.mp hz).1
    have hdist : dist (complexPlaneEquiv.symm (p : Point)) z = 1 :=
      (Finset.mem_filter.mp hz).2
    obtain ⟨q, hqA, hqz⟩ := Finset.mem_map.mp hzB
    have hdist' : dist (p : Point) q = 1 := by
      rw [← hqz] at hdist
      simpa using hdist
    let qs : {x // x ∈ A} := ⟨q, hqA⟩
    have hpq : p ≠ qs := by
      intro hpq
      have : dist (p : Point) q = 0 := by
        rw [show q = (p : Point) by exact congrArg Subtype.val hpq.symm]
        exact dist_self _
      linarith
    refine ⟨qs, ?_, ?_⟩
    · exact (SimpleGraph.mem_neighborFinset
        (G := Erdos957.distanceGraph A 1) (v := p) qs).mpr ⟨hpq, hdist'⟩
    · exact hqz

/-- Every vertex of a one-separated planar set has at most six unit neighbours. -/
theorem unit_degree_le_six {A : Finset Point}
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ dist x y)
    (p : {x // x ∈ A}) :
    (Erdos957.distanceGraph A 1).degree p ≤ 6 := by
  rw [degree_eq_complex_unitNeighbors]
  exact Erdos957Angle.card_unitNeighbors_le_six
    (complexPreimage_oneSeparated hsep) (complexPlaneEquiv.symm p)

/-- The number of unit-distance pairs in a one-separated planar set is at
most three times the number of points. -/
theorem unit_multiplicity_le_three_mul_card {A : Finset Point}
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ dist x y) :
    Erdos957.multiplicity A 1 ≤ 3 * A.card := by
  let G := Erdos957.distanceGraph A 1
  have hsum : ∑ v, G.degree v ≤ 6 * Fintype.card {x // x ∈ A} := by
    calc
      ∑ v, G.degree v ≤ ∑ _v : {x // x ∈ A}, 6 :=
        Finset.sum_le_sum fun v _ ↦ unit_degree_le_six hsep v
      _ = 6 * Fintype.card {x // x ∈ A} := by simp [mul_comm]
  have hhandshake : 2 * G.edgeFinset.card = ∑ v, G.degree v := by
    simpa [Nat.mul_comm] using G.sum_degrees_eq_twice_card_edges.symm
  have htwice : 2 * Erdos957.multiplicity A 1 ≤ 6 * A.card := by
    calc
      2 * Erdos957.multiplicity A 1 = 2 * G.edgeFinset.card := rfl
      _ = ∑ v, G.degree v := hhandshake
      _ ≤ 6 * A.card := by simpa using hsum
  omega

/-- The public maximum-distance predicate bounds even equal pairs. -/
lemma maximumDistance_all_pairs {A : Finset Point} {r : ℝ}
    (hmax : Erdos957.IsMaximumDistance A r) :
    ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ r := by
  intro x hx y hy
  by_cases hxy : x = y
  · subst y
    simpa using hmax.pos.le
  · exact hmax.2 _ (Erdos957.dist_mem_distanceSet hx hy hxy)

/-- Conversion to the maximum-distance predicate used by the diameter module. -/
lemma maximumDistance_to_diameter {A : Finset Point} {r : ℝ}
    (hmax : Erdos957.IsMaximumDistance A r) :
    Erdos957Diameter.IsMaximumDistance A r :=
  ⟨Erdos957.mem_distanceSet.mp hmax.1, maximumDistance_all_pairs hmax⟩

lemma multiplicity_eq_maximumDistancePairCount (A : Finset Point) (r : ℝ) :
    Erdos957.multiplicity A r =
      Erdos957Diameter.maximumDistancePairCount A r := rfl

lemma maximumDistanceEndpoints_eq_distanceEndpoints (A : Finset Point) (r : ℝ) :
    Erdos957Diameter.maximumDistanceEndpoints A r =
      Erdos957.distanceEndpoints A r := by
  classical
  ext x
  simp only [Erdos957Diameter.mem_maximumDistanceEndpoints,
    Erdos957.mem_distanceEndpoints]

/-- If the convex hull has at most two vertices, the multiplicity of a
maximum determined distance is at most two. -/
theorem maximum_multiplicity_le_two_of_hull_card_le_two
    {A : Finset Point} {r : ℝ}
    (hmax : Erdos957.IsMaximumDistance A r)
    (hhull : (Erdos957.hullVertices A).card ≤ 2) :
    Erdos957.multiplicity A r ≤ 2 := by
  have hpair := Erdos957Diameter.maximumDistancePairCount_le_endpoints
    (maximumDistance_to_diameter hmax)
  rw [maximumDistanceEndpoints_eq_distanceEndpoints] at hpair
  have hend : (Erdos957.distanceEndpoints A r).card ≤
      (Erdos957.hullVertices A).card :=
    Erdos957.card_distanceEndpoints_le_card_hullVertices A r
      (maximumDistance_all_pairs hmax)
  rw [multiplicity_eq_maximumDistancePairCount]
  calc
    Erdos957Diameter.maximumDistancePairCount A r
        ≤ (Erdos957.distanceEndpoints A r).card := hpair
    _ ≤ (Erdos957.hullVertices A).card := hend
    _ ≤ 2 := hhull

/-- The complete degenerate-hull product bound, in the natural-number form. -/
theorem multiplicity_product_le_six_mul_card_of_hull_card_le_two
    {A : Finset Point} {r : ℝ}
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ dist x y)
    (hmax : Erdos957.IsMaximumDistance A r)
    (hhull : (Erdos957.hullVertices A).card ≤ 2) :
    Erdos957.multiplicity A 1 * Erdos957.multiplicity A r ≤ 6 * A.card := by
  calc
    Erdos957.multiplicity A 1 * Erdos957.multiplicity A r
        ≤ (3 * A.card) * 2 :=
      Nat.mul_le_mul (unit_multiplicity_le_three_mul_card hsep)
        (maximum_multiplicity_le_two_of_hull_card_le_two hmax hhull)
    _ = 6 * A.card := by omega

/-- Real-valued form used by the final asymptotic estimate. -/
theorem multiplicity_product_real_le_six_mul_card_of_hull_card_le_two
    {A : Finset Point} {r : ℝ}
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ dist x y)
    (hmax : Erdos957.IsMaximumDistance A r)
    (hhull : (Erdos957.hullVertices A).card ≤ 2) :
    (Erdos957.multiplicity A 1 : ℝ) * Erdos957.multiplicity A r ≤
      6 * A.card := by
  exact_mod_cast multiplicity_product_le_six_mul_card_of_hull_card_le_two
    hsep hmax hhull

end

end Erdos957LowHull
