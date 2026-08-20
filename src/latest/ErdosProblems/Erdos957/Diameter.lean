/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos957.Hull
import ErdosProblems.Erdos223.Plane

open Metric
open scoped EuclideanGeometry RealInnerProductSpace SimpleGraph

namespace Erdos957Diameter

noncomputable section

abbrev Plane := Erdos223.Point 2

/-- `r` is attained by two distinct points of `A`, and bounds every distance in `A`. -/
def IsMaximumDistance (A : Finset Plane) (r : ℝ) : Prop :=
  (∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ dist x y = r) ∧
    ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ r

/-- The graph of pairs in `A` whose distance is exactly `r`. -/
def maximumDistanceGraph (A : Finset Plane) (r : ℝ) :
    SimpleGraph {x // x ∈ A} where
  Adj x y := x ≠ y ∧ dist (x : Plane) (y : Plane) = r
  symm.symm := by
    rintro x y ⟨hxy, h⟩
    exact ⟨hxy.symm, by simpa [dist_comm] using h⟩
  loopless.irrefl x h := h.1 rfl

noncomputable instance (A : Finset Plane) (r : ℝ) :
    DecidableRel (maximumDistanceGraph A r).Adj :=
  Classical.decRel _

/-- The number of unordered pairs in `A` at distance `r`. -/
def maximumDistancePairCount (A : Finset Plane) (r : ℝ) : ℕ :=
  (maximumDistanceGraph A r).edgeFinset.card

lemma IsMaximumDistance.pos {A : Finset Plane} {r : ℝ}
    (h : IsMaximumDistance A r) : 0 < r := by
  obtain ⟨x, hx, y, hy, hxy, hr⟩ := h.1
  rw [← hr]
  exact dist_pos.mpr hxy

/-- Multiplication by `r⁻¹`, viewed as a genuine equivalence when `r ≠ 0`. -/
def scaleEquiv (r : ℝ) (hr : r ≠ 0) : Plane ≃ Plane where
  toFun x := r⁻¹ • x
  invFun x := r • x
  left_inv x := by simp [smul_smul, hr]
  right_inv x := by simp [smul_smul, hr]

/-- The configuration obtained by scaling all points by `r⁻¹`. -/
def normalize (A : Finset Plane) (r : ℝ) (hr : r ≠ 0) : Finset Plane :=
  A.map (scaleEquiv r hr).toEmbedding

@[simp] lemma card_normalize (A : Finset Plane) (r : ℝ) (hr : r ≠ 0) :
    (normalize A r hr).card = A.card := by
  simp [normalize]

/-- Scaling induces the expected equivalence between the two finite vertex types. -/
def normalizeVertexEquiv (A : Finset Plane) (r : ℝ) (hr : r ≠ 0) :
    {x // x ∈ A} ≃ {x // x ∈ normalize A r hr} where
  toFun x :=
    ⟨scaleEquiv r hr x, Finset.mem_map.mpr ⟨x, x.property, rfl⟩⟩
  invFun y := by
    refine ⟨(scaleEquiv r hr).symm y, ?_⟩
    obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp y.property
    simpa [← hxy] using hx
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp

lemma dist_scaleEquiv (r : ℝ) (hr : 0 < r) (x y : Plane) :
    dist (scaleEquiv r hr.ne' x) (scaleEquiv r hr.ne' y) = r⁻¹ * dist x y := by
  change dist (r⁻¹ • x) (r⁻¹ • y) = r⁻¹ * dist x y
  rw [dist_smul₀]
  congr 1
  simp [Real.norm_eq_abs, abs_of_pos hr]

lemma isDiameterOne_normalize {A : Finset Plane} {r : ℝ}
    (h : IsMaximumDistance A r) :
    Erdos223.IsDiameterOne (normalize A r h.pos.ne') := by
  rw [Erdos223.isDiameterOne_iff]
  constructor
  · intro x hx y hy
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_map.mp hy
    change dist (scaleEquiv r h.pos.ne' x₀) (scaleEquiv r h.pos.ne' y₀) ≤ 1
    rw [dist_scaleEquiv r h.pos]
    have hr := h.2 x₀ hx₀ y₀ hy₀
    rw [inv_mul_le_one₀ h.pos]
    exact hr
  · obtain ⟨x, hx, y, hy, hxy, hdist⟩ := h.1
    refine ⟨scaleEquiv r h.pos.ne' x, ?_, scaleEquiv r h.pos.ne' y, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    · exact Finset.mem_map.mpr ⟨y, hy, rfl⟩
    · rw [dist_scaleEquiv r h.pos, hdist, inv_mul_cancel₀ h.pos.ne']

/-- Normalization identifies the arbitrary-radius maximum-distance graph with
the unit-diameter graph used by `Erdos223`. -/
def normalizeGraphIso {A : Finset Plane} {r : ℝ}
    (h : IsMaximumDistance A r) :
    maximumDistanceGraph A r ≃g
      Erdos223.diameterGraph (normalize A r h.pos.ne') where
  toEquiv := normalizeVertexEquiv A r h.pos.ne'
  map_rel_iff' := by
    intro x y
    change dist (scaleEquiv r h.pos.ne' x) (scaleEquiv r h.pos.ne' y) = 1 ↔
      (x ≠ y ∧ dist (x : Plane) (y : Plane) = r)
    rw [dist_scaleEquiv r h.pos]
    constructor
    · intro hxy
      have hdist : dist (x : Plane) (y : Plane) = r := by
        rw [inv_mul_eq_one₀ h.pos.ne'] at hxy
        exact hxy.symm
      have hne : x ≠ y := by
        intro hEq
        rw [hEq, dist_self] at hdist
        exact h.pos.ne' hdist.symm
      exact ⟨hne, hdist⟩
    · rintro ⟨-, rfl⟩
      exact inv_mul_cancel₀ h.pos.ne'

lemma maximumDistancePairCount_eq_normalized {A : Finset Plane} {r : ℝ}
    (h : IsMaximumDistance A r) :
    maximumDistancePairCount A r =
      Erdos223.diameterPairCount (normalize A r h.pos.ne') := by
  simpa [maximumDistancePairCount, Erdos223.diameterPairCount] using
    (normalizeGraphIso h).card_edgeFinset_eq

/-- Hopf--Pannwitz at arbitrary positive scale. -/
theorem maximumDistancePairCount_le_card {A : Finset Plane} {r : ℝ}
    (h : IsMaximumDistance A r) :
    maximumDistancePairCount A r ≤ A.card := by
  rw [maximumDistancePairCount_eq_normalized h, ← card_normalize A r h.pos.ne']
  exact Erdos223.diameterPairCount_le_card_plane _ (isDiameterOne_normalize h)

/-- The points of `A` incident to at least one distance-`r` pair. -/
def maximumDistanceEndpoints (A : Finset Plane) (r : ℝ) : Finset Plane :=
  A.filter fun x ↦ ∃ y ∈ A, x ≠ y ∧ dist x y = r

@[simp] lemma mem_maximumDistanceEndpoints {A : Finset Plane} {r : ℝ} {x : Plane} :
    x ∈ maximumDistanceEndpoints A r ↔
      x ∈ A ∧ ∃ y ∈ A, x ≠ y ∧ dist x y = r := by
  simp [maximumDistanceEndpoints]

lemma maximumDistanceEndpoints_subset (A : Finset Plane) (r : ℝ) :
    maximumDistanceEndpoints A r ⊆ A := by
  intro x hx
  exact (mem_maximumDistanceEndpoints.mp hx).1

lemma isMaximumDistance_endpoints {A : Finset Plane} {r : ℝ}
    (h : IsMaximumDistance A r) :
    IsMaximumDistance (maximumDistanceEndpoints A r) r := by
  obtain ⟨x, hx, y, hy, hxy, hd⟩ := h.1
  constructor
  · refine ⟨x, ?_, y, ?_, hxy, hd⟩
    · exact mem_maximumDistanceEndpoints.mpr ⟨hx, y, hy, hxy, hd⟩
    · exact mem_maximumDistanceEndpoints.mpr
        ⟨hy, x, hx, hxy.symm, by simpa [dist_comm] using hd⟩
  · intro p hp q hq
    exact h.2 p (maximumDistanceEndpoints_subset A r hp)
      q (maximumDistanceEndpoints_subset A r hq)

/-- The support of the maximum-distance graph is naturally the subtype of its
geometric endpoint finset. -/
def endpointVertexEquiv (A : Finset Plane) (r : ℝ) :
    {v : {x // x ∈ A} // v ∈ (maximumDistanceGraph A r).support} ≃
      {x // x ∈ maximumDistanceEndpoints A r} where
  toFun v := by
    refine ⟨v.1.1, ?_⟩
    obtain ⟨w, hvw⟩ := v.2
    exact mem_maximumDistanceEndpoints.mpr
      ⟨v.1.2, w.1, w.2, fun h ↦ hvw.1 (Subtype.ext h), hvw.2⟩
  invFun x :=
    let hx := mem_maximumDistanceEndpoints.mp x.2
    let y := Classical.choose hx.2
    let hy := Classical.choose_spec hx.2
    ⟨⟨x.1, hx.1⟩,
      ⟨⟨y, hy.1⟩, fun h ↦ hy.2.1 (congrArg Subtype.val h), hy.2.2⟩⟩
  left_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

/-- Deleting all isolated vertices from the maximum-distance graph produces
exactly the maximum-distance graph on the endpoint finset. -/
def supportGraphIso (A : Finset Plane) (r : ℝ) :
    (maximumDistanceGraph A r).induce (maximumDistanceGraph A r).support ≃g
      maximumDistanceGraph (maximumDistanceEndpoints A r) r where
  toEquiv := endpointVertexEquiv A r
  map_rel_iff' := by
    intro x y
    change
      ((endpointVertexEquiv A r x) ≠ endpointVertexEquiv A r y ∧
        dist ((endpointVertexEquiv A r x : {p // p ∈ maximumDistanceEndpoints A r}) : Plane)
          ((endpointVertexEquiv A r y : {p // p ∈ maximumDistanceEndpoints A r}) : Plane) = r) ↔
        (x.1 ≠ y.1 ∧ dist (x.1.1 : Plane) (y.1.1 : Plane) = r)
    simp only [endpointVertexEquiv]
    constructor
    · rintro ⟨hne, hd⟩
      refine ⟨?_, hd⟩
      intro hxy
      apply hne
      exact Subtype.ext
        (congrArg (fun z : {p // p ∈ A} ↦ (z : Plane)) hxy)
    · rintro ⟨hne, hd⟩
      refine ⟨?_, hd⟩
      intro hxy
      apply hne
      exact Subtype.ext
        (congrArg
          (fun z : {p // p ∈ maximumDistanceEndpoints A r} ↦ (z : Plane)) hxy)

lemma maximumDistancePairCount_endpoints_eq {A : Finset Plane} {r : ℝ} :
    maximumDistancePairCount (maximumDistanceEndpoints A r) r =
      maximumDistancePairCount A r := by
  calc
    maximumDistancePairCount (maximumDistanceEndpoints A r) r =
        ((maximumDistanceGraph A r).induce
          (maximumDistanceGraph A r).support).edgeFinset.card := by
      simpa [maximumDistancePairCount] using (supportGraphIso A r).card_edgeFinset_eq.symm
    _ = maximumDistancePairCount A r := by
      simpa [maximumDistancePairCount] using
        (maximumDistanceGraph A r).card_edgeFinset_induce_support

/-- Hopf--Pannwitz in endpoint-count form: the number of maximum-distance pairs
is at most the number of points incident to one of those pairs. -/
theorem maximumDistancePairCount_le_endpoints {A : Finset Plane} {r : ℝ}
    (h : IsMaximumDistance A r) :
    maximumDistancePairCount A r ≤ (maximumDistanceEndpoints A r).card := by
  rw [← maximumDistancePairCount_endpoints_eq]
  exact maximumDistancePairCount_le_card (isMaximumDistance_endpoints h)

end

end Erdos957Diameter

