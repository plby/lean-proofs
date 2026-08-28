import Wikipedia.HopfProblem.DegreeCollapseSphereFiniteRepresentative

/-!
# Exact local Cartesian formulas for the original sphere products

On the finite chart where the old images avoid the pole, the original
product suspension is the Cartesian product with the real identity.
The original smash square is the Cartesian square. These equalities
hold for the actual descended maps and supply eventual chart squares.
-/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereProductLocalFormula

open NoExoticSixSphere SphereComposition CubicalSphereSuspension
open FiniteSphereProductCharts SphereFiniteRepresentative

variable {m n : ℕ} (f : Based m n)

theorem compactMap_coe (p : V m) :
    compactMap f (↑p : OnePoint (V m)) =
      (euclideanOnePointSphere n).symm (f.val (point m p)) := by
  change (euclideanOnePointSphere n).symm
    (f.val (euclideanOnePointSphere m (↑p : OnePoint (V m)))) = _
  rw [euclideanOnePointSphere_coe]
  rfl

theorem line_formula (p : V m × ℝ) (hb : f.val (point m p.1) ≠ spherePole n) :
    (productBasedMap f).val ((lineChart m).symm p) =
      (lineChart n).symm (line f.val p) := by
  have h := ProductSphereFiber.product_formula f
    ((↑p.1 : OnePoint (V m)), (↑p.2 : OnePoint ℝ))
  rw [OnePointProduct.map_coe, compactMap_coe, euclideanOnePointSphere_symm_of_ne n hb,
    OnePointProduct.map_coe] at h
  exact (congrArg (productBasedMap f).val (lineChart_symm_coe m p)).trans
    (h.trans (lineChart_symm_coe n (line f.val p)).symm)

theorem line_pole (p : V m × ℝ) (hb : f.val (point m p.1) = spherePole n) :
    (productBasedMap f).val ((lineChart m).symm p) = spherePole (n + 1) := by
  have h := ProductSphereFiber.product_formula f
    ((↑p.1 : OnePoint (V m)), (↑p.2 : OnePoint ℝ))
  rw [OnePointProduct.map_coe, compactMap_coe, hb, inverseSphere_pole,
    OnePointProduct.map_infty_left, ProductSphereFiber.productSphereHomeomorph_infty] at h
  exact (congrArg (productBasedMap f).val (lineChart_symm_coe m p)).trans h

theorem pairChart_inverse_pairing (p : V m × V m) :
    (pairChart m).symm p = JamesSphere.pairing m (point m p.1, point m p.2) := by
  have h := pairing_finite m (point_ne_pole m p.1) (point_ne_pole m p.2)
  rw [projection_point, projection_point] at h
  exact h.symm

theorem square_formula (p : V m × V m)
    (hb : f.val (point m p.1) ≠ spherePole n)
    (hc : f.val (point m p.2) ≠ spherePole n) :
    SphereSmash.squareMap f ((pairChart m).symm p) =
      (pairChart n).symm (square f.val p) := by
  rw [pairChart_inverse_pairing, SphereSmash.squareMap_pairing]
  exact pairing_finite n hb hc

theorem square_pole_left (p : V m × V m)
    (hb : f.val (point m p.1) = spherePole n) :
    SphereSmash.squareMap f ((pairChart m).symm p) = spherePole (n + n) := by
  rw [pairChart_inverse_pairing, SphereSmash.squareMap_pairing, hb, JamesSphere.pairing_left_pole]

theorem square_pole_right (p : V m × V m)
    (hb : f.val (point m p.2) = spherePole n) :
    SphereSmash.squareMap f ((pairChart m).symm p) = spherePole (n + n) := by
  rw [pairChart_inverse_pairing, SphereSmash.squareMap_pairing, hb, JamesSphere.pairing_right_pole]

theorem finite_nonpole_open : IsOpen {p : V m | f.val (point m p) ≠ spherePole n} :=
  isClosed_singleton.isOpen_compl.preimage
    (f.val.continuous.comp (point_contMDiff m).continuous)

theorem line_eventually (p : V m × ℝ) (hb : f.val (point m p.1) ≠ spherePole n) :
    (fun u ↦ (productBasedMap f).val ((lineChart m).symm u)) =ᶠ[𝓝 p]
      (fun u ↦ (lineChart n).symm (line f.val u)) := by
  have hU : IsOpen {u : V m × ℝ | f.val (point m u.1) ≠ spherePole n} :=
    (finite_nonpole_open f).preimage continuous_fst
  filter_upwards [hU.mem_nhds hb] with u hu
  exact line_formula f u hu

theorem square_eventually (p : V m × V m)
    (hb : f.val (point m p.1) ≠ spherePole n)
    (hc : f.val (point m p.2) ≠ spherePole n) :
    (fun u ↦ SphereSmash.squareMap f ((pairChart m).symm u)) =ᶠ[𝓝 p]
      (fun u ↦ (pairChart n).symm (square f.val u)) := by
  have hU : IsOpen {u : V m × V m | f.val (point m u.1) ≠ spherePole n} :=
    (finite_nonpole_open f).preimage continuous_fst
  have hV : IsOpen {u : V m × V m | f.val (point m u.2) ≠ spherePole n} :=
    (finite_nonpole_open f).preimage continuous_snd
  filter_upwards [hU.mem_nhds hb, hV.mem_nhds hc] with u hu hv
  exact square_formula f u hu hv

end Wikipedia.HopfProblem.DegreeCollapse.SphereProductLocalFormula

