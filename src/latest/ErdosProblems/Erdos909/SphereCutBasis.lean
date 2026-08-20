/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos909.GoodSphereDirections
import ErdosProblems.Erdos909.GenericCut

/-!
# Countable chord-cut bases in finite-dimensional Euclidean affine spaces

This file combines the metric basis and chord-sphere lemmas with the finite
family of generic radial directions.  The resulting basis is countable, all
of its centers have simultaneously good radial normals, and every designated
relative sphere is exactly a Euclidean sphere in its chord hyperplane.
-/

open Set Topology TopologicalSpace
open Metric

namespace Erdos909

noncomputable section

variable {V P : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- Translation by `o` identifies the radius-`R` vector sphere with the
radius-`R` sphere centered at `o`. -/
def radialSphereIsometryEquiv (o : P) (R : ℝ) :
    sphere (0 : V) R ≃ᵢ sphere o R where
  toFun v := ⟨(v : V) +ᵥ o, by
    simpa only [mem_sphere, dist_vadd_left, dist_zero_right] using v.property⟩
  invFun c := ⟨(c : P) -ᵥ o, by
    rw [Metric.mem_sphere, dist_zero_right, ← dist_eq_norm_vsub V]
    exact c.property⟩
  left_inv v := by
    apply Subtype.ext
    exact vadd_vsub (v : V) o
  right_inv c := by
    apply Subtype.ext
    exact vsub_vadd (c : P) o
  isometry_toFun := Isometry.of_dist_eq fun v w =>
    dist_vadd_cancel_right (v : V) (w : V) o

@[simp]
theorem coe_radialSphereIsometryEquiv (o : P) (R : ℝ)
    (v : sphere (0 : V) R) :
    (radialSphereIsometryEquiv o R v : P) = (v : V) +ᵥ o :=
  rfl

@[simp]
theorem radialSphereIsometryEquiv_vsub (o : P) (R : ℝ)
    (v : sphere (0 : V) R) :
    (radialSphereIsometryEquiv o R v : P) -ᵥ o = (v : V) := by
  exact vadd_vsub (v : V) o

/-- A positive-radius Euclidean sphere admits a countable dense family of
centers whose radial vectors simultaneously avoid the orthogonal complements
of every member of a prescribed finite family of nonzero subspaces. -/
theorem exists_countable_dense_good_centers
    [FiniteDimensional ℝ V]
    (o : P) {R : ℝ} (hR : 0 < R)
    (F : Finset (Submodule ℝ V)) (hF : ∀ Q ∈ F, Q ≠ ⊥) :
    ∃ C : Set (sphere o R),
      C.Countable ∧ Dense C ∧
      ∀ c ∈ C, ∀ Q ∈ F, (c : P) -ᵥ o ∉ Qᗮ := by
  obtain ⟨D, hDgood, hDcount, hDdense⟩ :=
    exists_countable_dense_subset_goodSphereDirectionsFinset hR hF
  let e : sphere (0 : V) R ≃ᵢ sphere o R := radialSphereIsometryEquiv o R
  refine ⟨e '' D, hDcount.image e, ?_, ?_⟩
  · exact e.toHomeomorph.isDenseEmbedding.dense_image.mpr hDdense
  · rintro c ⟨v, hvD, rfl⟩ Q hQF
    have hvGood := hDgood hvD
    have hvQ : (v : V) ∉ Qᗮ := by
      have hvQgood : v ∈ goodSphereDirections R Q := by
        exact Set.mem_iInter.mp
          (Set.mem_iInter.mp hvGood Q) hQF
      exact hvQgood
    simpa only [e, radialSphereIsometryEquiv_vsub] using hvQ

/-- Fully packaged relative ball basis for a Euclidean sphere.

Besides countability and the basis property, the package records:

* simultaneous general position of every radial center;
* frontier containment in the designated relative metric sphere; and
* an exact realization of that relative sphere as a Euclidean sphere in the
  affine hyperplane orthogonal to the radial normal.

The last clause uses a negative-radius sphere when the designated relative
sphere is empty, so the interface is total and no nonemptiness side condition
is imposed on basis members. -/
theorem exists_countable_good_chord_ballBasis
    [FiniteDimensional ℝ V]
    (o : P) {R : ℝ} (hR : 0 < R)
    (F : Finset (Submodule ℝ V)) (hF : ∀ Q ∈ F, Q ≠ ⊥) :
    ∃ C : Set (sphere o R),
      C.Countable ∧ Dense C ∧
      (invNatBallBasis C).Countable ∧
      IsTopologicalBasis (invNatBallBasis C) ∧
      (∀ c ∈ C, ∀ Q ∈ F, (c : P) -ᵥ o ∉ Qᗮ) ∧
      ∀ U ∈ invNatBallBasis C,
        ∃ c ∈ C, ∃ n : ℕ,
          U = ball c (invNatRadius n) ∧
          frontier U ⊆ sphere c (invNatRadius n) ∧
          ∃ (H : AffineSubspace ℝ P) (s : EuclideanGeometry.Sphere H),
            H.direction = (ℝ ∙ ((c : P) -ᵥ o))ᗮ ∧
            (∀ Q ∈ F, Q ⊔ H.direction = ⊤) ∧
            Subtype.val '' (s : Set H) =
              Subtype.val ''
                (sphere c (invNatRadius n) : Set (sphere o R)) := by
  obtain ⟨C, hCc, hCd, hCgood⟩ :=
    exists_countable_dense_good_centers o hR F hF
  refine ⟨C, hCc, hCd, invNatBallBasis_countable hCc,
    invNatBallBasis_isTopologicalBasis hCd, hCgood, ?_⟩
  intro U hU
  obtain ⟨c, hc, n, rfl⟩ := hU
  refine ⟨c, hc, n, rfl, frontier_ball_subset_sphere, ?_⟩
  obtain ⟨H, s, hH, hs⟩ :=
    exists_affineSphere_image_eq_image_relativeSphere_total
      o R c (invNatRadius n)
  refine ⟨H, s, hH, ?_, hs⟩
  intro Q hQF
  have hv : (c : P) -ᵥ o ∉ (Q ⊓ (⊤ : Submodule ℝ V))ᗮ := by
    simpa using hCgood c hc Q hQF
  have htrans := GenericCut.sup_inf_orthogonal_eq_top
    (⊤ : Submodule ℝ V) Q (by simp) hv
  simpa only [top_inf_eq, hH] using htrans

end

end Erdos909
