import Wikipedia.NoExoticSixSphere.ManifoldSphereBoundaryRelation
import Wikipedia.NoExoticSixSphere.PartialFrameSphereHomology

/-!
# Applying the actual boundary relation to a continuous partial-frame map

The signed integral relation gives an unsigned mod-two obstruction relation.
For a continuous frame map whose actual linking-sphere obstructions are one,
an even singularity count forces equal endpoint obstructions. Constructing
the relevant global frame map and identifying its endpoint obstructions with
geometric normal-disk parity are separate remaining obligations.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily.ParityBallSystem

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {g : ℝ → Sphere 3 → M} (P : ParityBallSystem g)

theorem sum_boundary_frame_obstruction_zero [Fintype (BoundaryIndex g)] (r : ℕ)
    (F : C(P.puncturedCylinder, Space (3 + (r + 2)) (r + 2))) :
    ∑ i, sphereThirdObstruction r (F.comp (P.sphereInclusion i)) = 0 := by
  calc
    ∑ i, sphereThirdObstruction r (F.comp (P.sphereInclusion i)) =
        ∑ i, P.boundaryCoefficient i •
          sphereThirdObstruction r (F.comp (P.sphereInclusion i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rcases P.boundaryCoefficient_eq_one_or_neg_one i with h | h
      · rw [h, one_zsmul]
      · rw [h, neg_one_zsmul, ZMod.neg_eq_self_mod_two]
    _ = 0 := sphereThirdObstruction_sum_of_homology r F P.sphereInclusion
      P.boundaryCoefficient (P.sum_sphere_boundaryCoefficient_zero sphereThirdClass)

theorem endpoint_frame_obstruction_eq_of_even_links (r : ℕ)
    (F : C(P.puncturedCylinder, Space (3 + (r + 2)) (r + 2)))
    (heven : Even (Nat.card (singularParameters (n := 6) g)))
    (hlinks : ∀ q : singularParameters (n := 6) g,
      sphereThirdObstruction r (F.comp (P.sphereInclusion (.inr q))) = 1) :
    sphereThirdObstruction r (F.comp (P.sphereInclusion (.inl false))) =
      sphereThirdObstruction r (F.comp (P.sphereInclusion (.inl true))) := by
  let := P.finite_singular.to_subtype
  let := Fintype.ofFinite (singularParameters (n := 6) g)
  have hcard : (Fintype.card (singularParameters (n := 6) g) : ZMod 2) = 0 := by
    apply ZMod.natCast_eq_zero_iff_even.mpr
    simpa only [Nat.card_eq_fintype_card] using heven
  have h := P.sum_boundary_frame_obstruction_zero r F
  rw [Fintype.sum_sum_type, Fintype.sum_bool] at h
  simp only [hlinks, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    hcard, add_zero] at h
  have he := eq_neg_of_add_eq_zero_left h
  rw [ZMod.neg_eq_self_mod_two] at he
  exact he.symm

end NoExoticSixSphere.SphereFamily.ParityBallSystem
