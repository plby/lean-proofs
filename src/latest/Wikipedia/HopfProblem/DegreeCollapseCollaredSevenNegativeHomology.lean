import Wikipedia.HopfProblem.DegreeCollapseTimeCollarNegativeHomology
import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenNegativeCollar
import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenUpperHomology

/-!
# The original complementary-half homology map in a cleared seven-state

The literal nonpositive half and the nonnegative half of the reversed time
are identified by the identity on ambient points. Mayer--Vietoris and the
proved positive-half acyclicity then give isomorphisms in degrees one
through five and surjectivity in degree six for the original inclusion.
The boundary's nonzero sixth homology is not assumed to vanish.
-/

noncomputable section

open Set Function ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere SingularMayerVietoris PeriodTorusHigherHomology

variable {B : Type} [TopologicalSpace B] (S : CollaredSevenState B)

def negativeHalfTimeHomeomorph : S.NegativeHalf ≃ₜ
    TimeCollar.NonnegativeHalf (fun p : S.Space ↦ -S.time p) where
  toFun p := ⟨p.val, neg_nonneg.mpr p.property⟩
  invFun p := ⟨p.val, neg_nonneg.mp p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

theorem negativeHalfTime_inclusion :
    (TimeCollar.halfInclusion (fun p : S.Space ↦ -S.time p)).comp
      S.negativeHalfTimeHomeomorph.toHomotopyEquiv.toFun = S.negativeHalfInclusion := rfl

theorem negativeHalfInclusion_homology_factorization (k : ℕ) :
    singularHomologyMap S.negativeHalfInclusion k =
      (singularHomologyMap (TimeCollar.halfInclusion (fun p : S.Space ↦ -S.time p)) k).comp
        (singularHomologyMap S.negativeHalfTimeHomeomorph.toHomotopyEquiv.toFun k) :=
  singularHomologyMap_comp S.negativeHalfTimeHomeomorph.toHomotopyEquiv.toFun
    (TimeCollar.halfInclusion (fun p : S.Space ↦ -S.time p)) k

theorem negativeHalfInclusion_homology_bijective (eBoundary : B ≃ₜ Sphere 6)
    [Finite (SingularHomology S.Space 3)] [Subsingleton (SingularHomology S.Half 3)]
    (k : ℕ) (hk : k ≠ 0) (h6 : k < 6) :
    Bijective (singularHomologyMap S.negativeHalfInclusion k) := by
  have hB (j : ℕ) (hj : j ≠ 0) (hj6 : j ≠ 6) : Subsingleton (SingularHomology B j) := by
    let : Subsingleton (SingularHomology (Sphere 6) j) :=
      SphereHomology.unitSphere_homology_subsingleton 5 j hj hj6
    exact (homotopyEquivHomologyEquiv eBoundary.toHomotopyEquiv j).injective.subsingleton
  have hneg : Bijective (singularHomologyMap
      (TimeCollar.halfInclusion (fun p : S.Space ↦ -S.time p)) k) := by
    by_cases h1 : k = 1
    · subst k
      let := hB 1 (by decide) (by decide)
      let : Subsingleton (SingularHomology S.Space 1) :=
        IntegralTopClassLift.first_homology_subsingleton S.Space
      exact S.collar.negativeInclusion_homology_bijective_of_ambient_zero 1
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      let := hB j (by omega) (by omega)
      let := hB (j + 1) (by omega) (by omega)
      let : Subsingleton (SingularHomology S.Half (j + 1)) :=
        S.half_positive_homology_of_sphere eBoundary (j + 1) (by omega)
      exact S.collar.negativeInclusion_homology_bijective j
  rw [S.negativeHalfInclusion_homology_factorization k]
  exact hneg.comp
    (homotopyEquivHomologyEquiv S.negativeHalfTimeHomeomorph.toHomotopyEquiv k).bijective

theorem negativeHalfInclusion_homology_six_surjective (eBoundary : B ≃ₜ Sphere 6) :
    Surjective (singularHomologyMap S.negativeHalfInclusion 6) := by
  let : SimplyConnectedSpace B := eBoundary.toHomotopyEquiv.simplyConnectedSpace
  let : Subsingleton (SingularHomology (Sphere 6) 5) :=
    SphereHomology.unitSphere_homology_subsingleton 5 5 (by decide) (by decide)
  let : Subsingleton (SingularHomology B 5) :=
    (homotopyEquivHomologyEquiv eBoundary.toHomotopyEquiv 5).injective.subsingleton
  let : Subsingleton (SingularHomology S.Half 6) := S.half_sixth_homology
  rw [S.negativeHalfInclusion_homology_factorization 6]
  exact (S.collar.negativeInclusion_homology_surjective 5).comp
    (homotopyEquivHomologyEquiv S.negativeHalfTimeHomeomorph.toHomotopyEquiv 6).surjective

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
