import Wikipedia.NoExoticSixSphere.FourAnnulusPunctureCover
import Wikipedia.NoExoticSixSphere.MayerVietorisInclusionRange

/-!
# An actual overlap lift of the original outer-minus-inner boundary class

The literal radius-one and radius-two sphere maps are homotopic in the
complement of the origin. Their difference therefore vanishes after the
original singular-complement inclusion. Exactness of the actual open-cover
Mayer--Vietoris sequence lifts this difference to the original overlap.
No vanishing of ambient homology or signed boundary relation is assumed.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourAnnulus.ParityBallSystem

open GLOrthonormalization AnnulusDoublePoints SphereAnnulus
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {g : Vector 4 → M} (P : ParityBallSystem g)

def innerOuterNonzeroHomotopy :
    ((complementInNonzero g).comp P.complementInnerBoundary).Homotopy
      ((complementInNonzero g).comp P.complementOuterBoundary) where
  toFun v := ⟨(1 + (v.1 : ℝ)) • v.2.val, by
    have hq : v.2.val ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [ClosedHemisphere.unit_norm]
      exact one_ne_zero
    exact smul_ne_zero (add_pos_of_pos_of_nonneg zero_lt_one v.1.property.1).ne' hq⟩
  continuous_toFun := by
    have hs : Continuous (fun v : unitInterval × Sphere 3 ↦ 1 + (v.1 : ℝ)) :=
      continuous_const.add (continuous_subtype_val.comp continuous_fst)
    have hv : Continuous (fun v : unitInterval × Sphere 3 ↦ v.2.val) :=
      continuous_subtype_val.comp continuous_snd
    exact (hs.smul hv).subtype_mk _
  map_zero_left q := by
    apply Subtype.ext
    change (1 + (0 : ℝ)) • q.val = q.val
    simp
  map_one_left q := by
    apply Subtype.ext
    change (1 + (1 : ℝ)) • q.val = (2 : ℝ) • q.val
    norm_num

theorem inner_outer_nonzero_homologyMap (n : ℕ) :
    singularHomologyMap ((complementInNonzero g).comp P.complementInnerBoundary) n =
      singularHomologyMap ((complementInNonzero g).comp P.complementOuterBoundary) n :=
  homotopy_homologyMap P.innerOuterNonzeroHomotopy n

def boundaryDifference (n : ℕ) (a : SingularHomology (Sphere 3) n) :
    SingularHomology (SingularComplement g) n :=
  singularHomologyMap P.complementOuterBoundary n a -
    singularHomologyMap P.complementInnerBoundary n a

theorem boundaryDifference_inclusion_zero (n : ℕ) (a : SingularHomology (Sphere 3) n) :
    singularHomologyMap (complementInNonzero g) n (P.boundaryDifference n a) = 0 := by
  have h := congrArg (fun f ↦ f a) (P.inner_outer_nonzero_homologyMap n)
  simpa only [boundaryDifference, map_sub, singularHomologyMap_comp, LinearMap.comp_apply]
    using sub_eq_zero.mpr h.symm

theorem exists_boundaryDifference_lift (n : ℕ) (a : SingularHomology (Sphere 3) n) :
    ∃ b : SingularHomology (singularComplementSet g ∩ P.openHoles : Set (Vector 4)) n,
      singularHomologyMap (ContinuousMap.inclusion (inter_subset_left :
        singularComplementSet g ∩ P.openHoles ⊆ singularComplementSet g)) n b =
          P.boundaryDifference n a := by
  let E := homeomorphHomologyEquiv (complementHomeomorph g) n
  let F := homeomorphHomologyEquiv P.nonzeroOverlapHomeomorph n
  have hcomp : (subtypeInclusion (nonzeroComplementSet g)).comp
      (complementHomeomorph g : C(_, _)) = complementInNonzero g := by
    apply ContinuousMap.ext
    intro y
    rfl
  have hzero : singularHomologyMap (subtypeInclusion (nonzeroComplementSet g)) n
      (E (P.boundaryDifference n a)) = 0 := by
    change singularHomologyMap (subtypeInclusion (nonzeroComplementSet g)) n
      (singularHomologyMap (complementHomeomorph g : C(_, _)) n (P.boundaryDifference n a)) = 0
    rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, hcomp]
    exact P.boundaryDifference_inclusion_zero n a
  obtain ⟨b, hb, _⟩ := MayerVietorisInclusionRange.exists_intersection_lift_of_inclusion_zero
    (nonzeroComplementSet g) P.nonzeroHoles P.isOpen_nonzeroComplementSet
    P.isOpen_nonzeroHoles P.nonzero_complement_cover n (E (P.boundaryDifference n a)) hzero
  refine ⟨F.symm b, ?_⟩
  apply E.injective
  change singularHomologyMap (complementHomeomorph g : C(_, _)) n
      (singularHomologyMap (ContinuousMap.inclusion (inter_subset_left :
        singularComplementSet g ∩ P.openHoles ⊆ singularComplementSet g)) n (F.symm b)) =
          E (P.boundaryDifference n a)
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, ← P.nonzeroOverlap_comparison,
    singularHomologyMap_comp, LinearMap.comp_apply]
  change singularHomologyMap (ContinuousMap.inclusion (inter_subset_left :
    nonzeroComplementSet g ∩ P.nonzeroHoles ⊆ nonzeroComplementSet g)) n
      (F (F.symm b)) = E (P.boundaryDifference n a)
  rw [LinearEquiv.apply_symm_apply]
  exact hb

end NoExoticSixSphere.GenericFourAnnulus.ParityBallSystem
