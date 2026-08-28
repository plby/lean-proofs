import Wikipedia.HopfProblem.EllipticHigherHomologyDeckHomologyCoordinates
import Wikipedia.HopfProblem.EllipticHigherHomologyDeckHomologyProduct

/-!
# The actual elliptic deck action in adjacent-degree homology coordinates

The known affine conjugacy identifies the actual deck transformation with
a circle translation times the actual fibre automorphism.  The explicit
translation homotopy and the proved circle-product naturality theorem then
give its diagonal action on actual integral homology.  Inverting the genuine
homology equivalences gives the inverse-generator formula.  Consequently
the actual difference `id - H(deck⁻¹)` is the pair of actual Wang differences.
Bundled product maps use the canonical integral module structure explicitly.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology CircleTopology
open MappingTorusHomology DeckHomology

/-- The proved affine-coordinate formula is an equality of the actual continuous maps. -/
theorem splitPeriodTorusHomeomorph_comp_affine (j : Kind) (p : FixedPeriod j) :
    (splitPeriodTorusHomeomorph j p.val :
        C(p.val.Torus, CircleTopology.Circle × ProductTorus 3)).comp
        (periodAffineHomeomorph j p : C(p.val.Torus, p.val.Torus)) =
      (translatedProductMap (1 / (j.order : ℝ))
        (fibreTorusHomeomorph j : C(ProductTorus 3, ProductTorus 3))).comp
          (splitPeriodTorusHomeomorph j p.val :
            C(p.val.Torus, CircleTopology.Circle × ProductTorus 3)) := by
  apply ContinuousMap.ext
  intro x
  exact splitPeriodTorusHomeomorph_affineBiholomorph j p x

/-- The circle translation disappears on actual homology by the explicit homotopy. -/
theorem splitPeriodTorusHomology_affine_map (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    (homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) n).toLinearMap.comp
        (singularHomologyMap (periodAffineHomeomorph j p : C(p.val.Torus, p.val.Torus)) n) =
      (singularHomologyMap
        (circleProductMap (fibreTorusHomeomorph j : C(ProductTorus 3, ProductTorus 3))) n).comp
          (homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) n).toLinearMap := by
  simp only [homeomorphHomologyEquiv_toLinearMap]
  rw [← singularHomologyMap_comp, splitPeriodTorusHomeomorph_comp_affine,
    singularHomologyMap_comp, translatedProductMap_homologyMap]

theorem splitPeriodTorusHomology_affine (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (a : SingularHomology p.val.Torus n) :
    homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) n
        (singularHomologyMap (periodAffineHomeomorph j p : C(p.val.Torus, p.val.Torus)) n a) =
      singularHomologyMap
        (circleProductMap (fibreTorusHomeomorph j : C(ProductTorus 3, ProductTorus 3))) n
          (homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) n a) :=
  DFunLike.congr_fun (splitPeriodTorusHomology_affine_map j p n) a

/-- In the actual period-circle coordinates the generator acts diagonally by the
actual fibre homology maps, in every pair of adjacent degrees. -/
theorem periodCircleHomologyEquiv_affine (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (a : SingularHomology p.val.Torus (n + 1)) :
    periodCircleHomologyEquiv j p n
        (singularHomologyMap (periodAffineHomeomorph j p : C(p.val.Torus, p.val.Torus))
          (n + 1) a) =
      (singularHomologyMap (fibreTorusHomeomorph j : C(ProductTorus 3, ProductTorus 3))
          (n + 1) (periodCircleHomologyEquiv j p n a).1,
        singularHomologyMap (fibreTorusHomeomorph j : C(ProductTorus 3, ProductTorus 3))
          n (periodCircleHomologyEquiv j p n a).2) := by
  change circleProductHomologyEquiv (ProductTorus 3) n
    (homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) (n + 1)
      (singularHomologyMap (periodAffineHomeomorph j p : C(p.val.Torus, p.val.Torus))
        (n + 1) a)) = _
  rw [splitPeriodTorusHomology_affine]
  exact circleProductHomologyEquiv_naturality
    (fibreTorusHomeomorph j : C(ProductTorus 3, ProductTorus 3)) n _

theorem periodCircleHomologyEquiv_affine_map (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    (periodCircleHomologyEquiv j p n).toLinearMap.comp
        (singularHomologyMap (periodAffineHomeomorph j p : C(p.val.Torus, p.val.Torus))
          (n + 1)) =
      ((singularHomologyMap (fibreTorusHomeomorph j : C(ProductTorus 3, ProductTorus 3))
          (n + 1)).toAddMonoidHom.prodMap
        (singularHomologyMap (fibreTorusHomeomorph j : C(ProductTorus 3, ProductTorus 3))
          n).toAddMonoidHom).toIntLinearMap.comp
            (periodCircleHomologyEquiv j p n).toLinearMap := by
  apply LinearMap.ext
  intro a
  exact periodCircleHomologyEquiv_affine j p n a

/-- The inverse actual generator acts by the inverse actual fibre maps;
this follows by inverting the genuine homology equivalences. -/
theorem periodCircleHomologyEquiv_affine_symm (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (a : SingularHomology p.val.Torus (n + 1)) :
    periodCircleHomologyEquiv j p n
        (singularHomologyMap ((periodAffineHomeomorph j p).symm :
          C(p.val.Torus, p.val.Torus)) (n + 1) a) =
      (singularHomologyMap ((fibreTorusHomeomorph j).symm :
          C(ProductTorus 3, ProductTorus 3)) (n + 1) (periodCircleHomologyEquiv j p n a).1,
        singularHomologyMap ((fibreTorusHomeomorph j).symm :
          C(ProductTorus 3, ProductTorus 3)) n (periodCircleHomologyEquiv j p n a).2) := by
  let A := homeomorphHomologyEquiv (periodAffineHomeomorph j p) (n + 1)
  let D := (homeomorphHomologyEquiv (fibreTorusHomeomorph j) (n + 1)).prodCongr
    (homeomorphHomologyEquiv (fibreTorusHomeomorph j) n)
  have h := periodCircleHomologyEquiv_affine j p n (A.symm a)
  change periodCircleHomologyEquiv j p n (A (A.symm a)) =
    D (periodCircleHomologyEquiv j p n (A.symm a)) at h
  rw [LinearEquiv.apply_symm_apply] at h
  change periodCircleHomologyEquiv j p n (A.symm a) =
    D.symm (periodCircleHomologyEquiv j p n a)
  apply D.injective
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

theorem periodCircleHomologyEquiv_affine_symm_map (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    (periodCircleHomologyEquiv j p n).toLinearMap.comp
        (singularHomologyMap ((periodAffineHomeomorph j p).symm :
          C(p.val.Torus, p.val.Torus)) (n + 1)) =
      ((singularHomologyMap ((fibreTorusHomeomorph j).symm :
          C(ProductTorus 3, ProductTorus 3)) (n + 1)).toAddMonoidHom.prodMap
        (singularHomologyMap ((fibreTorusHomeomorph j).symm :
          C(ProductTorus 3, ProductTorus 3)) n).toAddMonoidHom).toIntLinearMap.comp
            (periodCircleHomologyEquiv j p n).toLinearMap := by
  apply LinearMap.ext
  intro a
  exact periodCircleHomologyEquiv_affine_symm j p n a

/-- The difference for the actual inverse deck generator on original period-torus homology. -/
def periodDeckDifference (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    SingularHomology p.val.Torus n →ₗ[ℤ] SingularHomology p.val.Torus n :=
  LinearMap.id - singularHomologyMap
    ((periodAffineHomeomorph j p).symm : C(p.val.Torus, p.val.Torus)) n

@[simp] theorem periodDeckDifference_apply (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (a : SingularHomology p.val.Torus n) :
    periodDeckDifference j p n a = a - singularHomologyMap
      ((periodAffineHomeomorph j p).symm : C(p.val.Torus, p.val.Torus)) n a := rfl

/-- The actual inverse-deck difference is literally the pair of adjacent Wang operators. -/
theorem periodCircleHomologyEquiv_periodDeckDifference (j : Kind) (p : FixedPeriod j)
    (n : ℕ) (a : SingularHomology p.val.Torus (n + 1)) :
    periodCircleHomologyEquiv j p n (periodDeckDifference j p (n + 1) a) =
      (wangDifference (fibreTorusHomeomorph j).symm (n + 1)
          (periodCircleHomologyEquiv j p n a).1,
        wangDifference (fibreTorusHomeomorph j).symm n
          (periodCircleHomologyEquiv j p n a).2) := by
  rw [periodDeckDifference_apply, map_sub, periodCircleHomologyEquiv_affine_symm]
  rfl

theorem periodCircleHomologyEquiv_periodDeckDifference_map (j : Kind) (p : FixedPeriod j)
    (n : ℕ) :
    (periodCircleHomologyEquiv j p n).toLinearMap.comp (periodDeckDifference j p (n + 1)) =
      ((wangDifference (fibreTorusHomeomorph j).symm (n + 1)).toAddMonoidHom.prodMap
        (wangDifference (fibreTorusHomeomorph j).symm n).toAddMonoidHom).toIntLinearMap.comp
          (periodCircleHomologyEquiv j p n).toLinearMap := by
  apply LinearMap.ext
  intro a
  exact periodCircleHomologyEquiv_periodDeckDifference j p n a

end Wikipedia.HopfProblem.Elliptic.HigherHomology
