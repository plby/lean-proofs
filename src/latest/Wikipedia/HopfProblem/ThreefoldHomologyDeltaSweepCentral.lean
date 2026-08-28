import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepCentralCover
import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepGlobal

/-!
# The genuine central-surface delta sweep and its finite-cover comparison

The sweep is the actual positive-circle cross product followed by the
original central action. Naturality of the native global inclusion shows
that every swept central one-class dies in the global second homology.
The original finite period-torus cover gives the exact Pontryagin-product
formula before any homology coordinates or duality are used.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep

open Elliptic EllipticFilling FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

/-- Sweep on the original special central quotient surface by its
actual period-one positive delta action. -/
def centralSweep (j : Kind) (n : ℕ) :
    SingularHomology (SpecialCentralSurface j) n →ₗ[ℤ]
      SingularHomology (SpecialCentralSurface j) (n + 1) :=
  sweep (centralActionMap j) n

@[simp] theorem centralSweep_apply (j : Kind) (n : ℕ)
    (v : SingularHomology (SpecialCentralSurface j) n) :
    centralSweep j n v = singularHomologyMap (centralActionMap j) (n + 1)
      (positiveCircleCross (SpecialCentralSurface j) n v) := rfl

/-- The original central-surface inclusion intertwines the actual
central and global sweeps on singular homology in every degree. -/
theorem globalSweep_centralInclusion (j : Kind) (n : ℕ)
    (v : SingularHomology (SpecialCentralSurface j) n) :
    globalSweep n (singularHomologyMap (centralInclusionMap j) n v) =
      singularHomologyMap (centralInclusionMap j) (n + 1) (centralSweep j n v) :=
  sweep_natural_of_equivariant (centralActionMap j) actionMap (centralInclusionMap j)
    (actionMap_centralInclusion j) n v

/-- Every genuine swept central one-class dies in global second
homology, by the proved vanishing of the original global first homology. -/
theorem centralSweep_global_eq_zero (j : Kind)
    (v : SingularHomology (SpecialCentralSurface j) 1) :
    singularHomologyMap (centralInclusionMap j) 2 (centralSweep j 1 v) = 0 := by
  rw [← globalSweep_centralInclusion j 1 v]
  exact globalSweep_one_apply_eq_zero _

/-- The genuine finite cover in fixed real coordinates identifies
the central sweep with the positive delta-left Pontryagin product. -/
theorem centralSweep_flatPeriodCover (j : Kind) (n : ℕ)
    (v : SingularHomology RealTorus₄ n) :
    centralSweep j n (singularHomologyMap (centralFlatPeriodCover j) n v) =
      singularHomologyMap (centralFlatPeriodCover j) (n + 1)
        (PeriodTorusHigherHomologyPontryagin.product RealTorus₄ n
          (TrianglePeriodFamily.FlatTorus.singularH1Equiv.symm deltaLattice) v) := by
  have h := sweep_equivariant_addition (centralActionMap j) deltaCircle
    (centralFlatPeriodCover j) (centralActionMap_flatPeriodCover j) n v
  rw [deltaCircle_positiveLoop_singularHomology] at h
  exact h

/-- The same exact comparison through the original complex period
torus and its original finite covering, without coordinate replacement. -/
theorem centralSweep_periodCover (j : Kind) (n : ℕ)
    (v : SingularHomology (SpecialCentralPeriodTorus j) n) :
    centralSweep j n (singularHomologyMap (specialCentralPeriodCover j) n v) =
      singularHomologyMap (specialCentralPeriodCover j) (n + 1)
        (PeriodTorusHigherHomologyPontryagin.product (SpecialCentralPeriodTorus j) n
          (singularHomologyMap (centralPeriodDeltaCircle j) 1
            (loopHomologyClass CirclePaths.positiveLoop)) v) :=
  sweep_equivariant_addition (centralActionMap j) (centralPeriodDeltaCircle j)
    (specialCentralPeriodCover j) (centralActionMap_periodCover j) n v

/-- Delta-left products from the actual central finite cover have
zero image in the actual global second homology. -/
theorem centralFlatPeriodCover_delta_product_global_eq_zero (j : Kind)
    (v : SingularHomology RealTorus₄ 1) :
    singularHomologyMap (centralInclusionMap j) 2
      (singularHomologyMap (centralFlatPeriodCover j) 2
        (PeriodTorusHigherHomologyPontryagin.product11 RealTorus₄
          (TrianglePeriodFamily.FlatTorus.singularH1Equiv.symm deltaLattice) v)) = 0 := by
  rw [← centralSweep_flatPeriodCover j 1 v]
  exact centralSweep_global_eq_zero j _

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep
