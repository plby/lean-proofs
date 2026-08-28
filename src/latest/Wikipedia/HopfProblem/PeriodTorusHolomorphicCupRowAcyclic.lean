import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupRowCokernel
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultAcyclic
import Wikipedia.HopfProblem.SheafSingularCupComparisonResolutionBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionNaturality

/-!
# Original native cohomology comparisons for the acyclic Dolbeault row

The old smooth and pair sheaves are genuinely acyclic. Their original
partial-resolution comparisons agree with the old bounded-resolution
comparisons under the canonical kernel-zero and cokernel maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Row

open PeriodTorusHolomorphicCohomology
open CuspNormalization.SheafCohomologyResolution

variable (p : PeriodDomain)

theorem I0_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (partialResolution p).I₀ (n + 1)) :=
  Dolbeault.smooth_higher_subsingleton p n

theorem I1_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (partialResolution p).I₁ (n + 1)) :=
  Dolbeault.pair_higher_subsingleton p n

local instance originalH1 :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (Dolbeault.resolution p).complex.X₁ 1) :=
  Dolbeault.smooth_higher_subsingleton p 0

local instance originalH2 :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (Dolbeault.resolution p).complex.X₁ 2) :=
  Dolbeault.smooth_higher_subsingleton p 1

local instance originalPairH1 :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (Dolbeault.resolution p).complex.X₂ 1) :=
  Dolbeault.pair_higher_subsingleton p 0

local instance truncatedH1 :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (partialResolution p).toAugmented.complex.X₁ 1) :=
  Dolbeault.smooth_higher_subsingleton p 0

local instance truncatedH2 :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (partialResolution p).toAugmented.complex.X₁ 2) :=
  Dolbeault.smooth_higher_subsingleton p 1

local instance truncatedPairH1 :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (partialResolution p).toAugmented.complex.X₂ 1) :=
  Dolbeault.pair_higher_subsingleton p 0

/-- The original acyclic partial-resolution H¹ comparison, with actual vanishings supplied. -/
def h1Iso : AddCommGrpCat.of (H p 1) ≅ (oneComplex p).homology := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (partialResolution p).I₀ 1) :=
    I0_higher_subsingleton p 0
  exact (partialResolution p).h1IsoAcyclic

/-- The original acyclic partial-resolution H² comparison, with actual vanishings supplied. -/
def h2Iso : AddCommGrpCat.of (H p 2) ≅ (twoComplex p).homology := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (partialResolution p).I₀ 1) :=
    I0_higher_subsingleton p 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (partialResolution p).I₀ 2) :=
    I0_higher_subsingleton p 1
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (partialResolution p).I₁ 1) :=
    I1_higher_subsingleton p 0
  exact (partialResolution p).h2IsoAcyclic

/-- The augmentation of the actual truncation comparison induces the identity in every degree. -/
theorem toOriginal_cohomologyMap (n : ℕ) :
    (CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology p.Torus) n).map
        (toOriginal p).augmentation = 𝟙 (AddCommGrpCat.of (H p n)) :=
  (CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology p.Torus) n).map_id (holomorphicSheaf p)

/-- The degree-one map is exactly the original bounded-resolution map. -/
theorem h1Iso_hom_eq_original :
    (h1Iso p).hom = (Dolbeault.resolution p).h1Iso.hom := by
  have h := (toOriginal p).h1Iso_naturality
  change (partialResolution p).toAugmented.h1Iso.hom ≫
    ShortComplex.homologyMap (partialResolution p).globalTruncationInclusion = _
  exact h.symm.trans
    ((congrArg (fun f : AddCommGrpCat.of (H p 1) ⟶ AddCommGrpCat.of (H p 1) =>
      f ≫ (Dolbeault.resolution p).h1Iso.hom) (toOriginal_cohomologyMap p 1)).trans
        (Category.id_comp _))

/-- The degree-two map agrees with the old map under the actual kernel-zero cokernel comparison. -/
theorem h2Iso_hom_comp_original :
    (h2Iso p).hom ≫ (twoOriginalCokernelIso p).hom =
      (Dolbeault.resolution p).h2Iso.hom := by
  have h := (toOriginal p).h2Iso_naturality
  have hn : (partialResolution p).toAugmented.h2Iso.hom ≫
      (truncatedCokernelIso p).hom = (Dolbeault.resolution p).h2Iso.hom := by
    rw [truncatedCokernelIso_hom]
    exact h.symm.trans
      ((congrArg (fun f : AddCommGrpCat.of (H p 2) ⟶ AddCommGrpCat.of (H p 2) =>
        f ≫ (Dolbeault.resolution p).h2Iso.hom) (toOriginal_cohomologyMap p 2)).trans
          (Category.id_comp _))
  change ((partialResolution p).toAugmented.h2Iso.hom ≫
    (partialResolution p).globalTwoCokernelIso.hom) ≫
      ((partialResolution p).globalTwoCokernelIso.inv ≫ (truncatedCokernelIso p).hom) = _
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hn

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Row
