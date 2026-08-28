import Wikipedia.HopfProblem.CuspNormalizationSheafNormalizationStalk
import Wikipedia.HopfProblem.CuspNormalizationSheafCurveStalkBasic

/-!
# Actual signed sheaf maps on categorical stalks

These are the actual stalk-functor images of the two signed pullbacks
and their difference. Their formulas use literal categorical section
germs and the actual additive structure on the stalks.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCurveStalk

open CuspQuotient ToricCharts ToricSpace SheafResolution

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual positive sheaf pullback evaluated by the actual stalk functor. -/
def plusStalkMap (k : Fin 3) (x : CentralSpace C ε) :
    (normalizationSheaf C ε hε).presheaf.stalk x →+
      (curveSheaf C ε hε hε1 hC hR k).presheaf.stalk x :=
  ((TopCat.Presheaf.stalkFunctor (X := TopCat.of (CentralSpace C ε)) AddCommGrpCat x).map
    (plusPullback C ε hε hε1 hC hR k).hom).hom

/-- The actual negative sheaf pullback evaluated by the actual stalk functor. -/
def minusStalkMap (k : Fin 3) (x : CentralSpace C ε) :
    (normalizationSheaf C ε hε).presheaf.stalk x →+
      (curveSheaf C ε hε hε1 hC hR k).presheaf.stalk x :=
  ((TopCat.Presheaf.stalkFunctor (X := TopCat.of (CentralSpace C ε)) AddCommGrpCat x).map
    (minusPullback C ε hε hε1 hC hR k).hom).hom

/-- The actual signed boundary sheaf morphism evaluated on actual stalks. -/
def boundaryStalkMap (k : Fin 3) (x : CentralSpace C ε) :
    (normalizationSheaf C ε hε).presheaf.stalk x →+
      (curveSheaf C ε hε hε1 hC hR k).presheaf.stalk x :=
  ((TopCat.Presheaf.stalkFunctor (X := TopCat.of (CentralSpace C ε)) AddCommGrpCat x).map
    (boundaryDifference C ε hε hε1 hC hR k).hom).hom

/-- Stalks preserve the literal difference defining the actual boundary. -/
theorem boundaryStalkMap_eq (k : Fin 3) (x : CentralSpace C ε) :
    boundaryStalkMap C ε hε hε1 hC hR k x =
      plusStalkMap C ε hε hε1 hC hR k x - minusStalkMap C ε hε hε1 hC hR k x := by
  apply AddMonoidHom.ext
  intro φ
  obtain ⟨U, hxU, f, rfl⟩ := (normalizationSheaf C ε hε).presheaf.exists_germ_eq φ
  change ((TopCat.Presheaf.stalkFunctor
      (X := TopCat.of (CentralSpace C ε)) AddCommGrpCat x).map
        (boundaryDifference C ε hε hε1 hC hR k).hom)
      ((normalizationSheaf C ε hε).presheaf.germ U x hxU f) =
    ((TopCat.Presheaf.stalkFunctor
      (X := TopCat.of (CentralSpace C ε)) AddCommGrpCat x).map
        (plusPullback C ε hε hε1 hC hR k).hom)
      ((normalizationSheaf C ε hε).presheaf.germ U x hxU f) -
    ((TopCat.Presheaf.stalkFunctor
      (X := TopCat.of (CentralSpace C ε)) AddCommGrpCat x).map
        (minusPullback C ε hε hε1 hC hR k).hom)
      ((normalizationSheaf C ε hε).presheaf.germ U x hxU f)
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply]
  exact map_sub ((curveSheaf C ε hε hε1 hC hR k).presheaf.germ U x hxU).hom _ _

@[simp] theorem plusStalkMap_germ (k : Fin 3) (x : CentralSpace C ε)
    (U : Opens (CentralSpace C ε)) (hxU : x ∈ U)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)
      ((Opens.map (normalizationMap C ε hε)).obj U)) :
    plusStalkMap C ε hε hε1 hC hR k x
        ((normalizationSheaf C ε hε).presheaf.germ U x hxU f) =
      (curveSheaf C ε hε hε1 hC hR k).presheaf.germ U x hxU
        ((plusPullback C ε hε hε1 hC hR k).hom.app (op U) f) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply
    (X := TopCat.of (CentralSpace C ε)) (C := AddCommGrpCat) U x hxU
    (plusPullback C ε hε hε1 hC hR k).hom f

@[simp] theorem minusStalkMap_germ (k : Fin 3) (x : CentralSpace C ε)
    (U : Opens (CentralSpace C ε)) (hxU : x ∈ U)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)
      ((Opens.map (normalizationMap C ε hε)).obj U)) :
    minusStalkMap C ε hε hε1 hC hR k x
        ((normalizationSheaf C ε hε).presheaf.germ U x hxU f) =
      (curveSheaf C ε hε hε1 hC hR k).presheaf.germ U x hxU
        ((minusPullback C ε hε hε1 hC hR k).hom.app (op U) f) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply
    (X := TopCat.of (CentralSpace C ε)) (C := AddCommGrpCat) U x hxU
    (minusPullback C ε hε hε1 hC hR k).hom f

end Wikipedia.HopfProblem.CuspNormalization.SheafCurveStalk
