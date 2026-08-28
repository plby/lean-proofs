import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenDolbeaultResolution
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyLocallyFine

/-!
# Genuine acyclicity of the restricted smooth Dolbeault terms

Every actual open subset of the finite-dimensional affine space is a
sigma-compact smooth manifold. The genuine locally fine theorem gives
acyclicity of its actual smooth-function sheaf. The coefficient-pair
term splits by literal projections and inclusions; the actual additive
cohomology functor transfers the same vanishing to that term.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.OpenDolbeault

/-- Restricted pairs are literally pairs of actual smooth functions
on the open submanifold, via the proved nested-domain maps. -/
def pairSectionEquiv (Ω : Opens (ℂ × ℂ)) (W : Opens Ω) :
    AffineDolbeault.PairSection (HolomorphicRestriction.imageOpen Ω W) ≃ₗ[ℂ]
      (SmoothFunctions.Section 𝓘(ℝ, ℂ × ℂ) Ω W ×
        SmoothFunctions.Section 𝓘(ℝ, ℂ × ℂ) Ω W) :=
  (smoothSectionEquiv 𝓘(ℝ, ℂ × ℂ) Ω W).toLinearEquiv.prodCongr
    (smoothSectionEquiv 𝓘(ℝ, ℂ × ℂ) Ω W).toLinearEquiv

def pairFirst : AffineDolbeault.pairSheaf ⟶ AffineDolbeault.smoothSheaf where
  hom :=
    { app U := AddCommGrpCat.ofHom
        (AddMonoidHom.fst (AffineDolbeault.SmoothSection U.unop)
          (AffineDolbeault.SmoothSection U.unop))
      naturality _ _ _ := rfl }

def pairSecond : AffineDolbeault.pairSheaf ⟶ AffineDolbeault.smoothSheaf where
  hom :=
    { app U := AddCommGrpCat.ofHom
        (AddMonoidHom.snd (AffineDolbeault.SmoothSection U.unop)
          (AffineDolbeault.SmoothSection U.unop))
      naturality _ _ _ := rfl }

def includeFirst : AffineDolbeault.smoothSheaf ⟶ AffineDolbeault.pairSheaf where
  hom :=
    { app U := AddCommGrpCat.ofHom
        (AddMonoidHom.inl (AffineDolbeault.SmoothSection U.unop)
          (AffineDolbeault.SmoothSection U.unop))
      naturality _ _ _ := rfl }

def includeSecond : AffineDolbeault.smoothSheaf ⟶ AffineDolbeault.pairSheaf where
  hom :=
    { app U := AddCommGrpCat.ofHom
        (AddMonoidHom.inr (AffineDolbeault.SmoothSection U.unop)
          (AffineDolbeault.SmoothSection U.unop))
      naturality _ _ _ := rfl }

/-- The literal two coordinates split the actual pair sheaf. -/
theorem pair_split : pairFirst ≫ includeFirst + pairSecond ≫ includeSecond =
    𝟙 AffineDolbeault.pairSheaf := by
  apply AffineDolbeault.pairSheafEnd_ext
  intro U s
  exact Prod.ext (add_zero s.1) (zero_add s.2)

/-- Actual additive restriction retains the actual pair splitting. -/
theorem restricted_pair_split (Ω : Opens (ℂ × ℂ)) :
    (restriction Ω).map pairFirst ≫ (restriction Ω).map includeFirst +
      (restriction Ω).map pairSecond ≫ (restriction Ω).map includeSecond =
        𝟙 (restrictedPairSheaf Ω) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add, pair_split]
  exact (restriction Ω).map_id _

/-- Genuine higher acyclicity of restricted smooth functions, proved
using their actual smooth-open sheaf and real partitions of unity. -/
theorem restricted_smooth_higher_subsingleton (Ω : Opens (ℂ × ℂ)) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (restrictedSmoothSheaf Ω) (n + 1)) := by
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  let e := ((CategoryTheory.Sheaf.functorH _ (n + 1)).mapIso
    (smoothIso Ω)).addCommGroupIsoToAddEquiv
  have hs := SmoothFunctions.higher_subsingleton 𝓘(ℝ, ℂ × ℂ) Ω n
  exact ⟨fun a b => e.injective (hs.elim (e a) (e b))⟩

/-- Any actual additive functor respects the literal pair splitting. -/
theorem pair_functor_isZero
    (F : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of (ℂ × ℂ)) ⥤ AddCommGrpCat.{0})
    [F.Additive] (hS : IsZero (F.obj AffineDolbeault.smoothSheaf)) :
    IsZero (F.obj AffineDolbeault.pairSheaf) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  have he := congrArg F.map pair_split
  rw [F.map_add, F.map_comp, F.map_comp, F.map_id] at he
  have hp : F.map pairFirst = 0 := hS.eq_of_tgt _ _
  have hq : F.map pairSecond = 0 := hS.eq_of_tgt _ _
  rw [hp, hq, zero_comp, zero_comp, zero_add] at he
  exact he.symm

/-- The actual pair splitting and the actual additive cohomology functor
give genuine higher acyclicity of the restricted form term. -/
theorem restricted_pair_higher_subsingleton (Ω : Opens (ℂ × ℂ)) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (restrictedPairSheaf Ω) (n + 1)) := by
  let F : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of (ℂ × ℂ)) ⥤ AddCommGrpCat.{0} :=
    restriction Ω ⋙ CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Ω) (n + 1)
  let : F.Additive := by
    let G : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of Ω) ⥤ AddCommGrpCat.{0} :=
      CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Ω) (n + 1)
    let : G.Additive := CategoryTheory.Sheaf.instAdditiveAddCommGrpCatFunctorH (n + 1)
    exact Functor.instAdditiveComp (restriction Ω) G
  let : Subsingleton (F.obj AffineDolbeault.smoothSheaf) :=
    restricted_smooth_higher_subsingleton Ω n
  exact AddCommGrpCat.subsingleton_of_isZero
    (pair_functor_isZero F (AddCommGrpCat.isZero_of_subsingleton _))

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.OpenDolbeault
