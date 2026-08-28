import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyThreeCoverNaturality
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyThreeCoverSections

/-!
# Actual section representatives for genuine Mayer--Vietoris classes

The canonical Ext-zero/sections equivalence turns the original connecting
map into a map on literal sections. Exactness, surjectivity, and open-set
naturality are proved for this map, rather than postulated.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ThreeCover

open OpenRestriction

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X) (A B : Opens X)

/-- The genuine connecting map with its canonical actual-section representatives. -/
def sectionConnecting : Sections F (A ⊓ B) →+
    CategoryTheory.Sheaf.H'.{0} F 1 (A ⊔ B) :=
  (MayerVietoris.connecting F A B 0).hom.comp (zeroEquiv (A ⊓ B) F).symm.toAddMonoidHom

theorem sectionConnecting_exact :
    Function.Exact (MayerVietoris.sectionsDifference F A B) (sectionConnecting F A B) := by
  intro s
  constructor
  · intro hs
    let x := (zeroEquiv (A ⊓ B) F).symm s
    obtain ⟨z, hz⟩ := ((MayerVietoris.intersectionComplex F A B 0).ab_exact_iff.mp
      (MayerVietoris.intersectionComplex_exact F A B 0)) x hs
    obtain ⟨⟨a, b⟩, rfl⟩ :=
      (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.symm.surjective z
    refine ⟨(zeroEquiv A F a, zeroEquiv B F b), ?_⟩
    exact Eq.trans (MayerVietoris.zeroEquiv_restrictionDifference F A B a b).symm
      (Eq.trans (congrArg (zeroEquiv (A ⊓ B) F) hz)
        ((zeroEquiv (A ⊓ B) F).apply_symm_apply s))
  · rintro ⟨⟨a, b⟩, rfl⟩
    let z := (AddCommGrpCat.biprodIsoProd
      (CategoryTheory.Sheaf.H'.{0} F 0 (MayerVietoris.square A B).X₂)
      (CategoryTheory.Sheaf.H'.{0} F 0 (MayerVietoris.square A B).X₃)).inv
      ⟨(zeroEquiv A F).symm a, (zeroEquiv B F).symm b⟩
    have hz : MayerVietoris.restrictionDifference F A B 0 z =
        (zeroEquiv (A ⊓ B) F).symm (MayerVietoris.sectionsDifference F A B (a, b)) := by
      apply (zeroEquiv (A ⊓ B) F).injective
      simpa only [z, AddEquiv.apply_symm_apply] using
        MayerVietoris.zeroEquiv_restrictionDifference F A B
          ((zeroEquiv A F).symm a) ((zeroEquiv B F).symm b)
    exact Eq.trans (congrArg (MayerVietoris.connecting F A B 0) hz.symm)
      (ConcreteCategory.congr_hom ((MayerVietoris.square A B).fromBiprod_δ F 0 1 rfl) z)

theorem sectionConnecting_difference (a : Sections F A) (b : Sections F B) :
    sectionConnecting F A B (MayerVietoris.sectionsDifference F A B (a, b)) = 0 :=
  (sectionConnecting_exact F A B _).mpr ⟨(a, b), rfl⟩

/-- Chart H¹ vanishing gives actual section representatives for every union class. -/
theorem sectionConnecting_surjective
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 A)]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 B)] :
    Function.Surjective (sectionConnecting F A B) :=
  (MayerVietoris.connecting_surjective F A B 0).comp
    (zeroEquiv (A ⊓ B) F).symm.surjective

variable {A B}

theorem zeroEquiv_symm_restrict {D E : Opens X} (h : D ≤ E) (s : Sections F E) :
    cohomologyRestrict F 0 h ((zeroEquiv E F).symm s) =
      (zeroEquiv D F).symm (sectionRestrict F h s) := by
  apply (zeroEquiv D F).injective
  simpa only [AddEquiv.apply_symm_apply] using
    MayerVietoris.zeroEquiv_naturality_open (homOfLE h) F ((zeroEquiv E F).symm s)

/-- The actual section connecting map commutes with actual inclusions of pairs of opens. -/
theorem sectionConnecting_naturality {U V : Opens X} (hA : A ≤ U) (hB : B ≤ V)
    (s : Sections F (U ⊓ V)) :
    cohomologyRestrict F 1 (sup_le_sup hA hB) (sectionConnecting F U V s) =
      sectionConnecting F A B (sectionRestrict F (inf_le_inf hA hB) s) :=
  Eq.trans (connecting_naturality F hA hB 0 ((zeroEquiv (U ⊓ V) F).symm s))
    (congrArg (MayerVietoris.connecting F A B 0)
      (zeroEquiv_symm_restrict F (inf_le_inf hA hB) s))

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ThreeCover
