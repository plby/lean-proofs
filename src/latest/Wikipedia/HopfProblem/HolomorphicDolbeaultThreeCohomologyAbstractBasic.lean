import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionSections

/-!
# The native degree-one connecting map on actual global sections

For a genuine short exact sequence of abelian sheaves, the map below is
Mathlib's degree-zero global-section comparison followed by its actual Ext
connecting morphism.  Its kernel consists exactly of global sections lifted
through the middle sheaf.  Surjectivity needs only actual degree-one
acyclicity of that middle sheaf.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.CohomologyAbstract

open CuspNormalization.SheafCohomologyResolution

variable {X : TopCat.{0}}

/-- Literal sections of the original sheaf on the top open set. -/
abbrev Sections (F : TopCat.Sheaf AddCommGrpCat.{0} X) : Type :=
  F.obj.obj (op (⊤ : Opens X))

/-- The original sheaf morphism, evaluated on the top open set. -/
def sectionMap {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f : F ⟶ G) :
    Sections F →+ Sections G := (f.hom.app (op ⊤)).hom

@[simp] theorem sectionMap_apply {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (f : F ⟶ G) (s : Sections F) : sectionMap f s = f.hom.app (op ⊤) s := rfl

/-- The canonical native degree-zero comparison, not a chosen vector-space
identification. -/
def zeroEquiv (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    CategoryTheory.Sheaf.H.{0} F 0 ≃+ Sections F :=
  CategoryTheory.Sheaf.H.equiv₀ F
    (show IsTerminal (⊤ : Opens X) from isTerminalTop)

theorem zeroEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (f : F ⟶ G) (s : CategoryTheory.Sheaf.H.{0} F 0) :
    sectionMap f (zeroEquiv F s) = zeroEquiv G (CategoryTheory.Sheaf.H.map f 0 s) :=
  CategoryTheory.Sheaf.H.equiv₀_naturality
    (show IsTerminal (⊤ : Opens X) from isTerminalTop) f s

theorem zeroEquiv_symm_naturality {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (f : F ⟶ G) (s : Sections F) :
    CategoryTheory.Sheaf.H.map f 0 ((zeroEquiv F).symm s) =
      (zeroEquiv G).symm (sectionMap f s) :=
  CategoryTheory.Sheaf.H.equiv₀_symm_naturality
    (show IsTerminal (⊤ : Opens X) from isTerminalTop) f s

variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}

/-- The genuine positive connecting class of an actual top-open section. -/
def classMap (hS : S.ShortExact) :
    Sections S.X₃ →+ CategoryTheory.Sheaf.H.{0} S.X₁ 1 :=
  (connecting (unitSheaf X) hS 0).comp (zeroEquiv S.X₃).symm.toAddMonoidHom

/-- The forward map uses exactly the original degree-zero comparison and the
original extension class of the specified short exact sequence. -/
theorem classMap_apply (hS : S.ShortExact) (s : Sections S.X₃) :
    classMap hS s =
      ((CategoryTheory.Sheaf.H.equiv₀ S.X₃
        (show IsTerminal (⊤ : Opens X) from isTerminalTop)).symm s).comp
          hS.extClass rfl := rfl

@[simp] theorem classMap_zeroEquiv (hS : S.ShortExact)
    (s : CategoryTheory.Sheaf.H.{0} S.X₃ 0) :
    classMap hS (zeroEquiv S.X₃ s) = connecting (unitSheaf X) hS 0 s := by
  change connecting (unitSheaf X) hS 0 ((zeroEquiv S.X₃).symm (zeroEquiv S.X₃ s)) = _
  rw [AddEquiv.symm_apply_apply]

/-- In particular, a degree-zero morphism has its literal Yoneda connecting
class, with no sign change. -/
theorem classMap_hom (hS : S.ShortExact) (a : unitSheaf X ⟶ S.X₃) :
    classMap hS (zeroEquiv S.X₃ (Ext.mk₀ a)) = (Ext.mk₀ a).comp hS.extClass rfl := by
  rw [classMap_zeroEquiv]
  rfl

/-- Exactness of the actual section map immediately before the genuine
degree-one connecting map. -/
theorem classMap_exact (hS : S.ShortExact) :
    Function.Exact (sectionMap S.g) (classMap hS) := by
  intro s
  constructor
  · intro hs
    change connecting (unitSheaf X) hS 0 ((zeroEquiv S.X₃).symm s) = 0 at hs
    obtain ⟨a, ha⟩ := (connecting_exact (unitSheaf X) hS 0 _).mp hs
    refine ⟨zeroEquiv S.X₂ a, ?_⟩
    have ha' : CategoryTheory.Sheaf.H.map S.g 0 a = (zeroEquiv S.X₃).symm s := ha
    exact (zeroEquiv_naturality S.g a).trans
      ((congrArg (zeroEquiv S.X₃) ha').trans ((zeroEquiv S.X₃).apply_symm_apply s))
  · rintro ⟨a, rfl⟩
    change connecting (unitSheaf X) hS 0
      ((zeroEquiv S.X₃).symm (sectionMap S.g a)) = 0
    rw [← zeroEquiv_symm_naturality]
    exact (connecting_exact (unitSheaf X) hS 0 _).mpr
      ⟨(zeroEquiv S.X₂).symm a, rfl⟩

theorem classMap_eq_zero_iff (hS : S.ShortExact) (s : Sections S.X₃) :
    classMap hS s = 0 ↔ ∃ a : Sections S.X₂, sectionMap S.g a = s :=
  classMap_exact hS s

theorem classMap_ker (hS : S.ShortExact) :
    (classMap hS).ker = (sectionMap S.g).range := by
  ext s
  exact classMap_eq_zero_iff hS s

/-- Only genuine `H¹`-vanishing of the middle sheaf is required for every
degree-one class to have an actual global-section representative. -/
theorem classMap_surjective (hS : S.ShortExact)
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.X₂ 1)] :
    Function.Surjective (classMap hS) := by
  let : Subsingleton (Ext.{0} (unitSheaf X) S.X₂ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} S.X₂ 1)›
  exact (connecting_surjective (unitSheaf X) hS 0).comp (zeroEquiv S.X₃).symm.surjective

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.CohomologyAbstract
