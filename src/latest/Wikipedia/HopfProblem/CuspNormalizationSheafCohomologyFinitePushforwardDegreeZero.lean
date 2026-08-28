import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardComparison

/-!
# Degree-zero compatibility of the genuine cohomology comparison

The all-degree equivalence agrees in degree zero with Mathlib's canonical
`Sheaf.H.equiv₀` and the literal global-section identification. Thus its
degree-zero action is the actual global-section map, not an arbitrary
isomorphism of abstract cohomology groups.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyFinitePushforward

/-- The representing-morphism equivalence is the genuine canonical
degree-zero cohomology comparison on degree-zero Ext classes. -/
theorem homGlobalEquiv_mk₀ {X : TopCat.{0}} (F : AbelianSheaf X)
    (h : integerSheaf X ⟶ F) :
    CategoryTheory.Sheaf.H.equiv₀ F
        (show IsTerminal (⊤ : Opens X) from isTerminalTop) (Ext.mk₀ h) =
      homGlobalEquiv X F h :=
  congrArg (homGlobalEquiv X F)
    ((Ext.addEquiv₀ (X := integerSheaf X) (Y := F)).apply_symm_apply h)

variable {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)

/-- The canonical forward cohomology map on actual degree-zero classes. -/
theorem cohomologyForward_mk₀ (F : AbelianSheaf X) (h : integerSheaf X ⟶ F) :
    cohomologyForward f hf hfinite F 0 (Ext.mk₀ h) =
      Ext.mk₀ (integerUnit f ≫ (pushforward f).map h) := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let _ := pushforward_preservesFiniteColimits f hf hfinite
  exact ExtComparison.comparison_mk₀ (C := AbelianSheaf X) (D := AbelianSheaf Y)
    (pushforward f) (integerUnit f) h

/-- The forward comparison preserves the literal actual global section. -/
theorem cohomologyForward_zero_global (F : AbelianSheaf X)
    (e : CategoryTheory.Sheaf.H.{0} F 0) :
    CategoryTheory.Sheaf.H.equiv₀ ((pushforward f).obj F)
        (show IsTerminal (⊤ : Opens Y) from isTerminalTop)
        (cohomologyForward f hf hfinite F 0 e) =
      CategoryTheory.Sheaf.H.equiv₀ F
        (show IsTerminal (⊤ : Opens X) from isTerminalTop) e := by
  obtain ⟨h, rfl⟩ := (Ext.mk₀_bijective (integerSheaf X) F).surjective e
  exact (congrArg
    (CategoryTheory.Sheaf.H.equiv₀ ((pushforward f).obj F)
      (show IsTerminal (⊤ : Opens Y) from isTerminalTop))
    (cohomologyForward_mk₀ f hf hfinite F h)).trans
      ((homGlobalEquiv_mk₀ ((pushforward f).obj F)
        (integerUnit f ≫ (pushforward f).map h)).trans
        ((congrArg (homGlobalEquiv Y ((pushforward f).obj F)) (integerUnit_comp f h)).trans
          ((homPushforwardEquiv_global f F h).trans (homGlobalEquiv_mk₀ F h).symm)))

/-- In degree zero the actual inverse cohomology equivalence is the
literal identity on global sections of the actual pushforward. -/
theorem cohomologyEquiv_zero_global (F : AbelianSheaf X)
    (e : CategoryTheory.Sheaf.H.{0} ((pushforward f).obj F) 0) :
    CategoryTheory.Sheaf.H.equiv₀ F
        (show IsTerminal (⊤ : Opens X) from isTerminalTop)
        (cohomologyEquiv f hf hfinite F 0 e) =
      globalSectionsEquiv f F
        (CategoryTheory.Sheaf.H.equiv₀ ((pushforward f).obj F)
          (show IsTerminal (⊤ : Opens Y) from isTerminalTop) e) :=
  (cohomologyForward_zero_global f hf hfinite F (cohomologyEquiv f hf hfinite F 0 e)).symm.trans
    (congrArg
      (CategoryTheory.Sheaf.H.equiv₀ ((pushforward f).obj F)
        (show IsTerminal (⊤ : Opens Y) from isTerminalTop))
      (cohomologyForward_equiv f hf hfinite F 0 e))

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyFinitePushforward
