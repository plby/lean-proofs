import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardExt
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardGlobal

/-!
# Genuine sheaf cohomology of finite closed pushforward

The exactness and preservation of injectives proved for the actual
pushforward functor extend the canonical global-section comparison to
all of Mathlib's actual Ext-defined sheaf cohomology groups. The resulting
equivalence is natural for the actual `Sheaf.H.map` and agrees in degree
zero with the literal equality of global sections.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyFinitePushforward

/-- The same actual small Ext instance in the native site-sheaf presentation. -/
instance nativeSheaf_hasExt (X : TopCat.{0}) :
    HasExt.{0} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  abelianSheaf_hasExt X

/-- The group structure is precisely the existing group structure of genuine Ext. -/
instance cohomologyAddCommGroup {X : TopCat.{0}} (F : AbelianSheaf X) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} F n) := Ext.instAddCommGroup

/-- The same existing Ext group structure for explicitly bundled spaces. -/
instance cohomologyAddCommGroupOfType {M : Type} [TopologicalSpace M]
    (F : AbelianSheaf (TopCat.of M)) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} F n) := Ext.instAddCommGroup

variable {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)

/-- The canonical actual Ext map from a sheaf to its finite closed pushforward. -/
def cohomologyForward (F : AbelianSheaf X) (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} F n →+
      CategoryTheory.Sheaf.H.{0} ((pushforward f).obj F) n := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let _ := pushforward_preservesFiniteColimits f hf hfinite
  exact ExtComparison.comparison (pushforward f) (integerUnit f) F n

/-- The genuine cohomology comparison is bijective in every degree. -/
theorem cohomologyForward_bijective (F : AbelianSheaf X) (n : ℕ) :
    Function.Bijective (cohomologyForward f hf hfinite F n) := by
  let _ := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let _ := pushforward_preservesFiniteColimits f hf hfinite
  let _ := pushforward_preservesInjectiveObjects f
  exact ExtComparison.comparison_bijective (pushforward f) (integerUnit f)
    (integerUnit_bijective f) F n

/-- Actual finite closed pushforward does not change actual sheaf cohomology. -/
def cohomologyEquiv (F : AbelianSheaf X) (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} ((pushforward f).obj F) n ≃+
      CategoryTheory.Sheaf.H.{0} F n :=
  (AddEquiv.ofBijective (cohomologyForward f hf hfinite F n)
    (cohomologyForward_bijective f hf hfinite F n)).symm

@[simp] theorem cohomologyEquiv_symm_apply (F : AbelianSheaf X) (n : ℕ)
    (e : CategoryTheory.Sheaf.H.{0} F n) :
    (cohomologyEquiv f hf hfinite F n).symm e = cohomologyForward f hf hfinite F n e := rfl

/-- The forward comparison after its actual inverse is identity. -/
theorem cohomologyForward_equiv (F : AbelianSheaf X) (n : ℕ)
    (e : CategoryTheory.Sheaf.H.{0} ((pushforward f).obj F) n) :
    cohomologyForward f hf hfinite F n (cohomologyEquiv f hf hfinite F n e) = e :=
  (cohomologyEquiv f hf hfinite F n).symm_apply_apply e

/-- Naturality of the canonical forward comparison for the genuine cohomology maps. -/
theorem cohomologyForward_naturality {F G : AbelianSheaf X} (g : F ⟶ G)
    (n : ℕ) (e : CategoryTheory.Sheaf.H.{0} F n) :
    cohomologyForward f hf hfinite G n (CategoryTheory.Sheaf.H.map g n e) =
      CategoryTheory.Sheaf.H.map ((pushforward f).map g) n
        (cohomologyForward f hf hfinite F n e) := by
  exact @ExtComparison.comparison_naturality
    (AbelianSheaf X) _ _ (AbelianSheaf Y) _ _ (pushforward f) (pushforward_additive f)
    (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
    (pushforward_preservesFiniteColimits f hf hfinite)
    (abelianSheaf_hasExt X) (abelianSheaf_hasExt Y)
    (integerSheaf X) (integerSheaf Y) (integerUnit f) F G g n e

/-- The inverse equivalence commutes with the actual induced maps on cohomology. -/
theorem cohomologyEquiv_naturality {F G : AbelianSheaf X} (g : F ⟶ G)
    (n : ℕ) (e : CategoryTheory.Sheaf.H.{0} ((pushforward f).obj F) n) :
    cohomologyEquiv f hf hfinite G n (CategoryTheory.Sheaf.H.map ((pushforward f).map g) n e) =
      CategoryTheory.Sheaf.H.map g n (cohomologyEquiv f hf hfinite F n e) := by
  apply (cohomologyForward_bijective f hf hfinite G n).injective
  exact (cohomologyForward_equiv f hf hfinite G n
    (CategoryTheory.Sheaf.H.map ((pushforward f).map g) n e)).trans
      ((congrArg (CategoryTheory.Sheaf.H.map ((pushforward f).map g) n)
        (cohomologyForward_equiv f hf hfinite F n e).symm).trans
        (cohomologyForward_naturality f hf hfinite g n
          (cohomologyEquiv f hf hfinite F n e)).symm)

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyFinitePushforward
