import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyMayerVietorisVanishing
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenRestrictionTop

/-!
# Mayer–Vietoris using actual cohomology of the restricted sheaves

The input groups here are the actual sheaf-cohomology groups on the
actual open subspaces. The proved open-restriction and top-open Ext
comparisons transfer the genuine Mayer–Vietoris exact sequence to these
groups. No comparison theorem is assumed as a hypothesis.
-/

noncomputable section

open TopologicalSpace CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.MayerVietoris

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)

theorem open_subsingleton_of_restriction (W : Opens X) (n : ℕ)
    [Subsingleton (CategoryTheory.Sheaf.H.{0} ((OpenRestriction.restriction W).obj F) n)] :
    Subsingleton (CategoryTheory.Sheaf.H'.{0} F n W) :=
  (OpenRestriction.cohomologyEquiv W F n).injective.subsingleton

theorem restriction_subsingleton_of_open (W : Opens X) (n : ℕ)
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F n W)] :
    Subsingleton (CategoryTheory.Sheaf.H.{0} ((OpenRestriction.restriction W).obj F) n) :=
  (OpenRestriction.cohomologyEquiv W F n).symm.injective.subsingleton

variable (U V : Opens X)

/-- Degree-one vanishing on the actual union subspace follows from
actual component H¹ vanishing and actual section-difference surjectivity. -/
theorem restriction_one_subsingleton
    (h : Function.Surjective (sectionsDifference F U V))
    [Subsingleton (CategoryTheory.Sheaf.H.{0} ((OpenRestriction.restriction U).obj F) 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} ((OpenRestriction.restriction V).obj F) 1)] :
    Subsingleton
      (CategoryTheory.Sheaf.H.{0} ((OpenRestriction.restriction (U ⊔ V)).obj F) 1) := by
  have := open_subsingleton_of_restriction F U 1
  have := open_subsingleton_of_restriction F V 1
  have := union_one_subsingleton F U V h
  exact restriction_subsingleton_of_open F (U ⊔ V) 1

/-- In degree `n+2`, only component Hⁿ⁺² and intersection Hⁿ⁺¹ vanishing
are needed; there is no section-surjectivity hypothesis in these degrees. -/
theorem restriction_higher_subsingleton_at (n : ℕ)
    [Subsingleton
      (CategoryTheory.Sheaf.H.{0} ((OpenRestriction.restriction U).obj F) (n + 2))]
    [Subsingleton
      (CategoryTheory.Sheaf.H.{0} ((OpenRestriction.restriction V).obj F) (n + 2))]
    [Subsingleton
      (CategoryTheory.Sheaf.H.{0} ((OpenRestriction.restriction (U ⊓ V)).obj F) (n + 1))] :
    Subsingleton
      (CategoryTheory.Sheaf.H.{0} ((OpenRestriction.restriction (U ⊔ V)).obj F) (n + 2)) := by
  have := open_subsingleton_of_restriction F U (n + 2)
  have := open_subsingleton_of_restriction F V (n + 2)
  have := open_subsingleton_of_restriction F (U ⊓ V) (n + 1)
  have := union_successor_subsingleton F U V (n + 1)
  exact restriction_subsingleton_of_open F (U ⊔ V) (n + 2)

/-- Actual positive-degree acyclicity glues on a union once the actual
section difference is onto. -/
theorem restriction_higher_subsingleton
    (hU : ∀ n, Subsingleton
      (CategoryTheory.Sheaf.H.{0} ((OpenRestriction.restriction U).obj F) (n + 1)))
    (hV : ∀ n, Subsingleton
      (CategoryTheory.Sheaf.H.{0} ((OpenRestriction.restriction V).obj F) (n + 1)))
    (hI : ∀ n, Subsingleton
      (CategoryTheory.Sheaf.H.{0} ((OpenRestriction.restriction (U ⊓ V)).obj F) (n + 1)))
    (h : Function.Surjective (sectionsDifference F U V)) (n : ℕ) :
    Subsingleton
      (CategoryTheory.Sheaf.H.{0} ((OpenRestriction.restriction (U ⊔ V)).obj F) (n + 1)) := by
  cases n with
  | zero =>
      have := hU 0
      have := hV 0
      exact restriction_one_subsingleton F U V h
  | succ n =>
      have := hU (n + 1)
      have := hV (n + 1)
      have := hI n
      exact restriction_higher_subsingleton_at F U V n

/-- For a genuine cover, vanishing on its union is genuine global sheaf-cohomology vanishing. -/
theorem sheaf_subsingleton_of_union (hcover : U ⊔ V = ⊤) (n : ℕ)
    (h : Subsingleton (CategoryTheory.Sheaf.H'.{0} F n (U ⊔ V))) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} F n) := by
  have : Subsingleton (CategoryTheory.Sheaf.H'.{0} F n (⊤ : Opens X)) := hcover ▸ h
  exact OpenRestriction.topCohomology_subsingleton X F n

/-- Actual H¹ vanishing for a two-open cover, with the literal section-difference input. -/
theorem sheaf_one_subsingleton_of_cover (hcover : U ⊔ V = ⊤)
    (h : Function.Surjective (sectionsDifference F U V))
    [Subsingleton (CategoryTheory.Sheaf.H.{0} ((OpenRestriction.restriction U).obj F) 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} ((OpenRestriction.restriction V).obj F) 1)] :
    Subsingleton (CategoryTheory.Sheaf.H.{0} F 1) := by
  have := open_subsingleton_of_restriction F U 1
  have := open_subsingleton_of_restriction F V 1
  exact sheaf_subsingleton_of_union F U V hcover 1 (union_one_subsingleton F U V h)

/-- Actual global Hⁿ⁺² vanishing from a two-open cover, using only the relevant
actual component and intersection cohomology groups. -/
theorem sheaf_higher_subsingleton_of_cover_at (hcover : U ⊔ V = ⊤) (n : ℕ)
    [Subsingleton
      (CategoryTheory.Sheaf.H.{0} ((OpenRestriction.restriction U).obj F) (n + 2))]
    [Subsingleton
      (CategoryTheory.Sheaf.H.{0} ((OpenRestriction.restriction V).obj F) (n + 2))]
    [Subsingleton
      (CategoryTheory.Sheaf.H.{0} ((OpenRestriction.restriction (U ⊓ V)).obj F) (n + 1))] :
    Subsingleton (CategoryTheory.Sheaf.H.{0} F (n + 2)) := by
  have := open_subsingleton_of_restriction F U (n + 2)
  have := open_subsingleton_of_restriction F V (n + 2)
  have := open_subsingleton_of_restriction F (U ⊓ V) (n + 1)
  exact sheaf_subsingleton_of_union F U V hcover (n + 2)
    (union_successor_subsingleton F U V (n + 1))

/-- Positive-degree acyclicity of an actual sheaf glues across an actual
two-open cover when its actual section-difference map is surjective. -/
theorem sheaf_higher_subsingleton_of_cover (hcover : U ⊔ V = ⊤)
    (hU : ∀ n, Subsingleton
      (CategoryTheory.Sheaf.H.{0} ((OpenRestriction.restriction U).obj F) (n + 1)))
    (hV : ∀ n, Subsingleton
      (CategoryTheory.Sheaf.H.{0} ((OpenRestriction.restriction V).obj F) (n + 1)))
    (hI : ∀ n, Subsingleton
      (CategoryTheory.Sheaf.H.{0} ((OpenRestriction.restriction (U ⊓ V)).obj F) (n + 1)))
    (h : Function.Surjective (sectionsDifference F U V)) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} F (n + 1)) := by
  cases n with
  | zero =>
      have := hU 0
      have := hV 0
      exact sheaf_one_subsingleton_of_cover F U V hcover h
  | succ n =>
      have := hU (n + 1)
      have := hV (n + 1)
      have := hI n
      exact sheaf_higher_subsingleton_of_cover_at F U V hcover n

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.MayerVietoris
