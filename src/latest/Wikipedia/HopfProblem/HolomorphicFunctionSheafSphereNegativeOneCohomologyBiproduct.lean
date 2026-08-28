import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereNegativeOneCohomologyBiproductSheaf
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereNegativeOneCohomologyScalarsZero
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereNegativeOneCohomologyVanishing
import Mathlib.LinearAlgebra.Prod

/-!
# Genuine cohomology of `𝒪 ⊕ 𝒪(-∞)` on the analytic sphere

The first actual summand projection induces a complex-linear
cohomology equivalence in every degree, with inverse given by the
first actual summand inclusion. Consequently degree zero is `ℂ`,
by evaluation at infinity, and every positive degree vanishes.
All scalar structures are induced by the original sheaf scalar maps.

This computes the stated direct-sum sheaf itself. It makes no claim
that this sheaf is a higher direct image of another space.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1.NegativeOneCohomology

attribute [local instance] sphereCohomologyModule negativeOneCohomologyModule
  splitCohomologyModule

/-- The first actual projection induces a linear cohomology equivalence
in every degree, because the actual second summand has zero cohomology. -/
def splitFirstCohomologyLinearEquiv (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} splitSheaf n ≃ₗ[ℂ]
      CategoryTheory.Sheaf.H.{0} sphereSheaf n := by
  letI := negativeOne_cohomology_subsingleton n
  letI : Unique (CategoryTheory.Sheaf.H.{0} negativeOneSheaf n) :=
    uniqueOfSubsingleton 0
  exact (splitCohomologyLinearEquiv n).trans LinearEquiv.prodUnique

/-- The equivalence is exactly the native map of the first projection. -/
@[simp] theorem splitFirstCohomologyLinearEquiv_apply (n : ℕ)
    (x : CategoryTheory.Sheaf.H.{0} splitSheaf n) :
    splitFirstCohomologyLinearEquiv n x =
      CategoryTheory.Sheaf.H.map splitFirstProjection n x :=
  splitCohomologyLinearEquiv_fst n x

/-- Its inverse is exactly the native map of the first inclusion. -/
@[simp] theorem splitFirstCohomologyLinearEquiv_symm_apply (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0} sphereSheaf n) :
    (splitFirstCohomologyLinearEquiv n).symm a =
      CategoryTheory.Sheaf.H.map splitFirstInclusion n a :=
  splitCohomologyLinearEquiv_symm_inl n a

/-- Native degree-zero cohomology of the actual direct sum is `ℂ`. -/
def splitH0LinearEquiv : CategoryTheory.Sheaf.H.{0} splitSheaf 0 ≃ₗ[ℂ] ℂ :=
  (splitFirstCohomologyLinearEquiv 0).trans sphereH0LinearEquiv

/-- This comparison first takes the genuine first summand, then its
actual global section, and finally evaluates at the actual point at infinity. -/
@[simp] theorem splitH0LinearEquiv_apply (x : CategoryTheory.Sheaf.H.{0} splitSheaf 0) :
    splitH0LinearEquiv x = h0GlobalAddEquiv 𝓘(ℂ) RiemannSphere
      (CategoryTheory.Sheaf.H.map splitFirstProjection 0 x)
      (toTopOpen RiemannSphere ∞) := by
  change sphereH0LinearEquiv (splitFirstCohomologyLinearEquiv 0 x) = _
  rw [splitFirstCohomologyLinearEquiv_apply, sphereH0LinearEquiv_apply]

/-- The inverse is the native first inclusion applied to the actual
degree-zero class of the literal constant holomorphic section. -/
theorem splitH0LinearEquiv_symm_apply (c : ℂ) :
    splitH0LinearEquiv.symm c =
      CategoryTheory.Sheaf.H.map splitFirstInclusion 0
        ((h0GlobalAddEquiv 𝓘(ℂ) RiemannSphere).symm
          (algebraMap ℂ (GlobalSections 𝓘(ℂ) RiemannSphere) c)) := by
  change (splitFirstCohomologyLinearEquiv 0).symm (sphereH0LinearEquiv.symm c) = _
  rw [splitFirstCohomologyLinearEquiv_symm_apply, sphereH0LinearEquiv_symm_apply]

/-- Every positive actual cohomology group of `𝒪 ⊕ 𝒪(-∞)` vanishes. -/
theorem split_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} splitSheaf (n + 1)) := by
  have hs := HolomorphicSheafCohomology.SphereDolbeault.holomorphic_higher_subsingleton n
  refine ⟨fun a b => (splitFirstCohomologyLinearEquiv (n + 1)).injective ?_⟩
  exact hs.elim _ _

theorem split_higher_eq_zero (n : ℕ)
    (x : CategoryTheory.Sheaf.H.{0} splitSheaf (n + 1)) : x = 0 :=
  (split_higher_subsingleton n).elim x 0

/-- The native positive-degree cohomology objects are actual zero objects. -/
theorem split_higher_isZero (n : ℕ) : IsZero
    ((CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology (TopCat.of RiemannSphere)) (n + 1)).obj splitSheaf) :=
  AddCommGrpCat.isZero_iff_subsingleton.mpr (split_higher_subsingleton n)

/-- Every native complex cohomology module of the direct sum is finite-dimensional. -/
instance split_cohomology_finite (n : ℕ) :
    Module.Finite ℂ (CategoryTheory.Sheaf.H.{0} splitSheaf n) := by
  cases n with
  | zero =>
    exact FiniteDimensional.of_injective splitH0LinearEquiv.toLinearMap
      splitH0LinearEquiv.injective
  | succ n =>
    let := split_higher_subsingleton n
    infer_instance

/-- The actual complex dimensions are one in degree zero and zero otherwise. -/
theorem split_cohomology_finrank (n : ℕ) :
    Module.finrank ℂ (CategoryTheory.Sheaf.H.{0} splitSheaf n) =
      if n = 0 then 1 else 0 := by
  cases n with
  | zero =>
    exact splitH0LinearEquiv.finrank_eq.trans (Module.finrank_self ℂ)
  | succ n =>
    let := split_higher_subsingleton n
    simp only [Nat.succ_ne_zero, if_false]
    exact Module.finrank_zero_of_subsingleton

/-- Each actual positive-degree module is canonically the zero complex vector space. -/
def split_higher_zeroLinearEquiv (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} splitSheaf (n + 1) ≃ₗ[ℂ] (Fin 0 → ℂ) := by
  letI := split_higher_subsingleton n
  exact LinearEquiv.ofSubsingleton _ _

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1.NegativeOneCohomology
