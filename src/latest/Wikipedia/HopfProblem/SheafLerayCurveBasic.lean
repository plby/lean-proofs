import Wikipedia.HopfProblem.SheafLerayCurveVanishing
import Wikipedia.HopfProblem.SheafLerayCurveSheafComparisons
import Wikipedia.HopfProblem.SheafLerayLowDegreesPushforward

/-!
# The actual higher-direct-image hypotheses for curve-type Leray edges

The vanishing condition is imposed on the genuine right-derived sheaf
pushforwards, only in a finite triangular range. Injectivity of the
terms of the actual pushed resolution is already proved for every
continuous map. Its required cycle vanishing is a consequence, not an
additional premise or a blanket assertion about abelian sheaves.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.SheafLerayCurve

open SheafHigherDirectImage
open CuspNormalization.SheafCohomologyFinitePushforward (integerSheaf)

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (F : AbelianSheaf X)

/-- The original chosen injective resolution after actual sheaf pushforward. -/
abbrev canonicalComplex := pushedResolution f (injectiveResolution F)

/-- Every term is genuinely injective, by the proved preservation of
injectives under the original sheaf pushforward. -/
theorem canonicalComplex_term_injective (q : ℕ) :
    Injective ((canonicalComplex f F).X q) :=
  SheafLerayLowDegrees.pushedResolution_term_injective f (injectiveResolution F) q

/-- Explicit actual cohomology vanishings, restricted to the finite range
`p ≥ 2` and `p + q ≤ N`. No higher direct image is assigned a new value. -/
def CohomologyVanishing (N : ℕ) : Prop :=
  ∀ q p : ℕ, 2 ≤ p → q + p ≤ N →
    Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F q) p)

theorem CohomologyVanishing.mono {N M : ℕ} (h : CohomologyVanishing f F N) (hMN : M ≤ N) :
    CohomologyVanishing f F M :=
  fun q p hp hqp => h q p hp (hqp.trans hMN)

/-- The original derived-functor resolution isomorphism transfers exactly
these actual sheaf-cohomology hypotheses to the native homology objects. -/
theorem canonicalComplex_higherVanishing (N : ℕ) (h : CohomologyVanishing f F N) :
    Abstract.HigherVanishing (integerSheaf Y) (canonicalComplex f F) N := by
  intro q p hp hqp
  let : Subsingleton (Ext (integerSheaf Y) (sheaf f F q) p) := h q p hp hqp
  exact ExtComparison.subsingleton_of_iso (integerSheaf Y)
    (resolutionIso f F (injectiveResolution F) q).symm p

/-- These three actual vanishings suffice for the degree-two edge. -/
theorem cohomologyVanishing_three
    (h02 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 0) 2))
    (h03 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 0) 3))
    (h12 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 1) 2)) :
    CohomologyVanishing f F 3 := by
  intro q p hp hqp
  have hq : q = 0 ∨ q = 1 := by omega
  rcases hq with rfl | rfl
  · have hp' : p = 2 ∨ p = 3 := by omega
    rcases hp' with rfl | rfl
    · exact h02
    · exact h03
  · have hp' : p = 2 := by omega
    subst p
    exact h12

/-- These six actual vanishings suffice for the degree-three edge. -/
theorem cohomologyVanishing_four
    (h02 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 0) 2))
    (h03 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 0) 3))
    (h04 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 0) 4))
    (h12 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 1) 2))
    (h13 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 1) 3))
    (h22 : Subsingleton (CategoryTheory.Sheaf.H.{0} (sheaf f F 2) 2)) :
    CohomologyVanishing f F 4 := by
  intro q p hp hqp
  have hq : q = 0 ∨ q = 1 ∨ q = 2 := by omega
  rcases hq with rfl | rfl | rfl
  · have hp' : p = 2 ∨ p = 3 ∨ p = 4 := by omega
    rcases hp' with rfl | rfl | rfl
    · exact h02
    · exact h03
    · exact h04
  · have hp' : p = 2 ∨ p = 3 := by omega
    rcases hp' with rfl | rfl
    · exact h12
    · exact h13
  · have hp' : p = 2 := by omega
    subst p
    exact h22

end Wikipedia.HopfProblem.SheafLerayCurve
