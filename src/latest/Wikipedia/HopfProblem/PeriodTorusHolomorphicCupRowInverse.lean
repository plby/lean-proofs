import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupRowOne
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupRowTwo

/-!
# Inverse representative formulas for the original native row comparisons

The forward comparisons have already been proved for the actual native
classes. A basic inverse-isomorphism identity gives the corresponding
inverse formulas, without unfolding either cohomology construction.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Row

open PeriodTorusHolomorphicCohomology

/-- An actual isomorphism's inverse recovers a proved forward representative. -/
theorem inverseClass_of_forward {A B : AddCommGrpCat.{0}}
    (e : A ≅ B) (a : A) (b : B) (h : e.hom a = b) : e.inv b = a :=
  (congrArg e.inv h).symm.trans (e.hom_inv_id_apply a)

variable (p : PeriodDomain)

/-- The inverse actual row comparison gives the old native closed-pair class. -/
theorem h1Iso_inv_class (s : Dolbeault.PairSection p ⊤)
    (hs : Dolbeault.topSection p ⊤ s = 0) :
    (h1Iso p).inv (oneClass p s hs) = nativeH1Class p s hs :=
  inverseClass_of_forward (h1Iso p) (nativeH1Class p s hs) (oneClass p s hs)
    (h1Iso_nativeClass p s hs)

/-- The inverse actual row comparison gives exactly the old native top class. -/
theorem h2Iso_inv_class (s : Dolbeault.SmoothSection p ⊤) :
    (h2Iso p).inv (twoClass p s) = nativeH2Class p s :=
  inverseClass_of_forward (h2Iso p) (nativeH2Class p s) (twoClass p s)
    (h2Iso_nativeClass p s)

/-- The old degree-one coordinates remain the two actual coefficient Haar means. -/
theorem h1Equiv_rowClass (s : Dolbeault.PairSection p ⊤)
    (hs : Dolbeault.topSection p ⊤ s = 0) :
    PeriodTorusHolomorphicCohomology.h1Equiv p ((h1Iso p).inv (oneClass p s hs)) =
      GlobalFourier.pairMean p s := by
  rw [h1Iso_inv_class]
  exact h1Equiv_nativeClass p s hs

/-- The unchanged old degree-two coordinate is the positive probability Haar mean. -/
theorem h2Equiv_rowClass (s : Dolbeault.SmoothSection p ⊤) :
    PeriodTorusHolomorphicCohomology.h2Equiv p ((h2Iso p).inv (twoClass p s)) =
      GlobalFourier.mean p s := by
  rw [h2Iso_inv_class]
  exact h2Equiv_nativeClass p s

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Row
