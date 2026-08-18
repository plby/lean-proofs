/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Proposition75Case1
import ErdosProblems.Erdos186.CFP.Bilu.Proposition75Case2

/-!
# The two branches of Bilu Proposition 7.5

This is the common Section 8-to-Section 9 interface.  A Case 1 certificate
contains the inball geometry and the large-covolume inequality.  A Case 2
certificate contains the constructed geometric witness, the short-normal
bound, and the explicit parameter inequality.  Either certificate proves
the same equation (7.8), `Proposition75Conclusion`.
-/

namespace Erdos186.CFP.Bilu.Proposition75Branches

open MeasureTheory Module
open scoped ENNReal
open Proposition75Data Proposition75Case1 Proposition75Case2

noncomputable section

/-- Complete data for the large-covolume branch of Proposition 7.5. -/
def Case1Branch {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) (constant scale : ENNReal) : Prop :=
  ∃ rho : ℝ, ∃ _X : Case1Witness D rho,
    case1GeometryFactor D rho ≤ constant ∧
      1 ≤ scale * ENNReal.ofReal
        (ZLattice.covolume D.latticePoints μHE[finrank ℝ D.C0])

/-- Complete data for the small-covolume, badly-approximable branch. -/
def Case2Branch {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) (constant scale : ENNReal) : Prop :=
  ∃ d k : ℕ, ∃ X : Case2Witness D d k, ∃ normalFactor : ENNReal,
    ENNReal.ofReal ‖X.l‖ ≤ normalFactor *
        ENNReal.ofReal
          (ZLattice.covolume D.latticePoints μHE[finrank ℝ D.C0]) ∧
      (2 * ENNReal.ofReal X.C)⁻¹ *
          (((‖(2 : ℝ)⁻¹‖₊ : ENNReal) ^ (d + k))⁻¹ *
            ((2 : ENNReal) ^ (m + r)) *
            (((d.factorial : ENNReal) * ENNReal.ofReal (X.rho ^ k))⁻¹ *
              ((d + k).factorial : ENNReal))) * normalFactor ≤
        constant * scale

/-- The exact Case 1/Case 2 alternative at the end of Section 8. -/
def Proposition75Cases {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) (constant scale : ENNReal) : Prop :=
  Case1Branch D constant scale ∨ Case2Branch D constant scale

theorem conclusion_of_case1Branch {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    {D : GeometricData B a} {constant scale : ENNReal}
    (h : Case1Branch D constant scale) :
    Proposition75Conclusion D constant scale := by
  obtain ⟨rho, X, hfactor, hthreshold⟩ := h
  exact proposition75Conclusion_case1_of_factor_le
    X constant scale hfactor hthreshold

theorem conclusion_of_case2Branch {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    {D : GeometricData B a} {constant scale : ENNReal}
    (h : Case2Branch D constant scale) :
    Proposition75Conclusion D constant scale := by
  obtain ⟨d, k, X, normalFactor, hnormal, hconstants⟩ := h
  exact proposition75Conclusion_of_raw_case2
    X normalFactor constant scale hnormal hconstants

/-- Common conclusion eliminator used by the iteration in Section 9. -/
theorem proposition75Conclusion_of_cases {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    {D : GeometricData B a} {constant scale : ENNReal}
    (h : Proposition75Cases D constant scale) :
    Proposition75Conclusion D constant scale := by
  rcases h with hcase1 | hcase2
  · exact conclusion_of_case1Branch hcase1
  · exact conclusion_of_case2Branch hcase2

end


end Erdos186.CFP.Bilu.Proposition75Branches

#print axioms Erdos186.CFP.Bilu.Proposition75Branches.conclusion_of_case1Branch
#print axioms Erdos186.CFP.Bilu.Proposition75Branches.conclusion_of_case2Branch
#print axioms
  Erdos186.CFP.Bilu.Proposition75Branches.proposition75Conclusion_of_cases
