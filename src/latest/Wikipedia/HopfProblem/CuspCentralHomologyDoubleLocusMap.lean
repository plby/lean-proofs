import Wikipedia.HopfProblem.CuspCentralHomologyEdgeOrbits
import Wikipedia.HopfProblem.CuspCentralHomologyCornerOrbits
import Wikipedia.HopfProblem.CuspCentralHomologySuspensionTopologyBasic
import Wikipedia.HopfProblem.CuspCentralHomologySuspensionCircles
import Mathlib.Topology.Constructions.SumProd

/-!
# The actual three-edge suspension map into the central cusp fibre

The first and third edge cylinders keep their orientation, while the middle
one is reversed. Thus all three height-zero circles map to the odd toric
pole, and all three height-one circles map to the even pole. These exact
equalities descend the actual central quotient map through the suspension.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspCollapse

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

@[simp] theorem centralProject_edgeCylinder_zero (k : Fin 6) (a : Circle) :
    centralProject C ε hε (edgeCylinder (C 0) k (0, a)) =
      cornerPoint C ε hε (k - 1) :=
  congrArg (centralProject C ε hε) (Subtype.ext (edgeCylinder_zero_coe (C 0) k a))

@[simp] theorem centralProject_edgeCylinder_one (k : Fin 6) (a : Circle) :
    centralProject C ε hε (edgeCylinder (C 0) k (1, a)) = cornerPoint C ε hε k :=
  congrArg (centralProject C ε hε) (Subtype.ext (edgeCylinder_one_coe (C 0) k a))

/-- The three genuine edge cylinders, oriented from the odd pole to the even pole. -/
def doubleCylinder (p : unitInterval × ThreeCircles) : QuotientCentralFibre C ε :=
  match p.2 with
  | Sum.inl a => centralProject C ε hε (edgeCylinder (C 0) 0 (p.1, a))
  | Sum.inr (Sum.inl a) =>
      centralProject C ε hε (edgeCylinder (C 0) 1 (unitInterval.symm p.1, a))
  | Sum.inr (Sum.inr a) => centralProject C ε hε (edgeCylinder (C 0) 2 (p.1, a))

@[simp] theorem doubleCylinder_first (t : unitInterval) (a : Circle) :
    doubleCylinder C ε hε (t, Sum.inl a) =
      centralProject C ε hε (edgeCylinder (C 0) 0 (t, a)) := rfl

@[simp] theorem doubleCylinder_middle (t : unitInterval) (a : Circle) :
    doubleCylinder C ε hε (t, Sum.inr (Sum.inl a)) =
      centralProject C ε hε (edgeCylinder (C 0) 1 (unitInterval.symm t, a)) := rfl

@[simp] theorem doubleCylinder_last (t : unitInterval) (a : Circle) :
    doubleCylinder C ε hε (t, Sum.inr (Sum.inr a)) =
      centralProject C ε hε (edgeCylinder (C 0) 2 (t, a)) := rfl

theorem doubleCylinder_continuous : Continuous (doubleCylinder C ε hε) := by
  have h0 : Continuous (fun p : unitInterval × Circle =>
      centralProject C ε hε (edgeCylinder (C 0) 0 p)) :=
    (centralProject_continuous C ε hε).comp (edgeCylinder_continuous (C 0) 0)
  have h1 : Continuous (fun p : unitInterval × Circle =>
      centralProject C ε hε (edgeCylinder (C 0) 1 (unitInterval.symm p.1, p.2))) :=
    (centralProject_continuous C ε hε).comp
      ((edgeCylinder_continuous (C 0) 1).comp
        ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd))
  have h2 : Continuous (fun p : unitInterval × Circle =>
      centralProject C ε hε (edgeCylinder (C 0) 2 p)) :=
    (centralProject_continuous C ε hε).comp (edgeCylinder_continuous (C 0) 2)
  let e0 : unitInterval × ThreeCircles ≃ₜ
      (unitInterval × Circle) ⊕ (unitInterval × (Circle ⊕ Circle)) :=
    Homeomorph.prodSumDistrib
  let e1 : unitInterval × (Circle ⊕ Circle) ≃ₜ
      (unitInterval × Circle) ⊕ (unitInterval × Circle) := Homeomorph.prodSumDistrib
  have h := (h0.sumElim ((h1.sumElim h2).comp e1.continuous)).comp e0.continuous
  apply h.congr
  rintro ⟨t, a⟩
  rcases a with a | a | a <;> rfl

@[simp] theorem doubleCylinder_zero (a : ThreeCircles) :
    doubleCylinder C ε hε (0, a) = oddPole C ε hε := by
  rcases a with a | a | a <;>
    simp only [doubleCylinder_first, doubleCylinder_middle, doubleCylinder_last,
      unitInterval.symm_zero, centralProject_edgeCylinder_zero, centralProject_edgeCylinder_one]
  all_goals exact (cornerPoint_eq_oddPole_iff C ε hε _).mpr (by decide)

@[simp] theorem doubleCylinder_one (a : ThreeCircles) :
    doubleCylinder C ε hε (1, a) = evenPole C ε hε := by
  rcases a with a | a | a <;>
    simp only [doubleCylinder_first, doubleCylinder_middle, doubleCylinder_last,
      unitInterval.symm_one, centralProject_edgeCylinder_zero, centralProject_edgeCylinder_one]
  all_goals exact (cornerPoint_eq_evenPole_iff C ε hε _).mpr (by decide)

theorem doubleCylinder_respects (p q : unitInterval × ThreeCircles)
    (h : (suspensionSetoid ThreeCircles).r p q) :
    doubleCylinder C ε hε p = doubleCylinder C ε hε q := by
  rcases p with ⟨s, a⟩
  rcases q with ⟨t, b⟩
  change s = t ∧ (s = 0 ∨ s = 1 ∨ a = b) at h
  rcases h with ⟨hst, hs⟩
  cases hst
  rcases hs with rfl | rfl | rfl <;> simp only [doubleCylinder_zero, doubleCylinder_one]

/-- The actual central cusp map descended through the unreduced three-circle suspension. -/
def doubleSuspensionMap : Suspension ThreeCircles → QuotientCentralFibre C ε :=
  Quotient.lift (doubleCylinder C ε hε) (doubleCylinder_respects C ε hε)

@[simp] theorem doubleSuspensionMap_mk (t : unitInterval) (a : ThreeCircles) :
    doubleSuspensionMap C ε hε (Suspension.mk t a) = doubleCylinder C ε hε (t, a) := rfl

theorem doubleSuspensionMap_continuous : Continuous (doubleSuspensionMap C ε hε) :=
  (Suspension.isQuotientMap_mk (X := ThreeCircles)).continuous_iff.mpr
    (doubleCylinder_continuous C ε hε)

@[simp] theorem doubleSuspensionMap_mk_first (t : unitInterval) (a : Circle) :
    doubleSuspensionMap C ε hε (Suspension.mk t (Sum.inl a)) =
      centralProject C ε hε (edgeCylinder (C 0) 0 (t, a)) := rfl

@[simp] theorem doubleSuspensionMap_mk_middle (t : unitInterval) (a : Circle) :
    doubleSuspensionMap C ε hε (Suspension.mk t (Sum.inr (Sum.inl a))) =
      centralProject C ε hε (edgeCylinder (C 0) 1 (unitInterval.symm t, a)) := rfl

@[simp] theorem doubleSuspensionMap_mk_last (t : unitInterval) (a : Circle) :
    doubleSuspensionMap C ε hε (Suspension.mk t (Sum.inr (Sum.inr a))) =
      centralProject C ε hε (edgeCylinder (C 0) 2 (t, a)) := rfl

@[simp] theorem doubleSuspensionMap_north :
    doubleSuspensionMap C ε hε Suspension.north = oddPole C ε hε := by
  change doubleCylinder C ε hε (0, _) = oddPole C ε hε
  exact doubleCylinder_zero C ε hε _

@[simp] theorem doubleSuspensionMap_south :
    doubleSuspensionMap C ε hε Suspension.south = evenPole C ε hε := by
  change doubleCylinder C ε hε (1, _) = evenPole C ε hε
  exact doubleCylinder_one C ε hε _

end Wikipedia.HopfProblem.CuspCentralHomology
