import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupTotalActual
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupFirstAlgebra
import Wikipedia.HopfProblem.SheafCupProductNativeBasic

/-!
# The actual holomorphic first-column algebra map on a period torus

The original holomorphic-to-smooth ring inclusion induces the actual
Godement coface map. Its images are killed by the proved prolonged
native derivatives, so the existing first-column construction applies
without a horizontal-vanishing hypothesis.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.FirstMaps

open SheafCupProduct

variable (p : PeriodDomain)

/-- The original global holomorphic Godement cofaces. -/
abbrev sourceData := SheafCupProduct.globalData (Derivation.holomorphicRingSheaf p)

/-- Literal actual ring maps on all four original Godement terms. -/
def firstMorphism : (sourceData p).Morphism (totalData p).cofaces :=
  GodementRing.cofaceMap (Derivation.inclusionRing p) (GodementRing.sections ⊤)

theorem gradient0_zero (a : (GodementRing.term0 (Derivation.holomorphicRingSheaf p)).obj.obj
    (op (⊤ : Opens p.Torus))) : (totalData p).gradient0 ((firstMorphism p).f0 a) = 0 := by
  apply Prod.ext
  · exact congrArg (fun f => Derivation.sectionMap f ⊤ a)
      (Derivation.native_inclusion_derivative0 p 0)
  · exact congrArg (fun f => Derivation.sectionMap f ⊤ a)
      (Derivation.native_inclusion_derivative0 p 1)

theorem gradient1_zero (a : (GodementRing.term1 (Derivation.holomorphicRingSheaf p)).obj.obj
    (op (⊤ : Opens p.Torus))) : (totalData p).gradient1 ((firstMorphism p).f1 a) = 0 := by
  apply Prod.ext
  · exact congrArg (fun f => Derivation.sectionMap f ⊤ a)
      (Derivation.native_inclusion_derivative1 p 0)
  · exact congrArg (fun f => Derivation.sectionMap f ⊤ a)
      (Derivation.native_inclusion_derivative1 p 1)

theorem gradient2_zero (a : (GodementRing.term2 (Derivation.holomorphicRingSheaf p)).obj.obj
    (op (⊤ : Opens p.Torus))) : (totalData p).gradient2 ((firstMorphism p).f2 a) = 0 := by
  apply Prod.ext
  · exact congrArg (fun f => Derivation.sectionMap f ⊤ a)
      (Derivation.native_inclusion_derivative2 p 0)
  · exact congrArg (fun f => Derivation.sectionMap f ⊤ a)
      (Derivation.native_inclusion_derivative2 p 1)

/-- The genuine, unconditionally constructed first-column algebra map. -/
def firstAlgebra : FirstAlgebra.Data (sourceData p) (totalData p) where
  morphism := firstMorphism p
  gradient0 := gradient0_zero p
  gradient1 := gradient1_zero p
  gradient2 := gradient2_zero p

/-- The original kernel/range quotient map in degree one. -/
abbrev firstH1 := (firstAlgebra p).cohomologyOneMap

/-- The original kernel/range quotient map in degree two. -/
abbrev firstH2 := (firstAlgebra p).cohomologyTwoMap

theorem firstH_cup (a b : (sourceData p).CohomologyOne) :
    firstH2 p ((sourceData p).cup a b) =
      (totalData p).cup (firstH1 p a) (firstH1 p b) :=
  (firstAlgebra p).map_cup a b

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.FirstMaps
