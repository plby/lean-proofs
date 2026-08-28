import Wikipedia.HomotopyGroupsOfSpheres.CliffordBalancedBottFormula
import Wikipedia.HomotopyGroupsOfSpheres.PointedHomotopyClassComparison

/-!
# The actual Clifford-to-balanced homotopy and its native class equality

The source includes the Clifford unitary matrix in two equal blocks, adds four
identity directions, and uses the fixed orthogonal normalization. All three
homotopies are composed before passing to native cubical homotopy classes.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open ComplexCrossProductUnitary QuaternionicSymmetricMatrices

def forgetSpecial : C(SpecialSpace (Fin 6 ⊕ Fin 6), Space (Fin 6 ⊕ Fin 6)) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def correctedUnderlyingMap : C(ComplexCrossProductUnitary.UnitSphere, Space (Fin 6 ⊕ Fin 6)) :=
  forgetSpecial.comp correctedSphereMap

theorem correctedUnderlyingMap_axis : correctedUnderlyingMap axis = identity :=
  congrArg Subtype.val correctedSphereMap_axis

def balancedCorrectionHomotopy :
    balancedSphereMap.HomotopyRel correctedUnderlyingMap {axis} :=
  (referenceCorrectionHomotopy.compContinuousMap forgetSpecial).cast rfl rfl

def coreToBalanced : C(Space (Fin 4 ⊕ Fin 4), Space (Fin 6 ⊕ Fin 6)) :=
  (normalizationHomeomorph : C(Space (Fin 6 ⊕ Fin 6), Space (Fin 6 ⊕ Fin 6))).comp
    BalancedPhasePadding.identityPadding

def rawCliffordSource : C(ComplexCrossProductUnitary.UnitSphere, Space (Fin 6 ⊕ Fin 6)) :=
  coreToBalanced.comp ComplexCliffordFive.blockIncludedSymmetricMap

def rawCliffordPaddingHomotopy : rawCliffordSource.HomotopyRel balancedSourceMap {axis} :=
  (ComplexCliffordFive.blockMixingHomotopy.compContinuousMap coreToBalanced).cast rfl rfl

def rawCliffordToBottHomotopy : rawCliffordSource.HomotopyRel correctedUnderlyingMap {axis} :=
  rawCliffordPaddingHomotopy.trans (balancedPaddingHomotopy.trans balancedCorrectionHomotopy)

theorem rawCliffordSource_axis : rawCliffordSource axis = identity := by
  have h := rawCliffordToBottHomotopy.eq_fst 1 (Set.mem_singleton axis)
  rw [rawCliffordToBottHomotopy.apply_one] at h
  exact h.symm.trans correctedUnderlyingMap_axis

attribute [local irreducible] rawCliffordSource correctedUnderlyingMap rawCliffordToBottHomotopy

def normalizedCliffordCube (p : GenLoop (Fin 5) ComplexCrossProductUnitary.UnitSphere axis) :
    GenLoop (Fin 5) (Space (Fin 6 ⊕ Fin 6)) identity :=
  pointedMapGenLoop rawCliffordSource axis identity rawCliffordSource_axis p

def correctedCube (p : GenLoop (Fin 5) ComplexCrossProductUnitary.UnitSphere axis) :
    GenLoop (Fin 5) (Space (Fin 6 ⊕ Fin 6)) identity :=
  pointedMapGenLoop correctedUnderlyingMap axis identity correctedUnderlyingMap_axis p

theorem normalizedCliffordClass_eq_corrected
    (p : GenLoop (Fin 5) ComplexCrossProductUnitary.UnitSphere axis) :
    (⟦normalizedCliffordCube p⟧ : π_ 5 (Space (Fin 6 ⊕ Fin 6)) identity) = ⟦correctedCube p⟧ :=
  Quotient.sound (pointedMapGenLoop_homotopic_of_homotopyRel
    rawCliffordSource correctedUnderlyingMap axis identity rawCliffordSource_axis
    correctedUnderlyingMap_axis rawCliffordToBottHomotopy p)

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
