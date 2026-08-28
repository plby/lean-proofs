import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyPieces

/-!
# Actual fibre inclusions behind the two cover markings

The inverse homotopy markings insert the contraction points of the two
slits. Paths inside the slits move those points to the common basepoint.
Applying the actual covering lifts and keeping the fibre coordinate fixed
gives genuine homotopies to the same original fibre inclusion.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods
open PeriodTorusHigherHomology PeriodTorusHigherHomology.CircleTopology

variable (D : Data ℂ TriangleRegularPoint) (b : SlitBaseLift)

/-- The actual inclusion of the fibre over the specified lift of the common basepoint. -/
def familyFibreInclusion : C(RealTorus₄, D.Space) :=
  ⟨fun f => D.quotient (b.val, f),
    D.quotient_continuous.comp (continuous_const.prodMk continuous_id)⟩

@[simp] theorem familyFibreInclusion_apply (f : RealTorus₄) :
    familyFibreInclusion D b f = D.quotient (b.val, f) := rfl

/-- The literal inclusion of the upper family open into the actual family. -/
def upperFamilyInclusion : C(upperFamily D, D.Space) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The literal inclusion of the lower family open into the actual family. -/
def lowerFamilyInclusion : C(lowerFamily D, D.Space) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem upperFamilyInclusion_apply (x : upperFamily D) :
    upperFamilyInclusion D x = x.val := rfl

@[simp] theorem lowerFamilyInclusion_apply (x : lowerFamily D) :
    lowerFamilyInclusion D x = x.val := rfl

/-- A path in the actual upper slit from its contraction point to the common basepoint. -/
def upperContractionToBasepoint : Path (contractionPoint upperBase) upperBasePoint :=
  PathConnectedSpace.somePath (contractionPoint upperBase) upperBasePoint

/-- The corresponding path inside the actual lower slit. -/
def lowerContractionToBasepoint : Path (contractionPoint lowerBase) lowerBasePoint :=
  PathConnectedSpace.somePath (contractionPoint lowerBase) lowerBasePoint

/-- The upper inverse marking inserts precisely its chosen contraction-point lift. -/
@[simp] theorem upperFamilyInverse_apply (f : RealTorus₄) :
    upperFamilyInclusion D ((upperHomotopyEquiv D b).invFun f) =
      D.quotient (upperLift b (contractionPoint upperBase), f) := rfl

/-- The lower inverse marking inserts its own contraction-point lift. -/
@[simp] theorem lowerFamilyInverse_apply (f : RealTorus₄) :
    lowerFamilyInclusion D ((lowerHomotopyEquiv D b).invFun f) =
      D.quotient (lowerLift b (contractionPoint lowerBase), f) := rfl

/-- Move the actual upper inverse marking to the original fibre, with fibre coordinate fixed. -/
def upperFamilyFibreHomotopy :
    ((upperFamilyInclusion D).comp (upperHomotopyEquiv D b).invFun).Homotopy
      (familyFibreInclusion D b) where
  toFun x := D.quotient (upperLift b (upperContractionToBasepoint x.1), x.2)
  continuous_toFun := D.quotient_continuous.comp
    (((upperLift b).continuous.comp
      (upperContractionToBasepoint.continuous.comp continuous_fst)).prodMk continuous_snd)
  map_zero_left f := by
    change D.quotient (upperLift b (upperContractionToBasepoint 0), f) =
      D.quotient (upperLift b (contractionPoint upperBase), f)
    rw [upperContractionToBasepoint.source]
  map_one_left f := by
    change D.quotient (upperLift b (upperContractionToBasepoint 1), f) =
      D.quotient (b.val, f)
    rw [upperContractionToBasepoint.target, upperLift_basepoint]

/-- The same construction in the lower slit ends at the same original fibre inclusion. -/
def lowerFamilyFibreHomotopy :
    ((lowerFamilyInclusion D).comp (lowerHomotopyEquiv D b).invFun).Homotopy
      (familyFibreInclusion D b) where
  toFun x := D.quotient (lowerLift b (lowerContractionToBasepoint x.1), x.2)
  continuous_toFun := D.quotient_continuous.comp
    (((lowerLift b).continuous.comp
      (lowerContractionToBasepoint.continuous.comp continuous_fst)).prodMk continuous_snd)
  map_zero_left f := by
    change D.quotient (lowerLift b (lowerContractionToBasepoint 0), f) =
      D.quotient (lowerLift b (contractionPoint lowerBase), f)
    rw [lowerContractionToBasepoint.source]
  map_one_left f := by
    change D.quotient (lowerLift b (lowerContractionToBasepoint 1), f) =
      D.quotient (b.val, f)
    rw [lowerContractionToBasepoint.target, lowerLift_basepoint]

@[simp] theorem upperFamilyFibreHomotopy_apply (t : unitInterval) (f : RealTorus₄) :
    upperFamilyFibreHomotopy D b (t, f) =
      D.quotient (upperLift b (upperContractionToBasepoint t), f) := rfl

@[simp] theorem lowerFamilyFibreHomotopy_apply (t : unitInterval) (f : RealTorus₄) :
    lowerFamilyFibreHomotopy D b (t, f) =
      D.quotient (lowerLift b (lowerContractionToBasepoint t), f) := rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
