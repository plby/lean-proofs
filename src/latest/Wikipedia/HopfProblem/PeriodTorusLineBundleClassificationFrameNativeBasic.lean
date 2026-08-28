import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFrameBasic
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeIdentification

/-!
# The radial section in an arbitrary original native line bundle

The construction is transferred into the actual original fibres by the
previously proved scalar-presentation identification. Its coefficients are
computed in the original native trivializations; neither topology nor atlas
is replaced by a definition.
-/

noncomputable section

open Set Bundle

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFrame

open PeriodTorusLineBundleClassificationNative

variable (V : ComplexPlane₂ → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]

/-- An actual section of the original native bundle, obtained from radial
transport of `1` in its preferred origin fibre coordinate. -/
def nativeFrame (x : ComplexPlane₂) : V x :=
  fiberIdentification V x (coreFrame (data V) x)

theorem nativeFrame_ne_zero (x : ComplexPlane₂) : nativeFrame V x ≠ 0 := by
  intro hx
  have h := (fiberIdentification V x).injective (hx.trans (map_zero _).symm)
  exact coreFrame_ne_zero (data V) x h

/-- The coefficient of the actual constructed section in an original native
trivialization, including the native off-chart convention. -/
def nativeFrameCoefficient (i x : ComplexPlane₂) : ℂ :=
  (nativeTriv V i (TotalSpace.mk x (nativeFrame V x))).2

/-- The coefficient comparison uses the existing native atlas map. -/
theorem nativeFrameCoefficient_eq (i : ComplexPlane₂) {x : ComplexPlane₂}
    (hx : x ∈ (nativeTriv V i).baseSet) :
    nativeFrameCoefficient V i x = frameCoefficient (data V) i x := by
  exact congrArg Prod.snd
    (toNative_localTriv V i ⟨x, coreFrame (data V) x⟩ hx)

theorem nativeFrameCoefficient_ne_zero (i : ComplexPlane₂) {x : ComplexPlane₂}
    (hx : x ∈ (nativeTriv V i).baseSet) : nativeFrameCoefficient V i x ≠ 0 := by
  rw [nativeFrameCoefficient_eq V i hx]
  exact frameCoefficient_ne_zero (data V) i x

/-- Exact transformation by the original native scalar coordinate changes. -/
theorem nativeFrameCoefficient_change (i j : ComplexPlane₂) {x : ComplexPlane₂}
    (hi : x ∈ (nativeTriv V i).baseSet) (hj : x ∈ (nativeTriv V j).baseSet) :
    (scalarTransition V i j x : ℂ) * nativeFrameCoefficient V i x =
      nativeFrameCoefficient V j x := by
  rw [nativeFrameCoefficient_eq V i hi, nativeFrameCoefficient_eq V j hj]
  exact frameCoefficient_compatible (data V) i j x ⟨hi, hj⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFrame
