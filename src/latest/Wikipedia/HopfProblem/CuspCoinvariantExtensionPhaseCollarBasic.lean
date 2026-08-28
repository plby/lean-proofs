import Wikipedia.HopfProblem.CuspCoinvariantExtensionPhaseBasic

/-!
# The actual open and closed relative cusp collars

The collar sets use the unchanged cusp parameter.  The prescribed closed
outer collar has the open region of exact punctured-phase agreement as a
neighborhood, and both are preserved by the original vertical flow.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCoinvariantExtension.Phase

open CuspUniformization SpecialPeriods.CuspFamily ThreefoldHomologyFinitenessCusp

/-- The open annulus is defined by the actual original cusp parameter. -/
def outerCollar (D : Data) (bound : ℝ) (E : CollarExtension D bound) :
    TopologicalSpace.Opens (FullSpace D) :=
  ⟨{q | E.innerRadius < parameterNorm D q},
    CollarExtension.outerCollar_isOpen D bound E⟩

theorem outerCollar_le_punctured (D : Data) (bound : ℝ) (E : CollarExtension D bound) :
    outerCollar D bound E ≤ puncturedQuotientOpen D.correction D.radius := by
  intro q hq
  exact norm_pos_iff.mp (E.innerRadius_pos.trans hq)

/-- The prescribed closed relative region is an outer collar inside the
unchanged full cap, not a compactification boundary. -/
def outerClosedCollar (D : Data) (bound : ℝ) : Set (FullSpace D) :=
  {q | bound ≤ parameterNorm D q}

theorem outerClosedCollar_isClosed (D : Data) (bound : ℝ) :
    IsClosed (outerClosedCollar D bound) :=
  isClosed_le continuous_const (parameterNorm D).continuous

theorem outerClosedCollar_subset_outer (D : Data) (bound : ℝ)
    (E : CollarExtension D bound) :
    outerClosedCollar D bound ⊆ outerCollar D bound E :=
  fun _ hq => E.innerRadius_lt_bound.trans_le hq

/-- The open annulus contains a neighborhood of the entire closed
relative collar, including all its original circle orbits. -/
theorem outerCollar_mem_nhdsSet (D : Data) (bound : ℝ) (E : CollarExtension D bound) :
    (outerCollar D bound E : Set (FullSpace D)) ∈ 𝓝ˢ (outerClosedCollar D bound) :=
  (outerCollar D bound E).isOpen.mem_nhdsSet.mpr
    (outerClosedCollar_subset_outer D bound E)

/-- The original complex vertical flow preserves the closed relative
collar because it preserves the actual cusp parameter. -/
theorem outerClosedCollar_flow (D : Data) (bound : ℝ) (s : ℂ) :
    MapsTo (SpecialPeriods.Threefold.VerticalAction.Cusp.flow D.correction D.radius s)
      (outerClosedCollar D bound) (outerClosedCollar D bound) := by
  intro q hq
  change bound ≤ ‖CuspQuotient.projection D.correction D.radius
    (SpecialPeriods.Threefold.VerticalAction.Cusp.flow D.correction D.radius s q)‖
  rw [SpecialPeriods.Threefold.VerticalAction.Cusp.projection_flow]
  exact hq

end Wikipedia.HopfProblem.CuspCoinvariantExtension.Phase
