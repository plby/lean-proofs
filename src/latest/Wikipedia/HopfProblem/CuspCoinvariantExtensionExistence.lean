import Wikipedia.HopfProblem.CuspCoinvariantExtensionActual
import Wikipedia.HopfProblem.CuspCoinvariantExtensionCentral

/-!
# A collar-adjusted gamma extension on the original full cusp cap

For every original cusp datum and every prescribed positive bound, there
is a continuous circle map on the entire actual cusp quotient.  It agrees
with the original punctured gamma beyond a smaller positive radius,
retains the marked coordinate on the actual central fibre, and is
invariant under the original real delta flow everywhere.

Both the controlled deformation and its working radius are constructed
from the existing holomorphic cusp data.  In particular, no extension,
submersion, product presentation, or sphere recognition is assumed.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCoinvariantExtension

open CuspUniformization CuspRetraction SpecialPeriods.CuspFamily
open ThreefoldHomologyFinitenessCusp

/-- A genuinely constructed collar-adjusted map, with all values and
symmetries referring to the original cusp quotient. -/
structure CollarExtension (D : Data) (bound : ℝ) where
  innerRadius : ℝ
  innerRadius_pos : 0 < innerRadius
  innerRadius_lt_bound : innerRadius < bound
  innerRadius_lt_radius : innerRadius < D.radius
  map : C(FullSpace D, AddCircle (1 : ℝ))
  central : ∀ q : QuotientCentralFibre D.correction D.radius,
    map q.val = centralGamma D.correction D.radius D.radius_pos D.holomorphic q
  realFlow : ∀ (t : ℝ) (q : FullSpace D),
    map (SpecialPeriods.Threefold.VerticalAction.Cusp.flow D.correction D.radius (t : ℂ) q) =
      map q
  outer : ∀ q : PuncturedQuotient D.correction D.radius,
    innerRadius ≤ parameterNorm D q.val → map q.val = puncturedGamma D q

/-- The existence theorem has no filling or extension hypothesis: a
controlled native closed core supplies all the pasting data. -/
theorem exists_collarExtension (D : Data) (bound : ℝ) (hbound : 0 < bound) :
    Nonempty (CollarExtension D bound) := by
  obtain ⟨η₀, hη₀, hη₀r, _hη₀1, hcore⟩ := exists_closed_core_gamma D
  let η := min η₀ (bound / 2)
  have hη : 0 < η := lt_min hη₀ (half_pos hbound)
  have hηη₀ : η ≤ η₀ := min_le_left _ _
  have hηbound : η < bound :=
    (min_le_right η₀ (bound / 2)).trans_lt (half_lt_self hbound)
  have hηr : η < D.radius := hηη₀.trans_lt hη₀r
  obtain ⟨core, hcentral, hphase, hshell⟩ := hcore η hη hηη₀ η hη le_rfl
  exact ⟨{
    innerRadius := η
    innerRadius_pos := hη
    innerRadius_lt_bound := hηbound
    innerRadius_lt_radius := hηr
    map := capGammaFromCore D hη hηr core (hshell hηr)
    central := capGammaFromCore_central D hη hηr core (hshell hηr) hcentral
    realFlow := capGammaFromCore_realFlow D hη hηr core (hshell hηr) (hphase hηr)
    outer := capGammaFromCore_outer D hη hηr core (hshell hηr) }⟩

/-- Choose one of the proved native collar-adjusted extensions. -/
def collarExtension (D : Data) (bound : ℝ) (hbound : 0 < bound) :
    CollarExtension D bound := Classical.choice (exists_collarExtension D bound hbound)

/-- A full positive outer annulus is an actual open subset of the cap. -/
theorem CollarExtension.outerCollar_isOpen (D : Data) (bound : ℝ)
    (E : CollarExtension D bound) :
    IsOpen {q : FullSpace D | E.innerRadius < parameterNorm D q} :=
  isOpen_lt continuous_const (parameterNorm D).continuous

/-- On that entire open collar, the extension is literally the original
punctured gamma map. -/
theorem CollarExtension.outerCollar_eq (D : Data) (bound : ℝ)
    (E : CollarExtension D bound) (q : FullSpace D)
    (hq : E.innerRadius < parameterNorm D q) :
    E.map q = puncturedGamma D
      ⟨q, norm_pos_iff.mp (E.innerRadius_pos.trans hq)⟩ :=
  E.outer ⟨q, norm_pos_iff.mp (E.innerRadius_pos.trans hq)⟩ hq.le

end Wikipedia.HopfProblem.CuspCoinvariantExtension
