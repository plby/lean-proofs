import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowExtCokernelBasic
import Wikipedia.HopfProblem.SheafHigherDirectImageExtBasic

/-!
# Literal cycles in a preserved kernel

The original left-exact functor preserves the actual kernel of a short
complex. Its native cycles isomorphism therefore lifts a literal closed
element into that original kernel. The corresponding cokernel comparison
sends its projection to the ordinary class of the same literal cycle.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ExponentialChernComparison.GlobalCycle

open ConstantSheafSingularComparison.LowExt.CycleCokernel
open SheafHigherDirectImage.ExtBridge

variable {C : Type*} [Category C] [Abelian C]
    (G : C ⥤ AddCommGrpCat.{0}) [G.Additive] [PreservesFiniteLimits G]
    (S : ShortComplex C) (z : (S.map G).X₂) (hz : (S.map G).g z = 0)

/-- Lift an actual closed element through the canonical comparison with
the original kernel preserved by the given left-exact functor. -/
def preservedCycle : G.obj (kernel S.g) :=
  (mappedLeftHomologyData G S).cyclesIso.hom ((S.map G).abCyclesIso.inv ⟨z, hz⟩)

/-- The lifted element has exactly its prescribed original value. -/
theorem preservedCycle_inclusion :
    G.map (kernel.ι S.g) (preservedCycle G S z hz) = z := by
  let h := mappedLeftHomologyData G S
  let c := (S.map G).abCyclesIso.inv ⟨z, hz⟩
  change h.i (h.cyclesIso.hom c) = z
  exact (ConcreteCategory.congr_hom h.cyclesIso_hom_comp_i c).trans
    ((S.map G).abCyclesIso_inv_apply_iCycles ⟨z, hz⟩)

/-- The original cokernel comparison retains the literal cycle class,
including the prescribed sign of its representative. -/
theorem preservedCycle_class :
    (shortCokernelIsoHomology G S).hom
        (cokernel.π (G.map (toKernel S)) (preservedCycle G S z hz)) =
      shortCycleClass (S.map G) z hz := by
  let h := mappedLeftHomologyData G S
  let c := (S.map G).abCyclesIso.inv ⟨z, hz⟩
  change h.homologyIso.inv (h.π (h.cyclesIso.hom c)) = (S.map G).homologyπ c
  have hp := ConcreteCategory.congr_hom h.homologyπ_comp_homologyIso_hom c
  exact (congrArg h.homologyIso.inv hp.symm).trans
    (ConcreteCategory.congr_hom h.homologyIso.hom_inv_id ((S.map G).homologyπ c))

end Wikipedia.HopfProblem.ExponentialChernComparison.GlobalCycle
