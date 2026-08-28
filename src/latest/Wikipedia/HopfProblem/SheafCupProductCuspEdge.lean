import Wikipedia.HopfProblem.SheafCupProductCuspBasic
import Wikipedia.HopfProblem.SheafCupProductCuspKernelPairing

/-!
# The actual cusp constant cup takes values in the actual edge kernel

The original categorical kernel, its inclusion, and the original native
constant cup are retained. The kernel lift is additive in both variables
and the inclusion recovers that same constant cup.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff

namespace Wikipedia.HopfProblem.SheafCupProduct.Cusp

open CuspNormalization SheafResolution SheafCohomologyConstantEdge
open CuspQuotient ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

local instance constantHAddCommGroup (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) n) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- The actual native constant cup, lifted to the original categorical edge kernel. -/
def constantCupInEdge :
    CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 1 →+
      CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 1 →+
        constantH2EdgeKernel C ε hε :=
  kernelPairing (A := AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 1))
    (constantH2EdgeMap C ε hε) (constantCup (TopCat.of (CentralSpace C ε)))
    (constantCup_normalization_zero C ε hε hε1 hC hR)

/-- The literal kernel inclusion sends the lifted class to the original native cup. -/
theorem constantCupInEdge_ι
    (a b : CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 1) :
    kernel.ι (constantH2EdgeMap C ε hε) (constantCupInEdge C ε hε hε1 hC hR a b) =
      constantCup (TopCat.of (CentralSpace C ε)) a b :=
  kernelPairing_ι (A := AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 1))
    (constantH2EdgeMap C ε hε) (constantCup (TopCat.of (CentralSpace C ε)))
    (constantCup_normalization_zero C ε hε hε1 hC hR) a b

end Wikipedia.HopfProblem.SheafCupProduct.Cusp
