import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 808 through 808. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk808

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_808 :
    geometryCheck (table.cell ⟨808, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_808 :
    crossingCheck (table.cell ⟨808, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_808 :
    scalarCheck (table.cell ⟨808, by decide⟩) = true := by
  kernel_decide

theorem certificate_808 :
    Certificate (table.cell ⟨808, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_808,
    crossing_of_check crossingCheck_808,
    scalar_of_check scalarCheck_808⟩

end Erdos1038.HighKPlatformConstantTableChunk808
