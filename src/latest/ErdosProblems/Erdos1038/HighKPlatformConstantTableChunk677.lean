import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 677 through 677. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk677

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_677 :
    geometryCheck (table.cell ⟨677, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_677 :
    crossingCheck (table.cell ⟨677, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_677 :
    scalarCheck (table.cell ⟨677, by decide⟩) = true := by
  kernel_decide

theorem certificate_677 :
    Certificate (table.cell ⟨677, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_677,
    crossing_of_check crossingCheck_677,
    scalar_of_check scalarCheck_677⟩

end Erdos1038.HighKPlatformConstantTableChunk677
