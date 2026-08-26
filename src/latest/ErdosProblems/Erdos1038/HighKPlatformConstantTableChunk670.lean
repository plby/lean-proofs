import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 670 through 670. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk670

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_670 :
    geometryCheck (table.cell ⟨670, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_670 :
    crossingCheck (table.cell ⟨670, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_670 :
    scalarCheck (table.cell ⟨670, by decide⟩) = true := by
  kernel_decide

theorem certificate_670 :
    Certificate (table.cell ⟨670, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_670,
    crossing_of_check crossingCheck_670,
    scalar_of_check scalarCheck_670⟩

end Erdos1038.HighKPlatformConstantTableChunk670
