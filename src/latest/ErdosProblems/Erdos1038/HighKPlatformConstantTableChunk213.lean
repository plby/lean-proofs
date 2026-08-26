import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 213 through 213. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk213

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_213 :
    geometryCheck (table.cell ⟨213, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_213 :
    crossingCheck (table.cell ⟨213, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_213 :
    scalarCheck (table.cell ⟨213, by decide⟩) = true := by
  kernel_decide

theorem certificate_213 :
    Certificate (table.cell ⟨213, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_213,
    crossing_of_check crossingCheck_213,
    scalar_of_check scalarCheck_213⟩

end Erdos1038.HighKPlatformConstantTableChunk213
