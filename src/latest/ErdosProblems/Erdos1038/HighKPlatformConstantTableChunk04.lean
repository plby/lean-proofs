import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 4 through 4. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk04

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_004 :
    geometryCheck (table.cell ⟨4, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_004 :
    crossingCheck (table.cell ⟨4, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_004 :
    scalarCheck (table.cell ⟨4, by decide⟩) = true := by
  kernel_decide

theorem certificate_004 :
    Certificate (table.cell ⟨4, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_004,
    crossing_of_check crossingCheck_004,
    scalar_of_check scalarCheck_004⟩

end Erdos1038.HighKPlatformConstantTableChunk04
