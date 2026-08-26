import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 90 through 90. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk90

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_090 :
    geometryCheck (table.cell ⟨90, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_090 :
    crossingCheck (table.cell ⟨90, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_090 :
    scalarCheck (table.cell ⟨90, by decide⟩) = true := by
  kernel_decide

theorem certificate_090 :
    Certificate (table.cell ⟨90, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_090,
    crossing_of_check crossingCheck_090,
    scalar_of_check scalarCheck_090⟩

end Erdos1038.HighKPlatformConstantTableChunk90
