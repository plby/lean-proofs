import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 256 through 256. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk256

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_256 :
    geometryCheck (table.cell ⟨256, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_256 :
    crossingCheck (table.cell ⟨256, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_256 :
    scalarCheck (table.cell ⟨256, by decide⟩) = true := by
  kernel_decide

theorem certificate_256 :
    Certificate (table.cell ⟨256, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_256,
    crossing_of_check crossingCheck_256,
    scalar_of_check scalarCheck_256⟩

end Erdos1038.HighKPlatformConstantTableChunk256
