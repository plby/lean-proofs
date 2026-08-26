import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 2 through 2. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk02

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_002 :
    geometryCheck (table.cell ⟨2, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_002 :
    crossingCheck (table.cell ⟨2, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_002 :
    scalarCheck (table.cell ⟨2, by decide⟩) = true := by
  kernel_decide

theorem certificate_002 :
    Certificate (table.cell ⟨2, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_002,
    crossing_of_check crossingCheck_002,
    scalar_of_check scalarCheck_002⟩

end Erdos1038.HighKPlatformConstantTableChunk02
