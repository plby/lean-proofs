import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 35 through 35. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk35

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_035 :
    geometryCheck (table.cell ⟨35, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_035 :
    crossingCheck (table.cell ⟨35, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_035 :
    scalarCheck (table.cell ⟨35, by decide⟩) = true := by
  kernel_decide

theorem certificate_035 :
    Certificate (table.cell ⟨35, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_035,
    crossing_of_check crossingCheck_035,
    scalar_of_check scalarCheck_035⟩

end Erdos1038.HighKPlatformConstantTableChunk35
