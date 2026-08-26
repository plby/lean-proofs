import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 584 through 584. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk584

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_584 :
    geometryCheck (table.cell ⟨584, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_584 :
    crossingCheck (table.cell ⟨584, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_584 :
    scalarCheck (table.cell ⟨584, by decide⟩) = true := by
  kernel_decide

theorem certificate_584 :
    Certificate (table.cell ⟨584, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_584,
    crossing_of_check crossingCheck_584,
    scalar_of_check scalarCheck_584⟩

end Erdos1038.HighKPlatformConstantTableChunk584
