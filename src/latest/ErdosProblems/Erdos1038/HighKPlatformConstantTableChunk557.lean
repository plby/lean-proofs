import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 557 through 557. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk557

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_557 :
    geometryCheck (table.cell ⟨557, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_557 :
    crossingCheck (table.cell ⟨557, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_557 :
    scalarCheck (table.cell ⟨557, by decide⟩) = true := by
  kernel_decide

theorem certificate_557 :
    Certificate (table.cell ⟨557, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_557,
    crossing_of_check crossingCheck_557,
    scalar_of_check scalarCheck_557⟩

end Erdos1038.HighKPlatformConstantTableChunk557
