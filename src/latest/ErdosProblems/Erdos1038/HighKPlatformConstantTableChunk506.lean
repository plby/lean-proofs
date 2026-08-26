import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 506 through 506. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk506

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_506 :
    geometryCheck (table.cell ⟨506, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_506 :
    crossingCheck (table.cell ⟨506, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_506 :
    scalarCheck (table.cell ⟨506, by decide⟩) = true := by
  kernel_decide

theorem certificate_506 :
    Certificate (table.cell ⟨506, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_506,
    crossing_of_check crossingCheck_506,
    scalar_of_check scalarCheck_506⟩

end Erdos1038.HighKPlatformConstantTableChunk506
