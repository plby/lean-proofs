import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 820 through 820. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk820

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_820 :
    geometryCheck (table.cell ⟨820, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_820 :
    crossingCheck (table.cell ⟨820, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_820 :
    scalarCheck (table.cell ⟨820, by decide⟩) = true := by
  kernel_decide

theorem certificate_820 :
    Certificate (table.cell ⟨820, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_820,
    crossing_of_check crossingCheck_820,
    scalar_of_check scalarCheck_820⟩

end Erdos1038.HighKPlatformConstantTableChunk820
