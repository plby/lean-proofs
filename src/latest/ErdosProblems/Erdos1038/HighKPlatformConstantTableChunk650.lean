import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 650 through 650. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk650

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_650 :
    geometryCheck (table.cell ⟨650, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_650 :
    crossingCheck (table.cell ⟨650, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_650 :
    scalarCheck (table.cell ⟨650, by decide⟩) = true := by
  kernel_decide

theorem certificate_650 :
    Certificate (table.cell ⟨650, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_650,
    crossing_of_check crossingCheck_650,
    scalar_of_check scalarCheck_650⟩

end Erdos1038.HighKPlatformConstantTableChunk650
