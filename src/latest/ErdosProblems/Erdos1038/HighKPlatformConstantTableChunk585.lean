import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 585 through 585. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk585

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_585 :
    geometryCheck (table.cell ⟨585, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_585 :
    crossingCheck (table.cell ⟨585, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_585 :
    scalarCheck (table.cell ⟨585, by decide⟩) = true := by
  kernel_decide

theorem certificate_585 :
    Certificate (table.cell ⟨585, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_585,
    crossing_of_check crossingCheck_585,
    scalar_of_check scalarCheck_585⟩

end Erdos1038.HighKPlatformConstantTableChunk585
