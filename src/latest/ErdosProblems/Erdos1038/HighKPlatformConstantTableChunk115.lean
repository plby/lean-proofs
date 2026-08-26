import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 115 through 115. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk115

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_115 :
    geometryCheck (table.cell ⟨115, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_115 :
    crossingCheck (table.cell ⟨115, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_115 :
    scalarCheck (table.cell ⟨115, by decide⟩) = true := by
  kernel_decide

theorem certificate_115 :
    Certificate (table.cell ⟨115, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_115,
    crossing_of_check crossingCheck_115,
    scalar_of_check scalarCheck_115⟩

end Erdos1038.HighKPlatformConstantTableChunk115
