import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 101 through 101. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk101

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_101 :
    geometryCheck (table.cell ⟨101, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_101 :
    crossingCheck (table.cell ⟨101, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_101 :
    scalarCheck (table.cell ⟨101, by decide⟩) = true := by
  kernel_decide

theorem certificate_101 :
    Certificate (table.cell ⟨101, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_101,
    crossing_of_check crossingCheck_101,
    scalar_of_check scalarCheck_101⟩

end Erdos1038.HighKPlatformConstantTableChunk101
