import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 678 through 678. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk678

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_678 :
    geometryCheck (table.cell ⟨678, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_678 :
    crossingCheck (table.cell ⟨678, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_678 :
    scalarCheck (table.cell ⟨678, by decide⟩) = true := by
  kernel_decide

theorem certificate_678 :
    Certificate (table.cell ⟨678, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_678,
    crossing_of_check crossingCheck_678,
    scalar_of_check scalarCheck_678⟩

end Erdos1038.HighKPlatformConstantTableChunk678
