import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 769 through 769. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk769

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_769 :
    geometryCheck (table.cell ⟨769, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_769 :
    crossingCheck (table.cell ⟨769, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_769 :
    scalarCheck (table.cell ⟨769, by decide⟩) = true := by
  kernel_decide

theorem certificate_769 :
    Certificate (table.cell ⟨769, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_769,
    crossing_of_check crossingCheck_769,
    scalar_of_check scalarCheck_769⟩

end Erdos1038.HighKPlatformConstantTableChunk769
