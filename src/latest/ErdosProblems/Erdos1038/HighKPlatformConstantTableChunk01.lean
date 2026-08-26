import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 1 through 1. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk01

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_001 :
    geometryCheck (table.cell ⟨1, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_001 :
    crossingCheck (table.cell ⟨1, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_001 :
    scalarCheck (table.cell ⟨1, by decide⟩) = true := by
  kernel_decide

theorem certificate_001 :
    Certificate (table.cell ⟨1, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_001,
    crossing_of_check crossingCheck_001,
    scalar_of_check scalarCheck_001⟩

end Erdos1038.HighKPlatformConstantTableChunk01
