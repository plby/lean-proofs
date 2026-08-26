import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 103 through 103. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk103

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_103 :
    geometryCheck (table.cell ⟨103, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_103 :
    crossingCheck (table.cell ⟨103, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_103 :
    scalarCheck (table.cell ⟨103, by decide⟩) = true := by
  kernel_decide

theorem certificate_103 :
    Certificate (table.cell ⟨103, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_103,
    crossing_of_check crossingCheck_103,
    scalar_of_check scalarCheck_103⟩

end Erdos1038.HighKPlatformConstantTableChunk103
