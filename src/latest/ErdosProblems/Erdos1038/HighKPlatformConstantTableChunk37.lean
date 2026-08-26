import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 37 through 37. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk37

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_037 :
    geometryCheck (table.cell ⟨37, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_037 :
    crossingCheck (table.cell ⟨37, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_037 :
    scalarCheck (table.cell ⟨37, by decide⟩) = true := by
  kernel_decide

theorem certificate_037 :
    Certificate (table.cell ⟨37, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_037,
    crossing_of_check crossingCheck_037,
    scalar_of_check scalarCheck_037⟩

end Erdos1038.HighKPlatformConstantTableChunk37
