import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 56 through 56. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk56

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_056 :
    geometryCheck (table.cell ⟨56, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_056 :
    crossingCheck (table.cell ⟨56, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_056 :
    scalarCheck (table.cell ⟨56, by decide⟩) = true := by
  kernel_decide

theorem certificate_056 :
    Certificate (table.cell ⟨56, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_056,
    crossing_of_check crossingCheck_056,
    scalar_of_check scalarCheck_056⟩

end Erdos1038.HighKPlatformConstantTableChunk56
