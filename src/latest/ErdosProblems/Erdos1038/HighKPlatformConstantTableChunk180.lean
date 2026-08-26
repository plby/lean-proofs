import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 180 through 180. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk180

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_180 :
    geometryCheck (table.cell ⟨180, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_180 :
    crossingCheck (table.cell ⟨180, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_180 :
    scalarCheck (table.cell ⟨180, by decide⟩) = true := by
  kernel_decide

theorem certificate_180 :
    Certificate (table.cell ⟨180, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_180,
    crossing_of_check crossingCheck_180,
    scalar_of_check scalarCheck_180⟩

end Erdos1038.HighKPlatformConstantTableChunk180
