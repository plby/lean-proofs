import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 15 through 15. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk15

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_015 :
    geometryCheck (table.cell ⟨15, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_015 :
    crossingCheck (table.cell ⟨15, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_015 :
    scalarCheck (table.cell ⟨15, by decide⟩) = true := by
  kernel_decide

theorem certificate_015 :
    Certificate (table.cell ⟨15, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_015,
    crossing_of_check crossingCheck_015,
    scalar_of_check scalarCheck_015⟩

end Erdos1038.HighKPlatformConstantTableChunk15
