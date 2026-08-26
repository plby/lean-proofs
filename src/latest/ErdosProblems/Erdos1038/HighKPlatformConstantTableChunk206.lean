import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 206 through 206. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk206

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_206 :
    geometryCheck (table.cell ⟨206, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_206 :
    crossingCheck (table.cell ⟨206, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_206 :
    scalarCheck (table.cell ⟨206, by decide⟩) = true := by
  kernel_decide

theorem certificate_206 :
    Certificate (table.cell ⟨206, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_206,
    crossing_of_check crossingCheck_206,
    scalar_of_check scalarCheck_206⟩

end Erdos1038.HighKPlatformConstantTableChunk206
