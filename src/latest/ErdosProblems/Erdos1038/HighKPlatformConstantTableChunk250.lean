import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 250 through 250. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk250

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_250 :
    geometryCheck (table.cell ⟨250, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_250 :
    crossingCheck (table.cell ⟨250, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_250 :
    scalarCheck (table.cell ⟨250, by decide⟩) = true := by
  kernel_decide

theorem certificate_250 :
    Certificate (table.cell ⟨250, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_250,
    crossing_of_check crossingCheck_250,
    scalar_of_check scalarCheck_250⟩

end Erdos1038.HighKPlatformConstantTableChunk250
