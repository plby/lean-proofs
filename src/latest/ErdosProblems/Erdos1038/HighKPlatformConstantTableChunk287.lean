import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 287 through 287. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk287

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_287 :
    geometryCheck (table.cell ⟨287, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_287 :
    crossingCheck (table.cell ⟨287, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_287 :
    scalarCheck (table.cell ⟨287, by decide⟩) = true := by
  kernel_decide

theorem certificate_287 :
    Certificate (table.cell ⟨287, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_287,
    crossing_of_check crossingCheck_287,
    scalar_of_check scalarCheck_287⟩

end Erdos1038.HighKPlatformConstantTableChunk287
