import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 292 through 292. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk292

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_292 :
    geometryCheck (table.cell ⟨292, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_292 :
    crossingCheck (table.cell ⟨292, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_292 :
    scalarCheck (table.cell ⟨292, by decide⟩) = true := by
  kernel_decide

theorem certificate_292 :
    Certificate (table.cell ⟨292, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_292,
    crossing_of_check crossingCheck_292,
    scalar_of_check scalarCheck_292⟩

end Erdos1038.HighKPlatformConstantTableChunk292
