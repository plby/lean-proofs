import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 301 through 301. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk301

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_301 :
    geometryCheck (table.cell ⟨301, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_301 :
    crossingCheck (table.cell ⟨301, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_301 :
    scalarCheck (table.cell ⟨301, by decide⟩) = true := by
  kernel_decide

theorem certificate_301 :
    Certificate (table.cell ⟨301, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_301,
    crossing_of_check crossingCheck_301,
    scalar_of_check scalarCheck_301⟩

end Erdos1038.HighKPlatformConstantTableChunk301
