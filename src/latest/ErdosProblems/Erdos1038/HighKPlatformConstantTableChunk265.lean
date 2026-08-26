import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 265 through 265. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk265

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_265 :
    geometryCheck (table.cell ⟨265, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_265 :
    crossingCheck (table.cell ⟨265, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_265 :
    scalarCheck (table.cell ⟨265, by decide⟩) = true := by
  kernel_decide

theorem certificate_265 :
    Certificate (table.cell ⟨265, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_265,
    crossing_of_check crossingCheck_265,
    scalar_of_check scalarCheck_265⟩

end Erdos1038.HighKPlatformConstantTableChunk265
