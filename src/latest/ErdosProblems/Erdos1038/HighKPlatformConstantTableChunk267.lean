import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 267 through 267. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk267

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_267 :
    geometryCheck (table.cell ⟨267, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_267 :
    crossingCheck (table.cell ⟨267, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_267 :
    scalarCheck (table.cell ⟨267, by decide⟩) = true := by
  kernel_decide

theorem certificate_267 :
    Certificate (table.cell ⟨267, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_267,
    crossing_of_check crossingCheck_267,
    scalar_of_check scalarCheck_267⟩

end Erdos1038.HighKPlatformConstantTableChunk267
