import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 833 through 833. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk833

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_833 :
    geometryCheck (table.cell ⟨833, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_833 :
    crossingCheck (table.cell ⟨833, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_833 :
    scalarCheck (table.cell ⟨833, by decide⟩) = true := by
  kernel_decide

theorem certificate_833 :
    Certificate (table.cell ⟨833, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_833,
    crossing_of_check crossingCheck_833,
    scalar_of_check scalarCheck_833⟩

end Erdos1038.HighKPlatformConstantTableChunk833
