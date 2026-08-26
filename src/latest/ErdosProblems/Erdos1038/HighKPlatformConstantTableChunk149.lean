import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 149 through 149. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk149

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_149 :
    geometryCheck (table.cell ⟨149, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_149 :
    crossingCheck (table.cell ⟨149, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_149 :
    scalarCheck (table.cell ⟨149, by decide⟩) = true := by
  kernel_decide

theorem certificate_149 :
    Certificate (table.cell ⟨149, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_149,
    crossing_of_check crossingCheck_149,
    scalar_of_check scalarCheck_149⟩

end Erdos1038.HighKPlatformConstantTableChunk149
