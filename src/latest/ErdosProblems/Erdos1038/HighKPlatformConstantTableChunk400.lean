import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 400 through 400. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk400

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_400 :
    geometryCheck (table.cell ⟨400, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_400 :
    crossingCheck (table.cell ⟨400, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_400 :
    scalarCheck (table.cell ⟨400, by decide⟩) = true := by
  kernel_decide

theorem certificate_400 :
    Certificate (table.cell ⟨400, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_400,
    crossing_of_check crossingCheck_400,
    scalar_of_check scalarCheck_400⟩

end Erdos1038.HighKPlatformConstantTableChunk400
