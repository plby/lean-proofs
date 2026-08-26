import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 502 through 502. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk502

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_502 :
    geometryCheck (table.cell ⟨502, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_502 :
    crossingCheck (table.cell ⟨502, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_502 :
    scalarCheck (table.cell ⟨502, by decide⟩) = true := by
  kernel_decide

theorem certificate_502 :
    Certificate (table.cell ⟨502, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_502,
    crossing_of_check crossingCheck_502,
    scalar_of_check scalarCheck_502⟩

end Erdos1038.HighKPlatformConstantTableChunk502
