import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 20 through 20. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk20

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_020 :
    geometryCheck (table.cell ⟨20, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_020 :
    crossingCheck (table.cell ⟨20, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_020 :
    scalarCheck (table.cell ⟨20, by decide⟩) = true := by
  kernel_decide

theorem certificate_020 :
    Certificate (table.cell ⟨20, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_020,
    crossing_of_check crossingCheck_020,
    scalar_of_check scalarCheck_020⟩

end Erdos1038.HighKPlatformConstantTableChunk20
