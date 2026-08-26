import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 783 through 783. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk783

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_783 :
    geometryCheck (table.cell ⟨783, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_783 :
    crossingCheck (table.cell ⟨783, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_783 :
    scalarCheck (table.cell ⟨783, by decide⟩) = true := by
  kernel_decide

theorem certificate_783 :
    Certificate (table.cell ⟨783, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_783,
    crossing_of_check crossingCheck_783,
    scalar_of_check scalarCheck_783⟩

end Erdos1038.HighKPlatformConstantTableChunk783
