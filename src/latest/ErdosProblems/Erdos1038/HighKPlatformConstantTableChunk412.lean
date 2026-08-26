import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 412 through 412. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk412

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_412 :
    geometryCheck (table.cell ⟨412, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_412 :
    crossingCheck (table.cell ⟨412, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_412 :
    scalarCheck (table.cell ⟨412, by decide⟩) = true := by
  kernel_decide

theorem certificate_412 :
    Certificate (table.cell ⟨412, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_412,
    crossing_of_check crossingCheck_412,
    scalar_of_check scalarCheck_412⟩

end Erdos1038.HighKPlatformConstantTableChunk412
