import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 734 through 734. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk734

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_734 :
    geometryCheck (table.cell ⟨734, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_734 :
    crossingCheck (table.cell ⟨734, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_734 :
    scalarCheck (table.cell ⟨734, by decide⟩) = true := by
  kernel_decide

theorem certificate_734 :
    Certificate (table.cell ⟨734, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_734,
    crossing_of_check crossingCheck_734,
    scalar_of_check scalarCheck_734⟩

end Erdos1038.HighKPlatformConstantTableChunk734
