import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 32 through 32. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk32

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_032 :
    geometryCheck (table.cell ⟨32, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_032 :
    crossingCheck (table.cell ⟨32, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_032 :
    scalarCheck (table.cell ⟨32, by decide⟩) = true := by
  kernel_decide

theorem certificate_032 :
    Certificate (table.cell ⟨32, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_032,
    crossing_of_check crossingCheck_032,
    scalar_of_check scalarCheck_032⟩

end Erdos1038.HighKPlatformConstantTableChunk32
