import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 757 through 757. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk757

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_757 :
    geometryCheck (table.cell ⟨757, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_757 :
    crossingCheck (table.cell ⟨757, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_757 :
    scalarCheck (table.cell ⟨757, by decide⟩) = true := by
  kernel_decide

theorem certificate_757 :
    Certificate (table.cell ⟨757, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_757,
    crossing_of_check crossingCheck_757,
    scalar_of_check scalarCheck_757⟩

end Erdos1038.HighKPlatformConstantTableChunk757
