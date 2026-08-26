import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 824 through 824. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk824

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_824 :
    geometryCheck (table.cell ⟨824, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_824 :
    crossingCheck (table.cell ⟨824, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_824 :
    scalarCheck (table.cell ⟨824, by decide⟩) = true := by
  kernel_decide

theorem certificate_824 :
    Certificate (table.cell ⟨824, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_824,
    crossing_of_check crossingCheck_824,
    scalar_of_check scalarCheck_824⟩

end Erdos1038.HighKPlatformConstantTableChunk824
