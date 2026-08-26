import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 53 through 53. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk53

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_053 :
    geometryCheck (table.cell ⟨53, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_053 :
    crossingCheck (table.cell ⟨53, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_053 :
    scalarCheck (table.cell ⟨53, by decide⟩) = true := by
  kernel_decide

theorem certificate_053 :
    Certificate (table.cell ⟨53, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_053,
    crossing_of_check crossingCheck_053,
    scalar_of_check scalarCheck_053⟩

end Erdos1038.HighKPlatformConstantTableChunk53
