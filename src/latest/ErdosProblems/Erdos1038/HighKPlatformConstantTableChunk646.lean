import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 646 through 646. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk646

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_646 :
    geometryCheck (table.cell ⟨646, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_646 :
    crossingCheck (table.cell ⟨646, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_646 :
    scalarCheck (table.cell ⟨646, by decide⟩) = true := by
  kernel_decide

theorem certificate_646 :
    Certificate (table.cell ⟨646, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_646,
    crossing_of_check crossingCheck_646,
    scalar_of_check scalarCheck_646⟩

end Erdos1038.HighKPlatformConstantTableChunk646
