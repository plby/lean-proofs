import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 105 through 105. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk105

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_105 :
    geometryCheck (table.cell ⟨105, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_105 :
    crossingCheck (table.cell ⟨105, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_105 :
    scalarCheck (table.cell ⟨105, by decide⟩) = true := by
  kernel_decide

theorem certificate_105 :
    Certificate (table.cell ⟨105, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_105,
    crossing_of_check crossingCheck_105,
    scalar_of_check scalarCheck_105⟩

end Erdos1038.HighKPlatformConstantTableChunk105
