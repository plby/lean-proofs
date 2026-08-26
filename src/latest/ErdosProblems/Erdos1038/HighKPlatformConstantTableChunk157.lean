import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 157 through 157. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk157

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_157 :
    geometryCheck (table.cell ⟨157, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_157 :
    crossingCheck (table.cell ⟨157, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_157 :
    scalarCheck (table.cell ⟨157, by decide⟩) = true := by
  kernel_decide

theorem certificate_157 :
    Certificate (table.cell ⟨157, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_157,
    crossing_of_check crossingCheck_157,
    scalar_of_check scalarCheck_157⟩

end Erdos1038.HighKPlatformConstantTableChunk157
