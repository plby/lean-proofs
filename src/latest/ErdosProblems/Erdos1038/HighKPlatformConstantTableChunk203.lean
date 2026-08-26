import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 203 through 203. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk203

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_203 :
    geometryCheck (table.cell ⟨203, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_203 :
    crossingCheck (table.cell ⟨203, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_203 :
    scalarCheck (table.cell ⟨203, by decide⟩) = true := by
  kernel_decide

theorem certificate_203 :
    Certificate (table.cell ⟨203, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_203,
    crossing_of_check crossingCheck_203,
    scalar_of_check scalarCheck_203⟩

end Erdos1038.HighKPlatformConstantTableChunk203
