import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 227 through 227. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk227

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_227 :
    geometryCheck (table.cell ⟨227, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_227 :
    crossingCheck (table.cell ⟨227, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_227 :
    scalarCheck (table.cell ⟨227, by decide⟩) = true := by
  kernel_decide

theorem certificate_227 :
    Certificate (table.cell ⟨227, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_227,
    crossing_of_check crossingCheck_227,
    scalar_of_check scalarCheck_227⟩

end Erdos1038.HighKPlatformConstantTableChunk227
