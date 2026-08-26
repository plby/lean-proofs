import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 328 through 328. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk328

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_328 :
    geometryCheck (table.cell ⟨328, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_328 :
    crossingCheck (table.cell ⟨328, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_328 :
    scalarCheck (table.cell ⟨328, by decide⟩) = true := by
  kernel_decide

theorem certificate_328 :
    Certificate (table.cell ⟨328, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_328,
    crossing_of_check crossingCheck_328,
    scalar_of_check scalarCheck_328⟩

end Erdos1038.HighKPlatformConstantTableChunk328
