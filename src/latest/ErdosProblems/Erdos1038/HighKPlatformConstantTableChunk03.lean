import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 3 through 3. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk03

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_003 :
    geometryCheck (table.cell ⟨3, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_003 :
    crossingCheck (table.cell ⟨3, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_003 :
    scalarCheck (table.cell ⟨3, by decide⟩) = true := by
  kernel_decide

theorem certificate_003 :
    Certificate (table.cell ⟨3, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_003,
    crossing_of_check crossingCheck_003,
    scalar_of_check scalarCheck_003⟩

end Erdos1038.HighKPlatformConstantTableChunk03
