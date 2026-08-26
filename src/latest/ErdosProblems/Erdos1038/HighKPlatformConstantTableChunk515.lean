import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 515 through 515. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk515

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_515 :
    geometryCheck (table.cell ⟨515, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_515 :
    crossingCheck (table.cell ⟨515, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_515 :
    scalarCheck (table.cell ⟨515, by decide⟩) = true := by
  kernel_decide

theorem certificate_515 :
    Certificate (table.cell ⟨515, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_515,
    crossing_of_check crossingCheck_515,
    scalar_of_check scalarCheck_515⟩

end Erdos1038.HighKPlatformConstantTableChunk515
