import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 524 through 524. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk524

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_524 :
    geometryCheck (table.cell ⟨524, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_524 :
    crossingCheck (table.cell ⟨524, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_524 :
    scalarCheck (table.cell ⟨524, by decide⟩) = true := by
  kernel_decide

theorem certificate_524 :
    Certificate (table.cell ⟨524, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_524,
    crossing_of_check crossingCheck_524,
    scalar_of_check scalarCheck_524⟩

end Erdos1038.HighKPlatformConstantTableChunk524
