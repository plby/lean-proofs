import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 762 through 762. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk762

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_762 :
    geometryCheck (table.cell ⟨762, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_762 :
    crossingCheck (table.cell ⟨762, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_762 :
    scalarCheck (table.cell ⟨762, by decide⟩) = true := by
  kernel_decide

theorem certificate_762 :
    Certificate (table.cell ⟨762, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_762,
    crossing_of_check crossingCheck_762,
    scalar_of_check scalarCheck_762⟩

end Erdos1038.HighKPlatformConstantTableChunk762
