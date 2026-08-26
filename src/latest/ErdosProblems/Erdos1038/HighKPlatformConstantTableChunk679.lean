import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 679 through 679. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk679

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_679 :
    geometryCheck (table.cell ⟨679, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_679 :
    crossingCheck (table.cell ⟨679, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_679 :
    scalarCheck (table.cell ⟨679, by decide⟩) = true := by
  kernel_decide

theorem certificate_679 :
    Certificate (table.cell ⟨679, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_679,
    crossing_of_check crossingCheck_679,
    scalar_of_check scalarCheck_679⟩

end Erdos1038.HighKPlatformConstantTableChunk679
