import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 132 through 132. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk132

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_132 :
    geometryCheck (table.cell ⟨132, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_132 :
    crossingCheck (table.cell ⟨132, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_132 :
    scalarCheck (table.cell ⟨132, by decide⟩) = true := by
  kernel_decide

theorem certificate_132 :
    Certificate (table.cell ⟨132, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_132,
    crossing_of_check crossingCheck_132,
    scalar_of_check scalarCheck_132⟩

end Erdos1038.HighKPlatformConstantTableChunk132
