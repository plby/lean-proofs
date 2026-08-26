import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 600 through 600. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk600

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_600 :
    geometryCheck (table.cell ⟨600, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_600 :
    crossingCheck (table.cell ⟨600, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_600 :
    scalarCheck (table.cell ⟨600, by decide⟩) = true := by
  kernel_decide

theorem certificate_600 :
    Certificate (table.cell ⟨600, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_600,
    crossing_of_check crossingCheck_600,
    scalar_of_check scalarCheck_600⟩

end Erdos1038.HighKPlatformConstantTableChunk600
