import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 350 through 350. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk350

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_350 :
    geometryCheck (table.cell ⟨350, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_350 :
    crossingCheck (table.cell ⟨350, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_350 :
    scalarCheck (table.cell ⟨350, by decide⟩) = true := by
  kernel_decide

theorem certificate_350 :
    Certificate (table.cell ⟨350, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_350,
    crossing_of_check crossingCheck_350,
    scalar_of_check scalarCheck_350⟩

end Erdos1038.HighKPlatformConstantTableChunk350
