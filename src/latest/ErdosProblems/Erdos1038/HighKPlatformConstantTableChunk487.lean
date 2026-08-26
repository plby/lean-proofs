import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 487 through 487. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk487

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_487 :
    geometryCheck (table.cell ⟨487, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_487 :
    crossingCheck (table.cell ⟨487, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_487 :
    scalarCheck (table.cell ⟨487, by decide⟩) = true := by
  kernel_decide

theorem certificate_487 :
    Certificate (table.cell ⟨487, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_487,
    crossing_of_check crossingCheck_487,
    scalar_of_check scalarCheck_487⟩

end Erdos1038.HighKPlatformConstantTableChunk487
