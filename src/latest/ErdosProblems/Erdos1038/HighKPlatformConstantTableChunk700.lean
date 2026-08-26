import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 700 through 700. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk700

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_700 :
    geometryCheck (table.cell ⟨700, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_700 :
    crossingCheck (table.cell ⟨700, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_700 :
    scalarCheck (table.cell ⟨700, by decide⟩) = true := by
  kernel_decide

theorem certificate_700 :
    Certificate (table.cell ⟨700, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_700,
    crossing_of_check crossingCheck_700,
    scalar_of_check scalarCheck_700⟩

end Erdos1038.HighKPlatformConstantTableChunk700
