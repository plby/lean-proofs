import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 642 through 642. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk642

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_642 :
    geometryCheck (table.cell ⟨642, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_642 :
    crossingCheck (table.cell ⟨642, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_642 :
    scalarCheck (table.cell ⟨642, by decide⟩) = true := by
  kernel_decide

theorem certificate_642 :
    Certificate (table.cell ⟨642, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_642,
    crossing_of_check crossingCheck_642,
    scalar_of_check scalarCheck_642⟩

end Erdos1038.HighKPlatformConstantTableChunk642
