import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 780 through 780. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk780

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_780 :
    geometryCheck (table.cell ⟨780, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_780 :
    crossingCheck (table.cell ⟨780, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_780 :
    scalarCheck (table.cell ⟨780, by decide⟩) = true := by
  kernel_decide

theorem certificate_780 :
    Certificate (table.cell ⟨780, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_780,
    crossing_of_check crossingCheck_780,
    scalar_of_check scalarCheck_780⟩

end Erdos1038.HighKPlatformConstantTableChunk780
