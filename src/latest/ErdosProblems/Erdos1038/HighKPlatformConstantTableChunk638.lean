import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 638 through 638. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk638

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_638 :
    geometryCheck (table.cell ⟨638, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_638 :
    crossingCheck (table.cell ⟨638, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_638 :
    scalarCheck (table.cell ⟨638, by decide⟩) = true := by
  kernel_decide

theorem certificate_638 :
    Certificate (table.cell ⟨638, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_638,
    crossing_of_check crossingCheck_638,
    scalar_of_check scalarCheck_638⟩

end Erdos1038.HighKPlatformConstantTableChunk638
