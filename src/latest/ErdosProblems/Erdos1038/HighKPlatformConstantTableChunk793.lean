import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 793 through 793. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk793

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_793 :
    geometryCheck (table.cell ⟨793, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_793 :
    crossingCheck (table.cell ⟨793, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_793 :
    scalarCheck (table.cell ⟨793, by decide⟩) = true := by
  kernel_decide

theorem certificate_793 :
    Certificate (table.cell ⟨793, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_793,
    crossing_of_check crossingCheck_793,
    scalar_of_check scalarCheck_793⟩

end Erdos1038.HighKPlatformConstantTableChunk793
