import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 687 through 687. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk687

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_687 :
    geometryCheck (table.cell ⟨687, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_687 :
    crossingCheck (table.cell ⟨687, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_687 :
    scalarCheck (table.cell ⟨687, by decide⟩) = true := by
  kernel_decide

theorem certificate_687 :
    Certificate (table.cell ⟨687, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_687,
    crossing_of_check crossingCheck_687,
    scalar_of_check scalarCheck_687⟩

end Erdos1038.HighKPlatformConstantTableChunk687
