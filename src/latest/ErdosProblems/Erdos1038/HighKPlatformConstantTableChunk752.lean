import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 752 through 752. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk752

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_752 :
    geometryCheck (table.cell ⟨752, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_752 :
    crossingCheck (table.cell ⟨752, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_752 :
    scalarCheck (table.cell ⟨752, by decide⟩) = true := by
  kernel_decide

theorem certificate_752 :
    Certificate (table.cell ⟨752, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_752,
    crossing_of_check crossingCheck_752,
    scalar_of_check scalarCheck_752⟩

end Erdos1038.HighKPlatformConstantTableChunk752
