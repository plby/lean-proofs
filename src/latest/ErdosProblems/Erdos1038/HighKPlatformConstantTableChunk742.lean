import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 742 through 742. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk742

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_742 :
    geometryCheck (table.cell ⟨742, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_742 :
    crossingCheck (table.cell ⟨742, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_742 :
    scalarCheck (table.cell ⟨742, by decide⟩) = true := by
  kernel_decide

theorem certificate_742 :
    Certificate (table.cell ⟨742, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_742,
    crossing_of_check crossingCheck_742,
    scalar_of_check scalarCheck_742⟩

end Erdos1038.HighKPlatformConstantTableChunk742
