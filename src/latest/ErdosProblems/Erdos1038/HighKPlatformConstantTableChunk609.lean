import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 609 through 609. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk609

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_609 :
    geometryCheck (table.cell ⟨609, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_609 :
    crossingCheck (table.cell ⟨609, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_609 :
    scalarCheck (table.cell ⟨609, by decide⟩) = true := by
  kernel_decide

theorem certificate_609 :
    Certificate (table.cell ⟨609, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_609,
    crossing_of_check crossingCheck_609,
    scalar_of_check scalarCheck_609⟩

end Erdos1038.HighKPlatformConstantTableChunk609
