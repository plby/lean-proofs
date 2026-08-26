import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 354 through 354. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk354

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_354 :
    geometryCheck (table.cell ⟨354, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_354 :
    crossingCheck (table.cell ⟨354, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_354 :
    scalarCheck (table.cell ⟨354, by decide⟩) = true := by
  kernel_decide

theorem certificate_354 :
    Certificate (table.cell ⟨354, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_354,
    crossing_of_check crossingCheck_354,
    scalar_of_check scalarCheck_354⟩

end Erdos1038.HighKPlatformConstantTableChunk354
