import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 597 through 597. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk597

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_597 :
    geometryCheck (table.cell ⟨597, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_597 :
    crossingCheck (table.cell ⟨597, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_597 :
    scalarCheck (table.cell ⟨597, by decide⟩) = true := by
  kernel_decide

theorem certificate_597 :
    Certificate (table.cell ⟨597, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_597,
    crossing_of_check crossingCheck_597,
    scalar_of_check scalarCheck_597⟩

end Erdos1038.HighKPlatformConstantTableChunk597
