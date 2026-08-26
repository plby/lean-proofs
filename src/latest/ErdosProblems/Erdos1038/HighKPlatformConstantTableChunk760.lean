import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 760 through 760. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk760

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_760 :
    geometryCheck (table.cell ⟨760, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_760 :
    crossingCheck (table.cell ⟨760, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_760 :
    scalarCheck (table.cell ⟨760, by decide⟩) = true := by
  kernel_decide

theorem certificate_760 :
    Certificate (table.cell ⟨760, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_760,
    crossing_of_check crossingCheck_760,
    scalar_of_check scalarCheck_760⟩

end Erdos1038.HighKPlatformConstantTableChunk760
