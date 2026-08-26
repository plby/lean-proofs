import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 770 through 770. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk770

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_770 :
    geometryCheck (table.cell ⟨770, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_770 :
    crossingCheck (table.cell ⟨770, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_770 :
    scalarCheck (table.cell ⟨770, by decide⟩) = true := by
  kernel_decide

theorem certificate_770 :
    Certificate (table.cell ⟨770, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_770,
    crossing_of_check crossingCheck_770,
    scalar_of_check scalarCheck_770⟩

end Erdos1038.HighKPlatformConstantTableChunk770
