import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 692 through 692. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk692

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_692 :
    geometryCheck (table.cell ⟨692, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_692 :
    crossingCheck (table.cell ⟨692, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_692 :
    scalarCheck (table.cell ⟨692, by decide⟩) = true := by
  kernel_decide

theorem certificate_692 :
    Certificate (table.cell ⟨692, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_692,
    crossing_of_check crossingCheck_692,
    scalar_of_check scalarCheck_692⟩

end Erdos1038.HighKPlatformConstantTableChunk692
