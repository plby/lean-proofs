import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 470 through 470. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk470

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_470 :
    geometryCheck (table.cell ⟨470, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_470 :
    crossingCheck (table.cell ⟨470, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_470 :
    scalarCheck (table.cell ⟨470, by decide⟩) = true := by
  kernel_decide

theorem certificate_470 :
    Certificate (table.cell ⟨470, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_470,
    crossing_of_check crossingCheck_470,
    scalar_of_check scalarCheck_470⟩

end Erdos1038.HighKPlatformConstantTableChunk470
