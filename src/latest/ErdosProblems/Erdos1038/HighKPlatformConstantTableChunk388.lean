import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 388 through 388. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk388

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_388 :
    geometryCheck (table.cell ⟨388, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_388 :
    crossingCheck (table.cell ⟨388, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_388 :
    scalarCheck (table.cell ⟨388, by decide⟩) = true := by
  kernel_decide

theorem certificate_388 :
    Certificate (table.cell ⟨388, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_388,
    crossing_of_check crossingCheck_388,
    scalar_of_check scalarCheck_388⟩

end Erdos1038.HighKPlatformConstantTableChunk388
