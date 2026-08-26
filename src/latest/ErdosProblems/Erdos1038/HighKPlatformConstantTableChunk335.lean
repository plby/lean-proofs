import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 335 through 335. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk335

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_335 :
    geometryCheck (table.cell ⟨335, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_335 :
    crossingCheck (table.cell ⟨335, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_335 :
    scalarCheck (table.cell ⟨335, by decide⟩) = true := by
  kernel_decide

theorem certificate_335 :
    Certificate (table.cell ⟨335, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_335,
    crossing_of_check crossingCheck_335,
    scalar_of_check scalarCheck_335⟩

end Erdos1038.HighKPlatformConstantTableChunk335
