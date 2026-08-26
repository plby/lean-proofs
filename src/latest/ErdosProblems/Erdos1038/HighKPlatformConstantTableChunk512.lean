import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 512 through 512. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk512

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_512 :
    geometryCheck (table.cell ⟨512, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_512 :
    crossingCheck (table.cell ⟨512, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_512 :
    scalarCheck (table.cell ⟨512, by decide⟩) = true := by
  kernel_decide

theorem certificate_512 :
    Certificate (table.cell ⟨512, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_512,
    crossing_of_check crossingCheck_512,
    scalar_of_check scalarCheck_512⟩

end Erdos1038.HighKPlatformConstantTableChunk512
