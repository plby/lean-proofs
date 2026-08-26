import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 691 through 691. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk691

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_691 :
    geometryCheck (table.cell ⟨691, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_691 :
    crossingCheck (table.cell ⟨691, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_691 :
    scalarCheck (table.cell ⟨691, by decide⟩) = true := by
  kernel_decide

theorem certificate_691 :
    Certificate (table.cell ⟨691, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_691,
    crossing_of_check crossingCheck_691,
    scalar_of_check scalarCheck_691⟩

end Erdos1038.HighKPlatformConstantTableChunk691
