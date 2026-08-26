import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 548 through 548. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk548

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_548 :
    geometryCheck (table.cell ⟨548, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_548 :
    crossingCheck (table.cell ⟨548, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_548 :
    scalarCheck (table.cell ⟨548, by decide⟩) = true := by
  kernel_decide

theorem certificate_548 :
    Certificate (table.cell ⟨548, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_548,
    crossing_of_check crossingCheck_548,
    scalar_of_check scalarCheck_548⟩

end Erdos1038.HighKPlatformConstantTableChunk548
