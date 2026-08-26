import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 540 through 540. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk540

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_540 :
    geometryCheck (table.cell ⟨540, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_540 :
    crossingCheck (table.cell ⟨540, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_540 :
    scalarCheck (table.cell ⟨540, by decide⟩) = true := by
  kernel_decide

theorem certificate_540 :
    Certificate (table.cell ⟨540, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_540,
    crossing_of_check crossingCheck_540,
    scalar_of_check scalarCheck_540⟩

end Erdos1038.HighKPlatformConstantTableChunk540
