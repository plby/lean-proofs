import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 532 through 532. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk532

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_532 :
    geometryCheck (table.cell ⟨532, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_532 :
    crossingCheck (table.cell ⟨532, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_532 :
    scalarCheck (table.cell ⟨532, by decide⟩) = true := by
  kernel_decide

theorem certificate_532 :
    Certificate (table.cell ⟨532, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_532,
    crossing_of_check crossingCheck_532,
    scalar_of_check scalarCheck_532⟩

end Erdos1038.HighKPlatformConstantTableChunk532
