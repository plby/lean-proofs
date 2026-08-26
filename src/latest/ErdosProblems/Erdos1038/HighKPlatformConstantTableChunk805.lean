import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 805 through 805. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk805

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_805 :
    geometryCheck (table.cell ⟨805, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_805 :
    crossingCheck (table.cell ⟨805, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_805 :
    scalarCheck (table.cell ⟨805, by decide⟩) = true := by
  kernel_decide

theorem certificate_805 :
    Certificate (table.cell ⟨805, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_805,
    crossing_of_check crossingCheck_805,
    scalar_of_check scalarCheck_805⟩

end Erdos1038.HighKPlatformConstantTableChunk805
