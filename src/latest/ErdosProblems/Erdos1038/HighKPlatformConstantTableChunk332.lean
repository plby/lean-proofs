import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 332 through 332. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk332

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_332 :
    geometryCheck (table.cell ⟨332, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_332 :
    crossingCheck (table.cell ⟨332, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_332 :
    scalarCheck (table.cell ⟨332, by decide⟩) = true := by
  kernel_decide

theorem certificate_332 :
    Certificate (table.cell ⟨332, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_332,
    crossing_of_check crossingCheck_332,
    scalar_of_check scalarCheck_332⟩

end Erdos1038.HighKPlatformConstantTableChunk332
