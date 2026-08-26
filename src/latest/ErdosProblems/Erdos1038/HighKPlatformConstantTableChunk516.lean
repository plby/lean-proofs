import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 516 through 516. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk516

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_516 :
    geometryCheck (table.cell ⟨516, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_516 :
    crossingCheck (table.cell ⟨516, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_516 :
    scalarCheck (table.cell ⟨516, by decide⟩) = true := by
  kernel_decide

theorem certificate_516 :
    Certificate (table.cell ⟨516, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_516,
    crossing_of_check crossingCheck_516,
    scalar_of_check scalarCheck_516⟩

end Erdos1038.HighKPlatformConstantTableChunk516
