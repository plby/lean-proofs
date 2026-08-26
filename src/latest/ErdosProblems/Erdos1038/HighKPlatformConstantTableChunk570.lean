import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 570 through 570. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk570

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_570 :
    geometryCheck (table.cell ⟨570, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_570 :
    crossingCheck (table.cell ⟨570, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_570 :
    scalarCheck (table.cell ⟨570, by decide⟩) = true := by
  kernel_decide

theorem certificate_570 :
    Certificate (table.cell ⟨570, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_570,
    crossing_of_check crossingCheck_570,
    scalar_of_check scalarCheck_570⟩

end Erdos1038.HighKPlatformConstantTableChunk570
