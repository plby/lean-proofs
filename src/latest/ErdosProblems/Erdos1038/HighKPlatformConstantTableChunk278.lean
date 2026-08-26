import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 278 through 278. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk278

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_278 :
    geometryCheck (table.cell ⟨278, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_278 :
    crossingCheck (table.cell ⟨278, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_278 :
    scalarCheck (table.cell ⟨278, by decide⟩) = true := by
  kernel_decide

theorem certificate_278 :
    Certificate (table.cell ⟨278, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_278,
    crossing_of_check crossingCheck_278,
    scalar_of_check scalarCheck_278⟩

end Erdos1038.HighKPlatformConstantTableChunk278
