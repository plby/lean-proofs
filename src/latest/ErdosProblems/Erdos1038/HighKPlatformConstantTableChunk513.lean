import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 513 through 513. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk513

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_513 :
    geometryCheck (table.cell ⟨513, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_513 :
    crossingCheck (table.cell ⟨513, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_513 :
    scalarCheck (table.cell ⟨513, by decide⟩) = true := by
  kernel_decide

theorem certificate_513 :
    Certificate (table.cell ⟨513, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_513,
    crossing_of_check crossingCheck_513,
    scalar_of_check scalarCheck_513⟩

end Erdos1038.HighKPlatformConstantTableChunk513
