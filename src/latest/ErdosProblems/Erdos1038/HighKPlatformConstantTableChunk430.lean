import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 430 through 430. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk430

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_430 :
    geometryCheck (table.cell ⟨430, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_430 :
    crossingCheck (table.cell ⟨430, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_430 :
    scalarCheck (table.cell ⟨430, by decide⟩) = true := by
  kernel_decide

theorem certificate_430 :
    Certificate (table.cell ⟨430, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_430,
    crossing_of_check crossingCheck_430,
    scalar_of_check scalarCheck_430⟩

end Erdos1038.HighKPlatformConstantTableChunk430
