import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 42 through 42. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk42

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_042 :
    geometryCheck (table.cell ⟨42, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_042 :
    crossingCheck (table.cell ⟨42, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_042 :
    scalarCheck (table.cell ⟨42, by decide⟩) = true := by
  kernel_decide

theorem certificate_042 :
    Certificate (table.cell ⟨42, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_042,
    crossing_of_check crossingCheck_042,
    scalar_of_check scalarCheck_042⟩

end Erdos1038.HighKPlatformConstantTableChunk42
