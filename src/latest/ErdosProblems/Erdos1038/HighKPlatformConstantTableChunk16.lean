import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 16 through 16. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk16

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_016 :
    geometryCheck (table.cell ⟨16, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_016 :
    crossingCheck (table.cell ⟨16, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_016 :
    scalarCheck (table.cell ⟨16, by decide⟩) = true := by
  kernel_decide

theorem certificate_016 :
    Certificate (table.cell ⟨16, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_016,
    crossing_of_check crossingCheck_016,
    scalar_of_check scalarCheck_016⟩

end Erdos1038.HighKPlatformConstantTableChunk16
