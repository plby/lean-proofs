import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 99 through 99. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk99

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_099 :
    geometryCheck (table.cell ⟨99, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_099 :
    crossingCheck (table.cell ⟨99, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_099 :
    scalarCheck (table.cell ⟨99, by decide⟩) = true := by
  kernel_decide

theorem certificate_099 :
    Certificate (table.cell ⟨99, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_099,
    crossing_of_check crossingCheck_099,
    scalar_of_check scalarCheck_099⟩

end Erdos1038.HighKPlatformConstantTableChunk99
