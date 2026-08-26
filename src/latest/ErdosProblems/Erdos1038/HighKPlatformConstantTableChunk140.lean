import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 140 through 140. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk140

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_140 :
    geometryCheck (table.cell ⟨140, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_140 :
    crossingCheck (table.cell ⟨140, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_140 :
    scalarCheck (table.cell ⟨140, by decide⟩) = true := by
  kernel_decide

theorem certificate_140 :
    Certificate (table.cell ⟨140, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_140,
    crossing_of_check crossingCheck_140,
    scalar_of_check scalarCheck_140⟩

end Erdos1038.HighKPlatformConstantTableChunk140
