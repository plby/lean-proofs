import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 9 through 9. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk09

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_009 :
    geometryCheck (table.cell ⟨9, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_009 :
    crossingCheck (table.cell ⟨9, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_009 :
    scalarCheck (table.cell ⟨9, by decide⟩) = true := by
  kernel_decide

theorem certificate_009 :
    Certificate (table.cell ⟨9, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_009,
    crossing_of_check crossingCheck_009,
    scalar_of_check scalarCheck_009⟩

end Erdos1038.HighKPlatformConstantTableChunk09
