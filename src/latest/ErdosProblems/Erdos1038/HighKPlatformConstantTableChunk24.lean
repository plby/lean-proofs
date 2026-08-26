import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 24 through 24. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk24

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_024 :
    geometryCheck (table.cell ⟨24, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_024 :
    crossingCheck (table.cell ⟨24, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_024 :
    scalarCheck (table.cell ⟨24, by decide⟩) = true := by
  kernel_decide

theorem certificate_024 :
    Certificate (table.cell ⟨24, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_024,
    crossing_of_check crossingCheck_024,
    scalar_of_check scalarCheck_024⟩

end Erdos1038.HighKPlatformConstantTableChunk24
