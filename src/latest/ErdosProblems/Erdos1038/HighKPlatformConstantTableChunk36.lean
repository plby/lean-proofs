import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 36 through 36. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk36

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_036 :
    geometryCheck (table.cell ⟨36, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_036 :
    crossingCheck (table.cell ⟨36, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_036 :
    scalarCheck (table.cell ⟨36, by decide⟩) = true := by
  kernel_decide

theorem certificate_036 :
    Certificate (table.cell ⟨36, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_036,
    crossing_of_check crossingCheck_036,
    scalar_of_check scalarCheck_036⟩

end Erdos1038.HighKPlatformConstantTableChunk36
