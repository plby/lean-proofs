import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 175 through 175. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk175

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_175 :
    geometryCheck (table.cell ⟨175, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_175 :
    crossingCheck (table.cell ⟨175, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_175 :
    scalarCheck (table.cell ⟨175, by decide⟩) = true := by
  kernel_decide

theorem certificate_175 :
    Certificate (table.cell ⟨175, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_175,
    crossing_of_check crossingCheck_175,
    scalar_of_check scalarCheck_175⟩

end Erdos1038.HighKPlatformConstantTableChunk175
