import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 107 through 107. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk107

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_107 :
    geometryCheck (table.cell ⟨107, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_107 :
    crossingCheck (table.cell ⟨107, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_107 :
    scalarCheck (table.cell ⟨107, by decide⟩) = true := by
  kernel_decide

theorem certificate_107 :
    Certificate (table.cell ⟨107, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_107,
    crossing_of_check crossingCheck_107,
    scalar_of_check scalarCheck_107⟩

end Erdos1038.HighKPlatformConstantTableChunk107
