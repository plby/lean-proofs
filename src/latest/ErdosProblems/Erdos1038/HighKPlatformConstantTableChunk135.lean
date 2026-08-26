import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 135 through 135. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk135

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_135 :
    geometryCheck (table.cell ⟨135, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_135 :
    crossingCheck (table.cell ⟨135, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_135 :
    scalarCheck (table.cell ⟨135, by decide⟩) = true := by
  kernel_decide

theorem certificate_135 :
    Certificate (table.cell ⟨135, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_135,
    crossing_of_check crossingCheck_135,
    scalar_of_check scalarCheck_135⟩

end Erdos1038.HighKPlatformConstantTableChunk135
