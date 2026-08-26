import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 26 through 26. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk26

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_026 :
    geometryCheck (table.cell ⟨26, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_026 :
    crossingCheck (table.cell ⟨26, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_026 :
    scalarCheck (table.cell ⟨26, by decide⟩) = true := by
  kernel_decide

theorem certificate_026 :
    Certificate (table.cell ⟨26, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_026,
    crossing_of_check crossingCheck_026,
    scalar_of_check scalarCheck_026⟩

end Erdos1038.HighKPlatformConstantTableChunk26
