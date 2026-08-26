import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 725 through 725. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk725

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_725 :
    geometryCheck (table.cell ⟨725, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_725 :
    crossingCheck (table.cell ⟨725, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_725 :
    scalarCheck (table.cell ⟨725, by decide⟩) = true := by
  kernel_decide

theorem certificate_725 :
    Certificate (table.cell ⟨725, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_725,
    crossing_of_check crossingCheck_725,
    scalar_of_check scalarCheck_725⟩

end Erdos1038.HighKPlatformConstantTableChunk725
