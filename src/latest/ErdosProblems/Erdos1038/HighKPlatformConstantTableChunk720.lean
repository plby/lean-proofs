import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 720 through 720. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk720

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_720 :
    geometryCheck (table.cell ⟨720, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_720 :
    crossingCheck (table.cell ⟨720, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_720 :
    scalarCheck (table.cell ⟨720, by decide⟩) = true := by
  kernel_decide

theorem certificate_720 :
    Certificate (table.cell ⟨720, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_720,
    crossing_of_check crossingCheck_720,
    scalar_of_check scalarCheck_720⟩

end Erdos1038.HighKPlatformConstantTableChunk720
