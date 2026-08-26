import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 669 through 669. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk669

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_669 :
    geometryCheck (table.cell ⟨669, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_669 :
    crossingCheck (table.cell ⟨669, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_669 :
    scalarCheck (table.cell ⟨669, by decide⟩) = true := by
  kernel_decide

theorem certificate_669 :
    Certificate (table.cell ⟨669, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_669,
    crossing_of_check crossingCheck_669,
    scalar_of_check scalarCheck_669⟩

end Erdos1038.HighKPlatformConstantTableChunk669
