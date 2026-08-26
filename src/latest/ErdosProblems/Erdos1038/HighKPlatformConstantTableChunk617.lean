import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 617 through 617. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk617

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_617 :
    geometryCheck (table.cell ⟨617, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_617 :
    crossingCheck (table.cell ⟨617, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_617 :
    scalarCheck (table.cell ⟨617, by decide⟩) = true := by
  kernel_decide

theorem certificate_617 :
    Certificate (table.cell ⟨617, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_617,
    crossing_of_check crossingCheck_617,
    scalar_of_check scalarCheck_617⟩

end Erdos1038.HighKPlatformConstantTableChunk617
