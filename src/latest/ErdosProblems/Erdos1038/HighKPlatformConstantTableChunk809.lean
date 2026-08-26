import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 809 through 809. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk809

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_809 :
    geometryCheck (table.cell ⟨809, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_809 :
    crossingCheck (table.cell ⟨809, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_809 :
    scalarCheck (table.cell ⟨809, by decide⟩) = true := by
  kernel_decide

theorem certificate_809 :
    Certificate (table.cell ⟨809, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_809,
    crossing_of_check crossingCheck_809,
    scalar_of_check scalarCheck_809⟩

end Erdos1038.HighKPlatformConstantTableChunk809
