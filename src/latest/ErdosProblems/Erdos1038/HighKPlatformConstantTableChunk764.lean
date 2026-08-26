import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 764 through 764. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk764

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_764 :
    geometryCheck (table.cell ⟨764, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_764 :
    crossingCheck (table.cell ⟨764, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_764 :
    scalarCheck (table.cell ⟨764, by decide⟩) = true := by
  kernel_decide

theorem certificate_764 :
    Certificate (table.cell ⟨764, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_764,
    crossing_of_check crossingCheck_764,
    scalar_of_check scalarCheck_764⟩

end Erdos1038.HighKPlatformConstantTableChunk764
