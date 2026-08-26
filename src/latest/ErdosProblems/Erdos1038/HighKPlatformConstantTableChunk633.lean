import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 633 through 633. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk633

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_633 :
    geometryCheck (table.cell ⟨633, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_633 :
    crossingCheck (table.cell ⟨633, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_633 :
    scalarCheck (table.cell ⟨633, by decide⟩) = true := by
  kernel_decide

theorem certificate_633 :
    Certificate (table.cell ⟨633, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_633,
    crossing_of_check crossingCheck_633,
    scalar_of_check scalarCheck_633⟩

end Erdos1038.HighKPlatformConstantTableChunk633
