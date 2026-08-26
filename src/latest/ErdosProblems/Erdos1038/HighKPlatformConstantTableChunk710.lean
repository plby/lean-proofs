import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 710 through 710. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk710

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_710 :
    geometryCheck (table.cell ⟨710, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_710 :
    crossingCheck (table.cell ⟨710, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_710 :
    scalarCheck (table.cell ⟨710, by decide⟩) = true := by
  kernel_decide

theorem certificate_710 :
    Certificate (table.cell ⟨710, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_710,
    crossing_of_check crossingCheck_710,
    scalar_of_check scalarCheck_710⟩

end Erdos1038.HighKPlatformConstantTableChunk710
