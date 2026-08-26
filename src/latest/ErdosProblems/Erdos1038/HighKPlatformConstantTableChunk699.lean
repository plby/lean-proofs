import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 699 through 699. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk699

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_699 :
    geometryCheck (table.cell ⟨699, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_699 :
    crossingCheck (table.cell ⟨699, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_699 :
    scalarCheck (table.cell ⟨699, by decide⟩) = true := by
  kernel_decide

theorem certificate_699 :
    Certificate (table.cell ⟨699, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_699,
    crossing_of_check crossingCheck_699,
    scalar_of_check scalarCheck_699⟩

end Erdos1038.HighKPlatformConstantTableChunk699
