import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 794 through 794. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk794

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_794 :
    geometryCheck (table.cell ⟨794, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_794 :
    crossingCheck (table.cell ⟨794, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_794 :
    scalarCheck (table.cell ⟨794, by decide⟩) = true := by
  kernel_decide

theorem certificate_794 :
    Certificate (table.cell ⟨794, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_794,
    crossing_of_check crossingCheck_794,
    scalar_of_check scalarCheck_794⟩

end Erdos1038.HighKPlatformConstantTableChunk794
