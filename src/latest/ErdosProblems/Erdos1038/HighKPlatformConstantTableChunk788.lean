import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 788 through 788. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk788

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_788 :
    geometryCheck (table.cell ⟨788, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_788 :
    crossingCheck (table.cell ⟨788, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_788 :
    scalarCheck (table.cell ⟨788, by decide⟩) = true := by
  kernel_decide

theorem certificate_788 :
    Certificate (table.cell ⟨788, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_788,
    crossing_of_check crossingCheck_788,
    scalar_of_check scalarCheck_788⟩

end Erdos1038.HighKPlatformConstantTableChunk788
