import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 839 through 839. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk839

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_839 :
    geometryCheck (table.cell ⟨839, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_839 :
    crossingCheck (table.cell ⟨839, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_839 :
    scalarCheck (table.cell ⟨839, by decide⟩) = true := by
  kernel_decide

theorem certificate_839 :
    Certificate (table.cell ⟨839, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_839,
    crossing_of_check crossingCheck_839,
    scalar_of_check scalarCheck_839⟩

end Erdos1038.HighKPlatformConstantTableChunk839
