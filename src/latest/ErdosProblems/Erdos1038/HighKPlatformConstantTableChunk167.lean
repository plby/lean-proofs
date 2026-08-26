import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 167 through 167. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk167

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_167 :
    geometryCheck (table.cell ⟨167, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_167 :
    crossingCheck (table.cell ⟨167, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_167 :
    scalarCheck (table.cell ⟨167, by decide⟩) = true := by
  kernel_decide

theorem certificate_167 :
    Certificate (table.cell ⟨167, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_167,
    crossing_of_check crossingCheck_167,
    scalar_of_check scalarCheck_167⟩

end Erdos1038.HighKPlatformConstantTableChunk167
