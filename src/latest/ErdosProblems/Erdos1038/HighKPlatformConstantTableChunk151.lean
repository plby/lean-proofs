import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 151 through 151. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk151

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_151 :
    geometryCheck (table.cell ⟨151, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_151 :
    crossingCheck (table.cell ⟨151, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_151 :
    scalarCheck (table.cell ⟨151, by decide⟩) = true := by
  kernel_decide

theorem certificate_151 :
    Certificate (table.cell ⟨151, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_151,
    crossing_of_check crossingCheck_151,
    scalar_of_check scalarCheck_151⟩

end Erdos1038.HighKPlatformConstantTableChunk151
