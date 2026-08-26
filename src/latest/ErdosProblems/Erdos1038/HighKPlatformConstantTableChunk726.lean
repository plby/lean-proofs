import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 726 through 726. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk726

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_726 :
    geometryCheck (table.cell ⟨726, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_726 :
    crossingCheck (table.cell ⟨726, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_726 :
    scalarCheck (table.cell ⟨726, by decide⟩) = true := by
  kernel_decide

theorem certificate_726 :
    Certificate (table.cell ⟨726, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_726,
    crossing_of_check crossingCheck_726,
    scalar_of_check scalarCheck_726⟩

end Erdos1038.HighKPlatformConstantTableChunk726
