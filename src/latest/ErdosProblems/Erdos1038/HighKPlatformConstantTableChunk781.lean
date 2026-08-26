import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 781 through 781. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk781

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_781 :
    geometryCheck (table.cell ⟨781, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_781 :
    crossingCheck (table.cell ⟨781, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_781 :
    scalarCheck (table.cell ⟨781, by decide⟩) = true := by
  kernel_decide

theorem certificate_781 :
    Certificate (table.cell ⟨781, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_781,
    crossing_of_check crossingCheck_781,
    scalar_of_check scalarCheck_781⟩

end Erdos1038.HighKPlatformConstantTableChunk781
