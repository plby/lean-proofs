import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 640 through 640. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk640

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_640 :
    geometryCheck (table.cell ⟨640, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_640 :
    crossingCheck (table.cell ⟨640, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_640 :
    scalarCheck (table.cell ⟨640, by decide⟩) = true := by
  kernel_decide

theorem certificate_640 :
    Certificate (table.cell ⟨640, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_640,
    crossing_of_check crossingCheck_640,
    scalar_of_check scalarCheck_640⟩

end Erdos1038.HighKPlatformConstantTableChunk640
