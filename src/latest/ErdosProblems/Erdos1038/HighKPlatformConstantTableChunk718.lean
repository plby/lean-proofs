import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 718 through 718. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk718

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_718 :
    geometryCheck (table.cell ⟨718, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_718 :
    crossingCheck (table.cell ⟨718, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_718 :
    scalarCheck (table.cell ⟨718, by decide⟩) = true := by
  kernel_decide

theorem certificate_718 :
    Certificate (table.cell ⟨718, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_718,
    crossing_of_check crossingCheck_718,
    scalar_of_check scalarCheck_718⟩

end Erdos1038.HighKPlatformConstantTableChunk718
