import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 802 through 802. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk802

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_802 :
    geometryCheck (table.cell ⟨802, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_802 :
    crossingCheck (table.cell ⟨802, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_802 :
    scalarCheck (table.cell ⟨802, by decide⟩) = true := by
  kernel_decide

theorem certificate_802 :
    Certificate (table.cell ⟨802, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_802,
    crossing_of_check crossingCheck_802,
    scalar_of_check scalarCheck_802⟩

end Erdos1038.HighKPlatformConstantTableChunk802
