import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 664 through 664. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk664

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_664 :
    geometryCheck (table.cell ⟨664, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_664 :
    crossingCheck (table.cell ⟨664, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_664 :
    scalarCheck (table.cell ⟨664, by decide⟩) = true := by
  kernel_decide

theorem certificate_664 :
    Certificate (table.cell ⟨664, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_664,
    crossing_of_check crossingCheck_664,
    scalar_of_check scalarCheck_664⟩

end Erdos1038.HighKPlatformConstantTableChunk664
