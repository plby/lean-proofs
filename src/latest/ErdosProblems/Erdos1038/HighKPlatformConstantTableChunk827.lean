import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 827 through 827. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk827

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_827 :
    geometryCheck (table.cell ⟨827, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_827 :
    crossingCheck (table.cell ⟨827, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_827 :
    scalarCheck (table.cell ⟨827, by decide⟩) = true := by
  kernel_decide

theorem certificate_827 :
    Certificate (table.cell ⟨827, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_827,
    crossing_of_check crossingCheck_827,
    scalar_of_check scalarCheck_827⟩

end Erdos1038.HighKPlatformConstantTableChunk827
