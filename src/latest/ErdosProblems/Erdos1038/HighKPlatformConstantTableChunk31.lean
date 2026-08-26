import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 31 through 31. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk31

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_031 :
    geometryCheck (table.cell ⟨31, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_031 :
    crossingCheck (table.cell ⟨31, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_031 :
    scalarCheck (table.cell ⟨31, by decide⟩) = true := by
  kernel_decide

theorem certificate_031 :
    Certificate (table.cell ⟨31, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_031,
    crossing_of_check crossingCheck_031,
    scalar_of_check scalarCheck_031⟩

end Erdos1038.HighKPlatformConstantTableChunk31
