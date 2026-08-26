import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 740 through 740. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk740

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_740 :
    geometryCheck (table.cell ⟨740, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_740 :
    crossingCheck (table.cell ⟨740, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_740 :
    scalarCheck (table.cell ⟨740, by decide⟩) = true := by
  kernel_decide

theorem certificate_740 :
    Certificate (table.cell ⟨740, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_740,
    crossing_of_check crossingCheck_740,
    scalar_of_check scalarCheck_740⟩

end Erdos1038.HighKPlatformConstantTableChunk740
