import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 818 through 818. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk818

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_818 :
    geometryCheck (table.cell ⟨818, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_818 :
    crossingCheck (table.cell ⟨818, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_818 :
    scalarCheck (table.cell ⟨818, by decide⟩) = true := by
  kernel_decide

theorem certificate_818 :
    Certificate (table.cell ⟨818, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_818,
    crossing_of_check crossingCheck_818,
    scalar_of_check scalarCheck_818⟩

end Erdos1038.HighKPlatformConstantTableChunk818
