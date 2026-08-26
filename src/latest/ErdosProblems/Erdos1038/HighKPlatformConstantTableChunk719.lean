import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 719 through 719. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk719

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_719 :
    geometryCheck (table.cell ⟨719, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_719 :
    crossingCheck (table.cell ⟨719, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_719 :
    scalarCheck (table.cell ⟨719, by decide⟩) = true := by
  kernel_decide

theorem certificate_719 :
    Certificate (table.cell ⟨719, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_719,
    crossing_of_check crossingCheck_719,
    scalar_of_check scalarCheck_719⟩

end Erdos1038.HighKPlatformConstantTableChunk719
