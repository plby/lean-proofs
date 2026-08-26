import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 816 through 816. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk816

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_816 :
    geometryCheck (table.cell ⟨816, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_816 :
    crossingCheck (table.cell ⟨816, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_816 :
    scalarCheck (table.cell ⟨816, by decide⟩) = true := by
  kernel_decide

theorem certificate_816 :
    Certificate (table.cell ⟨816, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_816,
    crossing_of_check crossingCheck_816,
    scalar_of_check scalarCheck_816⟩

end Erdos1038.HighKPlatformConstantTableChunk816
