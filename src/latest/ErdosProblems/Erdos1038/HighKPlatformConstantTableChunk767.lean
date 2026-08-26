import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 767 through 767. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk767

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_767 :
    geometryCheck (table.cell ⟨767, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_767 :
    crossingCheck (table.cell ⟨767, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_767 :
    scalarCheck (table.cell ⟨767, by decide⟩) = true := by
  kernel_decide

theorem certificate_767 :
    Certificate (table.cell ⟨767, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_767,
    crossing_of_check crossingCheck_767,
    scalar_of_check scalarCheck_767⟩

end Erdos1038.HighKPlatformConstantTableChunk767
