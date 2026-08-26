import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 823 through 823. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk823

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_823 :
    geometryCheck (table.cell ⟨823, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_823 :
    crossingCheck (table.cell ⟨823, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_823 :
    scalarCheck (table.cell ⟨823, by decide⟩) = true := by
  kernel_decide

theorem certificate_823 :
    Certificate (table.cell ⟨823, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_823,
    crossing_of_check crossingCheck_823,
    scalar_of_check scalarCheck_823⟩

end Erdos1038.HighKPlatformConstantTableChunk823
