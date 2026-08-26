import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 831 through 831. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk831

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_831 :
    geometryCheck (table.cell ⟨831, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_831 :
    crossingCheck (table.cell ⟨831, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_831 :
    scalarCheck (table.cell ⟨831, by decide⟩) = true := by
  kernel_decide

theorem certificate_831 :
    Certificate (table.cell ⟨831, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_831,
    crossing_of_check crossingCheck_831,
    scalar_of_check scalarCheck_831⟩

end Erdos1038.HighKPlatformConstantTableChunk831
