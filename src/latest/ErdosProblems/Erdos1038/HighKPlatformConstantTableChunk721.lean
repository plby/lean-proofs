import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 721 through 721. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk721

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_721 :
    geometryCheck (table.cell ⟨721, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_721 :
    crossingCheck (table.cell ⟨721, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_721 :
    scalarCheck (table.cell ⟨721, by decide⟩) = true := by
  kernel_decide

theorem certificate_721 :
    Certificate (table.cell ⟨721, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_721,
    crossing_of_check crossingCheck_721,
    scalar_of_check scalarCheck_721⟩

end Erdos1038.HighKPlatformConstantTableChunk721
