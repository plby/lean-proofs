import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 807 through 807. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk807

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_807 :
    geometryCheck (table.cell ⟨807, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_807 :
    crossingCheck (table.cell ⟨807, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_807 :
    scalarCheck (table.cell ⟨807, by decide⟩) = true := by
  kernel_decide

theorem certificate_807 :
    Certificate (table.cell ⟨807, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_807,
    crossing_of_check crossingCheck_807,
    scalar_of_check scalarCheck_807⟩

end Erdos1038.HighKPlatformConstantTableChunk807
