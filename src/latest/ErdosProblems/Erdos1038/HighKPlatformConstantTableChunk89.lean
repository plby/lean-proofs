import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 89 through 89. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk89

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_089 :
    geometryCheck (table.cell ⟨89, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_089 :
    crossingCheck (table.cell ⟨89, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_089 :
    scalarCheck (table.cell ⟨89, by decide⟩) = true := by
  kernel_decide

theorem certificate_089 :
    Certificate (table.cell ⟨89, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_089,
    crossing_of_check crossingCheck_089,
    scalar_of_check scalarCheck_089⟩

end Erdos1038.HighKPlatformConstantTableChunk89
