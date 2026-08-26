import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 417 through 417. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk417

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_417 :
    geometryCheck (table.cell ⟨417, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_417 :
    crossingCheck (table.cell ⟨417, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_417 :
    scalarCheck (table.cell ⟨417, by decide⟩) = true := by
  kernel_decide

theorem certificate_417 :
    Certificate (table.cell ⟨417, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_417,
    crossing_of_check crossingCheck_417,
    scalar_of_check scalarCheck_417⟩

end Erdos1038.HighKPlatformConstantTableChunk417
