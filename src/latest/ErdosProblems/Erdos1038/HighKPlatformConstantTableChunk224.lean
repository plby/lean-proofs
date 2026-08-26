import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 224 through 224. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk224

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_224 :
    geometryCheck (table.cell ⟨224, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_224 :
    crossingCheck (table.cell ⟨224, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_224 :
    scalarCheck (table.cell ⟨224, by decide⟩) = true := by
  kernel_decide

theorem certificate_224 :
    Certificate (table.cell ⟨224, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_224,
    crossing_of_check crossingCheck_224,
    scalar_of_check scalarCheck_224⟩

end Erdos1038.HighKPlatformConstantTableChunk224
