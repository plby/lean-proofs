import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 618 through 618. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk618

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_618 :
    geometryCheck (table.cell ⟨618, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_618 :
    crossingCheck (table.cell ⟨618, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_618 :
    scalarCheck (table.cell ⟨618, by decide⟩) = true := by
  kernel_decide

theorem certificate_618 :
    Certificate (table.cell ⟨618, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_618,
    crossing_of_check crossingCheck_618,
    scalar_of_check scalarCheck_618⟩

end Erdos1038.HighKPlatformConstantTableChunk618
