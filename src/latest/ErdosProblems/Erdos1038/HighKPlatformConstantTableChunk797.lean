import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 797 through 797. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk797

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_797 :
    geometryCheck (table.cell ⟨797, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_797 :
    crossingCheck (table.cell ⟨797, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_797 :
    scalarCheck (table.cell ⟨797, by decide⟩) = true := by
  kernel_decide

theorem certificate_797 :
    Certificate (table.cell ⟨797, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_797,
    crossing_of_check crossingCheck_797,
    scalar_of_check scalarCheck_797⟩

end Erdos1038.HighKPlatformConstantTableChunk797
