import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 27 through 27. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk27

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_027 :
    geometryCheck (table.cell ⟨27, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_027 :
    crossingCheck (table.cell ⟨27, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_027 :
    scalarCheck (table.cell ⟨27, by decide⟩) = true := by
  kernel_decide

theorem certificate_027 :
    Certificate (table.cell ⟨27, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_027,
    crossing_of_check crossingCheck_027,
    scalar_of_check scalarCheck_027⟩

end Erdos1038.HighKPlatformConstantTableChunk27
