import ErdosProblems.Erdos577.FirstPawMasks0

/-! Exact cyclic row and diagonal certificates for source patterns (3)–(8). -/

namespace Erdos577.FirstPaw.D0

theorem residuals_sound {m : ℕ} (h : m ∈ residualMasks) :
    Classified 0 m := by
  simp only [residualMasks, List.not_mem_nil] at h

end Erdos577.FirstPaw.D0
