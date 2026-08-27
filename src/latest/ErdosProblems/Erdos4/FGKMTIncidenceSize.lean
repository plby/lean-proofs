import ErdosProblems.Erdos4.FGKMTIncidence
import ErdosProblems.Erdos4.FGKMTSupport

/-! Size and support of the aggregate incidence law. -/

namespace Erdos4.FGKMT

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

theorem erasedIncidence_support (μ : I → FiniteLaw (Finset V)) (v : V)
    (hd : 0 < vertexDegree μ v) (f : Finset V)
    (hf : 0 < (erasedIncidence μ v).weight f) :
    ∃ e i, v ∈ e ∧ 0 < (μ i).weight e ∧ f = e.erase v := by
  obtain ⟨e, he, hef⟩ := FiniteLaw.map_support (incidenceLaw μ v) (fun e => e.erase v) f hf
  obtain ⟨hv, i, hi⟩ := incidenceLaw_support μ v hd e he
  exact ⟨e, i, hv, hi, hef.symm⟩

theorem erasedIncidence_size (μ : I → FiniteLaw (Finset V)) (v : V)
    (hd : 0 < vertexDegree μ v) {r : ℕ}
    (hsize : ∀ i e, 0 < (μ i).weight e → e.card ≤ r) :
    ∀ f, 0 < (erasedIncidence μ v).weight f → f.card ≤ r := by
  intro f hf
  obtain ⟨e, i, _hv, hi, rfl⟩ := erasedIncidence_support μ v hd f hf
  exact Finset.card_erase_le.trans (hsize i e hi)

end Erdos4.FGKMT
