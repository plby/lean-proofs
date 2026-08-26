import ErdosProblems.Erdos73.AntipodalPortGraph

/-! Concatenating two endpoint lists without losing their order or indexing. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {N : ℕ} {W : Type*}

def pairedPorts (s t : Fin N → W) (i : Fin (2 * N)) : W :=
  if h : i.val < N then s ⟨i.val, h⟩ else t ⟨i.val - N, by have hh := i.isLt; omega⟩

theorem pairedPorts_first (s t : Fin N → W) (i : Fin N) :
    pairedPorts s t (firstPort i) = s i := by
  dsimp only [pairedPorts, firstPort]
  rw [dif_pos i.isLt]

theorem pairedPorts_second (s t : Fin N → W) (i : Fin N) :
    pairedPorts s t (secondPort i) = t i := by
  dsimp only [pairedPorts, secondPort]
  rw [dif_neg (by omega)]
  congr 1
  apply Fin.ext
  change N + i.val - N = i.val
  omega

theorem pairedPorts_cases (i : Fin (2 * N)) :
    (∃ j : Fin N, i = firstPort j) ∨ ∃ j : Fin N, i = secondPort j := by
  by_cases hi : i.val < N
  · exact Or.inl ⟨⟨i.val, hi⟩, rfl⟩
  · refine Or.inr ⟨⟨i.val - N, by have hh := i.isLt; omega⟩, Fin.ext ?_⟩
    dsimp only [secondPort]
    omega

theorem eq_pairedPorts (f : Fin (2 * N) → W) :
    f = pairedPorts (fun i => f (firstPort i)) (fun i => f (secondPort i)) := by
  funext i
  rcases pairedPorts_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [pairedPorts_first]
  · rw [pairedPorts_second]

theorem pairedPorts_map {V : Type*} (f : W → V) (s t : Fin N → W) :
    (fun i => f (pairedPorts s t i)) = pairedPorts (fun i => f (s i)) (fun i => f (t i)) := by
  funext i
  rcases pairedPorts_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [pairedPorts_first, pairedPorts_first]
  · rw [pairedPorts_second, pairedPorts_second]

theorem pairedPorts_strictMono [LinearOrder W] (s t : Fin N → W)
    (hs : StrictMono s) (ht : StrictMono t) (hst : ∀ i j, s i < t j) :
    StrictMono (pairedPorts s t) := by
  intro i j hij
  rcases pairedPorts_cases i with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    rcases pairedPorts_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [pairedPorts_first, pairedPorts_first]
    exact hs (show i < j from hij)
  · rw [pairedPorts_first, pairedPorts_second]
    exact hst i j
  · have hi := i.isLt
    change N + i.val < j.val at hij
    have hj := j.isLt
    omega
  · rw [pairedPorts_second, pairedPorts_second]
    apply ht
    change N + i.val < N + j.val at hij
    exact Fin.mk_lt_mk.mpr (by omega)

end
end Erdos73
