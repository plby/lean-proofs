import ErdosProblems.Erdos73.NoncrossingPortBlocks
import ErdosProblems.Erdos73.OrientedEdgeMaps

/-! The simple graph encoded by antipodal pairs of a finite port word. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset

variable {N : ℕ} {U : Type*}

def firstPort (i : Fin N) : Fin (2 * N) := ⟨i.val, by omega⟩
def secondPort (i : Fin N) : Fin (2 * N) := ⟨N + i.val, by omega⟩

def antipodalPortGraph (label : Fin (2 * N) → U) : SimpleGraph U where
  Adj u v := u ≠ v ∧ ∃ i : Fin N,
    (label (firstPort i) = u ∧ label (secondPort i) = v) ∨
      (label (firstPort i) = v ∧ label (secondPort i) = u)
  symm := ⟨by
    rintro u v ⟨huv, i, hi⟩
    exact ⟨huv.symm, i, hi.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable [Fintype U] [LinearOrder U] (label : Fin (2 * N) → U)

def antipodalEdgeIndex (e : OrientedEdge (antipodalPortGraph label)) : Fin N :=
  e.adj.2.choose

theorem antipodalEdgeIndex_endpoints (e : OrientedEdge (antipodalPortGraph label)) :
    (label (firstPort (antipodalEdgeIndex label e)) = e.lo ∧
      label (secondPort (antipodalEdgeIndex label e)) = e.hi) ∨
    (label (firstPort (antipodalEdgeIndex label e)) = e.hi ∧
      label (secondPort (antipodalEdgeIndex label e)) = e.lo) := e.adj.2.choose_spec

theorem antipodalEdgeIndex_sym2 (e : OrientedEdge (antipodalPortGraph label)) :
    s(label (firstPort (antipodalEdgeIndex label e)),
      label (secondPort (antipodalEdgeIndex label e))) = s(e.lo, e.hi) :=
  Sym2.eq_iff.mpr (antipodalEdgeIndex_endpoints label e)

theorem antipodalEdgeIndex_injective : Function.Injective (antipodalEdgeIndex label) := by
  intro e f he
  apply OrientedEdge.eq_of_sym2_eq
  exact (antipodalEdgeIndex_sym2 label e).symm.trans (he ▸ antipodalEdgeIndex_sym2 label f)

def antipodalEdgeSource (e : OrientedEdge (antipodalPortGraph label)) : Fin (2 * N) :=
  if label (firstPort (antipodalEdgeIndex label e)) = e.lo then
    firstPort (antipodalEdgeIndex label e) else secondPort (antipodalEdgeIndex label e)

def antipodalEdgeTarget (e : OrientedEdge (antipodalPortGraph label)) : Fin (2 * N) :=
  if label (firstPort (antipodalEdgeIndex label e)) = e.lo then
    secondPort (antipodalEdgeIndex label e) else firstPort (antipodalEdgeIndex label e)

theorem antipodalEdgeSource_label (e : OrientedEdge (antipodalPortGraph label)) :
    label (antipodalEdgeSource label e) = e.lo := by
  rcases antipodalEdgeIndex_endpoints label e with he | he
  · rw [antipodalEdgeSource, if_pos he.1]
    exact he.1
  · have hn : label (firstPort (antipodalEdgeIndex label e)) ≠ e.lo :=
      fun hh => e.adj.ne (hh.symm.trans he.1)
    rw [antipodalEdgeSource, if_neg hn]
    exact he.2

theorem antipodalEdgeTarget_label (e : OrientedEdge (antipodalPortGraph label)) :
    label (antipodalEdgeTarget label e) = e.hi := by
  rcases antipodalEdgeIndex_endpoints label e with he | he
  · rw [antipodalEdgeTarget, if_pos he.1]
    exact he.2
  · have hn : label (firstPort (antipodalEdgeIndex label e)) ≠ e.lo :=
      fun hh => e.adj.ne (hh.symm.trans he.1)
    rw [antipodalEdgeTarget, if_neg hn]
    exact he.1

end
end Erdos73
