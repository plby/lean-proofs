import ErdosProblems.Erdos73.TwoGateNoncrossing
import ErdosProblems.Erdos73.CycleEnumeration
import ErdosProblems.Erdos73.CyclicAntipodalInvolution

/-! Antipodal port words obtained from tree-spliced rotation systems. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Equiv

theorem antipodal_pair_of_cycle_enumeration {D : Type*} {N : ℕ} (hN : 0 < N)
    (e : Fin (2 * N) ≃ D) (ρ α : Perm D)
    (he : ∀ i, e (finRotate (2 * N) i) = ρ (e i))
    (hα : Function.Involutive α) (hfree : ∀ d, α d ≠ d)
    (hcomm : Function.Commute α ρ) (i : Fin N) :
    α (e (firstPort i)) = e (secondPort i) := by
  let f : Fin (2 * N) → Fin (2 * N) := fun j => e.symm (α (e j))
  have hfinv : Function.Involutive f := by
    intro j
    dsimp only [f]
    rw [e.apply_symm_apply, hα (e j), e.symm_apply_apply]
  have hffree : ∀ j, f j ≠ j := by
    intro j hj
    apply hfree (e j)
    have hh := congrArg e hj
    simpa only [f, e.apply_symm_apply] using hh
  have hfcomm : Function.Commute f (finRotate (2 * N)) := by
    intro j
    apply e.injective
    simp only [f, e.apply_symm_apply, he]
    exact hcomm (e j)
  have hh := congrArg e (free_involution_firstPort hN f hfinv hffree hfcomm i)
  simpa only [f, e.apply_symm_apply] using hh

theorem le_antipodalPortGraph_of_pairing {D U : Type*} {N : ℕ}
    (e : Fin (2 * N) ≃ D) (label : D → U) (α : Perm D)
    (hα : Function.Involutive α)
    (hpair : ∀ i : Fin N, α (e (firstPort i)) = e (secondPort i))
    (G : SimpleGraph U)
    (hcover : ∀ u v, G.Adj u v → ∃ d, label d = u ∧ label (α d) = v) :
    G ≤ antipodalPortGraph (fun i => label (e i)) := by
  intro u v huv
  obtain ⟨d, hu, hv⟩ := hcover u v huv
  refine ⟨huv.ne, ?_⟩
  rcases pairedPorts_cases (e.symm d) with ⟨i, hi⟩ | ⟨i, hi⟩
  · have hd : d = e (firstPort i) := by
      simpa only [e.apply_symm_apply] using congrArg e hi
    refine ⟨i, Or.inl ⟨by simpa only [hd] using hu, ?_⟩⟩
    simpa only [hd, hpair i] using hv
  · have hd : d = e (secondPort i) := by
      simpa only [e.apply_symm_apply] using congrArg e hi
    have hp : α (e (secondPort i)) = e (firstPort i) := by
      rw [← hpair i, hα (e (firstPort i))]
    refine ⟨i, Or.inr ⟨?_, by simpa only [hd] using hu⟩⟩
    simpa only [hd, hp] using hv

namespace TreeSwitchSystem

variable {D U : Type*} [Fintype D] (C : TreeSwitchSystem D U)

theorem exists_noncrossing_antipodal_word {N : ℕ} (hN : 0 < N)
    (hcard : Fintype.card D = 2 * N) (hsurj : Function.Surjective C.label)
    (α : Perm D) (hα : Function.Involutive α) (hfree : ∀ d, α d ≠ d)
    (hcomm : Function.Commute α C.contour) (G : SimpleGraph U)
    (hcover : ∀ u v, G.Adj u v → ∃ d, C.label d = u ∧ C.label (α d) = v) :
    ∃ word : Fin (2 * N) → U, Function.Surjective word ∧ NoncrossingPortWord word ∧
      G ≤ antipodalPortGraph word := by
  have hpos : 0 < Fintype.card D := by omega
  obtain ⟨a⟩ := Fintype.card_pos_iff.mp hpos
  let e := cycleEnumeration C.contour C.contour_isCycleOn a (2 * N) hcard
  refine ⟨fun i => C.label (e i), hsurj.comp e.surjective, ?_, ?_⟩
  · exact C.contour_word_noncrossing e e.injective
      (cycleEnumeration_succ C.contour C.contour_isCycleOn a (2 * N) hcard)
  · apply le_antipodalPortGraph_of_pairing e C.label α hα ?_ G hcover
    exact antipodal_pair_of_cycle_enumeration hN e C.contour α
      (cycleEnumeration_rotate C.contour C.contour_isCycleOn a (2 * N) hcard)
      hα hfree hcomm

end TreeSwitchSystem
end
end Erdos73
