import ErdosProblems.Erdos633b.RationalAngleWeights

/-! Common angle weights transport under genuine vertex reindexing. -/

namespace Erdos633b.Triangle

theorem angle_weights_of_reindex (S : Triangle) (e : Equiv.Perm (Fin 3))
    (N : ℕ) (w : Fin 3 → ℕ)
    (hw : ∀ i, Triangle.angle (S.reindex e) i = (w i : ℝ) * (Real.pi / N))
    (hwp : ∀ i, 0 < w i ∧ w i < N) (hws : ∑ i, w i = N) :
    ∃ v : Fin 3 → ℕ,
      (∀ i, S.angle i = (v i : ℝ) * (Real.pi / N)) ∧
      (∀ i, 0 < v i ∧ v i < N) ∧ ∑ i, v i = N := by
  refine ⟨fun i => w (e i), ?_, fun i => hwp (e i), ?_⟩
  · intro i
    simpa only [Triangle.angle_reindex, Equiv.symm_apply_apply] using hw (e i)
  · exact (Fintype.sum_equiv e (fun i => w (e i)) w (fun _ => rfl)).trans hws

end Erdos633b.Triangle
