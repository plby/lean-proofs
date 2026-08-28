import Mathlib.Topology.Homotopy.HomotopyGroup

/-! # Reindexing the coordinates of native homotopy groups -/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres

variable {M N X : Type*} [TopologicalSpace X] (x : X)

/-- Relabeling cube coordinates preserves homotopies relative to the boundary. -/
def reindexHomotopy (e : M ≃ N) {p q : GenLoop M X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary M)) :
    (GenLoop.congr x e p).val.HomotopyRel (GenLoop.congr x e q).val (Cube.boundary N) where
  toFun tu := H (tu.1, tu.2 ∘ e)
  continuous_toFun := by fun_prop
  map_zero_left _ := H.map_zero_left _
  map_one_left _ := H.map_one_left _
  prop' s t ht := by
    obtain ⟨i, hi⟩ := ht
    apply H.eq_fst s
    exact ⟨e.symm i, by simpa only [Function.comp_apply, e.apply_symm_apply] using hi⟩

theorem reindex_homotopic (e : M ≃ N) {p q : GenLoop M X x} (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (GenLoop.congr x e p) (GenLoop.congr x e q) := by
  obtain ⟨H⟩ := h
  exact ⟨reindexHomotopy x e H⟩

/-- The usual cubical homotopy quotient is invariant under a coordinate equivalence. -/
def reindexEquiv (e : M ≃ N) : HomotopyGroup M X x ≃ HomotopyGroup N X x where
  toFun := Quotient.map (GenLoop.congr x e) (fun _ _ h => reindex_homotopic x e h)
  invFun := Quotient.map (GenLoop.congr x e.symm) (fun _ _ h => reindex_homotopic x e.symm h)
  left_inv a := by
    induction a using Quotient.inductionOn with
    | h p =>
      change (⟦GenLoop.congr x e.symm (GenLoop.congr x e p)⟧ : HomotopyGroup M X x) = ⟦p⟧
      have h : GenLoop.congr x e.symm (GenLoop.congr x e p) = p := by
        apply GenLoop.ext
        intro t
        change p (fun m => t (e.symm (e m))) = p t
        simp only [e.symm_apply_apply]
      rw [h]
  right_inv a := by
    induction a using Quotient.inductionOn with
    | h p =>
      change (⟦GenLoop.congr x e (GenLoop.congr x e.symm p)⟧ : HomotopyGroup N X x) = ⟦p⟧
      have h : GenLoop.congr x e (GenLoop.congr x e.symm p) = p := by
        apply GenLoop.ext
        intro t
        change p (fun n => t (e (e.symm n))) = p t
        simp only [e.apply_symm_apply]
      rw [h]

@[simp] theorem reindexEquiv_mk (e : M ≃ N) (p : GenLoop M X x) :
    reindexEquiv x e (⟦p⟧ : HomotopyGroup M X x) = ⟦GenLoop.congr x e p⟧ := rfl

variable [DecidableEq M] [DecidableEq N]

private theorem update_comp_equiv (e : M ≃ N) (t : N → I) (i : M) (s : I) :
    Function.update t (e i) s ∘ e = Function.update (t ∘ e) i s := by
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [Function.update_of_ne h, Function.update_of_ne (e.injective.ne h)]

/-- Reindexing carries concatenation to concatenation along the corresponding coordinate. -/
theorem reindex_transAt (e : M ≃ N) (i : M) (p q : GenLoop M X x) :
    GenLoop.congr x e (GenLoop.transAt i p q) =
      GenLoop.transAt (e i) (GenLoop.congr x e p) (GenLoop.congr x e q) := by
  apply GenLoop.ext
  intro t
  change (if (t (e i) : ℝ) ≤ 1 / 2 then
      p (Function.update (t ∘ e) i (Set.projIcc 0 1 zero_le_one (2 * t (e i))))
    else q (Function.update (t ∘ e) i (Set.projIcc 0 1 zero_le_one (2 * t (e i) - 1)))) =
    if (t (e i) : ℝ) ≤ 1 / 2 then
      p (Function.update t (e i) (Set.projIcc 0 1 zero_le_one (2 * t (e i))) ∘ e)
    else q (Function.update t (e i) (Set.projIcc 0 1 zero_le_one (2 * t (e i) - 1)) ∘ e)
  simp only [update_comp_equiv]

variable [Nonempty M] [Nonempty N]

/-- The coordinate equivalence preserves the original homotopy-group multiplication. -/
def reindexMulEquiv (e : M ≃ N) : HomotopyGroup M X x ≃* HomotopyGroup N X x where
  toEquiv := reindexEquiv x e
  map_mul' a b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    let i : M := Classical.arbitrary M
    exact (congrArg (reindexEquiv x e)
      (HomotopyGroup.mul_spec (i := i) (p := p) (q := q))).trans
      ((congrArg (fun s : GenLoop N X x => (⟦s⟧ : HomotopyGroup N X x))
        (reindex_transAt x e i q p)).trans
        (HomotopyGroup.mul_spec (i := e i)
          (p := GenLoop.congr x e p) (q := GenLoop.congr x e q)).symm)

end Wikipedia.HomotopyGroupsOfSpheres
