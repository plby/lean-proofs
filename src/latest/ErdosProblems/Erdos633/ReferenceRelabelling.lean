import ErdosProblems.Erdos633.NormalizedSides

/-!
# Relabelling the reference triangle

Carrier-preserving reference changes rebuild the tiling's congruence witnesses.
Equality of the chosen labelled isometries is proved separately in
`TilingRelabelCounts`. Angle and side commensurability are invariant under
every vertex permutation.
-/

namespace Erdos633

noncomputable def CongruentTiling.of_reference_carrier_eq
    {P R S : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (h : S.carrier = R.carrier) : CongruentTiling P S N where
  toTriangleDissection := T.toTriangleDissection
  congruent := by
    intro i
    obtain ⟨e, he⟩ := T.congruent i
    exact ⟨e, by rw [h]; exact he⟩

theorem Triangle.commensurableAngles_relabel_iff (P : Triangle) (e : Equiv.Perm (Fin 3)) :
    (P.relabel e).CommensurableAngles ↔ P.CommensurableAngles := by
  constructor
  · intro h j
    have hj := h (e.symm j)
    rw [P.cornerAngle_relabel, e.apply_symm_apply] at hj
    exact hj
  · intro h j
    rw [P.cornerAngle_relabel]
    exact h (e j)

theorem Triangle.sideLength_relabel (P : Triangle) (e : Equiv.Perm (Fin 3)) (j : Fin 3) :
    (P.relabel e).sideLength j = P.sideLength (e j) := by
  rcases fin_three_perm_cases e with h | h | h | h | h | h
  all_goals
    obtain ⟨h₀, h₁, h₂⟩ := h
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl <;>
      simp [Triangle.sideLength, Triangle.edgeStart, Triangle.edgeEnd,
        Triangle.relabel, Triangle.vertex, h₀, h₁, h₂, dist_comm]

theorem Triangle.CommensurableSides.side_ratio {P : Triangle}
    (h : P.CommensurableSides) (j k : Fin 3) :
    P.sideLength j / P.sideLength k ∈ rationalReals := by
  have hr := rationalReals.div_mem (h j) (h k)
  have heq : P.normalizedSide j / P.normalizedSide k =
      P.sideLength j / P.sideLength k := by
    unfold Triangle.normalizedSide
    field_simp [ne_of_gt (P.sideLength_pos 2), ne_of_gt (P.sideLength_pos k)]
  rwa [heq] at hr

theorem Triangle.commensurableSides_relabel_iff (P : Triangle) (e : Equiv.Perm (Fin 3)) :
    (P.relabel e).CommensurableSides ↔ P.CommensurableSides := by
  constructor
  · intro h j
    have hr := h.side_ratio (e.symm j) (e.symm 2)
    rw [P.sideLength_relabel, P.sideLength_relabel, e.apply_symm_apply,
      e.apply_symm_apply] at hr
    exact hr
  · intro h j
    unfold Triangle.normalizedSide
    rw [P.sideLength_relabel, P.sideLength_relabel]
    exact h.side_ratio (e j) (e 2)

theorem Triangle.exists_relabel_of_permuted_angles (P : Triangle) (A B C : ℝ)
    (h : PermutedTriple P.cornerAngle ![A, B, C]) :
    ∃ Q : Triangle, Q.carrier = P.carrier ∧ Q.angleA = A ∧ Q.angleB = B ∧ Q.angleC = C := by
  obtain ⟨e, he⟩ := h
  exact ⟨P.relabel e, P.relabel_carrier e,
    (P.cornerAngle_relabel e 0).trans (he 0),
    (P.cornerAngle_relabel e 1).trans (he 1),
    (P.cornerAngle_relabel e 2).trans (he 2)⟩

end Erdos633
