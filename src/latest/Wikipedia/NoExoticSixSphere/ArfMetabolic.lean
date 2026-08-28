import Wikipedia.NoExoticSixSphere.ArfInvariant

/-!
# Vanishing of the Arf invariant on metabolic quadratic spaces

If a subspace equals its polar orthogonal complement and the quadratic form
vanishes on it, averaging translations by that subspace makes the Gauss sum
equal to its positive cardinality. Hence the Arf invariant is zero.

This proves the algebraic criterion. Identifying such a subspace in the
homology of a manifold boundary is a separate geometric argument.
-/

open scoped BigOperators

namespace NoExoticSixSphere.Arf

variable {V : Type*} [AddCommGroup V] [Module F₂ V] [Fintype V]

omit [Fintype V] in
theorem gaussSum_translate_subspace (q : QuadraticForm F₂ V) (L : Submodule F₂ V)
    [Fintype L] [DecidablePred (fun v : V ↦ v ∈ L)] (hzero : ∀ l : L, q l = 0)
    (horth : ∀ v : V, (∀ l : L, q.polarBilin l v = 0) ↔ v ∈ L) (v : V) :
    (∑ l : L, sign (q (v + l))) = if v ∈ L then (Fintype.card L : ℤ) else 0 := by
  classical
  by_cases hv : v ∈ L
  · rw [if_pos hv]
    have hz : ∀ l : L, q (v + l) = 0 :=
      fun l ↦ hzero ⟨v + l, L.add_mem hv l.property⟩
    simp [hz]
  · rw [if_neg hv]
    obtain ⟨a, ha⟩ : ∃ a : L, q.polarBilin a v ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hv ((horth v).mp hn)
    have ha' : q.polarBilin a v = 1 := by
      have hc : ∀ c : F₂, c = 0 ∨ c = 1 := by
        intro c
        fin_cases c
        · exact Or.inl rfl
        · exact Or.inr rfl
      exact (hc _).resolve_left ha
    let l : L →ₗ[F₂] F₂ := (q.polarBilin.flip v).comp L.subtype
    have hl : gaussSum l = 0 := gaussSum_linear_eq_zero l a ha'
    have he : ∀ a : L, sign (q (v + a)) = sign (q v) * sign (l a) := by
      intro a
      rw [QuadraticMap.map_add q, hzero a, add_zero, sign_add]
      have hp : QuadraticMap.polar q v a = q.polarBilin a v :=
        QuadraticMap.polar_comm q v a
      rw [hp]
      rfl
    simp_rw [he]
    rw [← Finset.mul_sum]
    change sign (q v) * gaussSum l = 0
    rw [hl, mul_zero]

theorem gaussSum_eq_card_of_selfOrthogonal (q : QuadraticForm F₂ V)
    (L : Submodule F₂ V) [Fintype L] (hzero : ∀ l : L, q l = 0)
    (horth : ∀ v : V, (∀ l : L, q.polarBilin l v = 0) ↔ v ∈ L) :
    gaussSum q = Fintype.card L := by
  classical
  have havg : (Fintype.card L : ℤ) * gaussSum q =
      ∑ v : V, ∑ l : L, sign (q (v + l)) := by
    rw [Finset.sum_comm]
    have hshift (l : L) : (∑ v : V, sign (q (v + l))) = gaussSum q :=
      Equiv.sum_comp (Equiv.addRight (l : V)) (fun v ↦ sign (q v))
    simp_rw [hshift]
    simp
  have hsum : (∑ v : V, ∑ l : L, sign (q (v + l))) =
      (Fintype.card L : ℤ) * Fintype.card L := by
    simp_rw [gaussSum_translate_subspace q L hzero horth]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Fintype.card_subtype (fun v : V ↦ v ∈ L)]
  have hc : (0 : ℤ) < Fintype.card L := by exact_mod_cast Fintype.card_pos
  exact (mul_left_cancel₀ (ne_of_gt hc)) (havg.trans hsum)

theorem invariant_eq_zero_of_selfOrthogonal (q : QuadraticForm F₂ V)
    (hq : q.polarBilin.Nondegenerate) (L : Submodule F₂ V)
    (hzero : ∀ l : L, q l = 0)
    (horth : ∀ v : V, (∀ l : L, q.polarBilin l v = 0) ↔ v ∈ L) :
    invariant q hq = 0 := by
  classical
  let : Fintype L := Fintype.ofFinite L
  apply (invariant_eq_zero_iff q hq).mpr
  rw [gaussSum_eq_card_of_selfOrthogonal q L hzero horth]
  exact_mod_cast Fintype.card_pos

end NoExoticSixSphere.Arf
