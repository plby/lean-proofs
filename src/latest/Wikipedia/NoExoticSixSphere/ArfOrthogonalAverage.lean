import Wikipedia.NoExoticSixSphere.ArfIsotropicSubspaces

/-!
# Averaging a quadratic character over a totally singular subspace

Translation by a subspace on which the quadratic form vanishes leaves only
the polar orthogonal complement in the Gauss sum. For a maximal such subspace,
every remaining vector outside it has quadratic value one. The resulting
formula is `G(q) = 2 |L| - |Lᗮ|`.
-/

open scoped BigOperators

namespace NoExoticSixSphere.Arf

variable {V : Type*} [AddCommGroup V] [Module F₂ V] [Fintype V]

theorem gaussSum_linear_eq_card_or_zero (l : V →ₗ[F₂] F₂) [Decidable (l = 0)] :
    gaussSum l = if l = 0 then (Fintype.card V : ℤ) else 0 := by
  classical
  by_cases hl : l = 0
  · simp [hl, gaussSum]
  · rw [if_neg hl]
    obtain ⟨a, ha⟩ : ∃ a : V, l a ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hl (LinearMap.ext hn)
    have ha' : l a = 1 := by
      generalize l a = c at *
      fin_cases c
      · exact (ha rfl).elim
      · rfl
    exact gaussSum_linear_eq_zero l a ha'

omit [Fintype V] in
theorem gaussSum_translate_zero_subspace (q : QuadraticForm F₂ V) (L : Submodule F₂ V)
    [Fintype L] [DecidablePred (fun v : V ↦ v ∈ L.orthogonalBilin q.polarBilin)]
    (hzero : ∀ l : L, q l = 0) (v : V) :
    (∑ l : L, sign (q (v + l))) =
      if v ∈ L.orthogonalBilin q.polarBilin then
        (Fintype.card L : ℤ) * sign (q v) else 0 := by
  classical
  let l : L →ₗ[F₂] F₂ := (q.polarBilin.flip v).comp L.subtype
  have he : ∀ a : L, sign (q (v + a)) = sign (q v) * sign (l a) := by
    intro a
    rw [QuadraticMap.map_add q, hzero a, add_zero, sign_add]
    rw [show QuadraticMap.polar q v a = q.polarBilin a v from
      QuadraticMap.polar_comm q v a]
    rfl
  have hl : l = 0 ↔ v ∈ L.orthogonalBilin q.polarBilin := by
    constructor
    · intro h a ha
      exact congrArg (fun f : L →ₗ[F₂] F₂ ↦ f ⟨a, ha⟩) h
    · intro h
      exact LinearMap.ext (fun a ↦ h a a.property)
  simp_rw [he]
  rw [← Finset.mul_sum]
  change sign (q v) * gaussSum l = _
  rw [gaussSum_linear_eq_card_or_zero]
  by_cases hv : v ∈ L.orthogonalBilin q.polarBilin
  · rw [if_pos (hl.mpr hv), if_pos hv, mul_comm]
  · rw [if_neg (fun h ↦ hv (hl.mp h)), if_neg hv, mul_zero]

theorem gaussSum_eq_orthogonal_sum (q : QuadraticForm F₂ V) (L : Submodule F₂ V)
    [DecidablePred (fun v : V ↦ v ∈ L.orthogonalBilin q.polarBilin)]
    (hzero : ∀ l : L, q l = 0) :
    gaussSum q = ∑ v : V, if v ∈ L.orthogonalBilin q.polarBilin then sign (q v) else 0 := by
  classical
  let : Fintype L := Fintype.ofFinite L
  have havg : (Fintype.card L : ℤ) * gaussSum q =
      ∑ v : V, ∑ l : L, sign (q (v + l)) := by
    rw [Finset.sum_comm]
    have hshift (l : L) : (∑ v : V, sign (q (v + l))) = gaussSum q :=
      Equiv.sum_comp (Equiv.addRight (l : V)) (fun v ↦ sign (q v))
    simp_rw [hshift]
    simp
  have hrhs : (∑ v : V, ∑ l : L, sign (q (v + l))) =
      (Fintype.card L : ℤ) *
        ∑ v : V, if v ∈ L.orthogonalBilin q.polarBilin then sign (q v) else 0 := by
    simp_rw [gaussSum_translate_zero_subspace q L hzero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp
  have hc : (0 : ℤ) < Fintype.card L := by exact_mod_cast Fintype.card_pos
  exact mul_left_cancel₀ (ne_of_gt hc) (havg.trans hrhs)

theorem gaussSum_eq_of_maximal_zero (q : QuadraticForm F₂ V) (L : Submodule F₂ V)
    [Fintype L] [Fintype (L.orthogonalBilin q.polarBilin)]
    (hL : Maximal (fun K : Submodule F₂ V ↦ ∀ x : K, q x = 0) L) :
    gaussSum q = 2 * (Fintype.card L : ℤ) - Fintype.card (L.orthogonalBilin q.polarBilin) := by
  classical
  rw [gaussSum_eq_orthogonal_sum q L hL.1]
  have he (v : V) :
      (if v ∈ L.orthogonalBilin q.polarBilin then sign (q v) else 0) =
        (if v ∈ L then (2 : ℤ) else 0) -
          (if v ∈ L.orthogonalBilin q.polarBilin then (1 : ℤ) else 0) := by
    by_cases hv : v ∈ L
    · have ho := le_polarOrthogonal_of_zero q L hL.1 hv
      simp [hv, ho, hL.1 ⟨v, hv⟩]
    · by_cases ho : v ∈ L.orthogonalBilin q.polarBilin
      · have hqv : q v ≠ 0 := fun h ↦ hv (mem_of_maximal_zero_of_orthogonal q L hL v ho h)
        simp [hv, ho, sign, hqv]
      · simp [hv, ho]
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Fintype.card_subtype (fun v : V ↦ v ∈ L),
    ← Fintype.card_subtype (fun v : V ↦ v ∈ L.orthogonalBilin q.polarBilin)]
  ring

end NoExoticSixSphere.Arf
