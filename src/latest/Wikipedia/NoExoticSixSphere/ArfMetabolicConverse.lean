import Wikipedia.NoExoticSixSphere.ArfOrthogonalAverage
import Mathlib.GroupTheory.Coset.Card

/-!
# Arf invariant zero is equivalent to a totally singular self-orthogonal subspace

Choose a maximal subspace on which the quadratic form vanishes. The averaging
formula makes a positive Gauss sum imply that its orthogonal complement has
cardinality less than twice its own. The smaller cardinality divides the
larger one, so the two subspaces coincide.

This supplies the converse algebraic criterion without assuming symplectic
coordinates. It does not assert that the subspace can be realized by disjoint
embedded spheres, or that any framed manifold is nullbordant.
-/

namespace NoExoticSixSphere.Arf

variable {V : Type*} [AddCommGroup V] [Module F₂ V] [Fintype V]

theorem polarOrthogonal_eq_of_maximal_zero_of_gaussSum_pos (q : QuadraticForm F₂ V)
    (L : Submodule F₂ V) (hL : Maximal (fun K : Submodule F₂ V ↦ ∀ x : K, q x = 0) L)
    (hg : 0 < gaussSum q) : L.orthogonalBilin q.polarBilin = L := by
  classical
  let O := L.orthogonalBilin q.polarBilin
  let : Fintype L := Fintype.ofFinite L
  let : Fintype O := Fintype.ofFinite O
  have hle : L ≤ O := le_polarOrthogonal_of_zero q L hL.1
  have hformula : gaussSum q = 2 * (Fintype.card L : ℤ) - Fintype.card O :=
    gaussSum_eq_of_maximal_zero q L hL
  have hcard : Nat.card O < 2 * Nat.card L := by
    have hi : (Fintype.card O : ℤ) < 2 * (Fintype.card L : ℤ) := by
      linarith
    simpa only [Nat.card_eq_fintype_card] using (show Fintype.card O < 2 * Fintype.card L by
      exact_mod_cast hi)
  have hdvd : Nat.card L ∣ Nat.card O :=
    AddSubgroup.card_dvd_of_le (show L.toAddSubgroup ≤ O.toAddSubgroup from hle)
  obtain ⟨k, hk⟩ := hdvd
  have hklt : k < 2 := by
    rw [hk, Nat.mul_comm 2] at hcard
    exact (Nat.mul_lt_mul_left (show 0 < Nat.card L from Nat.card_pos)).mp hcard
  have hge : Nat.card O ≤ Nat.card L := by
    rw [hk]
    simpa using Nat.mul_le_mul_left (Nat.card L) (show k ≤ 1 by omega)
  have he : L.toAddSubgroup = O.toAddSubgroup :=
    AddSubgroup.eq_of_le_of_card_ge hle hge
  apply le_antisymm
  · intro v hv
    exact (show v ∈ L.toAddSubgroup from he.symm ▸ hv)
  · exact hle

theorem exists_selfOrthogonal_of_gaussSum_pos (q : QuadraticForm F₂ V)
    (hg : 0 < gaussSum q) :
    ∃ L : Submodule F₂ V, (∀ l : L, q l = 0) ∧
      ∀ v : V, (∀ l : L, q.polarBilin l v = 0) ↔ v ∈ L := by
  obtain ⟨L, hL⟩ := exists_maximal_zero_submodule q
  have he := polarOrthogonal_eq_of_maximal_zero_of_gaussSum_pos q L hL hg
  refine ⟨L, hL.1, ?_⟩
  intro v
  have hc : (∀ l : L, q.polarBilin l v = 0) ↔ v ∈ L.orthogonalBilin q.polarBilin :=
    ⟨fun h l hl ↦ h ⟨l, hl⟩, fun h l ↦ h l l.property⟩
  rwa [he] at hc

/-- The algebraic obstruction vanishes exactly when there is a totally singular
subspace equal to its polar orthogonal complement. Geometric realization is
not part of this equivalence. -/
theorem invariant_eq_zero_iff_exists_selfOrthogonal (q : QuadraticForm F₂ V)
    (hq : q.polarBilin.Nondegenerate) : invariant q hq = 0 ↔
      ∃ L : Submodule F₂ V, (∀ l : L, q l = 0) ∧
        ∀ v : V, (∀ l : L, q.polarBilin l v = 0) ↔ v ∈ L := by
  constructor
  · intro h
    exact exists_selfOrthogonal_of_gaussSum_pos q ((invariant_eq_zero_iff q hq).mp h)
  · rintro ⟨L, hzero, horth⟩
    exact invariant_eq_zero_of_selfOrthogonal q hq L hzero horth

end NoExoticSixSphere.Arf
