import Wikipedia.HopfProblem.OrbitPairFamilyDoublePoints
import Mathlib.Data.Set.Card

/-!
# Finite ordered triple points and local branch removal

A perturbation is fixed outside one source patch and has an injective
time-retaining track on that patch. If the changed branch avoids every
old double-point target at the corresponding time, no new triple point
can touch the patch. All remaining triple points are exactly the old ones
whose three source points lie outside it.
-/

noncomputable section

open Set Function

namespace Wikipedia.HopfProblem.OrbitPair.FamilyDoublePoints

variable {M N : Type*}

def triplePoints (F : ℝ × M → N) : Set (ℝ × (M × (M × M))) :=
  {q | q.2.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.2 ∧ q.2.2.1 ≠ q.2.2.2 ∧
    F (q.1, q.2.1) = F (q.1, q.2.2.1) ∧ F (q.1, q.2.1) = F (q.1, q.2.2.2)}

theorem mem_triplePoints_iff {F : ℝ × M → N} {q : ℝ × (M × (M × M))} :
    q ∈ triplePoints F ↔ q.2.2.1 ≠ q.2.2.2 ∧
      (q.1, (q.2.1, q.2.2.1)) ∈ doublePoints F ∧
      (q.1, (q.2.1, q.2.2.2)) ∈ doublePoints F := by
  constructor
  · intro h
    exact ⟨h.2.2.1, ⟨h.1, h.2.2.2.1⟩, ⟨h.2.1, h.2.2.2.2⟩⟩
  · rintro ⟨hyz, hxy, hxz⟩
    exact ⟨hxy.1, hxz.1, hyz, hxy.2, hxz.2⟩

theorem triplePoints_eq_of_doublePoints_eq {F G : ℝ × M → N}
    (h : doublePoints F = doublePoints G) : triplePoints F = triplePoints G := by
  ext q
  simp only [mem_triplePoints_iff, h]

theorem triplePoints_eq_of_one_pair_at_injective_slice {F G : ℝ × M → N}
    {t : ℝ} {x y : M} (hxy : x ≠ y) (hi : Injective (fun w => F (t, w)))
    (hD : doublePoints G = doublePoints F ∪ {(t, (x, y)), (t, (y, x))}) :
    triplePoints G = triplePoints F := by
  have hpair (u v : M) (h : (t, (u, v)) ∈ doublePoints G) :
      (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
    rw [hD] at h
    rcases h with h | h
    · exact False.elim (h.1 (hi h.2))
    · simpa only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq, true_and] using h
  have hnot (u v w : M) : (t, (u, (v, w))) ∉ triplePoints G := by
    intro h
    have huv := hpair u v ⟨h.1, h.2.2.2.1⟩
    have huw := hpair u w ⟨h.2.1, h.2.2.2.2⟩
    have hvw := h.2.2.1
    aesop
  ext q
  rcases q with ⟨s, u, v, w⟩
  by_cases ht : s = t
  · subst s
    have hnotF : (t, (u, (v, w))) ∉ triplePoints F :=
      fun h => h.1 (hi h.2.2.2.1)
    exact iff_of_false (hnot u v w) hnotF
  · simp only [mem_triplePoints_iff, hD, mem_union, mem_insert_iff, mem_singleton_iff,
      Prod.mk.injEq, ht, false_and, or_false]

theorem finite_triplePoints {F : ℝ × M → N} (hF : (doublePoints F).Finite) :
    (triplePoints F).Finite := by
  let combine : (ℝ × (M × M)) × (ℝ × (M × M)) → ℝ × (M × (M × M)) :=
    fun p => (p.1.1, (p.1.2.1, (p.1.2.2, p.2.2.2)))
  apply ((hF.prod hF).image combine).subset
  rintro ⟨t, x, y, z⟩ ⟨hxy, hxz, -, hFxy, hFxz⟩
  exact ⟨((t, (x, y)), (t, (x, z))), ⟨⟨hxy, hFxy⟩, ⟨hxz, hFxz⟩⟩, rfl⟩

theorem triple_rotate {F : ℝ × M → N} {t : ℝ} {x y z : M}
    (h : (t, (x, (y, z))) ∈ triplePoints F) : (t, (y, (z, x))) ∈ triplePoints F :=
  ⟨h.2.2.1, h.1.symm, h.2.1.symm, h.2.2.2.1.symm.trans h.2.2.2.2, h.2.2.2.1.symm⟩

theorem triple_first_outside_modified_patch {F G : ℝ × M → N} {S : Set (ℝ × M)}
    (hfixed : ∀ p ∉ S, G p = F p)
    (hinj : InjOn (fun p : ℝ × M => (p.1, G p)) S)
    (havoid : ∀ q ∈ S, ∀ p ∈ doublePoints F, p.1 = q.1 → G q ≠ F (p.1, p.2.1))
    {t : ℝ} {x y z : M} (h : (t, (x, (y, z))) ∈ triplePoints G) : (t, x) ∉ S := by
  intro hx
  have hy : (t, y) ∉ S := by
    intro hy
    have he := hinj hx hy (Prod.ext rfl h.2.2.2.1)
    exact h.1 (congrArg (fun p : ℝ × M => p.2) he)
  have hz : (t, z) ∉ S := by
    intro hz
    have he := hinj hx hz (Prod.ext rfl h.2.2.2.2)
    exact h.2.1 (congrArg (fun p : ℝ × M => p.2) he)
  have hold : (t, (y, z)) ∈ doublePoints F := by
    refine ⟨h.2.2.1, ?_⟩
    exact (hfixed (t, y) hy).symm.trans
      ((h.2.2.2.1.symm.trans h.2.2.2.2).trans (hfixed (t, z) hz))
  exact havoid (t, x) hx (t, (y, z)) hold rfl
    (h.2.2.2.1.trans (hfixed (t, y) hy))

theorem triplePoints_eq_outside_modified_patch {F G : ℝ × M → N} {S : Set (ℝ × M)}
    (hfixed : ∀ p ∉ S, G p = F p)
    (hinj : InjOn (fun p : ℝ × M => (p.1, G p)) S)
    (havoid : ∀ q ∈ S, ∀ p ∈ doublePoints F, p.1 = q.1 → G q ≠ F (p.1, p.2.1)) :
    triplePoints G = {q ∈ triplePoints F |
      (q.1, q.2.1) ∉ S ∧ (q.1, q.2.2.1) ∉ S ∧ (q.1, q.2.2.2) ∉ S} := by
  ext q
  rcases q with ⟨t, x, y, z⟩
  constructor
  · intro h
    have hx := triple_first_outside_modified_patch hfixed hinj havoid h
    have hy := triple_first_outside_modified_patch hfixed hinj havoid (triple_rotate h)
    have hz := triple_first_outside_modified_patch hfixed hinj havoid
      (triple_rotate (triple_rotate h))
    refine ⟨⟨h.1, h.2.1, h.2.2.1, ?_, ?_⟩, hx, hy, hz⟩
    · exact (hfixed (t, x) hx).symm.trans (h.2.2.2.1.trans (hfixed (t, y) hy))
    · exact (hfixed (t, x) hx).symm.trans (h.2.2.2.2.trans (hfixed (t, z) hz))
  · rintro ⟨h, hx, hy, hz⟩
    refine ⟨h.1, h.2.1, h.2.2.1, ?_, ?_⟩
    · exact (hfixed (t, x) hx).trans (h.2.2.2.1.trans (hfixed (t, y) hy).symm)
    · exact (hfixed (t, x) hx).trans (h.2.2.2.2.trans (hfixed (t, z) hz).symm)

theorem triple_ncard_decreases {F G : ℝ × M → N} {S : Set (ℝ × M)}
    (hfinite : (doublePoints F).Finite)
    (hfixed : ∀ p ∉ S, G p = F p)
    (hinj : InjOn (fun p : ℝ × M => (p.1, G p)) S)
    (havoid : ∀ q ∈ S, ∀ p ∈ doublePoints F, p.1 = q.1 → G q ≠ F (p.1, p.2.1))
    {t : ℝ} {x y z : M} (h : (t, (x, (y, z))) ∈ triplePoints F) (hx : (t, x) ∈ S) :
    (triplePoints G).ncard < (triplePoints F).ncard := by
  have heq := triplePoints_eq_outside_modified_patch hfixed hinj havoid
  have hsub : triplePoints G ⊆ triplePoints F := by rw [heq]; exact fun _ h => h.1
  have hnot : (t, (x, (y, z))) ∉ triplePoints G :=
    fun hg => triple_first_outside_modified_patch hfixed hinj havoid hg hx
  apply ncard_lt_ncard _ (finite_triplePoints hfinite)
  exact ⟨hsub, fun hrev => hnot (hrev h)⟩

end Wikipedia.HopfProblem.OrbitPair.FamilyDoublePoints
