import ErdosProblems.Erdos157.Parabola

/-! The sharper tag-support count used by the binary-field construction. -/

namespace Erdos157.Binary

open Elementary.Parabola

section Permutations

variable {K : Type*} [Field K] [DecidableEq K]

def triplePermutations (t : K × K × K) : Finset (K × K × K) :=
  {(t.1, t.2.1, t.2.2), (t.1, t.2.2, t.2.1),
    (t.2.1, t.1, t.2.2), (t.2.1, t.2.2, t.1),
    (t.2.2, t.1, t.2.1), (t.2.2, t.2.1, t.1)}

theorem mem_triplePermutations_of_support_eq (h2 : (2 : K) ≠ 0)
    {u v : K} {t w : K × K × K} (ht : IsTriple u v t) (hw : IsTriple u v w)
    (hs : support w = support t) : w ∈ triplePermutations t := by
  rcases t with ⟨a, b, c⟩
  rcases w with ⟨x, y, z⟩
  have hx : x ∈ support (a, b, c) := by rw [← hs]; simp [support]
  simp only [support, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · have hsum : y + z = b + c := by have := ht.1; have := hw.1; dsimp at *; linear_combination hw.1 - ht.1
    have hsq : y ^ 2 + z ^ 2 = b ^ 2 + c ^ 2 := by
      have := ht.2; have := hw.2; dsimp at *; linear_combination hw.2 - ht.2
    rcases pair_eq_of_sum_and_sq_sum h2 y z b c hsum hsq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [triplePermutations]
  · have hsum : y + z = a + c := by linear_combination hw.1 - ht.1
    have hsq : y ^ 2 + z ^ 2 = a ^ 2 + c ^ 2 := by linear_combination hw.2 - ht.2
    rcases pair_eq_of_sum_and_sq_sum h2 y z a c hsum hsq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [triplePermutations]
  · have hsum : y + z = a + b := by linear_combination hw.1 - ht.1
    have hsq : y ^ 2 + z ^ 2 = a ^ 2 + b ^ 2 := by linear_combination hw.2 - ht.2
    rcases pair_eq_of_sum_and_sq_sum h2 y z a b hsum hsq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [triplePermutations]

theorem card_le_six_mul_card_support_image (h2 : (2 : K) ≠ 0)
    {u v : K} (s : Finset (K × K × K)) (hs : ∀ t ∈ s, IsTriple u v t) :
    s.card ≤ 6 * (s.image support).card := by
  rw [Finset.card_eq_sum_card_image support s]
  calc
    _ ≤ ∑ a ∈ s.image support, 6 := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
      have hsub : {w ∈ s | support w = support t} ⊆ triplePermutations t := by
        intro w hw
        exact mem_triplePermutations_of_support_eq h2 (hs t ht)
          (hs w (Finset.mem_filter.mp hw).1) (Finset.mem_filter.mp hw).2
      exact (Finset.card_le_card hsub).trans (by apply Finset.card_le_six)
    _ = _ := by simp [Nat.mul_comm]

end Permutations

section FiniteFields

variable {K : Type*} [Field K] [CharP K 7] [Fintype K] [DecidableEq K]

omit [Fintype K] in
theorem unitTriple_support_two (u v : K) (r : Kˣ) :
    2 ≤ (support (unitTriple u v r)).card := by
  by_contra hn
  let t := unitTriple u v r
  have hsmall : (support t).card ≤ 1 := by dsimp only [t]; omega
  have hxy : t.1 = t.2.1 := Finset.card_le_one.mp hsmall _ (by simp [support])
    _ (by simp [support])
  have hxz : t.1 = t.2.2 := Finset.card_le_one.mp hsmall _ (by simp [support])
    _ (by simp [support])
  have hsum : t.1 + t.2.1 + t.2.2 = u := (unitTriple_isTriple u v r).1
  rw [← hxy, ← hxz] at hsum
  have h7 : (7 : K) = 0 := CharP.cast_eq_zero K 7
  have hz : firstParameter u t = 0 := by
    unfold firstParameter
    rw [← hxy]
    linear_combination -hsum + t.1 * h7
  exact r.ne_zero ((firstParameter_unitTriple u v r).symm.trans hz)

theorem tagSupports_eq_allSupports (u v : K) : tagSupports u v = allSupports u v := by
  apply Finset.erase_eq_of_notMem
  intro hm
  obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hm
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp ht
  have hcard := unitTriple_support_two u v r
  rw [he, Finset.card_singleton] at hcard
  omega

theorem card_field_le_six_mul_tagSupports (u v : K) :
    Fintype.card K - 1 ≤ 6 * (tagSupports u v).card := by
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K 7 2).mp h
    norm_num at this
  have h := card_le_six_mul_card_support_image h2
    (Finset.univ.image (unitTriple u v)) (by
      intro t ht
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp ht
      exact unitTriple_isTriple u v r)
  rw [Finset.card_image_of_injective _ (unitTriple_injective u v),
    Finset.card_univ, Fintype.card_units] at h
  rw [tagSupports_eq_allSupports]
  exact h

/-- A field with at least `7*n` elements supplies `n` independent tag trials. -/
theorem exists_disjoint_triples (u v : K) (n : ℕ)
    (hn : 1 ≤ n) (hcard : 7 * n ≤ Fintype.card K) :
    ∃ T : Fin n → K × K × K,
      (∀ i, IsTriple u v (T i)) ∧
      (∀ i, 2 ≤ (support (T i)).card) ∧
      Pairwise (fun i j => Disjoint (support (T i)) (support (T j))) := by
  have hbound := card_field_le_six_mul_tagSupports u v
  have hncard : n ≤ (tagSupports u v).card := by omega
  have hle : Fintype.card (Fin n) ≤ Fintype.card ↥(tagSupports u v) := by
    simpa using hncard
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hle
  have hex : ∀ i : Fin n, ∃ t, IsTriple u v t ∧ support t = (e i).1 :=
    fun i => mem_allSupports (Finset.mem_of_mem_erase (e i).2)
  choose T hT hs using hex
  refine ⟨T, hT, ?_, ?_⟩
  · intro i
    rw [hs i]
    exact (tagSupports_card_bounds (e i).2).1
  · intro i j hij
    rw [hs i, hs j]
    apply tagSupports_pairwise_disjoint u v (e i).2 (e j).2
    intro heq
    exact hij (e.injective (Subtype.ext heq))

end FiniteFields

end Erdos157.Binary
