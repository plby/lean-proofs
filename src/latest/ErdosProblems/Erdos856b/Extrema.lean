import ErdosProblems.Erdos856b.Blocks

/-! # Attainment and multiplication of the finite-block extremal numbers -/

namespace Erdos856b

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem unionFree_empty {k : ℕ} (hk : 0 < k) : UnionFree k (∅ : Finset (Finset α)) := by
  intro a _ ha
  have := ha ⟨0, hk⟩
  simp at this

theorem M_attained {k : ℕ} (hk : 0 < k) (n r : ℕ) :
    ∃ F : Finset (Finset (Fin n)), Uniform r F ∧ UnionFree k F ∧ F.card = M k n r := by
  have hempty : (∅ : Finset (Finset (Fin n))) ∈ admissibleFamilies k n r := by
    apply mem_admissibleFamilies.mpr
    exact ⟨by simp [Uniform], unionFree_empty hk⟩
  obtain ⟨F, hF, hmax⟩ := Finset.exists_mem_eq_sup (admissibleFamilies k n r)
    ⟨∅, hempty⟩ Finset.card
  exact ⟨F, (mem_admissibleFamilies.mp hF).1, (mem_admissibleFamilies.mp hF).2, hmax.symm⟩

theorem UnionFree.map {k : ℕ} (hk : 3 ≤ k) {F : Finset (Finset α)}
    (hF : UnionFree k F) (e : α ↪ β) : UnionFree k (F.image (Finset.map e)) := by
  classical
  intro a hinj ha hbad
  obtain ⟨u, hu⟩ := hbad
  choose b hb heq using fun i => Finset.mem_image.mp (ha i)
  have hbinj : Function.Injective b := by
    intro i j hij
    apply hinj
    rw [← heq i, ← heq j, hij]
  apply hF b hbinj hb
  let i₀ : Fin k := ⟨0, by omega⟩
  let j₀ : Fin k := ⟨1, by omega⟩
  have hne : i₀ ≠ j₀ := by
    intro h
    have := congrArg Fin.val h
    simp [i₀, j₀] at this
  refine ⟨b i₀ ∪ b j₀, fun i j hij => ?_⟩
  apply Finset.map_injective e
  simp only [Finset.map_union, heq]
  exact (hu i j hij).trans (hu i₀ j₀ hne).symm

omit [DecidableEq α] in
theorem Uniform.map {r : ℕ} {F : Finset (Finset α)} (hF : Uniform r F)
    (e : α ↪ β) : Uniform r (F.image (Finset.map e)) := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  simpa using hF b hb

/-- The finite extremal numbers are supermultiplicative under disjoint blocks. -/
theorem M_mul_le {k : ℕ} (hk : 3 ≤ k) (n m r s : ℕ) :
    M k n r * M k m s ≤ M k (n + m) (r + s) := by
  obtain ⟨F, hUF, hF, hcardF⟩ := M_attained (by omega : 0 < k) n r
  obtain ⟨G, hUG, hG, hcardG⟩ := M_attained (by omega : 0 < k) m s
  let e : Fin n ⊕ Fin m ↪ Fin (n + m) := (finSumFinEquiv).toEmbedding
  have hbound := card_le_M ((hUF.blockProduct hUG).map e)
    ((hF.blockProduct hk hG hUF hUG).map hk e)
  simpa only [Finset.card_image_of_injective _ (Finset.map_injective e),
    card_blockProduct, hcardF, hcardG] using hbound

theorem unionFree_singleton {k : ℕ} (hk : 3 ≤ k) (s : Finset α) :
    UnionFree k {s} := by
  intro a hinj ha
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨1, by omega⟩
  have hij : a i = a j := (Finset.mem_singleton.mp (ha i)).trans
    (Finset.mem_singleton.mp (ha j)).symm
  have h := congrArg Fin.val (hinj hij)
  simp [i, j] at h

theorem M_pos {k n r : ℕ} (hk : 3 ≤ k) (hr : r ≤ n) : 0 < M k n r := by
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq
    (show r ≤ (Finset.univ : Finset (Fin n)).card by simpa using hr)
  have h := card_le_M (F := {s}) (by simpa [Uniform] using hcard)
    (unionFree_singleton hk s)
  exact lt_of_lt_of_le Nat.zero_lt_one (by simpa using h)

theorem M_rank_zero {k : ℕ} (hk : 3 ≤ k) (n : ℕ) : M k n 0 = 1 := by
  have hupper := M_le_choose k n 0
  have hlower := M_pos hk (Nat.zero_le n)
  simpa using Nat.le_antisymm hupper
    (by simpa using Nat.succ_le_of_lt hlower : n.choose 0 ≤ M k n 0)

end Erdos856b
