import ErdosProblems.Erdos856b.Basic

/-!
# Products of uniform union-free families

Uniformity is essential: an indexed family with a common pairwise union can have repeated
members. For equal-sized members, a repetition forces all the members to be equal. This is
the input that allows union-free uniform families to be multiplied on disjoint ground sets.
-/

namespace Erdos856b

variable {α β ι : Type*} [DecidableEq α] [DecidableEq β]

/-- A repeated member of an equal-sized common-union configuration makes it constant. -/
theorem common_union_constant_of_not_injective {r : ℕ} {a : ι → Finset α}
    (hcard : ∀ i, (a i).card = r) {u : Finset α}
    (hunion : ∀ i j, i ≠ j → a i ∪ a j = u)
    (hnot : ¬ Function.Injective a) : ∀ i j, a i = a j := by
  classical
  simp only [Function.Injective, not_forall] at hnot
  obtain ⟨i₀, j₀, heq, hne⟩ := hnot
  have hu : u = a i₀ := by
    simpa only [← heq, Finset.union_self] using (hunion i₀ j₀ hne).symm
  have hbase (i : ι) : a i = a i₀ := by
    apply Finset.eq_of_subset_of_card_le
    · by_cases hi : i = i₀
      · subst i
        exact Finset.Subset.refl _
      · rw [← hu, ← hunion i i₀ hi]
        exact Finset.subset_union_left
    · rw [hcard, hcard]
  intro i j
  exact (hbase i).trans (hbase j).symm

/-- In a uniform union-free family every common-union configuration is constant. -/
theorem UnionFree.common_union_constant {k r : ℕ} {F : Finset (Finset α)}
    (hF : UnionFree k F) (hU : Uniform r F) {a : Fin k → Finset α}
    (ha : ∀ i, a i ∈ F) {u : Finset α}
    (hunion : ∀ i j, i ≠ j → a i ∪ a j = u) : ∀ i j, a i = a j := by
  apply common_union_constant_of_not_injective (fun i => hU _ (ha i)) hunion
  intro hinj
  exact hF a hinj ha ⟨u, hunion⟩

/-- Independent choices of one set in each of two disjoint blocks. -/
def blockProduct (F : Finset (Finset α)) (G : Finset (Finset β)) :
    Finset (Finset (α ⊕ β)) :=
  (F ×ˢ G).image (fun p => p.1.disjSum p.2)

theorem mem_blockProduct {F : Finset (Finset α)} {G : Finset (Finset β)}
    {s : Finset (α ⊕ β)} :
    s ∈ blockProduct F G ↔ s.toLeft ∈ F ∧ s.toRight ∈ G := by
  constructor
  · intro hs
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hs
    simpa using hab
  · rintro ⟨ha, hb⟩
    exact Finset.mem_image.mpr ⟨(s.toLeft, s.toRight), Finset.mem_product.mpr ⟨ha, hb⟩,
      Finset.toLeft_disjSum_toRight⟩

theorem card_blockProduct (F : Finset (Finset α)) (G : Finset (Finset β)) :
    (blockProduct F G).card = F.card * G.card := by
  rw [blockProduct, Finset.card_image_of_injective, Finset.card_product]
  intro p q hpq
  exact Prod.ext (Finset.disjSum_inj.mp hpq).1 (Finset.disjSum_inj.mp hpq).2

theorem Uniform.blockProduct {r s : ℕ} {F : Finset (Finset α)}
    {G : Finset (Finset β)} (hF : Uniform r F) (hG : Uniform s G) :
    Uniform (r + s) (blockProduct F G) := by
  intro a ha
  obtain ⟨hl, hr⟩ := mem_blockProduct.mp ha
  rw [← Finset.card_toLeft_add_card_toRight, hF _ hl, hG _ hr]

/-- The disjoint-block construction preserves the original `k`-distinct-sets exclusion. -/
theorem UnionFree.blockProduct {k r s : ℕ} (hk : 3 ≤ k)
    {F : Finset (Finset α)} {G : Finset (Finset β)}
    (hF : UnionFree k F) (hG : UnionFree k G) (hUF : Uniform r F) (hUG : Uniform s G) :
    UnionFree k (blockProduct F G) := by
  intro a hinj ha hbad
  obtain ⟨u, hu⟩ := hbad
  have hl : ∀ i, (a i).toLeft ∈ F := fun i => (mem_blockProduct.mp (ha i)).1
  have hr : ∀ i, (a i).toRight ∈ G := fun i => (mem_blockProduct.mp (ha i)).2
  have hcl := hF.common_union_constant hUF hl (u := u.toLeft) (by
    intro i j hij
    simpa only [Finset.toLeft_union] using congrArg Finset.toLeft (hu i j hij))
  have hcr := hG.common_union_constant hUG hr (u := u.toRight) (by
    intro i j hij
    simpa only [Finset.toRight_union] using congrArg Finset.toRight (hu i j hij))
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨1, by omega⟩
  have heq : a i = a j := by
    rw [← Finset.toLeft_disjSum_toRight (u := a i),
      ← Finset.toLeft_disjSum_toRight (u := a j), hcl i j, hcr i j]
  have := congrArg Fin.val (hinj heq)
  simp [i, j] at this

end Erdos856b
