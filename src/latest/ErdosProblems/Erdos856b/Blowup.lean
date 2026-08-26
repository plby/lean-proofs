import ErdosProblems.Erdos856b.Basic

/-!
# Cosunflower-free blow-ups

Lemma 3.3 of the source is expressed using a projection to the block index. A member of
the blow-up is a partial transversal: the projection is injective on that member.
-/

namespace Erdos856b

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Projecting a common-union configuration of partial transversals preserves distinctness. -/
theorem common_union_image_injective {k : ℕ} (hk : 3 ≤ k) {a : Fin k → Finset α}
    (ha : Function.Injective a) (π : α → β) (hπ : ∀ i, Set.InjOn π (a i))
    {u : Finset α} (hu : ∀ i j, i ≠ j → a i ∪ a j = u) :
    Function.Injective (fun i => (a i).image π) := by
  have hsub (i j : Fin k) (hij : i ≠ j)
      (himage : (a i).image π = (a j).image π) : a i ⊆ a j := by
    intro x hx
    by_contra hxj
    have hximage : π x ∈ (a j).image π := by
      rw [← himage]
      exact Finset.mem_image_of_mem _ hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hximage
    have hyi : y ∉ a i := by
      intro hyi
      have h := hπ i hyi hx hxy
      exact hxj (h ▸ hy)
    obtain ⟨l, hli, hlj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
    have hxU : x ∈ u := by rw [← hu i j hij]; exact Finset.mem_union_left _ hx
    have hyU : y ∈ u := by rw [← hu i j hij]; exact Finset.mem_union_right _ hy
    have hxl : x ∈ a l := by
      rw [← hu j l hlj.symm, Finset.mem_union] at hxU
      exact hxU.resolve_left hxj
    have hyl : y ∈ a l := by
      rw [← hu i l hli.symm, Finset.mem_union] at hyU
      exact hyU.resolve_left hyi
    have h := hπ l hyl hxl hxy
    exact hxj (h ▸ hy)
  intro i j hij
  by_contra hne
  exact hne (ha (Finset.Subset.antisymm (hsub i j hne hij) (hsub j i (Ne.symm hne) hij.symm)))

/-- A finite family of partial transversals whose block-index sets belong to `F`. -/
def blowup (π : α → β) (U : Finset α) (F : Finset (Finset β)) : Finset (Finset α) :=
  U.powerset.filter (fun s => Set.InjOn π s ∧ s.image π ∈ F)

omit [DecidableEq α] in
theorem mem_blowup {π : α → β} {U : Finset α} {F : Finset (Finset β)} {s : Finset α} :
    s ∈ blowup π U F ↔ s ⊆ U ∧ Set.InjOn π s ∧ s.image π ∈ F := by
  classical
  simp [blowup]

theorem UnionFree.blowup {k : ℕ} (hk : 3 ≤ k) {F : Finset (Finset β)}
    (hF : UnionFree k F) (π : α → β) (U : Finset α) : UnionFree k (blowup π U F) := by
  intro a ha hmem hbad
  obtain ⟨u, hu⟩ := hbad
  have hπ := fun i => (mem_blowup.mp (hmem i)).2.1
  have himage := fun i => (mem_blowup.mp (hmem i)).2.2
  apply hF (fun i => (a i).image π) (common_union_image_injective hk ha π hπ hu) himage
  refine ⟨u.image π, fun i j hij => ?_⟩
  rw [← Finset.image_union, hu i j hij]

omit [DecidableEq α] in
theorem Uniform.blowup {r : ℕ} {F : Finset (Finset β)} (hF : Uniform r F)
    (π : α → β) (U : Finset α) : Uniform r (blowup π U F) := by
  intro s hs
  obtain ⟨_, hinj, himage⟩ := mem_blowup.mp hs
  rw [← Finset.card_image_of_injOn hinj]
  exact hF _ himage

end Erdos856b
