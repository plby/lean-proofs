import ErdosProblems.Erdos587.SubgroupStability

/-! The subgroup-stability step from density of iterated images in bounding boxes. -/

open scoped Pointwise

namespace Erdos587.CFP

def iteratedImageSums {α G : Type*} [AddCommGroup G] [DecidableEq G]
    (φ : α → G) (A : Finset α) (h : ℕ) : Finset G := h • insert 0 (A.image φ)

theorem iteratedImageSums_mono {α G : Type*} [AddCommGroup G] [DecidableEq G]
    (φ : α → G) (h : ℕ) {A B : Finset α} (hAB : A ⊆ B) :
    iteratedImageSums φ A h ⊆ iteratedImageSums φ B h :=
  Finset.nsmul_subset_nsmul_left (Finset.insert_subset_insert 0 (Finset.image_mono φ hAB))

theorem iteratedImageSums_mem_generatedSubgroup {α G : Type*} [AddCommGroup G] [DecidableEq G]
    (φ : α → G) (A : Finset α) :
    ∀ h : ℕ, ∀ x ∈ iteratedImageSums φ A h, x ∈ generatedSubgroup φ A := by
  intro h
  induction h with
  | zero =>
      intro x hx
      have hx0 : x = 0 := by simpa [iteratedImageSums] using hx
      subst x
      exact (generatedSubgroup φ A).zero_mem
  | succ h ih =>
      intro x hx
      simp only [iteratedImageSums, succ_nsmul] at hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Finset.mem_add.mp hx
      apply (generatedSubgroup φ A).add_mem (ih y hy)
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact (generatedSubgroup φ A).zero_mem
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
        exact AddSubgroup.subset_closure ⟨a, ha, rfl⟩

/-- The corrected stability step. Its density hypotheses are the geometric
input to be supplied by the weak-stability and bounding-GAP theorems. -/
theorem exists_stable_subgroups_of_dense_iterated_images {α ι : Type*} [Fintype ι]
    (d : ι → ℕ) (φ : ∀ i, α → Fin (d i) → ℤ) (A : Finset α)
    (h : ι → ℕ) (lo : ∀ i, Fin (d i) → ℤ) (w : ∀ i, Fin (d i) → ℕ)
    (r M d₀ : ℕ) (hM : 1 ≤ M) (hdim : ∀ i, d i ≤ d₀)
    (hwidth : ∀ i j, M ≤ w i j)
    (hbox : ∀ i, iteratedImageSums (φ i) A (h i) ⊆ integerBox (lo i) (w i))
    (hdense : ∀ D ⊆ A, A.card ≤ D.card + (Fintype.card ι * M ^ d₀ + 1) * r →
      ∀ i, 2 * (integerBox (lo i) (w i)).card < (iteratedImageSums (φ i) D (h i)).card * M) :
    ∃ B ⊆ A, A.card ≤ B.card + (Fintype.card ι * M ^ d₀) * r ∧
      HasStableGeneratedSubgroups φ B r := by
  apply exists_subset_with_stable_generatedSubgroups φ A r (M ^ d₀)
  intro D hDA hcost i
  obtain ⟨hfinite, hindex⟩ := finiteIndex_and_index_le_of_dense_box
    (fun x hx => iteratedImageSums_mem_generatedSubgroup (φ i) D (h i) x hx)
    ((iteratedImageSums_mono (φ i) (h i) hDA).trans (hbox i))
    (hdense D hDA hcost i) (hwidth i)
  refine ⟨hfinite, ?_⟩
  have hi : (generatedSubgroup (φ i) D).index ≤ M ^ d i := by
    simpa only [Fintype.card_fin] using hindex
  exact hi.trans (pow_le_pow_right₀ hM (hdim i))

end Erdos587.CFP
