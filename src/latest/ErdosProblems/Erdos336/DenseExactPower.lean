import Mathlib
import ErdosProblems.Erdos336.ThickAbsorption
import ErdosProblems.Erdos336.CompactCover

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Dense exact powers from compact covers by a closed image
-/

namespace Erdos336

open scoped Pointwise

private theorem nsmul_topological_closure_subset
    {K : Type*} [TopologicalSpace K] [AddCommGroup K]
    [IsTopologicalAddGroup K] (A : Set K) :
    ∀ M : ℕ, M • closure A ⊆ closure (M • A) := by
  intro M
  induction M with
  | zero => exact subset_closure
  | succ M ih =>
      rw [succ_nsmul]
      intro y hy
      obtain ⟨x, hx, z, hz, rfl⟩ := hy
      have hx' : x ∈ closure (M • A) := ih hx
      exact vadd_set_closure_subset (M • A) A ⟨x, hx', z, hz, rfl⟩

private theorem zRep_of_mem_nsmul
    {D : Set ℤ} {M : ℕ} {s : ℤ} (hs : s ∈ M • D) :
    ZRepExactly D M s := by
  rw [Set.mem_nsmul] at hs
  obtain ⟨f, hf⟩ := hs
  let xs : List ℤ := List.ofFn (fun i : Fin M => (f i : ℤ))
  refine ⟨xs, by simp [xs], ?_, ?_⟩
  · intro x hx
    simp only [xs, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (f i).2
  · exact hf

/-- If the `M`-fold sum of the closure of `φ(D)` is the whole compact group,
then the images of exact `M`-representable integer shifts are dense. -/
theorem dense_representable_of_closed_power_cover
    {K : Type*} [TopologicalSpace K] [AddCommGroup K]
    [IsTopologicalAddGroup K]
    (φ : ℤ →+ K) {D : Set ℤ} {M : ℕ}
    (hcover : M • closure (φ '' D) = (Set.univ : Set K)) :
    Dense (φ '' {s : ℤ | ZRepExactly D M s}) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_univ_subset
  intro y hy
  have hyclosed : y ∈ closure (M • (φ '' D)) := by
    apply nsmul_topological_closure_subset (φ '' D) M
    rw [hcover]
    exact Set.mem_univ y
  apply closure_mono ?_ hyclosed
  intro z hz
  rw [← Set.image_nsmul φ D M] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  exact ⟨s, zRep_of_mem_nsmul hs, rfl⟩

/-- Compact cover consequence in the form needed by piecewise-Bohr
transference: a full closed `M`-fold power supplies finitely many exact
`M`-representable shifts covering every orbit point of an open patch. -/
theorem finite_patch_cover_of_closed_power
    {K : Type*} [TopologicalSpace K] [AddCommGroup K]
    [IsTopologicalAddGroup K] [CompactSpace K]
    (φ : ℤ →+ K) {D : Set ℤ} {M : ℕ} {U : Set K}
    (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hpower : M • closure (φ '' D) = (Set.univ : Set K)) :
    ∃ S : Finset ℤ,
      (∀ s ∈ S, ZRepExactly D M s) ∧
      (∀ n : ℤ, ∃ s ∈ S, φ (n - s) ∈ U) := by
  apply finite_representable_patch_cover φ hUopen hUne
  exact dense_representable_of_closed_power_cover φ hpower

end Erdos336
