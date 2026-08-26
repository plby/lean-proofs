import Mathlib
import ErdosProblems.Erdos336.ThickAbsorption

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Compactness turns dense representable shifts into a finite patch cover
-/

namespace Erdos336

/-- If exact `M`-representable integer shifts have dense image in a compact
topological additive group, finitely many of them cover every orbit point by
translates of any fixed nonempty open patch. -/
theorem finite_representable_patch_cover
    {K : Type*} [TopologicalSpace K] [AddCommGroup K]
    [IsTopologicalAddGroup K] [CompactSpace K]
    (φ : ℤ →+ K) {D : Set ℤ} {M : ℕ} {U : Set K}
    (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hdense : Dense (φ '' {s : ℤ | ZRepExactly D M s})) :
    ∃ S : Finset ℤ,
      (∀ s ∈ S, ZRepExactly D M s) ∧
      (∀ n : ℤ, ∃ s ∈ S, φ (n - s) ∈ U) := by
  let R := {s : ℤ | ZRepExactly D M s}
  let V : R → Set K := fun s => {y | y - φ s.1 ∈ U}
  have hVopen : ∀ s : R, IsOpen (V s) := by
    intro s
    exact hUopen.preimage (continuous_sub_right (φ s.1))
  have hcoverK : (Set.univ : Set K) ⊆ ⋃ s : R, V s := by
    intro y hy
    let W : Set K := {x | y - x ∈ U}
    have hWopen : IsOpen W := by
      exact hUopen.preimage (continuous_const.sub continuous_id)
    have hWne : W.Nonempty := by
      obtain ⟨u, hu⟩ := hUne
      exact ⟨y - u, by simpa [W]⟩
    obtain ⟨x, hximage, hxW⟩ := hdense.exists_mem_open hWopen hWne
    obtain ⟨s, hsR, rfl⟩ := hximage
    apply Set.mem_iUnion.mpr
    refine ⟨⟨s, hsR⟩, ?_⟩
    exact hxW
  obtain ⟨T, hTcover⟩ :=
    CompactSpace.isCompact_univ.elim_finite_subcover V hVopen hcoverK
  let S : Finset ℤ := T.image (fun s : R => s.1)
  refine ⟨S, ?_, ?_⟩
  · intro s hs
    simp only [S, Finset.mem_image] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact t.2
  · intro n
    have hnmem : φ n ∈ (Set.univ : Set K) := Set.mem_univ _
    have hnsub := hTcover hnmem
    simp only [Set.mem_iUnion] at hnsub
    obtain ⟨t, htT, htV⟩ := hnsub
    refine ⟨t.1, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨t, htT, rfl⟩
    · change φ n - φ t.1 ∈ U at htV
      simpa using htV

end Erdos336
