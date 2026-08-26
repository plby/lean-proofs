import Mathlib
import ErdosProblems.Erdos336.ThickAbsorption

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Projecting eventual exact covers to compact monothetic factors
-/

namespace Erdos336

open scoped Pointwise

private lemma mem_nsmul_of_zRep
    {D : Set ℤ} {M : ℕ} {s : ℤ} (hs : ZRepExactly D M s) :
    s ∈ M • D := by
  obtain ⟨xs, hlen, hxmem, hxsum⟩ := hs
  subst M
  rw [Set.mem_nsmul]
  let f : Fin xs.length → D := fun i =>
    ⟨xs.get i, hxmem (xs.get i) (List.get_mem xs i)⟩
  refine ⟨f, ?_⟩
  change (List.ofFn (fun i : Fin xs.length => xs.get i)).sum = s
  rw [List.ofFn_get]
  exact hxsum

private lemma compact_nsmul
    {K : Type*} [TopologicalSpace K] [AddCommGroup K]
    [IsTopologicalAddGroup K] {A : Set K} (hA : IsCompact A) :
    ∀ M : ℕ, IsCompact (M • A) := by
  intro M
  induction M with
  | zero => simp
  | succ M ih =>
      rw [succ_nsmul]
      exact ih.add hA

/-- In a compact monothetic factor, deleting an initial segment of the
positive orbit does not destroy density. -/
theorem dense_image_int_tail
    {K : Type*} [TopologicalSpace K] [AddCommGroup K]
    [IsTopologicalAddGroup K] [CompactSpace K]
    (φ : ℤ →+ K) (hdense : DenseRange φ) (N : ℤ) :
    Dense (φ '' {n : ℤ | N ≤ n}) := by
  let α : K := φ 1
  have hmap (z : ℤ) : φ z = z • α := by
    dsimp [α]
    rw [← map_zsmul]
    simp
  have hdenseNat : Dense (Set.range (fun k : ℕ => k • α)) := by
    rw [dense_iff_closure_eq]
    rw [← closure_range_zsmul_eq_nsmul α]
    have hz : Set.range (fun z : ℤ => z • α) = Set.range φ := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨z, hmap z⟩
      · rintro ⟨z, rfl⟩
        exact ⟨z, (hmap z).symm⟩
    rw [hz]
    exact (dense_iff_closure_eq.mp hdense)
  let N0 : ℕ := N.toNat
  have hshift : Dense ((φ (N0 : ℤ)) +ᵥ Set.range (fun k : ℕ => k • α)) :=
    hdenseNat.vadd (φ (N0 : ℤ))
  apply hshift.mono
  intro y hy
  obtain ⟨z, ⟨k, rfl⟩, rfl⟩ := hy
  refine ⟨(N0 : ℤ) + k, ?_, ?_⟩
  · change N ≤ (N0 : ℤ) + (k : ℤ)
    have hNN0 : N ≤ (N0 : ℤ) := by
      rcases le_total 0 N with hNpos | hNneg
      · dsimp [N0]
        rw [Int.toNat_of_nonneg hNpos]
      · have hz : (0 : ℤ) ≤ (N0 : ℤ) := by positivity
        omega
    omega
  · rw [map_add]
    congr 1
    simpa using hmap (k : ℤ)

private lemma zRep_union_extra_of_oneExtra
    {D : Set ℤ} {c n : ℤ} {h : ℕ}
    (hrep : ∃ j : ℕ, j ≤ h ∧
      ZRepExactly D (h - j) (n - (j : ℤ) * c)) :
    ZRepExactly (D ∪ {c}) h n := by
  obtain ⟨j, hjh, xs, hlen, hxmem, hxsum⟩ := hrep
  let ys := xs ++ List.replicate j c
  refine ⟨ys, ?_, ?_, ?_⟩
  · simp [ys, hlen]
    omega
  · intro x hx
    simp only [ys, List.mem_append, List.mem_replicate] at hx
    rcases hx with hx | ⟨_, rfl⟩
    · exact Or.inl (hxmem x hx)
    · exact Or.inr rfl
  · simp [ys, hxsum]

/-- Eventual exact parent coverage by `D` and one extra point projects to a
full exact parent power of the closed image in a compact monothetic factor. -/
theorem closed_parent_power_eq_univ_of_eventuallyWithOneExtra
    {K : Type*} [TopologicalSpace K] [AddCommGroup K]
    [IsTopologicalAddGroup K] [CompactSpace K] [T2Space K]
    (φ : ℤ →+ K) (hdense : DenseRange φ)
    {D : Set ℤ} {c : ℤ} {h : ℕ}
    (hparent : EventuallyWithOneExtra D c h) :
    h • (closure (φ '' D) ∪ {φ c}) = (Set.univ : Set K) := by
  obtain ⟨N, hN⟩ := hparent
  let E : Set K := closure (φ '' D) ∪ {φ c}
  have hcompactE : IsCompact E :=
    isClosed_closure.isCompact.union (isCompact_singleton)
  have hcompactC : IsCompact (h • E) := compact_nsmul hcompactE h
  have hclosedC : IsClosed (h • E) := hcompactC.isClosed
  have htail : φ '' {n : ℤ | N ≤ n} ⊆ h • E := by
    rintro y ⟨n, hn, rfl⟩
    have hnrep : ZRepExactly (D ∪ {c}) h n :=
      zRep_union_extra_of_oneExtra (hN n hn)
    have hnmem : n ∈ h • (D ∪ {c}) := mem_nsmul_of_zRep hnrep
    have himage : φ n ∈ h • (φ '' (D ∪ {c})) := by
      rw [← Set.image_nsmul φ (D ∪ {c}) h]
      exact ⟨n, hnmem, rfl⟩
    apply Set.nsmul_subset_nsmul_left ?_ himage
    intro z hz
    obtain ⟨a, ha, rfl⟩ := hz
    rcases ha with ha | rfl
    · exact Or.inl (subset_closure ⟨a, ha, rfl⟩)
    · exact Or.inr rfl
  apply Set.eq_univ_of_forall
  intro y
  have hdTail := dense_image_int_tail φ hdense N
  have hyclosure : y ∈ closure (φ '' {n : ℤ | N ≤ n}) :=
    dense_iff_closure_eq.mp hdTail ▸ Set.mem_univ y
  exact hclosedC.closure_subset_iff.mpr htail hyclosure

/-- Eventual exact integer coverage projects to a full exact power of the
closed image in every compact monothetic factor with dense orbit. -/
theorem closed_power_eq_univ_of_eventuallyExactlyZ
    {K : Type*} [TopologicalSpace K] [AddCommGroup K]
    [IsTopologicalAddGroup K] [CompactSpace K] [T2Space K]
    (φ : ℤ →+ K) (hdense : DenseRange φ)
    {D : Set ℤ} {M : ℕ} (hD : EventuallyExactlyZ D M) :
    M • closure (φ '' D) = (Set.univ : Set K) := by
  obtain ⟨N, hN⟩ := hD
  let C : Set K := M • closure (φ '' D)
  have hcompactE : IsCompact (closure (φ '' D)) :=
    isClosed_closure.isCompact
  have hcompactC : IsCompact C := compact_nsmul hcompactE M
  have hclosedC : IsClosed C := hcompactC.isClosed
  have htail : φ '' {n : ℤ | N ≤ n} ⊆ C := by
    rintro y ⟨n, hn, rfl⟩
    have hnrep := hN n hn
    have hnmem : n ∈ M • D := mem_nsmul_of_zRep hnrep
    have himage : φ n ∈ M • (φ '' D) := by
      rw [← Set.image_nsmul φ D M]
      exact ⟨n, hnmem, rfl⟩
    exact Set.nsmul_subset_nsmul_left subset_closure himage
  apply Set.eq_univ_of_forall
  intro y
  have hdTail := dense_image_int_tail φ hdense N
  have hyclosure : y ∈ closure (φ '' {n : ℤ | N ≤ n}) :=
    dense_iff_closure_eq.mp hdTail ▸ Set.mem_univ y
  exact hclosedC.closure_subset_iff.mpr htail hyclosure

end Erdos336
