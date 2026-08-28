import Wikipedia.NoExoticSixSphere.JamesFiltration
import Mathlib.Topology.DiscreteSubset
import Mathlib.Order.Bounds.Basic

/-!
# Compact domains map into a finite James stage

In the actual final topology, every compact subset has bounded reduced-word
length. The proof rules out an unbounded sequence by showing that every
subset of its range is closed. This does not assume a CW structure or a
James/loop-space equivalence. The base space only needs closed points.
-/

noncomputable section

open Set Topology

namespace NoExoticSixSphere.James

variable {X : Type*} (x₀ : X) [TopologicalSpace X]

theorem isClosed_iff_on_words (s : Set (Space X x₀)) :
    IsClosed s ↔ ∀ n : ℕ,
      IsClosed ((fun v : Fin n → X ↦ word x₀ (List.ofFn v)) ⁻¹' s) := by
  change @IsClosed (Space X x₀)
    (TopologicalSpace.coinduced (presentation x₀) inferInstance) s ↔ _
  rw [isClosed_coinduced, isClosed_sigma_iff]
  rfl

omit [TopologicalSpace X] in
theorem finite_array_preimage (n : ℕ) {s : Set (Space X x₀)} (hs : s.Finite) :
    ((fun v : Fin n → X ↦ word x₀ (List.ofFn v)) ⁻¹' s).Finite := by
  have he : ((fun v : Fin n → X ↦ word x₀ (List.ofFn v)) ⁻¹' s) =
      ⋃ w ∈ s, {v : Fin n → X | word x₀ (List.ofFn v) = w} := by
    ext v
    simp only [mem_preimage, mem_iUnion, mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨w, hw, h⟩
      exact h ▸ hw
  rw [he]
  exact hs.biUnion (fun w _ ↦ finite_array_fiber x₀ n w)

variable [T1Space X]

instance : T1Space (Space X x₀) where
  t1 w := (isClosed_iff_on_words x₀ {w}).mpr fun n ↦
    (finite_array_preimage x₀ n (Set.finite_singleton w)).isClosed

theorem isClosed_of_finite_stage_intersections {s : Set (Space X x₀)}
    (hs : ∀ n, (s ∩ stage x₀ n).Finite) : IsClosed s := by
  apply (isClosed_iff_on_words x₀ s).mpr
  intro n
  have he : ((fun v : Fin n → X ↦ word x₀ (List.ofFn v)) ⁻¹' s) =
      ((fun v : Fin n → X ↦ word x₀ (List.ofFn v)) ⁻¹' (s ∩ stage x₀ n)) := by
    ext v
    simp only [mem_preimage, mem_inter_iff]
    have hv : word x₀ (List.ofFn v) ∈ stage x₀ n := by
      rw [← range_word_array]
      exact mem_range_self v
    exact ⟨fun h ↦ ⟨h, hv⟩, And.left⟩
  rw [he]
  exact (finite_array_preimage x₀ n (hs n)).isClosed

omit [TopologicalSpace X] [T1Space X] in
theorem finite_stage_intersection_of_size_growth (w : ℕ → Space X x₀)
    (hw : ∀ n, n < size x₀ (w n)) (m : ℕ) :
    (range w ∩ stage x₀ m).Finite := by
  apply ((Set.finite_Iio m).image w).subset
  rintro z ⟨⟨n, rfl⟩, hz⟩
  refine ⟨n, ?_, rfl⟩
  exact (hw n).trans_le hz

theorem isClosed_subset_range_of_size_growth (w : ℕ → Space X x₀)
    (hw : ∀ n, n < size x₀ (w n)) {s : Set (Space X x₀)} (hs : s ⊆ range w) :
    IsClosed s := by
  apply isClosed_of_finite_stage_intersections x₀
  intro m
  exact (finite_stage_intersection_of_size_growth x₀ w hw m).subset
    (inter_subset_inter_left _ hs)

theorem exists_stage_of_isCompact {K : Set (Space X x₀)} (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ stage x₀ n := by
  classical
  by_contra h
  have he : ∀ n : ℕ, ∃ w ∈ K, n < size x₀ w := by
    intro n
    have hn : ¬ K ⊆ stage x₀ n := fun hn ↦ h ⟨n, hn⟩
    obtain ⟨w, hw, hn⟩ := Set.not_subset.mp hn
    exact ⟨w, hw, Nat.lt_of_not_ge hn⟩
  choose w hwK hw using he
  have hc : IsClosed (range w) :=
    isClosed_subset_range_of_size_growth x₀ w hw (Subset.refl _)
  have hd : IsDiscrete (range w) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro s hs
    exact ⟨s, isClosed_subset_range_of_size_growth x₀ w hw hs,
      inter_eq_left.mpr hs⟩
  have hsub : range w ⊆ K := by
    rintro z ⟨n, rfl⟩
    exact hwK n
  have hf : (range w).Finite := (hK.of_isClosed_subset hc hsub).finite hd
  obtain ⟨n, hn⟩ := (hf.image (size x₀)).bddAbove
  have hle : size x₀ (w n) ≤ n := hn ⟨w n, mem_range_self n, rfl⟩
  exact (hw n).not_ge hle

theorem exists_stage_of_continuous {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (f : Y → Space X x₀) (hf : Continuous f) :
    ∃ n : ℕ, ∀ y, f y ∈ stage x₀ n := by
  obtain ⟨n, hn⟩ := exists_stage_of_isCompact x₀ (isCompact_range hf)
  exact ⟨n, fun y ↦ hn (mem_range_self y)⟩

theorem exists_continuous_stage_factorization {Y : Type*} [TopologicalSpace Y]
    [CompactSpace Y] (f : C(Y, Space X x₀)) :
    ∃ (n : ℕ) (g : C(Y, stage x₀ n)), ∀ y, (g y).val = f y := by
  obtain ⟨n, hn⟩ := exists_stage_of_continuous x₀ f f.continuous
  exact ⟨n, ⟨fun y ↦ ⟨f y, hn y⟩, f.continuous.subtype_mk _⟩, fun _ ↦ rfl⟩

end NoExoticSixSphere.James
