import Wikipedia.HopfProblem.DegreeCollapseIndexedMorseCancellation
import Wikipedia.SmoothSixDPoincare.OrderedMorseLevelContractions

/-!
# Constructing lower-level circle contractions from intrinsic index data

An index-zero count of one identifies the first critical point as the
only minimum index, and a zero index-one count excludes all such handles.
If the critical points preceding an index-two point have index at most two,
the actual preceding surgeries all have index two. The constructed first
disk and ordered surgery theorem therefore give the required contractions.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem native_index_zero_point_unique (S : SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hn : 0 < S.count)
    (hcount : nativeMorseCount E f 0 = 1) :
    ∀ z ∈ criticalPoints E f, nativeMorseIndex E f z = 0 → z = (S.first hn).val := by
  have hfirst : nativeMorseIndex E f (S.first hn) = 0 :=
    (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
  change {z : M | z ∈ criticalPoints E f ∧ nativeMorseIndex E f z = 0}.ncard = 1 at hcount
  obtain ⟨z₀, hz₀⟩ := Set.ncard_eq_one.mp hcount
  have hfirstmem : (S.first hn).val ∈
      {z : M | z ∈ criticalPoints E f ∧ nativeMorseIndex E f z = 0} :=
    ⟨(S.first hn).property, hfirst⟩
  rw [hz₀, mem_singleton_iff] at hfirstmem
  intro z hz hi
  have hzmem : z ∈ {z : M | z ∈ criticalPoints E f ∧ nativeMorseIndex E f z = 0} := ⟨hz, hi⟩
  rw [hz₀, mem_singleton_iff] at hzmem
  exact hzmem.trans hfirstmem.symm

theorem native_index_one_excluded (S : SurgeryWindows E f)
    (hcount : nativeMorseCount E f 1 = 0) :
    ∀ z ∈ criticalPoints E f, nativeMorseIndex E f z ≠ 1 := by
  have hfinite : {z : M | z ∈ criticalPoints E f ∧ nativeMorseIndex E f z = 1}.Finite :=
    S.finite.subset (fun _ hz => hz.1)
  have hempty : {z : M | z ∈ criticalPoints E f ∧ nativeMorseIndex E f z = 1} = ∅ :=
    (Set.ncard_eq_zero hfinite).mp hcount
  intro z hz hi
  have hmem : z ∈ {z : M | z ∈ criticalPoints E f ∧ nativeMorseIndex E f z = 1} := ⟨hz, hi⟩
  rw [hempty] at hmem
  exact hmem

open Classical in
theorem lower_circle_nullhomotopies_of_ordered_native_indices (S : SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (p : criticalPoints E f) (hpindex : nativeMorseIndex E f p = 2)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0)
    (horder : ∀ r : criticalPoints E f, f r < f p → nativeMorseIndex E f r ≤ 2) :
    ∀ γ : C(Hemisphere.Sphere 1, (S.data p).LowerLevel),
      ∃ z, γ.Homotopic (ContinuousMap.const _ z) := by
  obtain ⟨j, rfl⟩ := S.point.surjective p
  have hn : 0 < S.count := (Nat.zero_le j.val).trans_lt j.isLt
  have hpnotfirst : S.point j ≠ S.first hn := by
    intro hpfirst
    have hfirst : nativeMorseIndex E f (S.first hn) = 0 :=
      (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
    rw [hpfirst] at hpindex
    omega
  have hj : 0 < j.val := by
    by_contra hj
    have hj0 : j.val = 0 := by omega
    have heq : S.point j = S.first hn := congrArg S.point (Fin.ext hj0)
    exact hpnotfirst heq
  have hmiddle (i : Fin S.count) (hi : 0 < i.val) (hij : i.val < j.val) :
      Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 2 ∨
      Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 3 := by
    have hvalues : f (S.point i) < f (S.point j) := S.point_strictMono (show i < j from hij)
    have hle := horder (S.point i) hvalues
    have hne0 : nativeMorseIndex E f (S.point i) ≠ 0 := by
      intro hindex
      have heq : (S.point i).val = (S.first hn).val :=
        native_index_zero_point_unique S hf hn hzero _ (S.point i).property hindex
      have heq' : S.point i = S.point ⟨0, hn⟩ := Subtype.ext heq
      have hival := congrArg Fin.val (S.point.injective heq')
      change i.val = 0 at hival
      omega
    have hne1 := native_index_one_excluded S hone _ (S.point i).property
    have hindex : nativeMorseIndex E f (S.point i) = 2 := by omega
    exact Or.inl ((nativeMorseIndex_eq_chart (S.data (S.point i)).chart).symm.trans hindex)
  exact S.lower_circle_nullhomotopies_of_middle_indices hf hdim j hj hmiddle

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
