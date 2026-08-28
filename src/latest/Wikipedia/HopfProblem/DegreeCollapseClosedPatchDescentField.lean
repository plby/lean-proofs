import Wikipedia.SmoothSixDPoincare.DescentFieldGluing

/-!
# Prescribed descending fields on finitely many disjoint closed patches

A given global descending field handles the complement of the patches.
The local fields need only agree with their own zero and descent
constraints. Removing the other closed patches gives the required local
compatibility without disjoint open charts or a cover of all critical points.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem exists_closed_patch_descent_field {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (V₀ : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV₀ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V₀ x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero₀ : ∀ x ∈ ManifoldMorse.criticalPoints E f, V₀ x = 0)
    (hdesc₀ : ∀ x, x ∉ ManifoldMorse.criticalPoints E f →
      mvfderiv 𝓘(ℝ, E) f x (V₀ x) < 0)
    {ι : Type*} [Finite ι] (K U : ι → Set M)
    (hK : ∀ i, IsClosed (K i)) (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i)
    (hdisj : Pairwise (fun i j => Disjoint (K i) (K j)))
    (Vloc : ι → (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hVloc : ∀ i, ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, Vloc i x⟩ : TangentBundle 𝓘(ℝ, E) M)) (U i))
    (hzero : ∀ i x, x ∈ U i → x ∈ ManifoldMorse.criticalPoints E f → Vloc i x = 0)
    (hdesc : ∀ i x, x ∈ U i → x ∉ ManifoldMorse.criticalPoints E f →
      mvfderiv 𝓘(ℝ, E) f x (Vloc i x) < 0) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0) ∧
      (∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
      ∀ i x, x ∈ K i → V x = Vloc i x := by
  classical
  let C : (x : M) → Set (TangentSpace 𝓘(ℝ, E) x) := fun x =>
    {w | (x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x w < 0) ∧
      (x ∈ ManifoldMorse.criticalPoints E f → w = 0) ∧
      ∀ i, x ∈ K i → w = Vloc i x}
  have hC (x : M) : Convex ℝ (C x) := by
    intro u hu v hv a b ha hb hab
    refine ⟨?_, ?_, ?_⟩
    · intro hreg
      have h := (convex_Iio (0 : ℝ)) (hu.1 hreg) (hv.1 hreg) ha hb hab
      simpa only [map_add, map_smul, smul_eq_mul, mem_Iio] using h
    · intro hcrit
      rw [hu.2.1 hcrit, hv.2.1 hcrit, smul_zero, smul_zero, add_zero]
    · intro i hxi
      rw [hu.2.2 i hxi, hv.2.2 i hxi, ← add_smul, hab, one_smul]
  have hclosed : IsClosed (⋃ i, K i) := isClosed_iUnion_of_finite hK
  have hlocal : ∀ p : M, ∃ O ∈ 𝓝 p,
      ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
        ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
          (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) O ∧
        ∀ x ∈ O, V x ∈ C x := by
    intro p
    by_cases hp : p ∈ ⋃ i, K i
    · obtain ⟨i, hpi⟩ := mem_iUnion.mp hp
      let R := ⋃ j : {j : ι // j ≠ i}, K j
      have hR : IsClosed R := isClosed_iUnion_of_finite (fun j => hK j)
      have hpR : p ∉ R := by
        intro hpR
        obtain ⟨j, hpj⟩ := mem_iUnion.mp hpR
        exact Set.disjoint_left.mp (hdisj (fun h => j.property h.symm)) hpi hpj
      refine ⟨U i ∩ Rᶜ, ((hU i).inter hR.isOpen_compl).mem_nhds ⟨hKU i hpi, hpR⟩,
        Vloc i, (hVloc i).mono inter_subset_left, ?_⟩
      intro x hx
      refine ⟨hdesc i x hx.1, hzero i x hx.1, ?_⟩
      intro j hxj
      by_cases hij : i = j
      · subst j
        rfl
      · exact False.elim (hx.2 (mem_iUnion.mpr ⟨⟨j, fun h => hij h.symm⟩, hxj⟩))
    · refine ⟨(⋃ i, K i)ᶜ, hclosed.isOpen_compl.mem_nhds hp,
        V₀, hV₀.contMDiffOn, ?_⟩
      intro x hx
      refine ⟨hdesc₀ x, hzero₀ x, ?_⟩
      intro i hxi
      exact False.elim (hx (mem_iUnion.mpr ⟨i, hxi⟩))
  obtain ⟨V, hV⟩ := exists_contMDiffSection_forall_mem_convex_of_local
    (n := ⊤) 𝓘(ℝ, E) (TangentSpace 𝓘(ℝ, E) (M := M)) C hC hlocal
  exact ⟨V, V.contMDiff, fun x => (hV x).2.1, fun x => (hV x).1,
    fun i x hx => (hV x).2.2 i hx⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
