import Wikipedia.SmoothSixDPoincare.PrescribedDerivativeField

/-!
# Gluing descending fields while preserving prescribed local pieces

A smooth partition of unity solves a convex constraint in each tangent
fiber: strictly decrease the function at regular points, and agree exactly
with a specified local field on each closed patch. The patches have disjoint
open neighborhoods and cover the critical set.
-/

noncomputable section

open Set Manifold
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- Preserve the prescribed local fields on closed patches while strictly descending elsewhere. -/
theorem exists_gluedDescentField {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {ι : Type*} [Finite ι] (U K : ι → Set M)
    (hU : ∀ i, IsOpen (U i)) (hK : ∀ i, IsClosed (K i))
    (hKU : ∀ i, K i ⊆ U i) (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hcover : ManifoldMorse.criticalPoints E f ⊆ ⋃ i, K i)
    (Vloc : ι → (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hVloc : ∀ i, ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, Vloc i x⟩ : TangentBundle 𝓘(ℝ, E) M)) (U i))
    (hdesc : ∀ i x, x ∈ U i → x ∉ ManifoldMorse.criticalPoints E f →
      mvfderiv 𝓘(ℝ, E) f x (Vloc i x) < 0) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
      ∀ i x, x ∈ K i → V x = Vloc i x := by
  let C : (x : M) → Set (TangentSpace 𝓘(ℝ, E) x) := fun x =>
    {w | (x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x w < 0) ∧
      ∀ i, x ∈ K i → w = Vloc i x}
  have hC (x : M) : Convex ℝ (C x) := by
    intro u hu v hv a b ha hb hab
    refine ⟨?_, ?_⟩
    · intro hreg
      have h := (convex_Iio (0 : ℝ)) (hu.1 hreg) (hv.1 hreg) ha hb hab
      simpa only [map_add, map_smul, smul_eq_mul, mem_Iio] using h
    · intro i hxi
      rw [hu.2 i hxi, hv.2 i hxi, ← add_smul, hab, one_smul]
  have hclosed : IsClosed (⋃ i, K i) := isClosed_iUnion_of_finite hK
  have hlocal : ∀ p : M, ∃ W ∈ 𝓝 p,
      ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
        ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
          (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) W ∧
        ∀ x ∈ W, V x ∈ C x := by
    intro p
    by_cases hp : p ∈ ⋃ i, K i
    · obtain ⟨i, hpi⟩ := mem_iUnion.mp hp
      refine ⟨U i, (hU i).mem_nhds (hKU i hpi), Vloc i, hVloc i, ?_⟩
      intro x hx
      refine ⟨hdesc i x hx, ?_⟩
      intro j hxj
      by_cases hij : i = j
      · subst j
        rfl
      · exact False.elim (Set.disjoint_left.mp (hdisj hij) hx (hKU j hxj))
    · have hpreg : p ∉ ManifoldMorse.criticalPoints E f := fun h => hp (hcover h)
      obtain ⟨W, hW, hpW, V, hV, hVf⟩ := exists_unitSpeedField_near_regular hf hpreg
      refine ⟨W ∩ (⋃ i, K i)ᶜ, (hW.inter hclosed.isOpen_compl).mem_nhds ⟨hpW, hp⟩,
        (fun x => -(V x)), hV.neg_section.mono inter_subset_left, ?_⟩
      intro x hx
      refine ⟨?_, ?_⟩
      · intro _
        change mvfderiv 𝓘(ℝ, E) f x (-V x) < 0
        rw [map_neg, hVf x hx.1]
        norm_num
      · intro i hxi
        exact False.elim (hx.2 (mem_iUnion.mpr ⟨i, hxi⟩))
  obtain ⟨V, hV⟩ := exists_contMDiffSection_forall_mem_convex_of_local
    (n := ⊤) 𝓘(ℝ, E) (TangentSpace 𝓘(ℝ, E) (M := M)) C hC hlocal
  exact ⟨V, V.contMDiff, fun x => (hV x).1, fun i x hx => (hV x).2 i hx⟩

end Wikipedia.SmoothSixDPoincare.FlowConstruction
