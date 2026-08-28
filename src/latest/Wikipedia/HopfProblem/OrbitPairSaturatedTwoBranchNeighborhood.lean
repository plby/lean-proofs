import Wikipedia.HopfProblem.OrbitPairNativeLocalInjectivity

/-!
# Saturated two-branch neighborhoods for a closed native map

Two disjoint compact source sets with injective native derivatives and
injective restrictions admit disjoint injectivity neighborhoods. If their
union is saturated and the whole map is closed, shrink a target
neighborhood so its entire preimage lies in these two branches. Both
source and target neighborhoods may be restricted to prescribed open sets.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeImmersion

variable {E G H K X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

theorem exists_saturated_two_branch_neighborhood {f : X → N}
    (hf : ContMDiff I J ∞ f) (hclosed : IsClosedMap f)
    {A B : Set X} (hA : IsCompact A) (hB : IsCompact B) (hdisj : Disjoint A B)
    (hAi : InjOn f A) (hBi : InjOn f B)
    (hi : ∀ x ∈ A ∪ B, Injective (mfderiv I J f x))
    (hsaturated : f ⁻¹' (f '' (A ∪ B)) = A ∪ B)
    {W : Set X} (hW : IsOpen W) (hAW : A ∪ B ⊆ W)
    {O₀ : Set N} (hO₀ : IsOpen O₀) (hAO₀ : MapsTo f (A ∪ B) O₀) :
    ∃ O : Set N, IsOpen O ∧ O ⊆ O₀ ∧ ∃ U V : Set X,
      IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = f ⁻¹' O ∧
      A ⊆ U ∧ B ⊆ V ∧ U ⊆ W ∧ V ⊆ W ∧ InjOn f U ∧ InjOn f V := by
  obtain ⟨R₁, R₂, hR₁, hR₂, hAR₁, hBR₂, hRdisj⟩ :=
    SeparatedNhds.of_isCompact_isCompact hA hB hdisj
  have hARW : A ⊆ R₁ ∩ W := fun x hx => ⟨hAR₁ hx, hAW (Or.inl hx)⟩
  have hBRW : B ⊆ R₂ ∩ W := fun x hx => ⟨hBR₂ hx, hAW (Or.inr hx)⟩
  obtain ⟨W₁, hW₁, hAW₁, hW₁R, hWi₁⟩ := exists_open_injOn_near_compact
    (hR₁.inter hW) hf.contMDiffOn hA hARW hAi (fun x hx => hi x (Or.inl hx))
  obtain ⟨W₂, hW₂, hBW₂, hW₂R, hWi₂⟩ := exists_open_injOn_near_compact
    (hR₂.inter hW) hf.contMDiffOn hB hBRW hBi (fun x hx => hi x (Or.inr hx))
  have hWdisj : Disjoint W₁ W₂ := hRdisj.mono
    (hW₁R.trans inter_subset_left) (hW₂R.trans inter_subset_left)
  have hpre : f ⁻¹' (f '' (A ∪ B)) ⊆ W₁ ∪ W₂ := by
    rw [hsaturated]
    exact union_subset_union hAW₁ hBW₂
  let O : Set N := O₀ ∩ (f '' (W₁ ∪ W₂)ᶜ)ᶜ
  have hO : IsOpen O := hO₀.inter
    (hclosed _ (hW₁.union hW₂).isClosed_compl).isOpen_compl
  have hCO : ∀ x ∈ A ∪ B, f x ∈ O := by
    intro x hx
    refine ⟨hAO₀ hx, ?_⟩
    rintro ⟨z, hz, heq⟩
    exact hz (hpre ⟨x, hx, heq.symm⟩)
  have hOW : f ⁻¹' O ⊆ W₁ ∪ W₂ := by
    intro x hx
    by_contra hn
    exact hx.2 ⟨x, hn, rfl⟩
  let U : Set X := W₁ ∩ f ⁻¹' O
  let V : Set X := W₂ ∩ f ⁻¹' O
  have hUV : U ∪ V = f ⁻¹' O := by
    apply subset_antisymm (union_subset inter_subset_right inter_subset_right)
    intro x hx
    rcases hOW hx with hxw | hxw
    · exact Or.inl ⟨hxw, hx⟩
    · exact Or.inr ⟨hxw, hx⟩
  exact ⟨O, hO, inter_subset_left, U, V,
    hW₁.inter (hO.preimage hf.continuous), hW₂.inter (hO.preimage hf.continuous),
    hWdisj.mono inter_subset_left inter_subset_left, hUV,
    (fun x hx => ⟨hAW₁ hx, hCO x (Or.inl hx)⟩),
    (fun x hx => ⟨hBW₂ hx, hCO x (Or.inr hx)⟩),
    (fun x hx => (hW₁R hx.1).2), (fun x hx => (hW₂R hx.1).2),
    hWi₁.mono inter_subset_left, hWi₂.mono inter_subset_left⟩

end Wikipedia.HopfProblem.OrbitPair.NativeImmersion
