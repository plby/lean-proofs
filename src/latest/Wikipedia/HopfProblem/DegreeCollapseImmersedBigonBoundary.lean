import Wikipedia.HopfProblem.DegreeCollapseImmersedWhitneyStrips
import Wikipedia.SmoothSixDPoincare.StripPairOverlap
import Wikipedia.SmoothSixDPoincare.StripPatchRestriction
import Wikipedia.SmoothSixDPoincare.SmoothCleanBigonBoundary

/-!
# A clean native bigon boundary from actual self-intersection branches

The constructed strips have the same corner maps. Their only possible
center coincidences are the two matching endpoints, so compact shrinking
removes every other strip overlap. The actual strip germs then construct
the full embedded immersive boundary neighborhood, retaining the normal
data for the framing step. This does not yet construct a framed Whitney
disk with interior avoiding the entire original immersed image.
-/

noncomputable section

open Set Function Module Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open Wikipedia.SmoothSixDPoincare

variable {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (Vector 6) M] [IsManifold (𝓡 6) ∞ M]
  {f : Sphere 3 → M}

theorem exists_native_branch_bigon_boundary
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x))
    (ht : ∀ x y, x ≠ y → f x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) f y)))
    {x₀ x₁ y₀ y₁ : Sphere 3} {u₀ u₁ v₀ v₁ : Vector 3}
    (a : CleanJoiningArc f x₀ x₁ u₀ u₁) (b : CleanJoiningArc f y₀ y₁ v₀ v₁)
    (hc₀ : f x₀ = f y₀) (hc₁ : f x₁ = f y₁)
    (hu₀ : u₀ ≠ 0) (hu₁ : u₁ ≠ 0) (hv₀ : v₀ ≠ 0) (hv₁ : v₁ ≠ 0)
    {U V : Set (Sphere 3)} (hU : IsOpen U) (hV : IsOpen V)
    (hAU : a.map '' Icc (0 : ℝ) 1 ⊆ U) (hBV : b.map '' Icc (0 : ℝ) 1 ⊆ V)
    (hUV : Disjoint (closure U) (closure V))
    (hUc : IsCompact (closure U)) (hVc : IsCompact (closure V))
    (heU : IsClosedEmbedding (fun x : closure U => f x))
    (heV : IsClosedEmbedding (fun x : closure V => f x))
    {O : Set M} (hO : IsOpen O)
    (hAO : MapsTo (f ∘ a.map) (Icc (0 : ℝ) 1) O)
    (hBO : MapsTo (f ∘ b.map) (Icc (0 : ℝ) 1) O) :
    ∃ c₀ : CleanCornerPatch (E := Vector 6) (f '' closure U) (f '' closure V)
        (fun t => f (NativeParametrization.centered (D := Vector 3) x₀ (t • u₀)))
        (fun t => f (NativeParametrization.centered (D := Vector 3) y₀ (t • v₀))),
      ∃ c₁ : CleanCornerPatch (E := Vector 6) (f '' closure U) (f '' closure V)
          (fun t => f (NativeParametrization.centered (D := Vector 3) x₁ (t • u₁)))
          (fun t => f (NativeParametrization.centered (D := Vector 3) y₁ (t • v₁))),
        ∃ k : CleanStripPatch (E := Vector 6) (f '' closure U) (f '' closure V)
            (f ∘ a.map) c₀.map c₁.map,
          ∃ l : CleanStripPatch (E := Vector 6) (f '' closure V) (f '' closure U)
              (f ∘ b.map) c₀.swap.map c₁.swap.map,
            Nonempty (StripNormalData (Vector 2) (Vector 3) (E := Vector 6)
              (f '' closure U) k.map) ∧
            Nonempty (StripNormalData (Vector 2) (Vector 3) (E := Vector 6)
              (f '' closure V) l.map) ∧ MapsTo k.map k.domain O ∧ MapsTo l.map l.domain O ∧
            (∀ p ∈ k.domain, ∀ q ∈ l.domain, k.map p = l.map q →
              p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap) ∧
            ∀ h : ℝ, 0 < h →
              Nonempty (CleanBigonBoundary (E := Vector 6) (f '' closure U) (f '' closure V)
                (f ∘ a.map) (f ∘ b.map) k.map l.map h) ∧
              ∀ _e : M ≃ₕ SixSphere,
                Nonempty (SmoothCleanBigonBoundary (E := Vector 6) (f '' closure U) (f '' closure V)
                  (f ∘ a.map) (f ∘ b.map) k.map l.map h) := by
  obtain ⟨c₀, c₁, k, l, hnK, hnL, hkO, hlO⟩ := exists_native_branch_strip_pair hf hi ht a b
    hc₀ hc₁ hu₀ hu₁ hv₀ hv₁ hU hV hAU hBV hUV hUc hVc heU heV hO hAO hBO
  have hab : Disjoint (a.map '' Icc (0 : ℝ) 1) (b.map '' Icc (0 : ℝ) 1) :=
    hUV.mono (fun _ hx => subset_closure (hAU hx)) (fun _ hy => subset_closure (hBV hy))
  have hinter := a.ambient_intersection_eq b hab hc₀ hc₁
  have hia : InjOn a.map (Icc (0 : ℝ) 1) := by
    intro t htI s hsI he
    exact congrArg Subtype.val (a.embedded.injective (a₁ := ⟨t, htI⟩) (a₂ := ⟨s, hsI⟩) he)
  have hib : InjOn b.map (Icc (0 : ℝ) 1) := by
    intro t htI s hsI he
    exact congrArg Subtype.val (b.embedded.injective (a₁ := ⟨t, htI⟩) (a₂ := ⟨s, hsI⟩) he)
  have h0 : (0 : ℝ) ∈ Icc 0 1 := by simp
  have h1 : (1 : ℝ) ∈ Icc 0 1 := by simp
  have hcoinc : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      (f ∘ a.map) t = (f ∘ b.map) s → (t = 0 ∧ s = 0) ∨ (t = 1 ∧ s = 1) := by
    intro t htI s hsI he
    have hmem : f (a.map t) ∈ ({f x₀, f x₁} : Set M) := by
      rw [← hinter]
      exact ⟨⟨a.map t, ⟨t, htI, rfl⟩, rfl⟩, ⟨b.map s, ⟨s, hsI, rfl⟩, he.symm⟩⟩
    change f (a.map t) = f x₀ ∨ f (a.map t) = f x₁ at hmem
    rcases hmem with hleft | hright
    · left
      constructor
      · exact hia htI h0 (a.image_injective ⟨t, htI, rfl⟩ ⟨0, h0, rfl⟩
          (hleft.trans (congrArg f a.start).symm))
      · exact hib hsI h0 (b.image_injective ⟨s, hsI, rfl⟩ ⟨0, h0, rfl⟩
          (he.symm.trans (hleft.trans (hc₀.trans (congrArg f b.start).symm))))
    · right
      constructor
      · exact hia htI h1 (a.image_injective ⟨t, htI, rfl⟩ ⟨1, h1, rfl⟩
          (hright.trans (congrArg f a.finish).symm))
      · exact hib hsI h1 (b.image_injective ⟨s, hsI, rfl⟩ ⟨1, h1, rfl⟩
          (he.symm.trans (hright.trans (hc₁.trans (congrArg f b.finish).symm))))
  obtain ⟨ε, hε, δ, hδ, W, Z, hW, hZ, hrectW, hrectZ, hWk, hZl, hoverlap⟩ :=
    exists_clean_strip_pair_neighborhoods c₀ c₁ k l hcoinc
  let k' := k.restrict hε hW hrectW hWk
  let l' := l.restrict hδ hZ hrectZ hZl
  have hoverlap' : ∀ p ∈ k'.domain, ∀ q ∈ l'.domain, k'.map p = l'.map q →
      p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap := hoverlap
  refine ⟨c₀, c₁, k', l', hnK, hnL, fun _ hp => hkO (hWk hp),
    fun _ hp => hlO (hZl hp), hoverlap', ?_⟩
  intro h hh
  obtain ⟨d⟩ := nonempty_cleanBigonBoundary hh c₀ c₁ k' l' hoverlap'
  exact ⟨⟨d⟩, fun e => nonempty_smoothCleanBigonBoundary e d⟩

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
