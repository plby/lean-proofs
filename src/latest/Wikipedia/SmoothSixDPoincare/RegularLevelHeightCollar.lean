import Wikipedia.SmoothSixDPoincare.CollarHeightCoordinates
import Wikipedia.SmoothSixDPoincare.RegularLevelCollar

/-!
# A collar whose second coordinate is exactly the original height

Invert the height-coordinate change inside the constructed transverse collar.
The resulting smooth partial diffeomorphism fixes the original level and
satisfies the exact equation `f (Φ (x,t)) = b + t` on its entire source.
-/

noncomputable section

open Set Metric Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.RegularLevel

/-- Compactness turns an open neighborhood of a whole level into a uniform height band. -/
theorem exists_heightBand_subset_open {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {g : X → ℝ} (hg : Continuous g) {a : ℝ} {U : Set X} (hU : IsOpen U)
    (hlevel : ∀ x, g x = a → x ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ g ⁻¹' ball a δ ⊆ U := by
  have hclosed : IsClosed (g '' Uᶜ) := (hU.isClosed_compl.isCompact.image hg).isClosed
  have ha : a ∉ g '' Uᶜ := by
    rintro ⟨x, hx, hxa⟩
    exact hx (hlevel x hxa)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl a ha
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  by_contra hnot
  exact hball hx ⟨x, hnot, rfl⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
  (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)

/-- The exact height collar is constructed from the original smooth function and regularity. -/
theorem exists_heightCollar [Nonempty {x : M // f x = b}] :
    letI := chartedSpace hf hreg
    ∃ ε : ℝ, 0 < ε ∧
      ∃ Ψ : PartialDiffeomorph (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
          ({x : M // f x = b} × ℝ) M ∞,
        (univ : Set {x : M // f x = b}) ×ˢ closedBall (0 : ℝ) ε ⊆ Ψ.source ∧
        (∀ x : {x : M // f x = b}, Ψ (x, 0) = x) ∧
        ∀ z ∈ Ψ.source, f (Ψ z) = b + z.2 := by
  let _ := chartedSpace hf hreg
  let _ := isManifold hf hreg
  let _ : CompactSpace {x : M // f x = b} :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  obtain ⟨ε, hε, Φ, hsource, hzero, hderiv⟩ := exists_transverseCollar hf hreg
  let H : {x : M // f x = b} × ℝ → ℝ := fun z => f (Φ z) - b
  have hH : ContMDiffOn (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ H Φ.source :=
    (hf.comp_contMDiffOn Φ.contMDiffOn_toFun).sub contMDiff_const.contMDiffOn
  have hH0 (x : {x : M // f x = b}) : H (x, 0) = 0 := by
    change f (Φ (x, 0)) - b = 0
    rw [hzero x, x.property, sub_self]
  have hzeroSource (x : {x : M // f x = b}) : (x, 0) ∈ Φ.source :=
    hsource ⟨mem_univ x, mem_closedBall_self hε.le⟩
  have hHt (x : {x : M // f x = b}) : HasDerivAt (fun t : ℝ => H (x, t)) 1 0 :=
    (hderiv x).sub_const b
  obtain ⟨χ, hKχ, -, hχ⟩ :=
    CollarHeight.exists_heightChangeChart Φ.open_source hH hH0 hzeroSource hHt
  have hχzero (x : {x : M // f x = b}) : χ (x, 0) = (x, 0) :=
    (congrFun hχ (x, 0)).trans (CollarHeight.heightChange_zero hH0 x)
  have hχtarget (x : {x : M // f x = b}) : (x, 0) ∈ χ.target := by
    rw [← hχzero x]
    exact χ.map_source' (hKχ ⟨mem_univ x, rfl⟩)
  have hχinv (x : {x : M // f x = b}) : χ.symm (x, 0) = (x, 0) := by
    have hh : χ.symm (χ (x, 0)) = (x, 0) := χ.left_inv' (hKχ ⟨mem_univ x, rfl⟩)
    rwa [hχzero x] at hh
  let Ψ := χ.symm.trans Φ
  have hzeroΨ : (univ : Set {x : M // f x = b}) ×ˢ {(0 : ℝ)} ⊆ Ψ.source := by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    have ht0 : t = 0 := ht
    subst t
    refine ⟨hχtarget x, ?_⟩
    change χ.symm (x, 0) ∈ Φ.source
    rw [hχinv x]
    exact hzeroSource x
  obtain ⟨δ, hδ, hproduct⟩ := DiskFraming.exists_pos_prod_closedBall_subset
    isCompact_univ Ψ.open_source hzeroΨ
  refine ⟨δ, hδ, Ψ, hproduct, ?_, ?_⟩
  · intro x
    change Φ (χ.symm (x, 0)) = x
    rw [hχinv x, hzero x]
  · intro z hz
    have hheight : H (χ.symm z) = z.2 := by
      calc
        H (χ.symm z) = (χ (χ.symm z)).2 :=
          (congrArg Prod.snd (congrFun hχ (χ.symm z))).symm
        _ = z.2 := congrArg Prod.snd (χ.right_inv' hz.1)
    change f (Φ (χ.symm z)) = b + z.2
    change f (Φ (χ.symm z)) - b = z.2 at hheight
    linarith

/-- The exact collar covers the entire nearby height band of the original compact manifold. -/
theorem exists_heightCollar_with_band [Nonempty {x : M // f x = b}] :
    letI := chartedSpace hf hreg
    ∃ ε : ℝ, 0 < ε ∧
      ∃ Ψ : PartialDiffeomorph (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
          ({x : M // f x = b} × ℝ) M ∞,
        (univ : Set {x : M // f x = b}) ×ˢ closedBall (0 : ℝ) ε ⊆ Ψ.source ∧
        (∀ x : {x : M // f x = b}, Ψ (x, 0) = x) ∧
        (∀ z ∈ Ψ.source, f (Ψ z) = b + z.2) ∧
        f ⁻¹' ball b ε ⊆ Ψ.target := by
  let _ := chartedSpace hf hreg
  obtain ⟨ε, hε, Ψ, hsource, hzero, hheight⟩ := exists_heightCollar hf hreg
  have hlevel : ∀ x, f x = b → x ∈ Ψ.target := by
    intro x hx
    let y : {x : M // f x = b} := ⟨x, hx⟩
    have hmem : Ψ (y, 0) ∈ Ψ.target :=
      Ψ.map_source' (hsource ⟨mem_univ y, mem_closedBall_self hε.le⟩)
    have hy : Ψ (y, 0) = x := hzero y
    exact hy ▸ hmem
  obtain ⟨δ, hδ, hband⟩ := exists_heightBand_subset_open hf.continuous Ψ.open_target hlevel
  refine ⟨min ε δ, lt_min hε hδ, Ψ, ?_, hzero, hheight, ?_⟩
  · exact fun z hz => hsource ⟨hz.1, closedBall_subset_closedBall (min_le_left ε δ) hz.2⟩
  · exact fun x hx => hband (ball_subset_ball (min_le_right ε δ) hx)

end Wikipedia.SmoothSixDPoincare.RegularLevel
