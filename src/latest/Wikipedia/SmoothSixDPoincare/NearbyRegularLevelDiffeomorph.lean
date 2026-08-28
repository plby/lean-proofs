import Wikipedia.SmoothSixDPoincare.RegularLevelHeightCollar

/-!
# Actual diffeomorphisms between nearby regular levels

Slices of the exact-height collar map onto the whole nearby level, because
the entire height band lies in the collar image. Both maps are smooth in the
native regular-level atlases and are explicit restrictions of the collar
and its inverse.
-/

noncomputable section

open Set Metric Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.RegularLevel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ}
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
  (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)

/-- Restrict the actual height collar to one level, retaining formulas for both smooth maps. -/
theorem exists_levelDiffeomorph_of_heightCollar (ε t : ℝ) (ht : |t| < ε)
    (hregt : ∀ x, f x = b + t → x ∉ ManifoldMorse.criticalPoints E f) :
    letI := chartedSpace hf hreg
    letI := chartedSpace hf hregt
    ∀ Ψ : PartialDiffeomorph (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
        ({x : M // f x = b} × ℝ) M ∞,
      ((univ : Set {x : M // f x = b}) ×ˢ closedBall (0 : ℝ) ε ⊆ Ψ.source) →
      (∀ z ∈ Ψ.source, f (Ψ z) = b + z.2) →
      (f ⁻¹' ball b ε ⊆ Ψ.target) →
      ∃ e : Diffeomorph 𝓘(ℝ, Model E) 𝓘(ℝ, Model E)
          {x : M // f x = b} {x : M // f x = b + t} ∞,
        (∀ x, (e x : M) = Ψ (x, t)) ∧ ∀ y, e.symm y = (Ψ.symm (y : M)).1 := by
  let _ := chartedSpace hf hreg
  let _ := chartedSpace hf hregt
  intro Ψ hsource hheight hband
  have hxSource (x : {x : M // f x = b}) : (x, t) ∈ Ψ.source :=
    hsource ⟨mem_univ x, by simpa only [mem_closedBall_zero_iff, Real.norm_eq_abs] using ht.le⟩
  have hyTarget (y : {x : M // f x = b + t}) : (y : M) ∈ Ψ.target := by
    apply hband
    change dist (f y) b < ε
    simpa only [y.property, Real.dist_eq, add_sub_cancel_left] using ht
  have hyTime (y : {x : M // f x = b + t}) : (Ψ.symm (y : M)).2 = t := by
    have hh := hheight (Ψ.symm (y : M)) (Ψ.map_target' (hyTarget y))
    have heq : Ψ (Ψ.symm (y : M)) = (y : M) := Ψ.right_inv' (hyTarget y)
    rw [heq, y.property] at hh
    linarith
  let up : {x : M // f x = b} → {x : M // f x = b + t} :=
    fun x => ⟨Ψ (x, t), hheight (x, t) (hxSource x)⟩
  let down : {x : M // f x = b + t} → {x : M // f x = b} :=
    fun y => (Ψ.symm (y : M)).1
  have hleft (x : {x : M // f x = b}) : down (up x) = x :=
    congrArg Prod.fst (Ψ.left_inv' (hxSource x))
  have hright (y : {x : M // f x = b + t}) : up (down y) = y := by
    apply Subtype.ext
    change Ψ ((Ψ.symm (y : M)).1, t) = (y : M)
    have hpair : ((Ψ.symm (y : M)).1, t) = Ψ.symm (y : M) :=
      Prod.ext rfl (hyTime y).symm
    rw [hpair]
    exact Ψ.right_inv' (hyTarget y)
  have hup : ContMDiff 𝓘(ℝ, Model E) 𝓘(ℝ, Model E) ∞ up := by
    apply (contMDiff_iff_inclusion hf hregt 𝓘(ℝ, Model E) up).mpr
    have hpair : ContMDiff 𝓘(ℝ, Model E) (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) ∞
        (fun x : {x : M // f x = b} => (x, t)) := contMDiff_id.prodMk contMDiff_const
    exact Ψ.contMDiffOn_toFun.comp_contMDiff hpair hxSource
  have hdown : ContMDiff 𝓘(ℝ, Model E) 𝓘(ℝ, Model E) ∞ down := by
    have hback := Ψ.contMDiffOn_invFun.comp_contMDiff (contMDiff_inclusion hf hregt) hyTarget
    exact contMDiff_fst.comp hback
  let e : Diffeomorph 𝓘(ℝ, Model E) 𝓘(ℝ, Model E)
      {x : M // f x = b} {x : M // f x = b + t} ∞ := {
    toFun := up
    invFun := down
    left_inv := hleft
    right_inv := hright
    contMDiff_toFun := hup
    contMDiff_invFun := hdown }
  exact ⟨e, fun _ => rfl, fun _ => rfl⟩

variable [T2Space M] [CompactSpace M]

/-- All sufficiently close regular levels are smoothly identified in their original atlases. -/
theorem exists_nearby_level_diffeomorphs_of_nonempty [Nonempty {x : M // f x = b}] :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      ∀ hregt : ∀ x, f x = b + t → x ∉ ManifoldMorse.criticalPoints E f,
        letI := chartedSpace hf hreg
        letI := chartedSpace hf hregt
        Nonempty (Diffeomorph 𝓘(ℝ, Model E) 𝓘(ℝ, Model E)
          {x : M // f x = b} {x : M // f x = b + t} ∞) := by
  let _ := chartedSpace hf hreg
  obtain ⟨ε, hε, Ψ, hsource, -, hheight, hband⟩ := exists_heightCollar_with_band hf hreg
  refine ⟨ε, hε, ?_⟩
  intro t ht hregt
  let _ := chartedSpace hf hregt
  obtain ⟨e, -, -⟩ := exists_levelDiffeomorph_of_heightCollar hf hreg ε t ht hregt
    Ψ hsource hheight hband
  exact ⟨e⟩

/-- Nearby regular levels are diffeomorphic, also when the original level is empty. -/
theorem exists_nearby_level_diffeomorphs :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      ∀ hregt : ∀ x, f x = b + t → x ∉ ManifoldMorse.criticalPoints E f,
        letI := chartedSpace hf hreg
        letI := chartedSpace hf hregt
        Nonempty (Diffeomorph 𝓘(ℝ, Model E) 𝓘(ℝ, Model E)
          {x : M // f x = b} {x : M // f x = b + t} ∞) := by
  classical
  by_cases hb : Nonempty {x : M // f x = b}
  · let _ := hb
    exact exists_nearby_level_diffeomorphs_of_nonempty hf hreg
  · let _ : IsEmpty {x : M // f x = b} := not_nonempty_iff.mp hb
    have hlevel : ∀ x, f x = b → x ∈ (∅ : Set M) :=
      fun x hx => (hb ⟨⟨x, hx⟩⟩).elim
    obtain ⟨ε, hε, hband⟩ := exists_heightBand_subset_open hf.continuous isOpen_empty hlevel
    refine ⟨ε, hε, ?_⟩
    intro t ht hregt
    let _ := chartedSpace hf hreg
    let _ := chartedSpace hf hregt
    let _ : IsEmpty {x : M // f x = b + t} := ⟨fun x => by
      apply hband
      change dist (f x) b < ε
      simpa only [x.property, Real.dist_eq, add_sub_cancel_left] using ht⟩
    exact ⟨Diffeomorph.empty⟩

end Wikipedia.SmoothSixDPoincare.RegularLevel
