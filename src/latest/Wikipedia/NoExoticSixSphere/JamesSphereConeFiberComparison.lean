import Wikipedia.NoExoticSixSphere.JamesSphereConeCylinderReflection

/-!
# Native homotopy excision for the actual finite James cone pair

Cylinder reflection gives injectivity of the original path-composition
fiber map through degree `3n - 3`. Together with the constructed
representatives, this proves bijectivity on the native homotopy groups.
Identifying this finite map with the full James quotient comparison is
a separate step; no additional EHP exactness is asserted here.
-/

noncomputable section

open Set Topology
open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.JamesSphere.SecondStageCone.FiberComparison

open RelativeFiberHomology

variable (n : ℕ) (a : StageAttachment.lower n 1)

theorem homotopic_reflect (d : ℕ) (hn : 2 ≤ n) (hdn : d + 1 ≤ 3 * n - 2)
    (p q : GenLoop (Fin d) (Fiber (StageAttachment.lower n 1) a)
      (HomotopyFiber.basepoint (subtypeInclusion (StageAttachment.lower n 1)) a))
    (h : GenLoop.Homotopic (HigherHomotopy.genLoopMap (map n a) (map_basepoint n a) p)
      (HigherHomotopy.genLoopMap (map n a) (map_basepoint n a) q)) :
    GenLoop.Homotopic p q := by
  obtain ⟨R⟩ := h
  let U := StageAttachment.lower n 1
  let V := Set.range (cone n)
  let b := conePoint n a
  let f := RelativeFiberCylinder.cylinder U a p.val
  let g := RelativeFiberCylinder.cylinder U a q.val
  let H : ((base n).comp f).Homotopy ((base n).comp g) := {
    toFun z := (R (z.1, z.2.2)).val.2 z.2.1
    continuous_toFun := continuous_eval.comp
      ((continuous_snd.comp (continuous_subtype_val.comp
        (R.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))).prodMk
          (continuous_fst.comp continuous_snd))
    map_zero_left z := congrArg (fun w : Fiber V b ↦ w.val.2 z.1) (R.map_zero_left z.2)
    map_one_left z := congrArg (fun w : Fiber V b ↦ w.val.2 z.1) (R.map_one_left z.2) }
  have h₀ : ∀ s z, H (s, (0, z)) ∈ Set.range (cone n) :=
    fun s z ↦ (R (s, z)).property.1 ▸ (R (s, z)).val.1.property
  have h₁ : ∀ s z, H (s, (1, z)) = base n a.val := fun s z ↦ (R (s, z)).property.2
  have hside : ∀ s t z, z ∈ Cube.boundary (Fin d) → H (s, (t, z)) = base n a.val := by
    intro s t z hz
    change (R (s, z)).val.2 t = base n a.val
    rw [R.eq_fst s hz]
    change base n ((p.val z).val.2 t) = base n a.val
    rw [p.property z hz]
    rfl
  obtain ⟨G, hG₀, hG₁, hGs⟩ := exists_cylinder_reflection n d hn hdn a f g H h₀ h₁ hside
  have hf₀ : ∀ z, f (0, z) ∈ U :=
    fun z ↦ (p.val z).property.1 ▸ (p.val z).val.1.property
  have hg₀ : ∀ z, g (0, z) ∈ U :=
    fun z ↦ (q.val z).property.1 ▸ (q.val z).val.1.property
  have hf₁ : ∀ z, f (1, z) = a.val := fun z ↦ (p.val z).property.2
  have hg₁ : ∀ z, g (1, z) = a.val := fun z ↦ (q.val z).property.2
  have hfside : ∀ t z, z ∈ Cube.boundary (Fin d) → f (t, z) = a.val := by
    intro t z hz
    change (p.val z).val.2 t = a.val
    rw [p.property z hz]
    rfl
  let L : (RelativeFiberCylinder.lift U a f hf₀ hf₁).HomotopyRel
      (RelativeFiberCylinder.lift U a g hg₀ hg₁) (Cube.boundary (Fin d)) := {
    toHomotopy := RelativeFiberCylinder.liftHomotopy U a f g hf₀ hf₁ hg₀ hg₁ G hG₀ hG₁
    prop' s z hz := RelativeFiberCylinder.liftHomotopy_fixed U a f g hf₀ hf₁ hg₀ hg₁
      G hG₀ hG₁ s z (fun t ↦ (hGs s t z hz).trans (hfside t z hz).symm) }
  have hp : RelativeFiberCylinder.lift U a f hf₀ hf₁ = p.val :=
    RelativeFiberCylinder.lift_cylinder U a p.val
  have hq : RelativeFiberCylinder.lift U a g hg₀ hg₁ = q.val :=
    RelativeFiberCylinder.lift_cylinder U a q.val
  rw [hp, hq] at L
  exact ⟨L⟩

theorem map_injective (d : ℕ) (hn : 2 ≤ n) (hdn : d ≤ 3 * n - 3) :
    Function.Injective (HigherHomotopy.map (N := Fin d) (map n a) (map_basepoint n a)) := by
  intro c e
  refine Quotient.inductionOn₂ c e ?_
  intro p q he
  apply Quotient.sound
  apply homotopic_reflect n a d hn (by omega) p q
  exact Quotient.exact he

theorem map_bijective (d : ℕ) (hn : 2 ≤ n) (hdn : d ≤ 3 * n - 3) :
    Function.Bijective (HigherHomotopy.map (N := Fin d) (map n a) (map_basepoint n a)) :=
  ⟨map_injective n a d hn hdn, map_surjective n a d hn (by omega)⟩

end NoExoticSixSphere.JamesSphere.SecondStageCone.FiberComparison
