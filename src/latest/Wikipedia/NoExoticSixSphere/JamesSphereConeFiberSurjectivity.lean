import Wikipedia.NoExoticSixSphere.JamesSphereCubicalCompression
import Wikipedia.NoExoticSixSphere.RelativeFiberCylinder
import Wikipedia.NoExoticSixSphere.CubeCollar
import Wikipedia.NoExoticSixSphere.InducedHomotopyMap

/-!
# Surjectivity on the actual fibers of the two James cone pairs

The pair map is the original inclusion of the second James stage into
its cone model, with the original lower subspace mapping into the cone
disk. Its fiber map postcomposes the actual paths. Cubical compression
gives representatives for every native target homotopy class through
degree `3n - 2`, with no homotopy-excision hypothesis.
-/

noncomputable section

open Set Topology
open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.JamesSphere.SecondStageCone.FiberComparison

open RelativeFiberHomology

variable (n : ℕ) (a : StageAttachment.lower n 1)

def conePoint : Set.range (cone n) := ⟨base n a.val, (base_mem_cone_iff n a.val).mpr a.property⟩

def map : C(Fiber (StageAttachment.lower n 1) a,
    Fiber (Set.range (cone n)) (conePoint n a)) :=
  RelativeFiberMap.map (base n) (fun x hx ↦ (base_mem_cone_iff n x).mpr hx)
    a (conePoint n a) rfl

theorem map_basepoint :
    map n a (HomotopyFiber.basepoint (subtypeInclusion (StageAttachment.lower n 1)) a) =
      HomotopyFiber.basepoint (subtypeInclusion (Set.range (cone n))) (conePoint n a) := rfl

theorem exists_representative (d : ℕ) (hn : 2 ≤ n) (hdn : d ≤ 3 * n - 2)
    (p : GenLoop (Fin d) (Fiber (Set.range (cone n)) (conePoint n a))
      (HomotopyFiber.basepoint (subtypeInclusion (Set.range (cone n))) (conePoint n a))) :
    ∃ q : GenLoop (Fin d) (Fiber (StageAttachment.lower n 1) a)
      (HomotopyFiber.basepoint (subtypeInclusion (StageAttachment.lower n 1)) a),
      GenLoop.Homotopic p (HigherHomotopy.genLoopMap (map n a) (map_basepoint n a) q) := by
  let U := StageAttachment.lower n 1
  let V := Set.range (cone n)
  let b := conePoint n a
  let f := RelativeFiberCylinder.cylinder V b p.val
  have hf₀ : ∀ z, f (0, z) ∈ V :=
    fun z ↦ (p.val z).property.1 ▸ (p.val z).val.1.property
  have hf₁ : ∀ z, f (1, z) = b.val := fun z ↦ (p.val z).property.2
  have hfside : ∀ t z, z ∈ Cube.boundary (Fin d) → f (t, z) = b.val := by
    intro t z hz
    change (p.val z).val.2 t = b.val
    rw [p.property z hz]
    rfl
  have hbA : b.val ∈ Set.range (base n) := Set.mem_range_self a.val
  obtain ⟨c, F, hc₀, hF₀, _, _, hFfix⟩ :=
    exists_cubical_compression n d hn hdn f (Cube.boundary (Fin d))
      (CubeCollar.isClosed_boundary (Fin d))
      (fun t z hz ↦ hfside t z hz ▸ hbA) (fun z ↦ hf₁ z ▸ hbA) hf₀
  have hF₁ : ∀ s z, F (s, (1, z)) = b.val := by
    intro s z
    exact (hFfix s (1, z) (hf₁ z ▸ hbA) (hf₁ z ▸ b.property) (Or.inl rfl)).trans (hf₁ z)
  have hFcside : ∀ s t z, z ∈ Cube.boundary (Fin d) → F (s, (t, z)) = f (t, z) := by
    intro s t z hz
    exact hFfix s (t, z) (hfside t z hz ▸ hbA) (hfside t z hz ▸ b.property) (Or.inr hz)
  have hc₁ : ∀ z, c (1, z) = a.val := by
    intro z
    apply (base_isClosedEmbedding n).injective
    have he := hF₁ 1 z
    rwa [F.apply_one] at he
  have hcside : ∀ t z, z ∈ Cube.boundary (Fin d) → c (t, z) = a.val := by
    intro t z hz
    apply (base_isClosedEmbedding n).injective
    have he := (hFcside 1 t z hz).trans (hfside t z hz)
    rwa [F.apply_one] at he
  let q : GenLoop (Fin d) (Fiber U a) (HomotopyFiber.basepoint (subtypeInclusion U) a) :=
    ⟨RelativeFiberCylinder.lift U a c hc₀ hc₁,
      fun z hz ↦ RelativeFiberCylinder.lift_eq_basepoint U a c hc₀ hc₁ z
        (fun t ↦ hcside t z hz)⟩
  have hg₀ : ∀ z, ((base n).comp c) (0, z) ∈ V :=
    fun z ↦ (base_mem_cone_iff n _).mpr (hc₀ z)
  have hg₁ : ∀ z, ((base n).comp c) (1, z) = b.val :=
    fun z ↦ congrArg (base n) (hc₁ z)
  let R : (RelativeFiberCylinder.lift V b f hf₀ hf₁).HomotopyRel
      (RelativeFiberCylinder.lift V b ((base n).comp c) hg₀ hg₁) (Cube.boundary (Fin d)) := {
    toHomotopy := RelativeFiberCylinder.liftHomotopy V b f ((base n).comp c)
      hf₀ hf₁ hg₀ hg₁ F hF₀ hF₁
    prop' s z hz := RelativeFiberCylinder.liftHomotopy_fixed V b f ((base n).comp c)
      hf₀ hf₁ hg₀ hg₁ F hF₀ hF₁ s z (fun t ↦ hFcside s t z hz) }
  have hstart : RelativeFiberCylinder.lift V b f hf₀ hf₁ = p.val :=
    RelativeFiberCylinder.lift_cylinder V b p.val
  have hend : RelativeFiberCylinder.lift V b ((base n).comp c) hg₀ hg₁ =
      (map n a).comp q.val := rfl
  rw [hstart, hend] at R
  exact ⟨q, ⟨R⟩⟩

theorem map_surjective (d : ℕ) (hn : 2 ≤ n) (hdn : d ≤ 3 * n - 2) :
    Function.Surjective (HigherHomotopy.map (N := Fin d) (map n a) (map_basepoint n a)) := by
  intro c
  refine Quotient.inductionOn c ?_
  intro p
  obtain ⟨q, hq⟩ := exists_representative n a d hn hdn p
  refine ⟨Quotient.mk _ q, ?_⟩
  change Quotient.mk _ (HigherHomotopy.genLoopMap (map n a) (map_basepoint n a) q) =
    Quotient.mk _ p
  exact Quotient.sound (GenLoop.Homotopic.symm hq)

end NoExoticSixSphere.JamesSphere.SecondStageCone.FiberComparison
