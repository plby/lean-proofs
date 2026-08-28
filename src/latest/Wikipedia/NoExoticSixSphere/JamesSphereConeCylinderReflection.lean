import Wikipedia.NoExoticSixSphere.JamesSphereConeFiberSurjectivity
import Wikipedia.NoExoticSixSphere.CubeFirstCoordinate

/-!
# Reflecting relative cylinder homotopies into the James stage

Apply compression with the original homotopy parameter as an extra
cube coordinate. Its endpoint faces remain in the James stage, so
their tracks lift through the original embedding. Joining those two
tracks to the compressed cylinder yields a homotopy between the exact
original endpoints, preserving the lower subspace and based faces.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace NoExoticSixSphere.JamesSphere.SecondStageCone

open CubicalCellSmoothing

def liftBaseFamily (n : ℕ) {Z : Type} [TopologicalSpace Z]
    (f : C(Z, Space n)) (hf : ∀ z, f z ∈ Set.range (base n)) : C(Z, SecondStage.Space n) :=
  ((base_isClosedEmbedding n).isEmbedding.toHomeomorph.symm :
    C(Set.range (base n), SecondStage.Space n)).comp
      ⟨fun z ↦ ⟨f z, hf z⟩, f.continuous.subtype_mk _⟩

theorem base_liftBaseFamily (n : ℕ) {Z : Type} [TopologicalSpace Z]
    (f : C(Z, Space n)) (hf : ∀ z, f z ∈ Set.range (base n)) (z : Z) :
    base n (liftBaseFamily n f hf z) = f z :=
  congrArg Subtype.val ((base_isClosedEmbedding n).isEmbedding.toHomeomorph.apply_symm_apply
    ⟨f z, hf z⟩)

theorem exists_cylinder_reflection (n d : ℕ) (hn : 2 ≤ n) (hdn : d + 1 ≤ 3 * n - 2)
    (a : StageAttachment.lower n 1) (f g : C(I × Parameters d, SecondStage.Space n))
    (H : ((base n).comp f).Homotopy ((base n).comp g))
    (h₀ : ∀ s z, H (s, (0, z)) ∈ Set.range (cone n))
    (h₁ : ∀ s z, H (s, (1, z)) = base n a.val)
    (hside : ∀ s t z, z ∈ Cube.boundary (Fin d) → H (s, (t, z)) = base n a.val) :
    ∃ G : f.Homotopy g,
      (∀ s z, G (s, (0, z)) ∈ StageAttachment.lower n 1) ∧
      (∀ s z, G (s, (1, z)) = a.val) ∧
      ∀ s t z, z ∈ Cube.boundary (Fin d) → G (s, (t, z)) = a.val := by
  let k : C(I × Parameters (d + 1), Space n) := ⟨fun z ↦
    H ((CubeFirstCoordinate.split d z.2).1, (z.1, (CubeFirstCoordinate.split d z.2).2)),
    H.continuous.comp
      ((continuous_fst.comp ((CubeFirstCoordinate.split d).continuous.comp continuous_snd)).prodMk
        (continuous_fst.prodMk
          (continuous_snd.comp ((CubeFirstCoordinate.split d).continuous.comp continuous_snd))))⟩
  have hbA : base n a.val ∈ Set.range (base n) := Set.mem_range_self a.val
  have hbC : base n a.val ∈ Set.range (cone n) := (base_mem_cone_iff n a.val).mpr a.property
  have hkside : ∀ t z, z ∈ Cube.boundary (Fin (d + 1)) → k (t, z) ∈ Set.range (base n) := by
    intro t z hz
    rcases (CubeFirstCoordinate.boundary_split_iff d z).mp hz with he | he | he
    · change H ((CubeFirstCoordinate.split d z).1,
        (t, (CubeFirstCoordinate.split d z).2)) ∈ Set.range (base n)
      rw [he, H.apply_zero]
      exact Set.mem_range_self _
    · change H ((CubeFirstCoordinate.split d z).1,
        (t, (CubeFirstCoordinate.split d z).2)) ∈ Set.range (base n)
      rw [he, H.apply_one]
      exact Set.mem_range_self _
    · exact hside _ t _ he ▸ hbA
  obtain ⟨c, L, hc₀, hL₀, _, hLside, hLfix⟩ :=
    exists_cubical_compression n (d + 1) hn hdn k (Cube.boundary (Fin (d + 1)))
      (CubeCollar.isClosed_boundary (Fin (d + 1))) hkside
      (fun z ↦ h₁ _ _ ▸ hbA) (fun z ↦ h₀ _ _)
  have hL₁ : ∀ s z, L (s, (1, z)) = base n a.val := by
    intro s z
    have hk : k (1, z) = base n a.val := h₁ _ _
    exact (hLfix s (1, z) (hk ▸ hbA) (hk ▸ hbC) (Or.inl rfl)).trans hk
  have hLbased : ∀ s t r z, z ∈ Cube.boundary (Fin d) →
      L (s, (t, CubeFirstCoordinate.join d (r, z))) = base n a.val := by
    intro s t r z hz
    have hk : k (t, CubeFirstCoordinate.join d (r, z)) = base n a.val := hside r t z hz
    have hz' := (CubeFirstCoordinate.boundary_join_iff d (r, z)).mpr (Or.inr (Or.inr hz))
    exact (hLfix s _ (hk ▸ hbA) (hk ▸ hbC) (Or.inr hz')).trans hk
  let track (e : I) : C(I × (I × Parameters d), Space n) :=
    L.toContinuousMap.comp ⟨fun z ↦ (z.1, (z.2.1, CubeFirstCoordinate.join d (e, z.2.2))),
      continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
        ((CubeFirstCoordinate.join d).continuous.comp
          (continuous_const.prodMk (continuous_snd.comp continuous_snd))))⟩
  have htrack (e : I) (he : e = 0 ∨ e = 1) : ∀ z, track e z ∈ Set.range (base n) := by
    rintro ⟨s, t, z⟩
    apply hLside s t
    apply (CubeFirstCoordinate.boundary_join_iff d (e, z)).mpr
    exact he.elim Or.inl (fun h ↦ Or.inr (Or.inl h))
  let A := liftBaseFamily n (track 0) (htrack 0 (Or.inl rfl))
  let D := liftBaseFamily n (track 1) (htrack 1 (Or.inr rfl))
  have hAbase (z) : base n (A z) = track 0 z := base_liftBaseFamily n _ _ z
  have hDbase (z) : base n (D z) = track 1 z := base_liftBaseFamily n _ _ z
  let c₀ : C(I × Parameters d, SecondStage.Space n) :=
    c.comp ⟨fun z ↦ (z.1, CubeFirstCoordinate.join d (0, z.2)),
      continuous_fst.prodMk ((CubeFirstCoordinate.join d).continuous.comp
        (continuous_const.prodMk continuous_snd))⟩
  let c₁ : C(I × Parameters d, SecondStage.Space n) :=
    c.comp ⟨fun z ↦ (z.1, CubeFirstCoordinate.join d (1, z.2)),
      continuous_fst.prodMk ((CubeFirstCoordinate.join d).continuous.comp
        (continuous_const.prodMk continuous_snd))⟩
  let A' : f.Homotopy c₀ := {
    toContinuousMap := A
    map_zero_left z := by
      apply (base_isClosedEmbedding n).injective
      change base n (A (0, z)) = base n (f z)
      rw [hAbase]
      change L (0, (z.1, CubeFirstCoordinate.join d (0, z.2))) = base n (f z)
      rw [L.apply_zero]
      exact H.apply_zero z
    map_one_left z := by
      apply (base_isClosedEmbedding n).injective
      change base n (A (1, z)) = base n (c₀ z)
      rw [hAbase]
      exact L.apply_one (z.1, CubeFirstCoordinate.join d (0, z.2)) }
  let D' : g.Homotopy c₁ := {
    toContinuousMap := D
    map_zero_left z := by
      apply (base_isClosedEmbedding n).injective
      change base n (D (0, z)) = base n (g z)
      rw [hDbase]
      change L (0, (z.1, CubeFirstCoordinate.join d (1, z.2))) = base n (g z)
      rw [L.apply_zero]
      exact H.apply_one z
    map_one_left z := by
      apply (base_isClosedEmbedding n).injective
      change base n (D (1, z)) = base n (c₁ z)
      rw [hDbase]
      exact L.apply_one (z.1, CubeFirstCoordinate.join d (1, z.2)) }
  let B : c₀.Homotopy c₁ := {
    toFun z := c (z.2.1, CubeFirstCoordinate.join d (z.1, z.2.2))
    continuous_toFun := c.continuous.comp ((continuous_fst.comp continuous_snd).prodMk
      ((CubeFirstCoordinate.join d).continuous.comp
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))
    map_zero_left _ := rfl
    map_one_left _ := rfl }
  have hA₀ : ∀ s z, A' (s, (0, z)) ∈ StageAttachment.lower n 1 := by
    intro s z
    apply (base_mem_cone_iff n _).mp
    change base n (A (s, (0, z))) ∈ Set.range (cone n)
    rw [hAbase]
    exact hL₀ s (CubeFirstCoordinate.join d (0, z))
  have hD₀ : ∀ s z, D' (s, (0, z)) ∈ StageAttachment.lower n 1 := by
    intro s z
    apply (base_mem_cone_iff n _).mp
    change base n (D (s, (0, z))) ∈ Set.range (cone n)
    rw [hDbase]
    exact hL₀ s (CubeFirstCoordinate.join d (1, z))
  have hA₁ : ∀ s z, A' (s, (1, z)) = a.val := by
    intro s z
    apply (base_isClosedEmbedding n).injective
    change base n (A (s, (1, z))) = base n a.val
    rw [hAbase]
    exact hL₁ s _
  have hD₁ : ∀ s z, D' (s, (1, z)) = a.val := by
    intro s z
    apply (base_isClosedEmbedding n).injective
    change base n (D (s, (1, z))) = base n a.val
    rw [hDbase]
    exact hL₁ s _
  have hAs : ∀ s t z, z ∈ Cube.boundary (Fin d) → A' (s, (t, z)) = a.val := by
    intro s t z hz
    apply (base_isClosedEmbedding n).injective
    change base n (A (s, (t, z))) = base n a.val
    rw [hAbase]
    exact hLbased s t 0 z hz
  have hDs : ∀ s t z, z ∈ Cube.boundary (Fin d) → D' (s, (t, z)) = a.val := by
    intro s t z hz
    apply (base_isClosedEmbedding n).injective
    change base n (D (s, (t, z))) = base n a.val
    rw [hDbase]
    exact hLbased s t 1 z hz
  have hB₁ : ∀ s z, B (s, (1, z)) = a.val := by
    intro s z
    apply (base_isClosedEmbedding n).injective
    have he := hL₁ 1 (CubeFirstCoordinate.join d (s, z))
    rwa [L.apply_one] at he
  have hBs : ∀ s t z, z ∈ Cube.boundary (Fin d) → B (s, (t, z)) = a.val := by
    intro s t z hz
    apply (base_isClosedEmbedding n).injective
    have he := hLbased 1 t s z hz
    rwa [L.apply_one] at he
  refine ⟨A'.trans (B.trans D'.symm), ?_, ?_, ?_⟩
  · intro s z
    apply trans_pointwise_property A' (B.trans D'.symm) (0, z)
      (fun y ↦ y ∈ StageAttachment.lower n 1) (fun r ↦ hA₀ r z) ?_ s
    intro r
    exact trans_pointwise_property B D'.symm (0, z)
      (fun y ↦ y ∈ StageAttachment.lower n 1)
      (fun t ↦ hc₀ (CubeFirstCoordinate.join d (t, z))) (fun t ↦ hD₀ _ z) r
  · intro s z
    apply trans_pointwise_property A' (B.trans D'.symm) (1, z)
      (fun y ↦ y = a.val) (fun r ↦ hA₁ r z) ?_ s
    intro r
    exact trans_pointwise_property B D'.symm (1, z)
      (fun y ↦ y = a.val) (fun t ↦ hB₁ t z) (fun t ↦ hD₁ _ z) r
  · intro s t z hz
    apply trans_pointwise_property A' (B.trans D'.symm) (t, z)
      (fun y ↦ y = a.val) (fun r ↦ hAs r t z hz) ?_ s
    intro r
    exact trans_pointwise_property B D'.symm (t, z)
      (fun y ↦ y = a.val) (fun v ↦ hBs v t z hz) (fun v ↦ hDs _ t z hz) r

end NoExoticSixSphere.JamesSphere.SecondStageCone
