import Wikipedia.NoExoticSixSphere.CompactSphereCoincidenceTrace
import Wikipedia.NoExoticSixSphere.TransverseSphereChartDifference
import Wikipedia.NoExoticSixSphere.ImplicitCurveCoordinates
import Wikipedia.NoExoticSixSphere.PartialHomeomorphSubsets
import Wikipedia.NoExoticSixSphere.LocalInverse

/-!
# Actual time coordinates near a transverse point of the compact trace

The coincidence equation together with unchanged time has invertible
derivative. Restrict to the interior of the time window and pair region,
then restrict these genuine inverse-function coordinates to the actual
zero set. The resulting chart is exactly the original time projection.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CompactPairTrace

open GLOrthonormalization IntersectionTrace

def zeroLine (F : Type*) [Zero F] : Set (F × ℝ) := {p | p.1 = 0}

def zeroLineTimeHomeomorph (F : Type*) [TopologicalSpace F] [Zero F] : zeroLine F ≃ₜ ℝ where
  toFun p := p.val.2
  invFun t := ⟨(0, t), rfl⟩
  left_inv p := Subtype.ext (Prod.ext p.property.symm rfl)
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.snd
  continuous_invFun := (continuous_const.prodMk continuous_id).subtype_mk _

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] (f g : ℝ → Sphere 3 → M) (K : Set (Sphere 3 × Sphere 3))
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))

include hf hg in
theorem exists_ambient_time_coordinates_of_charts (a : ℝ × (Sphere 3 × Sphere 3))
    (s z : SphereChart) (c : ManifoldChart M)
    (hx : a.2.1 ∈ s.source) (hy : a.2.2 ∈ z.source) (hc : f a.1 a.2.1 ∈ c.source)
    (hxy : f a.1 a.2.1 = g a.1 a.2.2)
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) (f a.1) a.2.1).coprod
      (mfderiv (𝓡 3) (𝓡 6) (g a.1) a.2.2))) :
    ∃ T : OpenPartialHomeomorph (ℝ × (Sphere 3 × Sphere 3)) (Vector 6 × ℝ),
      a ∈ T.source ∧ (∀ b, (T b).2 = b.1) ∧
      ∀ b ∈ T.source, (T b).1 = 0 ↔ f b.1 b.2.1 = g b.1 b.2.2 := by
  have hcy : g a.1 a.2.2 ∈ c.source := hxy ▸ hc
  have hx' : s.symm (s a.2.1) = a.2.1 := s.left_inv hx
  have hy' : z.symm (z a.2.2) = a.2.2 := z.left_inv hy
  let P := Vector 3 × Vector 3
  let Φ : P × ℝ → Vector 6 := fun q ↦ coordinateDifference f g s z c (q.2, q.1)
  let U : Set (P × ℝ) := Prod.swap ⁻¹' fullCoordinateDomain f g s z c
  have hswap : ContDiff ℝ ∞ (Prod.swap : P × ℝ → ℝ × P) :=
    contDiff_snd.prodMk contDiff_fst
  have hU : IsOpen U := (isOpen_fullCoordinateDomain f g hf hg s z c).preimage
    hswap.continuous
  have hΦ : ContDiffOn ℝ ∞ Φ U :=
    (contDiffOn_coordinateDifference_full f g hf hg s z c).comp hswap.contDiffOn
      (fun _ hq ↦ hq)
  have hbase : ((s a.2.1, z a.2.2), a.1) ∈ U := by
    change (s a.2.1 ∈ s.target ∧ z a.2.2 ∈ z.target) ∧
      (f a.1 (s.symm (s a.2.1)) ∈ c.source ∧
        g a.1 (z.symm (z a.2.2)) ∈ c.source)
    rw [hx', hy']
    exact ⟨⟨s.map_source hx, z.map_source hy⟩, hc, hcy⟩
  have hbij : Bijective (fderiv ℝ (fun q : P ↦ Φ (q, a.1))
      (s a.2.1, z a.2.2)) :=
    bijective_fderiv_spatial_difference f g hf hg a.1 a.2.1 a.2.2
      s z c hx hy hc hxy ht
  obtain ⟨Ψ, hΨbase, hΨU, hΨform⟩ := ImplicitCurve.exists_parameter_coordinates Φ U hU
    (s a.2.1, z a.2.2) a.1 hbase hΦ hbij
  let T₀ := (Homeomorph.prodComm ℝ (Sphere 3 × Sphere 3)).toOpenPartialHomeomorph.trans
    ((s.toOpenPartialHomeomorph.prod z.toOpenPartialHomeomorph).prod
      (OpenPartialHomeomorph.refl ℝ))
  let Tbase := T₀.trans Ψ.toOpenPartialHomeomorph
  have hTform (b : ℝ × (Sphere 3 × Sphere 3)) : Tbase b =
      (coordinateDifference f g s z c (b.1, (s b.2.1, z b.2.2)), b.1) := hΨform (T₀ b)
  refine ⟨Tbase, ⟨⟨mem_univ _, ⟨hx, hy⟩, mem_univ _⟩, hΨbase⟩,
    fun b ↦ congrArg Prod.snd (hTform b), ?_⟩
  intro b hb
  have hbU : (b.1, (s b.2.1, z b.2.2)) ∈ fullCoordinateDomain f g s z c := hΨU hb.2
  have hbx : b.2.1 ∈ s.source := hb.1.2.1.1
  have hby : b.2.2 ∈ z.source := hb.1.2.1.2
  have hbs : s.symm (s b.2.1) = b.2.1 := s.left_inv hbx
  have hbz : z.symm (z b.2.2) = b.2.2 := z.left_inv hby
  have hzero := coordinateDifference_zero_iff_full f g s z c
    (b.1, (s b.2.1, z b.2.2)) hbU
  rw [hbs, hbz] at hzero
  rw [hTform]
  exact hzero

include hf hg in
theorem exists_ambient_time_coordinates (a : ℝ × (Sphere 3 × Sphere 3))
    (hxy : f a.1 a.2.1 = g a.1 a.2.2)
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) (f a.1) a.2.1).coprod
      (mfderiv (𝓡 3) (𝓡 6) (g a.1) a.2.2))) :
    ∃ T : OpenPartialHomeomorph (ℝ × (Sphere 3 × Sphere 3)) (Vector 6 × ℝ),
      a ∈ T.source ∧ (∀ b, (T b).2 = b.1) ∧
      ∀ b ∈ T.source, (T b).1 = 0 ↔ f b.1 b.2.1 = g b.1 b.2.2 := by
  let s : SphereChart := modelChartPartialDiffeomorph (I := 𝓡 3) a.2.1
  let z : SphereChart := modelChartPartialDiffeomorph (I := 𝓡 3) a.2.2
  let c : ManifoldChart M := modelChartPartialDiffeomorph (I := 𝓡 6) (f a.1 a.2.1)
  exact exists_ambient_time_coordinates_of_charts f g hf hg a s z c
    (mem_extChartAt_source _) (mem_extChartAt_source _) (mem_extChartAt_source _) hxy ht

include hf hg in
theorem exists_time_chart (a : space f g K)
    (ha : a.val.1 ∈ Ioo (-1 : ℝ) 1) (hK : a.val.2 ∈ interior K)
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) (f a.val.1) a.val.2.1).coprod
      (mfderiv (𝓡 3) (𝓡 6) (g a.val.1) a.val.2.2))) :
    ∃ d : OpenPartialHomeomorph (space f g K) ℝ, a ∈ d.source ∧
      ∀ q ∈ d.source, d q = time f g K q := by
  obtain ⟨Tbase, haBase, htime, hzero⟩ :=
    exists_ambient_time_coordinates f g hf hg a.val a.property.2 ht
  let W : Set (ℝ × (Sphere 3 × Sphere 3)) :=
    {p | p.1 ∈ Ioo (-1 : ℝ) 1 ∧ p.2 ∈ interior K}
  have hW : IsOpen W := (isOpen_Ioo.preimage continuous_fst).inter
    (isOpen_interior.preimage continuous_snd)
  let T := Tbase.restrOpen W hW
  have hImage : T.IsImage (space f g K) (zeroLine (Vector 6)) := by
    intro b hb
    have hbW : b ∈ W := hb.2
    change (Tbase b).1 = 0 ↔ (b.1 ∈ Icc (-1 : ℝ) 1 ∧ b.2 ∈ K) ∧
      f b.1 b.2.1 = g b.1 b.2.2
    rw [hzero b hb.1]
    exact ⟨fun h ↦ ⟨⟨Ioo_subset_Icc_self hbW.1, interior_subset hbW.2⟩, h⟩, fun h ↦ h.2⟩
  let a₀ : zeroLine (Vector 6) := ⟨(0, a.val.1), rfl⟩
  let E := SubsetCoordinates.coordinates T hImage a a₀
  let d := E.trans (zeroLineTimeHomeomorph (Vector 6)).toOpenPartialHomeomorph
  have haT : a.val ∈ T.source := ⟨haBase, ha, hK⟩
  refine ⟨d, ⟨haT, mem_univ _⟩, ?_⟩
  intro q hq
  change (E q).val.2 = q.val.1
  rw [SubsetCoordinates.coordinates_val T hImage a a₀ hq.1]
  exact htime q.val

end NoExoticSixSphere.CompactPairTrace
