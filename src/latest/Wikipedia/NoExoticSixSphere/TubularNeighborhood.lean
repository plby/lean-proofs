import Wikipedia.NoExoticSixSphere.CompactNormalNeighborhood

/-!
# A smooth tubular neighborhood for a compact Euclidean embedding

The normal-displacement map restricts to a diffeomorphism between an open
neighborhood of the zero section and an open neighborhood of the embedded
manifold. Nonemptiness is needed only to package a total inverse function on
the ambient space in `PartialDiffeomorph`.
-/

open scoped Manifold ContDiff Topology Bundle
open Bundle Filter Set

namespace NoExoticSixSphere.EuclideanEmbedding

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  (e : EuclideanEmbedding n M) [Nonempty M]

local instance normalBundle_nonempty : Nonempty e.NormalBundle :=
  ⟨zeroSection e.NormalModel e.NormalSpace (Classical.choice ‹Nonempty M›)⟩

/-- The partial equivalence determined by an injective normal neighborhood. -/
noncomputable def normalNeighborhoodEquiv {U : Set e.NormalBundle}
    (hinj : InjOn e.normalDisplacement U) :
    PartialEquiv e.NormalBundle (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
  hinj.toPartialEquiv e.normalDisplacement U

/-- The inverse on an injective neighborhood agrees locally with each smooth local inverse. -/
theorem contMDiffAt_normalNeighborhood_inverse {U : Set e.NormalBundle} (hU : IsOpen U)
    (hinj : InjOn e.normalDisplacement U)
    (hloc : IsLocalDiffeomorphOn ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
      e.normalDisplacement U)
    {y : EuclideanSpace ℝ (Fin e.ambientDimension)}
    (hy : y ∈ (e.normalNeighborhoodEquiv hinj).target) :
    ContMDiffAt (𝓡 e.ambientDimension) ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) ∞
      (e.normalNeighborhoodEquiv hinj).symm y := by
  let p := e.normalNeighborhoodEquiv hinj
  have hx : p.symm y ∈ U := p.map_target hy
  obtain ⟨φ, hφx, heq⟩ := hloc ⟨p.symm y, hx⟩
  have hφxy : φ (p.symm y) = y := (heq hφx).symm.trans (p.right_inv hy)
  have hφy : y ∈ φ.target := hφxy ▸ φ.map_source' hφx
  have hφyx : φ.symm y = p.symm y := by
    calc
      φ.symm y = φ.symm (φ (p.symm y)) := congrArg φ.symm hφxy.symm
      _ = p.symm y := φ.left_inv' hφx
  have hg : ContMDiffAt (𝓡 e.ambientDimension) ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) ∞
      φ.symm y := φ.contMDiffOn_invFun.contMDiffAt (φ.open_target.mem_nhds hφy)
  have hNU : U ∈ 𝓝 (φ.symm y) := by
    rw [hφyx]
    exact hU.mem_nhds hx
  have hfg : p.symm =ᶠ[𝓝 y] φ.symm := by
    filter_upwards [φ.open_target.mem_nhds hφy, hg.continuousAt hNU] with z hz hzU
    have hfz : e.normalDisplacement (φ.symm z) = z :=
      (heq (φ.map_target' hz)).trans (φ.right_inv' hz)
    exact (congrArg p.symm hfz.symm).trans (p.left_inv hzU)
  exact hfg.contMDiffAt_iff.mpr hg

/-- The actual smooth partial diffeomorphism defined by normal displacement. -/
noncomputable def normalNeighborhoodPartialDiffeomorph {U : Set e.NormalBundle}
    (hU : IsOpen U) (hinj : InjOn e.normalDisplacement U)
    (hloc : IsLocalDiffeomorphOn ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
      e.normalDisplacement U) :
    PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension)
      e.NormalBundle (EuclideanSpace ℝ (Fin e.ambientDimension)) ∞ where
  toPartialEquiv := e.normalNeighborhoodEquiv hinj
  open_source := hU
  open_target := e.isOpen_normalNeighborhood_image hU hloc
  contMDiffOn_toFun := e.contMDiff_normalDisplacement.contMDiffOn
  contMDiffOn_invFun := fun _ hy ↦
    (e.contMDiffAt_normalNeighborhood_inverse hU hinj hloc hy).contMDiffWithinAt

/-- A compact nonempty Euclidean embedding has a genuine smooth tubular neighborhood. -/
theorem exists_tubularNeighborhood [CompactSpace M] :
    ∃ Φ : PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension)
        e.NormalBundle (EuclideanSpace ℝ (Fin e.ambientDimension)) ∞,
      range (zeroSection e.NormalModel e.NormalSpace) ⊆ Φ.source ∧
      (Φ : e.NormalBundle → EuclideanSpace ℝ (Fin e.ambientDimension)) = e.normalDisplacement ∧
      range e.toFun ⊆ Φ.target := by
  obtain ⟨U, hU, hzero, hinj, hloc⟩ := e.exists_injective_normalNeighborhood
  let Φ := e.normalNeighborhoodPartialDiffeomorph hU hinj hloc
  refine ⟨Φ, hzero, rfl, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx : zeroSection e.NormalModel e.NormalSpace x ∈ Φ.source := hzero ⟨x, rfl⟩
  have hy := Φ.map_source' hx
  simpa only [Φ, normalNeighborhoodPartialDiffeomorph, normalNeighborhoodEquiv,
    Set.InjOn.toPartialEquiv, Set.BijOn.toPartialEquiv, e.normalDisplacement_zero] using hy

end NoExoticSixSphere.EuclideanEmbedding
