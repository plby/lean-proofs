import Wikipedia.NoExoticSixSphere.CircleHomotopyParameter
import Wikipedia.NoExoticSixSphere.OrthogonalMinimumDeformation
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Reflecting relative homotopies into the minimum polygon locus

An interval homotopy is extended over `Circle × M`. Applying minimum deformation
there fixes the two endpoint fibers and every protected parameter. Restriction
along a semicircle then gives a homotopy entirely in the minimum locus.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalExponential OrthogonalVertexSpace

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] {n m : ℕ}

include I

theorem exists_minimum_homotopy_from_ambient (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (hsmall : ∀ J : OrthogonalComplexStructures.Space n, ∀ i : Fin (m + 1),
      (τ i.succ - τ i.castSucc) • (Real.pi • J.1) ∈ (logarithmChart n).target)
    (cap : ℝ) (hcap : (n : ℝ) * Real.pi ^ 2 < cap)
    (hcompact : IsCompact (energySublevel a b τ cap))
    (hshort : energySublevel a b τ cap ⊆ shortDomain a b m)
    (hd : finrank ℝ B + 3 < n)
    (f g : C(M, Space n m)) (S : Set M)
    (hf : ∀ x, f x ∈ minimumSet a b τ) (hg : ∀ x, g x ∈ minimumSet a b τ)
    (F : ContinuousMap.HomotopyRel f g S) (hF : ∀ t x, F (t, x) ∈ admissible a b m)
    (start : ℝ) (hstart : start < cap) (henergy : ∀ t x, energy a b τ (F (t, x)) ≤ start) :
    ∃ G : ContinuousMap.HomotopyRel f g S, ∀ t x, G (t, x) ∈ minimumSet a b τ := by
  let P := CircleHomotopyParameter.extend F.toContinuousMap
  have hP (z : Circle × M) : P z ∈ admissible a b m :=
    hF (CircleHomotopyParameter.height z.1) z.2
  have hPenergy (z : Circle × M) : energy a b τ (P z) ≤ start :=
    henergy (CircleHomotopyParameter.height z.1) z.2
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin 1) × B) + 2 < n := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin]
    omega
  obtain ⟨Q, hQ, T, _⟩ := exists_homotopy_into_minimum (I := (𝓡 1).prod I)
    (M := Circle × M) a b τ hτ hzero hone hanti hsmall cap hcap hcompact hshort hdim
    P hP start hstart hPenergy
  exact CircleHomotopyParameter.homotopy_in_subset_of_fixed_extension F
    (minimumSet a b τ) hf hg Q hQ (fun z hz ↦ (T.fst_eq_snd hz).symm)

noncomputable def minimumInclusion (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ) :
    C(minimumSet a b τ, Space n m) := ⟨Subtype.val, continuous_subtype_val⟩

theorem nonempty_minimumHomotopyRel_of_ambient (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (hsmall : ∀ J : OrthogonalComplexStructures.Space n, ∀ i : Fin (m + 1),
      (τ i.succ - τ i.castSucc) • (Real.pi • J.1) ∈ (logarithmChart n).target)
    (cap : ℝ) (hcap : (n : ℝ) * Real.pi ^ 2 < cap)
    (hcompact : IsCompact (energySublevel a b τ cap))
    (hshort : energySublevel a b τ cap ⊆ shortDomain a b m)
    (hd : finrank ℝ B + 3 < n)
    (f g : C(M, minimumSet a b τ)) (S : Set M)
    (F : ContinuousMap.HomotopyRel ((minimumInclusion a b τ).comp f)
      ((minimumInclusion a b τ).comp g) S)
    (hF : ∀ t x, F (t, x) ∈ admissible a b m)
    (start : ℝ) (hstart : start < cap) (henergy : ∀ t x, energy a b τ (F (t, x)) ≤ start) :
    Nonempty (ContinuousMap.HomotopyRel f g S) := by
  obtain ⟨G, hG⟩ := exists_minimum_homotopy_from_ambient (I := I)
    a b τ hτ hzero hone hanti hsmall cap hcap hcompact hshort hd
    ((minimumInclusion a b τ).comp f) ((minimumInclusion a b τ).comp g) S
    (fun x ↦ (f x).2) (fun x ↦ (g x).2) F hF start hstart henergy
  exact ⟨{
    toFun := fun z ↦ ⟨G z, hG z.1 z.2⟩
    continuous_toFun := G.continuous.subtype_mk _
    map_zero_left := fun x ↦ Subtype.ext (G.apply_zero x)
    map_one_left := fun x ↦ Subtype.ext (G.apply_one x)
    prop' := fun t x hx ↦ Subtype.ext (G.eq_fst t hx) }⟩

end NoExoticSixSphere.OrthogonalPolygon
