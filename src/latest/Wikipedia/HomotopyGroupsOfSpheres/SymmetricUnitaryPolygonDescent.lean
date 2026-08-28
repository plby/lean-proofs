import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygonDifferential
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryCompactness
import Wikipedia.NoExoticSixSphere.OrthogonalUniformDescent

/-!
# Actual noncritical descent inside symmetric determinant-one polygons

Negative velocity jumps are reversible trace-zero directions at each vertex.
Their exponentials stay in the original constrained space and agree with
orthogonal descent. Compactness supplies a uniform admissible descent interval.
-/

noncomputable section

@[instance_reducible] private def descentOrthogonalModelNormedSpace (d m : ℕ) :
    NormedSpace ℝ (NoExoticSixSphere.OrthogonalVertexSpace.Model d m) := inferInstance

open scoped Matrix.Norms.Frobenius Topology Manifold
open Set Filter

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

namespace VertexSpace

theorem continuousAt_of_forget {N : Type*} [Fintype N] [DecidableEq N] {m : ℕ}
    {X : Type*} [TopologicalSpace X] {f : X → Space N m} {x : X}
    (h : ContinuousAt (fun y ↦ forget (f y)) x) : ContinuousAt f x := by
  have he := (continuous_forget (N := N) (m := m)).isClosedEmbedding
    (forget_injective (N := N) (m := m))
  exact he.isEmbedding.isInducing.continuousAt_iff.mpr h

end VertexSpace

namespace Polygon

open VertexSpace ComplexMatrixRealRepresentation

variable {N : Type*} [Fintype N] [DecidableEq N] {m : ℕ}

local instance descentOrthogonalModelSpace :
    NormedSpace ℝ (NoExoticSixSphere.OrthogonalVertexSpace.Model (2 * Fintype.card N) m) :=
  descentOrthogonalModelNormedSpace _ _

theorem noncritical_forget (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m)
    (hn : fderiv ℝ (localEnergy a b τ v) 0 ≠ 0) :
    mfderiv 𝓘(ℝ, NoExoticSixSphere.OrthogonalVertexSpace.Model (2 * Fintype.card N) m) 𝓘(ℝ, ℝ)
      (NoExoticSixSphere.OrthogonalPolygon.energy (specialOrthogonal a) (specialOrthogonal b) τ)
        (forget v) ≠ 0 := fun h ↦ hn (critical_of_forget a b τ v hv h)

def jumpSquareNorm (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) : ℝ :=
  NoExoticSixSphere.OrthogonalPolygon.jumpSquareNorm
    (specialOrthogonal a) (specialOrthogonal b) τ (forget v)

theorem jumpSquareNorm_eq_zero_iff (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) : jumpSquareNorm a b τ v = 0 ↔
      NoExoticSixSphere.OrthogonalPolygon.velocityJump
        (specialOrthogonal a) (specialOrthogonal b) τ (forget v) = 0 :=
  NoExoticSixSphere.OrthogonalPolygon.jumpSquareNorm_eq_zero_iff
    (specialOrthogonal a) (specialOrthogonal b) τ (forget v)

theorem jumpSquareNorm_pos_of_noncritical (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m)
    (hn : fderiv ℝ (localEnergy a b τ v) 0 ≠ 0) : 0 < jumpSquareNorm a b τ v :=
  NoExoticSixSphere.OrthogonalPolygon.jumpSquareNorm_pos_of_noncritical
    (specialOrthogonal a) (specialOrthogonal b) τ (forget v) (admissible_forget a b hv)
    (noncritical_forget a b τ v hv hn)

theorem jumpSquareNorm_eq_zero_of_critical (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m)
    (hcrit : fderiv ℝ (localEnergy a b τ v) 0 = 0) : jumpSquareNorm a b τ v = 0 :=
  (jumpSquareNorm_eq_zero_iff a b τ v).mpr
    ((NoExoticSixSphere.OrthogonalPolygon.mfderiv_energy_eq_zero_iff
      (specialOrthogonal a) (specialOrthogonal b) τ (forget v) (admissible_forget a b hv)).mp
        (critical_forget a b τ v hv hcrit))

theorem continuousAt_jumpSquareNorm (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    {v : VertexSpace.Space N m} (hv : v ∈ admissible a b m) :
    ContinuousAt (jumpSquareNorm a b τ) v :=
  (NoExoticSixSphere.OrthogonalPolygon.continuousAt_jumpSquareNorm
    (specialOrthogonal a) (specialOrthogonal b) τ (admissible_forget a b hv)).comp
      (continuous_forget (N := N) (m := m)).continuousAt

def descent (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (p : VertexSpace.Space N m × ℝ) : VertexSpace.Space N m := by
  classical
  exact if h : p.1 ∈ admissible a b m then
    vertexVariation p.1 (-jumpDirection a b τ p.1 h) p.2 else p.1

theorem descent_zero (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ) (v : VertexSpace.Space N m) :
    descent a b τ (v, 0) = v := by
  by_cases hv : v ∈ admissible a b m
  · rw [descent, dif_pos hv, vertexVariation_zero]
  · rw [descent, dif_neg hv]

theorem forget_descent (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m) (s : ℝ) :
    forget (descent a b τ (v, s)) = NoExoticSixSphere.OrthogonalPolygon.descent
      (specialOrthogonal a) (specialOrthogonal b) τ (forget v, s) := by
  rw [descent, dif_pos hv, forget_vertexVariation]
  change NoExoticSixSphere.OrthogonalPolygon.vertexVariation (forget v)
    (fun j ↦ ComplexSkewMatrices.toOrthogonalSkew (-velocityJump a b τ v j)) s = _
  have hneg : (fun j ↦ ComplexSkewMatrices.toOrthogonalSkew (-velocityJump a b τ v j)) =
      -NoExoticSixSphere.OrthogonalPolygon.velocityJump
        (specialOrthogonal a) (specialOrthogonal b) τ (forget v) := by
    funext j
    simp only [map_neg, Pi.neg_apply, velocityJump_forget a b τ hv]
  rw [hneg]
  rfl

private theorem continuousAt_ambient_descent (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    {p : VertexSpace.Space N m × ℝ} (hp : p.1 ∈ admissible a b m) :
    ContinuousAt (fun q : VertexSpace.Space N m × ℝ ↦
      NoExoticSixSphere.OrthogonalPolygon.descent (specialOrthogonal a) (specialOrthogonal b) τ
        (forget q.1, q.2)) p := by
  let input : C(VertexSpace.Space N m × ℝ,
      NoExoticSixSphere.OrthogonalVertexSpace.Space (2 * Fintype.card N) m × ℝ) :=
    ⟨fun q ↦ (forget q.1, q.2),
      (continuous_forget.comp continuous_fst).prodMk continuous_snd⟩
  have hd : ContinuousAt (NoExoticSixSphere.OrthogonalPolygon.descent
      (specialOrthogonal a) (specialOrthogonal b) τ) (input p) :=
    NoExoticSixSphere.OrthogonalPolygon.continuousAt_descent
      (specialOrthogonal a) (specialOrthogonal b) τ
      (p := (forget p.1, p.2)) (admissible_forget a b hp)
  exact hd.comp (f := input) input.continuous.continuousAt

theorem continuousAt_forget_descent (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    {p : VertexSpace.Space N m × ℝ} (hp : p.1 ∈ admissible a b m) :
    ContinuousAt (fun q ↦ forget (descent a b τ q)) p := by
  have hnear : ∀ᶠ q : VertexSpace.Space N m × ℝ in 𝓝 p, q.1 ∈ admissible a b m :=
    continuousAt_fst.eventually ((isOpen_admissible a b m).mem_nhds hp)
  exact (continuousAt_ambient_descent a b τ hp).congr_of_eventuallyEq
    (hnear.mono (fun q hq ↦ forget_descent a b τ q.1 hq q.2))

theorem continuousAt_descent (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    {p : VertexSpace.Space N m × ℝ} (hp : p.1 ∈ admissible a b m) :
    ContinuousAt (descent a b τ) p := continuousAt_of_forget (continuousAt_forget_descent a b τ hp)

theorem exists_uniform_descent (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (C : Set (VertexSpace.Space N m)) (hC : IsCompact C) (ha : C ⊆ admissible a b m)
    (hn : ∀ v ∈ C, fderiv ℝ (localEnergy a b τ v) 0 ≠ 0) :
    ∃ c > 0, ∃ T > 0, ∀ v ∈ C, ∀ s ∈ Icc (0 : ℝ) T,
      descent a b τ (v, s) ∈ admissible a b m ∧
        energy a b τ (descent a b τ (v, s)) ≤ energy a b τ v - c * s := by
  have hCa : forget '' C ⊆ NoExoticSixSphere.OrthogonalPolygon.admissible
      (specialOrthogonal a) (specialOrthogonal b) m := by
    rintro _ ⟨v, hv, rfl⟩
    exact admissible_forget a b (ha hv)
  have hCn : ∀ w ∈ forget '' C,
      mfderiv 𝓘(ℝ, NoExoticSixSphere.OrthogonalVertexSpace.Model (2 * Fintype.card N) m) 𝓘(ℝ, ℝ)
        (NoExoticSixSphere.OrthogonalPolygon.energy (specialOrthogonal a) (specialOrthogonal b) τ)
          w ≠ 0 := by
    rintro _ ⟨v, hv, rfl⟩
    exact noncritical_forget a b τ v (ha hv) (hn v hv)
  obtain ⟨c, hc, T₀, hT₀, hstep⟩ := NoExoticSixSphere.OrthogonalPolygon.exists_uniform_descent
    (specialOrthogonal a) (specialOrthogonal b) τ (forget '' C)
    (hC.image continuous_forget) hCa hCn
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hmap : Continuous (fun p : ℝ × C ↦ descent a b τ (p.2.1, p.1)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (continuousAt_descent a b τ (ha p.2.2)).comp
      ((continuous_subtype_val.continuousAt.comp continuousAt_snd).prodMk continuousAt_fst)
  have ho : IsOpen {s : ℝ | ∀ v : C, descent a b τ (v.1, s) ∈ admissible a b m} :=
    NoExoticSixSphere.isOpen_forall_compact ((isOpen_admissible a b m).preimage hmap)
  have hz : (0 : ℝ) ∈ {s : ℝ | ∀ v : C, descent a b τ (v.1, s) ∈ admissible a b m} := by
    intro v
    rw [descent_zero]
    exact ha v.2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hz)
  refine ⟨c, hc, min T₀ (ε / 2), lt_min hT₀ (by positivity), ?_⟩
  intro v hv s hs
  have hs₀ : s ∈ Icc (0 : ℝ) T₀ := ⟨hs.1, hs.2.trans (min_le_left _ _)⟩
  have hsball : s ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    have hh := hs.2.trans (min_le_right T₀ (ε / 2))
    linarith
  refine ⟨hball hsball ⟨v, hv⟩, ?_⟩
  have he := (hstep (forget v) ⟨v, hv, rfl⟩ s hs₀).2
  change NoExoticSixSphere.OrthogonalPolygon.energy (specialOrthogonal a) (specialOrthogonal b) τ
    (forget (descent a b τ (v, s))) ≤ _
  rw [forget_descent a b τ v (ha hv) s]
  exact he

end Polygon
end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
