import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructurePolygonDifferential
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureVertexVariation
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicUniformDescent

/-!
# Energy descent inside the complex-structure polygon space

The velocity jumps are actual anticommuting tangent directions. Exponentiating
their negatives keeps each vertex in the complex-structure locus and agrees
with the proved symplectic descent after inclusion. Compactness shortens the
uniform descent interval so that the restricted admissibility condition holds.
-/

noncomputable section

open Set Filter
open scoped Topology Manifold

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

namespace ComplexStructureVertices

theorem continuousAt_of_forget {n m : ℕ} {X : Type*} [TopologicalSpace X]
    {f : X → Space n m} {x : X} (h : ContinuousAt (fun y ↦ forget (f y)) x) :
    ContinuousAt f x := by
  apply continuousAt_pi.mpr
  intro i
  have h₁ : ContinuousAt (fun y ↦ (ComplexStructures.toSymplectic (f y i)).val) x :=
    continuous_subtype_val.continuousAt.comp ((continuous_apply i).continuousAt.comp h)
  have h₂ : ContinuousAt (fun y ↦ (ComplexStructures.toSymplectic (f y i)).val.val) x :=
    continuous_subtype_val.continuousAt.comp h₁
  have hop : ContinuousAt (fun y ↦ (ComplexStructures.toSymplectic (f y i)).val.val.val) x :=
    continuous_subtype_val.continuousAt.comp h₂
  exact tendsto_subtype_rng.mpr (tendsto_subtype_rng.mpr hop)

end ComplexStructureVertices

namespace ComplexStructurePolygon

open ComplexStructures ComplexStructureVertices

variable {n m : ℕ}

theorem noncritical_forget (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m)
    (hn : fderiv ℝ (localEnergy a b τ v) 0 ≠ 0) :
    mfderiv 𝓘(ℝ, VertexSpace.Model n m) 𝓘(ℝ, ℝ)
      (Polygon.energy (toSymplectic a) (toSymplectic b) τ) (forget v) ≠ 0 := by
  intro hc
  exact hn ((fderiv_localEnergy_eq_zero_iff a b τ v hv).mpr
    ((Polygon.mfderiv_energy_eq_zero_iff (toSymplectic a) (toSymplectic b) τ
      (forget v) (admissible_forget a b hv)).mp hc))

def jumpSquareNorm (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (v : ComplexStructureVertices.Space n m) : ℝ :=
  Polygon.jumpSquareNorm (toSymplectic a) (toSymplectic b) τ (forget v)

theorem jumpSquareNorm_eq_zero_iff (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (v : ComplexStructureVertices.Space n m) :
    jumpSquareNorm a b τ v = 0 ↔
      Polygon.velocityJump (toSymplectic a) (toSymplectic b) τ (forget v) = 0 :=
  Polygon.jumpSquareNorm_eq_zero_iff (toSymplectic a) (toSymplectic b) τ (forget v)

theorem jumpSquareNorm_pos_of_noncritical (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) (v : ComplexStructureVertices.Space n m)
    (hv : v ∈ admissible a b m) (hn : fderiv ℝ (localEnergy a b τ v) 0 ≠ 0) :
    0 < jumpSquareNorm a b τ v :=
  Polygon.jumpSquareNorm_pos_of_noncritical (toSymplectic a) (toSymplectic b) τ
    (forget v) (admissible_forget a b hv) (noncritical_forget a b τ v hv hn)

theorem continuousAt_jumpSquareNorm (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    {v : ComplexStructureVertices.Space n m} (hv : v ∈ admissible a b m) :
    ContinuousAt (jumpSquareNorm a b τ) v :=
  (Polygon.continuousAt_jumpSquareNorm (toSymplectic a) (toSymplectic b) τ
    (admissible_forget a b hv)).comp continuous_forget.continuousAt

def descent (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (p : ComplexStructureVertices.Space n m × ℝ) : ComplexStructureVertices.Space n m := by
  classical
  exact if h : p.1 ∈ admissible a b m then
    vertexVariation p.1 (-jumpDirection a b τ p.1 h) p.2 else p.1

theorem descent_zero (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (v : ComplexStructureVertices.Space n m) : descent a b τ (v, 0) = v := by
  by_cases hv : v ∈ admissible a b m
  · rw [descent, dif_pos hv, vertexVariation_zero]
  · rw [descent, dif_neg hv]

theorem forget_descent (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m) (s : ℝ) :
    forget (descent a b τ (v, s)) =
      Polygon.descent (toSymplectic a) (toSymplectic b) τ (forget v, s) := by
  rw [descent, dif_pos hv, forget_vertexVariation]
  change Polygon.vertexVariation (forget v) (modelInclusion v (-jumpDirection a b τ v hv)) s = _
  have hneg : modelInclusion v (-jumpDirection a b τ v hv) =
      -Polygon.velocityJump (toSymplectic a) (toSymplectic b) τ (forget v) := by
    funext i
    apply Subtype.ext
    rfl
  rw [hneg]
  rfl

private theorem continuousAt_ambient_descent (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) {p : ComplexStructureVertices.Space n m × ℝ}
    (hp : p.1 ∈ admissible a b m) :
    ContinuousAt (fun q : ComplexStructureVertices.Space n m × ℝ ↦
      Polygon.descent (toSymplectic a) (toSymplectic b) τ (forget q.1, q.2)) p := by
  let input : C(ComplexStructureVertices.Space n m × ℝ, VertexSpace.Space n m × ℝ) :=
    ⟨fun q ↦ (forget q.1, q.2),
      (continuous_forget.comp continuous_fst).prodMk continuous_snd⟩
  have hd : ContinuousAt (Polygon.descent (toSymplectic a) (toSymplectic b) τ) (input p) :=
    Polygon.continuousAt_descent (toSymplectic a) (toSymplectic b) τ
      (p := (forget p.1, p.2)) (admissible_forget a b hp)
  exact hd.comp input.continuous.continuousAt

theorem continuousAt_forget_descent (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    {p : ComplexStructureVertices.Space n m × ℝ} (hp : p.1 ∈ admissible a b m) :
    ContinuousAt (fun q ↦ forget (descent a b τ q)) p := by
  have hnear : ∀ᶠ q : ComplexStructureVertices.Space n m × ℝ in 𝓝 p,
      q.1 ∈ admissible a b m :=
    continuousAt_fst.eventually ((isOpen_admissible a b m).mem_nhds hp)
  exact (continuousAt_ambient_descent a b τ hp).congr_of_eventuallyEq
    (hnear.mono (fun q hq ↦ forget_descent a b τ q.1 hq q.2))

theorem continuousAt_descent (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    {p : ComplexStructureVertices.Space n m × ℝ} (hp : p.1 ∈ admissible a b m) :
    ContinuousAt (descent a b τ) p :=
  continuousAt_of_forget (continuousAt_forget_descent a b τ hp)

theorem exists_uniform_descent (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (C : Set (ComplexStructureVertices.Space n m)) (hC : IsCompact C)
    (ha : C ⊆ admissible a b m)
    (hn : ∀ v ∈ C, fderiv ℝ (localEnergy a b τ v) 0 ≠ 0) :
    ∃ c > 0, ∃ T > 0, ∀ v ∈ C, ∀ s ∈ Icc (0 : ℝ) T,
      descent a b τ (v, s) ∈ admissible a b m ∧
        energy a b τ (descent a b τ (v, s)) ≤ energy a b τ v - c * s := by
  have hCa : forget '' C ⊆ Polygon.admissible (toSymplectic a) (toSymplectic b) m := by
    rintro _ ⟨v, hv, rfl⟩
    exact admissible_forget a b (ha hv)
  have hCn : ∀ w ∈ forget '' C,
      mfderiv 𝓘(ℝ, VertexSpace.Model n m) 𝓘(ℝ, ℝ)
        (Polygon.energy (toSymplectic a) (toSymplectic b) τ) w ≠ 0 := by
    rintro _ ⟨v, hv, rfl⟩
    exact noncritical_forget a b τ v (ha hv) (hn v hv)
  obtain ⟨c, hc, T₀, hT₀, hstep⟩ := Polygon.exists_uniform_descent
    (toSymplectic a) (toSymplectic b) τ (forget '' C)
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
  change Polygon.energy (toSymplectic a) (toSymplectic b) τ
    (forget (descent a b τ (v, s))) ≤ _
  rw [forget_descent a b τ v (ha hv) s]
  exact he

end ComplexStructurePolygon
end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
