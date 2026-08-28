import Wikipedia.HopfProblem.DegreeCollapseCubicEndpointCoordinates

/-!
# Actual cubic endpoint germs from native signed quadratic charts

The explicit scalar endpoint coordinate is multiplied by the identity on
the transverse coordinates and composed with the given native Morse chart.
This constructs an actual smooth endpoint chart with the cubic function
formula and the prescribed physical critical point.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def scalarProductChart (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) (ℝ × V) (ℝ × V) ∞ where
  toPartialEquiv := (Φ.toOpenPartialHomeomorph.prod (OpenPartialHomeomorph.refl V)).toPartialEquiv
  open_source := Φ.open_source.prod isOpen_univ
  open_target := Φ.open_target.prod isOpen_univ
  contMDiffOn_toFun := by
    have h : ContDiffOn ℝ ∞ (fun p : ℝ × V => (Φ p.1, p.2)) (Φ.source ×ˢ univ) :=
      (Φ.contMDiffOn_toFun.contDiffOn.comp contDiff_fst.contDiffOn
        (fun _ hp => hp.1)).prodMk contDiff_snd.contDiffOn
    exact h.contMDiffOn
  contMDiffOn_invFun := by
    have h : ContDiffOn ℝ ∞ (fun p : ℝ × V => (Φ.symm p.1, p.2)) (Φ.target ×ˢ univ) :=
      (Φ.contMDiffOn_invFun.contDiffOn.comp contDiff_fst.contDiffOn
        (fun _ hp => hp.1)).prodMk contDiff_snd.contDiffOn
    exact h.contMDiffOn

theorem exists_endpoint_product_chart {m : ℕ} (σ : Fin m → ℝ)
    {a : ℝ} (ha : 0 < a) (e : ℝ) (he : e ^ 2 = 1) :
    ∃ P : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, Model m) (Model m) (Model m) ∞,
      (e * a, (0 : Fin m → ℝ)) ∈ P.source ∧ P (e * a, 0) = 0 ∧
      (∀ p, (P p).2 = p.2) ∧
      (∀ p ∈ P.source, cubic σ (-(a ^ 2)) p = cubic σ (-(a ^ 2)) (e * a, 0) +
        e * (P p).1 ^ 2 + ∑ i, σ i * (P p).2 i ^ 2) := by
  obtain ⟨Φ, hp, hsource, hΦ, hcenter⟩ := exists_endpoint_scalar_chart ha e
  let P := scalarProductChart (V := Fin m → ℝ) Φ
  have hP (p : Model m) : P p = (endpointCoordinate a e p.1, p.2) :=
    Prod.ext (congrFun hΦ p.1) rfl
  refine ⟨P, ⟨hp, mem_univ _⟩, ?_, fun _ => rfl, ?_⟩
  · rw [hP, endpointCoordinate_center]
    rfl
  · intro p hp
    rw [hP]
    exact cubic_endpoint_square σ a e he (hsource hp.1)

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- A native signed quadratic chart produces a native exact cubic endpoint
chart, retaining the same critical point and staying in the original target. -/
theorem exists_native_cubic_endpoint {m : ℕ} (σ : Fin m → ℝ)
    {a : ℝ} (ha : 0 < a) (e : ℝ) (he : e ^ 2 = 1)
    (Q : PartialDiffeomorph 𝓘(ℝ, Model m) I (Model m) M ∞)
    (h0 : (0 : Model m) ∈ Q.source) {f : M → ℝ} (b : ℝ)
    (hquad : ∀ p ∈ Q.source, f (Q p) = b + cubic σ (-(a ^ 2)) (e * a, 0) +
      e * p.1 ^ 2 + ∑ i, σ i * p.2 i ^ 2) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) I (Model m) M ∞,
      (e * a, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (e * a, 0) = Q 0 ∧
      Φ.target ⊆ Q.target ∧ (∀ p ∈ Φ.source, f (Φ p) = b + cubic σ (-(a ^ 2)) p) := by
  obtain ⟨P, hp, hcenter, _, hP⟩ := exists_endpoint_product_chart σ ha e he
  let Φ := P.trans Q
  have hpΦ : (e * a, (0 : Fin m → ℝ)) ∈ Φ.source := by
    change (e * a, (0 : Fin m → ℝ)) ∈ P.source ∧ P (e * a, 0) ∈ Q.source
    exact ⟨hp, hcenter.symm ▸ h0⟩
  refine ⟨Φ, hpΦ, ?_, fun _ hp => hp.1, ?_⟩
  · change Q (P (e * a, 0)) = Q 0
    rw [hcenter]
  · intro p hp
    change f (Q (P p)) = b + cubic σ (-(a ^ 2)) p
    rw [hquad (P p) hp.2, hP p hp.1]
    ring

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
