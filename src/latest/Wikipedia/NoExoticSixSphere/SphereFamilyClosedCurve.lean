import Wikipedia.NoExoticSixSphere.SphereFamilyPairCoordinates

/-!
# Transferring a reflection chart to the actual sphere-family closure

The local coordinate relation restricts to the actual closure subtypes.
Its compatibility with swapping transfers a real curve chart and its
reflection symmetry without changing either ambient topology.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily

open GLOrthonormalization ManifoldAffineSphereFamily FamilyEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]

theorem exists_closed_curve_of_coordinate_curve
    (g : ℝ → Sphere 3 → M) (hg : Continuous (uncurry g))
    (s : SourceChart) (c : TargetChart n M) (q : ℝ × Sphere 3)
    (hs : q.2 ∈ s.source) (hc : g q.1 q.2 ∈ c.source)
    (hcurve : ∃ hb : (q.1, (s q.2, s q.2)) ∈ closure (doublePoints (coordinateFamily g s c)),
      ∃ k : OpenPartialHomeomorph (closure (doublePoints (coordinateFamily g s c))) ℝ,
        (⟨(q.1, (s q.2, s q.2)), hb⟩ :
          closure (doublePoints (coordinateFamily g s c))) ∈ k.source ∧
        k ⟨(q.1, (s q.2, s q.2)), hb⟩ = 0 ∧
        (∀ r ∈ k.source, swapClosure (coordinateFamily g s c) r ∈ k.source) ∧
        ∀ r ∈ k.source, k (swapClosure (coordinateFamily g s c) r) = -k r) :
    ∃ ha : (q.1, (q.2, q.2)) ∈ closure (doublePoints g),
    ∃ d : OpenPartialHomeomorph (closure (doublePoints g)) ℝ,
      (⟨(q.1, (q.2, q.2)), ha⟩ : closure (doublePoints g)) ∈ d.source ∧
      d ⟨(q.1, (q.2, q.2)), ha⟩ = 0 ∧
      (∀ r ∈ d.source, swapClosure g r ∈ d.source) ∧
      ∀ r ∈ d.source, d (swapClosure g r) = -d r := by
  obtain ⟨hb, k, hkq, hkzero, hkswap, hkneg⟩ := hcurve
  let T := pairCoordinates g hg s c
  have hqT : (q.1, (q.2, q.2)) ∈ T.source :=
    (mem_pairCoordinates_source g hg s c _).mpr ⟨hs, hs, hc, hc⟩
  have hT := isImage_closedDoublePoints g hg s c
  have ha : (q.1, (q.2, q.2)) ∈ closure (doublePoints g) := (hT hqT).mp hb
  let a₀ : closure (doublePoints g) := ⟨(q.1, (q.2, q.2)), ha⟩
  let b₀ : closure (doublePoints (coordinateFamily g s c)) := ⟨(q.1, (s q.2, s q.2)), hb⟩
  let e := SubsetCoordinates.coordinates T hT a₀ b₀
  have eval {r : closure (doublePoints g)} (hr : r ∈ e.source) : (e r).val = T r.val :=
    SubsetCoordinates.coordinates_val _ _ _ _ hr
  have he₀ : e a₀ = b₀ := Subtype.ext (eval hqT)
  have hswapSource {r : closure (doublePoints g)} (hr : r ∈ e.source) :
      swapClosure g r ∈ e.source := pairCoordinates_source_swap g hg s c hr
  have hcommute {r : closure (doublePoints g)} (hr : r ∈ e.source) :
      e (swapClosure g r) = swapClosure (coordinateFamily g s c) (e r) := by
    apply Subtype.ext
    rw [eval (hswapSource hr)]
    change T (swapPair r.val) = swapPair (e r).val
    rw [eval hr]
    exact pairCoordinates_swap g hg s c r.val
  let d := e.trans k
  have hdq : a₀ ∈ d.source := by
    refine ⟨hqT, ?_⟩
    change e a₀ ∈ k.source
    rw [he₀]
    exact hkq
  refine ⟨ha, d, hdq, ?_, ?_, ?_⟩
  · change k (e a₀) = 0
    rw [he₀]
    exact hkzero
  · intro r hr
    refine ⟨hswapSource hr.1, ?_⟩
    change e (swapClosure g r) ∈ k.source
    rw [hcommute hr.1]
    exact hkswap (e r) hr.2
  · intro r hr
    change k (e (swapClosure g r)) = -k (e r)
    rw [hcommute hr.1]
    exact hkneg (e r) hr.2

end NoExoticSixSphere.SphereFamily
