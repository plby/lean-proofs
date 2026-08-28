import Wikipedia.SmoothSixDPoincare.MorseBeltNormalRegularity
import Wikipedia.SmoothSixDPoincare.MorseTransverseAttaching
import Wikipedia.SmoothSixDPoincare.SphereNormalJacobian
import Mathlib.Data.Sign.Basic

/-!
# Signs at actual transverse Morse-belt intersections

The negative coordinates of the original Morse chart give one fixed normal
map along the entire belt. Together with the outward orientation of the
attaching sphere they give nonzero signed Jacobians at transverse crossings.
The actual finite intersection set can therefore be counted with integer
weights. No value or homotopy invariance of this count is assumed or proved here.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold BigOperators

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M} (d : MorseSurgeryData E f p)

/-- One fixed normal reference frame for the entire belt. -/
def beltNormalReference (m : ℕ) (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m) :
    (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod, hdim, Nat.add_comm])

/-- The actual signed normal Jacobian of a sphere map at a point of its domain. -/
def beltIntersectionJacobian (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) (x : Hemisphere.Sphere m) : ℝ :=
  letI : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  SphereNormalCoordinates.normalJacobian j x
    (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x)

/-- The sign is zero only when the actual normal Jacobian is singular. -/
def beltIntersectionSign (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) (x : Hemisphere.Sphere m) : SignType :=
  SignType.sign (d.beltIntersectionJacobian m j g x)

/-- Domain points whose actual images lie on the original belt. -/
def beltIntersectionPoints (m : ℕ) (g : Hemisphere.Sphere m → d.UpperLevel) :
    Set (Hemisphere.Sphere m) := g ⁻¹' range d.surgery.beltSphere

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Opposite unit signs are exactly opposite actual normal Jacobians. -/
theorem beltIntersectionSigns_opposite_iff (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) (x y : Hemisphere.Sphere m) :
    d.beltIntersectionSign m j g x * d.beltIntersectionSign m j g y = -1 ↔
      d.beltIntersectionJacobian m j g x * d.beltIntersectionJacobian m j g y < 0 := by
  unfold beltIntersectionSign
  rw [← sign_mul, sign_eq_neg_one_iff]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The opposite-pair condition is independent of the one global reference-frame choice. -/
theorem opposite_beltIntersectionSigns_change_reference (m : ℕ)
    (j k : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) (x y : Hemisphere.Sphere m) :
    (d.beltIntersectionSign m k g x * d.beltIntersectionSign m k g y = -1) ↔
      (d.beltIntersectionSign m j g x * d.beltIntersectionSign m j g y = -1) := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  rw [d.beltIntersectionSigns_opposite_iff, d.beltIntersectionSigns_opposite_iff]
  exact SphereNormalCoordinates.opposite_normalJacobians_change_reference j k x y _ _

/-- The integer-weighted count of the actual finite crossing set. -/
def beltIntersectionCount (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) (hfin : (d.beltIntersectionPoints m g).Finite) : ℤ :=
  ∑ x ∈ hfin.toFinset, (d.beltIntersectionSign m j g x : ℤ)

variable (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
/-- Transversality makes the actual signed normal Jacobian nonzero. -/
theorem beltIntersectionJacobian_ne_zero (n m : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_ht : ∀ x y, NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E)
        g d.surgery.beltSphere x y)
      (x : Hemisphere.Sphere m), x ∈ d.beltIntersectionPoints m g →
      d.beltIntersectionJacobian m j g x ≠ 0 := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro hg ht x hx
  obtain ⟨v, hv⟩ := hx
  have hA := d.bijective_beltNormal_comp_of_transverse hf n m hdim g hg x v hv (ht x v hv)
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x
  have hAi : A.IsInvertible :=
    ⟨(LinearEquiv.ofBijective A.toLinearMap hA).toContinuousLinearEquiv, rfl⟩
  exact SphereNormalCoordinates.normalJacobian_ne_zero j x A hAi

open Classical in
/-- Every actual transverse crossing receives exactly one of the two unit signs. -/
theorem beltIntersectionSign_unit (n m : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_ht : ∀ x y, NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E)
        g d.surgery.beltSphere x y)
      (x : Hemisphere.Sphere m), x ∈ d.beltIntersectionPoints m g →
      d.beltIntersectionSign m j g x = 1 ∨ d.beltIntersectionSign m j g x = -1 := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg ht x hx
  have hn : d.beltIntersectionSign m j g x ≠ 0 :=
    sign_ne_zero.mpr (d.beltIntersectionJacobian_ne_zero hf n m hdim j g hg ht x hx)
  rcases SignType.trichotomy (d.beltIntersectionSign m j g x) with h | h | h
  · exact Or.inr h
  · exact (hn h).elim
  · exact Or.inl h

open Classical in
/-- The crossing domain is finite for the actual transverse embedded sphere. -/
theorem finite_beltIntersectionPoints [T2Space M] [CompactSpace M] (n m : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_hinj : Injective g)
      (_ht : ∀ x y, NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E)
        g d.surgery.beltSphere x y),
      (d.beltIntersectionPoints m g).Finite := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  intro hg hinj ht
  have hdim' : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) +
      Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [RegularLevel.Model, finrank_euclideanSpace_fin]
    have hp : Module.finrank ℝ d.chart.PositiveCoordinates = n + 1 := Fact.out
    have hs := d.chart.finrank_negative_add_positive
    omega
  have hfin := finite_transverse_intersections hg (d.belt_smooth hf n) hinj
    d.belt_isClosedEmbedding.injective hdim' (fun x y hxy => ht x y hxy)
  have hpre : (g ⁻¹' (range g ∩ range d.surgery.beltSphere)).Finite :=
    hfin.preimage hinj.injOn
  exact hpre.subset (fun x hx => ⟨⟨x, rfl⟩, hx⟩)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
