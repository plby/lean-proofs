import Wikipedia.SmoothSixDPoincare.WhitneyModelCancellation
import Wikipedia.SmoothSixDPoincare.SupportedBumpIsotopy
import Wikipedia.SmoothSixDPoincare.WhitneyBigon

/-!
# Supported smooth cancellation in a supplied Whitney model chart

The actual six-dimensional model motion extends to a smooth family of global
diffeomorphisms of the native manifold, fixed outside the chart. Its endpoint
separates the two actual modeled sheet images. The model chart and support
containment are explicit hypotheses of this intermediate result: constructing
such a chart from a native Whitney disk and the intersecting handles remains
a separate obligation.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

variable {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Space) J Space M ∞)

def nativeFirstSheet : Set M := Φ '' (range firstSheet ∩ Φ.source)

def nativeSecondSheet (h : ℝ) : Set M := Φ '' (range (secondSheet h) ∩ Φ.source)

omit [T2Space M] in
/-- The support-containment hypothesis includes the full joining segment, hence both corners. -/
theorem joiningSegment_mem_source (hK : tsupport cutoff ⊆ Φ.source)
    {s : ℝ} (hs : |s| ≤ 1) : firstSheet (s, 0) ∈ Φ.source := by
  apply hK
  apply subset_tsupport cutoff
  change cutoff (firstSheet (s, 0)) ≠ 0
  rw [cutoff_firstSheet_zero hs]
  norm_num

omit [T2Space M] in
/-- The support condition also contains the full small cornered bigon. -/
theorem bigon_mem_source (hK : tsupport cutoff ⊆ Φ.source)
    {h : ℝ} (hh : 0 < h) (hsmall : h ≤ 1) {p : ℝ × ℝ} (hp : p ∈ bigon h) :
    bigonEmbedding p ∈ Φ.source := by
  apply hK
  apply subset_tsupport cutoff
  change cutoff (bigonEmbedding p) ≠ 0
  rw [cutoff_bigonEmbedding hh hsmall hp]
  norm_num

omit [T2Space M] in
/-- Inside the genuine chart, the original sheets have exactly the model intersections. -/
theorem native_first_eq_second_iff {h : ℝ} (hh : 0 < h) (p q : Sheet)
    (hp : firstSheet p ∈ Φ.source) (hq : secondSheet h q ∈ Φ.source) :
    Φ (firstSheet p) = Φ (secondSheet h q) ↔
      p.1 = q.1 ∧ p.2 = 0 ∧ q.2 = 0 ∧ (q.1 = -1 ∨ q.1 = 1) := by
  constructor
  · intro heq
    exact (firstSheet_eq_secondSheet_iff hh p q).mp (Φ.toPartialEquiv.injOn hp hq heq)
  · intro heq
    exact congrArg Φ ((firstSheet_eq_secondSheet_iff hh p q).mpr heq)

/-- A genuine supported smooth motion removes the two intersections in the supplied model chart.
This does not assume a move or a diffeomorphism as an input; both are constructed. -/
theorem exists_supported_native_model_cancellation (hK : tsupport cutoff ⊆ Φ.source) :
    ∃ η : ℝ, 0 < η ∧ ∀ h : ℝ, 0 < h → h < η →
      ∃ A : ℝ × M → M,
        ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
        (∀ z, A (0, z) = z) ∧
        (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ z, A (t, z) = d z) ∧
        (∀ t z, z ∉ Φ.target → A (t, z) = z) ∧
        Disjoint ((fun z => A (1, z)) '' nativeFirstSheet Φ) (nativeSecondSheet Φ h) := by
  obtain ⟨η₀, hη₀, hmodel⟩ := exists_small_model_cancellation
  obtain ⟨ε, hε, hnative⟩ := SupportedDiffeomorph.exists_small_supported_bump_isotopy Φ
    contDiff_cutoff hasCompactSupport_cutoff hK
  refine ⟨min η₀ (ε / 4), lt_min hη₀ (by positivity), ?_⟩
  intro h hh hsmall
  obtain ⟨d, hd, hfix, -⟩ := hmodel h hh (hsmall.trans_le (min_le_left _ _))
  have hnorm : ‖moveVector h‖ < ε := by
    rw [norm_moveVector hh.le]
    have hsmall' := hsmall.trans_le (min_le_right η₀ (ε / 4))
    linarith
  obtain ⟨A, hA, hzero, hdiff, hAfixed, hAend⟩ := hnative (moveVector h) hnorm
  have hdS : MapsTo d Φ.source Φ.source :=
    SupportedDiffeomorph.mapsTo_source Φ d.toEquiv hK hfix
  refine ⟨A, hA, hzero, hdiff, ?_, ?_⟩
  · intro t z hz
    apply hAfixed t z
    rintro ⟨q, hq, rfl⟩
    exact hz (Φ.map_source' (hK hq))
  · rw [Set.disjoint_left]
    intro z hz₁ hz₂
    obtain ⟨y, hy, hyz⟩ := hz₁
    obtain ⟨a, ⟨⟨p, hpa⟩, ha⟩, hay⟩ := hy
    obtain ⟨b, ⟨⟨q, hqb⟩, hb⟩, hbz⟩ := hz₂
    have hleft : A (1, Φ a) = z := by rw [hay]; exact hyz
    have hcomm : A (1, Φ a) = Φ (d a) :=
      (hAend a ha).trans (congrArg Φ (hd a).symm)
    have hcoordinates : d a = b := Φ.toPartialEquiv.injOn (hdS ha) hb
      (hcomm.symm.trans (hleft.trans hbz.symm))
    apply shifted_firstSheet_ne_secondSheet hh hd p q
    rw [hpa, hqb]
    exact hcoordinates

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel
