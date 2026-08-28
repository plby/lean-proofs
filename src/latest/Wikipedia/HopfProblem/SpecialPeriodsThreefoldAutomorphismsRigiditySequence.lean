import Wikipedia.HopfProblem.SpecialPeriodsThreefoldAutomorphismsNormalization
import Wikipedia.HopfProblem.HolomorphicAutomorphismComponents
import Wikipedia.HopfProblem.HolomorphicAutomorphismDisplacement
import Wikipedia.HopfProblem.HolomorphicAutomorphismFiniteNormalFamily

/-!
# Actual normalized sequences for local automorphism rigidity

If the vertical action failed to contain a neighborhood of one, the
ordinary compact-open topology would provide genuine automorphisms
outside its image approaching one. The actual flow normalization gives
such a sequence with one scalar coordinate fixed. The original compact
atlas then supplies bounded normalized coordinate maps and one common
holomorphic normal-limit subsequence.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Automorphisms

open HolomorphicAutomorphism.Displacement

local notation "Model" => ℂ × ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  Threefold.space_compact Threefold.space_t2Space Threefold.space_secondCountable

/-- A finite nested cover constructed from the original threefold charts. -/
def rigidityAtlas : HolomorphicAutomorphism.CompactAtlas Model Threefold.Space :=
  HolomorphicAutomorphism.compactAtlas Model Threefold.Space

/-- A genuine sequence of full automorphisms, with the consequences of
the actual normalization recorded for later limiting arguments. -/
structure NormalizedSequence where
  maps : ℕ → Aut
  tends_one : Tendsto maps atTop (𝓝 1)
  outside : ∀ n, maps n ∉ verticalHom.range
  chart_valid : ∀ n, maps n ∈ good rigidityAtlas
  detector_zero : ∀ n, detector (maps n normalizationPoint) = 0

theorem NormalizedSequence.ne_one (S : NormalizedSequence) (n : ℕ) : S.maps n ≠ 1 := by
  intro h
  apply S.outside n
  rw [h]
  exact verticalHom.range.one_mem

/-- Failure of local surjectivity produces the genuine normalized
sequence; no sequence or extension hypothesis is retained. -/
theorem exists_normalizedSequence
    (hlocal : (verticalHom.range : Set Aut) ∉ 𝓝 (1 : Aut)) :
    Nonempty NormalizedSequence := by
  obtain ⟨g, hg, hgt⟩ := HolomorphicAutomorphism.exists_sequence_outside IF Threefold.Space hlocal
  let f : ℕ → Aut := fun n => normalize (g n)
  have hft : Tendsto f atTop (𝓝 (1 : Aut)) := by
    simpa only [f, Function.comp_def, normalize_one] using
      normalize_continuousAt_one.tendsto.comp hgt
  have hfo : ∀ n, f n ∉ verticalHom.range := fun n => normalize_not_mem_range (hg n)
  have hvalid : ∀ᶠ n in atTop, f n ∈ good rigidityAtlas :=
    hft.eventually (good_nhds_one rigidityAtlas)
  have hzero : ∀ᶠ n in atTop, detector (f n normalizationPoint) = 0 :=
    hgt.eventually normalize_detector_eventually
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hvalid.and hzero)
  exact ⟨{
    maps := fun n => f (n + N)
    tends_one := hft.comp (tendsto_add_atTop_nat N)
    outside := fun n => hfo (n + N)
    chart_valid := fun n => (hN (n + N) (Nat.le_add_left N n)).1
    detector_zero := fun n => (hN (n + N) (Nat.le_add_left N n)).2 }⟩

/-- A true increasing subsequence retains every actual normalization property. -/
def NormalizedSequence.reindex (S : NormalizedSequence) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    NormalizedSequence where
  maps := S.maps ∘ φ
  tends_one := S.tends_one.comp hφ.tendsto_atTop
  outside n := S.outside (φ n)
  chart_valid n := S.chart_valid (φ n)
  detector_zero n := S.detector_zero (φ n)

/-- The actual finite compact atlas gives simultaneous holomorphic
normal limits of the actual normalized displacements. -/
theorem NormalizedSequence.exists_coordinate_limits (S : NormalizedSequence) :
    ∃ (T : NormalizedSequence) (h : rigidityAtlas.Index → Model → Model),
      (∀ i, DifferentiableOn ℂ (h i) (rigidityAtlas.outerCoordinates i)) ∧
      (∀ i, TendstoLocallyUniformlyOn
        (fun n => normalized rigidityAtlas (T.maps n) i) (h i) atTop
        (rigidityAtlas.outerCoordinates i)) := by
  obtain ⟨h, φ, hφ, hd, hlim, _⟩ :=
    HolomorphicAutomorphismFiniteNormalFamily.exists_simultaneous_subseq
      (fun i : rigidityAtlas.Index => (rigidityAtlas.outerCoordinates i : Set Model))
      (fun i => (rigidityAtlas.outerCoordinates i).isOpen)
      (fun n i => normalized rigidityAtlas (S.maps n) i)
      (fun n i => normalized_differentiableOn rigidityAtlas (S.chart_valid n) i)
      (fun _ => (1 : ℝ))
      (fun n i _ hz => normalized_norm_le_one_on_outer rigidityAtlas (S.chart_valid n) i hz)
  exact ⟨S.reindex φ hφ, h, hd, hlim⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Automorphisms
