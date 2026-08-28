import Wikipedia.NoExoticSixSphere.OrthogonalUniformDescent
import Wikipedia.NoExoticSixSphere.OrthogonalPolygonSublevels
import Wikipedia.NoExoticSixSphere.RealIntervalProgress

/-!
# An energy-decreasing step fixing a lower polygon sublevel

A continuous cutoff of the descent time fixes polygons below a lower energy
threshold. On a compact band without critical points, the resulting step stays
in the original sublevel, never increases energy, and gives a uniform decrease
above a second, strictly larger threshold.
-/

open Set unitInterval
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization OrthogonalVertexSpace RealIntervalProgress

variable {n m : ℕ}

def energyBand (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ) (l E : ℝ) :
    Set (Space n m) := energySublevel a b τ E ∩ energy a b τ ⁻¹' Ici l

theorem isCompact_energyBand (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (l E : ℝ) (hcompact : IsCompact (energySublevel a b τ E)) :
    IsCompact (energyBand a b τ l E) := by
  have he : ContinuousOn (energy a b τ) (energySublevel a b τ E) :=
    (contMDiffOn_energy a b τ).continuousOn.mono (fun _ hv ↦ hv.1)
  exact (he.preimage_isClosed_of_isClosed hcompact.isClosed isClosed_Ici).isCompact

noncomputable def cutoffDescent (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (l k T : ℝ) (p : I × Space n m) : Space n m :=
  descent a b τ (p.2, (p.1 : ℝ) * T * progress l k (energy a b τ p.2))

theorem cutoffDescent_zero (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (l k T : ℝ) (v : Space n m) : cutoffDescent a b τ l k T (0, v) = v := by
  simp [cutoffDescent, descent_zero]

theorem cutoffDescent_fixed (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (l k T : ℝ) (hlk : l ≤ k) (v : Space n m) (hv : energy a b τ v ≤ l) (s : I) :
    cutoffDescent a b τ l k T (s, v) = v := by
  simp [cutoffDescent, progress_before hlk hv, descent_zero]

theorem cutoffDescent_one (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (l k T : ℝ) (hlk : l < k) (v : Space n m) (hv : k ≤ energy a b τ v) :
    cutoffDescent a b τ l k T (1, v) = descent a b τ (v, T) := by
  simp [cutoffDescent, progress_after hlk hv]

theorem cutoffTime_mem (l k T e : ℝ) (hT : 0 ≤ T) (s : I) :
    (s : ℝ) * T * progress l k e ∈ Icc (0 : ℝ) T := by
  have hp : progress l k e ∈ Icc (0 : ℝ) 1 :=
    (projIcc (0 : ℝ) 1 zero_le_one ((e - l) / (k - l))).property
  have hst : 0 ≤ (s : ℝ) * T := mul_nonneg s.2.1 hT
  refine ⟨mul_nonneg hst hp.1, ?_⟩
  calc
    (s : ℝ) * T * progress l k e ≤ (s : ℝ) * T * 1 :=
      mul_le_mul_of_nonneg_left hp.2 hst
    _ ≤ T := by simpa only [mul_one, one_mul] using mul_le_mul_of_nonneg_right s.2.2 hT

theorem continuous_cutoffDescent_sublevel (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (l k T E : ℝ) :
    Continuous (fun p : I × energySublevel a b τ E ↦
      cutoffDescent a b τ l k T (p.1, p.2.1)) := by
  have hv : Continuous (fun p : I × energySublevel a b τ E ↦ p.2.1) :=
    continuous_subtype_val.comp continuous_snd
  have he : Continuous (fun p : I × energySublevel a b τ E ↦ energy a b τ p.2.1) :=
    (contMDiffOn_energy a b τ).continuousOn.comp_continuous hv (fun p ↦ p.2.2.1)
  have ht : Continuous (fun p : I × energySublevel a b τ E ↦
      (p.1 : ℝ) * T * progress l k (energy a b τ p.2.1)) :=
    ((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
      ((continuous_progress l k).comp he)
  apply continuous_iff_continuousAt.mpr
  intro p
  exact ContinuousAt.comp
    (f := fun q : I × energySublevel a b τ E ↦
      (q.2.1, (q.1 : ℝ) * T * progress l k (energy a b τ q.2.1)))
    (g := descent a b τ) (continuousAt_descent a b τ p.2.2.1)
    (hv.prodMk ht).continuousAt

theorem cutoffDescent_mem_and_energy_le (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (l k T c E : ℝ) (hlk : l < k) (hT : 0 ≤ T) (hc : 0 ≤ c)
    (hstep : ∀ v ∈ energyBand a b τ l E, ∀ t ∈ Icc (0 : ℝ) T,
      descent a b τ (v, t) ∈ admissible a b m ∧
        energy a b τ (descent a b τ (v, t)) ≤ energy a b τ v - c * t)
    (v : Space n m) (hv : v ∈ energySublevel a b τ E) (s : I) :
    cutoffDescent a b τ l k T (s, v) ∈ energySublevel a b τ E ∧
      energy a b τ (cutoffDescent a b τ l k T (s, v)) ≤ energy a b τ v := by
  by_cases hl : energy a b τ v ≤ l
  · rw [cutoffDescent_fixed a b τ l k T hlk.le v hl s]
    exact ⟨hv, le_rfl⟩
  · have hb : v ∈ energyBand a b τ l E := ⟨hv, (lt_of_not_ge hl).le⟩
    have ht := cutoffTime_mem l k T (energy a b τ v) hT s
    have hd := hstep v hb _ ht
    have he : energy a b τ (cutoffDescent a b τ l k T (s, v)) ≤ energy a b τ v :=
      hd.2.trans (sub_le_self _ (mul_nonneg hc ht.1))
    exact ⟨⟨hd.1, he.trans hv.2⟩, he⟩

/-- A continuous step on the entire upper sublevel, stationary below `l`,
with a uniform energy decrement above `k`. -/
theorem exists_cutoff_descent (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (l k E : ℝ) (hlk : l < k) (hcompact : IsCompact (energySublevel a b τ E))
    (hn : ∀ v ∈ energyBand a b τ l E,
      mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v ≠ 0) :
    ∃ δ > 0, ∃ H : C(I × energySublevel a b τ E, energySublevel a b τ E),
      (∀ v, H (0, v) = v) ∧
      (∀ s v, energy a b τ v.1 ≤ l → H (s, v) = v) ∧
      (∀ s v, energy a b τ (H (s, v)).1 ≤ energy a b τ v.1) ∧
      (∀ v, k ≤ energy a b τ v.1 → energy a b τ (H (1, v)).1 ≤ energy a b τ v.1 - δ) := by
  obtain ⟨c, hc, T, hT, hstep⟩ := exists_uniform_descent a b τ (energyBand a b τ l E)
    (isCompact_energyBand a b τ l E hcompact) (fun _ hv ↦ hv.1.1) hn
  have hpres := cutoffDescent_mem_and_energy_le a b τ l k T c E hlk hT.le hc.le hstep
  let H : C(I × energySublevel a b τ E, energySublevel a b τ E) :=
    ⟨fun p ↦ ⟨cutoffDescent a b τ l k T (p.1, p.2.1), (hpres p.2.1 p.2.2 p.1).1⟩,
      (continuous_cutoffDescent_sublevel a b τ l k T E).subtype_mk _⟩
  refine ⟨c * T, mul_pos hc hT, H, ?_, ?_, ?_, ?_⟩
  · intro v
    apply Subtype.ext
    exact cutoffDescent_zero a b τ l k T v.1
  · intro s v hv
    apply Subtype.ext
    exact cutoffDescent_fixed a b τ l k T hlk.le v.1 hv s
  · intro s v
    exact (hpres v.1 v.2 s).2
  · intro v hv
    change energy a b τ (cutoffDescent a b τ l k T (1, v.1)) ≤ _
    rw [cutoffDescent_one a b τ l k T hlk v.1 hv]
    exact (hstep v.1 ⟨v.2, hlk.le.trans hv⟩ T ⟨hT.le, le_rfl⟩).2

end NoExoticSixSphere.OrthogonalPolygon
