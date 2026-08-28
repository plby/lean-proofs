import Wikipedia.NoExoticSixSphere.LocalLoweringData
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Compact cores and common controls for lowering

The finite cover is chosen before the common spatial tolerance. The energy
window is chosen only afterwards, as required by the local lowering data.
The construction also permits an empty level and an empty finite cover.
-/

open Set

namespace NoExoticSixSphere.FiniteControlledLowering

variable {M Y : Type*} [TopologicalSpace M] [PseudoMetricSpace Y]
  {energy : Y → ℝ} {admissible : Set Y} {floor level cap : ℝ}

theorem exists_finite_lowering_cover [LocallyCompactSpace Y]
    (K : Set Y) (hK : IsCompact K)
    (hlocal : ∀ x ∈ K, ∃ D : LocalLoweringData M energy admissible floor level cap,
      x ∈ D.domain) :
    ∃ n : ℕ, ∃ D : Fin n → LocalLoweringData M energy admissible floor level cap,
      ∃ F : Fin n → Set Y,
        (∀ i, IsCompact (F i) ∧ F i ⊆ (D i).domain) ∧
        K ⊆ ⋃ i, interior (F i) := by
  classical
  choose D hD using fun x : K ↦ hlocal x x.property
  choose F hF hxF hFD using fun x : K ↦ exists_compact_subset (D x).open_domain (hD x)
  have hcover : K ⊆ ⋃ x : K, interior (F x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxF ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K ↦ interior (F x))
    (fun _ ↦ isOpen_interior) hcover
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  refine ⟨Fintype.card s, (fun i ↦ D (e i).val), (fun i ↦ F (e i).val),
    (fun i ↦ ⟨hF _, hFD _⟩), ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
  refine mem_iUnion.mpr ⟨e.symm ⟨y, hy⟩, ?_⟩
  simpa only [e.apply_symm_apply] using hxy

theorem exists_pos_le_finset {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) : ∃ r > 0, ∀ i ∈ s, r ≤ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨r, hr, hrf⟩ := ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
    refine ⟨min (f i) r, lt_min (hf i (Finset.mem_insert_self _ _)) hr, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hrf j hj)

theorem exists_common_lowering_control (n : ℕ)
    (D : Fin n → LocalLoweringData M energy admissible floor level cap)
    (F : Fin n → Set Y) (hF : ∀ i, IsCompact (F i) ∧ F i ⊆ (D i).domain) :
    ∃ ρ > 0, ∃ ζ > 0,
      (∀ i, ∀ y ∈ F i, ∀ z, dist z y ≤ (n : ℝ) * ρ → z ∈ (D i).domain) ∧
      (∀ ξ : ℝ, 0 < ξ → ξ ≤ ζ → ∀ i,
        StepProperty (M := M) energy admissible (D i).domain floor
          (D i).threshold cap ξ ζ ρ) := by
  classical
  choose δ hδ hthick using fun i ↦
    (hF i).1.exists_thickening_subset_open (D i).open_domain (hF i).2
  obtain ⟨d, hd, hdδ⟩ := exists_pos_le_finset Finset.univ δ (by simpa using hδ)
  have hdδ' : ∀ i, d ≤ δ i := fun i ↦ hdδ i (Finset.mem_univ i)
  let ρ : ℝ := d / (2 * ((n : ℝ) + 1))
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : 0 < 2 * ((n : ℝ) + 1) := by positivity
  have hρ : 0 < ρ := div_pos hd hden
  have hnρ : (n : ℝ) * ρ < d := by
    dsimp [ρ]
    rw [← mul_div_assoc, div_lt_iff₀ hden]
    nlinarith
  choose ζ hζ hstep using fun i ↦ (D i).control ρ hρ
  obtain ⟨zeta, hzeta, hzetai⟩ := exists_pos_le_finset Finset.univ ζ (by simpa using hζ)
  have hzetai' : ∀ i, zeta ≤ ζ i := fun i ↦ hzetai i (Finset.mem_univ i)
  refine ⟨ρ, hρ, zeta, hzeta, ?_, ?_⟩
  · intro i y hy z hz
    exact hthick i (Metric.mem_thickening_iff.mpr ⟨y, hy, hz.trans_lt (hnρ.trans_le (hdδ' i))⟩)
  · intro ξ hξ hξz i
    exact (hstep i ξ hξ (hξz.trans (hzetai' i))).smaller_window (hzetai' i)

end NoExoticSixSphere.FiniteControlledLowering
