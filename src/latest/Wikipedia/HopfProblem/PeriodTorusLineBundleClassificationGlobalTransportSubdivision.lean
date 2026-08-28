import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport
import Mathlib.Topology.UnitInterval

/-!
# Locally uniform finite chart subdivisions of radial paths

The actual trivializing cover supplies a finite monotone chart subdivision
of every radial path. Compactness and the tube lemma make the same finite
breakpoints and chart indices valid on an open neighbourhood of its endpoint.
No subdivision or global frame is assumed.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalTransport

open HolomorphicCharacterBundle PeriodTorusLineBundleClassificationTransport

variable {ι : Type*} (A : TransitionData ComplexPlane₂ ι)

/-- Construct a finite chart subdivision from the actual radial pullback cover.
The segment count is positive, even when one chart suffices. -/
theorem exists_radial_subdivision (x₀ : ComplexPlane₂) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : Fin (n + 1) → ℝ,
      t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧
      ∃ c : Fin n → ι, ∀ k,
        MapsTo (radialCurve x₀) (Icc (t k.castSucc) (t k.succ)) (A.baseSet (c k)) := by
  classical
  let γ : I → ComplexPlane₂ := fun t => radialCurve x₀ t
  have hγ : Continuous γ :=
    (radialCurve_contDiff x₀).continuous.comp continuous_subtype_val
  obtain ⟨t, ht0, htmono, ⟨m, htm⟩, htchart⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i => (A.isOpen_baseSet i).preimage hγ)
      (fun s _ => mem_iUnion.mpr ⟨A.indexAt (γ s), A.mem_baseSet_at (γ s)⟩)
  choose c hc using htchart
  refine ⟨m + 1, Nat.succ_pos m, (fun k => (t k.val : ℝ)), ?_, ?_, ?_,
    (fun k => c k.val), ?_⟩
  · exact congrArg (fun s : I => (s : ℝ)) ht0
  · exact congrArg (fun s : I => (s : ℝ)) (htm (m + 1) (Nat.le_succ m))
  · intro k l hkl
    exact htmono hkl
  · intro k r hr
    change (t k.val : ℝ) ≤ r ∧ r ≤ (t (k.val + 1) : ℝ) at hr
    let s : I := ⟨r, ⟨(t k.val).property.1.trans hr.1,
      hr.2.trans (t (k.val + 1)).property.2⟩⟩
    exact hc k.val (show s ∈ Icc (t k.val) (t (k.val + 1)) from hr)

/-- One compact radial segment stays in its chart for all nearby endpoints. -/
theorem radial_segment_uniform_nhds (i : ι) (a b : ℝ) (x₀ : ComplexPlane₂)
    (hchart : MapsTo (radialCurve x₀) (Icc a b) (A.baseSet i)) :
    ∃ U : Set ComplexPlane₂, IsOpen U ∧ x₀ ∈ U ∧
      ∀ x ∈ U, MapsTo (radialCurve x) (Icc a b) (A.baseSet i) := by
  let O : Set (ComplexPlane₂ × ℝ) := {q | radialCurve q.1 q.2 ∈ A.baseSet i}
  have hOo : IsOpen O :=
    (A.isOpen_baseSet i).preimage (continuous_snd.smul continuous_fst)
  have hKO : ({x₀} ×ˢ Icc a b) ⊆ O := by
    rintro ⟨x, s⟩ ⟨hx, hs⟩
    obtain rfl := mem_singleton_iff.mp hx
    exact hchart hs
  obtain ⟨U, V, hUo, -, hxU, hIV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hOo hKO
  refine ⟨U, hUo, hxU (mem_singleton x₀), ?_⟩
  intro x hx s hs
  exact hUV (show (x, s) ∈ U ×ˢ V from ⟨hx, hIV hs⟩)

/-- The finite collection of compact segments has a single common open
endpoint neighbourhood, with the original breakpoints and chart indices. -/
theorem radial_subdivision_uniform_nhds {n : ℕ} (t : Fin (n + 1) → ℝ)
    (c : Fin n → ι) (x₀ : ComplexPlane₂)
    (hchart : ∀ k,
      MapsTo (radialCurve x₀) (Icc (t k.castSucc) (t k.succ)) (A.baseSet (c k))) :
    ∃ U : Set ComplexPlane₂, IsOpen U ∧ x₀ ∈ U ∧ ∀ x ∈ U, ∀ k,
      MapsTo (radialCurve x) (Icc (t k.castSucc) (t k.succ)) (A.baseSet (c k)) := by
  classical
  choose U hUo hxU hUchart using fun k =>
    radial_segment_uniform_nhds A (c k) (t k.castSucc) (t k.succ) x₀ (hchart k)
  refine ⟨⋂ k, U k, isOpen_iInter_of_finite hUo, mem_iInter.mpr hxU, ?_⟩
  intro x hx k
  exact hUchart k x (mem_iInter.mp hx k)

/-- Monotonicity converts the subdivision's closed intervals into the
unordered interval convention used by actual scalar transport. -/
theorem radial_subdivision_mapsTo_uIcc {n : ℕ} (t : Fin (n + 1) → ℝ)
    (ht : Monotone t) (c : Fin n → ι) (x : ComplexPlane₂)
    (hchart : ∀ k,
      MapsTo (radialCurve x) (Icc (t k.castSucc) (t k.succ)) (A.baseSet (c k)))
    (k : Fin n) :
    MapsTo (radialCurve x) (uIcc (t k.castSucc) (t k.succ)) (A.baseSet (c k)) := by
  rw [uIcc_of_le (ht k.castSucc_le_succ)]
  exact hchart k

/-- Every endpoint has a constructed positive finite subdivision whose
breakpoints and chart indices remain valid on an open neighbourhood. -/
theorem exists_locally_uniform_radial_subdivision (x₀ : ComplexPlane₂) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : Fin (n + 1) → ℝ,
      t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧
      ∃ c : Fin n → ι, ∃ U : Set ComplexPlane₂,
        IsOpen U ∧ x₀ ∈ U ∧ ∀ x ∈ U, ∀ k,
          MapsTo (radialCurve x) (Icc (t k.castSucc) (t k.succ)) (A.baseSet (c k)) := by
  obtain ⟨n, hn, t, ht0, ht1, htm, c, hc⟩ := exists_radial_subdivision A x₀
  obtain ⟨U, hU, hxU, hUc⟩ := radial_subdivision_uniform_nhds A t c x₀ hc
  exact ⟨n, hn, t, ht0, ht1, htm, c, U, hU, hxU, hUc⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalTransport
