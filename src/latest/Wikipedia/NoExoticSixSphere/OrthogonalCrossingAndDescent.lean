import Wikipedia.NoExoticSixSphere.OrthogonalPrescribedThresholdCrossing
import Wikipedia.NoExoticSixSphere.OrthogonalSupportedBandDeformation
import Wikipedia.NoExoticSixSphere.OrthogonalCriticalEnergyIsolation

/-!
# Combining a localized crossing with descent below the critical level

The selected compact parameter set ends in a prescribed lower sublevel.
Every parameter already in that sublevel stays there throughout the combined
homotopy. A still lower sublevel is fixed pointwise, as are points outside the
crossing neighborhood whose original energy is at least the critical energy.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization OrthogonalVertexSpace

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] {n m : ℕ}

include I

theorem exists_crossing_and_descent (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ shortDomain a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (habove : (n : ℝ) * Real.pi ^ 2 < energy a b τ v)
    (N : Set (Space n m)) (hN : IsOpen N) (hvN : v ∈ N)
    (l₀ l ε : ℝ) (hl₀ : l₀ < l) (hl : l < energy a b τ v) (hε : 0 < ε)
    (hcompact : IsCompact (energySublevel a b τ (energy a b τ v)))
    (hFloor : energy a b τ v - 8 * Real.pi ^ 2 < l₀)
    (hd : finrank ℝ B + 2 < n) :
    ∃ V : Set (Space n m), IsOpen V ∧ v ∈ V ∧ V ⊆ admissible a b m ∩ N ∧
      ∀ (p : C(M, Space n m)), (∀ x, p x ∈ admissible a b m) →
        ∀ (K : Set M), IsCompact K → K ⊆ p ⁻¹' V →
          ∃ q : C(M, Space n m), (∀ x ∈ K, energy a b τ (q x) ≤ l) ∧
            ∃ G : ContinuousMap.HomotopyRel p q
              ({x | energy a b τ (p x) ≤ l₀} ∪
                ((p ⁻¹' V)ᶜ ∩ {x | energy a b τ v ≤ energy a b τ (p x)})),
              ∀ t x, G (t, x) ∈ admissible a b m ∧
                energy a b τ (G (t, x)) ≤ max (energy a b τ (p x)) (energy a b τ v + ε) ∧
                (energy a b τ (p x) ≤ l → energy a b τ (G (t, x)) ≤ l) := by
  obtain ⟨V, hV, hvV, hVsub, -, k, hlk, hk, hcross⟩ :=
    exists_crossing_fixing_sublevel (I := I) (M := M) a b τ hτ hzero hone v hv hcrit hanti
      habove N hN hvN l ε hl hε hd
  let u := (k + energy a b τ v) / 2
  let E := (u + energy a b τ v) / 2
  have hku : k < u := by dsimp [u]; linarith
  have huC : u < energy a b τ v := by dsimp [u]; linarith
  have huE : u < E := by dsimp [E]; linarith
  have hEC : E < energy a b τ v := by dsimp [E]; linarith
  have hEcompact := isCompact_energySublevel_of_le a b τ hEC.le hcompact
  have hNoncrit : ∀ z ∈ energyBand a b τ l₀ E,
      mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) z ≠ 0 :=
    fun z hz ↦ noncritical_below_critical_energy a b τ hτ hzero hone hanti v hv.1 hcrit
      z hz.1.1 (hFloor.trans_le hz.2) (hz.1.2.trans_lt hEC)
  refine ⟨V, hV, hvV, hVsub, ?_⟩
  intro p hp K hK hKV
  obtain ⟨q, hqK, G₁, hG₁⟩ := hcross p hp K hK hKV
  have hqAdm (x) : q x ∈ admissible a b m := by
    simpa only [G₁.apply_one] using (hG₁ 1 x).1
  obtain ⟨r, G₂, hG₂, hr⟩ := exists_supported_band_family a b τ l₀ l k u E hl₀ hku huE
    hEcompact hNoncrit q hqAdm
  let S := {x | energy a b τ (p x) ≤ l₀} ∪
    ((p ⁻¹' V)ᶜ ∩ {x | energy a b τ v ≤ energy a b τ (p x)})
  have hS₁ : S ⊆ {x | energy a b τ (p x) ≤ l} ∪ (p ⁻¹' V)ᶜ := by
    intro x hx
    exact hx.elim (fun h ↦ Or.inl (h.trans hl₀.le)) (fun h ↦ Or.inr h.1)
  have hqEq {x} (hx : x ∈ S) : q x = p x := (G₁.fst_eq_snd (hS₁ hx)).symm
  let H₁ : ContinuousMap.HomotopyRel p q S :=
    { toHomotopy := G₁.toHomotopy
      prop' := fun t x hx ↦ G₁.eq_fst t (hS₁ hx) }
  let H₂ : ContinuousMap.HomotopyRel q r S :=
    { toHomotopy := G₂.toHomotopy
      prop' := fun t x hx ↦ G₂.eq_fst t (by
        change energy a b τ (q x) ≤ l₀ ∨ u ≤ energy a b τ (q x)
        rw [hqEq hx]
        exact hx.elim Or.inl (fun h ↦ Or.inr (huC.le.trans h.2))) }
  have hqCap (x) : energy a b τ (q x) ≤ max (energy a b τ (p x)) (energy a b τ v + ε) := by
    simpa only [G₁.apply_one] using (hG₁ 1 x).2.1
  have hqLow {x} (hx : energy a b τ (p x) ≤ l) : q x = p x :=
    (G₁.fst_eq_snd (Or.inl hx)).symm
  refine ⟨r, fun x hx ↦ hr x (hqK x hx).le, H₁.trans H₂, fun t x ↦ ?_⟩
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split_ifs
  · refine ⟨(hG₁ _ x).1, (hG₁ _ x).2.1, ?_⟩
    intro hx
    change energy a b τ (G₁ (_, x)) ≤ l
    rw [G₁.eq_fst _ (Or.inl hx)]
    exact hx
  · refine ⟨(hG₂ _ x).1, (hG₂ _ x).2.trans (hqCap x), ?_⟩
    intro hx
    exact ((hG₂ _ x).2.trans_eq (congrArg (energy a b τ) (hqLow hx))).trans hx

end NoExoticSixSphere.OrthogonalPolygon
