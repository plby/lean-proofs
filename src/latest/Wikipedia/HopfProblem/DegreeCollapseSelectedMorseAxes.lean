import Wikipedia.HopfProblem.DegreeCollapseSignedMorseFieldEndpoints
import Wikipedia.HopfProblem.DegreeCollapseMorseBlockAlignment

/-!
# Selected Morse axes aligned with arbitrary nonzero endpoint rays

The selected coordinate is a nonzero vector in precisely the block given
by its sign. Actual block reflections align its outgoing positive ray or
incoming negative ray with any prescribed nonzero endpoint vector, while
retaining the exact linear-to-Morse field conjugacy.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}

open ManifoldMorse

open Classical in
theorem selectedMorseFieldEquiv_axis_ne_zero (c : SignedMorseChart (E := E) f x)
    {m : ℕ} (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) :
    selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ)) ≠ 0 := by
  intro h
  have hh := (selectedMorseFieldEquiv c ρ).injective
    (h.trans (map_zero (selectedMorseFieldEquiv c ρ)).symm)
  have h1 := congrArg Prod.fst hh
  norm_num at h1

open Classical in
theorem selectedMorseFieldEquiv_negative_axis (c : SignedMorseChart (E := E) f x)
    {m : ℕ} (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ none) = -1) :
    (selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))).2 = 0 ∧
      (selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))).1 ≠ 0 := by
  let z := selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))
  have hw : endpointLinearField (fun i => c.weights (ρ (some i))) (1 / 2)
      (c.weights (ρ none)) (1, (0 : Fin m → ℝ)) = (1, 0) := by
    ext i <;> simp [endpointLinearField, he]
  have hh := selectedMorseFieldEquiv_descent c ρ (1, (0 : Fin m → ℝ))
  rw [hw] at hh
  have h2 : z.2 = -z.2 := congrArg Prod.snd hh
  have hs : (2 : ℝ) • z.2 = 0 := by
    rw [two_smul]
    exact (congrArg (fun v => v + z.2) h2).trans (neg_add_cancel z.2)
  have hz : z.2 = 0 := (smul_eq_zero.mp hs).resolve_left (by norm_num)
  refine ⟨hz, ?_⟩
  intro h1
  exact selectedMorseFieldEquiv_axis_ne_zero c ρ (Prod.ext h1 hz)

open Classical in
theorem selectedMorseFieldEquiv_positive_axis (c : SignedMorseChart (E := E) f x)
    {m : ℕ} (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ none) = 1) :
    (selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))).1 = 0 ∧
      (selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))).2 ≠ 0 := by
  let z := selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))
  have hw : endpointLinearField (fun i => c.weights (ρ (some i))) (1 / 2)
      (c.weights (ρ none)) (1, (0 : Fin m → ℝ)) = -(1, 0) := by
    ext i <;> simp [endpointLinearField, he]
  have hh := selectedMorseFieldEquiv_descent c ρ (1, (0 : Fin m → ℝ))
  rw [hw, map_neg] at hh
  have h1 : z.1 = -z.1 := (congrArg Prod.fst hh).symm
  have hs : (2 : ℝ) • z.1 = 0 := by
    rw [two_smul]
    exact (congrArg (fun v => v + z.1) h1).trans (neg_add_cancel z.1)
  have hz : z.1 = 0 := (smul_eq_zero.mp hs).resolve_left (by norm_num)
  refine ⟨hz, ?_⟩
  intro h2
  exact selectedMorseFieldEquiv_axis_ne_zero c ρ (Prod.ext hz h2)

open Classical in
/-- The outgoing positive scalar ray is aligned with the prescribed negative-block vector. -/
theorem exists_selected_outgoing_axis (c : SignedMorseChart (E := E) f x)
    {m : ℕ} (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ none) = -1)
    {v : c.NegativeCoordinates} (hv : v ≠ 0) :
    ∃ (r : ℝ) (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates)),
      0 < r ∧ L (r, 0) = (v, 0) ∧
      ∀ p, L (endpointLinearField (fun i => c.weights (ρ (some i))) (1 / 2)
        (c.weights (ρ none)) p) = MorseHandle.descent (L p) := by
  let L₀ := selectedMorseFieldEquiv c ρ
  obtain ⟨hz, hn⟩ := selectedMorseFieldEquiv_negative_axis c ρ he
  obtain ⟨r, A, hr, hA, _⟩ := exists_positive_ray_alignment hn hv
  let B := A.toContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ c.PositiveCoordinates)
  let L := L₀.trans B
  refine ⟨r, L, hr, ?_, ?_⟩
  · have hp : (r, (0 : Fin m → ℝ)) = r • (1, 0) := by simp
    rw [hp, L.map_smul]
    apply Prod.ext
    · change r • A ((L₀ (1, 0)).1) = v
      rw [← A.map_smul]
      exact hA
    · change r • (L₀ (1, 0)).2 = 0
      rw [hz, smul_zero]
  · intro p
    change B (L₀ _) = MorseHandle.descent (B (L₀ p))
    rw [selectedMorseFieldEquiv_descent]
    exact morse_block_change_descent _ _ _

open Classical in
/-- The incoming negative scalar ray is aligned with the prescribed positive-block vector. -/
theorem exists_selected_incoming_axis (c : SignedMorseChart (E := E) f x)
    {m : ℕ} (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ none) = 1)
    {v : c.PositiveCoordinates} (hv : v ≠ 0) :
    ∃ (r : ℝ) (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates)),
      0 < r ∧ L (-r, 0) = (0, v) ∧
      ∀ p, L (endpointLinearField (fun i => c.weights (ρ (some i))) (1 / 2)
        (c.weights (ρ none)) p) = MorseHandle.descent (L p) := by
  let L₀ := selectedMorseFieldEquiv c ρ
  obtain ⟨hz, hn⟩ := selectedMorseFieldEquiv_positive_axis c ρ he
  obtain ⟨r, A, hr, hA, _⟩ := exists_positive_ray_alignment hn (neg_ne_zero.mpr hv)
  let B := (ContinuousLinearEquiv.refl ℝ c.NegativeCoordinates).prodCongr A.toContinuousLinearEquiv
  let L := L₀.trans B
  refine ⟨r, L, hr, ?_, ?_⟩
  · have hp : (-r, (0 : Fin m → ℝ)) = (-r) • (1, 0) := by simp
    rw [hp, L.map_smul]
    apply Prod.ext
    · change (-r) • (L₀ (1, 0)).1 = 0
      rw [hz, smul_zero]
    · change (-r) • A ((L₀ (1, 0)).2) = v
      rw [neg_smul, ← A.map_smul, hA, neg_neg]
  · intro p
    change B (L₀ _) = MorseHandle.descent (B (L₀ p))
    rw [selectedMorseFieldEquiv_descent]
    exact morse_block_change_descent _ _ _

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
