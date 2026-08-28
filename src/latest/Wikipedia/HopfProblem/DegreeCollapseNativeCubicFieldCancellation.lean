import Wikipedia.HopfProblem.DegreeCollapseCubicFieldCancellation
import Wikipedia.HopfProblem.DegreeCollapseLocalFieldReplacement

/-!
# Native field-zero cancellation in a thin cubic-axis neighborhood

The compact cutoff is constructed in the supplied original chart. Pullback
and compact replacement give a global smooth native field losing exactly
the two original zeros. A new Morse function is not asserted: that requires
the global no-return and Lyapunov-function construction.
-/

noncomputable section

open Set Filter Function Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {D E M : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem partialChartField_zero_iff
    (Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞) (W : D → D)
    {x : M} (hx : x ∈ Φ.target) :
    FlowConstruction.partialChartField Φ.symm W x = 0 ↔ W (Φ.symm x) = 0 := by
  rw [FlowConstruction.partialChartField_eq_mfderiv_symm Φ.symm W hx]
  have hl : IsLocalDiffeomorphAt 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ Φ (Φ.symm x) :=
    ⟨Φ, Φ.map_target' hx, fun _ _ => rfl⟩
  let A := hl.mfderivToContinuousLinearEquiv (by simp)
  let B : D ≃L[ℝ] TangentSpace 𝓘(ℝ, D) (Φ.symm x) :=
    (NormedSpace.fromTangentSpace (Φ.symm x)).symm
  change A (B (W (Φ.symm x))) = 0 ↔ W (Φ.symm x) = 0
  constructor
  · intro h
    have hb : B (W (Φ.symm x)) = 0 := A.injective (h.trans (map_zero A).symm)
    exact B.injective (hb.trans (map_zero B).symm)
  · intro h
    rw [h, map_zero, map_zero]

variable {m : ℕ} (σ : Fin m → ℝ)

theorem cubicDescent_zero_iff (hσ : ∀ i, σ i ≠ 0) (a : ℝ) (p : Model m) :
    cubicDescent σ (-(a ^ 2)) p = 0 ↔ p = (a, 0) ∨ p = (-a, 0) := by
  rw [← negative_parameter_critical_iff σ hσ a p]
  constructor
  · intro hp
    by_contra hn
    have hh := cubicDescent_strict σ hn
    rw [hp, map_zero] at hh
    exact lt_irrefl _ hh
  · exact cubicDescent_zero_of_critical σ

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- Construct a native field with exactly the two cubic zeros removed.
No new global Lyapunov function is assumed or concluded. -/
theorem exists_native_cubic_field_cancellation_in (hσ : ∀ i, σ i ≠ 0)
    {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x)
    {N : Set M} (hN : IsOpen N)
    (haxisN : ∀ s ∈ Icc (-a) a, Φ (s, 0) ∈ N) :
    ∃ φ : Model m → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Φ.source ∧
      Φ '' tsupport φ ⊆ N ∧
      (∀ p, φ p ∈ Icc (0 : ℝ) 1) ∧ (∀ s ∈ Icc (-a) a, φ (s, 0) = 1) ∧
      ∃ V' : (x : M) → TangentSpace 𝓘(ℝ, E) x,
        ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
          (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x ∈ Φ.target,
          V' x = FlowConstruction.partialChartField Φ.symm (cancelledDescent σ a φ) x) ∧
        (∀ x, V' x = 0 ↔ V x = 0 ∧ x ≠ Φ (a, 0) ∧ x ≠ Φ (-a, 0)) ∧
        ∀ x ∉ Φ '' tsupport φ, ∀ᶠ y in 𝓝 x, V' y = V y := by
  have hopen : IsOpen (Φ.source ∩ Φ ⁻¹' N) :=
    Φ.toOpenPartialHomeomorph.isOpen_inter_preimage hN
  have haxis' : Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source ∩ Φ ⁻¹' N := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact ⟨haxis ⟨hs, rfl⟩, haxisN s hs⟩
  obtain ⟨φ, hφ, hc, hsupp', hrange, hone, hD, hnonzero, hoff⟩ :=
    exists_cubic_field_cancellation σ hσ ha hopen haxis'
  have hsupp : tsupport φ ⊆ Φ.source := fun _ hx => (hsupp' hx).1
  have hsuppN : Φ '' tsupport φ ⊆ N := by
    rintro x ⟨z, hz, rfl⟩
    exact (hsupp' hz).2
  let W := FlowConstruction.partialChartField Φ.symm (cancelledDescent σ a φ)
  have hW : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)) Φ.target :=
    FlowConstruction.contMDiffOn_partialChartField Φ.symm hD
  have hfix (x : M) (hx : x ∈ Φ.target) (hnot : x ∉ Φ '' tsupport φ) : W x = V x := by
    have hinv : Φ.symm x ∉ tsupport φ := fun h => hnot ⟨Φ.symm x, h, Φ.right_inv' hx⟩
    have he := (hoff (Φ.symm x) hinv).eq_of_nhds
    rw [hmodel x hx]
    unfold W nativeCubicDescent FlowConstruction.partialChartField
    simp only [VectorField.mpullback_apply, he]
  have hreg (x : M) (hx : x ∈ Φ.target) : W x ≠ 0 := by
    intro hz
    exact hnonzero _ ((partialChartField_zero_iff Φ (cancelledDescent σ a φ) hx).mp hz)
  obtain ⟨V', hV', heq, hzero, hkeep⟩ :=
    LocalFieldReplacement.exists_smooth_field_replacement Φ V W hV hW hc hsupp hfix hreg
  have hp : (a, (0 : Fin m → ℝ)) ∈ Φ.source := haxis ⟨⟨by linarith, le_rfl⟩, rfl⟩
  have hq : (-a, (0 : Fin m → ℝ)) ∈ Φ.source := haxis ⟨⟨le_rfl, by linarith⟩, rfl⟩
  refine ⟨φ, hφ, hc, hsupp, hsuppN, hrange, hone, V', hV', heq, ?_, hkeep⟩
  intro x
  rw [hzero x]
  constructor
  · rintro ⟨hx, hout⟩
    exact ⟨hx, fun he => hout (he ▸ Φ.map_source' hp),
      fun he => hout (he ▸ Φ.map_source' hq)⟩
  · rintro ⟨hx, hxp, hxq⟩
    refine ⟨hx, ?_⟩
    intro hxt
    have hz : FlowConstruction.partialChartField Φ.symm (cubicDescent σ (-(a ^ 2))) x = 0 :=
      (hmodel x hxt).symm.trans hx
    have hd := (partialChartField_zero_iff Φ (cubicDescent σ (-(a ^ 2))) hxt).mp hz
    rcases (cubicDescent_zero_iff σ hσ a (Φ.symm x)).mp hd with hh | hh
    · exact hxp ((Φ.right_inv' hxt).symm.trans (congrArg Φ hh))
    · exact hxq ((Φ.right_inv' hxt).symm.trans (congrArg Φ hh))

/-- The unrestricted neighborhood version retains the original cancellation interface. -/
theorem exists_native_cubic_field_cancellation (hσ : ∀ i, σ i ≠ 0)
    {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) :
    ∃ φ : Model m → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Φ.source ∧
      (∀ p, φ p ∈ Icc (0 : ℝ) 1) ∧ (∀ s ∈ Icc (-a) a, φ (s, 0) = 1) ∧
      ∃ V' : (x : M) → TangentSpace 𝓘(ℝ, E) x,
        ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
          (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x ∈ Φ.target,
          V' x = FlowConstruction.partialChartField Φ.symm (cancelledDescent σ a φ) x) ∧
        (∀ x, V' x = 0 ↔ V x = 0 ∧ x ≠ Φ (a, 0) ∧ x ≠ Φ (-a, 0)) ∧
        ∀ x ∉ Φ '' tsupport φ, ∀ᶠ y in 𝓝 x, V' y = V y := by
  obtain ⟨φ, hφ, hc, hsupp, -, hrange, hone, hrest⟩ :=
    exists_native_cubic_field_cancellation_in σ hσ ha Φ haxis V hV hmodel
      isOpen_univ (fun _ _ => mem_univ _)
  exact ⟨φ, hφ, hc, hsupp, hrange, hone, hrest⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
