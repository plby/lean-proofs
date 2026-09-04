import ErdosProblems.Erdos157.WindowFailure
import ErdosProblems.Erdos157.UniformProducts
import ErdosProblems.Erdos157.MaskSelection
import ErdosProblems.Erdos157.SidonEncoding

/-! The final countable-product choice and conversion to an asymptotic basis. -/

namespace Erdos157.Elementary

open AuxiliaryModuli Filter

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

noncomputable def parametersFromLevels (ξ : ∀ k, LevelParameters K k) : IntegerParameters K where
  block f i := if hi : i < f.level then (ξ f.level f.2).1 ⟨i, hi⟩ else Classical.choice (blockChoiceNonempty i)
  top f := (ξ f.level f.2).2

theorem localValue_parametersFromLevels (τ : MaskChoice K) (ξ : ∀ k, LevelParameters K k)
    (k : ℕ) (hk : 400 ≤ k) (f : LevelLabel K k) :
    localValue K τ k f (ξ k f) =
      encoded K τ (parametersFromLevels K ξ) ⟨⟨k, hk⟩, f⟩ := by
  apply localValue_eq_encoded K τ (parametersFromLevels K ξ) ⟨⟨k, hk⟩, f⟩ (ξ k f)
  · intro i
    change Fin k at i
    change (if hi : i.1 < k then (ξ k f).1 ⟨i.1, hi⟩ else Classical.choice (blockChoiceNonempty i)) = _
    rw [dif_pos i.2]
  · rfl

theorem locallyRepresented_mem_tripleSumset (τ : MaskChoice K) (ξ : ∀ k, LevelParameters K k)
    (k m : ℕ) (hk : 400 ≤ k) (hm : LocallyRepresented K τ k (ξ k) m) :
    m ∈ TripleSumset (encodedSet K τ (parametersFromLevels K ξ)) := by
  obtain ⟨f₁, f₂, f₃, he⟩ := hm
  have hmem (f : LevelLabel K k) : localValue K τ k f (ξ k f) ∈
      encodedSet K τ (parametersFromLevels K ξ) :=
    ⟨⟨⟨k, hk⟩, f⟩, (localValue_parametersFromLevels K τ ξ k hk f).symm⟩
  exact ⟨_, hmem f₁, _, hmem f₂, _, hmem f₃, he.symm⟩

theorem encoded_basis_of_eventual_windows (τ : MaskChoice K) (ξ : ∀ k, LevelParameters K k)
    (hcover : ∀ᶠ k in atTop, ∀ m, 6 * blockPlace K 0 k ≤ m →
      m < 6 * blockPlace K 0 (k + 1) → LocallyRepresented K τ k (ξ k) m) :
    IsAsymptoticBasisOfOrderThree (encodedSet K τ (parametersFromLevels K ξ)) := by
  apply (isAsymptoticBasisOfOrderThree_iff_eventually _).mpr
  have hlevels := (tendsto_targetLevel K).eventually (hcover.and (eventually_ge_atTop 400))
  filter_upwards [hlevels, eventually_ge_atTop 6] with m hm h6
  have hw := targetLevel_window K m h6
  exact locallyRepresented_mem_tripleSumset K τ ξ (targetLevel K m) m hm.2 (hm.1 m hw.1 hw.2)

theorem exists_eventually_covering_levels (τ : MaskChoice CoefficientField)
    (hτ : ∀ᶠ k in atTop, ∀ z : MaskTarget CoefficientField k,
      MaskTargetHit CoefficientField (fun i => τ i) z) :
    ∃ ξ : ∀ k, LevelParameters CoefficientField k,
      ∀ᶠ k in atTop, ∀ m, 6 * blockPlace CoefficientField 0 k ≤ m →
        m < 6 * blockPlace CoefficientField 0 (k + 1) →
        LocallyRepresented CoefficientField τ k (ξ k) m := by
  classical
  let X (k : ℕ) := LevelParameters CoefficientField k
  let (k : ℕ) : MeasurableSpace (X k) := ⊤
  let (k : ℕ) : DiscreteMeasurableSpace (X k) := ⟨fun _ => trivial⟩
  let μ := UniformProducts.productMeasure X
  let bad (k : ℕ) : Set (∀ k, X k) := {ξ | WindowFailure τ k (ξ k)}
  have hbad : ∀ᶠ k in atTop, μ.real (bad k) ≤ Real.exp (-(k : ℝ)) := by
    filter_upwards [eventually_window_failure_density τ hτ] with k hk
    have he := UniformProducts.coordinate_density X k (WindowFailure τ k)
    exact he.trans_le hk
  obtain ⟨ξ, hξ⟩ := exists_eventually_avoiding_events μ bad (fun k => Real.exp (-(k : ℝ)))
    Real.summable_exp_neg_nat hbad
  refine ⟨ξ, hξ.mono ?_⟩
  intro k hk m hlo hhi
  by_contra h
  exact hk ⟨⟨m, hhi⟩, hlo, h⟩

theorem exists_encoded_asymptoticBasis :
    ∃ τ : MaskChoice CoefficientField, ∃ ω : IntegerParameters CoefficientField,
      IsAsymptoticBasisOfOrderThree (encodedSet CoefficientField τ ω) := by
  obtain ⟨τ, hτ⟩ := exists_eventually_good_masks CoefficientField
  obtain ⟨ξ, hξ⟩ := exists_eventually_covering_levels τ hτ
  exact ⟨τ, parametersFromLevels CoefficientField ξ,
    encoded_basis_of_eventual_windows CoefficientField τ ξ hξ⟩

end Erdos157.Elementary
