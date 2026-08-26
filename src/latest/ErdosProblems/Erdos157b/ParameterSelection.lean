import ErdosProblems.Erdos157b.WindowDecay
import ErdosProblems.Erdos157b.JointChoices
import ErdosProblems.Erdos157b.SidonEncoding

/-! One countable product choice gives a Sidon asymptotic basis over the binary field. -/

namespace Erdos157.Binary

open Elementary Filter

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


theorem exists_encoded_asymptoticBasis :
    ∃ τ : MaskChoice CoefficientField, ∃ ω : IntegerParameters CoefficientField,
      IsAsymptoticBasisOfOrderThree (encodedSet CoefficientField τ ω) := by
  classical
  let A (i : ℕ) := TagField i → LogDigit CoefficientField i
  let B (i : ℕ) := LevelParameters CoefficientField i
  let X (i : ℕ) := A i × B i
  letI (i : ℕ) : MeasurableSpace (X i) := ⊤
  letI (i : ℕ) : DiscreteMeasurableSpace (X i) := ⟨fun _ => trivial⟩
  let μ := UniformProducts.productMeasure X
  let bad (k : ℕ) : Set (∀ i, X i) :=
    {x | JointWindowFailure k (fun i : Fin k => (x i).1, (x k).2)}
  have hbad : ∀ᶠ k in atTop, μ.real (bad k) ≤ 2 * Real.exp (-(k : ℝ)) := by
    filter_upwards [eventually_joint_window_failure] with k hk
    have he := joint_cylinder_density A B k (JointWindowFailure k)
    exact he.trans_le hk
  have hsum : Summable (fun k : ℕ => 2 * Real.exp (-(k : ℝ))) :=
    Real.summable_exp_neg_nat.mul_left 2
  obtain ⟨x, hx⟩ := exists_eventually_avoiding_events μ bad
    (fun k => 2 * Real.exp (-(k : ℝ))) hsum hbad
  let τ : MaskChoice CoefficientField := fun i => (x i).1
  let ξ : ∀ k, LevelParameters CoefficientField k := fun k => (x k).2
  refine ⟨τ, parametersFromLevels CoefficientField ξ, ?_⟩
  apply encoded_basis_of_eventual_windows CoefficientField τ ξ
  filter_upwards [hx] with k hk
  intro m hlo hhi
  have hlocal : LocallyRepresented CoefficientField
      (extendLevelMasks CoefficientField (fun i : Fin k => (x i).1)) k (x k).2 m := by
    by_contra h
    exact hk ⟨⟨m, hhi⟩, hlo, h⟩
  apply (locallyRepresented_congr_masks CoefficientField
    (extendLevelMasks CoefficientField (fun i : Fin k => (x i).1)) τ k
    (fun i => congrFun (extendLevelMasks_prefix CoefficientField
      (fun i : Fin k => (x i).1)) i) (ξ k) m).mp
  exact hlocal

end Erdos157.Binary
