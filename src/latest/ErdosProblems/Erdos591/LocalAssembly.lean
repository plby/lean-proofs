import ErdosProblems.Erdos591.EMStepOracle
import ErdosProblems.Erdos591.PieceIndiv

open Cardinal Ordinal

namespace Erdos591.LocalAssembly

universe u

/-- The exponent occurring in the local target block. -/
abbrev exp (n : ℕ) : Ordinal.{0} := ω * (n + 1 : ℕ)

/-- The local target and source ordinals. -/
noncomputable abbrev target (n : ℕ) : Ordinal.{0} := ω ^ exp n
noncomputable abbrev source (n : ℕ) : Ordinal.{0} := ω ^ (exp n * 2)

theorem exp_add_self (n : ℕ) : exp n + exp n = exp n * 2 := by
  calc
    exp n + exp n = exp n * 1 + exp n * 1 := by simp
    _ = exp n * (1 + 1) := (mul_add _ _ _).symm
    _ = exp n * 2 := by norm_num

theorem source_eq_target_mul_target (n : ℕ) :
    source n = target n * target n := by
  rw [← Ordinal.opow_add, exp_add_self]

theorem one_add_exp (n : ℕ) : (1 : Ordinal.{0}) + exp n = exp n := by
  apply Ordinal.add_of_omega0_le Ordinal.one_lt_omega0
  simpa [exp] using
    (Ordinal.mul_le_mul_left (a := (1 : Ordinal.{0}))
      (b := (n + 1 : ℕ)) (c := ω) (by simp))

theorem omega_mul_target (n : ℕ) :
    (ω : Ordinal.{0}) * target n = target n := by
  calc
    (ω : Ordinal.{0}) * target n = ω ^ ((1 : Ordinal.{0}) + exp n) := by
      rw [Ordinal.opow_one_add]
    _ = target n := by rw [one_add_exp]

/-- A copy of `target n * target n` in `source n`, split into consecutive
`target n`-blocks. -/
noncomputable def initialBlocks (n : ℕ) :
    Erdos591.StrongIteration.BlockFamily
      (target n).ToType (target n).ToType (source n).ToType := by
  let L := (target n).ToType ×ₗ (target n).ToType
  have htype : typeLT L = typeLT (source n).ToType := by
    change Ordinal.type
      (Prod.Lex ((· < ·) : (target n).ToType → (target n).ToType → Prop)
        ((· < ·) : (target n).ToType → (target n).ToType → Prop)) = _
    rw [Ordinal.type_prod_lex, Ordinal.type_toType, Ordinal.type_toType,
      ]
    exact (source_eq_target_mul_target n).symm
  let relIso :
      ((· < ·) : L → L → Prop) ≃r
        ((· < ·) : (source n).ToType → (source n).ToType → Prop) :=
    Classical.choice (Ordinal.type_eq.mp htype)
  let whole : L ↪o (source n).ToType :=
    OrderEmbedding.ofStrictMono relIso (fun _ _ h ↦ relIso.map_rel_iff.mpr h)
  refine
    { embedding := fun b ↦ OrderEmbedding.ofStrictMono
        (fun y ↦ whole (toLex (b, y))) ?_
      separated := ?_ }
  · intro y z hyz
    apply whole.strictMono
    exact Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, hyz⟩)
  · intro b c hbc y z
    apply whole.strictMono
    exact Prod.Lex.lt_iff.mpr (Or.inl hbc)

/-- Turn a blue-independent order embedding into the red-set alternative. -/
theorem red_set_of_embedding {α β : Ordinal.{u}}
    (red blue : SimpleGraph α.ToType) (hcompl : IsCompl red blue)
    (e : β.ToType ↪o α.ToType)
    (he : ∀ x y, x ≠ y → ¬ blue.Adj (e x) (e y)) :
    ∃ S : Set α.ToType, red.IsClique S ∧ typeLT S = β := by
  let S : Set α.ToType := Set.range e
  refine ⟨S, ?_, ?_⟩
  · apply Erdos590.Larson.clique_of_no_blue_triangle red blue hcompl
    intro x hx y hy hxy
    rcases hx with ⟨a, rfl⟩
    rcases hy with ⟨b, rfl⟩
    apply he a b
    exact fun hab ↦ hxy (congrArg e hab)
  · have htype : typeLT β.ToType = typeLT S :=
      OrderIso.ordinalType_congr e.orderIso
    simpa [Ordinal.type_toType] using htype.symm

theorem cliqueFree_four_of_no_cardinal_clique {X : Type}
    (blue : SimpleGraph X)
    (h : ¬ ∃ S : Set X, blue.IsClique S ∧ #S = 4) :
    blue.CliqueFree 4 := by
  intro t ht
  apply h
  refine ⟨(t : Set X), ht.1, ?_⟩
  let e : (t : Set X) ≃ (t : Type) :=
    Equiv.setCongr (by ext x; simp)
  calc
    #(t : Set X) = #(t : Type) := Cardinal.mk_congr e
    _ = (t.card : Cardinal) := Cardinal.mk_coe_finset
    _ = 4 := by exact_mod_cast ht.2

theorem no_compl_large_of_no_embedding {B X : Type}
    [LinearOrder B] [LinearOrder X]
    (blue : SimpleGraph X)
    (h : Erdos591.StrongIteration.NoRedBCopy (B := B) blue) :
    ¬ ∃ S : Set X, blueᶜ.IsClique S ∧
      Erdos591.Schipperus.K4Core.Large B S := by
  rintro ⟨S, hS, ⟨f⟩⟩
  apply h
  let e : B ↪o X := f.trans (OrderEmbedding.subtype S)
  refine ⟨e, ?_⟩
  intro b c hbc
  have heq : e b ≠ e c := fun h' ↦ hbc (e.injective h')
  have hc : blueᶜ.Adj (e b) (e c) :=
    hS (f b).2 (f c).2 heq
  exact (blue.compl_adj (e b) (e c)).mp hc |>.2

/-- Exact local Erdős--Milner assembly.  The only nonstructural input is
the one-step oracle; the rest is the checked countable fusion and ordinal
arithmetic. -/
theorem local_four_of_step_oracle (n : ℕ)
    (localStepOracle :
      ∀ (blue : SimpleGraph (source n).ToType),
        Erdos591.StrongIteration.NoBlueK4 blue →
        Erdos591.StrongIteration.NoRedBCopy
          (B := (target n).ToType) blue →
        Erdos591.StrongIteration.StepOracle
          (B := (target n).ToType)
          (Y := (target n).ToType) blue) :
    OrdinalCardinalRamsey (source n) (target n) 4 := by
  intro red blue hcompl
  by_cases hK4 : ∃ S : Set (source n).ToType,
      blue.IsClique S ∧ #S = 4
  · exact Or.inr hK4
  · apply Or.inl
    by_cases hDirect : ∃ e : (target n).ToType ↪o (source n).ToType,
        ∀ b c, b ≠ c → ¬ blue.Adj (e b) (e c)
    · rcases hDirect with ⟨e, he⟩
      exact red_set_of_embedding red blue hcompl e he
    · have hOracle := localStepOracle blue hK4 hDirect
      let : Countable (target n).ToType :=
        Cardinal.mk_le_aleph0_iff.mp (by
          rw [Cardinal.mk_toType, Ordinal.card_omega0_opow]
          · apply max_le le_rfl
            rw [Ordinal.card_mul, Ordinal.card_omega0, Ordinal.card_nat,
              Cardinal.aleph0_mul_nat (by omega : n + 1 ≠ 0)]
          · apply mul_ne_zero Ordinal.omega0_ne_zero
            norm_num)
      let : Nonempty (target n).ToType :=
        Ordinal.nonempty_toType_iff.mpr
          (Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero)
      rcases Erdos591.StrongIteration.exists_orderEmbedding_not_adj blue hOracle
          (initialBlocks n) with ⟨e, he⟩
      let relIso :
          ((· < ·) : (target n).ToType → (target n).ToType → Prop) ≃r
            ((· < ·) : Erdos591.StrongIteration.Fiber (target n).ToType →
              Erdos591.StrongIteration.Fiber (target n).ToType → Prop) := by
        have htype : typeLT (target n).ToType =
            typeLT (Erdos591.StrongIteration.Fiber (target n).ToType) := by
          rw [Erdos591.StrongIteration.typeLT_fiber, Ordinal.type_toType, omega_mul_target,
            ]
        exact Classical.choice (Ordinal.type_eq.mp htype)
      let intoFiber : (target n).ToType ↪o
          Erdos591.StrongIteration.Fiber (target n).ToType :=
        OrderEmbedding.ofStrictMono relIso
          (fun _ _ h ↦ relIso.map_rel_iff.mpr h)
      let finalEmbedding : (target n).ToType ↪o (source n).ToType :=
        intoFiber.trans e
      apply red_set_of_embedding red blue hcompl finalEmbedding
      intro x y hxy
      apply he
      exact fun h ↦ hxy (intoFiber.injective h)

/-- Exact local Erdős--Milner relation derived from Chang's
`ω^ω → (ω^ω,3)²` relation. -/
theorem local_four_of_em_inputs (n : ℕ)
    (h590 : OrdinalCardinalRamsey
      (ω ^ ω : Ordinal.{0}) (ω ^ ω : Ordinal.{0}) 3) :
    OrdinalCardinalRamsey (source n) (target n) 4 := by
  let : Nonempty (target n).ToType :=
    Ordinal.nonempty_toType_iff.mpr
      (Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero)
  have hlim : Order.IsSuccLimit (typeLT (target n).ToType) := by
    rw [Ordinal.type_toType]
    exact Erdos591.Schipperus.PieceIndiv.localTarget_isSuccLimit n
  have hindY : Erdos591.Schipperus.K4Core.FinitelyIndivisible
      (target n).ToType := by
    apply Erdos591.Schipperus.PieceIndiv.omegaPower_finitelyIndivisible_of_le
      h590 (exp n) (n + 1)
    · exact Ordinal.type_toType _
    · exact le_rfl
  apply local_four_of_step_oracle n
  intro blue hK4 hNoRed
  exact Erdos591.Schipperus.EMStepOracle.stepOracle_of_k4_core
    (exp n) (by rw [Ordinal.type_toType]) hindY
    (fun e hP he ↦
      Erdos591.Schipperus.PieceIndiv.omegaPower_finitelyIndivisible_of_le
        h590 e (n + 1) hP he)
    (Erdos591.Schipperus.PieceIndiv.not_large_Iic_of_isSuccLimit hlim)
    (Erdos591.Schipperus.PieceIndiv.singleton_not_large_of_isSuccLimit hlim)
    blueᶜ blue
    (isCompl_compl.symm : IsCompl blueᶜ blue)
    (no_compl_large_of_no_embedding blue hNoRed)
    (cliqueFree_four_of_no_cardinal_clique blue hK4)

end Erdos591.LocalAssembly
