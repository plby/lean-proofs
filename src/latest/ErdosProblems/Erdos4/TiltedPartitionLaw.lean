import ErdosProblems.Erdos4.TiltedCappedLaw
import ErdosProblems.Erdos4.TiltedLabelLaw
import ErdosProblems.Erdos4.TiltedBlocks

/-! Uniform block laws retain every fiber block, including the final short block. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT

noncomputable def partitionRoot {C : Finset ℕ} (P : Finpartition C) (v : C) : P.parts :=
  ⟨P.part v.val, P.part_mem.mpr v.property⟩

theorem part_count_pos {C : Finset ℕ} (P : Finpartition C) (hC : C.Nonempty) : 0 < P.parts.card := by
  obtain ⟨v, hv⟩ := hC
  exact Finset.card_pos.mpr ⟨P.part v, P.part_mem.mpr hv⟩

noncomputable def uniformPartLaw {C : Finset ℕ} (P : Finpartition C) (hC : C.Nonempty) :
    FiniteLaw P.parts where
  weight _ := 1 / (P.parts.card : ℝ)
  nonneg _ := by positivity
  total := by
    obtain ⟨v, hv⟩ := hC
    have hP : P.parts.Nonempty := ⟨P.part v, P.part_mem.mpr hv⟩
    have hP0 : (P.parts.card : ℝ) ≠ 0 := by exact_mod_cast hP.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    field_simp

theorem uniformPartLaw_weight {C : Finset ℕ} (P : Finpartition C) (hC : C.Nonempty) (E : P.parts) :
    (uniformPartLaw P hC).weight E = 1 / (P.parts.card : ℝ) := rfl

theorem uniformPartLaw_mean {C : Finset ℕ} (P : Finpartition C) (hC : C.Nonempty) (f : P.parts → ℝ) :
    (uniformPartLaw P hC).mean f = (∑ E, f E) / (P.parts.card : ℝ) := by
  simp only [FiniteLaw.mean, uniformPartLaw_weight, one_div]
  rw [← Finset.mul_sum]
  ring

theorem sum_partitionRoots {C : Finset ℕ} (P : Finpartition C) (f : P.parts → ℝ) :
    (∑ v : C, f (partitionRoot P v)) = ∑ E : P.parts, (E.val.card : ℝ) * f E := by
  classical
  calc
    _ = ∑ z : (Σ E : P.parts, E.val), f z.1 :=
      P.equivSigmaParts.sum_comp (fun z => f z.1)
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

theorem weighted_sum_partitionRoots_le {C : Finset ℕ} (P : Finpartition C)
    (f : P.parts → ℝ) (hf : ∀ E, 0 ≤ f E) (q : C → ℝ) {Q : ℝ} (hQ : 0 ≤ Q)
    (hq : ∀ v, q v ≤ Q) {K : ℕ} (hK : ∀ E ∈ P.parts, E.card ≤ K) :
    (∑ v : C, q v * f (partitionRoot P v)) ≤ Q * K * ∑ E : P.parts, f E := by
  calc
    _ ≤ ∑ v : C, Q * f (partitionRoot P v) :=
      Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_right (hq v) (hf _))
    _ = Q * ∑ E : P.parts, (E.val.card : ℝ) * f E := by
      rw [← Finset.mul_sum, sum_partitionRoots]
    _ ≤ Q * ∑ E : P.parts, (K : ℝ) * f E := by
      apply mul_le_mul_of_nonneg_left _ hQ
      exact Finset.sum_le_sum (fun E _ => mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (hK E.val E.property)) (hf E))
    _ = _ := by rw [← Finset.mul_sum]; ring

def blockEvent {Ω : Type*} (R : ℕ → Ω → Prop) (E : Finset ℕ) (o : Ω) : Prop :=
  ∀ v ∈ E, R v o

theorem blockEvent_root {Ω : Type*} {C : Finset ℕ} (P : Finpartition C)
    (R : ℕ → Ω → Prop) (v : C) (o : Ω) :
    blockEvent R (partitionRoot P v).val o → R v.val o := by
  intro h
  exact h v.val (P.mem_part v.property)

noncomputable def partitionNormalizer {Ω : Type*} [Fintype Ω] (ν : FiniteLaw Ω)
    {C : Finset ℕ} (P : Finpartition C) (hC : C.Nonempty) (R : ℕ → Ω → Prop) (o : Ω) : ℝ :=
  eventNormalizer ν (uniformPartLaw P hC) (fun E => blockEvent R E.val) o

theorem partitionNormalizer_sum {Ω : Type*} [Fintype Ω] (ν : FiniteLaw Ω)
    {C : Finset ℕ} (P : Finpartition C) (hC : C.Nonempty) (R : ℕ → Ω → Prop) (o : Ω) :
    (∑ E : P.parts, eventWeight ν (blockEvent R E.val) o) =
      (P.parts.card : ℝ) * partitionNormalizer ν P hC R o := by
  have hB : (P.parts.card : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (part_count_pos P hC))
  rw [partitionNormalizer, eventNormalizer, uniformPartLaw_mean]
  field_simp

noncomputable def partitionChoiceLaw {Ω : Type*} [Fintype Ω] (ν : FiniteLaw Ω)
    {C : Finset ℕ} (P : Finpartition C) (hC : C.Nonempty) (R : ℕ → Ω → Prop) (o : Ω) :
    FiniteLaw (Option P.parts) := cappedLabelLaw ν (uniformPartLaw P hC) (fun E => blockEvent R E.val) o

def selectedPart {C : Finset ℕ} (P : Finpartition C) (e : Option P.parts) : Finset ℕ :=
  e.elim ∅ Subtype.val

open Classical in
theorem partitionChoiceLaw_vertex {Ω : Type*} [Fintype Ω] (ν : FiniteLaw Ω)
    {C : Finset ℕ} (P : Finpartition C) (hC : C.Nonempty) (R : ℕ → Ω → Prop) (o : Ω) (v : C) :
    (partitionChoiceLaw ν P hC R o).prob (fun e => v.val ∈ selectedPart P e) =
      (if partitionNormalizer ν P hC R o ≤ 2
        then eventWeight ν (blockEvent R (partitionRoot P v).val) o else 0) / (2 * (P.parts.card : ℝ)) := by
  have heq : (fun e => v.val ∈ selectedPart P e) = (fun e => e = some (partitionRoot P v)) := by
    funext e
    apply propext
    cases e with
    | none => simp [selectedPart]
    | some E =>
      simp only [selectedPart, Option.elim_some, Option.some.injEq]
      constructor
      · intro hvE
        exact Subtype.ext (P.part_eq_of_mem E.property hvE).symm
      · intro he
        subst E
        exact P.mem_part v.property
  rw [heq, partitionChoiceLaw, cappedLabelLaw_some, uniformPartLaw_weight]
  change (if partitionNormalizer ν P hC R o ≤ 2 then
    (1 / (P.parts.card : ℝ)) * eventWeight ν (blockEvent R (partitionRoot P v).val) o / 2 else 0) = _
  split_ifs <;> ring

theorem selectedPart_mem_or_empty {C : Finset ℕ} (P : Finpartition C) (e : Option P.parts) :
    selectedPart P e = ∅ ∨ selectedPart P e ∈ P.parts := by
  cases e with
  | none => exact Or.inl rfl
  | some E => exact Or.inr E.property

theorem selectedPart_survives {Ω : Type*} [Fintype Ω] (ν : FiniteLaw Ω)
    {C : Finset ℕ} (P : Finpartition C) (hC : C.Nonempty) (R : ℕ → Ω → Prop)
    (o : Ω) (e : Option P.parts) (he : 0 < (partitionChoiceLaw ν P hC R o).weight e) :
    blockEvent R (selectedPart P e) o := by
  cases e with
  | none => simp [blockEvent, selectedPart]
  | some E => exact cappedLabelLaw_support ν (uniformPartLaw P hC) _ o E he

end Erdos4.Tilted
