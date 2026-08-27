import ErdosProblems.Erdos4.FGKMTConditionalLaw
import ErdosProblems.Erdos4.FGKMTReweighting

/-!
# Joint survival after pinning a set of vertices

Conditioning on the survival of `T` sets the model probabilities on `T`
to one. Relative joint-survival accuracy persists for every test set
whose union with `T` is within the original cardinality budget.
-/

open scoped BigOperators

namespace Erdos4.FGKMT

theorem ratio_near_one {a b ε : ℝ} (hε : ε < 1) (ha : |a - 1| ≤ ε) (hb : |b - 1| ≤ ε) :
    |a / b - 1| ≤ 2 * ε / (1 - ε) := by
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans ha
  have hb0 : 0 < b := by have hh := (abs_le.mp hb).1; linarith
  have hblow : 1 - ε ≤ b := by have hh := (abs_le.mp hb).1; linarith
  have hab : |a - b| ≤ 2 * ε := by
    have hh := abs_sub_le a 1 b
    rw [abs_sub_comm 1 b] at hh
    linarith
  have heq : a / b - 1 = (a - b) / b := by field_simp
  rw [heq, abs_div, abs_of_pos hb0]
  exact (div_le_div_of_nonneg_right hab hb0.le).trans
    (div_le_div_of_nonneg_left (by positivity) (by linarith) hblow)

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def pinnedModel (p : V → ℝ) (T : Finset V) (v : V) : ℝ :=
  if v ∈ T then 1 else p v

omit [Fintype V] in
theorem pinnedModel_pos (p : V → ℝ) (hp : ∀ v, 0 < p v) (T : Finset V) :
    ∀ v, 0 < pinnedModel p T v := by
  intro v
  unfold pinnedModel
  split_ifs
  · norm_num
  · exact hp v

omit [Fintype V] in
theorem setProduct_pinned (p : V → ℝ) (T F : Finset V) :
    setProduct (pinnedModel p T) F = setProduct p (F \ T) := by
  calc
    _ = setProduct (pinnedModel p T) (F \ T) := by
      symm
      apply Finset.prod_subset Finset.sdiff_subset
      intro v hv hvnot
      have hvT : v ∈ T := by
        by_contra hnot
        exact hvnot (Finset.mem_sdiff.mpr ⟨hv, hnot⟩)
      exact if_pos hvT
    _ = _ := Finset.prod_congr rfl (fun v hv => if_neg (Finset.mem_sdiff.mp hv).2)

omit [Fintype V] in
theorem setProduct_union_pinned (p : V → ℝ) (T F : Finset V) :
    setProduct p (T ∪ F) = setProduct p T * setProduct (pinnedModel p T) F := by
  rw [setProduct_pinned]
  have hd : Disjoint T (F \ T) := by
    apply Finset.disjoint_left.mpr
    intro v hv hvF
    exact (Finset.mem_sdiff.mp hvF).2 hv
  have hh := Finset.prod_union (f := p) hd
  simpa only [setProduct, Finset.union_sdiff_self_eq_union] using hh

noncomputable def conditionSurvival (ν : FiniteLaw (Finset V)) (T : Finset V) :
    FiniteLaw (Finset V) := ν.condition (fun W => T ⊆ W) ∅

theorem conditional_survival (ν : FiniteLaw (Finset V)) (T F : Finset V)
    (hT : survival ν T ≠ 0) :
    survival (conditionSurvival ν T) F = survival ν (T ∪ F) / survival ν T := by
  unfold survival conditionSurvival
  rw [FiniteLaw.condition_prob ν (fun W => T ⊆ W) (fun W => F ⊆ W) ∅ hT]
  congr 1
  unfold FiniteLaw.prob
  apply Finset.sum_congr rfl
  intro W _hW
  by_cases hTW : T ⊆ W <;> by_cases hFW : F ⊆ W <;>
    simp [Finset.union_subset_iff, hTW, hFW]

theorem survival_pos_of_accurate (ν : FiniteLaw (Finset V)) (p : V → ℝ)
    (hp : ∀ v, 0 < p v) {A : ℕ} {ε : ℝ} (hε : ε < 1)
    (hacc : SurvivalAccurate ν p A ε) {T : Finset V} (hT : T.card ≤ A) : 0 < survival ν T := by
  have hh := (abs_le.mp (hacc T hT)).1
  have hratio : 0 < survival ν T / setProduct p T := by linarith
  exact ((div_pos_iff.mp hratio).resolve_right
    (fun h => (not_lt_of_ge (setProduct_pos p hp T).le) h.2)).1

theorem conditional_accuracy (ν : FiniteLaw (Finset V)) (p : V → ℝ)
    (hp : ∀ v, 0 < p v) {A B : ℕ} {ε : ℝ} (hε : ε < 1)
    (hacc : SurvivalAccurate ν p A ε) (T : Finset V) (hsize : T.card + B ≤ A) :
    SurvivalAccurate (conditionSurvival ν T) (pinnedModel p T) B (2 * ε / (1 - ε)) := by
  have hT : T.card ≤ A := by omega
  have hTpos := survival_pos_of_accurate ν p hp hε hacc hT
  intro F hF
  have hTF : (T ∪ F).card ≤ A := by
    have hh := Finset.card_union_le T F
    omega
  have hh := ratio_near_one hε (hacc (T ∪ F) hTF) (hacc T hT)
  have hPT := setProduct_pos p hp T
  have hPF := setProduct_pos (pinnedModel p T) (pinnedModel_pos p hp T) F
  have heq : (survival ν (T ∪ F) / setProduct p (T ∪ F)) /
      (survival ν T / setProduct p T) =
      survival (conditionSurvival ν T) F / setProduct (pinnedModel p T) F := by
    rw [conditional_survival ν T F hTpos.ne', setProduct_union_pinned]
    field_simp
  rw [heq] at hh
  exact hh

end Erdos4.FGKMT
