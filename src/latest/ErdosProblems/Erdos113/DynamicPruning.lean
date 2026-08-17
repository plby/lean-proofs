import ErdosProblems.Erdos113.CyclePruning
import ErdosProblems.Erdos113.Regularization

open scoped Real SimpleGraph

namespace Erdos113DynamicPruning

noncomputable section

open Erdos113Cycles Erdos113CyclePruning
  Erdos113Regular

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The integer load threshold used at one dyadic stage.  The predecessor
of the ceiling, rather than the ceiling itself, is what removes the usual
additive-one loss from the final local estimate. -/
def dynamicThreshold (m R q : ℕ) : ℕ :=
  ⌈((8 * R * (q + 1) : ℕ) : ℝ) / m⌉₊

lemma dynamicThreshold_pos {m R q : ℕ} (hm : 0 < m) (hR : 0 < R) :
    0 < dynamicThreshold m R q := by
  rw [dynamicThreshold, Nat.ceil_pos]
  positivity

lemma cast_dynamicThreshold_sub_one_le {m R q : ℕ}
    (hm : 0 < m) (hR : 0 < R) :
    ((dynamicThreshold m R q - 1 : ℕ) : ℝ) ≤
      ((8 * R * (q + 1) : ℕ) : ℝ) / m := by
  have hpos := dynamicThreshold_pos (q := q) hm hR
  have hlt := Nat.ceil_lt_add_one
    (show 0 ≤ ((8 * R * (q + 1) : ℕ) : ℝ) / m by positivity)
  change (dynamicThreshold m R q : ℝ) <
    ((8 * R * (q + 1) : ℕ) : ℝ) / m + 1 at hlt
  rw [Nat.cast_sub (by omega : 1 ≤ dynamicThreshold m R q), Nat.cast_one]
  linarith

lemma ratio_le_cast_dynamicThreshold {m R q : ℕ} :
    ((8 * R * (q + 1) : ℕ) : ℝ) / m ≤
      (dynamicThreshold m R q : ℝ) := by
  exact Nat.le_ceil _

/-- Internal dyadic recursion.  `m` and `R` remain the initial edge count
and total number of available halving stages, while `r` is the number of
stages still available. -/
private theorem exists_dynamic_pruned_aux
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m R r : ℕ) (hm : 0 < m) (hR : 0 < R) (hr : r ≤ R) :
    ∀ E : Finset (Sym2 V), E ⊆ G.edgeFinset → E.card ≤ m →
      (orderedFourCycles E).card < 2 ^ r →
      ∃ D : Finset (Sym2 V),
        D ⊆ E ∧
        (E \ D).card * (8 * R) ≤ r * m ∧
        ∀ e ∈ D,
          D.card * (orderedFourCyclesThroughEdge D e).card ≤
            16 * R * ((orderedFourCycles D).card + 1) := by
  induction r with
  | zero =>
      intro E hEG hEm hq
      have hqzero : (orderedFourCycles E).card = 0 := by
        simpa using hq
      refine ⟨E, Finset.Subset.rfl, by simp, ?_⟩
      intro e he
      have hsub := orderedFourCyclesThroughEdge_subset E e
      have hloadzero : (orderedFourCyclesThroughEdge E e).card = 0 := by
        have hcard := Finset.card_le_card hsub
        omega
      simp [hloadzero]
  | succ r ih =>
      intro E hEG hEm hq
      let q := (orderedFourCycles E).card
      let K := dynamicThreshold m R q
      have hK : 0 < K := by
        dsimp [K]
        exact dynamicThreshold_pos hm hR
      obtain ⟨E₁, hE₁E, hpaid, hload⟩ :=
        exists_pruned_subset G K E hEG
      have hE₁G : E₁ ⊆ G.edgeFinset := hE₁E.trans hEG
      have hE₁m : E₁.card ≤ m := (Finset.card_le_card hE₁E).trans hEm
      let q₁ := (orderedFourCycles E₁).card
      have hq₁q : q₁ ≤ q := by
        dsimp [q₁, q]
        omega
      have hstage : (E \ E₁).card * (8 * R) ≤ m := by
        have hratio := ratio_le_cast_dynamicThreshold (m := m) (R := R) (q := q)
        have hpaid' : (E \ E₁).card * K ≤ q := by
          dsimp [q, K] at hpaid ⊢
          omega
        have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        have hrealPaid :
            ((E \ E₁).card : ℝ) * (K : ℝ) ≤ (q : ℝ) := by
          exact_mod_cast hpaid'
        have hrealRatio :
            (((8 * R * (q + 1) : ℕ) : ℝ) / m) ≤ (K : ℝ) := by
          simpa [K] using hratio
        have hreal :
            (((E \ E₁).card * (8 * R) : ℕ) : ℝ) < (m : ℝ) := by
          have hqnonneg : (0 : ℝ) ≤ q := by positivity
          have hqone : (0 : ℝ) < q + 1 := by positivity
          have hmul :
              ((E \ E₁).card : ℝ) *
                  ((((8 * R * (q + 1) : ℕ) : ℝ) / m)) ≤ (q : ℝ) :=
            (mul_le_mul_of_nonneg_left hrealRatio
              (by positivity : (0 : ℝ) ≤ (E \ E₁).card)).trans hrealPaid
          push_cast at hmul ⊢
          have hmul' :
              ((E \ E₁).card : ℝ) * (8 * R : ℕ) * (q + 1 : ℕ) ≤
                (q : ℝ) * m := by
            apply (div_le_iff₀ hmR).mp
            calc
              (((E \ E₁).card : ℝ) * (8 * R : ℕ) * (q + 1 : ℕ)) /
                    (m : ℝ) =
                  ((E \ E₁).card : ℝ) *
                    ((((8 * R * (q + 1) : ℕ) : ℝ) / m)) := by
                      push_cast
                      ring
              _ ≤ (q : ℝ) := by
                    simpa [Nat.cast_mul, Nat.cast_add] using hmul
          push_cast at hmul' ⊢
          nlinarith
        exact_mod_cast hreal.le
      by_cases hhalf : 2 * q₁ < q
      · have hq₁pow : q₁ < 2 ^ r := by
          have hpow : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
          rw [hpow] at hq
          omega
        obtain ⟨D, hDE₁, hbudget, hlocal⟩ :=
          ih (Nat.le_trans (Nat.le_succ r) hr) E₁ hE₁G hE₁m hq₁pow
        refine ⟨D, hDE₁.trans hE₁E, ?_, hlocal⟩
        have hsplit : (E \ D).card = (E \ E₁).card + (E₁ \ D).card := by
          have h₁ := Finset.card_sdiff_add_card_eq_card hDE₁
          have h₂ := Finset.card_sdiff_add_card_eq_card (hDE₁.trans hE₁E)
          have h₃ := Finset.card_sdiff_add_card_eq_card hE₁E
          omega
        rw [hsplit, Nat.add_mul]
        calc
          (E \ E₁).card * (8 * R) + (E₁ \ D).card * (8 * R) ≤
              m + r * m := Nat.add_le_add hstage hbudget
          _ = (r + 1) * m := by ring
      · have hqle : q ≤ 2 * q₁ := by omega
        refine ⟨E₁, hE₁E, ?_, ?_⟩
        · exact hstage.trans (by
            have : m ≤ (r + 1) * m := by
              nlinarith
            exact this)
        · intro e he
          have hloadNat : (orderedFourCyclesThroughEdge E₁ e).card ≤ K - 1 :=
            Nat.le_sub_one_of_lt (hload e he)
          have hpred := cast_dynamicThreshold_sub_one_le
            (m := m) (R := R) (q := q) hm hR
          have hDcard : E₁.card ≤ m := hE₁m
          have hreal :
              ((E₁.card * (orderedFourCyclesThroughEdge E₁ e).card : ℕ) : ℝ) ≤
                ((16 * R * (q₁ + 1) : ℕ) : ℝ) := by
            have hmnonneg : (0 : ℝ) ≤ m := by positivity
            have hloadReal :
                ((orderedFourCyclesThroughEdge E₁ e).card : ℝ) ≤
                  (K - 1 : ℕ) := by exact_mod_cast hloadNat
            calc
              ((E₁.card * (orderedFourCyclesThroughEdge E₁ e).card : ℕ) : ℝ) ≤
                  (m : ℝ) * (K - 1 : ℕ) := by
                    push_cast
                    gcongr
              _ ≤ (m : ℝ) *
                    (((8 * R * (q + 1) : ℕ) : ℝ) / m) := by gcongr
              _ = ((8 * R * (q + 1) : ℕ) : ℝ) := by
                    field_simp
              _ ≤ ((16 * R * (q₁ + 1) : ℕ) : ℝ) := by
                    exact_mod_cast (by nlinarith :
                      8 * R * (q + 1) ≤ 16 * R * (q₁ + 1))
          exact_mod_cast hreal

/-- Repeated dyadic pruning retains strictly more than half of a nonempty
edge set and gives a local ordered-four-cycle load controlled by the final,
not the initial, ordered-four-cycle count. -/
theorem exists_dynamically_pruned_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Finset (Sym2 V)) (hE : E ⊆ G.edgeFinset) (R : ℕ) (hR : 0 < R)
    (hEne : E.Nonempty)
    (hq : (orderedFourCycles E).card < 2 ^ R) :
    ∃ D : Finset (Sym2 V),
      D ⊆ E ∧ E.card < 2 * D.card ∧
      ∀ e ∈ D,
        D.card * (orderedFourCyclesThroughEdge D e).card ≤
          16 * R * ((orderedFourCycles D).card + 1) := by
  let m := E.card
  have hm : 0 < m := by simpa [m] using Finset.card_pos.mpr hEne
  obtain ⟨D, hDE, hbudget, hlocal⟩ :=
    exists_dynamic_pruned_aux G m R R hm hR le_rfl E hE (by simp [m]) hq
  refine ⟨D, hDE, ?_, hlocal⟩
  have hcancel : (E \ D).card * 8 ≤ m := by
    have hb : R * ((E \ D).card * 8) ≤ R * m := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hbudget
    exact Nat.le_of_mul_le_mul_left hb hR
  have hcard := Finset.card_sdiff_add_card_eq_card hDE
  dsimp [m] at hcancel
  omega

/-- The graph-theoretic specialization needs only four times the binary
degree-bin count, since the total number of ordered four-cycles is at most
`|V|^4`. -/
theorem exists_dynamically_pruned_edgeFinset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hedge : ∃ x y, G.Adj x y) :
    ∃ D : Finset (Sym2 V),
      D ⊆ G.edgeFinset ∧ G.edgeFinset.card < 2 * D.card ∧
      ∀ e ∈ D,
        D.card * (orderedFourCyclesThroughEdge D e).card ≤
          64 * degreeBinCount (W := V) *
            ((orderedFourCycles D).card + 1) := by
  let L := degreeBinCount (W := V)
  let R := 4 * L
  have hnpos : 0 < Fintype.card V := by
    obtain ⟨x, _y, _hxy⟩ := hedge
    exact Fintype.card_pos_iff.mpr ⟨x⟩
  have hL : 0 < L := by
    dsimp [L, degreeBinCount]
    omega
  have hR : 0 < R := by dsimp [R]; positivity
  have hnlt : Fintype.card V < 2 ^ L := by
    simpa [L, degreeBinCount, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Fintype.card V))
  have hnPow : Fintype.card V ^ 4 < 2 ^ R := by
    calc
      Fintype.card V ^ 4 < (2 ^ L) ^ 4 := by gcongr
      _ = 2 ^ R := by simp [R, pow_mul, mul_comm]
  have hq : (orderedFourCycles G.edgeFinset).card < 2 ^ R :=
    (card_orderedFourCycles_le G.edgeFinset).trans_lt hnPow
  have hEne : G.edgeFinset.Nonempty := by
    obtain ⟨x, y, hxy⟩ := hedge
    exact ⟨s(x, y), by simpa using hxy⟩
  obtain ⟨D, hDsub, hDcard, hDload⟩ :=
    exists_dynamically_pruned_subset G G.edgeFinset Finset.Subset.rfl
      R hR hEne hq
  refine ⟨D, hDsub, hDcard, ?_⟩
  intro e he
  convert hDload e he using 1 <;> dsimp [R, L] <;> ring

end

end Erdos113DynamicPruning
