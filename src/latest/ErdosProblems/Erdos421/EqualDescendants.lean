import ErdosProblems.Erdos421.ParentForest

/-! # Equal-multiplier descendants and their finite count -/

namespace Erdos421

/-- The geometric condition propagated by any nonempty chain of equal edges. -/
def EqualEdge (i k : ℕ) : Prop :=
  ∃ j : ℕ, 2 ≤ j ∧ prime k < j * prime i ∧ j * prime (i + 1) < prime (k + 1)

theorem EqualEdge.trans {i j k : ℕ} (hij : EqualEdge i j) (hjk : EqualEdge j k) :
    EqualEdge i k := by
  obtain ⟨a, ha, haL, haR⟩ := hij
  obtain ⟨b, hb, hbL, hbR⟩ := hjk
  have hcomp := equal_edge_composition ⟨haL, haR⟩ ⟨hbL, hbR⟩ (by omega)
  exact ⟨b * a, by nlinarith, hcomp⟩

theorem EqualEdge.short_parent {i k : ℕ} (h : EqualEdge i k) (hk : ShortGap k) :
    ShortGap i := by
  obtain ⟨j, hj, hleft, hright⟩ := h
  have hlen : j * gapLength i < gapLength k :=
    equal_edge_length (prime_strictMono (Nat.lt_succ_self i)).le hleft hright
  by_contra hi
  have hip : prime i < gapLength i ^ 20 := Nat.lt_of_not_ge hi
  have hjpos : 0 < j := by omega
  have hjpow : j ≤ j ^ 20 := by
    calc
      j = j ^ 1 := (pow_one j).symm
      _ ≤ j ^ 20 := Nat.pow_le_pow_right hjpos (by decide)
  have hpow := Nat.pow_lt_pow_left hlen (by decide : 20 ≠ 0)
  rw [mul_pow] at hpow
  have hmul : j * prime i < j ^ 20 * gapLength i ^ 20 :=
    (Nat.mul_lt_mul_of_pos_left hip hjpos).trans_le
      (Nat.mul_le_mul_right _ hjpow)
  have : prime k < gapLength k ^ 20 := hleft.trans (hmul.trans hpow)
  exact this.not_ge hk

theorem parent_edge_alternatives {k u : ℕ} (hk : Rejected k) (hraw : ¬ Raw k)
    (hshort : ShortGap k) (hB : prime (k + 1) ≤ 2 ^ (60 * u)) :
    EqualEdge (parent k) k ∨ (prime (parent k)) ^ 2 ≤
      2 ^ (60 * u) * gapLength (parent k) + prime (parent k) * 2 ^ (3 * u) := by
  classical
  have h : Rejected k ∧ ¬ Raw k := ⟨hk, hraw⟩
  let w := chosenParentData k h
  have hp : parent k = w.index := by simp only [parent, dif_pos h, w]
  rw [hp]
  rcases witness_boundary_alternatives w.left_mem w.right_mem w.witness.separated
      w.witness.product_eq with heq | hineq
  · obtain ⟨j, hj, hL, hR⟩ := heq
    exact Or.inl ⟨j, hj, w.witness.gap_left.trans_le hL, hR.trans_lt w.witness.gap_right⟩
  · right
    have hs : w.witness.n - w.witness.m + 1 ≤ 2 ^ (3 * u) := by
      apply le_trans _ (hshort.length_le_scale hB)
      unfold gapLength
      have := w.witness.gap_left
      have := w.witness.gap_right
      have := w.witness.later_nonempty
      omega
    have hn : w.witness.n ≤ 2 ^ (60 * u) := w.witness.gap_right.le.trans hB
    exact hineq.trans (Nat.add_le_add (Nat.mul_le_mul_right _ hn)
      (Nat.mul_le_mul_left _ hs))

noncomputable def equalDescendants (B i : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range B).filter
    (fun k ↦ ShortGap k ∧ prime (k + 1) ≤ B ∧ (k = i ∨ EqualEdge i k))

theorem mem_equalDescendants {B i k : ℕ} : k ∈ equalDescendants B i ↔
    ShortGap k ∧ prime (k + 1) ≤ B ∧ (k = i ∨ EqualEdge i k) := by
  classical
  constructor
  · intro hk
    exact (Finset.mem_filter.mp hk).2
  · intro hk
    have hidx : k + 1 ≤ prime (k + 1) := prime_strictMono.id_le (k + 1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hidx.trans hk.2.1), hk⟩

theorem equalDescendants_card_scale (i u : ℕ) :
    (equalDescendants (2 ^ (60 * u)) i).card ≤ 1 + 2 ^ (3 * u) := by
  classical
  let S := equalDescendants (2 ^ (60 * u)) i
  let H := 2 ^ (3 * u)
  have hmem : ∀ k : S, ShortGap k ∧ prime (k + 1) ≤ 2 ^ (60 * u) ∧
      (k.val = i ∨ EqualEdge i k) := fun k ↦ mem_equalDescendants.mp k.property
  have hcode : ∀ k : S, ∃ j, j ≤ H ∧ (j = 0 ↔ k.val = i) ∧
      (k.val ≠ i → prime k < j * prime i ∧ j * prime (i + 1) < prime (k + 1)) := by
    intro k
    by_cases hki : k.val = i
    · exact ⟨0, Nat.zero_le _, by simp [hki], fun h ↦ (h hki).elim⟩
    · obtain ⟨j, hj, hL, hR⟩ := (hmem k).2.2.resolve_left hki
      have hlen : j * gapLength i < gapLength k :=
        equal_edge_length (prime_strictMono (Nat.lt_succ_self i)).le hL hR
      have hpos : 1 ≤ gapLength i := by
        unfold gapLength
        have hpi : prime i < prime (i + 1) := prime_strictMono (Nat.lt_succ_self i)
        omega
      have hjH : j ≤ H := by
        have hle := Nat.mul_le_mul_left j hpos
        have hg := (hmem k).1.length_le_scale (hmem k).2.1
        dsimp only [H]
        nlinarith
      exact ⟨j, hjH, by simp [hki, show j ≠ 0 by omega], fun _ ↦ ⟨hL, hR⟩⟩
  choose code hcode using hcode
  let f : S → Fin (H + 1) := fun k ↦ ⟨code k, Nat.lt_succ_of_le (hcode k).1⟩
  have hinj : Function.Injective f := by
    intro k l heq
    have hc : code k = code l := congrArg Fin.val heq
    by_cases hki : k.val = i
    · have hzero : code k = 0 := (hcode k).2.1.mpr hki
      have hli : l.val = i := (hcode l).2.1.mp (hc ▸ hzero)
      exact Subtype.ext (hki.trans hli.symm)
    · have hli : l.val ≠ i := by
        intro hli
        apply hki
        exact (hcode k).2.1.mp (hc.trans ((hcode l).2.1.mpr hli))
      have hk := (hcode k).2.2 hki
      have hl := (hcode l).2.2 hli
      apply Subtype.ext
      apply prime_gap_index_unique hk.1
        ((Nat.mul_le_mul_left (code k) (prime_strictMono (Nat.lt_succ_self i)).le).trans_lt hk.2)
      · rw [hc]
        exact hl.1
      · rw [hc]
        exact (Nat.mul_le_mul_left (code l)
          (prime_strictMono (Nat.lt_succ_self i)).le).trans_lt hl.2
  have hcard := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe, Fintype.card_fin, H, Nat.add_comm] using hcard

end Erdos421
