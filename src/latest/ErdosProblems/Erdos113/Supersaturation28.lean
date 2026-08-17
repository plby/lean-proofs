import ErdosProblems.Erdos113.CellPruning
import ErdosProblems.Erdos113.Genuine28

open scoped BigOperators Real SimpleGraph

namespace Erdos113Supersaturation28

noncomputable section

open Erdos113Cycles Erdos113Regular Erdos113BipartiteGraph
  Erdos113CellPruning Erdos113Genuine28

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- A polynomial-slack, fully finite substitute for the fixed-length
Morris--Saxton supersaturation statement needed in the many-four-cycle
case.  The powers of `degreeBinCount` are harmless logarithmic losses.

The numerical hypothesis says that the minimum degree furnished by the
dense pruned cell is large enough for the length-28 conflict estimate. -/
theorem genuineCycles28_lower_of_edgeDensity
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (hedge : ∃ x y, A.Adj x y)
    (hlarge :
      702464 * (16 * (degreeBinCount (W := W) : ℝ)) *
          (2 * Fintype.card W : ℝ) ^ ((1 : ℝ) / 14) ≤
        (A.edgeFinset.card : ℝ) /
          (32 * (degreeBinCount (W := W) : ℝ) ^ 3 * Fintype.card W)) :
    ((A.edgeFinset.card : ℝ) /
        (32 * (degreeBinCount (W := W) : ℝ) ^ 3 * Fintype.card W)) ^ 28 /
        (2 * (2 : ℝ) ^ 28) ≤
      ((genuineCycles A 28).card : ℝ) := by
  classical
  obtain ⟨i, j, E, hEsub, hEne, hEdense, hleftMin, hrightMin⟩ :=
    exists_pruned_cell A hedge
  let B := retainedGraph E
  let side : LiveLeft E ⊕ LiveRight E → Bool :=
    Sum.elim (fun _ ↦ false) (fun _ ↦ true)
  let proj : LiveLeft E ⊕ LiveRight E → W :=
    Sum.elim (fun x ↦ x.1.1) (fun y ↦ y.1.1)
  let R : (LiveLeft E ⊕ LiveRight E) →
      (LiveLeft E ⊕ LiveRight E) → Prop := fun x y ↦ proj x = proj y
  let L : ℝ := degreeBinCount (W := W)
  let cap : Bool → ℝ := fun b ↦
    if b then 2 ^ (j.val + 1) else 2 ^ (i.val + 1)
  let d : Bool → ℝ := fun b ↦ cap b / (16 * L)
  let δ : ℝ := (A.edgeFinset.card : ℝ) /
    (32 * L ^ 3 * Fintype.card W)
  let N : ℝ := Fintype.card (LiveLeft E ⊕ LiveRight E)
  letI : DecidableRel B.Adj := inferInstance
  letI : DecidableRel R := fun x y ↦ inferInstanceAs (Decidable (proj x = proj y))
  letI : Nonempty (LiveLeft E ⊕ LiveRight E) :=
    nonempty_of_nonempty E hEne
  have hn : 0 < (Fintype.card W : ℝ) := by
    obtain ⟨x, y, hxy⟩ := hedge
    have : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨x⟩
    exact_mod_cast this
  have hL : 0 < L := by
    dsimp [L, degreeBinCount]
    positivity
  have hcap : ∀ b, 0 < cap b := by
    intro b
    cases b <;> simp [cap] <;> positivity
  have hd : ∀ b, 0 < d b := by
    intro b
    dsimp [d]
    exact div_pos (hcap b) (mul_pos (by norm_num) hL)
  have hcardN : Fintype.card (LiveLeft E ⊕ LiveRight E) ≤
      2 * Fintype.card W := by
    rw [Fintype.card_sum]
    have hl : Fintype.card (LiveLeft E) ≤ Fintype.card W := by
      calc
        Fintype.card (LiveLeft E) ≤ Fintype.card (BinVertex A i) :=
          Fintype.card_subtype_le _
        _ ≤ Fintype.card W := Fintype.card_subtype_le _
    have hr : Fintype.card (LiveRight E) ≤ Fintype.card W := by
      calc
        Fintype.card (LiveRight E) ≤ Fintype.card (BinVertex A j) :=
          Fintype.card_subtype_le _
        _ ≤ Fintype.card W := Fintype.card_subtype_le _
    omega
  have hNroot : N ^ ((1 : ℝ) / 14) ≤
      (2 * Fintype.card W : ℝ) ^ ((1 : ℝ) / 14) := by
    apply Real.rpow_le_rpow
    · dsimp [N]
      positivity
    · dsimp [N]
      exact_mod_cast hcardN
    · norm_num
  have hEcapLeft : E.card ≤ Fintype.card W * 2 ^ (i.val + 1) := by
    calc
      E.card ≤ Fintype.card (BinVertex A i) * 2 ^ (i.val + 1) :=
        card_le_card_mul_of_leftFiber_le E _ (fun x ↦ by
          exact (card_leftFiber_le_degree A i j E hEsub x).trans
            (degree_bounds_of_mem_bin A i x.2).2.le)
      _ ≤ Fintype.card W * 2 ^ (i.val + 1) := by
        gcongr
        exact Fintype.card_subtype_le _
  have hEcapRight : E.card ≤ Fintype.card W * 2 ^ (j.val + 1) := by
    calc
      E.card ≤ Fintype.card (BinVertex A j) * 2 ^ (j.val + 1) :=
        card_le_card_mul_of_rightFiber_le E _ (fun y ↦ by
          exact (card_rightFiber_le_degree A i j E hEsub y).trans
            (degree_bounds_of_mem_bin A j y.2).2.le)
      _ ≤ Fintype.card W * 2 ^ (j.val + 1) := by
        gcongr
        exact Fintype.card_subtype_le _
  have hδd : ∀ b, δ ≤ d b := by
    intro b
    have hnat : A.edgeFinset.card ≤
        2 * degreeBinCount (W := W) ^ 2 *
          (Fintype.card W * (if b then 2 ^ (j.val + 1) else 2 ^ (i.val + 1))) := by
      calc
        A.edgeFinset.card ≤
            2 * degreeBinCount (W := W) ^ 2 * E.card := hEdense
        _ ≤ 2 * degreeBinCount (W := W) ^ 2 *
            (Fintype.card W *
              (if b then 2 ^ (j.val + 1) else 2 ^ (i.val + 1))) := by
          gcongr
          cases b
          · simpa using hEcapLeft
          · simpa using hEcapRight
    have hreal : (A.edgeFinset.card : ℝ) ≤
        2 * L ^ 2 * (Fintype.card W : ℝ) * cap b := by
      cases b
      · simp only [Bool.false_eq_true, if_false] at hnat
        dsimp [L, cap]
        push_cast
        exact_mod_cast (by simpa [mul_assoc] using hnat)
      · simp only [if_true] at hnat
        dsimp [L, cap]
        push_cast
        exact_mod_cast (by simpa [mul_assoc] using hnat)
    dsimp [δ, d]
    apply (div_le_iff₀ (by positivity :
      (0 : ℝ) < 32 * L ^ 3 * Fintype.card W)).2
    calc
      (A.edgeFinset.card : ℝ) ≤
          2 * L ^ 2 * (Fintype.card W : ℝ) * cap b := hreal
      _ = cap b / (16 * L) *
          (32 * L ^ 3 * Fintype.card W) := by
        field_simp [ne_of_gt hL]
        ring
  have hprojAdj {x y : LiveLeft E ⊕ LiveRight E} (hxy : B.Adj x y) :
      A.Adj (proj x) (proj y) := by
    rcases x with x | x <;> rcases y with y | y
    · exact False.elim hxy
    · exact (mem_cellEdges A i j _).mp (hEsub hxy)
    · exact ((mem_cellEdges A i j _).mp (hEsub hxy)).symm
    · exact False.elim hxy
  have hdegreeMax (x : LiveLeft E ⊕ LiveRight E) :
      (B.degree x : ℝ) ≤ (16 * L) * d (side x) := by
    have hcapDegree : (B.degree x : ℝ) ≤ cap (side x) := by
      rcases x with x | x
      · rw [degree_inl]
        dsimp [side, cap]
        exact_mod_cast (card_leftFiber_le_degree A i j E hEsub x.1).trans
          (degree_bounds_of_mem_bin A i x.1.2).2.le
      · rw [degree_inr]
        dsimp [side, cap]
        exact_mod_cast (card_rightFiber_le_degree A i j E hEsub x.1).trans
          (degree_bounds_of_mem_bin A j x.1.2).2.le
    have hid : cap (side x) = (16 * L) * d (side x) := by
      dsimp [d]
      field_simp [ne_of_gt hL]
    exact hcapDegree.trans_eq hid
  have hdegreeMin (x : LiveLeft E ⊕ LiveRight E) :
      d (side x) ≤ (B.degree x : ℝ) := by
    rcases x with x | x
    · obtain ⟨y, hy⟩ := x.2
      have hinc : (E ∩ leftFiber (cellEdges A i j) x.1).Nonempty := by
        refine ⟨(x.1, y), Finset.mem_inter.mpr ⟨hy, ?_⟩⟩
        exact (mem_leftFiber _ _ _).mpr ⟨hEsub hy, rfl⟩
      have hm := hleftMin x.1 hinc
      rw [degree_inl]
      have hmR : ((cellThreshold (2 ^ (i.val + 1))
          (degreeBinCount (W := W)) : ℕ) : ℝ) ≤
          ((leftFiber E x.1).card : ℝ) := by exact_mod_cast hm
      have hbase := (cap_div_le_cast_cellThreshold
        (cap := 2 ^ (i.val + 1))
        (L := degreeBinCount (W := W))).trans hmR
      dsimp [d, cap, side, L]
      norm_num [Nat.cast_pow, Nat.cast_mul] at hbase ⊢
      simpa using hbase
    · obtain ⟨y, hy⟩ := x.2
      have hinc : (E ∩ rightFiber (cellEdges A i j) x.1).Nonempty := by
        refine ⟨(y, x.1), Finset.mem_inter.mpr ⟨hy, ?_⟩⟩
        exact (mem_rightFiber _ _ _).mpr ⟨hEsub hy, rfl⟩
      have hm := hrightMin x.1 hinc
      rw [degree_inr]
      have hmR : ((cellThreshold (2 ^ (j.val + 1))
          (degreeBinCount (W := W)) : ℕ) : ℝ) ≤
          ((rightFiber E x.1).card : ℝ) := by exact_mod_cast hm
      have hbase := (cap_div_le_cast_cellThreshold
        (cap := 2 ^ (j.val + 1))
        (L := degreeBinCount (W := W))).trans hmR
      dsimp [d, cap, side, L]
      norm_num [Nat.cast_pow, Nat.cast_mul] at hbase ⊢
      simpa using hbase
  have hcross : ∀ {x y}, B.Adj x y → side y = !side x := by
    intro x y hxy
    exact cross E hxy
  have hlocal (u y : LiveLeft E ⊕ LiveRight E) :
      (((B.neighborFinset y).filter (R u)).card : ℝ) ≤ 1 := by
    have hinj : Set.InjOn proj (B.neighborSet y) := by
      intro x hx z hz hxz
      rcases y with y | y
      · rcases x with x | x
        · exact False.elim hx
        · rcases z with z | z
          · exact False.elim hz
          · congr 1
            apply Subtype.ext
            apply Subtype.ext
            exact hxz
      · rcases x with x | x
        · rcases z with z | z
          · congr 1
            apply Subtype.ext
            apply Subtype.ext
            exact hxz
          · exact False.elim hz
        · exact False.elim hx
    have hsub : (B.neighborFinset y).filter (R u) ⊆
        (B.neighborFinset y).filter (fun z ↦ proj z = proj u) := by
      intro z hz
      have hz' := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hz'.1, hz'.2.symm⟩
    have hone : ((B.neighborFinset y).filter
        (fun z ↦ proj z = proj u)).card ≤ 1 := by
      by_contra! htwo
      obtain ⟨x, hx, z, hz, hxz⟩ := Finset.one_lt_card.mp htwo
      have hxeq := (Finset.mem_filter.mp hx).2
      have hzeq := (Finset.mem_filter.mp hz).2
      apply hxz
      apply hinj
      · exact (B.mem_neighborFinset y x).mp (Finset.mem_filter.mp hx).1
      · exact (B.mem_neighborFinset y z).mp (Finset.mem_filter.mp hz).1
      · exact hxeq.trans hzeq.symm
    exact_mod_cast (Finset.card_le_card hsub).trans hone
  have hlargeB : ∀ b,
      702464 * (16 * L) * N ^ ((1 : ℝ) / 14) ≤ d b := by
    intro b
    calc
      702464 * (16 * L) * N ^ ((1 : ℝ) / 14) ≤
          702464 * (16 * L) *
            (2 * Fintype.card W : ℝ) ^ ((1 : ℝ) / 14) := by
        gcongr
      _ ≤ δ := by simpa [δ, L] using hlarge
      _ ≤ d b := hδd b
  have hfree := relationFreeCycles_half_of_bipartiteAlmostRegular
    B R side d (16 * L) N rfl hd (by positivity) hcross hdegreeMin
      hdegreeMax (fun _ _ h ↦ h.symm) hlocal hlargeB
  have hδnonneg : 0 ≤ δ := by dsimp [δ]; positivity
  have hclosedLower : δ ^ 28 ≤ (Conflict28.closedWalkCount B 28 : ℝ) := by
    calc
      δ ^ 28 = (δ * δ) ^ 14 := by ring
      _ ≤ (d false * d true) ^ 14 := by
        apply pow_le_pow_left₀ (mul_nonneg hδnonneg hδnonneg)
        exact mul_le_mul (hδd false) (hδd true) hδnonneg (hd false).le
      _ ≤ (Conflict28.closedWalkCount B 28 : ℝ) :=
        closedWalkCount_28_lower_bipartite B side d
          (fun b ↦ (hd b).le) hcross hdegreeMin
  let f : RelationFreeHomCycle28 B R →
      (Fin 28 → Bool) × ↑(genuineCycles A 28) := fun x ↦
    (fun k ↦ side (x.1.1 k),
      ⟨fun k ↦ proj (x.1.1 k), by
        rw [mem_genuineCycles]
        refine ⟨?_, ?_⟩
        · intro p q hpq
          by_contra hpne
          exact x.2 p q hpne hpq
        · intro k
          exact hprojAdj (x.1.2 k)⟩)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    funext k
    have hs := congrFun (congrArg Prod.fst hxy) k
    have hp := congrFun (congrArg (fun z ↦ (z.2.1 : Fin 28 → W)) hxy) k
    rcases hx : x.1.1 k with u | v <;> rcases hy : y.1.1 k with u' | v'
    · congr 1
      apply Subtype.ext
      apply Subtype.ext
      simpa [f, proj, hx, hy] using hp
    · have : false = true := by simpa [f, side, hx, hy] using hs
      contradiction
    · have : true = false := by simpa [f, side, hx, hy] using hs
      contradiction
    · congr 1
      apply Subtype.ext
      apply Subtype.ext
      simpa [f, proj, hx, hy] using hp
  have hcardNat := Fintype.card_le_of_injective f hf
  have hcard : (Fintype.card (RelationFreeHomCycle28 B R) : ℝ) ≤
      (2 : ℝ) ^ 28 * ((genuineCycles A 28).card : ℝ) := by
    have hcardNat' : Fintype.card (RelationFreeHomCycle28 B R) ≤
        2 ^ 28 * (genuineCycles A 28).card := by
      rw [← Fintype.card_coe]
      simpa using hcardNat
    exact_mod_cast hcardNat'
  have hpowpos : 0 < (2 : ℝ) ^ 28 := by positivity
  calc
    δ ^ 28 / (2 * (2 : ℝ) ^ 28) =
        (δ ^ 28 / 2) / (2 : ℝ) ^ 28 := by ring
    _ ≤ ((Conflict28.closedWalkCount B 28 : ℝ) / 2) /
          (2 : ℝ) ^ 28 := by
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hclosedLower (by norm_num)) hpowpos.le
    _ ≤ (Fintype.card (RelationFreeHomCycle28 B R) : ℝ) /
          (2 : ℝ) ^ 28 := div_le_div_of_nonneg_right hfree hpowpos.le
    _ ≤ ((genuineCycles A 28).card : ℝ) :=
      (div_le_iff₀ hpowpos).2 (by
        simpa [mul_comm] using hcard)

end

end Erdos113Supersaturation28
