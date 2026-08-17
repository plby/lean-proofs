/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos546.Basic
import ErdosProblems.Erdos546.Numeric
import ErdosProblems.Erdos546.MonoPair

/-!
# A dyadic sparse-colour lemma

This file gives the rounding-safe version of Sudakov's sparse-colour
monochromatic-pair lemma.  All density and reservoir estimates are expressed
by multiplication in `ℕ`.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos546

open Finset
open SimpleGraph

/-! ## Counting and pruning -/

/-- The number of neighbours of `v` which lie in `S`. -/
noncomputable def degreeInto {N : ℕ} (R : SimpleGraph (Fin N))
    (v : Fin N) (S : Finset (Fin N)) : ℕ := by
  classical
  exact (S.filter fun w ↦ R.Adj v w).card

private lemma crossEdgeCount_eq_sum_degreeInto {N : ℕ}
    (R : SimpleGraph (Fin N)) (S T : Finset (Fin N)) :
    crossEdgeCount R S T = ∑ v ∈ S, degreeInto R v T := by
  classical
  change #(Rel.interedges R.Adj S T) = _
  rw [Rel.interedges_eq_biUnion, Finset.card_biUnion]
  · simp [degreeInto]
  · intro a ha b hb hab
    change Disjoint
      ((T.filter fun y ↦ R.Adj a y).map ⟨(a, ·), Prod.mk_right_injective a⟩)
      ((T.filter fun y ↦ R.Adj b y).map ⟨(b, ·), Prod.mk_right_injective b⟩)
    rw [Finset.disjoint_left]
    intro p hpa hpb
    simp only [Finset.mem_map] at hpa hpb
    obtain ⟨ya, hya, rfl⟩ := hpa
    obtain ⟨yb, hyb, heq⟩ := hpb
    exact hab (Prod.mk.inj heq).1.symm

private lemma degreeInto_erase_self {N : ℕ} (R : SimpleGraph (Fin N))
    (S : Finset (Fin N)) {v : Fin N} (hv : v ∈ S) :
    degreeInto R v S = degreeInto R v (S.erase v) := by
  classical
  rw [← Finset.insert_erase hv]
  unfold degreeInto
  rw [Finset.filter_insert]
  simp

private lemma degreeInto_insert_of_adj {N : ℕ} (R : SimpleGraph (Fin N))
    (T : Finset (Fin N)) (x v : Fin N) (hv : v ∉ T) (hxv : R.Adj x v) :
    degreeInto R x (insert v T) = degreeInto R x T + 1 := by
  classical
  unfold degreeInto
  rw [Finset.filter_insert]
  simp [hxv, hv]

private lemma degreeInto_insert_of_not_adj {N : ℕ} (R : SimpleGraph (Fin N))
    (T : Finset (Fin N)) (x v : Fin N) (hxv : ¬ R.Adj x v) :
    degreeInto R x (insert v T) = degreeInto R x T := by
  classical
  unfold degreeInto
  rw [Finset.filter_insert]
  simp [hxv]

/-- Removing one vertex removes exactly twice its remaining internal degree
from the ordered internal-edge count. -/
private lemma crossEdgeCount_erase {N : ℕ} (R : SimpleGraph (Fin N))
    (S : Finset (Fin N)) {v : Fin N} (hv : v ∈ S) :
    crossEdgeCount R S S = crossEdgeCount R (S.erase v) (S.erase v) +
      2 * degreeInto R v (S.erase v) := by
  classical
  rw [crossEdgeCount_eq_sum_degreeInto, crossEdgeCount_eq_sum_degreeInto]
  have hvnot : v ∉ S.erase v := by simp
  have hsymm :
      ∑ x ∈ S.erase v, (if R.Adj x v then 1 else 0) =
        degreeInto R v (S.erase v) := by
    classical
    unfold degreeInto
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : R.Adj x v
    · simp [h, R.adj_symm h]
    · have hvx : ¬ R.Adj v x := fun hvx ↦ h (R.adj_symm hvx)
      simp [h, hvx]
  calc
    ∑ x ∈ S, degreeInto R x S =
        ∑ x ∈ insert v (S.erase v), degreeInto R x (insert v (S.erase v)) := by
          rw [Finset.insert_erase hv]
    _ = degreeInto R v (insert v (S.erase v)) +
          ∑ x ∈ S.erase v, degreeInto R x (insert v (S.erase v)) := by
          rw [Finset.sum_insert hvnot]
    _ = degreeInto R v (S.erase v) +
          ∑ x ∈ S.erase v,
            (degreeInto R x (S.erase v) + if R.Adj x v then 1 else 0) := by
          have hself : degreeInto R v (insert v (S.erase v)) =
              degreeInto R v (S.erase v) :=
            degreeInto_insert_of_not_adj R (S.erase v) v v R.irrefl
          rw [hself]
          apply congrArg (degreeInto R v (S.erase v) + ·)
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxv : R.Adj x v
          · simpa [hxv] using degreeInto_insert_of_adj R (S.erase v) x v hvnot hxv
          · simpa [hxv] using degreeInto_insert_of_not_adj R (S.erase v) x v hxv
    _ = (∑ x ∈ S.erase v, degreeInto R x (S.erase v)) +
          2 * degreeInto R v (S.erase v) := by
          rw [Finset.sum_add_distrib, hsymm]
          ring

/-- Exact finite pruning.  Vertices of current degree at least `k` are
successively deleted.  The ordered edge sets charged at different deletions
are disjoint, which is recorded by the final inequality. -/
private lemma exists_pruned_subset {N : ℕ} (R : SimpleGraph (Fin N))
    (S : Finset (Fin N)) (k : ℕ) :
    ∃ T ⊆ S,
      (∀ v ∈ T, degreeInto R v T < k) ∧
      2 * k * (S.card - T.card) ≤ crossEdgeCount R S S := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
      by_cases hall : ∀ v ∈ S, degreeInto R v S < k
      · exact ⟨S, subset_rfl, hall, by simp⟩
      · push Not at hall
        obtain ⟨v, hvS, hvdeg⟩ := hall
        have herase : S.erase v ⊂ S := Finset.erase_ssubset hvS
        obtain ⟨T, hTS, hdegT, hloss⟩ := ih (S.erase v) herase
        refine ⟨T, hTS.trans (Finset.erase_subset _ _), hdegT, ?_⟩
        have hvnot : v ∉ S.erase v := by simp
        have hcardT : T.card ≤ (S.erase v).card := Finset.card_le_card hTS
        have hcardS : S.card = (S.erase v).card + 1 := by
          rw [← Finset.card_insert_of_notMem hvnot, Finset.insert_erase hvS]
        rw [degreeInto_erase_self R S hvS] at hvdeg
        have hdiff : S.card - T.card = (S.erase v).card - T.card + 1 := by
          omega
        rw [crossEdgeCount_erase R S hvS, hdiff]
        calc
          2 * k * ((S.erase v).card - T.card + 1) =
              2 * k * ((S.erase v).card - T.card) + 2 * k := by ring
          _ ≤ crossEdgeCount R (S.erase v) (S.erase v) +
                2 * degreeInto R v (S.erase v) := by
            exact Nat.add_le_add hloss (Nat.mul_le_mul_left 2 hvdeg)

/-! ## Binomial estimates -/

private lemma factorial_ratio_lower (r : ℕ) (hr : 0 < r) :
    ((r : ℝ) / 3) ^ r ≤ (r.factorial : ℝ) := by
  have harg : (1 : ℝ) ≤ 2 * Real.pi * r := by
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith [Real.pi_gt_three, Real.pi_pos]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * r) :=
    Real.one_le_sqrt.mpr harg
  have hdiv : (r : ℝ) / 3 ≤ (r : ℝ) / Real.exp 1 := by
    apply div_le_div_of_nonneg_left (by positivity) (Real.exp_pos 1)
    exact Real.exp_one_lt_three.le
  calc
    ((r : ℝ) / 3) ^ r ≤ ((r : ℝ) / Real.exp 1) ^ r :=
      pow_le_pow_left₀ (by positivity) hdiv _
    _ ≤ Real.sqrt (2 * Real.pi * r) * ((r : ℝ) / Real.exp 1) ^ r :=
      le_mul_of_one_le_left (by positivity) hsqrt
    _ ≤ (r.factorial : ℝ) := Stirling.le_factorial_stirling r

/-- A convenient integer version of `choose b r ≤ (3b/r)^r`. -/
private lemma choose_le_two_pow_mul
    {Q b r : ℕ} (hr : 0 < r) (hratio : 3 * b ≤ 2 ^ Q * r) :
    b.choose r ≤ 2 ^ (Q * r) := by
  have hfac := factorial_ratio_lower r hr
  have hchoose : (b.choose r : ℝ) ≤ (b : ℝ) ^ r / (r.factorial : ℝ) :=
    Nat.choose_le_pow_div r b
  have hp : (0 : ℝ) < ((r : ℝ) / 3) ^ r := by positivity
  have hratio' : (b : ℝ) ^ r / (r.factorial : ℝ) ≤
      (b : ℝ) ^ r / (((r : ℝ) / 3) ^ r) := by
    exact div_le_div_of_nonneg_left (by positivity) hp hfac
  have hbase : (3 : ℝ) * b / r ≤ (2 : ℝ) ^ Q := by
    rw [div_le_iff₀ (by positivity)]
    exact_mod_cast hratio
  have heq : (b : ℝ) ^ r / (((r : ℝ) / 3) ^ r) =
      (((3 : ℝ) * b / r) ^ r) := by
    rw [← div_pow]
    congr 1
    field_simp [show (r : ℝ) ≠ 0 by positivity]
  have hreal : (b.choose r : ℝ) ≤ ((2 : ℝ) ^ Q) ^ r :=
    hchoose.trans (hratio'.trans (heq ▸ pow_le_pow_left₀ (by positivity) hbase r))
  have hnat : b.choose r ≤ (2 ^ Q) ^ r := by exact_mod_cast hreal
  simpa [pow_mul] using hnat

/-! ## Finite-set helpers -/

private lemma exists_superset_card_eq_of_subset {N r : ℕ}
    {A B : Finset (Fin N)} (hAB : A ⊆ B)
    (hAr : A.card ≤ r) (hrB : r ≤ B.card) :
    ∃ C : Finset (Fin N), A ⊆ C ∧ C ⊆ B ∧ C.card = r := by
  classical
  have hdiff : r - A.card ≤ (B \ A).card := by
    rw [Finset.card_sdiff_of_subset hAB]
    omega
  obtain ⟨D, hDBA, hDcard⟩ := Finset.exists_subset_card_eq hdiff
  refine ⟨A ∪ D, Finset.subset_union_left, ?_, ?_⟩
  · exact Finset.union_subset hAB
      (hDBA.trans (Finset.sdiff_subset : B \ A ⊆ B))
  · rw [Finset.card_union_of_disjoint]
    · omega
    · rw [Finset.disjoint_left]
      intro x hxA hxD
      exact (Finset.mem_sdiff.mp (hDBA hxD)).2 hxA

private lemma isClique_union_of_cross {N : ℕ} {G : SimpleGraph (Fin N)}
    {A B : Finset (Fin N)}
    (hA : G.IsClique (↑A : Set (Fin N)))
    (hB : G.IsClique (↑B : Set (Fin N)))
    (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    G.IsClique (↑(A ∪ B) : Set (Fin N)) := by
  rw [SimpleGraph.isClique_iff] at hA hB ⊢
  intro x hx y hy hxy
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hx hy
  rcases hx with hxA | hxB <;> rcases hy with hyA | hyB
  · exact hA hxA hyA hxy
  · exact hcross x hxA y hyB
  · exact G.adj_symm (hcross y hyA x hxB)
  · exact hB hxB hyB hxy

private lemma ceilDiv_pos_of_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    0 < ceilDiv a b := by
  by_contra h
  have hz : ceilDiv a b = 0 := by omega
  have := le_mul_ceilDiv a hb
  rw [hz, Nat.mul_zero] at this
  omega

private lemma ceilDiv_four_mul_le_eight_mul {b t d z : ℕ}
    (hd : 0 < d) (hb : b ≤ 2 * t) (htz : t ≤ d * z) :
    ceilDiv (4 * b) d ≤ 8 * z := by
  apply (ceilDiv_le_iff hd).2
  calc
    4 * b ≤ 8 * t := by omega
    _ ≤ 8 * (d * z) := Nat.mul_le_mul_left 8 htz
    _ = d * (8 * z) := by ring

private lemma ceilDiv_eight_mul_le_eight_mul {t d z : ℕ}
    (hd : 0 < d) (htz : t ≤ d * z) :
    ceilDiv (8 * t) d ≤ 8 * z := by
  apply (ceilDiv_le_iff hd).2
  calc
    8 * t ≤ 8 * (d * z) := Nat.mul_le_mul_left 8 htz
    _ = d * (8 * z) := by ring

private lemma absorb_additive_reservoir {N A Y c : ℕ}
    (hmain : N ≤ A * (Y + c)) (hsmall : 2 * A * c ≤ N) :
    N ≤ 2 * A * Y := by
  have h2 : 2 * N ≤ 2 * (A * Y + A * c) :=
    Nat.mul_le_mul_left 2 (by simpa [Nat.mul_add] using hmain)
  have h3 : 2 * N ≤ 2 * A * Y + N := by
    calc
      2 * N ≤ 2 * (A * Y + A * c) := h2
      _ = 2 * A * Y + 2 * A * c := by ring
      _ ≤ 2 * A * Y + N := Nat.add_le_add_left hsmall (2 * A * Y)
  omega

private lemma eight_qz_add_three_le_nine_qz {Q z : ℕ} (h : 3 ≤ Q * z) :
    8 * Q * z + 3 ≤ 9 * Q * z := by
  calc
    8 * Q * z + 3 = 8 * (Q * z) + 3 := by ring
    _ ≤ 9 * (Q * z) := by omega
    _ = 9 * Q * z := by ring

private lemma exists_pruned_half {Q N : ℕ} (R : SimpleGraph (Fin N))
    (hNpos : 0 < N) (hsparse : SquareSparse Q R Finset.univ) :
    ∃ S : Finset (Fin N), S ⊆ Finset.univ ∧
      (∀ v ∈ S, degreeInto R v S < ceilDiv N (2 ^ Q)) ∧
      N ≤ 2 * S.card := by
  let d := 2 ^ Q
  let k := ceilDiv N d
  have hd : 0 < d := by simp [d]
  have hkpos : 0 < k := ceilDiv_pos_of_pos hNpos hd
  have hNk : N ≤ d * k := le_mul_ceilDiv N hd
  obtain ⟨S, hSuniv, hSdeg, hSprune⟩ :=
    exists_pruned_subset R (Finset.univ : Finset (Fin N)) k
  have hScardN : S.card ≤ N := by simpa using Finset.card_le_card hSuniv
  have hSquare : d * crossEdgeCount R Finset.univ Finset.univ ≤ N * N := by
    change d * squareEdgeCount R Finset.univ ≤ N * N
    simpa [SquareSparse, d] using hsparse
  have hdelmul : 2 * N * (N - S.card) ≤ N * N := by
    calc
      2 * N * (N - S.card) ≤ 2 * (d * k) * (N - S.card) := by
        exact Nat.mul_le_mul_right (N - S.card) (Nat.mul_le_mul_left 2 hNk)
      _ = d * (2 * k * (N - S.card)) := by ring
      _ ≤ d * crossEdgeCount R Finset.univ Finset.univ :=
        Nat.mul_le_mul_left d (by simpa using hSprune)
      _ ≤ N * N := hSquare
  have hdel : 2 * (N - S.card) ≤ N := by
    apply Nat.le_of_mul_le_mul_right (c := N) (hc := hNpos)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hdelmul
  refine ⟨S, hSuniv, by simpa [d, k] using hSdeg, ?_⟩
  omega

private lemma exists_sparse_blue_fibre {Q t N : ℕ}
    (R : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (hQ : 15 ≤ Q) (ht : 2 ^ Q ≤ t) (hN16 : 16 * t ≤ N)
    (hSdeg : ∀ v ∈ S, degreeInto R v S < ceilDiv N (2 ^ Q))
    (hSlarge : N ≤ 2 * S.card) :
    ∃ B C T : Finset (Fin N),
      Rᶜ.IsClique (↑B : Set (Fin N)) ∧ B.card ≤ 2 * t ∧
      C ⊆ B ∧ C.card = ceilDiv (4 * B.card) (2 ^ Q) ∧
      Disjoint B T ∧
      (∀ x ∈ B \ C, ∀ y ∈ T, Rᶜ.Adj x y) ∧
      N ≤ 2 ^ (9 * Q * ceilDiv t (2 ^ Q)) * T.card ∧
      (B.card = 2 * t ∨
        (B.card < 2 * t ∧ ∀ D ⊆ T,
          Rᶜ.IsClique (↑D : Set (Fin N)) →
            D.card ≤ ceilDiv (4 * B.card) (2 ^ Q))) := by
  classical
  let d := 2 ^ Q
  let z := ceilDiv t d
  let k := ceilDiv N d
  have hd : 0 < d := by simp [d]
  have hdlarge : 32768 ≤ d := by
    simpa [d] using Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hQ
  have ht' : d ≤ t := by simpa [d] using ht
  have htpos : 0 < t := lt_of_lt_of_le hd ht'
  have hzpos : 0 < z := ceilDiv_pos_of_pos htpos hd
  have htz : t ≤ d * z := le_mul_ceilDiv t hd
  have hNpos : 0 < N := lt_of_lt_of_le (by nlinarith : 0 < 16 * t) hN16
  let blueCliques : Finset (Finset (Fin N)) :=
    S.powerset.filter fun B ↦ Rᶜ.IsClique (↑B : Set (Fin N)) ∧ B.card ≤ 2 * t
  have hblueNonempty : blueCliques.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [blueCliques, SimpleGraph.isClique_iff]
  obtain ⟨B, hBmem, hBmax⟩ :=
    Finset.exists_max_image blueCliques Finset.card hblueNonempty
  have hBS : B ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hBmem).1
  have hBclique : Rᶜ.IsClique (↑B : Set (Fin N)) := (Finset.mem_filter.mp hBmem).2.1
  have hb_le : B.card ≤ 2 * t := (Finset.mem_filter.mp hBmem).2.2
  have hSnonempty : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hS0
    rw [hS0, Finset.card_empty, Nat.mul_zero] at hSlarge
    omega
  have hbpos : 0 < B.card := by
    obtain ⟨v, hvS⟩ := hSnonempty
    have ht2 : 1 ≤ 2 * t := by omega
    have hsingle : {v} ∈ blueCliques := by simp [blueCliques, hvS, ht2]
    have := hBmax {v} hsingle
    simpa using this
  let b := B.card
  let r := ceilDiv (4 * b) d
  have hbpos' : 0 < b := by simpa [b] using hbpos
  have hrpos : 0 < r := ceilDiv_pos_of_pos (Nat.mul_pos (by norm_num) hbpos') hd
  have hdr : 4 * b ≤ d * r := le_mul_ceilDiv (4 * b) hd
  have hrb : r ≤ b := by
    apply (ceilDiv_le_iff hd).2
    exact Nat.mul_le_mul_right b (by omega : 4 ≤ d)
  have hrz : r ≤ 8 * z :=
    ceilDiv_four_mul_le_eight_mul hd (by simpa [b] using hb_le) htz
  have hchooseBr : b.choose r ≤ 2 ^ (Q * r) :=
    choose_le_two_pow_mul hrpos
      ((Nat.mul_le_mul_right b (by norm_num : 3 ≤ 4)).trans hdr)
  have hchooseBrZ : b.choose r ≤ 2 ^ (8 * Q * z) :=
    hchooseBr.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  let bad := (S \ B).filter fun y ↦ r ≤ degreeInto R y B
  have hbadSub : bad ⊆ S \ B := Finset.filter_subset _ _
  have hbadIncidence : r * bad.card ≤ crossEdgeCount R bad B := by
    rw [crossEdgeCount_eq_sum_degreeInto]
    calc
      r * bad.card = ∑ _y ∈ bad, r := by simp [mul_comm]
      _ ≤ ∑ y ∈ bad, degreeInto R y B := by
        apply Finset.sum_le_sum
        intro y hy
        exact (Finset.mem_filter.mp hy).2
  have hdegreeMono : ∀ v ∈ B, degreeInto R v bad ≤ degreeInto R v S := by
    intro v hv
    unfold degreeInto
    exact Finset.card_mono (Finset.filter_subset_filter _ (hbadSub.trans
      (Finset.sdiff_subset : S \ B ⊆ S)))
  have hdklt : d * (k - 1) < N := by
    have hceil : d * k ≤ N + d - 1 := by
      dsimp [k, ceilDiv]
      exact Nat.mul_div_le _ _
    have hk : k - 1 + 1 = k := Nat.sub_add_cancel
      (ceilDiv_pos_of_pos hNpos hd)
    have heq : d * (k - 1) + d = d * k := by
      calc
        d * (k - 1) + d = d * ((k - 1) + 1) := by ring
        _ = d * k := by rw [hk]
    omega
  have hBdegree : ∀ v ∈ B, degreeInto R v S ≤ k - 1 := by
    intro v hv
    have h := hSdeg v (hBS hv)
    change degreeInto R v S < k at h
    omega
  have hsumB : crossEdgeCount R B bad ≤ b * (k - 1) := by
    rw [crossEdgeCount_eq_sum_degreeInto]
    calc
      ∑ v ∈ B, degreeInto R v bad ≤
          ∑ v ∈ B, degreeInto R v S := Finset.sum_le_sum hdegreeMono
      _ ≤ ∑ _v ∈ B, (k - 1) := Finset.sum_le_sum hBdegree
      _ = b * (k - 1) := by simp [b]
  have hbadlt : 4 * bad.card < N := by
    have hmain : 4 * b * bad.card < N * b := by
      calc
        4 * b * bad.card ≤ d * r * bad.card := Nat.mul_le_mul_right bad.card hdr
        _ = d * (r * bad.card) := by ring
        _ ≤ d * crossEdgeCount R bad B := Nat.mul_le_mul_left d hbadIncidence
        _ = d * crossEdgeCount R B bad := by rw [crossEdgeCount_comm]
        _ ≤ d * (b * (k - 1)) := Nat.mul_le_mul_left d hsumB
        _ = (d * (k - 1)) * b := by ring
        _ < N * b := Nat.mul_lt_mul_of_pos_right hdklt hbpos'
    exact (Nat.mul_lt_mul_right hbpos').mp (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmain)
  let U := (S \ B) \ bad
  have hBsmallN : 8 * B.card ≤ N := (by nlinarith [hN16, hb_le])
  have hUlarge : N ≤ 8 * U.card := by
    have hdecomp : S.card = B.card + bad.card + U.card := by
      have hSB : (S \ B).card = S.card - B.card := Finset.card_sdiff_of_subset hBS
      have hbad : U.card = (S \ B).card - bad.card := by
        dsimp [U]
        exact Finset.card_sdiff_of_subset hbadSub
      omega
    omega
  let fibre (C : Finset (Fin N)) : Finset (Fin N) :=
    U.filter fun y ↦ (B.filter fun x ↦ R.Adj y x) ⊆ C
  let choices := B.powersetCard r
  have hchoices : choices.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    simpa [choices, Finset.card_pos, Nat.choose_pos hrb]
  obtain ⟨C, hCchoice, hCmax⟩ :=
    Finset.exists_max_image choices (fun C ↦ (fibre C).card) hchoices
  have hCB : C ⊆ B := (Finset.mem_powersetCard.mp hCchoice).1
  have hCcard : C.card = r := (Finset.mem_powersetCard.mp hCchoice).2
  have hUcover : U ⊆ choices.biUnion fibre := by
    intro y hyU
    let A := B.filter fun x ↦ R.Adj y x
    have hAB : A ⊆ B := Finset.filter_subset _ _
    have hAcard : A.card = degreeInto R y B := by simp [A, degreeInto]
    have hyr : degreeInto R y B < r := by
      have hySB : y ∈ S \ B := (Finset.mem_sdiff.mp hyU).1
      have hynbad : y ∉ bad := (Finset.mem_sdiff.mp hyU).2
      by_contra hn
      exact hynbad (Finset.mem_filter.mpr ⟨hySB, by omega⟩)
    obtain ⟨C', hAC', hC'B, hC'card⟩ :=
      exists_superset_card_eq_of_subset hAB (by omega) hrb
    apply Finset.mem_biUnion.mpr
    refine ⟨C', Finset.mem_powersetCard.mpr ⟨hC'B, hC'card⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨hyU, by simpa [A] using hAC'⟩
  have hUfibre : U.card ≤ b.choose r * (fibre C).card := by
    calc
      U.card ≤ (choices.biUnion fibre).card := Finset.card_mono hUcover
      _ ≤ ∑ C' ∈ choices, (fibre C').card := Finset.card_biUnion_le
      _ ≤ ∑ _C' ∈ choices, (fibre C).card := by
        exact Finset.sum_le_sum fun C' hC' ↦ hCmax C' hC'
      _ = b.choose r * (fibre C).card := by
        rw [← Finset.card_powersetCard]
        simp [choices]
  have hNFibre : N ≤ 2 ^ (9 * Q * z) * (fibre C).card := by
    have hQz : 3 ≤ Q * z := by
      calc 3 ≤ 15 * 1 := by norm_num
        _ ≤ Q * z := Nat.mul_le_mul hQ (by omega)
    calc
      N ≤ 8 * U.card := hUlarge
      _ ≤ 8 * (b.choose r * (fibre C).card) := Nat.mul_le_mul_left 8 hUfibre
      _ ≤ 8 * (2 ^ (8 * Q * z) * (fibre C).card) := by
        exact Nat.mul_le_mul_left 8 (Nat.mul_le_mul_right _ hchooseBrZ)
      _ = 2 ^ (8 * Q * z + 3) * (fibre C).card := by
        rw [pow_add]
        norm_num
        ring
      _ ≤ 2 ^ (9 * Q * z) * (fibre C).card := by
        apply Nat.mul_le_mul_right
        exact Nat.pow_le_pow_right (by norm_num)
          (eight_qz_add_three_le_nine_qz hQz)
  have hBT : Disjoint B (fibre C) := by
    rw [Finset.disjoint_left]
    intro x hxB hxT
    have hxU := (Finset.mem_filter.mp hxT).1
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hxU).1).2 hxB
  have hCcrossBlue : ∀ x ∈ B \ C, ∀ y ∈ fibre C, Rᶜ.Adj x y := by
    intro x hx y hy
    have hxB := (Finset.mem_sdiff.mp hx).1
    have hxC := (Finset.mem_sdiff.mp hx).2
    have hyC := (Finset.mem_filter.mp hy).2
    rw [SimpleGraph.compl_adj]
    refine ⟨?_, ?_⟩
    · intro hxy
      subst y
      exact Finset.disjoint_left.mp hBT hxB hy
    intro hrxy
    exact hxC (hyC (Finset.mem_filter.mpr ⟨hxB, R.adj_symm hrxy⟩))
  have hmaxT : B.card < 2 * t → ∀ D ⊆ fibre C,
      Rᶜ.IsClique (↑D : Set (Fin N)) → D.card ≤ r := by
    intro hb_lt D hDT hDclique
    by_contra hDr
    have hrD : r < D.card := by omega
    let W := (B \ C) ∪ D
    have hdisj : Disjoint (B \ C) D := hBT.mono_left (Finset.sdiff_subset)
      |>.mono_right hDT
    have hWclique : Rᶜ.IsClique (↑W : Set (Fin N)) := by
      apply isClique_union_of_cross
      · exact hBclique.subset (by exact_mod_cast (Finset.sdiff_subset : B \ C ⊆ B))
      · exact hDclique
      · intro x hx y hy
        exact hCcrossBlue x hx y (hDT hy)
    have hWcard : B.card < W.card := by
      dsimp [W]
      rw [Finset.card_union_of_disjoint hdisj,
        Finset.card_sdiff_of_subset hCB, hCcard]
      omega
    have hWS : W ⊆ S := by
      apply Finset.union_subset
      · exact (Finset.sdiff_subset : B \ C ⊆ B).trans hBS
      · intro x hx
        have hxU := (Finset.mem_filter.mp (hDT hx)).1
        exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hxU).1).1
    obtain ⟨W', hW'W, hW'card⟩ :=
      Finset.exists_subset_card_eq (show B.card + 1 ≤ W.card by omega)
    have hW'mem : W' ∈ blueCliques := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr (hW'W.trans hWS), ?_, ?_⟩
      · exact hWclique.subset (by exact_mod_cast hW'W)
      · omega
    have := hBmax W' hW'mem
    omega
  refine ⟨B, C, fibre C, hBclique, hb_le, hCB, by simpa [b, r, d] using hCcard,
    hBT, hCcrossBlue, by simpa [z, d] using hNFibre, ?_⟩
  exact eq_or_lt_of_le hb_le |>.imp_right fun h ↦ ⟨h, hmaxT h⟩

/-! ## The exact dyadic sparse-colour lemma -/

/- Sudakov's sparse-colour lemma in a denominator-free dyadic form. -/
/- The first, monolithic development of the assembly is retained below as a
reference for the individual estimates.  The checked theorem following it
uses the two factored lemmas above so that every declaration stays within the
default elaboration budget.
theorem exists_monoPair_of_squareSparse {Q t N : ℕ}
    (R : SimpleGraph (Fin N))
    (hQ : 15 ≤ Q) (ht : 2 ^ Q ≤ t)
    (hsparse : SquareSparse Q R Finset.univ)
    (hN : t * 2 ^ (32 * Q * ceilDiv t (2 ^ Q)) ≤ N) :
    ∃ X Y : Finset (Fin N), HasMonoPair R X Y ∧ t ≤ X.card ∧
      N ≤ 2 ^ (32 * Q * ceilDiv t (2 ^ Q)) * Y.card := by
  classical
  let d := 2 ^ Q
  let z := ceilDiv t d
  let L := 32 * Q * z
  have hd : 0 < d := by simp [d]
  have hdlarge : 32768 ≤ d := by
    simpa [d] using Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hQ
  have ht' : d ≤ t := by simpa [d] using ht
  have htpos : 0 < t := lt_of_lt_of_le hd ht'
  have hzpos : 0 < z := ceilDiv_pos_of_pos htpos hd
  have htz : t ≤ d * z := le_mul_ceilDiv t hd
  have hL : L = 32 * Q * z := rfl
  have hLlarge : 4 ≤ L := by
    dsimp [L]
    nlinarith
  have hpow16 : 16 ≤ 2 ^ L := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hLlarge
  have hN' : t * 2 ^ L ≤ N := by simpa [d, z, L] using hN
  have hNpos : 0 < N := lt_of_lt_of_le (Nat.mul_pos htpos (by positivity)) hN'
  have hdN : d ≤ N := by
    exact ht'.trans ((Nat.le_mul_of_pos_right t (by positivity : 0 < 2 ^ L)).trans hN')

  let k := ceilDiv N d
  have hkpos : 0 < k := ceilDiv_pos_of_pos hNpos hd
  have hNk : N ≤ d * k := le_mul_ceilDiv N hd
  obtain ⟨S, hSuniv, hSdeg, hSprune⟩ :=
    exists_pruned_subset R (Finset.univ : Finset (Fin N)) k
  have hScardN : S.card ≤ N := by simpa using Finset.card_le_card hSuniv
  have hSquare : d * crossEdgeCount R Finset.univ Finset.univ ≤ N * N := by
    change d * squareEdgeCount R Finset.univ ≤ N * N
    simpa [SquareSparse, d] using hsparse
  have hdelmul : 2 * N * (N - S.card) ≤ N * N := by
    calc
      2 * N * (N - S.card) ≤ 2 * (d * k) * (N - S.card) := by
        exact Nat.mul_le_mul_right (N - S.card) (Nat.mul_le_mul_left 2 hNk)
      _ = d * (2 * k * (N - S.card)) := by ring
      _ ≤ d * crossEdgeCount R Finset.univ Finset.univ :=
        Nat.mul_le_mul_left d (by simpa using hSprune)
      _ ≤ N * N := hSquare
  have hdel : 2 * (N - S.card) ≤ N := by
    apply Nat.le_of_mul_le_mul_right (c := N) (hc := hNpos)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hdelmul
  have hSlarge : N ≤ 2 * S.card := by omega

  let blueCliques : Finset (Finset (Fin N)) :=
    S.powerset.filter fun B ↦ Rᶜ.IsClique (↑B : Set (Fin N)) ∧ B.card ≤ 2 * t
  have hblueNonempty : blueCliques.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [blueCliques, SimpleGraph.isClique_iff]
  obtain ⟨B, hBmem, hBmax⟩ :=
    Finset.exists_max_image blueCliques Finset.card hblueNonempty
  have hBS : B ⊆ S := (Finset.mem_powerset.mp (Finset.mem_filter.mp hBmem).1)
  have hBclique : Rᶜ.IsClique (↑B : Set (Fin N)) := (Finset.mem_filter.mp hBmem).2.1
  have hb_le : B.card ≤ 2 * t := (Finset.mem_filter.mp hBmem).2.2
  have hSnonempty : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hS0
    rw [hS0, Finset.card_empty, Nat.mul_zero] at hSlarge
    omega
  have hbpos : 0 < B.card := by
    obtain ⟨v, hvS⟩ := hSnonempty
    have ht2 : 1 ≤ 2 * t := by omega
    have hsingle : {v} ∈ blueCliques := by
      simp [blueCliques, hvS, ht2]
    have := hBmax {v} hsingle
    simpa using this
  let b := B.card
  let r := ceilDiv (4 * b) d
  have hbpos' : 0 < b := by simpa [b] using hbpos
  have hrpos : 0 < r := ceilDiv_pos_of_pos (Nat.mul_pos (by norm_num) hbpos') hd
  have hdr : 4 * b ≤ d * r := le_mul_ceilDiv (4 * b) hd
  have hrb : r ≤ b := by
    apply (ceilDiv_le_iff hd).2
    have h4d : 4 ≤ d := by omega
    exact Nat.mul_le_mul_right b h4d
  have hrz : r ≤ 8 * z := by
    exact ceilDiv_four_mul_le_eight_mul hd (by simpa [b] using hb_le) htz
  have hchooseBr : b.choose r ≤ 2 ^ (Q * r) :=
    choose_le_two_pow_mul hrpos ((Nat.mul_le_mul_right b (by norm_num : 3 ≤ 4)).trans hdr)
  have hchooseBrZ : b.choose r ≤ 2 ^ (8 * Q * z) := by
    exact hchooseBr.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))

  let bad := (S \ B).filter fun y ↦ r ≤ degreeInto R y B
  have hbadSub : bad ⊆ S \ B := Finset.filter_subset _ _
  have hbadIncidence : r * bad.card ≤ crossEdgeCount R bad B := by
    rw [crossEdgeCount_eq_sum_degreeInto]
    calc
      r * bad.card = ∑ _y ∈ bad, r := by simp [mul_comm]
      _ ≤ ∑ y ∈ bad, degreeInto R y B := by
        apply Finset.sum_le_sum
        intro y hy
        exact (Finset.mem_filter.mp hy).2
  have hcrossBad : crossEdgeCount R bad B = crossEdgeCount R B bad :=
    crossEdgeCount_comm R bad B
  have hdegreeMono : ∀ v ∈ B, degreeInto R v bad ≤ degreeInto R v S := by
    intro v hv
    unfold degreeInto
    exact Finset.card_mono (Finset.filter_subset_filter _ (hbadSub.trans
      (Finset.sdiff_subset : S \ B ⊆ S)))
  have hdklt : d * (k - 1) < N := by
    have hceil : d * k ≤ N + d - 1 := by
      dsimp [k]
      rw [ceilDiv_eq]
      exact Nat.mul_div_le _ _
    have hk : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
    have heq : d * (k - 1) + d = d * k := by
      rw [← Nat.mul_add, hk]
    omega
  have hBdegree : ∀ v ∈ B, degreeInto R v S ≤ k - 1 := by
    intro v hv
    have := hSdeg v (hBS hv)
    omega
  have hsumB : crossEdgeCount R B bad ≤ b * (k - 1) := by
    rw [crossEdgeCount_eq_sum_degreeInto]
    calc
      ∑ v ∈ B, degreeInto R v bad ≤
          ∑ v ∈ B, degreeInto R v S := by
            exact Finset.sum_le_sum hdegreeMono
      _ ≤ ∑ _v ∈ B, (k - 1) := by
            exact Finset.sum_le_sum hBdegree
      _ = b * (k - 1) := by simp [b]
  have hbadlt : 4 * bad.card < N := by
    have hmain : 4 * b * bad.card < N * b := by
      calc
        4 * b * bad.card ≤ d * r * bad.card :=
          Nat.mul_le_mul_right bad.card hdr
        _ = d * (r * bad.card) := by ring
        _ ≤ d * crossEdgeCount R bad B :=
          Nat.mul_le_mul_left d hbadIncidence
        _ = d * crossEdgeCount R B bad := by rw [hcrossBad]
        _ ≤ d * (b * (k - 1)) := Nat.mul_le_mul_left d hsumB
        _ = (d * (k - 1)) * b := by ring
        _ < N * b := Nat.mul_lt_mul_of_pos_right hdklt hbpos'
    exact (Nat.mul_lt_mul_right hbpos').mp (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmain)

  let U := (S \ B) \ bad
  have hBsmallN : 8 * B.card ≤ N := by
    calc
      8 * B.card ≤ 16 * t := by omega
      _ ≤ t * 2 ^ L := by nlinarith
      _ ≤ N := hN'
  have hUlarge : N ≤ 8 * U.card := by
    have hbadcard : 4 * bad.card ≤ N := hbadlt.le
    have hdecomp : S.card = B.card + bad.card + U.card := by
      have hSB : (S \ B).card = S.card - B.card :=
        Finset.card_sdiff_of_subset hBS
      have hbad : U.card = (S \ B).card - bad.card := by
        dsimp [U]
        exact Finset.card_sdiff_of_subset hbadSub
      omega
    omega

  let fibre (C : Finset (Fin N)) : Finset (Fin N) :=
    U.filter fun y ↦ (B.filter fun x ↦ R.Adj y x) ⊆ C
  let choices := B.powersetCard r
  have hchoices : choices.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    simpa [choices, Finset.card_pos, Nat.choose_pos hrb]
  obtain ⟨C, hCchoice, hCmax⟩ :=
    Finset.exists_max_image choices (fun C ↦ (fibre C).card) hchoices
  have hCB : C ⊆ B := (Finset.mem_powersetCard.mp hCchoice).1
  have hCcard : C.card = r := (Finset.mem_powersetCard.mp hCchoice).2
  have hUcover : U ⊆ choices.biUnion fibre := by
    intro y hyU
    let A := B.filter fun x ↦ R.Adj y x
    have hAB : A ⊆ B := Finset.filter_subset _ _
    have hAcard : A.card = degreeInto R y B := by simp [A, degreeInto]
    have hyr : degreeInto R y B < r := by
      have hySB : y ∈ S \ B := by
        exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hyU).1)
      have hynbad : y ∉ bad := (Finset.mem_sdiff.mp hyU).2
      by_contra hn
      exact hynbad (Finset.mem_filter.mpr ⟨hySB, by omega⟩)
    obtain ⟨C', hAC', hC'B, hC'card⟩ :=
      exists_superset_card_eq_of_subset hAB (by omega) hrb
    apply Finset.mem_biUnion.mpr
    refine ⟨C', Finset.mem_powersetCard.mpr ⟨hC'B, hC'card⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨hyU, by simpa [A] using hAC'⟩
  have hUfibre : U.card ≤ b.choose r * (fibre C).card := by
    calc
      U.card ≤ (choices.biUnion fibre).card := Finset.card_mono hUcover
      _ ≤ ∑ C' ∈ choices, (fibre C').card := Finset.card_biUnion_le
      _ ≤ ∑ _C' ∈ choices, (fibre C).card := by
        apply Finset.sum_le_sum
        intro C' hC'
        exact hCmax C' hC'
      _ = b.choose r * (fibre C).card := by
        rw [← Finset.card_powersetCard]
        simp [choices]
  have hNFibre : N ≤ 2 ^ (9 * Q * z) * (fibre C).card := by
    calc
      N ≤ 8 * U.card := hUlarge
      _ ≤ 8 * (b.choose r * (fibre C).card) := Nat.mul_le_mul_left 8 hUfibre
      _ ≤ 8 * (2 ^ (8 * Q * z) * (fibre C).card) := by
        exact Nat.mul_le_mul_left 8 (Nat.mul_le_mul_right _ hchooseBrZ)
      _ = 2 ^ (8 * Q * z + 3) * (fibre C).card := by
        rw [pow_add]
        norm_num
        ring
      _ ≤ 2 ^ (9 * Q * z) * (fibre C).card := by
        apply Nat.mul_le_mul_right
        apply Nat.pow_le_pow_right (by norm_num)
        nlinarith

  have hCcrossBlue : ∀ x ∈ B \ C, ∀ y ∈ fibre C, Rᶜ.Adj x y := by
    intro x hx y hy
    have hxB := (Finset.mem_sdiff.mp hx).1
    have hxC := (Finset.mem_sdiff.mp hx).2
    have hyU := (Finset.mem_filter.mp hy).1
    have hyC := (Finset.mem_filter.mp hy).2
    have hyB : y ∉ B := by
      exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hyU).1).2
    rw [SimpleGraph.compl_adj]
    refine ⟨?_, ?_⟩
    · exact fun hxy ↦ hyB (hxy ▸ hxB)
    · intro hrxy
      exact hxC (hyC (Finset.mem_filter.mpr ⟨hxB, R.adj_symm hrxy⟩))

  by_cases hlarge : B.card = 2 * t
  · let X := B \ C
    let Y := fibre C
    have hXcard : t ≤ X.card := by
      dsimp [X]
      rw [Finset.card_sdiff_of_subset hCB, hCcard, hlarge]
      have hrt : r ≤ t := by
        apply (ceilDiv_le_iff hd).2
        have h8d : 8 ≤ d := by omega
        dsimp [r, b]
        rw [hlarge]
        nlinarith
      omega
    have hpair : MonoPair Rᶜ X Y := by
      refine ⟨?_, ?_, ?_⟩
      · rw [Finset.disjoint_left]
        intro x hxX hxY
        have hxB : x ∈ B := (Finset.mem_sdiff.mp hxX).1
        have hxU := (Finset.mem_filter.mp hxY).1
        exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hxU).1).2 hxB
      · exact hBclique.subset (by exact_mod_cast Finset.sdiff_subset B C)
      · exact hCcrossBlue
    refine ⟨X, Y, Or.inr hpair, hXcard, ?_⟩
    exact hNFibre.trans (Nat.mul_le_mul_right Y.card
      (Nat.pow_le_pow_right (by norm_num) (by dsimp [L]; nlinarith)))
  · have hb_lt : B.card < 2 * t := by omega
    let ell := ceilDiv (8 * t) d + 1
    have hellz : ell ≤ 9 * z := by
      have h8 := ceilDiv_eight_mul_le_eight_mul hd htz
      dsimp [ell]
      nlinarith
    have hellpos : 0 < ell := by simp [ell]
    have hrell : r + 1 ≤ ell := by
      dsimp [r, ell]
      exact Nat.add_le_add_right (ceilDiv_mono_left (by dsimp [b]; omega)) 1
    have hellt : ell ≤ t := by
      dsimp [ell]
      apply Nat.add_le_of_le_sub (by omega)
      apply (ceilDiv_le_iff hd).2
      have : 8 * t ≤ d * (t - 1) := by nlinarith
      exact this
    have hratioEll : 3 * (t + ell) ≤ d * ell := by
      have h8t : 8 * t ≤ d * ceilDiv (8 * t) d := le_mul_ceilDiv (8 * t) hd
      dsimp [ell]
      nlinarith
    have hchooseEll : Nat.choose (t + ell) t ≤ 2 ^ (Q * ell) := by
      rw [Nat.choose_symm_add]
      exact choose_le_two_pow_mul hellpos hratioEll
    have hchooseEllZ : Nat.choose (t + ell) t ≤ 2 ^ (9 * Q * z) :=
      hchooseEll.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))

    have hNoBlue : ¬ ∃ D : Finset (Fin N), D ⊆ fibre C ∧
        Rᶜ.IsClique (↑D : Set (Fin N)) ∧ D.card = ell := by
      rintro ⟨D, hDT, hDclique, hDcard⟩
      let W := (B \ C) ∪ D
      have hdisj : Disjoint (B \ C) D := by
        rw [Finset.disjoint_left]
        intro x hx xD
        have hxB := (Finset.mem_sdiff.mp hx).1
        have hxT := hDT xD
        have hxU := (Finset.mem_filter.mp hxT).1
        exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hxU).1).2 hxB
      have hWclique : Rᶜ.IsClique (↑W : Set (Fin N)) := by
        apply isClique_union_of_cross
        · exact hBclique.subset (by exact_mod_cast Finset.sdiff_subset B C)
        · exact hDclique
        · intro x hx y hy
          exact hCcrossBlue x hx y (hDT hy)
      have hWcard : B.card < W.card := by
        dsimp [W]
        rw [Finset.card_union_of_disjoint hdisj,
          Finset.card_sdiff_of_subset hCB, hCcard, hDcard]
        omega
      have hWS : W ⊆ S := by
        apply Finset.union_subset
        · exact (Finset.sdiff_subset B C).trans hBS
        · intro x hx
          have hxT := hDT hx
          exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp
            (Finset.mem_filter.mp hxT).1).1).1
      have hb1 : B.card + 1 ≤ W.card := by omega
      obtain ⟨W', hW'W, hW'card⟩ := Finset.exists_subset_card_eq hb1
      have hW'mem : W' ∈ blueCliques := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powerset.mpr (hW'W.trans hWS), ?_, ?_⟩
        · exact hWclique.subset (by exact_mod_cast hW'W)
        · omega
      have := hBmax W' hW'mem
      omega

    have hTlower : Nat.choose (t + ell) t ≤ (fibre C).card := by
      have hcancel : t * 2 ^ (23 * Q * z) ≤ (fibre C).card := by
        apply Nat.le_of_mul_le_mul_left (c := 2 ^ (9 * Q * z)) (hc := by positivity)
        calc
          2 ^ (9 * Q * z) * (t * 2 ^ (23 * Q * z)) =
              t * 2 ^ (32 * Q * z) := by rw [← pow_add]; ring
          _ ≤ N := hN'
          _ ≤ 2 ^ (9 * Q * z) * (fibre C).card := hNFibre
      exact hchooseEllZ.trans ((Nat.le_mul_of_pos_left _ htpos).trans hcancel)
    obtain ⟨X, Y, hXT, hYT, hcolour, hES⟩ :=
      exists_monoPair_in_finset_choose_bound R (fibre C) t ell hTlower
    have hred : MonoPair R X Y ∧ X.card = t := by
      rcases hcolour with hred | hblue
      · exact hred
      · exfalso
        apply hNoBlue
        exact ⟨X, hXT, hblue.1, hblue.2⟩
    have hES' : (fibre C).card ≤ 2 ^ (9 * Q * z) * (Y.card + t + ell) := by
      exact hES.trans (Nat.mul_le_mul_right _ hchooseEllZ)
    have hNYadd : N ≤ 2 ^ (18 * Q * z) * (Y.card + t + ell) := by
      calc
        N ≤ 2 ^ (9 * Q * z) * (fibre C).card := hNFibre
        _ ≤ 2 ^ (9 * Q * z) *
            (2 ^ (9 * Q * z) * (Y.card + t + ell)) := Nat.mul_le_mul_left _ hES'
        _ = 2 ^ (18 * Q * z) * (Y.card + t + ell) := by
          rw [← pow_add]
          congr 1
          ring
    have haddSmall : 2 * (2 ^ (18 * Q * z) * (t + ell)) ≤ N := by
      calc
        2 * (2 ^ (18 * Q * z) * (t + ell)) ≤
            4 * (2 ^ (18 * Q * z) * t) := by nlinarith
        _ ≤ t * 2 ^ (32 * Q * z) := by
          rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]
          apply Nat.mul_le_mul_left t
          apply Nat.pow_le_pow_right (by norm_num)
          nlinarith
        _ ≤ N := hN'
    have hNY : N ≤ 2 * 2 ^ (18 * Q * z) * Y.card := by
      have htwice := Nat.mul_le_mul_left 2 hNYadd
      ring_nf at htwice ⊢
      omega
    have h2pow : 2 * 2 ^ (18 * Q * z) ≤ 2 ^ L := by
      rw [show 2 * 2 ^ (18 * Q * z) = 2 ^ (18 * Q * z + 1) by
        rw [pow_succ]; ring]
      apply Nat.pow_le_pow_right (by norm_num)
      dsimp [L]
      nlinarith
    refine ⟨X, Y, Or.inl hred.1, by omega, ?_⟩
    exact hNY.trans (Nat.mul_le_mul_right Y.card h2pow)
-/

private lemma finish_sparse_small_branch {Q t N b : ℕ}
    (R : SimpleGraph (Fin N)) (T : Finset (Fin N))
    (hQ : 15 ≤ Q) (ht : 2 ^ Q ≤ t)
    (hN : t * 2 ^ (32 * Q * ceilDiv t (2 ^ Q)) ≤ N)
    (hNT : N ≤ 2 ^ (9 * Q * ceilDiv t (2 ^ Q)) * T.card)
    (hb : b < 2 * t)
    (hmaxT : ∀ D ⊆ T, Rᶜ.IsClique (↑D : Set (Fin N)) →
      D.card ≤ ceilDiv (4 * b) (2 ^ Q)) :
    ∃ X Y : Finset (Fin N), HasMonoPair R X Y ∧ t ≤ X.card ∧
      N ≤ 2 ^ (32 * Q * ceilDiv t (2 ^ Q)) * Y.card := by
  classical
  let d := 2 ^ Q
  let z := ceilDiv t d
  let L := 32 * Q * z
  let r := ceilDiv (4 * b) d
  let ell := ceilDiv (8 * t) d + 1
  have hd : 0 < d := by simp [d]
  have hdlarge : 32768 ≤ d := by
    simpa [d] using Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hQ
  have ht' : d ≤ t := by simpa [d] using ht
  have htpos : 0 < t := lt_of_lt_of_le hd ht'
  have hzpos : 0 < z := ceilDiv_pos_of_pos htpos hd
  have htz : t ≤ d * z := le_mul_ceilDiv t hd
  have hN' : t * 2 ^ L ≤ N := by simpa [d, z, L] using hN
  have hNT' : N ≤ 2 ^ (9 * Q * z) * T.card := by simpa [d, z] using hNT
  have hellz : ell ≤ 9 * z := by
    have h8 := ceilDiv_eight_mul_le_eight_mul hd htz
    change ceilDiv (8 * t) d + 1 ≤ 9 * z
    omega
  have hellpos : 0 < ell := by simp [ell]
  have hrell : r + 1 ≤ ell := by
    dsimp [r, ell]
    exact Nat.add_le_add_right (ceilDiv_mono_left (by omega)) 1
  have hellt : ell ≤ t := by
    dsimp [ell]
    apply Nat.add_le_of_le_sub (by omega)
    apply (ceilDiv_le_iff hd).2
    have htTwo : t ≤ 2 * (t - 1) := by omega
    calc
      8 * t ≤ 8 * (2 * (t - 1)) := Nat.mul_le_mul_left 8 htTwo
      _ = 16 * (t - 1) := by ring
      _ ≤ d * (t - 1) := Nat.mul_le_mul_right (t - 1) (by omega)
  have hratioEll : 3 * (t + ell) ≤ d * ell := by
    have h8t : 8 * t ≤ d * ceilDiv (8 * t) d := le_mul_ceilDiv (8 * t) hd
    calc
      3 * (t + ell) ≤ 6 * t := by omega
      _ ≤ 8 * t := by omega
      _ ≤ d * ceilDiv (8 * t) d := h8t
      _ ≤ d * ell := by
        apply Nat.mul_le_mul_left
        simp [ell]
  have hchooseEll : Nat.choose (t + ell) t ≤ 2 ^ (Q * ell) := by
    rw [Nat.choose_symm_add]
    exact choose_le_two_pow_mul hellpos hratioEll
  have hchooseEllZ : Nat.choose (t + ell) t ≤ 2 ^ (9 * Q * z) :=
    hchooseEll.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  have hNoBlue : ¬ ∃ D : Finset (Fin N), D ⊆ T ∧
      Rᶜ.IsClique (↑D : Set (Fin N)) ∧ D.card = ell := by
    rintro ⟨D, hDT, hDclique, hDcard⟩
    have hD := hmaxT D hDT hDclique
    change D.card ≤ r at hD
    rw [hDcard] at hD
    omega
  have hTlower : Nat.choose (t + ell) t ≤ T.card := by
    have hcancel : t * 2 ^ (23 * Q * z) ≤ T.card := by
      apply Nat.le_of_mul_le_mul_left (c := 2 ^ (9 * Q * z)) (hc := by positivity)
      calc
        2 ^ (9 * Q * z) * (t * 2 ^ (23 * Q * z)) =
            t * (2 ^ (9 * Q * z) * 2 ^ (23 * Q * z)) := by ring
        _ = t * 2 ^ (32 * Q * z) := by
            rw [← pow_add]
            congr 1
            ring
        _ ≤ N := hN'
        _ ≤ 2 ^ (9 * Q * z) * T.card := hNT'
    have hpows : 2 ^ (9 * Q * z) ≤ 2 ^ (23 * Q * z) :=
      Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    exact hchooseEllZ.trans (hpows.trans
      ((Nat.le_mul_of_pos_left _ htpos).trans hcancel))
  obtain ⟨X, Y, hXT, hYT, hcolour, hES⟩ :=
    exists_monoPair_in_finset_choose_bound R T t ell hTlower
  have hred : MonoPair R X Y ∧ X.card = t := by
    rcases hcolour with hred | hblue
    · exact hred
    · exfalso
      exact hNoBlue ⟨X, hXT, hblue.1.2.1, hblue.2⟩
  have hES' : T.card ≤ 2 ^ (9 * Q * z) * (Y.card + t + ell) :=
    hES.trans (Nat.mul_le_mul_right _ hchooseEllZ)
  have hNYadd : N ≤ 2 ^ (18 * Q * z) * (Y.card + t + ell) := by
    calc
      N ≤ 2 ^ (9 * Q * z) * T.card := hNT'
      _ ≤ 2 ^ (9 * Q * z) *
          (2 ^ (9 * Q * z) * (Y.card + t + ell)) := Nat.mul_le_mul_left _ hES'
      _ = 2 ^ (18 * Q * z) * (Y.card + t + ell) := by
        rw [← mul_assoc, ← pow_add]
        congr 2
        ring
  have haddSmall : 2 * (2 ^ (18 * Q * z) * (t + ell)) ≤ N := by
    calc
      2 * (2 ^ (18 * Q * z) * (t + ell)) ≤
          2 * (2 ^ (18 * Q * z) * (2 * t)) := by
            exact Nat.mul_le_mul_left 2
              (Nat.mul_le_mul_left (2 ^ (18 * Q * z)) (by omega))
      _ = 4 * (2 ^ (18 * Q * z) * t) := by ring
      _ ≤ t * 2 ^ (32 * Q * z) := by
        rw [show 4 = 2 ^ 2 by norm_num]
        calc
          2 ^ 2 * (2 ^ (18 * Q * z) * t) =
              t * 2 ^ (18 * Q * z + 2) := by rw [pow_add]; ring
          _ ≤ t * 2 ^ (32 * Q * z) := by
            apply Nat.mul_le_mul_left
            apply Nat.pow_le_pow_right (by norm_num)
            have hQz : 1 ≤ Q * z := Nat.mul_pos (by omega) hzpos
            calc
              18 * Q * z + 2 = 18 * (Q * z) + 2 := by ring
              _ ≤ 32 * (Q * z) := by omega
              _ = 32 * Q * z := by ring
      _ ≤ N := hN'
  have hNY : N ≤ 2 * 2 ^ (18 * Q * z) * Y.card := by
    exact absorb_additive_reservoir (by simpa [Nat.add_assoc] using hNYadd) (by
      simpa [mul_assoc] using haddSmall)
  have h2pow : 2 * 2 ^ (18 * Q * z) ≤ 2 ^ L := by
    rw [show 2 * 2 ^ (18 * Q * z) = 2 ^ (18 * Q * z + 1) by
      rw [pow_succ]; ring]
    apply Nat.pow_le_pow_right (by norm_num)
    have hQz : 1 ≤ Q * z := Nat.mul_pos (by omega) hzpos
    dsimp [L]
    calc
      18 * Q * z + 1 = 18 * (Q * z) + 1 := by ring
      _ ≤ 32 * (Q * z) := by omega
      _ = 32 * Q * z := by ring
  refine ⟨X, Y, Or.inl hred.1, by omega, ?_⟩
  exact hNY.trans (Nat.mul_le_mul_right Y.card h2pow)

/-- Sudakov's sparse-colour lemma in a denominator-free dyadic form. -/
theorem exists_monoPair_of_squareSparse {Q t N : ℕ}
    (R : SimpleGraph (Fin N))
    (hQ : 15 ≤ Q) (ht : 2 ^ Q ≤ t)
    (hsparse : SquareSparse Q R Finset.univ)
    (hN : t * 2 ^ (32 * Q * ceilDiv t (2 ^ Q)) ≤ N) :
    ∃ X Y : Finset (Fin N), HasMonoPair R X Y ∧ t ≤ X.card ∧
      N ≤ 2 ^ (32 * Q * ceilDiv t (2 ^ Q)) * Y.card := by
  classical
  let d := 2 ^ Q
  let z := ceilDiv t d
  let L := 32 * Q * z
  have hd : 0 < d := by simp [d]
  have hdlarge : 32768 ≤ d := by
    simpa [d] using Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hQ
  have ht' : d ≤ t := by simpa [d] using ht
  have htpos : 0 < t := lt_of_lt_of_le hd ht'
  have hzpos : 0 < z := ceilDiv_pos_of_pos htpos hd
  have htz : t ≤ d * z := le_mul_ceilDiv t hd
  have hLlarge : 4 ≤ L := by dsimp [L]; nlinarith
  have hpow16 : 16 ≤ 2 ^ L := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hLlarge
  have hN' : t * 2 ^ L ≤ N := by simpa [d, z, L] using hN
  have hNpos : 0 < N := lt_of_lt_of_le (Nat.mul_pos htpos (by positivity)) hN'
  have hN16 : 16 * t ≤ N := by
    calc
      16 * t ≤ t * 2 ^ L := by nlinarith
      _ ≤ N := hN'
  obtain ⟨S, hSuniv, hSdeg, hSlarge⟩ := exists_pruned_half R hNpos hsparse
  obtain ⟨B, C, T, hBclique, hb_le, hCB, hCcard, hBT, hcross,
      hNT, hcase⟩ :=
    exists_sparse_blue_fibre R S hQ ht hN16 hSdeg hSlarge
  let r := ceilDiv (4 * B.card) d
  have hCr : C.card = r := by simpa [r, d] using hCcard
  rcases hcase with hlarge | ⟨hb_lt, hmaxT⟩
  · let X := B \ C
    have hrt : r ≤ t := by
      apply (ceilDiv_le_iff hd).2
      have h8d : 8 ≤ d := by omega
      change 4 * B.card ≤ d * t
      rw [hlarge]
      nlinarith
    have hXcard : t ≤ X.card := by
      dsimp [X]
      rw [Finset.card_sdiff_of_subset hCB, hCr, hlarge]
      omega
    have hpair : MonoPair Rᶜ X T := by
      refine ⟨hBT.mono_left (Finset.sdiff_subset : B \ C ⊆ B), ?_, ?_⟩
      · exact hBclique.subset (by exact_mod_cast (Finset.sdiff_subset : B \ C ⊆ B))
      · exact hcross
    refine ⟨X, T, Or.inr hpair, hXcard, ?_⟩
    have hNT' : N ≤ 2 ^ (9 * Q * z) * T.card := by simpa [d, z] using hNT
    have hexp : 9 * Q * z ≤ L := by
      dsimp [L]
      exact Nat.mul_le_mul_right z (Nat.mul_le_mul_right Q (by norm_num))
    exact hNT'.trans (Nat.mul_le_mul_right T.card
      (Nat.pow_le_pow_right (by norm_num) hexp))
  · exact finish_sparse_small_branch R T hQ ht hN hNT hb_lt hmaxT
  /- The following is the inlined version of `finish_sparse_small_branch`,
  retained as a record of the constant bookkeeping.
    let ell := ceilDiv (8 * t) d + 1
    have hellz : ell ≤ 9 * z := by
      have h8 := ceilDiv_eight_mul_le_eight_mul hd htz
      change ceilDiv (8 * t) d + 1 ≤ 9 * z
      omega
    have hellpos : 0 < ell := by simp [ell]
    have hrell : r + 1 ≤ ell := by
      dsimp [r, ell]
      exact Nat.add_le_add_right (ceilDiv_mono_left (by omega)) 1
    have hellt : ell ≤ t := by
      dsimp [ell]
      apply Nat.add_le_of_le_sub (by omega)
      apply (ceilDiv_le_iff hd).2
      have htTwo : t ≤ 2 * (t - 1) := by omega
      calc
        8 * t ≤ 8 * (2 * (t - 1)) := Nat.mul_le_mul_left 8 htTwo
        _ = 16 * (t - 1) := by ring
        _ ≤ d * (t - 1) := Nat.mul_le_mul_right (t - 1) (by omega)
    have hratioEll : 3 * (t + ell) ≤ d * ell := by
      have h8t : 8 * t ≤ d * ceilDiv (8 * t) d := le_mul_ceilDiv (8 * t) hd
      calc
        3 * (t + ell) ≤ 6 * t := by omega
        _ ≤ 8 * t := by omega
        _ ≤ d * ceilDiv (8 * t) d := h8t
        _ ≤ d * ell := by
          apply Nat.mul_le_mul_left
          simp [ell]
    have hchooseEll : Nat.choose (t + ell) t ≤ 2 ^ (Q * ell) := by
      rw [Nat.choose_symm_add]
      exact choose_le_two_pow_mul hellpos hratioEll
    have hchooseEllZ : Nat.choose (t + ell) t ≤ 2 ^ (9 * Q * z) :=
      hchooseEll.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
    have hNoBlue : ¬ ∃ D : Finset (Fin N), D ⊆ T ∧
        Rᶜ.IsClique (↑D : Set (Fin N)) ∧ D.card = ell := by
      rintro ⟨D, hDT, hDclique, hDcard⟩
      have := hmaxT D hDT hDclique
      rw [hDcard] at this
      omega
    have hTlower : Nat.choose (t + ell) t ≤ T.card := by
      have hcancel : t * 2 ^ (23 * Q * z) ≤ T.card := by
        apply Nat.le_of_mul_le_mul_left (c := 2 ^ (9 * Q * z)) (hc := by positivity)
        calc
          2 ^ (9 * Q * z) * (t * 2 ^ (23 * Q * z)) =
              t * (2 ^ (9 * Q * z) * 2 ^ (23 * Q * z)) := by ring
          _ = t * 2 ^ (32 * Q * z) := by
              rw [← pow_add]
              congr 1
              ring
          _ ≤ N := hN'
          _ ≤ 2 ^ (9 * Q * z) * T.card := by simpa [d, z] using hNT
      have hpows : 2 ^ (9 * Q * z) ≤ 2 ^ (23 * Q * z) :=
        Nat.pow_le_pow_right (by norm_num) (by nlinarith)
      exact hchooseEllZ.trans (hpows.trans
        ((Nat.le_mul_of_pos_left _ htpos).trans hcancel))
    obtain ⟨X, Y, hXT, hYT, hcolour, hES⟩ :=
      exists_monoPair_in_finset_choose_bound R T t ell hTlower
    have hred : MonoPair R X Y ∧ X.card = t := by
      rcases hcolour with hred | hblue
      · exact hred
      · exfalso
        exact hNoBlue ⟨X, hXT, hblue.1.2.1, hblue.2⟩
    have hES' : T.card ≤ 2 ^ (9 * Q * z) * (Y.card + t + ell) :=
      hES.trans (Nat.mul_le_mul_right _ hchooseEllZ)
    have hNYadd : N ≤ 2 ^ (18 * Q * z) * (Y.card + t + ell) := by
      calc
        N ≤ 2 ^ (9 * Q * z) * T.card := by simpa [d, z] using hNT
        _ ≤ 2 ^ (9 * Q * z) *
            (2 ^ (9 * Q * z) * (Y.card + t + ell)) := Nat.mul_le_mul_left _ hES'
        _ = 2 ^ (18 * Q * z) * (Y.card + t + ell) := by
          rw [← mul_assoc, ← pow_add]
          congr 2
          ring
    have haddSmall : 2 * (2 ^ (18 * Q * z) * (t + ell)) ≤ N := by
      calc
        2 * (2 ^ (18 * Q * z) * (t + ell)) ≤
            2 * (2 ^ (18 * Q * z) * (2 * t)) := by
              exact Nat.mul_le_mul_left 2
                (Nat.mul_le_mul_left (2 ^ (18 * Q * z)) (by omega))
        _ = 4 * (2 ^ (18 * Q * z) * t) := by ring
        _ ≤ t * 2 ^ (32 * Q * z) := by
          rw [show 4 = 2 ^ 2 by norm_num]
          calc
            2 ^ 2 * (2 ^ (18 * Q * z) * t) =
                t * 2 ^ (18 * Q * z + 2) := by rw [pow_add]; ring
            _ ≤ t * 2 ^ (32 * Q * z) := by
              apply Nat.mul_le_mul_left
              apply Nat.pow_le_pow_right (by norm_num)
              have hQz : 1 ≤ Q * z := Nat.mul_pos (by omega) hzpos
              nlinarith
        _ ≤ N := hN'
    have hNY : N ≤ 2 * 2 ^ (18 * Q * z) * Y.card := by
      exact absorb_additive_reservoir (by simpa [Nat.add_assoc] using hNYadd) (by
        simpa [mul_assoc] using haddSmall)
    have h2pow : 2 * 2 ^ (18 * Q * z) ≤ 2 ^ L := by
      rw [show 2 * 2 ^ (18 * Q * z) = 2 ^ (18 * Q * z + 1) by
        rw [pow_succ]; ring]
      apply Nat.pow_le_pow_right (by norm_num)
      have hQz : 1 ≤ Q * z := Nat.mul_pos (by omega) hzpos
      dsimp [L]
      nlinarith
    refine ⟨X, Y, Or.inl hred.1, by omega, ?_⟩
    exact hNY.trans (Nat.mul_le_mul_right Y.card h2pow)
  -/

end Erdos546
