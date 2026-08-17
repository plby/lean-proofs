/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos110.TypeRealization

/-!
# A Specker relation with no short odd closed walks

We use the interval consequences of the disjoint type
`0^s (01)^(n-s) 1^s`.  A deliberately generous width bound permits a
fixed middle coordinate throughout a walk; this is the standard Specker
argument with the inessential sharp constant removed.
-/

noncomputable section

open Finset

namespace Erdos110
namespace Specker

/-- A strictly increasing `n`-tuple. -/
structure IncSeq (n : ℕ) (α : Type*) [LinearOrder α] where
  val : Fin n → α
  strictMono : StrictMono val

instance {n : ℕ} {α : Type*} [LinearOrder α] :
    CoeFun (IncSeq n α) (fun _ ↦ Fin n → α) :=
  ⟨IncSeq.val⟩

/-- The inequalities forced by the oriented Specker type. -/
def Up {n : ℕ} {α : Type*} [LinearOrder α]
    (s : ℕ) (a b : IncSeq n α) : Prop :=
  ∀ i : ℕ, ∀ _hsi : s < i, ∀ hin : i < n,
    b ⟨i - s - 1, (Nat.sub_le i (s + 1)).trans_lt hin⟩ < a ⟨i, hin⟩ ∧
      a ⟨i, hin⟩ < b ⟨i - s, (Nat.sub_le i s).trans_lt hin⟩

/-- The symmetric Specker relation. -/
def Adj {n : ℕ} {α : Type*} [LinearOrder α]
    (s : ℕ) (a b : IncSeq n α) : Prop :=
  Up s a b ∨ Up s b a

theorem adj_symm {n : ℕ} {α : Type*} [LinearOrder α]
    {s : ℕ} {a b : IncSeq n α} : Adj s a b → Adj s b a := by
  rintro (h | h) <;> simp [Adj, h]

theorem not_adj_self {n : ℕ} {α : Type*} [LinearOrder α]
    {s : ℕ} {a : IncSeq n α} (hs : s + 1 < n) : ¬ Adj s a a := by
  intro h
  rcases h with h | h
  all_goals
    have hbad := (h (s + 1) (by omega) hs).2
    have h1n : 1 < n := lt_of_le_of_lt (Nat.succ_le_succ (Nat.zero_le s)) hs
    have hidx : (⟨1, h1n⟩ : Fin n) ≤ ⟨s + 1, hs⟩ := by
      exact Nat.succ_le_succ (Nat.zero_le s)
    have hgood : a ⟨1, h1n⟩ ≤ a ⟨s + 1, hs⟩ :=
      a.strictMono.monotone hidx
    have hsubn : s + 1 - s < n := by omega
    have heq : (⟨s + 1 - s, hsubn⟩ : Fin n) = ⟨1, h1n⟩ := by
      apply Fin.ext
      simp
    rw [heq] at hbad
    exact (not_lt_of_ge hgood) hbad

/-- Number of forward-oriented steps before `j`. -/
private def upCount (up : ℕ → Prop) [DecidablePred up] (j : ℕ) : ℕ :=
  ((Finset.range j).filter up).card

/-- Number of backward-oriented steps before `j`. -/
private def downCount (up : ℕ → Prop) [DecidablePred up] (j : ℕ) : ℕ :=
  j - upCount up j

private theorem upCount_le (up : ℕ → Prop) [DecidablePred up] (j : ℕ) :
    upCount up j ≤ j := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range j)

private theorem upCount_succ_true (up : ℕ → Prop) [DecidablePred up]
    (j : ℕ) (h : up j) : upCount up (j + 1) = upCount up j + 1 := by
  change ((Finset.range (j + 1)).filter up).card =
    ((Finset.range j).filter up).card + 1
  rw [Finset.range_add_one, Finset.filter_insert]
  simp only [h, if_pos]
  exact Finset.card_insert_of_notMem (by simp)

private theorem upCount_succ_false (up : ℕ → Prop) [DecidablePred up]
    (j : ℕ) (h : ¬ up j) : upCount up (j + 1) = upCount up j := by
  change ((Finset.range (j + 1)).filter up).card =
    ((Finset.range j).filter up).card
  rw [Finset.range_add_one, Finset.filter_insert]
  simp [h]

private theorem downCount_succ_true (up : ℕ → Prop) [DecidablePred up]
    (j : ℕ) (h : up j) : downCount up (j + 1) = downCount up j := by
  rw [downCount, downCount, upCount_succ_true up j h]
  have := upCount_le up j
  omega

private theorem downCount_succ_false (up : ℕ → Prop) [DecidablePred up]
    (j : ℕ) (h : ¬ up j) : downCount up (j + 1) = downCount up j + 1 := by
  rw [downCount, downCount, upCount_succ_false up j h]
  have := upCount_le up j
  omega

private def lowerIndex (ell s u d : ℕ) : ℕ :=
  (ell - u) * (s + 1) + d * s

private def middleIndex (ell s : ℕ) : ℕ := ell * (s + 1)

private def upperIndex (ell s u d : ℕ) : ℕ :=
  (ell - u) * (s + 1) + u + d * (s + 1)

private theorem count_sum (up : ℕ → Prop) [DecidablePred up] (j : ℕ) :
    upCount up j + downCount up j = j := by
  dsimp [downCount]
  have := upCount_le up j
  omega

private theorem lower_le_upper (ell s u d : ℕ) :
    lowerIndex ell s u d ≤ upperIndex ell s u d := by
  dsimp [lowerIndex, upperIndex]
  nlinarith

private theorem indices_lt {ell s n j u d : ℕ}
    (hj : j ≤ ell) (hu : u ≤ j) (hud : u + d = j)
    (hn : 3 * ell * (s + 1) + s + 1 < n) :
    lowerIndex ell s u d < n ∧ middleIndex ell s < n ∧
      upperIndex ell s u d < n := by
  dsimp [lowerIndex, middleIndex, upperIndex]
  have helu : ell - u ≤ ell := Nat.sub_le _ _
  have hd : d ≤ ell := by omega
  have hu' : u ≤ ell := hu.trans hj
  have h1 := Nat.mul_le_mul_right (s + 1) helu
  have h2 := Nat.mul_le_mul_right s hd
  have h3 := Nat.mul_le_mul_right (s + 1) hd
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem lower_pos_of_step {ell s j u d : ℕ}
    (hj : j < ell) (hu : u ≤ j) : 0 < lowerIndex ell s u d := by
  dsimp [lowerIndex]
  have : u < ell := hu.trans_lt hj
  have hsub : 0 < ell - u := Nat.sub_pos_of_lt this
  have hmul : 0 < (ell - u) * (s + 1) := Nat.mul_pos hsub (by omega)
  omega

private theorem lower_gt_s_of_step {ell s j u d : ℕ}
    (hj : j < ell) (hu : u ≤ j) : s < lowerIndex ell s u d := by
  dsimp [lowerIndex]
  have hsub : 0 < ell - u := Nat.sub_pos_of_lt (hu.trans_lt hj)
  have hone : 1 ≤ ell - u := hsub
  have hmul := Nat.mul_le_mul_right (s + 1) hone
  nlinarith

private theorem upper_shift_lt {ell s n j u d : ℕ}
    (hj : j ≤ ell) (hu : u ≤ j) (hud : u + d = j)
    (hn : 3 * ell * (s + 1) + s + 1 < n) :
    upperIndex ell s u d + s + 1 < n := by
  dsimp [upperIndex]
  have helu : ell - u ≤ ell := Nat.sub_le _ _
  have hd : d ≤ ell := by omega
  have hu' : u ≤ ell := hu.trans hj
  have h1 := Nat.mul_le_mul_right (s + 1) helu
  have h2 := Nat.mul_le_mul_right (s + 1) hd
  nlinarith

/-- Coordinate bounds propagated along an oriented walk. -/
private theorem path_bounds
    {n : ℕ} {α : Type*} [LinearOrder α]
    (s ell : ℕ) (hn : 3 * ell * (s + 1) + s + 1 < n)
    (v : ℕ → IncSeq n α) (up : ℕ → Prop) [DecidablePred up]
    (hedge : ∀ j < ell, if up j then Up s (v j) (v (j + 1))
      else Up s (v (j + 1)) (v j)) :
    ∀ j, ∀ hj : j ≤ ell,
      let u := upCount up j
      let d := downCount up j
      let L := lowerIndex ell s u d
      let M := middleIndex ell s
      let R := upperIndex ell s u d
      (v j ⟨L, by
          simpa only [L, u, d] using
            (indices_lt (ell := ell) (s := s) (n := n) (j := j)
              (u := upCount up j) (d := downCount up j) hj
              (upCount_le up j) (count_sum up j) hn).1⟩ ≤
          v 0 ⟨M, by
            simpa only [M] using
              (indices_lt (ell := ell) (s := s) (n := n) (j := j)
                (u := upCount up j) (d := downCount up j) hj
                (upCount_le up j) (count_sum up j) hn).2.1⟩ ∧
        v 0 ⟨M, by
          simpa only [M] using
            (indices_lt (ell := ell) (s := s) (n := n) (j := j)
              (u := upCount up j) (d := downCount up j) hj
              (upCount_le up j) (count_sum up j) hn).2.1⟩ ≤
          v j ⟨R, by
            simpa only [R, u, d] using
              (indices_lt (ell := ell) (s := s) (n := n) (j := j)
                (u := upCount up j) (d := downCount up j) hj
                (upCount_le up j) (count_sum up j) hn).2.2⟩) ∧
      (0 < j →
        v j ⟨L, by
          simpa only [L, u, d] using
            (indices_lt (ell := ell) (s := s) (n := n) (j := j)
              (u := upCount up j) (d := downCount up j) hj
              (upCount_le up j) (count_sum up j) hn).1⟩ <
            v 0 ⟨M, by
              simpa only [M] using
                (indices_lt (ell := ell) (s := s) (n := n) (j := j)
                  (u := upCount up j) (d := downCount up j) hj
                  (upCount_le up j) (count_sum up j) hn).2.1⟩ ∧
          v 0 ⟨M, by
            simpa only [M] using
              (indices_lt (ell := ell) (s := s) (n := n) (j := j)
                (u := upCount up j) (d := downCount up j) hj
                (upCount_le up j) (count_sum up j) hn).2.1⟩ <
            v j ⟨R, by
              simpa only [R, u, d] using
                (indices_lt (ell := ell) (s := s) (n := n) (j := j)
                  (u := upCount up j) (d := downCount up j) hj
                  (upCount_le up j) (count_sum up j) hn).2.2⟩) := by
  intro j hj
  induction j with
  | zero =>
      simp [upCount, downCount, lowerIndex, middleIndex, upperIndex]
  | succ j ih =>
      have hjlt : j < ell := by omega
      have hih := ih (by omega)
      let u := upCount up j
      let d := downCount up j
      have hu : u ≤ j := upCount_le up j
      have hud : u + d = j := by dsimp [d, downCount]; omega
      have hLpos : 0 < lowerIndex ell s u d := lower_pos_of_step hjlt hu
      have hLlarge : s < lowerIndex ell s u d := lower_gt_s_of_step hjlt hu
      have hLR : lowerIndex ell s u d ≤ upperIndex ell s u d :=
        lower_le_upper ell s u d
      have hRpos : 0 < upperIndex ell s u d :=
        hLpos.trans_le hLR
      have hRlarge : s < upperIndex ell s u d := hLlarge.trans_le hLR
      have hRshift : upperIndex ell s u d + s + 1 < n :=
        upper_shift_lt (by omega) hu hud hn
      have hLshift : lowerIndex ell s u d + s + 1 < n :=
        (Nat.add_le_add_right (lower_le_upper ell s u d) (s + 1)).trans_lt hRshift
      by_cases hup : up j
      · have he := by simpa [hup] using hedge j hjlt
        have hlow := (he (lowerIndex ell s u d) hLlarge
          (indices_lt (by omega) hu hud hn).1).1
        have hupp := (he (upperIndex ell s u d) hRlarge
          (indices_lt (by omega) hu hud hn).2.2).2
        have hu' := upCount_succ_true up j hup
        have hd' := downCount_succ_true up j hup
        dsimp only
        simp only [hu', hd']
        have hLidx : lowerIndex ell s (u + 1) d + s + 1 =
            lowerIndex ell s u d := by
          have hsub : ell - (u + 1) + 1 = ell - u := by omega
          have hmul := congrArg (fun x : ℕ ↦ x * (s + 1)) hsub
          dsimp [lowerIndex]
          nlinarith
        have hRidx : upperIndex ell s (u + 1) d + s =
            upperIndex ell s u d := by
          have hsub : ell - (u + 1) + 1 = ell - u := by omega
          have hmul := congrArg (fun x : ℕ ↦ x * (s + 1)) hsub
          dsimp [upperIndex]
          nlinarith
        have hlow' :
            v (j + 1) ⟨lowerIndex ell s (u + 1) d, by
              exact (indices_lt (j := j + 1) (by omega) (by omega)
                (by omega) hn).1⟩ <
              v j ⟨lowerIndex ell s u d, (indices_lt (by omega) hu hud hn).1⟩ := by
          convert hlow using 1 <;> congr 1 <;> apply Fin.ext <;> simp <;> omega
        have hupp' :
            v j ⟨upperIndex ell s u d, (indices_lt (by omega) hu hud hn).2.2⟩ <
              v (j + 1) ⟨upperIndex ell s (u + 1) d, by
                exact (indices_lt (j := j + 1) (by omega) (by omega)
                  (by omega) hn).2.2⟩ := by
          convert hupp using 1 <;> congr 1 <;> apply Fin.ext <;> simp <;> omega
        exact ⟨⟨hlow'.le.trans hih.1.1, hih.1.2.trans hupp'.le⟩,
          fun _ ↦ ⟨hlow'.trans_le hih.1.1, hih.1.2.trans_lt hupp'⟩⟩
      · have he := by simpa [hup] using hedge j hjlt
        have hlowA := (he (lowerIndex ell s u d + s) (by omega)
          (by omega)).2
        have huppB := (he (upperIndex ell s u d + s + 1) (by omega)
          hRshift).1
        have hu' := upCount_succ_false up j hup
        have hd' := downCount_succ_false up j hup
        dsimp only
        simp only [hu', hd']
        have hLidx : lowerIndex ell s u (d + 1) =
            lowerIndex ell s u d + s := by
          dsimp [lowerIndex]
          ring
        have hRidx : upperIndex ell s u (d + 1) =
            upperIndex ell s u d + s + 1 := by
          dsimp [upperIndex]
          ring
        have hlow' :
            v (j + 1) ⟨lowerIndex ell s u (d + 1), by
              exact (indices_lt (j := j + 1) (by omega) (by omega)
                (by omega) hn).1⟩ <
              v j ⟨lowerIndex ell s u d, (indices_lt (by omega) hu hud hn).1⟩ := by
          convert hlowA using 1 <;> congr 1 <;> apply Fin.ext <;> simp <;> omega
        have hupp' :
            v j ⟨upperIndex ell s u d, (indices_lt (by omega) hu hud hn).2.2⟩ <
              v (j + 1) ⟨upperIndex ell s u (d + 1), by
                exact (indices_lt (j := j + 1) (by omega) (by omega)
                  (by omega) hn).2.2⟩ := by
          convert huppB using 1 <;> congr 1 <;> apply Fin.ext <;> simp <;> omega
        exact ⟨⟨hlow'.le.trans hih.1.1, hih.1.2.trans hupp'.le⟩,
          fun _ ↦ ⟨hlow'.trans_le hih.1.1, hih.1.2.trans_lt hupp'⟩⟩

private theorem counts_ne_of_odd (up : ℕ → Prop) [DecidablePred up]
    {ell : ℕ} (hodd : Odd ell) : upCount up ell ≠ downCount up ell := by
  intro h
  obtain ⟨k, hk⟩ := hodd
  have hu := upCount_le up ell
  have hud : upCount up ell + downCount up ell = ell := by
    simp [downCount]
    omega
  omega

/-- The Specker relation has no odd closed walk of length at most `2s+1`
when the tuple width satisfies the displayed generous bound. -/
theorem no_short_odd_closed_walk
    {n : ℕ} {α : Type*} [LinearOrder α]
    (s ell : ℕ) (hs : 1 ≤ s) (hell : ell ≤ 2 * s + 1)
    (hn : 3 * ell * (s + 1) + s + 1 < n)
    (hodd : Odd ell) (v : ℕ → IncSeq n α)
    (hedge : ∀ j < ell, Adj s (v j) (v (j + 1)))
    (hclosed : v ell = v 0) : False := by
  classical
  let up : ℕ → Prop := fun j ↦ Up s (v j) (v (j + 1))
  have hedge' : ∀ j < ell, if up j then Up s (v j) (v (j + 1))
      else Up s (v (j + 1)) (v j) := by
    intro j hj
    by_cases h : up j
    · simpa [h]
    · simpa [h, up] using (hedge j hj).resolve_left h
  have hb := path_bounds s ell hn v up hedge' ell le_rfl
  have hellpos : 0 < ell := by
    obtain ⟨k, rfl⟩ := hodd
    omega
  have hstrict := hb.2 hellpos
  let u := upCount up ell
  let d := downCount up ell
  have hu : u ≤ ell := upCount_le up ell
  have hud : u + d = ell := by dsimp [d, downCount]; omega
  have hne : u ≠ d := counts_ne_of_odd up hodd
  have hidxL : lowerIndex ell s u d < middleIndex ell s := by
    rw [hclosed] at hstrict
    exact (v 0).strictMono.lt_iff_lt.mp hstrict.1
  have hidxR : middleIndex ell s < upperIndex ell s u d := by
    rw [hclosed] at hstrict
    exact (v 0).strictMono.lt_iff_lt.mp hstrict.2
  rcases lt_or_gt_of_ne hne with hudlt | hdult
  · have hu_le_s : u ≤ s := by omega
    have hsub : ell - u = d := by omega
    dsimp [lowerIndex, middleIndex] at hidxL
    rw [hsub] at hidxL
    have : (u + 1) * s ≤ d * s := Nat.mul_le_mul_right s hudlt
    nlinarith
  · have hd_le_s : d ≤ s := by omega
    have hsub : ell - u = d := by omega
    dsimp [middleIndex, upperIndex] at hidxR
    rw [hsub] at hidxR
    have : (d + 1) * s ≤ u * s := Nat.mul_le_mul_right s hdult
    nlinarith

/-- A width sufficient for odd girth greater than `2s+1`. -/
def width (s : ℕ) : ℕ :=
  3 * (2 * s + 1) * (s + 1) + s + 2

theorem width_bound (s ell : ℕ) (hell : ell ≤ 2 * s + 1) :
    3 * ell * (s + 1) + s + 1 < width s := by
  dsimp [width]
  nlinarith

end Specker
end Erdos110
