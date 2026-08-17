import ErdosProblems.Erdos387.AnalyticInputs
import ErdosProblems.Erdos387.LocalDensity

open Finset

namespace Erdos473

open Erdos387

private lemma card_filter_Ioc_le_card_filter_Ioc_add (P : ℕ → Prop)
    [DecidablePred P] (X H U : ℕ) :
    ((Finset.Ioc X U).filter P).card ≤
      ((Finset.Ioc (X + H) U).filter P).card + H := by
  have hsub : (Finset.Ioc X U).filter P ⊆
      ((Finset.Ioc (X + H) U).filter P) ∪ Finset.Ioc X (X + H) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    have hnI := Finset.mem_Ioc.mp hn.1
    by_cases h : n ≤ X + H
    · exact Finset.mem_union_right _ (Finset.mem_Ioc.2 ⟨hnI.1, h⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.2
        ⟨Finset.mem_Ioc.2 ⟨by omega, hnI.2⟩, hn.2⟩)
  calc
    ((Finset.Ioc X U).filter P).card
        ≤ (((Finset.Ioc (X + H) U).filter P) ∪
            Finset.Ioc X (X + H)).card := Finset.card_le_card hsub
    _ ≤ ((Finset.Ioc (X + H) U).filter P).card +
        (Finset.Ioc X (X + H)).card := Finset.card_union_le _ _
    _ = ((Finset.Ioc (X + H) U).filter P).card + H := by simp

private lemma exists_parameter (X₀ H : ℕ) :
    ∃ X : ℕ, X₀ ≤ X ∧ H + 2 < X ∧
      let L := Nat.log 2 X + 1
      16 ≤ L ∧ 8 * L ^ 4 * (2 * H + 3) ≤ X := by
  let m := max X₀ H + 100
  let k := 10 * m
  let X := 2 ^ k
  refine ⟨X, ?_, ?_, ?_⟩
  · have hmX₀ : X₀ ≤ m := by
      dsimp [m]
      omega
    have hmpos : 0 < m := by simp [m]
    have hmle : m ≤ 2 ^ m := by
      exact (Nat.le_mul_of_pos_left m Nat.zero_lt_two).trans
        (Nat.mul_le_pow (by decide : 2 ≠ 1) m)
    have hmk : m ≤ k := by dsimp [k]; omega
    exact hmX₀.trans (hmle.trans (pow_le_pow_right' (by decide : 1 ≤ 2) hmk))
  · have hmH : H + 100 ≤ m := by
      dsimp [m]
      omega
    have hmle : m ≤ 2 ^ m := by
      exact (Nat.le_mul_of_pos_left m Nat.zero_lt_two).trans
        (Nat.mul_le_pow (by decide : 2 ≠ 1) m)
    have hmk : m ≤ k := by dsimp [k]; omega
    have := hmH.trans (hmle.trans
      (pow_le_pow_right' (by decide : 1 ≤ 2) hmk))
    omega
  · have hlog : Nat.log 2 X = k := by
      simp [X, Nat.log_pow (by decide : 1 < 2)]
    rw [hlog]
    dsimp only
    constructor
    · dsimp [k, m]
      omega
    · have hm : 100 ≤ m := by simp [m]
      have hHm : 2 * H + 3 ≤ 3 * m := by
        have : H ≤ m := by dsimp [m]; omega
        omega
      have hLm : k + 1 ≤ 11 * m := by dsimp [k]; omega
      have hpow : 2 * m ^ 2 ≤ 2 ^ (2 * m) :=
        (Nat.le_add_right (2 * m ^ 2) 1).trans
          (Nat.two_mul_sq_add_one_le_two_pow_two_mul m)
      have hpow5 : (2 * m ^ 2) ^ 5 ≤ (2 ^ (2 * m)) ^ 5 :=
        Nat.pow_le_pow_left hpow 5
      have hcoeff : 351384 ≤ 32 * m ^ 5 := by
        calc
          351384 ≤ 32 * 100 ^ 5 := by norm_num
          _ ≤ 32 * m ^ 5 := Nat.mul_le_mul_left 32
            (Nat.pow_le_pow_left hm 5)
      have hrough : 8 * (k + 1) ^ 4 * (2 * H + 3) ≤
          (2 ^ (2 * m)) ^ 5 := by
        calc
          8 * (k + 1) ^ 4 * (2 * H + 3)
              ≤ 8 * (11 * m) ^ 4 * (3 * m) :=
                Nat.mul_le_mul
                  (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hLm 4)) hHm
          _ = 351384 * m ^ 5 := by ring
          _ ≤ (32 * m ^ 5) * m ^ 5 := Nat.mul_le_mul_right (m ^ 5) hcoeff
          _ = (2 * m ^ 2) ^ 5 := by ring
          _ ≤ (2 ^ (2 * m)) ^ 5 := hpow5
      calc
        8 * (k + 1) ^ 4 * (2 * H + 3)
            ≤ (2 ^ (2 * m)) ^ 5 := hrough
        _ = X := by
          simp only [X, k]
          rw [show 10 * m = (2 * m) * 5 by omega]
          exact (pow_mul 2 (2 * m) 5).symm

theorem exists_prime_cluster (hSW : ShiftedSiegelWalfiszLower) (H : ℕ) :
    ∃ (S : Finset ℕ) (q₀ qstar : ℕ),
      S.Nonempty ∧
      (∀ q ∈ S, q.Prime) ∧
      q₀ ∈ S ∧ qstar ∈ S ∧
      (∀ q ∈ S, q₀ ≤ q) ∧ (∀ q ∈ S, q ≤ qstar) ∧
      H < qstar - q₀ ∧ qstar - q₀ + 2 * H < q₀ ∧
      S.gcd (fun q => q - q₀) = 2 := by
  classical
  obtain ⟨X₀, hX₀⟩ := hSW 3
  obtain ⟨X, hX₀X, hHX, hL16, hlarge⟩ := exists_parameter X₀ H
  let L := Nat.log 2 X + 1
  have hLpos : 0 < L := by simp [L]
  have hL16' : 16 ≤ L := hL16
  have hlargeDiv : 2 * H + 3 ≤ X / (8 * L ^ 4) := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 8 * L ^ 4)).2
    simpa [mul_comm] using hlarge
  have residue_card (Q a : ℕ) (hQ : 2 ≤ Q) (hQL : Q ≤ L ^ 3)
      (hcop : a.Coprime Q) :
      H + 3 ≤
        ((Finset.Ioc (X + H) (2 * X)).filter
          (fun p => p.Prime ∧ p % Q = a % Q)).card := by
    let A := (Finset.Ioc X (2 * X)).filter
      (fun p => p.Prime ∧ p % Q = a % Q)
    let B := (Finset.Ioc (X + H) (2 * X)).filter
      (fun p => p.Prime ∧ p % Q = a % Q)
    have hden : 8 * Q * L ≤ 8 * L ^ 4 := by
      calc
        8 * Q * L ≤ 8 * L ^ 3 * L :=
          Nat.mul_le_mul_right L (Nat.mul_le_mul_left 8 hQL)
        _ = 8 * L ^ 4 := by ring
    have hdenpos : 0 < 8 * Q * L := by positivity
    have hdiv : X / (8 * L ^ 4) ≤ X / (8 * Q * L) :=
      Nat.div_le_div_left hden hdenpos
    have hA : A.card ≥ X / (8 * Q * L) := by
      simpa only [A, L, Nat.sub_zero] using
        hX₀ X Q a 0 hX₀X hQ hQL (Nat.zero_le _) hcop
    have hAB : A.card ≤ B.card + H := by
      simpa only [A, B] using
        card_filter_Ioc_le_card_filter_Ioc_add
          (fun p => p.Prime ∧ p % Q = a % Q) X H (2 * X)
    have hbigA : 2 * H + 3 ≤ A.card := hlargeDiv.trans (hdiv.trans hA)
    change H + 3 ≤ B.card
    omega
  let S := (Finset.Ioc (X + H) (2 * X)).filter Nat.Prime
  have htwoL : 2 ≤ L ^ 3 := by
    calc
      2 ≤ 16 ^ 3 := by norm_num
      _ ≤ L ^ 3 := Nat.pow_le_pow_left hL16' 3
  have hS2card := residue_card 2 1 (by norm_num) htwoL (by norm_num)
  have hS2sub :
      (Finset.Ioc (X + H) (2 * X)).filter
          (fun p => p.Prime ∧ p % 2 = 1 % 2) ⊆ S := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  have hScard : H + 3 ≤ S.card :=
    hS2card.trans (Finset.card_le_card hS2sub)
  let t := X / (64 * L)
  have hHt : H ≤ t := by
    have hden : 64 * L ≤ 8 * L ^ 4 := by
      calc
        64 * L ≤ 8 * (L ^ 3) * L := by
          apply Nat.mul_le_mul_right L
          have : 8 ≤ L ^ 3 := by
            calc 8 ≤ 16 ^ 3 := by norm_num
                 _ ≤ L ^ 3 := Nat.pow_le_pow_left hL16' 3
          omega
        _ = 8 * L ^ 4 := by ring
    have := hlargeDiv.trans
      (Nat.div_le_div_left hden (by positivity : 0 < 64 * L))
    omega
  have hfour_t : 4 * t ≤ X / (16 * L) := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 16 * L)).2
    calc
      4 * t * (16 * L) = (64 * L) * (X / (64 * L)) := by
        simp only [t]
        ring
      _ ≤ X := Nat.mul_div_le X (64 * L)
  have hA2 := hX₀ X 2 1 0 hX₀X (by norm_num) htwoL
    (Nat.zero_le _) (by norm_num)
  have hA2B2 := card_filter_Ioc_le_card_filter_Ioc_add
    (fun p => p.Prime ∧ p % 2 = 1 % 2) X H (2 * X)
  have htS2 : t ≤
      ((Finset.Ioc (X + H) (2 * X)).filter
        (fun p => p.Prime ∧ p % 2 = 1 % 2)).card := by
    have htA : t + H ≤
        ((Finset.Ioc X (2 * X)).filter
          (fun p => p.Prime ∧ p % 2 = 1 % 2)).card := by
      have : t + H ≤ 4 * t := by omega
      exact this.trans (hfour_t.trans (by simpa [L] using hA2))
    omega
  have htS : t ≤ S.card := htS2.trans (Finset.card_le_card hS2sub)
  have hSnon : S.Nonempty := Finset.card_pos.mp (by omega)
  let q₀ := S.min' hSnon
  let qstar := S.max' hSnon
  have hq₀mem : q₀ ∈ S := Finset.min'_mem S hSnon
  have hqstarmem : qstar ∈ S := Finset.max'_mem S hSnon
  have hq₀min : ∀ q ∈ S, q₀ ≤ q := fun q hq => Finset.min'_le S q hq
  have hqstarmax : ∀ q ∈ S, q ≤ qstar := fun q hq => Finset.le_max' S q hq
  have hprime : ∀ q ∈ S, q.Prime := by
    intro q hq
    exact (Finset.mem_filter.mp hq).2
  have hbounds : ∀ q ∈ S, X + H < q ∧ q ≤ 2 * X := by
    intro q hq
    exact Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1
  have hdiam : H < qstar - q₀ := by
    by_contra h
    have hsub : S ⊆ Finset.Icc q₀ (q₀ + H) := by
      intro q hq
      exact Finset.mem_Icc.2 ⟨hq₀min q hq, by
        have := hqstarmax q hq
        have hminmax := hq₀min qstar hqstarmem
        omega⟩
    have hc := Finset.card_le_card hsub
    simp at hc
    omega
  have hleft : qstar - q₀ + 2 * H < q₀ := by
    have hq₀b := (hbounds q₀ hq₀mem).1
    have hqstarb := (hbounds qstar hqstarmem).2
    have hminmax := hq₀min qstar hqstarmem
    omega
  let g := S.gcd (fun q => q - q₀)
  have hodd : ∀ q ∈ S, Odd q := by
    intro q hq
    exact (hprime q hq).odd_of_ne_two (by
      have := (hbounds q hq).1
      omega)
  have htwo_g : 2 ∣ g := by
    apply Finset.dvd_gcd
    intro q hq
    exact (Nat.Odd.sub_odd (hodd q hq) (hodd q₀ hq₀mem)).two_dvd
  refine ⟨S, q₀, qstar, hSnon, hprime, hq₀mem, hqstarmem,
    hq₀min, hqstarmax, hdiam, hleft, ?_⟩
  apply Nat.dvd_antisymm ?_ htwo_g
  -- It remains to exclude four and every odd prime divisor of `g`.
  by_contra hg2
  have hgapPos : 0 < qstar - q₀ := by omega
  have hgGap : g ∣ qstar - q₀ := Finset.gcd_dvd hqstarmem
  have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgGap hgapPos
  have hglt : 2 < g := by
    have hgle : 2 ≤ g := Nat.le_of_dvd hgpos htwo_g
    have hgne : g ≠ 2 := fun h => hg2 (by simp [h])
    exact lt_of_le_of_ne hgle hgne.symm
  rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hglt with
      hfour | ⟨r, hrprime, hrg, hrodd⟩
  · let a₄ := if q₀ % 4 = 1 then 3 else 1
    have ha₄cop : a₄.Coprime 4 := by
      dsimp [a₄]
      split <;> norm_num
    have hfourL : 4 ≤ L ^ 3 := by
      calc 4 ≤ 16 ^ 3 := by norm_num
           _ ≤ L ^ 3 := Nat.pow_le_pow_left hL16' 3
    have hcard₄ := residue_card 4 a₄ (by norm_num) hfourL ha₄cop
    obtain ⟨q, hq⟩ := Finset.card_pos.mp (show 0 <
        ((Finset.Ioc (X + H) (2 * X)).filter
          (fun p => p.Prime ∧ p % 4 = a₄ % 4)).card by omega)
    have hqdata := Finset.mem_filter.mp hq
    have hqS : q ∈ S := Finset.mem_filter.2 ⟨hqdata.1, hqdata.2.1⟩
    have hq₀mod := Nat.odd_mod_four_iff.mp
      (Nat.odd_iff.mp (hodd q₀ hq₀mem))
    have hmodne : q % 4 ≠ q₀ % 4 := by
      dsimp [a₄] at hqdata
      split at hqdata <;> omega
    have hdiv : 4 ∣ q - q₀ := hfour.trans (Finset.gcd_dvd hqS)
    have hmodeq : q₀ ≡ q [MOD 4] :=
      (Nat.modEq_iff_dvd' (hq₀min q hqS)).2 hdiv
    change q₀ % 4 = q % 4 at hmodeq
    exact hmodne hmodeq.symm
  · have hrpos : 0 < r := hrprime.pos
    let M := modularPreimageIoc (X + H) (2 * X) r {q₀ % r}
    have hSM : S ⊆ M := by
      intro q hq
      have hgap : r ∣ q - q₀ := hrg.trans (Finset.gcd_dvd hq)
      have hmodeq : q₀ ≡ q [MOD r] :=
        (Nat.modEq_iff_dvd' (hq₀min q hq)).2 hgap
      change q ∈ modularPreimageIoc (X + H) (2 * X) r {q₀ % r}
      rw [modularPreimageIoc, Finset.mem_filter, Finset.mem_singleton]
      change q₀ % r = q % r at hmodeq
      exact ⟨(Finset.mem_filter.mp hq).1,
        hmodeq.symm⟩
    have hMraw := abs_card_modularPreimageIoc_sub_density
      (L := X + H) (U := 2 * X) (g := r)
      (by omega : X + H ≤ 2 * X) hrpos ({q₀ % r} : Finset ℕ)
      (by intro b hb; simp only [Finset.mem_singleton] at hb; subst b;
          exact Nat.mod_lt _ hrpos)
    have hMreal : (M.card : ℝ) ≤
        (((2 * X - (X + H) : ℕ) : ℝ) / r) + 2 := by
      have hu := (abs_le.mp hMraw).2
      dsimp [M]
      norm_num at hu ⊢
      linarith
    have hMnat : M.card ≤ (2 * X - (X + H)) / r + 2 := by
      let n₂ : ℕ := 2
      have hMreal' : (M.card : ℝ) ≤
          (((2 * X - (X + H) : ℕ) : ℝ) / r) + (n₂ : ℝ) := by
        simpa [n₂] using hMreal
      have hf := Nat.le_floor hMreal'
      rw [Nat.floor_add_natCast (by positivity) n₂,
        Nat.floor_div_eq_div] at hf
      simpa [n₂] using hf
    have hlen : 2 * X - (X + H) ≤ X := by omega
    have hMnat' : M.card ≤ X / r + 2 :=
      hMnat.trans (Nat.add_le_add_right (Nat.div_le_div_right hlen) 2)
    have hcardSM : S.card ≤ M.card := Finset.card_le_card hSM
    have hrsmall : r ≤ 256 * L := by
      by_contra hr
      have hrbig : 256 * L < r := by omega
      let u := X / (256 * L)
      have hu3 : 3 ≤ u := by
        have hden : 256 * L ≤ 8 * L ^ 4 := by
          calc
            256 * L = 8 * 32 * L := by ring
            _ ≤ 8 * L ^ 3 * L := by
              apply Nat.mul_le_mul_right L
              apply Nat.mul_le_mul_left 8
              calc 32 ≤ 16 ^ 3 := by norm_num
                   _ ≤ L ^ 3 := Nat.pow_le_pow_left hL16' 3
            _ = 8 * L ^ 4 := by ring
        have hh := hlargeDiv.trans
          (Nat.div_le_div_left hden (by positivity : 0 < 256 * L))
        omega
      have hfouru : 4 * u ≤ t := by
        apply (Nat.le_div_iff_mul_le (by positivity : 0 < 64 * L)).2
        calc
          4 * u * (64 * L) = (256 * L) * (X / (256 * L)) := by
            simp only [u]
            ring
          _ ≤ X := Nat.mul_div_le X (256 * L)
      have hdivr : X / r ≤ u := by
        exact Nat.div_le_div_left (by omega : 256 * L ≤ r)
          (by positivity : 0 < 256 * L)
      have : t ≤ u + 2 :=
        htS.trans (hcardSM.trans (hMnat'.trans (Nat.add_le_add_right hdivr 2)))
      omega
    have hrL : r ≤ L ^ 3 := by
      calc
        r ≤ 256 * L := hrsmall
        _ = 16 ^ 2 * L := by norm_num
        _ ≤ L ^ 2 * L := Nat.mul_le_mul_right L
          (Nat.pow_le_pow_left hL16' 2)
        _ = L ^ 3 := by ring
    have hrgt2 : 2 < r := lt_of_le_of_ne hrprime.two_le (by
      intro h
      subst r
      exact (by norm_num : ¬Odd 2) hrodd)
    let a := if q₀ % r = 1 then 2 else 1
    have hacop : a.Coprime r := by
      dsimp [a]
      split
      · exact hrodd.coprime_two_left
      · simp
    have hcardr := residue_card r a hrprime.two_le hrL hacop
    obtain ⟨q, hq⟩ := Finset.card_pos.mp (show 0 <
        ((Finset.Ioc (X + H) (2 * X)).filter
          (fun p => p.Prime ∧ p % r = a % r)).card by omega)
    have hqdata := Finset.mem_filter.mp hq
    have hqS : q ∈ S := Finset.mem_filter.2 ⟨hqdata.1, hqdata.2.1⟩
    have hqmod : q % r = a % r := hqdata.2.2
    have hmodne : q % r ≠ q₀ % r := by
      dsimp [a] at hqmod
      split at hqmod
      · have h2mod : 2 % r = 2 := Nat.mod_eq_of_lt hrgt2
        rw [h2mod] at hqmod
        omega
      · have h1mod : 1 % r = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1mod] at hqmod
        omega
    have hdiv : r ∣ q - q₀ := hrg.trans (Finset.gcd_dvd hqS)
    have hmodeq : q₀ ≡ q [MOD r] :=
      (Nat.modEq_iff_dvd' (hq₀min q hqS)).2 hdiv
    change q₀ % r = q % r at hmodeq
    exact hmodne hmodeq.symm

structure PrimeCluster (H : ℕ) where
  q0 : ℕ
  D : ℕ
  gaps : Finset ℕ
  D_large : H < D
  left_large : D + 2 * H < q0
  zero_mem : 0 ∈ gaps
  D_mem : D ∈ gaps
  gap_le : ∀ d : ℕ, d ∈ gaps → d ≤ D
  prime : ∀ d : ℕ, d ∈ gaps → Nat.Prime (q0 + d)
  gcd_eq_two : gaps.gcd (fun d => (d : ℤ)) = 2

private lemma finset_gcd_natCast (T : Finset ℕ) (f : ℕ → ℕ) :
    T.gcd (fun x => (f x : ℤ)) = ((T.gcd (α := ℕ) f : ℕ) : ℤ) := by
  induction T using Finset.induction with
  | empty => simp
  | @insert a T ha ih =>
      simp only [Finset.gcd_insert, ih]
      change (Int.gcd (f a) (T.gcd (α := ℕ) f) : ℤ) =
        ((Nat.gcd (f a) (T.gcd (α := ℕ) f) : ℕ) : ℤ)
      rw [Int.gcd_natCast_natCast]

theorem primeCluster_nonempty (hSW : ShiftedSiegelWalfiszLower) (H : ℕ) :
    Nonempty (PrimeCluster H) := by
  classical
  obtain ⟨S, q₀, qstar, hSnon, hprime, hq₀mem, hqstarmem,
    hq₀min, hqstarmax, hdiam, hleft, hgcd⟩ :=
    exists_prime_cluster hSW H
  let D := qstar - q₀
  let gaps := S.image (fun q => q - q₀)
  refine ⟨{
    q0 := q₀
    D := D
    gaps := gaps
    D_large := hdiam
    left_large := hleft
    zero_mem := ?_
    D_mem := ?_
    gap_le := ?_
    prime := ?_
    gcd_eq_two := ?_ }⟩
  · exact Finset.mem_image.2 ⟨q₀, hq₀mem, by simp⟩
  · exact Finset.mem_image.2 ⟨qstar, hqstarmem, rfl⟩
  · intro d hd
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hd
    dsimp only [D]
    have := hq₀min q hq
    have := hqstarmax q hq
    omega
  · intro d hd
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hd
    have hmin := hq₀min q hq
    rw [Nat.add_sub_of_le hmin]
    exact hprime q hq
  · dsimp [gaps]
    rw [Finset.gcd_image]
    change S.gcd (fun q => ((q - q₀ : ℕ) : ℤ)) = 2
    rw [finset_gcd_natCast, hgcd]
    norm_num

end Erdos473
