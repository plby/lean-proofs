import ErdosProblems.Erdos245.Gap

open Filter Set
open scoped Pointwise Topology BigOperators

namespace Erdos245Scratch

open Erdos899
open Erdos587

lemma window_add_eq_at_doubling_gap
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Ici 1) (i : ℕ)
    (hgap : 2 * enumerate S i < enumerate S (i + 1)) :
    window S (enumerate S i) + window S (enumerate S i) =
      window (S + S) (2 * enumerate S i) := by
  classical
  apply Finset.Subset.antisymm
  · exact window_add_subset S (enumerate S i)
  · intro z hz
    have hz' := mem_window.mp hz
    have hzle := hz'.2.1
    obtain ⟨x, hxS, y, hyS, rfl⟩ := hz'.2.2
    have hxle : x ≤ enumerate S i := by
      by_contra hx
      have hxgt : enumerate S i < x := Nat.lt_of_not_ge hx
      rw [← range_enumerate hS] at hxS
      obtain ⟨j, rfl⟩ := hxS
      have hij : i < j := (enumerate_strictMono hS).lt_iff_lt.mp hxgt
      have hnext : enumerate S (i + 1) ≤ enumerate S j :=
        (enumerate_strictMono hS).monotone (by omega)
      have htooLarge : 2 * enumerate S i < enumerate S j + y :=
        hgap.trans_le (hnext.trans (Nat.le_add_right _ _))
      exact (Nat.not_lt_of_ge hzle) htooLarge
    have hyle : y ≤ enumerate S i := by
      by_contra hy
      have hygt : enumerate S i < y := Nat.lt_of_not_ge hy
      rw [← range_enumerate hS] at hyS
      obtain ⟨j, rfl⟩ := hyS
      have hij : i < j := (enumerate_strictMono hS).lt_iff_lt.mp hygt
      have hnext : enumerate S (i + 1) ≤ enumerate S j :=
        (enumerate_strictMono hS).monotone (by omega)
      have htooLarge : 2 * enumerate S i < x + enumerate S j :=
        hgap.trans_le (hnext.trans (Nat.le_add_left _ _))
      exact (Nat.not_lt_of_ge hzle) htooLarge
    exact Finset.mem_add.mpr ⟨x,
      mem_window.mpr ⟨hpos hxS, hxle, hxS⟩, y,
      mem_window.mpr ⟨hpos hyS, hyle, hyS⟩, rfl⟩

/-- A rationally separated eventual ratio below three is incompatible with
zero density.  The integer `m` records the reciprocal separation from three. -/
lemma not_eventually_scaled_sum_lt_three
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Ici 1)
    (hden : Tendsto (fun N ↦ (countIn S N : ℝ) / N) atTop (nhds 0))
    (m : ℕ) (hm : 0 < m)
    (hscaled : ∀ᶠ N in atTop,
      m * countIn (S + S) N < (3 * m - 1) * countIn S N) : False := by
  have hsum : ∀ᶠ N in atTop,
      countIn (S + S) N < 3 * countIn S N := by
    filter_upwards [hscaled] with N hN
    apply (Nat.mul_lt_mul_left hm).mp
    calc
      m * countIn (S + S) N <
          (3 * m - 1) * countIn S N := hN
      _ ≤ (3 * m) * countIn S N :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = m * (3 * countIn S N) := by ring
  let e := enumerate S
  let D := e 0 + 2 * e 1
  have hdenseD : ∀ᶠ N in atTop,
      (D + 1) * countIn S N < N :=
    density_eventually_mul_lt (countIn S) hden (by omega)
  obtain ⟨Lden, hLden⟩ := eventually_atTop.1 hdenseD
  obtain ⟨Lscaled, hLscaled⟩ := eventually_atTop.1 hscaled
  let s := max (max Lden Lscaled) (4 * m)
  obtain ⟨i, his, hgap⟩ :=
    exists_doubling_gap_of_eventually_three hS hpos hden hsum s
  let k := i + 1
  let X := window S (e i)
  have hie : i ≤ e i := (enumerate_strictMono hS).id_le i
  have hLdeni : Lden ≤ e i := by
    dsimp [s] at his
    omega
  have hLscaledi : Lscaled ≤ 2 * e i := by
    dsimp [s] at his
    omega
  have hk4m : 4 * m ≤ k := by
    dsimp [s, k] at his ⊢
    omega
  have hkpos : 0 < k := by simp [k]
  have hXcard : X.card = k := by
    change countIn S (enumerate S i) = i + 1
    exact countIn_enumerate_eq hS hpos i
  have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
  have hscaledGap := hLscaled (2 * e i) hLscaledi
  have hsumcard : (X + X).card = countIn (S + S) (2 * e i) := by
    change (window S (enumerate S i) + window S (enumerate S i)).card = _
    rw [window_add_eq_at_doubling_gap hS hpos i hgap]
    rfl
  have hcount2 : countIn S (2 * e i) = k := by
    have hlower : k ≤ countIn S (2 * e i) := by
      dsimp [k, e]
      rw [← countIn_enumerate_eq hS hpos i]
      exact countIn_mono_nat S (by omega)
    have hnot : ¬(i + 1 < countIn S (2 * e i)) := by
      intro hlt
      have hnextle :=
        (enumerate_le_iff_lt_countIn hS hpos (i + 1) (2 * e i)).mpr hlt
      dsimp [e] at hgap hnextle
      omega
    dsimp [k]
    omega
  have hscaledX : m * (X + X).card < (3 * m - 1) * k := by
    rw [hsumcard]
    simpa only [hcount2] using hscaledGap
  have hupper : (3 * m - 1) * k ≤ m * (3 * k - 4) := by
    calc
      (3 * m - 1) * k = 3 * m * k - k := by
        rw [Nat.sub_mul]
        simp
      _ ≤ 3 * m * k - 4 * m := Nat.sub_le_sub_left hk4m _
      _ = m * (3 * k - 4) := by
        rw [Nat.mul_sub_left_distrib]
        congr 1 <;> ring
  have hsmalllt : (X + X).card < 3 * k - 4 := by
    apply (Nat.mul_lt_mul_left hm).mp
    exact hscaledX.trans_le hupper
  have hsmall : (X + X).card ≤ 3 * X.card - 4 := by
    rw [hXcard]
    exact hsmalllt.le
  have hk2 : 2 ≤ X.card := by
    rw [hXcard]
    have : 4 ≤ 4 * m := by omega
    omega
  obtain ⟨a, d, L, hd, hL, hXAP⟩ :=
    exists_short_natAP_of_three_k_minus_four hXne hk2 hsmall
  have hmem (j : ℕ) (hj : j ≤ i) : e j ∈ X := by
    apply mem_window.mpr
    exact ⟨hpos (enumerate_mem hS j),
      (enumerate_strictMono hS).monotone hj,
      enumerate_mem hS j⟩
  obtain ⟨j0, hj0L, hj0⟩ :=
    Erdos13Additive.mem_natAP.mp (hXAP (hmem 0 (Nat.zero_le i)))
  obtain ⟨j1, hj1L, hj1⟩ :=
    Erdos13Additive.mem_natAP.mp (hXAP (hmem 1 (by omega)))
  obtain ⟨ji, hjiL, hji⟩ :=
    Erdos13Additive.mem_natAP.mp (hXAP (hmem i le_rfl))
  have he01 : e 0 < e 1 := enumerate_strictMono hS (by omega)
  have hj01 : j0 < j1 := by
    by_contra hnot
    have hjle : j1 ≤ j0 := Nat.le_of_not_gt hnot
    have hmul := Nat.mul_le_mul_left d hjle
    have he10 : e 1 ≤ e 0 := by
      rw [← hj1, ← hj0]
      exact Nat.add_le_add_left hmul a
    exact (Nat.not_le_of_gt he01) he10
  have hdle : d ≤ e 1 := by
    have hmul := Nat.mul_le_mul_left d (show j0 + 1 ≤ j1 by omega)
    calc
      d ≤ a + d * j0 + d := by omega
      _ = a + d * (j0 + 1) := by ring
      _ ≤ a + d * j1 := Nat.add_le_add_left hmul a
      _ = e 1 := hj1
  have hale : a ≤ e 0 := by omega
  have hji2k : ji ≤ 2 * k := by
    rw [hXcard] at hL
    omega
  have hdji : d * ji ≤ e 1 * (2 * k) :=
    Nat.mul_le_mul hdle hji2k
  have hlinear : e i ≤ D * k := by
    calc
      e i = a + d * ji := hji.symm
      _ ≤ e 0 + e 1 * (2 * k) := Nat.add_le_add hale hdji
      _ ≤ (e 0 + 2 * e 1) * k := by
        have he0mul : e 0 ≤ e 0 * k := by
          simpa only [mul_one] using Nat.mul_le_mul_left (e 0) (show 1 ≤ k by omega)
        calc
          e 0 + e 1 * (2 * k) = e 0 + (2 * e 1) * k := by ring
          _ ≤ e 0 * k + (2 * e 1) * k := Nat.add_le_add_right he0mul _
          _ = (e 0 + 2 * e 1) * k := by ring
      _ = D * k := rfl
  have hdenseLast := hLden (e i) hLdeni
  change (D + 1) * countIn S (enumerate S i) < e i at hdenseLast
  rw [countIn_enumerate_eq hS hpos i] at hdenseLast
  change (D + 1) * k < e i at hdenseLast
  rw [add_mul, one_mul] at hdenseLast
  omega

end Erdos245Scratch

