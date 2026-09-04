import ErdosProblems.Erdos245.GAPTheory
import ErdosProblems.Erdos899

open Filter Set
open scoped Pointwise Topology BigOperators

namespace Erdos245Scratch

open Erdos899
open Erdos587

lemma countIn_enumerate_eq {S : Set ℕ} (hS : S.Infinite)
    (hpos : S ⊆ Ici 1) (i : ℕ) :
    countIn S (enumerate S i) = i + 1 := by
  classical
  let F : Finset ℕ :=
    (Finset.univ : Finset (Fin (i + 1))).image
      (fun j : Fin (i + 1) ↦ enumerate S j.1)
  have hFinj : Function.Injective
      (fun j : Fin (i + 1) ↦ enumerate S j.1) :=
    (enumerate_strictMono hS).injective.comp Fin.val_injective
  have hFcard : F.card = i + 1 := by
    change ((Finset.univ : Finset (Fin (i + 1))).image
      (fun j : Fin (i + 1) ↦ enumerate S j.1)).card = i + 1
    calc
      _ = (Finset.univ : Finset (Fin (i + 1))).card :=
        Finset.card_image_of_injective _ hFinj
      _ = i + 1 := by simp
  have hFeq : F = window S (enumerate S i) := by
    ext x
    change x ∈ (Finset.univ : Finset (Fin (i + 1))).image
      (fun j : Fin (i + 1) ↦ enumerate S j.1) ↔
        x ∈ window S (enumerate S i)
    constructor
    · intro hx
      obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hx
      have hji : j.1 ≤ i := by omega
      exact mem_window.mpr ⟨hpos (enumerate_mem hS j),
        (enumerate_strictMono hS).monotone hji,
        enumerate_mem hS j⟩
    · intro hx
      have hxS := (mem_window.mp hx).2.2
      rw [← range_enumerate hS] at hxS
      obtain ⟨j, rfl⟩ := hxS
      have hji : j ≤ i :=
        (enumerate_strictMono hS).le_iff_le.mp (mem_window.mp hx).2.1
      apply Finset.mem_image.mpr
      exact ⟨⟨j, by omega⟩, Finset.mem_univ _, rfl⟩
  rw [countIn, ← hFeq, hFcard]

lemma enumerate_le_iff_lt_countIn {S : Set ℕ} (hS : S.Infinite)
    (hpos : S ⊆ Ici 1) (i N : ℕ) :
    enumerate S i ≤ N ↔ i < countIn S N := by
  constructor
  · intro hiN
    have hmono := countIn_mono_nat S hiN
    rw [countIn_enumerate_eq hS hpos i] at hmono
    omega
  · intro hicount
    by_contra hnot
    have hNlt : N < enumerate S i := Nat.lt_of_not_ge hnot
    have hsub : window S N ⊂ window S (enumerate S i) := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · intro x hx
        apply mem_window.mpr
        have hx' := mem_window.mp hx
        exact ⟨hx'.1, hx'.2.1.trans hNlt.le, hx'.2.2⟩
      · intro heq
        have hemem : enumerate S i ∈ window S (enumerate S i) :=
          mem_window.mpr ⟨hpos (enumerate_mem hS i), le_rfl,
            enumerate_mem hS i⟩
        rw [← heq] at hemem
        exact (Nat.not_le_of_gt hNlt) (mem_window.mp hemem).2.1
    have hcardlt := Finset.card_lt_card hsub
    change countIn S N < countIn S (enumerate S i) at hcardlt
    rw [countIn_enumerate_eq hS hpos i] at hcardlt
    omega

lemma window_eq_image_range_enumerate {S : Set ℕ} (hS : S.Infinite)
    (hpos : S ⊆ Ici 1) (N : ℕ) :
    window S N = (Finset.range (countIn S N)).image (enumerate S) := by
  classical
  ext x
  constructor
  · intro hx
    have hxS := (mem_window.mp hx).2.2
    rw [← range_enumerate hS] at hxS
    obtain ⟨i, rfl⟩ := hxS
    apply Finset.mem_image.mpr
    exact ⟨i, Finset.mem_range.mpr
      ((enumerate_le_iff_lt_countIn hS hpos i N).mp
        (mem_window.mp hx).2.1), rfl⟩
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    apply mem_window.mpr
    exact ⟨hpos (enumerate_mem hS i),
      (enumerate_le_iff_lt_countIn hS hpos i N).mpr
        (Finset.mem_range.mp hi), enumerate_mem hS i⟩

lemma window_add_subset (S : Set ℕ) (N : ℕ) :
    window S N + window S N ⊆ window (S + S) (2 * N) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
  have hx' := mem_window.mp hx
  have hy' := mem_window.mp hy
  apply mem_window.mpr
  exact ⟨by omega, by omega, Set.add_mem_add hx'.2.2 hy'.2.2⟩

/-- Density zero forces arbitrarily large scales at which doubling the
cutoff multiplies the counting function by at most four. -/
lemma frequently_countIn_two_mul_le_four
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Ici 1)
    (hden : Tendsto (fun N ↦ (countIn S N : ℝ) / N) atTop (nhds 0)) :
    ∃ᶠ N in atTop, countIn S (2 * N) ≤ 4 * countIn S N := by
  by_contra hfreq
  have hgrow : ∀ᶠ N in atTop, 4 * countIn S N < countIn S (2 * N) := by
    filter_upwards [(Filter.not_frequently.mp hfreq)] with N hN
    omega
  have hdense : ∀ᶠ N in atTop, 2 * countIn S N < N :=
    density_eventually_mul_lt (countIn S) hden (by omega)
  have hpositive : ∀ᶠ N in atTop, 0 < countIn S N :=
    eventually_countIn_pos hS hpos
  obtain ⟨L, hL⟩ := eventually_atTop.1 (hgrow.and (hdense.and hpositive))
  let N₀ := max 1 L
  have hN₀L : L ≤ N₀ := le_max_right _ _
  have hN₀pos : 0 < N₀ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have haN₀ : 0 < countIn S N₀ := (hL N₀ hN₀L).2.2
  have hiter : ∀ t : ℕ,
      4 ^ t * countIn S N₀ ≤ countIn S (2 ^ t * N₀) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        have hscale : L ≤ 2 ^ t * N₀ := by
          have hp : 1 ≤ 2 ^ t := by
            have : 0 < 2 ^ t := pow_pos (by omega) _
            omega
          calc
            L ≤ N₀ := hN₀L
            _ = 1 * N₀ := by simp
            _ ≤ 2 ^ t * N₀ := Nat.mul_le_mul_right N₀ hp
        have hstep := (hL (2 ^ t * N₀) hscale).1
        calc
          4 ^ (t + 1) * countIn S N₀ =
              4 * (4 ^ t * countIn S N₀) := by ring
          _ ≤ 4 * countIn S (2 ^ t * N₀) :=
            Nat.mul_le_mul_left 4 ih
          _ ≤ countIn S (2 * (2 ^ t * N₀)) := hstep.le
          _ = countIn S (2 ^ (t + 1) * N₀) := by ring_nf
  have hscale : L ≤ 2 ^ N₀ * N₀ := by
    have hp : 1 ≤ 2 ^ N₀ := by
      have : 0 < 2 ^ N₀ := pow_pos (by omega) _
      omega
    calc
      L ≤ N₀ := hN₀L
      _ = 1 * N₀ := by simp
      _ ≤ 2 ^ N₀ * N₀ := Nat.mul_le_mul_right N₀ hp
  have hsmall := (hL (2 ^ N₀ * N₀) hscale).2.1
  have hlower := hiter N₀
  have hpow : 2 ^ N₀ * N₀ < 4 ^ N₀ := by
    calc
      2 ^ N₀ * N₀ < 2 ^ N₀ * 2 ^ N₀ :=
        (Nat.mul_lt_mul_left (pow_pos (by omega) _)).2 N₀.lt_two_pow_self
      _ = 4 ^ N₀ := by rw [← Nat.mul_pow]
  have hfour : 4 ^ N₀ ≤ countIn S (2 ^ N₀ * N₀) := by
    calc
      4 ^ N₀ = 4 ^ N₀ * 1 := by simp
      _ ≤ 4 ^ N₀ * countIn S N₀ :=
        Nat.mul_le_mul_left _ haN₀
      _ ≤ countIn S (2 ^ N₀ * N₀) := hlower
  have hcontra : 2 * 4 ^ N₀ < 2 ^ N₀ * N₀ := by
    exact (Nat.mul_le_mul_left 2 hfour).trans_lt hsmall
  omega

end Erdos245Scratch
