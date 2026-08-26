/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Copyright 2026 Johan Land.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 1112.
Informal proof: Johan Land, using Claude Fable 5 and Claude Opus 4.8.
Formal proof: Johan Land, using Claude Fable 5 and Claude Opus 4.8.
GPT-5.5 and Gemini 3.1 supplied advice and adversarial review.
Source: https://www.erdosproblems.com/1112#post-7375
https://github.com/beetree/math_erdos_1112/tree/63ed94d3e802782aeb521095c17d6109a2dc57b5
Original Lean version: 4.27.0.
Original Mathlib commit: a3a10db0e9d66acbebf76c5e6a135066525ac900.
-/
/-
The slot lemma's `sharp`-independent sub-lemmas.

Split out of `SlotLemma.lean` so these five parts build without importing
`Sharp.Main` (only the final assembly `tailCovering_of_three_letters` needs
`sharp`). Paper: the non-existence section.
-/
import ErdosProblems.Erdos1112.NonEx.GapWord
import ErdosProblems.Erdos1112.NonEx.Kit
import ErdosProblems.Erdos1112.SubsetSums

namespace Erdos1112
namespace Proof

/-- A submultiset of a mapped multiset is the map of a submultiset. -/
private lemma le_map_exists {α β : Type*} {f : α → β} {t : Multiset β}
    {s : Multiset α} (h : t ≤ Multiset.map f s) :
    ∃ u, u ≤ s ∧ Multiset.map f u = t := by
  classical
  induction s using Multiset.induction generalizing t with
  | empty =>
      rw [Multiset.map_zero, Multiset.le_zero] at h
      exact ⟨0, le_rfl, by simp [h]⟩
  | cons a s ih =>
      rw [Multiset.map_cons] at h
      by_cases hmem : f a ∈ t
      · obtain ⟨t', rfl⟩ := Multiset.exists_cons_of_mem hmem
        have h' : t' ≤ Multiset.map f s := (Multiset.cons_le_cons_iff (f a)).mp h
        obtain ⟨u, hu, hmap⟩ := ih h'
        exact ⟨a ::ₘ u, Multiset.cons_le_cons a hu, by rw [Multiset.map_cons, hmap]⟩
      · have h' : t ≤ Multiset.map f s := by
          rw [Multiset.le_iff_count] at h ⊢
          intro b
          have hb := h b
          rw [Multiset.count_cons] at hb
          by_cases hbfa : b = f a
          · subst hbfa; rw [Multiset.count_eq_zero.mpr hmem]; exact Nat.zero_le _
          · rw [if_neg hbfa] at hb; exact hb
        obtain ⟨u, hu, hmap⟩ := ih h'
        exact ⟨u, le_trans hu (Multiset.le_cons_self s a), hmap⟩

/-- **Sub-lemma 1: subset sums ↔ index subsets.** A subset sum of the
indexed multiset `{δ t : t ∈ Fin m}` is realized by a Finset of indices. -/
theorem subsetSums_index {m : ℕ} (δ : Fin m → ℕ) {v : ℕ}
    (hv : v ∈ subsetSums (Multiset.map δ Finset.univ.val)) :
    ∃ T : Finset (Fin m), (∑ t ∈ T, δ t) = v := by
  classical
  rw [mem_subsetSums] at hv
  obtain ⟨T', hle, hsum⟩ := hv
  obtain ⟨u, hu, hmap⟩ := le_map_exists hle
  have hunod : u.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro x
    have h1 := Multiset.le_iff_count.mp hu x
    have h2 := (Multiset.nodup_iff_count_le_one.mp Finset.univ.nodup) x
    omega
  refine ⟨u.toFinset, ?_⟩
  have hval : u.toFinset.val = u := by rw [Multiset.toFinset_val]; exact hunod.dedup
  change (Multiset.map δ u.toFinset.val).sum = v
  rw [hval, hmap]; exact hsum

/-- **Sub-lemma 2: slot positions.** Given target gap values each in the
tail alphabet, distinct positions past `N₀` realizing them (`gap a (p t) =
δ t`). Route: greedy selection using infinite occurrence, avoiding the finite
set of already-chosen positions. -/
theorem exists_slot_positions {a : ℕ → ℕ} {m : ℕ} (δ : Fin m → ℕ) (N₀ : ℕ)
    (hδ : ∀ t, δ t ∈ tailAlphabet a) :
    ∃ p : Fin m → ℕ, (∀ t, N₀ ≤ p t) ∧ Function.Injective p ∧
      (∀ t, gap a (p t) = δ t) := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    exact ⟨Fin.elim0, fun t => t.elim0, fun t => t.elim0, fun t => t.elim0⟩
  -- extend `δ` to `ℕ` (clamp the index); each value stays in the tail alphabet
  set δ' : ℕ → ℕ := fun t => δ ⟨min t (m - 1), by omega⟩ with hδ'def
  have hδ'tail : ∀ t : ℕ, ∀ B : ℕ, ∃ n, B ≤ n ∧ gap a n = δ' t := fun t B => hδ _ B
  -- greedy strictly-increasing positions `q t` with `gap a (q t) = δ' t`
  set q : ℕ → ℕ := fun t => Nat.rec
    ((hδ'tail 0 N₀).choose)
    (fun t qt => (hδ'tail (t + 1) (qt + 1)).choose) t with hqdef
  have hq0 : N₀ ≤ q 0 ∧ gap a (q 0) = δ' 0 := (hδ'tail 0 N₀).choose_spec
  have hqsucc : ∀ t, q t + 1 ≤ q (t + 1) ∧ gap a (q (t + 1)) = δ' (t + 1) :=
    fun t => (hδ'tail (t + 1) (q t + 1)).choose_spec
  have hqmono : StrictMono q := by
    apply strictMono_nat_of_lt_succ
    intro t; have := (hqsucc t).1; omega
  have hqN₀ : ∀ t, N₀ ≤ q t := by
    intro t
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · exact hq0.1
    · exact le_trans hq0.1 (hqmono.monotone (Nat.zero_le t))
  have hqgap : ∀ t, gap a (q t) = δ' t := by
    intro t
    cases t with
    | zero => exact hq0.2
    | succ t => exact (hqsucc t).2
  refine ⟨fun t => q t.val, fun t => hqN₀ _, ?_, fun t => ?_⟩
  · intro s t hst
    exact Fin.ext (hqmono.injective hst)
  · rw [hqgap]
    simp only [hδ'def, min_eq_left (Nat.le_sub_one_of_lt t.isLt), Fin.eta]

/-- **Sub-lemma 3: slot realization.** The `m` slots at positions `p`
(each toggled off/on = index `p t` / `p t + 1`) realize `∑ a(p t) +
(on-subset sum of the gaps)` as an `m`-fold sum. Route: the direct
`Fin m` config `t ↦ if t ∈ T then p t + 1 else p t`, with `a (p t + 1) =
a (p t) + gap a (p t)`. -/
theorem slot_realize {a : ℕ → ℕ} {m d₁ d₂ : ℕ} (hgaps : HasGapsIn d₁ d₂ a)
    (p : Fin m → ℕ) (T : Finset (Fin m)) :
    (∑ t, a (p t)) + (∑ t ∈ T, gap a (p t)) ∈ kFoldSumset m a := by
  classical
  have key : ∀ t : Fin m, a (if t ∈ T then p t + 1 else p t) =
      a (p t) + (if t ∈ T then gap a (p t) else 0) := by
    intro t
    by_cases ht : t ∈ T
    · rw [if_pos ht, if_pos ht, hgaps.succ_eq_add_gap]
    · rw [if_neg ht, if_neg ht, Nat.add_zero]
  refine ⟨fun t => if t ∈ T then p t + 1 else p t, ?_⟩
  symm
  calc ∑ t, a (if t ∈ T then p t + 1 else p t)
      = ∑ t, (a (p t) + if t ∈ T then gap a (p t) else 0) :=
        Finset.sum_congr rfl (fun t _ => key t)
    _ = (∑ t, a (p t)) + ∑ t, (if t ∈ T then gap a (p t) else 0) :=
        Finset.sum_add_distrib
    _ = (∑ t, a (p t)) + ∑ t ∈ T, gap a (p t) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **Sub-lemma 4: coarse dial.** A value family `base + a n + [c, c+M−1]`
(`n ≥ T₀`, all in `kA`) with `a` stepping by `≤ M` covers all large integers.
Route: `discrete_ivt` on `n ↦ a (T₀ + n)` into the window
`[x − base − c − (M−1), x − base − c]`, step `≤ M`, width `M−1`. -/
theorem slot_dial {a : ℕ → ℕ} {k M base c T₀ : ℕ} (hM : 0 < M)
    (hgrow : ∀ n, T₀ ≤ n → a n < a (n + 1))
    (hstep : ∀ n, T₀ ≤ n → a (n + 1) ≤ a n + M)
    (hmem : ∀ n v, T₀ ≤ n → c ≤ v → v ≤ c + (M - 1) →
      base + a n + v ∈ kFoldSumset k a) :
    ∃ X₀, ∀ x, X₀ ≤ x → x ∈ kFoldSumset k a := by
  classical
  refine ⟨base + a T₀ + c + M, fun x hx => ?_⟩
  -- lower bound: `a (T₀ + j) ≥ a T₀ + j`
  have hlb : ∀ j, a T₀ + j ≤ a (T₀ + j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have := hgrow (T₀ + j) (Nat.le_add_right _ _)
        have he : T₀ + (j + 1) = (T₀ + j) + 1 := by omega
        rw [he]; omega
  -- discrete IVT on `f j = a (T₀ + j)` into `[x−base−c−(M−1), x−base−c]`
  have h0 : (a (T₀ + 0) : ℤ) ≤ (x : ℤ) - base - c - (M - 1) := by
    have : (a (T₀ + 0) : ℤ) = (a T₀ : ℤ) := by norm_num
    rw [this]; omega
  have hN : (x : ℤ) - base - c ≤ (a (T₀ + x) : ℤ) := by
    have h1 := hlb x; omega
  have hstep' : ∀ n, n < x → (a (T₀ + (n + 1)) : ℤ) - a (T₀ + n) ≤ M := by
    intro n _
    have he : T₀ + (n + 1) = (T₀ + n) + 1 := by omega
    have := hstep (T₀ + n) (Nat.le_add_right _ _)
    rw [he]; omega
  obtain ⟨j, _, hjlo, hjhi⟩ :=
    discrete_ivt (f := fun j => (a (T₀ + j) : ℤ)) (N := x) h0 hN (by omega)
      hstep' (by omega)
  -- decode: `n := T₀ + j`, `v := x − base − a n`
  set n := T₀ + j with hndef
  have hz1 : (a n : ℤ) ≤ (x : ℤ) - base - c := by simp only [hndef]; linarith
  have hz2 : (x : ℤ) - base - c - (M - 1) ≤ (a n : ℤ) := by simp only [hndef]; linarith
  have hxv : x = base + a n + (x - base - a n) := by omega
  rw [hxv]
  exact hmem n (x - base - a n) (by simp only [hndef]; omega) (by omega) (by omega)

/-- Finset gcd commutes with dividing out a common factor. (Copy of
`Sharp/Graham.lean`'s lemma — this file is Sharp-independent by design.) -/
private lemma gcd_image_div_aux {s : Finset ℕ} {c : ℕ}
    (h : ∀ x ∈ s, c ∣ x) : (s.image (· / c)).gcd id * c = s.gcd id := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
      rw [Finset.image_insert, Finset.gcd_insert, Finset.gcd_insert]
      have hcx : c ∣ x := h x (Finset.mem_insert_self _ _)
      have ih' := ih fun y hy => h y (Finset.mem_insert_of_mem hy)
      simp only [id_eq]
      rw [← ih']
      change Nat.gcd (x / c) ((Finset.image (· / c) s).gcd id) * c =
        Nat.gcd x ((Finset.image (· / c) s).gcd id * c)
      rw [← Nat.gcd_mul_right, Nat.div_mul_cancel hcx]

open scoped Classical in
/-- **Sub-lemma 5: gcd rescaling.** If the tail alphabet has gcd `g`, the
tail is `a (T+n) = c + g·a' n` for a sequence `a'` whose tail alphabet is the
`/g` rescale (gcd 1), with the same ≥ 3-letter and `≤ d₂` structure. Route:
`a' n := (a (T+n) − a T)/g`; gaps divide by `g` (all tail gaps ≡ 0 mod g);
consumed by `tailCoveringN_of_rescaled`. -/
theorem exists_rescale {a : ℕ → ℕ} {d₁ d₂ : ℕ} (hd₁ : 1 ≤ d₁)
    (hgaps : HasGapsIn d₁ d₂ a)
    (h3 : ∃ x y z : ℕ, x ∈ tailAlphabet a ∧ y ∈ tailAlphabet a ∧
      z ∈ tailAlphabet a ∧ x < y ∧ y < z) :
    ∃ (a' : ℕ → ℕ) (T g c : ℕ), 0 < g ∧ (∀ n, a (T + n) = c + g * a' n) ∧
      (∃ x y z : ℕ, x ∈ tailAlphabet a' ∧ y ∈ tailAlphabet a' ∧
        z ∈ tailAlphabet a' ∧ x < y ∧ y < z) ∧
      ((Finset.Icc 1 d₂).filter (· ∈ tailAlphabet a')).gcd id = 1 := by
  classical
  -- tail index `T` past which every gap is a tail-alphabet letter
  obtain ⟨T, hT⟩ := exists_tail_index hgaps
  -- the tail alphabet as a Finset `G ⊆ [d₁, d₂]`, and `g := gcd G`
  set G : Finset ℕ := (Finset.Icc d₁ d₂).filter (· ∈ tailAlphabet a) with hGdef
  have hmemG : ∀ x, x ∈ tailAlphabet a → x ∈ G := by
    intro x hx
    rw [hGdef, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨mem_tailAlphabet_bounds hgaps hx, hx⟩
  set g : ℕ := G.gcd id with hgdef
  -- `g > 0` (G nonempty via `h3`, elements ≥ d₁ ≥ 1).
  have hg0 : 0 < g := by
    obtain ⟨x, _, _, hx, _, _, _, _⟩ := h3
    have hxd : d₁ ≤ x := (mem_tailAlphabet_bounds hgaps hx).1
    have hgx : g ∣ x := hgdef ▸ Finset.gcd_dvd (hmemG x hx)
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · rw [h0] at hgx; rw [Nat.zero_dvd] at hgx; omega
    · exact h0
  -- every tail gap is divisible by `g`
  have hgdvd : ∀ n, T ≤ n → g ∣ gap a n := by
    intro n hn
    exact hgdef ▸ Finset.gcd_dvd (hmemG _ (hT n hn))
  -- `a (T+n) − a T` is a `g`-multiple (telescoping sum of tail gaps).
  have hdvd_a : ∀ n, g ∣ (a (T + n) - a T) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have he : T + (n + 1) = (T + n) + 1 := by omega
        have hmono : a T ≤ a (T + n) := hgaps.monotone (by omega)
        have hstep : a (T + (n + 1)) - a T = (a (T + n) - a T) + gap a (T + n) := by
          rw [he, hgaps.succ_eq_add_gap]; omega
        rw [hstep]
        exact Nat.dvd_add ih (hgdvd (T + n) (Nat.le_add_right _ _))
  -- the rescaled sequence and offset
  set a' : ℕ → ℕ := fun n => (a (T + n) - a T) / g with ha'def
  set c : ℕ := a T with hcdef
  have haffine : ∀ n, a (T + n) = c + g * a' n := by
    intro n
    have hle : a T ≤ a (T + n) := hgaps.monotone (Nat.le_add_right _ _)
    rw [ha'def, hcdef, Nat.mul_div_cancel' (hdvd_a n)]
    omega
  -- `gap a' n = gap a (T+n) / g`
  have hgap' : ∀ n, gap a' n = gap a (T + n) / g := by
    intro n
    obtain ⟨X', hX'⟩ := hdvd_a (n + 1)
    obtain ⟨Y', hY'⟩ := hdvd_a n
    have hmono2 : a (T + n) ≤ a (T + (n + 1)) := hgaps.monotone (by omega)
    have haX : a' (n + 1) = X' := by
      change (a (T + (n + 1)) - a T) / g = X'
      rw [hX', Nat.mul_div_cancel_left _ hg0]
    have haY : a' n = Y' := by
      change (a (T + n) - a T) / g = Y'
      rw [hY', Nat.mul_div_cancel_left _ hg0]
    have hYX : Y' ≤ X' := Nat.le_of_mul_le_mul_left (by omega) hg0
    have hmono0 : a T ≤ a (T + n) := hgaps.monotone (by omega)
    have hgapval : gap a (T + n) = g * (X' - Y') := by
      change a (T + n + 1) - a (T + n) = g * (X' - Y')
      have h1 : a (T + n + 1) = a (T + (n + 1)) := by rw [Nat.add_assoc]
      rw [Nat.mul_sub, ← hX', ← hY', h1]; omega
    change a' (n + 1) - a' n = gap a (T + n) / g
    rw [haX, haY, hgapval, Nat.mul_div_cancel_left _ hg0]
  -- a-tail letters push forward to a'-tail letters under `/g`
  have htail' : ∀ w, w ∈ tailAlphabet a → w / g ∈ tailAlphabet a' := by
    intro w hw N
    obtain ⟨n, hn, hgn⟩ := hw (N + T)
    refine ⟨n - T, by omega, ?_⟩
    have he : T + (n - T) = n := by omega
    rw [hgap' (n - T), he, hgn]
  -- and pull back: an a'-tail letter `v` has `g·v` an a-tail letter
  have htail_rev : ∀ v, v ∈ tailAlphabet a' → g * v ∈ tailAlphabet a := by
    intro v hv N
    obtain ⟨n, hn, hgn⟩ := hv N
    refine ⟨T + n, by omega, ?_⟩
    have hd := hgdvd (T + n) (Nat.le_add_right _ _)
    have hvv : v = gap a (T + n) / g := by rw [← hgap' n, hgn]
    rw [hvv, Nat.mul_div_cancel' hd]
  refine ⟨a', T, g, c, hg0, haffine, ?_, ?_⟩
  · -- ≥ 3 tail letters of `a'`: the `/g` images of `h3`'s letters
    obtain ⟨x, y, z, hx, hy, hz, hxy, hyz⟩ := h3
    have hgy : g ∣ y := hgdef ▸ Finset.gcd_dvd (hmemG y hy)
    have hgz : g ∣ z := hgdef ▸ Finset.gcd_dvd (hmemG z hz)
    exact ⟨x / g, y / g, z / g, htail' x hx, htail' y hy, htail' z hz,
      Nat.div_lt_div_of_lt_of_dvd hgy hxy, Nat.div_lt_div_of_lt_of_dvd hgz hyz⟩
  · -- gcd of the rescaled alphabet `= gcd G / g = 1`
    have hG'eq : (Finset.Icc 1 d₂).filter (· ∈ tailAlphabet a') = G.image (· / g) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, hGdef]
      constructor
      · rintro ⟨-, hvtail⟩
        refine ⟨g * v, ?_, ?_⟩
        · exact ⟨mem_tailAlphabet_bounds hgaps (htail_rev v hvtail), htail_rev v hvtail⟩
        · rw [Nat.mul_div_cancel_left _ hg0]
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨⟨hw1, hw2⟩, hwtail⟩ := hw
        have hgw : g ∣ w := hgdef ▸ Finset.gcd_dvd (hmemG w hwtail)
        refine ⟨⟨?_, ?_⟩, htail' w hwtail⟩
        · exact Nat.one_le_div_iff hg0 |>.mpr (Nat.le_of_dvd (by omega) hgw)
        · exact le_trans (Nat.div_le_self _ _) hw2
    rw [hG'eq]
    have hkey := gcd_image_div_aux (s := G) (c := g) (fun w hw => hgdef ▸ Finset.gcd_dvd hw)
    rw [← hgdef] at hkey
    have h2 : (G.image (· / g)).gcd id * g = 1 * g := by rw [hkey, one_mul]
    exact Nat.eq_of_mul_eq_mul_right hg0 h2

end Proof
end Erdos1112
