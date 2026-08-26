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
Case P (Lemmas 3.12/3.13/3.14 + three explicit certificates):
`a ∣ b + M` — the η = −1 line. Sub-regimes: r = 3 (M < 2a), r = 4
(M = 2a + t), M ≥ 2a + 4, plus the three exceptional triples
(3,7,8), (4,9,11), (5,12,13). Paper: the bounded subset-sum covering section.

Unified route: a *pair-frame* construction covers every
`η = −1` triple at once. Writing `b + M = r·a` (`r ≥ 3`), the multiset
`(x, y, z) = (r−1, ⌈(M−r)/2⌉, ⌊(M−r)/2⌋)` of budget `M − 1` realizes a run
of `M` consecutive integers: a `(b, M)` pair is a residue-free mover worth
`r` grid units of `a`, and `r − 1` copies of `a` supply the fine residue.
`caseP_large` uses the `FrameCert` route where `M ≥ 2a + 4` makes
the budget slack ample; `caseP_r3`/`caseP_r4` and the three certificates all
go through the pair construction `caseP_pair`.
-/
import ErdosProblems.Erdos1112.Sharp.Lift
import ErdosProblems.Erdos1112.Sharp.Frame
import ErdosProblems.Erdos1112.Sharp.Staircase

namespace Erdos1112
namespace Proof

/-- the ETAneg lemma (ETAneg; `a ∣ b + M`, `M ≥ 2a + 4`).

`FrameCert` route: with `Y = ⌈(a−1)/2⌉ = a/2`, `Z = ⌊(a−1)/2⌋ = (a−1)/2`
(so `Y + Z = a − 1`) and `x = M − a`, every residue `ρ` mod `a` has a box
representative — either `(w, 0)` (`w ≤ Y`, height `w·b`) or `(0, a−w)`
(height `(a−w)·M`), by the signed cover `j·b + k·M ≡ (j−k)·b (mod a)`. The
budget corner (`Y·b`, `a` even, `b = M−1`) is vacuous because `a ∣ b + M`
with `a` even forces `b + M` even, hence `b ≤ M − 2`. -/
theorem caseP_large {a b M : ℕ} (hc : HardCore a b M) (hP : a ∣ (b + M))
    (hM : 2 * a + 4 ≤ M) : SharpTriple a b M := by
  have ha3 := hc.three_le
  obtain ⟨ha0, hab, hbM, hco, hδ⟩ := hc
  set Y : ℕ := a / 2 with hYdef
  set Z : ℕ := (a - 1) / 2 with hZdef
  have hYZ : Y + Z = a - 1 := by rw [hYdef, hZdef]; omega
  have h2Y_le : 2 * Y ≤ a := by rw [hYdef]; omega
  have h2Y_ge : a ≤ 2 * Y + 1 := by rw [hYdef]; omega
  have h2Z1 : 2 * Z + 1 ≤ a := by rw [hZdef]; omega
  -- budget: `M − 1 + Z·M ≤ a·(M − a)`
  have hZM : M - 1 + Z * M ≤ a * (M - a) := by
    zify [show a ≤ M by omega, show 1 ≤ M by omega]
    have h1 : 2 * (Z : ℤ) + 1 ≤ (a : ℤ) := by exact_mod_cast h2Z1
    nlinarith [mul_nonneg (show (0:ℤ) ≤ (a:ℤ) - 1 by omega)
        (show (0:ℤ) ≤ (M:ℤ) - 2 * a - 2 by omega),
      mul_nonneg (show (0:ℤ) ≤ (a:ℤ) - 1 - 2 * Z by omega)
        (show (0:ℤ) ≤ (M:ℤ) by positivity)]
  -- budget: `M − 1 + Y·b ≤ a·(M − a)` (the corner)
  have hYb : M - 1 + Y * b ≤ a * (M - a) := by
    rcases Nat.lt_or_ge (2 * Y) a with hodd | heven
    · -- `a` odd: `2Y + 1 = a`, use `b ≤ M − 1`
      have h2Y : 2 * Y + 1 = a := by omega
      zify [show a ≤ M by omega, show 1 ≤ M by omega]
      have hc : (2 * Y + 1 : ℤ) = (a : ℤ) := by exact_mod_cast h2Y
      have hYbb : 2 * ((Y : ℤ) * b) = ((a : ℤ) - 1) * b := by linear_combination b * hc
      nlinarith [hYbb, mul_nonneg (show (0:ℤ) ≤ (a:ℤ) - 1 by omega)
          (show (0:ℤ) ≤ (M:ℤ) - 2 * a - 1 by omega),
        mul_le_mul_of_nonneg_left (show (b:ℤ) ≤ (M:ℤ) - 1 by omega)
          (show (0:ℤ) ≤ (a:ℤ) - 1 by omega)]
    · -- `a` even: `2Y = a`, parity forces `b ≤ M − 2`
      have h2Y : 2 * Y = a := by omega
      have h2a : 2 ∣ a := ⟨Y, by omega⟩
      have h2bM : 2 ∣ (b + M) := h2a.trans hP
      have hb2 : b + 2 ≤ M := by omega
      zify [show a ≤ M by omega, show 1 ≤ M by omega]
      have hc : (2 * Y : ℤ) = (a : ℤ) := by exact_mod_cast h2Y
      have hYbb : 2 * ((Y : ℤ) * b) = (a : ℤ) * b := by linear_combination b * hc
      nlinarith [hYbb, mul_nonneg (show (0:ℤ) ≤ (a:ℤ) - 2 by omega)
          (show (0:ℤ) ≤ (M:ℤ) - 2 * a - 2 by omega),
        mul_le_mul_of_nonneg_left (show (b:ℤ) ≤ (M:ℤ) - 2 by omega)
          (show (0:ℤ) ≤ (a:ℤ) by omega)]
  -- the frame certificate
  have hcert : FrameCert a b M (M - a) Y Z := by
    refine ⟨by omega, by omega, by omega, ?_⟩
    intro ρ hρ
    obtain ⟨w0, -, hw0a, hw0res⟩ := exists_frame ha0 hco.symm 0 ρ
    rw [Nat.zero_add] at hw0a
    rw [Nat.mod_eq_of_lt hρ] at hw0res
    by_cases hw0Y : w0 ≤ Y
    · refine ⟨w0, 0, hw0Y, Nat.zero_le _, ?_, ?_⟩
      · simp only [Nat.zero_mul, Nat.add_zero]; exact hw0res
      · have hwb : w0 * b ≤ Y * b := Nat.mul_le_mul_right b hw0Y
        simp only [Nat.zero_mul, Nat.add_zero]
        exact le_trans (by omega : M - 1 + w0 * b ≤ M - 1 + Y * b) hYb
    · have hw0'le : a - w0 ≤ Z := by omega
      refine ⟨0, a - w0, Nat.zero_le _, hw0'le, ?_, ?_⟩
      · -- `((a − w0)·M) % a = ρ` via `(a − w0)·M ≡ w0·b (mod a)`
        simp only [Nat.zero_mul, Nat.zero_add]
        obtain ⟨w0', hw0'sum⟩ : ∃ w', w' + w0 = a := ⟨a - w0, by omega⟩
        rw [show a - w0 = w0' by omega]
        rw [← hw0res]
        have h1 : w0' * M ≡ w0' * M + w0 * (b + M) [MOD a] :=
          (Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).mpr (by
            rw [Nat.add_sub_cancel_left]; exact hP.mul_left w0)
        have h2 : w0' * M + w0 * (b + M) = a * M + w0 * b := by
          rw [← hw0'sum]; ring
        have h3 : a * M + w0 * b ≡ w0 * b [MOD a] := by
          have hz : a * M ≡ 0 [MOD a] := (Nat.modEq_zero_iff_dvd).mpr ⟨M, rfl⟩
          have hz' := hz.add_right (w0 * b)
          rwa [zero_add] at hz'
        calc w0' * M ≡ w0' * M + w0 * (b + M) [MOD a] := h1
          _ = a * M + w0 * b := h2
          _ ≡ w0 * b [MOD a] := h3
      · have hwM : (a - w0) * M ≤ Z * M := Nat.mul_le_mul_right M hw0'le
        simp only [Nat.zero_mul, Nat.zero_add]
        exact le_trans (by omega : M - 1 + (a - w0) * M ≤ M - 1 + Z * M) hZM
  exact hcert.sharpTriple

/-- **The pair-frame construction** (Lemmas 3.12/3.13 template, uniform in `r`).

With `b + M = r·a` (`r ≥ 3`), the multiset `(x, y, z) = (r−1, ⌈(M−r)/2⌉,
⌊(M−r)/2⌋)` realizes a run of `M` consecutive integers starting at
`max(p·b, q·M)` (`p = ⌊a/2⌋`, `q = ⌈a/2⌉−1`). A `(b, M)` pair sums to `r·a`
(a residue-free mover of `r` grid units of `a`); `r−1` copies of `a` give the
fine residue `i`. For a target `n`, pick the signed representative `w`
(`w·b ≡ n mod a`): if `w ≥ 0` spend `w` extra `b`'s, else `−w` extra `M`'s.
The four budget inequalities `E1,E2,F1,F2` (proved per-`r` by the caller)
place `n` inside the covered interval. -/
lemma caseP_pair {a b M r : ℕ}
    (hc : HardCore a b M) (hr : 3 ≤ r) (hP : b + M = r * a)
    (hE1 : (a - 1) * b + M - 1 ≤ a * (r * ((M - r) / 2) + (r - 1)))
    (hE2 : ((a - 1) / 2) * (b + M) + M - 1 ≤ a * (r * ((M - r) / 2) + (r - 1)))
    (hF1 : (a / 2) * (b + M) + M - 1 ≤ a * (r * ((M - r + 1) / 2) + (r - 1)))
    (hF2 : a * M - 1 ≤ a * (r * ((M - r + 1) / 2) + (r - 1))) :
    SharpTriple a b M := by
  have ha3 := hc.three_le
  obtain ⟨ha0, hab, hbM, hco, hδ⟩ := hc
  have hrpos : 0 < r := by omega
  set x : ℕ := r - 1 with hxdef
  set z : ℕ := (M - r) / 2 with hzdef
  set y : ℕ := (M - r + 1) / 2 with hydef
  set p : ℕ := a / 2 with hpdef
  set q : ℕ := (a - 1) / 2 with hqdef
  -- `M ≥ a + r − 1` (from `b < M`, i.e. `ra ≤ 2M − 1`)
  have hMar : a + r - 1 ≤ M := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 3 := ⟨r - 3, by omega⟩
    have hexp : (r' + 3) * a = r' * a + 3 * a := by ring
    have h2M : r' * a + 3 * a + 1 ≤ 2 * M := by omega
    have hr'a : 3 * r' ≤ r' * a := by
      have h := Nat.mul_le_mul_left r' ha3; omega
    omega
  have hpq : p + q = a - 1 := by rw [hpdef, hqdef]; omega
  have hyz : y + z = M - r := by rw [hydef, hzdef]; omega
  have hzy : z ≤ y := by rw [hydef, hzdef]; omega
  have hbud : x + y + z = M - 1 := by rw [hxdef]; omega
  have hpy : p ≤ y := by rw [hpdef, hydef]; omega
  have hqz : q ≤ z := by rw [hqdef, hzdef]; omega
  set low : ℕ := max (p * b) (q * M) with hlowdef
  -- `low + M − 1 ≤ a·(r·z + x)` and the `+q·b` variant (rz-group: E1, E2)
  have hpqM : p * M + q * M = (a - 1) * M := by rw [← Nat.add_mul, hpq]
  have hpqb : p * b + q * b = (a - 1) * b := by rw [← Nat.add_mul, hpq]
  have haM : (a - 1) * M + M = a * M := by rw [← Nat.succ_mul]; congr 1; omega
  have hqbM : q * b + q * M = q * (b + M) := by rw [← Nat.mul_add]
  have hpbM : p * b + p * M = p * (b + M) := by rw [← Nat.mul_add]
  have hlow_rz : low + M - 1 ≤ a * (r * z + x) := by
    rw [hlowdef]
    rcases le_total (p * b) (q * M) with h | h
    · rw [max_eq_right h]
      have hle : q * M ≤ q * (b + M) := Nat.mul_le_mul_left q (by omega)
      omega
    · rw [max_eq_left h]
      have hle : p * b ≤ (a - 1) * b := Nat.mul_le_mul_right b (by omega)
      omega
  have hlow_rz_qb : low + M - 1 + q * b ≤ a * (r * z + x) := by
    rw [hlowdef]
    rcases le_total (p * b) (q * M) with h | h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h]
      have : p * b + q * b = (a - 1) * b := hpqb
      omega
  have hlow_ry_pM : low + M - 1 + p * M ≤ a * (r * y + x) := by
    rw [hlowdef]
    rcases le_total (p * b) (q * M) with h | h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h]; omega
  -- assemble
  refine ⟨stair a b M x y z, ?_, ?_, low, ?_⟩
  · intro w hw
    simp only [stair, Multiset.mem_add, Multiset.mem_replicate] at hw
    rcases hw with (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · simp only [stair, Multiset.card_add, Multiset.card_replicate]; omega
  · intro i hi
    set n : ℕ := low + i with hndef
    obtain ⟨w0, -, hw0a, hw0res⟩ := exists_frame ha0 hco.symm 0 n
    rw [Nat.zero_add] at hw0a
    by_cases hw0p : w0 ≤ p
    · -- `w ≥ 0` branch: `w0` extra `b`'s
      have hw0b_le : w0 * b ≤ n := by
        have h1 : w0 * b ≤ p * b := Nat.mul_le_mul_right b hw0p
        have h2 : p * b ≤ low := le_max_left _ _
        omega
      have hdvd : a ∣ n - w0 * b := (Nat.modEq_iff_dvd' hw0b_le).mp hw0res
      set A : ℕ := (n - w0 * b) / a with hAdef
      have hAa : a * A = n - w0 * b := Nat.mul_div_cancel' hdvd
      have hnA : n = w0 * b + a * A := by omega
      set k' : ℕ := A / r with hk'def
      set i' : ℕ := A % r with hi'def
      have hAik : A = i' + r * k' := by
        rw [hi'def, hk'def, Nat.add_comm]; exact (Nat.div_add_mod A r).symm
      have hi'x : i' ≤ x := by rw [hi'def, hxdef]; have := Nat.mod_lt A hrpos; omega
      -- `A ≤ r·z + x`
      have hAle : a * A ≤ a * (r * z + x) := by
        have : a * A ≤ low + M - 1 := by omega
        omega
      have hC1 : A ≤ r * z + x := Nat.le_of_mul_le_mul_left hAle ha0
      have hk'z : k' ≤ z := by
        rw [hk'def]
        have hlt : A < (z + 1) * r := by
          have : (z + 1) * r = r * z + r := by ring
          omega
        exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hrpos).mpr hlt)
      -- `A + r·w0 ≤ r·y + x`
      have harw : a * r * w0 = w0 * b + w0 * M := by
        rw [show w0 * b + w0 * M = w0 * (b + M) from by ring, hP]; ring
      have hC2mul : a * (A + r * w0) = n + w0 * M := by
        have hexp : a * (A + r * w0) = a * A + a * r * w0 := by ring
        rw [hexp, harw]; omega
      have hC2 : A + r * w0 ≤ r * y + x := by
        apply Nat.le_of_mul_le_mul_left _ ha0
        rw [hC2mul]
        have hw0M : w0 * M ≤ p * M := Nat.mul_le_mul_right M hw0p
        omega
      have hjy : w0 + k' ≤ y := by
        have hrk : k' * r ≤ A := by rw [hk'def]; exact Nat.div_mul_le_self A r
        have hlt : (w0 + k') * r < (y + 1) * r := by
          have e1 : (w0 + k') * r = r * w0 + k' * r := by ring
          have e2 : (y + 1) * r = r * y + r := by ring
          omega
        exact Nat.lt_succ_iff.mp (lt_of_mul_lt_mul_right hlt (Nat.zero_le _))
      refine mem_subsetSums.mpr ⟨Multiset.replicate i' a +
        Multiset.replicate (w0 + k') b + Multiset.replicate k' M, ?_, ?_⟩
      · exact add_le_add (add_le_add
          ((Multiset.replicate_le_replicate a).mpr hi'x)
          ((Multiset.replicate_le_replicate b).mpr hjy))
          ((Multiset.replicate_le_replicate M).mpr hk'z)
      · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
        have hkbM : k' * b + k' * M = k' * (r * a) := by rw [← hP]; ring
        have hstep : i' * a + (w0 + k') * b + k' * M = w0 * b + a * A := by
          have expand : i' * a + (w0 + k') * b + k' * M
              = i' * a + w0 * b + (k' * b + k' * M) := by ring
          rw [expand, hkbM, hAik]; ring
        rw [hstep]; exact hnA.symm
    · -- `w < 0` branch: `v = a − w0` extra `M`'s
      have hw0p' : p < w0 := by omega
      set v : ℕ := a - w0 with hvdef
      have hv1 : 1 ≤ v := by omega
      have hvq : v ≤ q := by omega
      have hvw0 : v + w0 = a := by omega
      -- `v·M ≡ w0·b (mod a)` hence `v·M ≡ n (mod a)`
      have hvM_res : (v * M) % a = n % a := by
        have h1 : v * M ≡ v * M + w0 * (b + M) [MOD a] :=
          (Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).mpr (by
            rw [Nat.add_sub_cancel_left, hP]; exact ⟨w0 * r, by ring⟩)
        have h2 : v * M + w0 * (b + M) = a * M + w0 * b := by
          rw [← hvw0]; ring
        have h3 : a * M + w0 * b ≡ w0 * b [MOD a] := by
          have hz : a * M ≡ 0 [MOD a] := (Nat.modEq_zero_iff_dvd).mpr ⟨M, rfl⟩
          have hz' := hz.add_right (w0 * b)
          rwa [zero_add] at hz'
        have hchain : v * M ≡ w0 * b [MOD a] := by
          calc v * M ≡ v * M + w0 * (b + M) [MOD a] := h1
            _ = a * M + w0 * b := h2
            _ ≡ w0 * b [MOD a] := h3
        exact hchain.trans hw0res
      have hvM_le : v * M ≤ n := by
        have h1 : v * M ≤ q * M := Nat.mul_le_mul_right M hvq
        have h2 : q * M ≤ low := le_max_right _ _
        omega
      have hdvd : a ∣ n - v * M := (Nat.modEq_iff_dvd' hvM_le).mp hvM_res
      set A : ℕ := (n - v * M) / a with hAdef
      have hAa : a * A = n - v * M := Nat.mul_div_cancel' hdvd
      have hnA : n = v * M + a * A := by omega
      set j' : ℕ := A / r with hj'def
      set i' : ℕ := A % r with hi'def
      have hAij : A = i' + r * j' := by
        rw [hi'def, hj'def, Nat.add_comm]; exact (Nat.div_add_mod A r).symm
      have hi'x : i' ≤ x := by rw [hi'def, hxdef]; have := Nat.mod_lt A hrpos; omega
      -- `A ≤ r·y + x` (from rz-group + z ≤ y)
      have hAle : a * A ≤ a * (r * y + x) := by
        have hle1 : a * A ≤ low + M - 1 := by omega
        have hle2 : a * (r * z + x) ≤ a * (r * y + x) :=
          Nat.mul_le_mul_left a (by
            have : r * z ≤ r * y := Nat.mul_le_mul_left r hzy
            omega)
        omega
      have hjy : j' ≤ y := by
        have hAry : A ≤ r * y + x := Nat.le_of_mul_le_mul_left hAle ha0
        rw [hj'def]
        have hlt : A < (y + 1) * r := by
          have : (y + 1) * r = r * y + r := by ring
          omega
        exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hrpos).mpr hlt)
      -- `A + r·v ≤ r·z + x`
      have hbrv : a * r * v = v * b + v * M := by
        rw [show v * b + v * M = v * (b + M) from by ring, hP]; ring
      have hD2mul : a * (A + r * v) = n + v * b := by
        have hexp : a * (A + r * v) = a * A + a * r * v := by ring
        rw [hexp, hbrv]; omega
      have hD2 : A + r * v ≤ r * z + x := by
        apply Nat.le_of_mul_le_mul_left _ ha0
        rw [hD2mul]
        have hvb : v * b ≤ q * b := Nat.mul_le_mul_right b hvq
        omega
      have hk'z : j' + v ≤ z := by
        have hrj : j' * r ≤ A := by rw [hj'def]; exact Nat.div_mul_le_self A r
        have hlt : (j' + v) * r < (z + 1) * r := by
          have e1 : (j' + v) * r = r * v + j' * r := by ring
          have e2 : (z + 1) * r = r * z + r := by ring
          omega
        exact Nat.lt_succ_iff.mp (lt_of_mul_lt_mul_right hlt (Nat.zero_le _))
      refine mem_subsetSums.mpr ⟨Multiset.replicate i' a +
        Multiset.replicate j' b + Multiset.replicate (j' + v) M, ?_, ?_⟩
      · exact add_le_add (add_le_add
          ((Multiset.replicate_le_replicate a).mpr hi'x)
          ((Multiset.replicate_le_replicate b).mpr hjy))
          ((Multiset.replicate_le_replicate M).mpr hk'z)
      · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
        have hjbM : j' * b + j' * M = j' * (r * a) := by rw [← hP]; ring
        have hstep : i' * a + j' * b + (j' + v) * M = v * M + a * A := by
          have expand : i' * a + j' * b + (j' + v) * M
              = i' * a + (j' * b + j' * M) + v * M := by ring
          rw [expand, hjbM, hAij]; ring
        rw [hstep]; exact hnA.symm

set_option maxHeartbeats 1600000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
/-- the r = 3 pair lemma (G′; `b + M = 3a`, i.e. `M < 2a`) — pair construction, `r = 3`. -/
theorem caseP_r3 {a b M : ℕ} (hc : HardCore a b M) (hP : b + M = 3 * a) :
    SharpTriple a b M := by
  have ha3 := hc.three_le
  have ha0 : 0 < a := hc.1
  have hab : a < b := hc.2.1
  have hbM : b < M := hc.2.2.1
  have hδ : M + 2 ≤ a + b := hc.2.2.2.2
  have hbz : (b : ℤ) + M = 3 * a := by exact_mod_cast hP
  have hbM' : (b : ℤ) < M := by exact_mod_cast hbM
  have hMb : (0 : ℤ) ≤ 2 * (M : ℤ) - 3 * a := by linarith
  have hM2a : (M : ℤ) < 2 * a := by
    have : M < 2 * a := by omega
    exact_mod_cast this
  refine caseP_pair (r := 3) hc (by norm_num) hP ?_ ?_ ?_ ?_
  · -- E1
    rcases Nat.lt_or_ge a 8 with hs | hs
    · interval_cases a <;> omega
    · set z := (M - 3) / 2 with hzd
      have hzz : (M : ℤ) ≤ 2 * z + 4 := by exact_mod_cast (show M ≤ 2 * z + 4 from by omega)
      have haa : (8 : ℤ) ≤ a := by exact_mod_cast hs
      have hbe : (b : ℤ) = 3 * a - M := by linarith
      have hpos : 1 ≤ (a - 1) * b + M := le_trans (by omega) (Nat.le_add_left M _)
      zify [show 1 ≤ a by omega, hpos]
      rw [hbe]
      nlinarith [hzz, haa, hMb, hM2a,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ 2 * (z:ℤ) + 4 - M by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) hMb,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 8 by linarith)]
  · -- E2
    rcases Nat.lt_or_ge a 8 with hs | hs
    · interval_cases a <;> omega
    · set z := (M - 3) / 2 with hzd
      set q := (a - 1) / 2 with hqd
      have hzz : (M : ℤ) ≤ 2 * z + 4 := by exact_mod_cast (show M ≤ 2 * z + 4 from by omega)
      have hqq : (2 : ℤ) * q + 1 ≤ (a : ℤ) := by exact_mod_cast (show 2 * q + 1 ≤ a from by omega)
      have haa : (8 : ℤ) ≤ a := by exact_mod_cast hs
      have hpos : 1 ≤ q * (b + M) + M := le_trans (by omega) (Nat.le_add_left M _)
      zify [hpos]
      rw [hbz]
      nlinarith [hzz, hqq, haa, hMb, hM2a,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ 2 * (z:ℤ) + 4 - M by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 1 - 2 * q by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) hMb,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 8 by linarith)]
  · -- F1
    rcases Nat.lt_or_ge a 8 with hs | hs
    · interval_cases a <;> omega
    · set y := (M - 3 + 1) / 2 with hyd
      set p := a / 2 with hpd
      have hyy : (M : ℤ) ≤ 2 * y + 3 := by exact_mod_cast (show M ≤ 2 * y + 3 from by omega)
      have hpp : (2 : ℤ) * p ≤ (a : ℤ) := by exact_mod_cast (show 2 * p ≤ a from by omega)
      have haa : (8 : ℤ) ≤ a := by exact_mod_cast hs
      have hpos : 1 ≤ p * (b + M) + M := le_trans (by omega) (Nat.le_add_left M _)
      zify [hpos]
      rw [hbz]
      nlinarith [hyy, hpp, haa, hMb, hM2a,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ 2 * (y:ℤ) + 3 - M by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 2 * p by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) hMb,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 8 by linarith)]
  · -- F2
    rcases Nat.lt_or_ge a 8 with hs | hs
    · interval_cases a <;> omega
    · set y := (M - 3 + 1) / 2 with hyd
      have hyy : (M : ℤ) ≤ 2 * y + 3 := by exact_mod_cast (show M ≤ 2 * y + 3 from by omega)
      have haa : (8 : ℤ) ≤ a := by exact_mod_cast hs
      have hpos : 1 ≤ a * M := Nat.mul_pos ha0 (by omega : 0 < M)
      zify [hpos]
      nlinarith [hyy, haa, hMb, hM2a,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ 2 * (y:ℤ) + 3 - M by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) hMb,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 8 by linarith)]

set_option maxHeartbeats 1600000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
/-- the r = 4 pair lemma (G; `b + M = 4a`) — pair construction, `r = 4`. -/
theorem caseP_r4 {a b M : ℕ} (hc : HardCore a b M) (hP : b + M = 4 * a) :
    SharpTriple a b M := by
  have ha3 := hc.three_le
  have ha0 : 0 < a := hc.1
  have hab : a < b := hc.2.1
  have hbM : b < M := hc.2.2.1
  have hδ : M + 2 ≤ a + b := hc.2.2.2.2
  have hbz : (b : ℤ) + M = 4 * a := by exact_mod_cast hP
  have hbM' : (b : ℤ) < M := by exact_mod_cast hbM
  have hMb : (0 : ℤ) ≤ 2 * (M : ℤ) - 4 * a := by linarith
  have hM3a : (M : ℤ) < 3 * a := by
    have : M < 3 * a := by omega
    exact_mod_cast this
  refine caseP_pair (r := 4) hc (by norm_num) hP ?_ ?_ ?_ ?_
  · -- E1
    rcases Nat.lt_or_ge a 8 with hs | hs
    · interval_cases a <;> omega
    · set z := (M - 4) / 2 with hzd
      have hzz : (M : ℤ) ≤ 2 * z + 5 := by exact_mod_cast (show M ≤ 2 * z + 5 from by omega)
      have haa : (8 : ℤ) ≤ a := by exact_mod_cast hs
      have hbe : (b : ℤ) = 4 * a - M := by linarith
      have hpos : 1 ≤ (a - 1) * b + M := le_trans (by omega) (Nat.le_add_left M _)
      zify [show 1 ≤ a by omega, hpos]
      rw [hbe]
      nlinarith [hzz, haa, hMb, hM3a,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ 2 * (z:ℤ) + 5 - M by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) hMb,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 8 by linarith)]
  · -- E2
    rcases Nat.lt_or_ge a 8 with hs | hs
    · interval_cases a <;> omega
    · set z := (M - 4) / 2 with hzd
      set q := (a - 1) / 2 with hqd
      have hzz : (M : ℤ) ≤ 2 * z + 5 := by exact_mod_cast (show M ≤ 2 * z + 5 from by omega)
      have hqq : (2 : ℤ) * q + 1 ≤ (a : ℤ) := by exact_mod_cast (show 2 * q + 1 ≤ a from by omega)
      have haa : (8 : ℤ) ≤ a := by exact_mod_cast hs
      have hpos : 1 ≤ q * (b + M) + M := le_trans (by omega) (Nat.le_add_left M _)
      zify [hpos]
      rw [hbz]
      nlinarith [hzz, hqq, haa, hMb, hM3a,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ 2 * (z:ℤ) + 5 - M by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 1 - 2 * q by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) hMb,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 8 by linarith)]
  · -- F1
    rcases Nat.lt_or_ge a 8 with hs | hs
    · interval_cases a <;> omega
    · set y := (M - 4 + 1) / 2 with hyd
      set p := a / 2 with hpd
      have hyy : (M : ℤ) ≤ 2 * y + 4 := by exact_mod_cast (show M ≤ 2 * y + 4 from by omega)
      have hpp : (2 : ℤ) * p ≤ (a : ℤ) := by exact_mod_cast (show 2 * p ≤ a from by omega)
      have haa : (8 : ℤ) ≤ a := by exact_mod_cast hs
      have hpos : 1 ≤ p * (b + M) + M := le_trans (by omega) (Nat.le_add_left M _)
      zify [hpos]
      rw [hbz]
      nlinarith [hyy, hpp, haa, hMb, hM3a,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ 2 * (y:ℤ) + 4 - M by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 2 * p by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) hMb,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 8 by linarith)]
  · -- F2
    rcases Nat.lt_or_ge a 8 with hs | hs
    · interval_cases a <;> omega
    · set y := (M - 4 + 1) / 2 with hyd
      have hyy : (M : ℤ) ≤ 2 * y + 4 := by exact_mod_cast (show M ≤ 2 * y + 4 from by omega)
      have haa : (8 : ℤ) ≤ a := by exact_mod_cast hs
      have hpos : 1 ≤ a * M := Nat.mul_pos ha0 (by omega : 0 < M)
      zify [hpos]
      nlinarith [hyy, haa, hMb, hM3a,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ 2 * (y:ℤ) + 4 - M by linarith),
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) hMb,
        mul_nonneg (show (0:ℤ) ≤ (a:ℤ) by positivity) (show (0:ℤ) ≤ (a:ℤ) - 8 by linarith)]

/-- **Case P assembled** (Exhaustion of Case P, the subset-sum section): every `η = −1` triple
`b + M = r·a` is covered — `r = 3` (the r = 3 pair lemma), `r = 4` (the r = 4 pair lemma),
`M ≥ 2a + 4` (the ETAneg lemma), and the `r ≥ 5, M < 2a + 4` corner (the three
explicit triples `(3,7,8), (4,9,11), (5,12,13)`) directly by the pair
construction. -/
theorem caseP {a b M : ℕ} (hc : HardCore a b M) (hP : a ∣ (b + M)) :
    SharpTriple a b M := by
  have ha3 := hc.three_le
  have ha0 : 0 < a := hc.1
  have hab : a < b := hc.2.1
  have hbM : b < M := hc.2.2.1
  have hδ : M + 2 ≤ a + b := hc.2.2.2.2
  obtain ⟨r, hr⟩ := hP
  have hr3 : 3 ≤ r := by
    by_contra hcon
    push Not at hcon
    interval_cases r <;> omega
  rcases Nat.lt_or_ge M (2 * a + 4) with hMs | hMl
  · -- `M < 2a + 4`
    have hM2 : a * r < 4 * a + 8 := by omega
    rcases Nat.lt_or_ge r 5 with hr5 | hr5
    · -- `r = 3` or `r = 4`
      interval_cases r
      · exact caseP_r3 hc (by omega)
      · exact caseP_r4 hc (by omega)
    · -- `r ≥ 5` : `a` bounded, finite corner
      have ha8 : a < 8 := by
        have h5a : 5 * a ≤ a * r := by
          have := Nat.mul_le_mul_left a hr5; omega
        omega
      have hr7 : r ≤ 6 := by
        by_contra hcon
        push Not at hcon
        have h7a : 7 * a ≤ a * r := by
          have := Nat.mul_le_mul_left a hcon; omega
        omega
      interval_cases r
      · interval_cases a <;>
          exact caseP_pair (r := 5) hc (by norm_num) (by omega) (by omega) (by omega)
            (by omega) (by omega)
      · interval_cases a <;>
          exact caseP_pair (r := 6) hc (by norm_num) (by omega) (by omega) (by omega)
            (by omega) (by omega)
  · -- `M ≥ 2a + 4`
    exact caseP_large hc ⟨r, hr⟩ hMl

end Proof
end Erdos1112
