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
the staircase lemma: staircase windows and merges over `G = {a, b, M}`,
including the extended form (d) with the frame-merge condition
`V′ − C′ ≥ a − 1`. The counterexample showing the condition is NOT
removable — `(a,b,M) = (5,7,9)`, multiset `{5,5,5,7}` missing `11` inside
the would-be interval `[10,12]` — is pinned below as a machine-checked
guard.

Notation (paper): `e := b − a`, `μ := M − a`, `g := gcd(e, μ)`, `e′ := e/g`,
`μ′ := μ/g` (coprime, `e′ < μ′`), `C′ := (e′−1)(μ′−1)`, and for the staircase
multiset `(x, y, z)`: `c := y + z`, `V′ := y·e′ + z·μ′ − C′`.

Formalization conventions: `C′, V′` are parameters pinned by ADDITIVE
defining hypotheses (`hV' : V' + C' = e'*y + μ'*z`) to dodge ℕ-subtraction;
the merge condition is `hmerge : a + C' ≤ V' + 1` (⟺ `V′−C′ ≥ a−1`); the
extended form's descent uses the closed form `j* = (u₀ − V' + a − 1)/a`, so
the single-frame-per-class case (`J = 0`) needs no separate treatment.
-/
import ErdosProblems.Erdos1112.Sharp.TwoGen
import ErdosProblems.Erdos1112.Sharp.Frame

namespace Erdos1112
namespace Proof

/-- The staircase multiset `(x, y, z)` of copies of `(a, b, M)`. -/
def stair (a b M x y z : ℕ) : Multiset ℕ :=
  Multiset.replicate x a + Multiset.replicate y b + Multiset.replicate z M

/-- `n < (n/d + 1)·d` for `d > 0` (Euclid remainder bound). -/
private lemma lt_div_add_one_mul_self (n : ℕ) {d : ℕ} (hd : 0 < d) :
    n < (n / d + 1) * d := by
  have h1 := Nat.div_add_mod n d
  have h2 := Nat.mod_lt n hd
  have h3 : (n / d + 1) * d = d * (n / d) + d := by ring
  omega

section Staircase

variable {a b M x y z g e' μ' C' V' : ℕ}

/-- Basic facts about the gcd-normalized letters, packaged. -/
structure StairSetup (a b M g e' μ' : ℕ) : Prop where
  hab : a < b
  hbM : b < M
  ha : 0 < a
  hgdef : g = Nat.gcd (b - a) (M - a)
  he' : e' = (b - a) / g
  hμ' : μ' = (M - a) / g

namespace StairSetup

lemma g_pos (S : StairSetup a b M g e' μ') : 0 < g := by
  rw [S.hgdef]
  have hab := S.hab
  exact Nat.gcd_pos_of_pos_left _ (by omega)

lemma g_dvd_e (S : StairSetup a b M g e' μ') : g ∣ b - a :=
  S.hgdef ▸ Nat.gcd_dvd_left _ _

lemma g_dvd_μ (S : StairSetup a b M g e' μ') : g ∣ M - a :=
  S.hgdef ▸ Nat.gcd_dvd_right _ _

lemma e_eq (S : StairSetup a b M g e' μ') : b = a + g * e' := by
  have h := Nat.mul_div_cancel' S.g_dvd_e
  rw [S.he']
  have hab := S.hab
  omega

lemma μ_eq (S : StairSetup a b M g e' μ') : M = a + g * μ' := by
  have h := Nat.mul_div_cancel' S.g_dvd_μ
  rw [S.hμ']
  have hbM := S.hbM
  have hab := S.hab
  omega

lemma e'_pos (S : StairSetup a b M g e' μ') : 0 < e' := by
  rw [S.he']
  have hab := S.hab
  exact Nat.div_pos (Nat.le_of_dvd (by omega) S.g_dvd_e) S.g_pos

lemma e'_lt_μ' (S : StairSetup a b M g e' μ') : e' < μ' := by
  have h1 := S.e_eq
  have h2 := S.μ_eq
  have hbM := S.hbM
  have h3 : g * e' < g * μ' := by omega
  exact Nat.lt_of_mul_lt_mul_left h3

lemma coprime' (S : StairSetup a b M g e' μ') : Nat.Coprime e' μ' := by
  rw [S.he', S.hμ', S.hgdef]
  exact Nat.coprime_div_gcd_div_gcd (S.hgdef ▸ S.g_pos)

end StairSetup

/-- **3.3(a) (level windows).** For `y ≥ μ′−1`, `z ≥ e′−1` and any level
`y + z ≤ t ≤ x`: every `u ∈ [C′, V′]` gives `t·a + g·u` as a subset sum of
the staircase, realized with exactly `t` elements. -/
theorem staircase_level (S : StairSetup a b M g e' μ')
    (hC' : C' = (e' - 1) * (μ' - 1)) (hV' : V' + C' = e' * y + μ' * z)
    (hy : μ' - 1 ≤ y) (hz : e' - 1 ≤ z)
    {t : ℕ} (hct : y + z ≤ t) (htx : t ≤ x)
    {u : ℕ} (hu_lo : C' ≤ u) (hu_hi : u ≤ V') :
    t * a + g * u ∈ subsetSums (stair a b M x y z) := by
  have he'μ' := S.e'_lt_μ'
  have he'0 := S.e'_pos
  have hco' := S.coprime'
  obtain ⟨i, j, hiy, hjz, huij⟩ :=
    twoGen_interval he'μ' he'0 hco' hy hz u (hC' ▸ hu_lo)
      (by rw [← hC']; omega)
  apply mem_subsetSums.mpr
  refine ⟨Multiset.replicate (t - i - j) a + Multiset.replicate i b +
    Multiset.replicate j M, ?_, ?_⟩
  · exact add_le_add (add_le_add
      ((Multiset.replicate_le_replicate a).mpr (by omega))
      ((Multiset.replicate_le_replicate b).mpr hiy))
      ((Multiset.replicate_le_replicate M).mpr hjz)
  · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
    have hijt : t - i - j + i + j = t := by omega
    calc (t - i - j) * a + i * b + j * M
        = (t - i - j) * a + i * (a + g * e') + j * (a + g * μ') := by
          rw [← S.e_eq, ← S.μ_eq]
      _ = (t - i - j + i + j) * a + g * (i * e' + j * μ') := by ring
      _ = t * a + g * u := by rw [hijt, ← huij]

/-- Residue frame: since `gcd(a, g) = 1`, some level in `[c, c+g)` matches
`n`'s residue class modulo `g`. -/
lemma exists_frame (hg : 0 < g) (hag : Nat.Coprime a g) (c n : ℕ) :
    ∃ t₀, c ≤ t₀ ∧ t₀ < c + g ∧ (t₀ * a) % g = n % g := by
  have : NeZero g := ⟨hg.ne'⟩
  have hunit : IsUnit (a : ZMod g) := by
    rw [ZMod.isUnit_iff_coprime]
    exact hag
  set v : ZMod g := (((n : ZMod g) - (c : ZMod g) * (a : ZMod g)) * hunit.unit⁻¹) with hvdef
  refine ⟨c + v.val, Nat.le_add_right _ _, by
    have := ZMod.val_lt v
    omega, ?_⟩
  have hcast : (((c + v.val) * a : ℕ) : ZMod g) = ((n : ℕ) : ZMod g) := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
    rw [hvdef]
    have hinv : ((n : ZMod g) - (c : ZMod g) * (a : ZMod g)) * ↑hunit.unit⁻¹ * (a : ZMod g)
        = (n : ZMod g) - (c : ZMod g) * (a : ZMod g) := by
      have hu1 : (↑hunit.unit⁻¹ : ZMod g) * (a : ZMod g) = 1 := hunit.val_inv_mul
      calc ((n : ZMod g) - (c : ZMod g) * (a : ZMod g)) * ↑hunit.unit⁻¹ * (a : ZMod g)
          = ((n : ZMod g) - (c : ZMod g) * (a : ZMod g)) * (↑hunit.unit⁻¹ * (a : ZMod g)) := by
            ring
        _ = (n : ZMod g) - (c : ZMod g) * (a : ZMod g) := by rw [hu1, mul_one]
    calc
      ((c : ZMod g) + ((n : ZMod g) - (c : ZMod g) * (a : ZMod g)) * ↑hunit.unit⁻¹) * (a : ZMod g)
        = (c : ZMod g) * (a : ZMod g) +
          ((n : ZMod g) - (c : ZMod g) * (a : ZMod g)) * ↑hunit.unit⁻¹ * (a : ZMod g) := by
          ring
      _ = (n : ZMod g) := by rw [hinv]; ring
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast

/-- Single-frame landing: a level `t₀ ∈ [c, x]` in `n`'s residue class with
`n` inside its window realizes `n`. -/
theorem staircase_land (S : StairSetup a b M g e' μ')
    (hC' : C' = (e' - 1) * (μ' - 1)) (hV' : V' + C' = e' * y + μ' * z)
    (hy : μ' - 1 ≤ y) (hz : e' - 1 ≤ z)
    {t₀ n : ℕ} (hct : y + z ≤ t₀) (htx : t₀ ≤ x)
    (hres : (t₀ * a) % g = n % g)
    (hlo : t₀ * a + g * C' ≤ n) (hhi : n ≤ t₀ * a + g * V') :
    n ∈ subsetSums (stair a b M x y z) := by
  have hg := S.g_pos
  have hta_n : t₀ * a ≤ n := le_trans (Nat.le_add_right _ _) hlo
  have hdvd : g ∣ n - t₀ * a := (Nat.modEq_iff_dvd' hta_n).mp hres
  set u : ℕ := (n - t₀ * a) / g with hudef
  have hu : g * u = n - t₀ * a := Nat.mul_div_cancel' hdvd
  have hn_eq : n = t₀ * a + g * u := by omega
  have hu_lo : C' ≤ u := by
    have h1 : g * C' ≤ g * u := by omega
    exact Nat.le_of_mul_le_mul_left h1 hg
  have hu_hi : u ≤ V' := by
    have h1 : g * u ≤ g * V' := by omega
    exact Nat.le_of_mul_le_mul_left h1 hg
  rw [hn_eq]
  exact staircase_level S hC' hV' hy hz hct htx hu_lo hu_hi

/-- **The staircase extended/base form (d), base form.** With `x ≥ c + g − 1`
(one frame per residue class
available in `[c, c+g)`), the sums cover the solid interval
`[(c+g−1)·a + g·C′, c·a + g·V′]` — no merge hypothesis. -/
theorem staircase_phase_base (S : StairSetup a b M g e' μ')
    (hC' : C' = (e' - 1) * (μ' - 1)) (hV' : V' + C' = e' * y + μ' * z)
    (hag : Nat.Coprime a g)
    (hy : μ' - 1 ≤ y) (hz : e' - 1 ≤ z)
    (hx : y + z + g - 1 ≤ x) :
    ∀ n, (y + z + g - 1) * a + g * C' ≤ n → n ≤ (y + z) * a + g * V' →
      n ∈ subsetSums (stair a b M x y z) := by
  intro n hnlo hnhi
  have hg := S.g_pos
  obtain ⟨t₀, ht₀c, ht₀g, hres⟩ := exists_frame hg hag (y + z) n
  have hta1 : t₀ * a ≤ (y + z + g - 1) * a :=
    Nat.mul_le_mul_right a (by omega)
  have hta2 : (y + z) * a ≤ t₀ * a := Nat.mul_le_mul_right a ht₀c
  exact staircase_land S hC' hV' hy hz ht₀c (by omega) hres
    (by omega) (by omega)

set_option maxHeartbeats 800000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
/-- **the staircase extended/base form (d), extended form.** With `x ≥ c + g` and the frame-merge
condition `V′ − C′ ≥ a − 1` (here `a + C' ≤ V' + 1`), the frames of each
residue class merge and the sums cover the solid interval
`[(c+g−1)·a + g·C′, (x−g+1)·a + g·V′]`. The merge condition is NOT removable:
see the counterexample below. -/
theorem staircase_phase_extended (S : StairSetup a b M g e' μ')
    (hC' : C' = (e' - 1) * (μ' - 1)) (hV' : V' + C' = e' * y + μ' * z)
    (hag : Nat.Coprime a g)
    (hy : μ' - 1 ≤ y) (hz : e' - 1 ≤ z)
    (hx : y + z + g ≤ x)
    (hmerge : a + C' ≤ V' + 1) :
    ∀ n, (y + z + g - 1) * a + g * C' ≤ n → n ≤ (x - g + 1) * a + g * V' →
      n ∈ subsetSums (stair a b M x y z) := by
  intro n hnlo hnhi
  have hg := S.g_pos
  have ha := S.ha
  obtain ⟨t₀, ht₀c, ht₀g, hres⟩ := exists_frame hg hag (y + z) n
  -- u₀: the offset at the first frame
  have hta1 : t₀ * a ≤ (y + z + g - 1) * a := Nat.mul_le_mul_right a (by omega)
  have hta_n : t₀ * a + g * C' ≤ n := by omega
  have hdvd : g ∣ n - t₀ * a :=
    (Nat.modEq_iff_dvd' (by omega)).mp hres
  set u₀ : ℕ := (n - t₀ * a) / g with hu₀def
  have hu₀ : g * u₀ = n - t₀ * a := Nat.mul_div_cancel' hdvd
  have hn_eq : n = t₀ * a + g * u₀ := by omega
  have hu₀_lo : C' ≤ u₀ := by
    have h1 : g * C' ≤ g * u₀ := by omega
    exact Nat.le_of_mul_le_mul_left h1 hg
  -- the last frame of the class below x: J := ⌊(x − t₀)/g⌋
  have hxt₀ : t₀ ≤ x := by omega
  set J : ℕ := (x - t₀) / g with hJdef
  have hJx : t₀ + J * g ≤ x := by
    have h1 := Nat.div_mul_le_self (x - t₀) g
    rw [← hJdef] at h1
    omega
  have hJmax : x - t₀ < (J + 1) * g := by
    have h1 := lt_div_add_one_mul_self (x - t₀) hg
    rw [← hJdef] at h1
    exact h1
  -- window at the last frame bounds u₀ from above: u₀ ≤ V′ + J·a
  have huJ : u₀ ≤ V' + J * a := by
    have hbr1 : (J + 1) * g = J * g + g := by ring
    have h1 : (x - g + 1) * a ≤ (t₀ + J * g) * a :=
      Nat.mul_le_mul_right a (by omega)
    have h2 : (t₀ + J * g) * a = t₀ * a + J * g * a := by ring
    have h3 : g * (V' + J * a) = g * V' + J * g * a := by ring
    have h4 : g * u₀ ≤ g * (V' + J * a) := by omega
    exact Nat.le_of_mul_le_mul_left h4 hg
  -- the descent index: j* := ⌈(u₀ − V′)/a⌉ (0 if already inside the window)
  set j : ℕ := (u₀ - V' + a - 1) / a with hjdef
  have hj_land_hi : u₀ - j * a ≤ V' := by
    have h1 := lt_div_add_one_mul_self (u₀ - V' + a - 1) ha
    rw [← hjdef] at h1
    have hexp : (j + 1) * a = j * a + a := by ring
    omega
  have hj_land_lo : C' ≤ u₀ - j * a := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hj0, Nat.zero_mul, Nat.sub_zero]
      exact hu₀_lo
    · have h1 : j * a ≤ u₀ - V' + a - 1 := by
        have h2 := Nat.div_mul_le_self (u₀ - V' + a - 1) a
        rw [← hjdef] at h2
        exact h2
      have h3 : a ≤ j * a := Nat.le_mul_of_pos_left a hjpos
      omega
  have hjJ : j ≤ J := by
    have h1 : u₀ - V' + a - 1 < (J + 1) * a := by
      have hexp : (J + 1) * a = J * a + a := by ring
      omega
    have h2 : (u₀ - V' + a - 1) / a < J + 1 :=
      (Nat.div_lt_iff_lt_mul ha).mpr h1
    rw [← hjdef] at h2
    omega
  have ht_le : t₀ + j * g ≤ x := by
    have h1 : j * g ≤ J * g := Nat.mul_le_mul_right g hjJ
    omega
  -- j·a never overshoots u₀ (uses the merge condition via V′ ≥ C′ + a − 1)
  have hja_u₀ : j * a ≤ u₀ := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hj0, Nat.zero_mul]
      exact Nat.zero_le _
    · have h1 : j * a ≤ u₀ - V' + a - 1 := by
        have h2 := Nat.div_mul_le_self (u₀ - V' + a - 1) a
        rw [← hjdef] at h2
        exact h2
      have h3 : a ≤ j * a := Nat.le_mul_of_pos_left a hjpos
      omega
  have hres' : ((t₀ + j * g) * a) % g = n % g := by
    have h1 : (t₀ + j * g) * a = t₀ * a + j * a * g := by ring
    have h2 : (t₀ * a + j * a * g) % g = (t₀ * a) % g := Nat.add_mul_mod_self_right _ _ _
    rw [h1, h2]
    exact hres
  have hgu_sub : g * (u₀ - j * a) = g * u₀ - g * (j * a) := by
    zify [hja_u₀, Nat.mul_le_mul_left g hja_u₀]
    ring
  have hbr4 : g * (j * a) = j * g * a := by ring
  have hgja : g * (j * a) ≤ g * u₀ := Nat.mul_le_mul_left g hja_u₀
  apply staircase_land S hC' hV' hy hz (le_trans ht₀c (Nat.le_add_right _ _)) ht_le hres'
  · -- lower window at the landing frame
    have h1 : (t₀ + j * g) * a = t₀ * a + j * g * a := by ring
    have h3 : g * C' ≤ g * (u₀ - j * a) := Nat.mul_le_mul_left g hj_land_lo
    omega
  · have h1 : (t₀ + j * g) * a = t₀ * a + j * g * a := by ring
    have h3 : g * (u₀ - j * a) ≤ g * V' := Nat.mul_le_mul_left g hj_land_hi
    omega

/-- **the staircase short merge (c) (short two-frame merge, `g = 1`, `x = y + z`).** Level `y+z+1`
exceeds the `a`-budget by one, so it loses exactly the zero offset; with
`V′ ≥ a + max(C′,1) − 1` the two levels still merge and the sums cover
`[(y+z)·a + C′, (y+z+1)·a + V′]`. Needed only for Case L's `a` odd, `g = 1`
branch. -/
theorem staircase_merge_c (S : StairSetup a b M g e' μ')
    (hg1 : g = 1)
    (hC' : C' = (e' - 1) * (μ' - 1)) (hV' : V' + C' = e' * y + μ' * z)
    (hy : μ' - 1 ≤ y) (hz : e' - 1 ≤ z)
    (hx : x = y + z)
    (hmerge : a + max C' 1 ≤ V' + 1) :
    ∀ n, (y + z) * a + C' ≤ n → n ≤ (y + z + 1) * a + V' →
      n ∈ subsetSums (stair a b M x y z) := by
  subst hg1
  subst hx
  have ha := S.ha
  -- level `c = y+z` covers `(y+z)*a + [C', V']`
  have hlevel_c : ∀ u, C' ≤ u → u ≤ V' →
      (y + z) * a + u ∈ subsetSums (stair a b M (y + z) y z) := by
    intro u hu_lo hu_hi
    have h := staircase_level S hC' hV' hy hz (le_refl (y + z)) (le_refl (y + z))
      hu_lo hu_hi
    simpa using h
  -- level `c+1` covers `(y+z+1)*a + [max C' 1, V']` (zero offset excluded)
  have hlevel_c1 : ∀ u, max C' 1 ≤ u → u ≤ V' →
      (y + z + 1) * a + u ∈ subsetSums (stair a b M (y + z) y z) := by
    intro u hu_lo hu_hi
    have hu1 : 1 ≤ u := le_trans (le_max_right _ _) hu_lo
    have huC : C' ≤ u := le_trans (le_max_left _ _) hu_lo
    obtain ⟨i, j, hiy, hjz, huij⟩ :=
      twoGen_interval S.e'_lt_μ' S.e'_pos S.coprime' hy hz u (hC' ▸ huC)
        (by rw [← hC']; omega)
    have hij1 : 1 ≤ i + j := by
      rcases Nat.eq_zero_or_pos (i + j) with h0 | h0
      · exfalso
        obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := by omega
        simp only [Nat.zero_mul, Nat.add_zero] at huij
        omega
      · exact h0
    apply mem_subsetSums.mpr
    refine ⟨Multiset.replicate (y + z + 1 - i - j) a + Multiset.replicate i b +
      Multiset.replicate j M, ?_, ?_⟩
    · exact add_le_add (add_le_add
        ((Multiset.replicate_le_replicate a).mpr (by omega))
        ((Multiset.replicate_le_replicate b).mpr hiy))
        ((Multiset.replicate_le_replicate M).mpr hjz)
    · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
      have hijt : y + z + 1 - i - j + i + j = y + z + 1 := by omega
      calc (y + z + 1 - i - j) * a + i * b + j * M
          = (y + z + 1 - i - j) * a + i * (a + 1 * e') + j * (a + 1 * μ') := by
            rw [← S.e_eq, ← S.μ_eq]
        _ = (y + z + 1 - i - j + i + j) * a + (i * e' + j * μ') := by ring
        _ = (y + z + 1) * a + u := by rw [hijt, ← huij]
  -- merge the two levels
  intro n hnlo hnhi
  have hab : (y + z + 1) * a = (y + z) * a + a := by ring
  rcases Nat.lt_or_ge n ((y + z) * a + V' + 1) with hcase | hcase
  · -- lands in level c
    have hn : n = (y + z) * a + (n - (y + z) * a) := by omega
    rw [hn]
    exact hlevel_c _ (by omega) (by omega)
  · -- lands in level c+1
    have haV : a ≤ V' + 1 := le_trans (by omega) hmerge
    have hge : (y + z + 1) * a ≤ n := by omega
    have hn : n = (y + z + 1) * a + (n - (y + z + 1) * a) := by omega
    rw [hn]
    refine hlevel_c1 _ ?_ (by omega)
    -- u = n - (y+z+1)*a ≥ V'+1-a ≥ max C' 1
    omega

/-- **The merge condition of the staircase extended/base form (d) is not removable**
(counterexample,
machine-checked): for `(a,b,M) = (5,7,9)` with
`(x,y,z) = (3,1,0)` — the multiset `{5,5,5,7}`, which satisfies every
hypothesis of the extended form EXCEPT `V′−C′ ≥ a−1` — the would-be interval
`[10, 12]` is broken: `11` is not a subset sum (while `10` and `12` are).
Any attempt to drop `hmerge` from `staircase_phase_extended` must fail here. -/
example :
    11 ∉ subsetSums (stair 5 7 9 3 1 0) ∧
    10 ∈ subsetSums (stair 5 7 9 3 1 0) ∧
    12 ∈ subsetSums (stair 5 7 9 3 1 0) := by
  decide

end Staircase

end Proof
end Erdos1112
