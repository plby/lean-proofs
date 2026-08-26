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
reduction layer: the L1/L2/L3 dispatch lemmas (paper 3.6–3.8) and
the reduction principle packaging Graham's reduction with the minimal-
alphabet analysis (3.5, 3.9, 3.10).

Edge hygiene:
  * L3 is stated WITHOUT assuming `1 < α` — at `α = a/d = 1` (i.e. `a ∣ b`)
    the conductor `(α−1)(β−1)` is 0 and everything still works; the equality
    corner `(α, β) = (1, 2)` is pinned as a decided instance below.
  * L3's `y ≥ α − 1` requirement is the explicit lemma `L3_y_bound`.
-/
import ErdosProblems.Erdos1112.Sharp.Staircase

namespace Erdos1112
namespace Proof

/-- **L1 (small coprime pair)**: a coprime pair `α, γ` with `α + γ + 1 ≤ M` realizes
an `M`-run within budget `M − 1` using only `α`s and `γ`s. -/
theorem sharp_of_small_coprime_pair {α γ M : ℕ} (hα : 0 < α) (hγ : 0 < γ)
    (hco : Nat.Coprime α γ) (hle : α + γ + 1 ≤ M) :
    ∃ S : Multiset ℕ, (∀ w ∈ S, w = α ∨ w = γ) ∧ S.card ≤ M - 1 ∧
      HasRun (subsetSums S) M := by
  obtain ⟨x, hxM⟩ : ∃ x, x + α = M := ⟨M - α, by omega⟩
  refine ⟨Multiset.replicate (α - 1) γ + Multiset.replicate 0 γ +
    Multiset.replicate x α, ?_, ?_, (α - 1) * γ, ?_⟩
  · intro w hw
    rcases Multiset.mem_add.mp hw with hw | hw
    · rcases Multiset.mem_add.mp hw with hw | hw
      · exact Or.inr (Multiset.eq_of_mem_replicate hw)
      · exact Or.inr (Multiset.eq_of_mem_replicate hw)
    · exact Or.inl (Multiset.eq_of_mem_replicate hw)
  · simp only [Multiset.card_add, Multiset.card_replicate]
    omega
  · intro i hi
    apply frame_lemma hα (S := (α - 1) * γ)
    · intro ρ hρ
      obtain ⟨j, -, hjα, hres⟩ := exists_frame hα hco.symm 0 ρ
      refine ⟨j, 0, by omega, le_refl 0, ?_, ?_⟩
      · rw [Nat.zero_mul, Nat.add_zero, hres, Nat.mod_eq_of_lt hρ]
      · rw [Nat.zero_mul, Nat.add_zero]
        exact Nat.mul_le_mul_right γ (by omega)
    · -- (α−1)·γ ≤ (α−1)·γ + i, trivially
      omega
    · -- (α−1)·γ + i ≤ α·x, from (α−1)(γ+1) ≤ (α−1)x and i ≤ M−1
      have h1 : γ + 1 ≤ x := by omega
      have h2 : (α - 1) * (γ + 1) ≤ (α - 1) * x := Nat.mul_le_mul_left _ h1
      have h3 : (α - 1) * (γ + 1) = (α - 1) * γ + (α - 1) := by ring
      have h4 : α * x = (α - 1) * x + x := by
        have : α = (α - 1) + 1 := by omega
        calc α * x = ((α - 1) + 1) * x := by rw [← this]
          _ = (α - 1) * x + x := by ring
      omega

/-- **L2 (pair at the boundary)**: a coprime pair at the boundary `α + β ∈ {M, M+1}`
(the paper's `t = 0` / `t = 1` split). -/
theorem sharp_of_boundary_pair {α β M : ℕ} (hα : 0 < α) (hαβ : α < β)
    (hco : Nat.Coprime α β) (hb : α + β = M ∨ α + β = M + 1) :
    ∃ S : Multiset ℕ, (∀ w ∈ S, w = α ∨ w = β) ∧ S.card ≤ M - 1 ∧
      HasRun (subsetSums S) M := by
  -- t = 1 for α + β = M, t = 0 for α + β = M + 1
  obtain ⟨t, ht⟩ : ∃ t, (α + β = M ∧ t = 1) ∨ (α + β = M + 1 ∧ t = 0) := by
    rcases hb with hb | hb
    · exact ⟨1, Or.inl ⟨hb, rfl⟩⟩
    · exact ⟨0, Or.inr ⟨hb, rfl⟩⟩
  set x : ℕ := β - 1 with hxdef
  set y : ℕ := α - 1 + t with hydef
  have hCval : (α - 1) * (β - 1) + α + β = α * β + 1 := by
    zify [show 1 ≤ α by omega, show 1 ≤ β by omega]
    ring
  have hgrid : α * x + β * y + α + β = α * β + β * (α - 1 + t) + β := by
    have h1 : α * (β - 1) + α = α * β := by
      zify [show 1 ≤ β by omega]
      ring
    rw [hxdef, hydef]
    omega
  refine ⟨Multiset.replicate x α + Multiset.replicate y β, ?_, ?_, (α - 1) * (β - 1), ?_⟩
  · intro w hw
    rcases Multiset.mem_add.mp hw with hw | hw
    · exact Or.inl (Multiset.eq_of_mem_replicate hw)
    · exact Or.inr (Multiset.eq_of_mem_replicate hw)
  · simp only [Multiset.card_add, Multiset.card_replicate]
    rcases ht with ⟨hM, ht1⟩ | ⟨hM, ht0⟩ <;> omega
  · intro i hi
    apply twoGen_hasRun hαβ hα hco (by omega) (by omega)
    · omega
    · -- (C + i) + C ≤ αx + βy: equality case is t = 0 at i = M−1
      have hββ : β * (α - 1 + t) = β * (α - 1) + β * t := by ring
      rcases ht with ⟨hM, ht1⟩ | ⟨hM, ht0⟩ <;>
        · subst_vars
          have hβα : β * (α - 1) + β = β * α := by
            zify [show 1 ≤ α by omega]
            ring
          have hαβc : α * β = β * α := Nat.mul_comm _ _
          omega

/-- **L3's `y`-requirement, explicit**: with `d ≥ 2`,
`1 ≤ α < β` and `M ≥ d·β + 1`, the count `y = M − d − β + 1` satisfies
`y ≥ α − 1` — via `(d−1)(β−1) ≥ α − 2`. -/
lemma L3_y_bound {d α β M : ℕ} (hd : 2 ≤ d) (h1 : 1 ≤ α) (hαβ : α < β)
    (hM : d * β + 1 ≤ M) : α - 1 ≤ M - d - β + 1 := by
  have h2 : (d - 1) * (β - 1) + d + β = d * β + 1 := by
    zify [show 1 ≤ d by omega, show 1 ≤ β by omega]
    ring
  have h3 : β - 1 ≤ (d - 1) * (β - 1) := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- **L3 (non-coprime pair)**: `G = {a, b, M}` with `d := gcd(a,b) ≥ 2` (so
`gcd(d, M) = 1` since `gcd(G) = 1`). Stated via `a = d·α`, `b = d·β` with
`α < β` coprime — `α = 1` (i.e. `a ∣ b`) explicitly allowed. -/
theorem sharp_of_noncoprime_pair {d α β M : ℕ} (hd : 2 ≤ d) (hα : 0 < α)
    (hαβ : α < β) (hco : Nat.Coprime α β) (hdM : Nat.Coprime M d)
    (hM : d * β + 1 ≤ M) :
    ∃ S : Multiset ℕ, (∀ w ∈ S, w = d * α ∨ w = d * β ∨ w = M) ∧
      S.card ≤ M - 1 ∧ HasRun (subsetSums S) M := by
  have hβ2 : 2 ≤ β := by omega
  have hdβ_bridge : (d - 1) * (β - 1) + d + β = d * β + 1 := by
    zify [show 1 ≤ d by omega, show 1 ≤ β by omega]
    ring
  have hdβ1 : 1 * 1 ≤ (d - 1) * (β - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hdβM : d + β + 1 ≤ M := by omega
  have hy_ge : α - 1 ≤ M - d - β + 1 := L3_y_bound hd (by omega) hαβ hM
  -- the budget inequality, DIRECT for all M ≥ dβ+1
  have hkey : 2 * ((α - 1) * (β - 1)) + M ≤ α * (β - 1) + β * (M - d - β + 1) + 1 := by
    have hMZ : (d : ℤ) * β + 1 ≤ (M : ℤ) := by exact_mod_cast hM
    zify [show 1 ≤ α by omega, show 1 ≤ β by omega, show d ≤ M by omega,
      show β ≤ M - d by omega]
    nlinarith [mul_nonneg (show (0:ℤ) ≤ (β:ℤ) - 1 by omega)
        (show (0:ℤ) ≤ (M:ℤ) - ((d:ℤ) * β + 1) by linarith),
      mul_nonneg (mul_nonneg (show (0:ℤ) ≤ (d:ℤ) - 2 by omega)
        (show (0:ℤ) ≤ (β:ℤ) by omega)) (show (0:ℤ) ≤ (β:ℤ) - 2 by omega),
      mul_nonneg (show (0:ℤ) ≤ (β:ℤ) - (α:ℤ) - 1 by omega)
        (show (0:ℤ) ≤ (β:ℤ) by omega)]
  refine ⟨Multiset.replicate (β - 1) (d * α) +
    Multiset.replicate (M - d - β + 1) (d * β) + Multiset.replicate (d - 1) M,
    ?_, ?_, d * ((α - 1) * (β - 1)) + (d - 1) * M, ?_⟩
  · intro w hw
    rcases Multiset.mem_add.mp hw with hw | hw
    · rcases Multiset.mem_add.mp hw with hw | hw
      · exact Or.inl (Multiset.eq_of_mem_replicate hw)
      · exact Or.inr (Or.inl (Multiset.eq_of_mem_replicate hw))
    · exact Or.inr (Or.inr (Multiset.eq_of_mem_replicate hw))
  · simp only [Multiset.card_add, Multiset.card_replicate]
    omega
  · intro i hi
    obtain ⟨k, -, hkd, hres⟩ := exists_frame (show 0 < d by omega) hdM 0
      (d * ((α - 1) * (β - 1)) + (d - 1) * M + i)
    set n : ℕ := d * ((α - 1) * (β - 1)) + (d - 1) * M + i with hndef
    have hkd' : k ≤ d - 1 := by omega
    have hkM_le : k * M ≤ (d - 1) * M := Nat.mul_le_mul_right M hkd'
    have hkMn : k * M ≤ n := by omega
    have hdvd : d ∣ n - k * M := (Nat.modEq_iff_dvd' hkMn).mp hres
    set w : ℕ := (n - k * M) / d with hwdef
    have hw : d * w = n - k * M := Nat.mul_div_cancel' hdvd
    have hw_lo : (α - 1) * (β - 1) ≤ w := by
      have h1 : d * ((α - 1) * (β - 1)) ≤ d * w := by omega
      exact Nat.le_of_mul_le_mul_left h1 (by omega)
    have hMd_bridge : (d - 1) * M + M = d * M := by
      zify [show 1 ≤ d by omega]
      ring
    have hdM1 : 1 ≤ d * M := Nat.mul_pos (by omega) (by omega)
    have hw_hi : w + (α - 1) * (β - 1) ≤ α * (β - 1) + β * (M - d - β + 1) := by
      have h1 : d * w ≤ d * ((α - 1) * (β - 1)) + d * M - 1 := by omega
      have h2 : w ≤ (α - 1) * (β - 1) + M - 1 := by
        by_contra hcon
        push Not at hcon
        have h3 : d * ((α - 1) * (β - 1) + M) ≤ d * w :=
          Nat.mul_le_mul_left d (by omega)
        have h4 : d * ((α - 1) * (β - 1) + M) =
            d * ((α - 1) * (β - 1)) + d * M := by ring
        omega
      omega
    obtain ⟨i', j', hi'x, hj'y, hwij⟩ :=
      twoGen_interval hαβ hα hco (le_refl (β - 1)) hy_ge w hw_lo hw_hi
    refine mem_subsetSums.mpr ⟨Multiset.replicate i' (d * α) +
      Multiset.replicate j' (d * β) + Multiset.replicate k M, ?_, ?_⟩
    · exact add_le_add (add_le_add
        ((Multiset.replicate_le_replicate _).mpr hi'x)
        ((Multiset.replicate_le_replicate _).mpr hj'y))
        ((Multiset.replicate_le_replicate _).mpr hkd')
    · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
      have hexp : i' * (d * α) + j' * (d * β) + k * M =
          d * (i' * α + j' * β) + k * M := by ring
      rw [hexp, ← hwij]
      omega

set_option maxRecDepth 100000 in
/-- The `(α, β) = (1, 2)` equality corner of L3, pinned as a decided
instance: `G = {5, 10, 11}` (`d = 5`, `a ∣ b`), witness
`{5} + 5×{10} + 4×{11}`, budget `10 = M − 1`, covering an 11-run. -/
example : ∀ i < 11, 44 + i ∈ subsetSums
    (Multiset.replicate 1 5 + Multiset.replicate 5 10 + Multiset.replicate 4 11) := by
  decide

/-! ### Reduction-layer interfaces

`sharpAt_of_hardcore`'s assembly will case-split as:
`1 ∈ G` → `sharp_of_one_mem`;  redundant `e ≠ M` → card-recursion;
redundant `e = M` → outer `ih` at `max (G.erase M) < M` + Graham fill
(`HasRun.cons_of_le`);  `|G| = 3` → L1 / L2 / L3 / hard-core `hc`
(with `Coprime M d` derived from `gcd G = 1` at the L3 branch);
`|G| ≥ 4` minimal → `sharp_of_minimal` (which consumes
`minimal_structure`'s `≥ 30` bound; the M ≤ 130 enumeration is NOT expected
to enter). -/

/-- `1 ∈ G` is trivial: `M − 1` copies of `1` cover `[0, M−1]`. -/
theorem sharp_of_one_mem (M : ℕ) :
    ∃ S : Multiset ℕ, (∀ w ∈ S, w = 1) ∧ S.card ≤ M - 1 ∧
      HasRun (subsetSums S) M := by
  refine ⟨Multiset.replicate (M - 1) 1,
    fun w hw => Multiset.eq_of_mem_replicate hw, ?_, 0, ?_⟩
  · simp [Multiset.card_replicate]
  · intro i hi
    refine mem_subsetSums.mpr ⟨Multiset.replicate i 1, ?_, ?_⟩
    · exact (Multiset.replicate_le_replicate 1).mpr (by omega)
    · simp [Multiset.sum_replicate]

/-- The 3.10 descent measure, standalone: rescaling by
`δ ≥ 2` strictly shrinks the maximum. -/
lemma rescaled_max_lt {δ M M' : ℕ} (hδ : 2 ≤ δ) (hM : 0 < M)
    (hδM' : δ * M' ≤ M) : M' < M := by
  have h2 : 2 * M' ≤ δ * M' := Nat.mul_le_mul_right M' hδ
  omega

/-- A prime other than 2 and 3 is at least 5. -/
lemma five_le_of_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    5 ≤ p := by
  have hp2 := hp.two_le
  rcases Nat.lt_or_ge p 5 with h | h
  · interval_cases p
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact absurd hp (by decide)
  · exact h

/-- Three pairwise-distinct primes multiply to at least `2·3·5 = 30`. -/
lemma thirty_le_prime_triple {p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    30 ≤ p * q * r := by
  have h2p := hp.two_le
  have h2q := hq.two_le
  have h2r := hr.two_le
  have h3 : ∀ {x : ℕ}, 2 ≤ x → x ≠ 2 → 3 ≤ x := fun hx h => by omega
  -- helper closing a leaf `30 ≤ a*b*c` from `u ≤ a, v ≤ b, w ≤ c, 30 ≤ u*v*w`
  have leaf : ∀ {a b c u v w : ℕ}, u ≤ a → v ≤ b → w ≤ c → 30 ≤ u * v * w →
      30 ≤ a * b * c := fun ha hb hc h30 =>
    le_trans h30 (Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc)
  by_cases hp2 : p = 2
  · subst hp2
    have hq3' := h3 h2q (Ne.symm hpq)
    have hr3' := h3 h2r (Ne.symm hpr)
    by_cases hq3 : q = 3
    · subst hq3
      have := five_le_of_prime hr (Ne.symm hpr) (Ne.symm hqr)
      exact leaf (le_refl 2) (le_refl 3) this (by norm_num)
    · have := five_le_of_prime hq (Ne.symm hpq) hq3
      exact leaf (le_refl 2) this hr3' (by norm_num)
  · by_cases hq2 : q = 2
    · subst hq2
      have hp3' := h3 h2p hp2
      have hr3' := h3 h2r (Ne.symm hqr)
      by_cases hp3 : p = 3
      · subst hp3
        have := five_le_of_prime hr (Ne.symm hqr) (Ne.symm hpr)
        exact leaf (le_refl 3) (le_refl 2) this (by norm_num)
      · have := five_le_of_prime hp hp2 hp3
        exact leaf this (le_refl 2) hr3' (by norm_num)
    · by_cases hr2 : r = 2
      · subst hr2
        have hp3' := h3 h2p hp2
        have hq3' := h3 h2q hq2
        by_cases hp3 : p = 3
        · subst hp3
          have hq5 := five_le_of_prime hq hq2 (Ne.symm hpq)
          exact leaf (le_refl 3) hq5 (le_refl 2) (by norm_num)
        · have hp5 := five_le_of_prime hp hp2 hp3
          exact leaf hp5 hq3' (le_refl 2) (by norm_num)
      · -- none is 2: all ≥ 3; if one is 3 the others are ≥ 5; 3·5·5 ≥ 30
        have hp3' := h3 h2p hp2
        have hq3' := h3 h2q hq2
        have hr3' := h3 h2r hr2
        by_cases hp3 : p = 3
        · subst hp3
          have hq5 := five_le_of_prime hq hq2 (Ne.symm hpq)
          have hr5 := five_le_of_prime hr hr2 (Ne.symm hpr)
          exact leaf (le_refl 3) hq5 hr5 (by norm_num)
        · have hp5 := five_le_of_prime hp hp2 hp3
          exact leaf hp5 hq3' hr3' (by norm_num)

/-- Three pairwise-coprime naturals ≥ 2 multiply to ≥ 30: coprimality forces
distinct minimal prime factors, which land at ≥ {2,3,5}. -/
lemma thirty_le_mul_coprime {d₁ d₂ d₃ : ℕ} (h1 : 2 ≤ d₁) (h2 : 2 ≤ d₂)
    (h3 : 2 ≤ d₃) (c12 : Nat.Coprime d₁ d₂) (c13 : Nat.Coprime d₁ d₃)
    (c23 : Nat.Coprime d₂ d₃) : 30 ≤ d₁ * d₂ * d₃ := by
  have hp1 := Nat.minFac_prime (show d₁ ≠ 1 by omega)
  have hp2 := Nat.minFac_prime (show d₂ ≠ 1 by omega)
  have hp3 := Nat.minFac_prime (show d₃ ≠ 1 by omega)
  have hne : ∀ {u v : ℕ}, 2 ≤ u → Nat.Coprime u v → u.minFac ≠ v.minFac := by
    intro u v hu huv he
    have hd : u.minFac ∣ Nat.gcd u v :=
      Nat.dvd_gcd (Nat.minFac_dvd u) (he ▸ Nat.minFac_dvd v)
    have h1' := Nat.dvd_one.mp (huv.gcd_eq_one ▸ hd)
    have h2' := (Nat.minFac_prime (show u ≠ 1 by omega)).two_le
    omega
  have h30 := thirty_le_prime_triple hp1 hp2 hp3
    (hne h1 c12) (hne h1 c13) (hne h2 c23)
  calc (30 : ℕ) ≤ d₁.minFac * d₂.minFac * d₃.minFac := h30
    _ ≤ d₁ * d₂ * d₃ :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.minFac_le (by omega))
          (Nat.minFac_le (by omega))) (Nat.minFac_le (by omega))

/-- **3.9 (structure of minimal alphabets)**: if `G` (card ≥ 4, positive,
gcd 1) has every single-element erasure non-coprime, then every element is
divisible by three pairwise-coprime factors ≥ 2, hence `≥ 30`. -/
theorem minimal_structure {G : Finset ℕ} (hpos : ∀ g ∈ G, 0 < g)
    (hcard : 4 ≤ G.card) (hgcd : G.gcd id = 1)
    (hmin : ∀ e ∈ G, (G.erase e).gcd id ≠ 1) :
    ∀ g ∈ G, 30 ≤ g := by
  intro g hg
  have hg0 := hpos g hg
  -- three distinct elements ≠ g
  have hce := Finset.card_erase_of_mem hg
  obtain ⟨g₁, hg₁⟩ := Finset.card_pos.mp (by omega : 0 < (G.erase g).card)
  obtain ⟨hg₁g, hg₁G⟩ := Finset.mem_erase.mp hg₁
  have hce₁ := Finset.card_erase_of_mem hg₁
  obtain ⟨g₂, hg₂⟩ := Finset.card_pos.mp
    (by omega : 0 < ((G.erase g).erase g₁).card)
  obtain ⟨hg₂g₁, hg₂'⟩ := Finset.mem_erase.mp hg₂
  obtain ⟨hg₂g, hg₂G⟩ := Finset.mem_erase.mp hg₂'
  have hce₂ := Finset.card_erase_of_mem hg₂
  obtain ⟨g₃, hg₃⟩ := Finset.card_pos.mp
    (by omega : 0 < (((G.erase g).erase g₁).erase g₂).card)
  obtain ⟨hg₃g₂, hg₃'⟩ := Finset.mem_erase.mp hg₃
  obtain ⟨hg₃g₁, hg₃''⟩ := Finset.mem_erase.mp hg₃'
  obtain ⟨hg₃g, hg₃G⟩ := Finset.mem_erase.mp hg₃''
  -- leave-one-out gcds are pairwise coprime
  have key : ∀ u ∈ G, ∀ v ∈ G, u ≠ v →
      Nat.Coprime ((G.erase u).gcd id) ((G.erase v).gcd id) := by
    intro u hu v hv huv
    have hdvd : Nat.gcd ((G.erase u).gcd id) ((G.erase v).gcd id) ∣ G.gcd id := by
      apply Finset.dvd_gcd
      intro x hx
      by_cases hxu : x = u
      · subst hxu
        exact dvd_trans (Nat.gcd_dvd_right _ _)
          (Finset.gcd_dvd (Finset.mem_erase.mpr ⟨huv, hx⟩))
      · exact dvd_trans (Nat.gcd_dvd_left _ _)
          (Finset.gcd_dvd (Finset.mem_erase.mpr ⟨hxu, hx⟩))
    rw [hgcd] at hdvd
    exact Nat.dvd_one.mp hdvd
  -- they are ≥ 2 and divide g
  have hd2 : ∀ u ∈ G, u ≠ g → 2 ≤ (G.erase u).gcd id := by
    intro u hu hug
    have hne1 := hmin u hu
    have hne0 : (G.erase u).gcd id ≠ 0 := by
      intro h0
      have hz := Finset.gcd_eq_zero_iff.mp h0 g
        (Finset.mem_erase.mpr ⟨Ne.symm hug, hg⟩)
      simp only [id] at hz
      omega
    omega
  have hdvdg : ∀ u ∈ G, u ≠ g → (G.erase u).gcd id ∣ g := fun u _ hug =>
    Finset.gcd_dvd (Finset.mem_erase.mpr ⟨Ne.symm hug, hg⟩)
  -- compose
  have h30 := thirty_le_mul_coprime
    (hd2 g₁ hg₁G hg₁g) (hd2 g₂ hg₂G hg₂g) (hd2 g₃ hg₃G hg₃g)
    (key g₁ hg₁G g₂ hg₂G (Ne.symm hg₂g₁))
    (key g₁ hg₁G g₃ hg₃G (Ne.symm hg₃g₁))
    (key g₂ hg₂G g₃ hg₃G (Ne.symm hg₃g₂))
  have p12 := (key g₁ hg₁G g₂ hg₂G (Ne.symm hg₂g₁)).mul_dvd_of_dvd_of_dvd
    (hdvdg g₁ hg₁G hg₁g) (hdvdg g₂ hg₂G hg₂g)
  have c3 : Nat.Coprime ((G.erase g₁).gcd id * (G.erase g₂).gcd id)
      ((G.erase g₃).gcd id) :=
    Nat.Coprime.mul_left (key g₁ hg₁G g₃ hg₃G (Ne.symm hg₃g₁))
      (key g₂ hg₂G g₃ hg₃G (Ne.symm hg₃g₂))
  have p123 := c3.mul_dvd_of_dvd_of_dvd p12 (hdvdg g₃ hg₃G hg₃g)
  exact le_trans h30 (Nat.le_of_dvd hg0 p123)

/-- Scaling transport for subset sums (needed by 3.10's `G'/δ` recursion). -/
theorem subsetSums_map_mul (c : ℕ) (S : Multiset ℕ) :
    subsetSums (S.map (c * ·)) = (subsetSums S).image (c * ·) := by
  induction S using Multiset.induction with
  | empty => simp
  | cons x S ih =>
      rw [Multiset.map_cons, subsetSums_cons, subsetSums_cons, ih,
        Finset.image_union, Finset.image_image, Finset.image_image]
      congr 1
      have hfun : ((c * ·) ∘ (x + ·)) = ((c * x + ·) ∘ (c * ·)) := by
        funext u
        simp only [Function.comp_apply]
        ring
      rw [hfun]

/-- Finset gcd commutes with dividing out a common factor. -/
lemma finset_gcd_image_div {s : Finset ℕ} {c : ℕ}
    (h : ∀ x ∈ s, c ∣ x) : (s.image (· / c)).gcd id * c = s.gcd id := by
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

/-- **3.10's budget inequality, closed by the `≥ 30` bound alone** — the
`δ = 2` corner needs only `M ≥ 8 ≤ 30`, so the `M ≤ 130` minimal-alphabet
enumeration NEVER enters the formal proof. -/
lemma minimal_budget {δ M : ℕ} (hδ : 2 ≤ δ) (h3δ : 3 * δ ≤ M) (h30 : 30 ≤ M) :
    M / δ + 2 * δ - 1 ≤ M - 1 := by
  rcases Nat.eq_or_lt_of_le hδ with hδ2 | hδ3
  · have hδ2' : δ = 2 := hδ2.symm
    subst hδ2'
    omega
  · have h1 : M / δ ≤ M / 3 := Nat.div_le_div_left hδ3 (by omega)
    have h2 : δ ≤ M / 3 := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have h3 : M / 3 * 3 ≤ M := Nat.div_mul_le_self M 3
    omega

/-- Local copy of the Euclid remainder bound (the Staircase one is private). -/
private lemma lt_div_add_one_mul_self' (n : ℕ) {d : ℕ} (hd : 0 < d) :
    n < (n / d + 1) * d := by
  have h1 := Nat.div_add_mod n d
  have h2 := Nat.mod_lt n hd
  have h3 : (n / d + 1) * d = d * (n / d) + d := by ring
  omega

/-- **3.10**: minimal alphabets with `|G| ≥ 4`, by the outer strong induction
(recursing to `max H = M/δ < M` for `H := (G.erase (min G))/δ`), Graham fill
inside `H`, δ-scaling (`subsetSums_map_mul`), and residue bridging with
copies of `min G`; budget closes via `minimal_structure`'s `≥ 30` bound. -/
theorem sharp_of_minimal {M : ℕ} (ih : ∀ M', M' < M → SharpAt M')
    {G : Finset ℕ} (hpos : ∀ g ∈ G, 0 < g) (hcard : 4 ≤ G.card)
    (hgcd : G.gcd id = 1) (hmax : ∀ g ∈ G, g ≤ M) (hM : M ∈ G)
    (hmin : ∀ e ∈ G, (G.erase e).gcd id ≠ 1) :
    ∃ S : Multiset ℕ, (∀ w ∈ S, w ∈ G) ∧ S.card ≤ M - 1 ∧
      HasRun (subsetSums S) M := by
  classical
  have h30 := minimal_structure hpos hcard hgcd hmin
  have hM30 : 30 ≤ M := h30 M hM
  have hM0 : 0 < M := by omega
  -- the minimum a and the rest G'
  have hGne : G.Nonempty := ⟨M, hM⟩
  set a : ℕ := G.min' hGne with hadef
  have haG : a ∈ G := G.min'_mem hGne
  have ha0 : 0 < a := hpos a haG
  have ha_le : ∀ x ∈ G, a ≤ x := fun x hx => G.min'_le x hx
  have ha_lt : ∀ x ∈ G, x ≠ a → a < x := fun x hx hxa =>
    lt_of_le_of_ne (ha_le x hx) (Ne.symm hxa)
  set G' : Finset ℕ := G.erase a with hG'def
  have hG'card : 3 ≤ G'.card := by
    have h := Finset.card_erase_of_mem haG
    rw [← hG'def] at h
    omega
  have hG'sub : ∀ x ∈ G', x ∈ G := fun x hx => Finset.mem_erase.mp hx |>.2
  have hG'ne_a : ∀ x ∈ G', x ≠ a := fun x hx => Finset.mem_erase.mp hx |>.1
  have haM : a < M := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < G'.card)
    have hxG := hG'sub x hx
    have h1 := ha_lt x hxG (hG'ne_a x hx)
    have h2 := hmax x hxG
    -- a < x ≤ M, and if a = M then x > M
    rcases Nat.lt_or_ge a M with h | h
    · exact h
    · have := hmax a haG
      omega
  have hMG' : M ∈ G' := Finset.mem_erase.mpr ⟨by omega, hM⟩
  -- δ and the rescaled alphabet H
  set δ : ℕ := G'.gcd id with hδdef
  have hδdvd : ∀ x ∈ G', δ ∣ x := fun x hx => Finset.gcd_dvd hx
  have hδ2 : 2 ≤ δ := by
    have hne1 : δ ≠ 1 := hmin a haG
    have hne0 : δ ≠ 0 := by
      intro h0
      have hz := Finset.gcd_eq_zero_iff.mp h0 M hMG'
      simp only [id_eq] at hz
      omega
    omega
  have hδ0 : 0 < δ := by omega
  set H : Finset ℕ := G'.image (· / δ) with hHdef
  have hHval : ∀ v ∈ H, δ * v ∈ G' := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    rwa [Nat.mul_div_cancel' (hδdvd x hx)]
  have hHgcd : H.gcd id = 1 := by
    have h1 := finset_gcd_image_div hδdvd
    rw [← hδdef] at h1
    have h2 : H.gcd id * δ = δ := by rw [hHdef, h1, hδdef]
    have := Nat.eq_of_mul_eq_mul_right hδ0 (h2.trans (Nat.one_mul δ).symm)
    exact this
  have hHcard : 3 ≤ H.card := by
    have hinj : Set.InjOn (· / δ) G' := by
      intro x hx y hy hxy
      have hxy' : x / δ = y / δ := hxy
      have hx' := Nat.div_mul_cancel (hδdvd x hx)
      have hy' := Nat.div_mul_cancel (hδdvd y hy)
      have hmul := congrArg (· * δ) hxy'
      omega
    rw [hHdef, Finset.card_image_of_injOn hinj]
    omega
  set M' : ℕ := M / δ with hM'def
  have hδM : δ * M' = M := Nat.mul_div_cancel' (hδdvd M hMG')
  have hM'H : M' ∈ H := Finset.mem_image.mpr ⟨M, hMG', rfl⟩
  have hHle : ∀ v ∈ H, v ≤ M' := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact Nat.div_le_div_right (hmax x (hG'sub x hx))
  have hHpos : ∀ v ∈ H, 0 < v := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact Nat.div_pos (Nat.le_of_dvd (hpos x (hG'sub x hx)) (hδdvd x hx)) hδ0
  have hM'M : M' < M := rescaled_max_lt hδ2 hM0 (le_of_eq hδM)
  have hM'1 : 1 ≤ M' := hHpos M' hM'H
  -- three distinct δ-multiples give 3δ ≤ M
  have h3δ : 3 * δ ≤ M := by
    obtain ⟨x₁, hx₁⟩ := Finset.card_pos.mp (by omega : 0 < H.card)
    obtain ⟨x₂, hx₂⟩ := Finset.card_pos.mp
      (by have := Finset.card_erase_of_mem hx₁; omega : 0 < (H.erase x₁).card)
    obtain ⟨hx₂₁, hx₂H⟩ := Finset.mem_erase.mp hx₂
    obtain ⟨x₃, hx₃⟩ := Finset.card_pos.mp
      (by have := Finset.card_erase_of_mem hx₂
          have := Finset.card_erase_of_mem hx₁
          omega : 0 < ((H.erase x₁).erase x₂).card)
    obtain ⟨hx₃₂, hx₃'⟩ := Finset.mem_erase.mp hx₃
    obtain ⟨hx₃₁, hx₃H⟩ := Finset.mem_erase.mp hx₃'
    have hp1 := hHpos x₁ hx₁
    have hp2 := hHpos x₂ hx₂H
    have hp3 := hHpos x₃ hx₃H
    have hl1 := hHle x₁ hx₁
    have hl2 := hHle x₂ hx₂H
    have hl3 := hHle x₃ hx₃H
    -- among three distinct positives one is ≥ 3
    have hone : 3 ≤ x₁ ∨ 3 ≤ x₂ ∨ 3 ≤ x₃ := by omega
    have hM'3 : 3 ≤ M' := by omega
    calc 3 * δ ≤ M' * δ := Nat.mul_le_mul_right δ hM'3
      _ = M := by rw [Nat.mul_comm]; exact hδM
  -- apply the outer induction at M'
  obtain ⟨SH, hSH_mem, hSH_card, cH, hcH⟩ :=
    ih M' hM'M H hHpos hHcard hHgcd hHle hM'H
  -- fill with copies of a' := min H up to length ℓ
  have hHne : H.Nonempty := ⟨M', hM'H⟩
  set a' : ℕ := H.min' hHne with ha'def
  have ha'H : a' ∈ H := H.min'_mem hHne
  have ha'1 : 1 ≤ a' := hHpos a' ha'H
  have ha'M' : a' ≤ M' := hHle a' ha'H
  have haa' : a + 1 ≤ δ * a' := by
    have h1 := hHval a' ha'H
    have h2 := ha_lt (δ * a') (hG'sub _ h1) (hG'ne_a _ h1)
    omega
  set ℓ : ℕ := (M - 1 + (δ - 1) * a) / δ + 2 with hℓdef
  set t : ℕ := (ℓ - M' + a' - 1) / a' with htdef
  have hfill : HasRun (subsetSums (Multiset.replicate t a' + SH)) (M' + t * a') := by
    clear_value t
    clear htdef
    induction t with
    | zero => simpa using ⟨cH, hcH⟩
    | succ s ihs =>
        have h2 : a' ≤ M' + s * a' := by
          have : 0 ≤ s * a' := Nat.zero_le _
          omega
        have h3 := HasRun.cons_of_le h2 ihs
        have e1 : a' ::ₘ (Multiset.replicate s a' + SH) =
            Multiset.replicate (s + 1) a' + SH := by
          rw [Multiset.replicate_succ, Multiset.cons_add]
        have e2 : M' + s * a' + a' = M' + (s + 1) * a' := by ring
        rwa [e1, e2] at h3
  set L₂ : ℕ := M' + t * a' with hL₂def
  obtain ⟨c₂, hc₂⟩ := hfill
  -- length reached: L₂ ≥ ℓ
  have htℓ : ℓ ≤ L₂ := by
    have h1 := lt_div_add_one_mul_self' (ℓ - M' + a' - 1) ha'1
    rw [← htdef] at h1
    have hexp : (t + 1) * a' = t * a' + a' := by ring
    omega
  -- window arithmetic
  have hwin : M - 1 + (δ - 1) * a + 1 ≤ δ * (L₂ - 1) := by
    have h1 := Nat.div_add_mod (M - 1 + (δ - 1) * a) δ
    have h2 := Nat.mod_lt (M - 1 + (δ - 1) * a) hδ0
    have h3 : δ * (L₂ - 1) = δ * L₂ - δ := by
      have : 1 ≤ L₂ := by omega
      zify [this, show δ ≤ δ * L₂ from Nat.le_mul_of_pos_right δ (by omega)]
      ring
    have h4 : δ * ℓ ≤ δ * L₂ := Nat.mul_le_mul_left δ htℓ
    have h5 : δ * ℓ = δ * ((M - 1 + (δ - 1) * a) / δ) + 2 * δ := by
      rw [hℓdef]; ring
    omega
  -- t is small: t ≤ δ
  have htδ : t ≤ δ := by
    have hdiv : (M - 1 + (δ - 1) * a) / δ < M' + (δ - 1) * a' := by
      rw [Nat.div_lt_iff_lt_mul hδ0]
      have hb1 : (M' + (δ - 1) * a') * δ = M' * δ + (δ - 1) * a' * δ := by ring
      have hb2 : M' * δ = M := by rw [Nat.mul_comm]; exact hδM
      have hb3 : (δ - 1) * a ≤ (δ - 1) * a' * δ - (δ - 1) := by
        have h1 : (δ - 1) * a ≤ (δ - 1) * (δ * a' - 1) :=
          Nat.mul_le_mul_left _ (by omega)
        have h2 : (δ - 1) * (δ * a' - 1) = (δ - 1) * (δ * a') - (δ - 1) := by
          have : 1 ≤ δ * a' := by omega
          zify [this, show (δ-1) ≤ (δ-1) * (δ * a') from
            Nat.le_mul_of_pos_right _ (by omega)]
          ring
        have h3 : (δ - 1) * (δ * a') = (δ - 1) * a' * δ := by ring
        omega
      have hb4 : (δ - 1) ≤ (δ - 1) * a' * δ := by
        calc δ - 1 ≤ (δ - 1) * (a' * δ) :=
              Nat.le_mul_of_pos_right _ (by positivity)
          _ = (δ - 1) * a' * δ := by ring
      omega
    have h1 : ℓ - M' + a' - 1 < (δ + 1) * a' := by
      have hexp : (δ + 1) * a' = δ * a' + a' := by ring
      have h2 : ℓ ≤ M' + (δ - 1) * a' + 1 := by omega
      have h3 : (δ - 1) * a' + a' = δ * a' := by
        have h4 : ((δ - 1) + 1) * a' = (δ - 1) * a' + a' := by ring
        have h5 : (δ - 1) + 1 = δ := by omega
        rw [h5] at h4
        omega
      omega
    have h2 := (Nat.div_lt_iff_lt_mul ha'1).mpr h1
    rw [← htdef] at h2
    omega
  -- coprimality of a and δ
  have hCop : Nat.Coprime a δ := by
    have hdvd : Nat.gcd a δ ∣ G.gcd id := by
      apply Finset.dvd_gcd
      intro x hx
      by_cases hxa : x = a
      · subst hxa
        exact dvd_trans (Nat.gcd_dvd_left _ _) dvd_rfl
      · exact dvd_trans (Nat.gcd_dvd_right _ _)
          (hδdvd x (Finset.mem_erase.mpr ⟨hxa, hx⟩))
    rw [hgcd] at hdvd
    exact Nat.dvd_one.mp hdvd
  -- assemble the witness
  refine ⟨(Multiset.replicate t a' + SH).map (δ * ·) +
    Multiset.replicate (δ - 1) a, ?_, ?_, δ * c₂ + (δ - 1) * a, ?_⟩
  · intro w hw
    rcases Multiset.mem_add.mp hw with hw | hw
    · obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hw
      rcases Multiset.mem_add.mp hv with hv | hv
      · have := Multiset.eq_of_mem_replicate hv
        subst this
        exact hG'sub _ (hHval a' ha'H)
      · exact hG'sub _ (hHval v (hSH_mem v hv))
    · have := Multiset.eq_of_mem_replicate hw
      subst this
      exact haG
  · simp only [Multiset.card_add, Multiset.card_map, Multiset.card_replicate]
    have hbudget := minimal_budget hδ2 h3δ hM30
    rw [← hM'def] at hbudget
    omega
  · intro i hi
    obtain ⟨k, -, hkδ, hres⟩ := exists_frame hδ0 hCop 0
      (δ * c₂ + (δ - 1) * a + i)
    set n : ℕ := δ * c₂ + (δ - 1) * a + i with hndef
    have hkδ' : k ≤ δ - 1 := by omega
    have hka_le : k * a ≤ (δ - 1) * a := Nat.mul_le_mul_right a hkδ'
    have hkan : k * a ≤ n := by omega
    have hdvd : δ ∣ n - k * a := (Nat.modEq_iff_dvd' hkan).mp hres
    set w : ℕ := (n - k * a) / δ with hwdef
    have hw : δ * w = n - k * a := Nat.mul_div_cancel' hdvd
    have hw_lo : c₂ ≤ w := by
      have h1 : δ * c₂ ≤ δ * w := by omega
      exact Nat.le_of_mul_le_mul_left h1 hδ0
    have hw_hi : w < c₂ + L₂ := by
      have h1 : δ * w ≤ δ * c₂ + (δ - 1) * a + M - 1 := by omega
      by_contra hcon
      push Not at hcon
      have h2 : δ * (c₂ + L₂) ≤ δ * w := Nat.mul_le_mul_left δ hcon
      have h3 : δ * (c₂ + L₂) = δ * c₂ + δ * L₂ := by ring
      have h4 : δ * (L₂ - 1) + δ = δ * L₂ := by
        have : 1 ≤ L₂ := by omega
        zify [this, show δ ≤ δ * L₂ from Nat.le_mul_of_pos_right δ (by omega)]
        ring
      omega
    have hw_mem : w ∈ subsetSums (Multiset.replicate t a' + SH) := by
      have h1 : w = c₂ + (w - c₂) := by omega
      rw [h1]
      exact hc₂ (w - c₂) (by omega)
    have hδw : δ * w ∈ subsetSums ((Multiset.replicate t a' + SH).map (δ * ·)) := by
      rw [subsetSums_map_mul]
      exact Finset.mem_image_of_mem _ hw_mem
    have hka : k * a ∈ subsetSums (Multiset.replicate (δ - 1) a) := by
      apply mem_subsetSums.mpr
      refine ⟨Multiset.replicate k a, (Multiset.replicate_le_replicate a).mpr hkδ', ?_⟩
      simp [Multiset.sum_replicate, smul_eq_mul]
    have := add_mem_subsetSums_add hδw hka
    have heq : δ * w + k * a = n := by omega
    rwa [heq] at this

/-- Graham fill, packaged: a run of length `ℓ ≥ a₀` extends by `t` copies of
`a₀` to length `ℓ + t·a₀`. -/
lemma HasRun.add_replicate {S : Multiset ℕ} {ℓ a₀ : ℕ} (ha : a₀ ≤ ℓ)
    (h : HasRun (subsetSums S) ℓ) (t : ℕ) :
    HasRun (subsetSums (Multiset.replicate t a₀ + S)) (ℓ + t * a₀) := by
  induction t with
  | zero => simpa using h
  | succ s ihs =>
      have h2 : a₀ ≤ ℓ + s * a₀ := by
        have : 0 ≤ s * a₀ := Nat.zero_le _
        omega
      have h3 := HasRun.cons_of_le h2 ihs
      have e1 : a₀ ::ₘ (Multiset.replicate s a₀ + S) =
          Multiset.replicate (s + 1) a₀ + S := by
        rw [Multiset.replicate_succ, Multiset.cons_add]
      have e2 : ℓ + s * a₀ + a₀ = ℓ + (s + 1) * a₀ := by ring
      rwa [e1, e2] at h3

/-- **Reduction principle** (Lemmas 3.5–3.10 packaged): if all hard-core
triples at maximum `M` are sharp, and (SHARP) holds at every smaller
maximum, then (SHARP) holds at `M`. Assembly: `1 ∈ G` triviality; redundant
`e ≠ M` by inner card induction; redundant `e = M` by the outer `ih` at the
new maximum plus Graham fill; `|G| = 3` dispatch through L1/L2/L3/hard-core;
`|G| ≥ 4` minimal through `sharp_of_minimal`. -/
theorem sharpAt_of_hardcore (M : ℕ) (ih : ∀ M', M' < M → SharpAt M')
    (hc : ∀ a b, HardCore a b M → SharpTriple a b M) : SharpAt M := by
  classical
  suffices aux : ∀ n (G : Finset ℕ), G.card ≤ n → (∀ g ∈ G, 0 < g) →
      3 ≤ G.card → G.gcd id = 1 → (∀ g ∈ G, g ≤ M) → M ∈ G →
      ∃ S : Multiset ℕ, (∀ w ∈ S, w ∈ G) ∧ S.card ≤ M - 1 ∧
        HasRun (subsetSums S) M by
    intro G hpos hcard hgcd hle hMG
    exact aux G.card G le_rfl hpos hcard hgcd hle hMG
  intro n
  induction n with
  | zero =>
      intro G hcn _ hcard _ _ _
      exfalso
      omega
  | succ n ihn =>
      intro G hcn hpos hcard hgcd hle hMG
      have hM0 : 0 < M := hpos M hMG
      -- trivial case: 1 ∈ G
      by_cases h1G : 1 ∈ G
      · obtain ⟨S, hS1, hSc, hSr⟩ := sharp_of_one_mem M
        exact ⟨S, fun w hw => (hS1 w hw) ▸ h1G, hSc, hSr⟩
      -- redundant element?
      by_cases hred : ∃ e ∈ G, 4 ≤ G.card ∧ (G.erase e).gcd id = 1
      · obtain ⟨e, heG, hc4, hegcd⟩ := hred
        have hcard' : 3 ≤ (G.erase e).card := by
          have h := Finset.card_erase_of_mem heG
          omega
        by_cases heM : e = M
        · -- e = M removable: outer ih at the new maximum, then Graham fill
          rw [heM] at heG hegcd hcard'
          have hne : (G.erase M).Nonempty := Finset.card_pos.mp (by omega)
          set M₂ : ℕ := (G.erase M).max' hne with hM₂def
          have hM₂mem : M₂ ∈ G.erase M := Finset.max'_mem _ hne
          have hM₂G : M₂ ∈ G := (Finset.mem_erase.mp hM₂mem).2
          have hM₂M : M₂ < M :=
            lt_of_le_of_ne (hle M₂ hM₂G) (Finset.mem_erase.mp hM₂mem).1
          obtain ⟨S, hSmem, hScard, hSrun⟩ :=
            ih M₂ hM₂M (G.erase M)
              (fun g hg => hpos g ((Finset.mem_erase.mp hg).2))
              hcard' hegcd
              (fun g hg => Finset.le_max' _ g hg) hM₂mem
          -- fill with M − M₂ copies of the minimum of G.erase M
          set a₀ : ℕ := (G.erase M).min' hne with ha₀def
          have ha₀mem : a₀ ∈ G.erase M := Finset.min'_mem _ hne
          have ha₀G : a₀ ∈ G := (Finset.mem_erase.mp ha₀mem).2
          have ha₀1 : 1 ≤ a₀ := hpos a₀ ha₀G
          have ha₀M₂ : a₀ ≤ M₂ := Finset.le_max' _ a₀ ha₀mem
          obtain ⟨c₀, hc₀⟩ := hSrun
          have hfilled := HasRun.add_replicate ha₀M₂ ⟨c₀, hc₀⟩ (M - M₂)
          refine ⟨Multiset.replicate (M - M₂) a₀ + S, ?_, ?_, ?_⟩
          · intro w hw
            rcases Multiset.mem_add.mp hw with hw | hw
            · exact (Multiset.eq_of_mem_replicate hw) ▸ ha₀G
            · exact (Finset.mem_erase.mp (Finset.mem_coe.mp
                (Finset.mem_coe.mpr (hSmem w hw)))).2
          · simp only [Multiset.card_add, Multiset.card_replicate]
            have hM₂1 : 1 ≤ M₂ := hpos M₂ hM₂G
            omega
          · apply hfilled.of_le
            have h1 : (M - M₂) * 1 ≤ (M - M₂) * a₀ :=
              Nat.mul_le_mul_left _ ha₀1
            omega
        · -- e ≠ M: recurse on the cardinality
          have hMe : M ∈ G.erase e := Finset.mem_erase.mpr ⟨fun h => heM h.symm, hMG⟩
          have hcn' : (G.erase e).card ≤ n := by
            have h := Finset.card_erase_of_mem heG
            omega
          obtain ⟨S, hSmem, hScard, hSrun⟩ :=
            ihn (G.erase e) hcn'
              (fun g hg => hpos g ((Finset.mem_erase.mp hg).2))
              hcard' hegcd
              (fun g hg => hle g ((Finset.mem_erase.mp hg).2)) hMe
          exact ⟨S, fun w hw => (Finset.mem_erase.mp (hSmem w hw)).2, hScard, hSrun⟩
      · -- no redundant element: |G| = 3 dispatch, or |G| ≥ 4 minimal
        push Not at hred
        by_cases hcard3 : G.card = 3
        · -- extract the triple a₀ < b₀ < M
          have hne : (G.erase M).Nonempty := by
            apply Finset.card_pos.mp
            have h := Finset.card_erase_of_mem hMG
            omega
          obtain ⟨x₁, hx₁⟩ := hne
          have hce := Finset.card_erase_of_mem hMG
          obtain ⟨x₂, hx₂⟩ := Finset.card_pos.mp
            (by have := Finset.card_erase_of_mem hx₁; omega :
              0 < ((G.erase M).erase x₁).card)
          obtain ⟨hx₂₁, hx₂'⟩ := Finset.mem_erase.mp hx₂
          obtain ⟨hx₁M, hx₁G⟩ := Finset.mem_erase.mp hx₁
          obtain ⟨hx₂M, hx₂G⟩ := Finset.mem_erase.mp hx₂'
          -- order them
          obtain ⟨a₀, b₀, ha₀G, hb₀G, ha₀M, hb₀M, hab⟩ :
              ∃ a₀ b₀, a₀ ∈ G ∧ b₀ ∈ G ∧ a₀ ≠ M ∧ b₀ ≠ M ∧ a₀ < b₀ := by
            rcases Nat.lt_or_ge x₁ x₂ with h | h
            · exact ⟨x₁, x₂, hx₁G, hx₂G, hx₁M, hx₂M, h⟩
            · have hlt : x₂ < x₁ := lt_of_le_of_ne h hx₂₁
              exact ⟨x₂, x₁, hx₂G, hx₁G, hx₂M, hx₁M, hlt⟩
          have ha₀2 : 2 ≤ a₀ := by
            have h1 := hpos a₀ ha₀G
            rcases Nat.lt_or_ge a₀ 2 with h | h
            · interval_cases a₀
              exact absurd ha₀G h1G
            · exact h
          have hb₀M' : b₀ < M := lt_of_le_of_ne (hle b₀ hb₀G) hb₀M
          -- G = {a₀, b₀, M}
          have hGeq : ({a₀, b₀, M} : Finset ℕ) = G := by
            apply Finset.eq_of_subset_of_card_le
            · intro w hw
              simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl | rfl <;> assumption
            · have h1 : a₀ ∉ ({b₀, M} : Finset ℕ) := by
                simp only [Finset.mem_insert, Finset.mem_singleton]
                push Not
                exact ⟨by omega, ha₀M⟩
              have h2 : b₀ ∉ ({M} : Finset ℕ) := by
                simp only [Finset.mem_singleton]
                exact hb₀M
              have hcard_ins : ({a₀, b₀, M} : Finset ℕ).card = 3 := by
                rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
                  Finset.card_singleton]
              omega
          set d : ℕ := Nat.gcd a₀ b₀ with hddef
          have hd1 : 1 ≤ d := Nat.gcd_pos_of_pos_left _ (by omega)
          rcases Nat.lt_or_ge d 2 with hd1' | hd2
          · -- coprime pair: L1 / L2 / hard-core
            have hco : Nat.Coprime a₀ b₀ := by
              have : d = 1 := by omega
              rw [hddef] at this
              exact this
            rcases Nat.lt_or_ge (a₀ + b₀) M with hsum | hsum
            · -- a₀ + b₀ + 1 ≤ M: L1
              obtain ⟨S, hSel, hSc, hSr⟩ :=
                sharp_of_small_coprime_pair (M := M) (by omega : 0 < a₀)
                  (by omega : 0 < b₀) hco (by omega)
              exact ⟨S, fun w hw => by
                rcases hSel w hw with rfl | rfl <;> assumption, hSc, hSr⟩
            · rcases Nat.lt_or_ge (M + 1) (a₀ + b₀) with hsum2 | hsum2
              · -- a₀ + b₀ ≥ M + 2: hard core
                have hHC : HardCore a₀ b₀ M :=
                  ⟨by omega, hab, hb₀M', hco, by omega⟩
                obtain ⟨S, hSel, hSc, hSr⟩ := hc a₀ b₀ hHC
                exact ⟨S, fun w hw => by
                  rcases hSel w hw with rfl | rfl | rfl <;> assumption, hSc, hSr⟩
              · -- boundary: L2
                obtain ⟨S, hSel, hSc, hSr⟩ :=
                  sharp_of_boundary_pair (M := M) (by omega : 0 < a₀) hab hco
                    (by omega)
                exact ⟨S, fun w hw => by
                  rcases hSel w hw with rfl | rfl <;> assumption, hSc, hSr⟩
          · -- d ≥ 2: L3
            have hdvda := Nat.gcd_dvd_left a₀ b₀
            have hdvdb := Nat.gcd_dvd_right a₀ b₀
            rw [← hddef] at hdvda hdvdb
            have hd0 : 0 < d := by omega
            have hdM : Nat.Coprime M d := by
              have hdvd : Nat.gcd d M ∣ G.gcd id := by
                apply Finset.dvd_gcd
                intro w hw
                rw [← hGeq] at hw
                simp only [Finset.mem_insert, Finset.mem_singleton] at hw
                rcases hw with rfl | rfl | rfl
                · exact dvd_trans (Nat.gcd_dvd_left _ _) hdvda
                · exact dvd_trans (Nat.gcd_dvd_left _ _) hdvdb
                · exact Nat.gcd_dvd_right _ _
              rw [hgcd] at hdvd
              have := Nat.dvd_one.mp hdvd
              rw [Nat.coprime_comm]
              exact this
            have hα0 : 0 < a₀ / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdvda) hd0
            have hαβ : a₀ / d < b₀ / d :=
              Nat.div_lt_div_of_lt_of_dvd hdvdb hab
            have hco' : Nat.Coprime (a₀ / d) (b₀ / d) := by
              rw [hddef]
              exact Nat.coprime_div_gcd_div_gcd (hddef ▸ hd0)
            have hb₀eq : d * (b₀ / d) = b₀ := Nat.mul_div_cancel' hdvdb
            have ha₀eq : d * (a₀ / d) = a₀ := Nat.mul_div_cancel' hdvda
            obtain ⟨S, hSel, hSc, hSr⟩ :=
              sharp_of_noncoprime_pair hd2 hα0 hαβ hco' hdM
                (by rw [hb₀eq]; omega)
            refine ⟨S, fun w hw => ?_, hSc, hSr⟩
            rcases hSel w hw with rfl | rfl | rfl
            · rw [ha₀eq]; exact ha₀G
            · rw [hb₀eq]; exact hb₀G
            · exact hMG
        · -- |G| ≥ 4 and minimal
          exact sharp_of_minimal ih hpos (by omega) hgcd hle hMG
            (fun e he => hred e he (by omega))

end Proof
end Erdos1112
