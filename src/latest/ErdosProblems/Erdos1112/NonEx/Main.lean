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
Non-existence master assembly (the paper's case table): every `(d₁,d₂)`-sequence with
`d₂ ≤ k` is tail-covering; with the certificate (the corresponding paper lemma) this yields the
strong non-existence theorem, statement-identical to the frozen target
`Erdos1112.erdos_1112_strong_nonexistence`.
-/
import ErdosProblems.Erdos1112.NonEx.Certificate
import ErdosProblems.Erdos1112.NonEx.SlotLemma
import ErdosProblems.Erdos1112.NonEx.TwoLetter.Sturmian

namespace Erdos1112
namespace Proof

/-- Prefix-count splits along a shift: `q(T+m) = q T + q_tail m`. -/
private lemma qCount_shift (w : ℕ → Bool) (T m : ℕ) :
    qCount w (T + m) = qCount w T + qCount (fun l => w (T + l)) m := by
  induction m with
  | zero => simp [qCount]
  | succ m ih =>
      have e1 : qCount w (T + (m + 1)) = qCount w (T + m) + (if w (T + m + 1) then 1 else 0) := by
        rw [show T + (m + 1) = (T + m) + 1 from by ring, qCount_succ]
      have e2 : qCount (fun l => w (T + l)) (m + 1)
          = qCount (fun l => w (T + l)) m + (if w (T + m + 1) then 1 else 0) := by
        rw [qCount_succ]; simp only [show T + (m + 1) = T + m + 1 from by ring]
      rw [e1, e2, ih]; ring

/-- A width-two antidiagonal of a tail lifts to one of the whole word. -/
private lemma widthTwo_shift (w : ℕ → Bool) (T σ : ℕ)
    (hW : WidthTwoAt (fun l => w (T + l)) σ) : WidthTwoAt w (2 * T + σ) := by
  obtain ⟨i, j, i', j', hij, hij', hcmp⟩ := hW
  refine ⟨T + i, T + j, T + i', T + j', by omega, by omega, ?_⟩
  have qi := qCount_shift w T i; have qj := qCount_shift w T j
  have qi' := qCount_shift w T i'; have qj' := qCount_shift w T j'
  omega

/-- **Two-letter branch**: a tail alphabet of exactly two letters is
tail-covering. It reduces via `sweep` / `width_of_unbalanced` to the
eventually-periodic case or, through Morse–Hedlund, the Sturmian ladder. The other tail-alphabet
sizes are handled elsewhere (1-letter: single-letter; ≥ 3: Slot Lemma). -/
theorem tailCoveringN_of_two_letters {k d₁ d₂ : ℕ} {a : ℕ → ℕ}
    (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁) (hgaps : HasGapsIn d₁ d₂ a) (hd : d₂ ≤ k)
    (htwo : ∃ x y : ℕ, x < y ∧ tailAlphabet a = {x, y}) :
    TailCoveringN k a := by
  classical
  obtain ⟨x, y, hxy, htwoeq⟩ := htwo
  have hxmem : x ∈ tailAlphabet a := by rw [htwoeq]; left; rfl
  have hymem : y ∈ tailAlphabet a := by rw [htwoeq]; right; rfl
  have hxb := mem_tailAlphabet_bounds hgaps hxmem
  have hyb := mem_tailAlphabet_bounds hgaps hymem
  have hx1 : 1 ≤ x := le_trans hd₁ hxb.1
  have hyd2 : y ≤ d₂ := hyb.2
  set g : ℕ := Nat.gcd x y with hgdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left y (by omega)
  have hgx : g ∣ x := Nat.gcd_dvd_left x y
  have hgy : g ∣ y := Nat.gcd_dvd_right x y
  have hgyx : g ∣ (y - x) := by
    obtain ⟨p, hp⟩ := hgx; obtain ⟨q, hq⟩ := hgy
    exact ⟨q - p, by rw [hp, hq, Nat.mul_sub]⟩
  set δ : ℕ := x / g with hδdef
  set ee : ℕ := (y - x) / g with heedef
  have hδ0 : 0 < δ := Nat.div_pos (Nat.le_of_dvd (by omega) hgx) hg0
  have hee0 : 0 < ee := Nat.div_pos (Nat.le_of_dvd (by omega) hgyx) hg0
  have hxg : x = g * δ := by rw [hδdef, Nat.mul_div_cancel' hgx]
  have hyxg : y - x = g * ee := by rw [heedef, Nat.mul_div_cancel' hgyx]
  have hyg : y = g * (δ + ee) := by rw [Nat.mul_add, ← hxg, ← hyxg]; omega
  have hdd : δ + ee = y / g := by rw [hyg, Nat.mul_div_cancel_left _ hg0]
  have hco : Nat.Coprime δ (δ + ee) := hdd ▸ Nat.coprime_div_gcd_div_gcd hg0
  -- tail index `T ≥ g` past which gaps ∈ {x, y}
  obtain ⟨T0, hT0⟩ := exists_tail_index hgaps
  set T : ℕ := max T0 g with hTdef
  have hgapxy : ∀ n, gap a (T + n) = x ∨ gap a (T + n) = y := by
    intro n
    have hm := hT0 (T + n) (by omega)
    rw [htwoeq] at hm; exact hm
  have hgdvdgap : ∀ n, g ∣ gap a (T + n) := by
    intro n; rcases hgapxy n with h | h
    · rw [h]; exact hgx
    · rw [h]; exact hgy
  have hgapbnd : ∀ n, g * δ ≤ gap a (T + n) ∧ gap a (T + n) ≤ g * (δ + ee) := by
    intro n
    have e1 : g * δ = x := hxg.symm
    have e2 : g * (δ + ee) = y := hyg.symm
    rcases hgapxy n with h | h <;> rw [h, e1, e2] <;> omega
  have haTn : ∀ n, n ≤ a n := by
    intro n; induction n with
    | zero => omega
    | succ n ih =>
        have h1 := hgaps.le_gap n; have h2 := hgaps.succ_eq_add_gap n; omega
  have haTg : g ≤ a T := le_trans (by omega) (haTn T)
  have hdvd : ∀ n, g ∣ (a (T + n) - a T) := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
        have he : T + (n + 1) = (T + n) + 1 := by omega
        have hgm := hgdvdgap n
        have hmono : a T ≤ a (T + n) := hgaps.monotone (by omega)
        have hstep : a (T + (n + 1)) = a (T + n) + gap a (T + n) := by
          rw [he, hgaps.succ_eq_add_gap]
        have : a (T + (n + 1)) - a T = (a (T + n) - a T) + gap a (T + n) := by
          rw [hstep]; omega
        rw [this]; exact Nat.dvd_add ih hgm
  set a' : ℕ → ℕ := fun n => (a (T + n) - a T) / g + 1 with ha'def
  set c : ℕ := a T - g with hcdef
  have haffine : ∀ n, a (T + n) = c + g * a' n := by
    intro n
    have hmono : a T ≤ a (T + n) := hgaps.monotone (by omega)
    have hcancel : g * ((a (T + n) - a T) / g) = a (T + n) - a T := Nat.mul_div_cancel' (hdvd n)
    simp only [ha'def, hcdef, Nat.mul_add, Nat.mul_one, hcancel]
    omega
  have hgap' : ∀ n, gap a' n = gap a (T + n) / g := by
    intro n
    have hd1 := hdvd (n + 1); have hd0 := hdvd n
    obtain ⟨X', hX'⟩ := hd1; obtain ⟨Y', hY'⟩ := hd0
    have hmono0 : a T ≤ a (T + n) := hgaps.monotone (by omega)
    have hmono1 : a (T + n) ≤ a (T + (n + 1)) := hgaps.monotone (by omega)
    have hgm := hgdvdgap n
    have he : T + (n + 1) = (T + n) + 1 := by omega
    have hax : a' (n + 1) = X' + 1 := by
      simp only [ha'def]; rw [hX', Nat.mul_div_cancel_left _ hg0]
    have hay : a' n = Y' + 1 := by
      simp only [ha'def]; rw [hY', Nat.mul_div_cancel_left _ hg0]
    have hYX : Y' ≤ X' := by
      have : g * Y' ≤ g * X' := by omega
      exact Nat.le_of_mul_le_mul_left this hg0
    have hgapval : gap a (T + n) = g * (X' - Y') := by
      change a (T + n + 1) - a (T + n) = g * (X' - Y')
      have h1 : a (T + n + 1) = a (T + (n + 1)) := by rw [he]
      rw [Nat.mul_sub, ← hX', ← hY', h1]; omega
    change a' (n + 1) - a' n = gap a (T + n) / g
    rw [hax, hay, hgapval, Nat.mul_div_cancel_left _ hg0]; omega
  have hmono' : ∀ i, a' i ≤ a' (i + 1) := by
    intro i
    have hm : a (T + i) ≤ a (T + (i + 1)) := hgaps.monotone (by omega)
    have hdiv : (a (T + i) - a T) / g ≤ (a (T + (i + 1)) - a T) / g :=
      Nat.div_le_div_right (Nat.sub_le_sub_right hm _)
    change (a (T + i) - a T) / g + 1 ≤ (a (T + (i + 1)) - a T) / g + 1
    exact Nat.add_le_add_right hdiv 1
  have hgaps' : HasGapsIn δ (δ + ee) a' := by
    refine ⟨by simp only [ha'def]; positivity, fun i => ⟨?_, ?_⟩⟩
    · have hgi := hgap' i
      have hlo : δ ≤ gap a' i := by
        rw [hgi, show δ = g * δ / g from by rw [Nat.mul_div_cancel_left _ hg0]]
        exact Nat.div_le_div_right (hgapbnd i).1
      have hgdef' : gap a' i = a' (i + 1) - a' i := rfl
      have := hmono' i; omega
    · have hgi := hgap' i
      have hhi : gap a' i ≤ δ + ee := by
        rw [hgi, show δ + ee = g * (δ + ee) / g from by rw [Nat.mul_div_cancel_left _ hg0]]
        exact Nat.div_le_div_right (hgapbnd i).2
      have hgdef' : gap a' i = a' (i + 1) - a' i := rfl
      have := hmono' i; omega
  -- the two-letter word of `a'`
  have hval : ∀ n, gap a' n = δ ∨ gap a' n = δ + ee := by
    intro n
    have hgi := hgap' n
    rcases hgapxy n with h | h
    · left; rw [hgi, h, hxg, Nat.mul_div_cancel_left _ hg0]
    · right; rw [hgi, h, hyg, Nat.mul_div_cancel_left _ hg0]
  set h' : ℕ → Bool := fun m => decide (gap a' (m - 1) = δ + ee) with hh'def
  have hgaprel : ∀ n, gap a' n = δ + ee * (if h' (n + 1) then 1 else 0) := by
    intro n
    have hh : h' (n + 1) = decide (gap a' n = δ + ee) := by
      simp only [hh'def, Nat.add_one_sub_one]
    rcases hval n with h | h
    · have hf : h' (n + 1) = false := by
        rw [hh, h]; simp only [decide_eq_false_iff_not]; omega
      rw [hf, h]; simp
    · have ht : h' (n + 1) = true := by rw [hh, h]; simp
      rw [ht, h]; simp
  -- reduce to covering `a'`, then rescale-lift back to `a`
  have hd2'k : δ + ee ≤ k := by
    rw [hdd]; exact le_trans (Nat.div_le_self y g) (le_trans hyd2 hd)
  suffices hcov' : TailCoveringN k a' by
    exact tailCoveringN_of_rescaled T g c hg0 a' haffine hcov'
  by_cases hper : EventuallyPeriodicW h'
  · -- eventually periodic word ⇒ eventually periodic gaps (the corresponding paper lemma)
    apply tailCoveringN_of_eventually_periodic (by omega) hδ0 hgaps'
    obtain ⟨p, hp0, Tp, hTp⟩ := hper
    refine ⟨p, hp0, Tp, fun n hn => ?_⟩
    rw [hgaprel (n + p), hgaprel n, show (n + p) + 1 = (n + 1) + p from by ring,
      hTp (n + 1) (by omega)]
  · by_cases hunbal : ∀ T', ∃ σ, T' ≤ σ ∧ WidthTwoAt h' σ
    · -- unbalanced at unboundedly many antidiagonals ⇒ width ⇒ sweep (2.7–2.9)
      obtain ⟨σ₀, _, hσ₀⟩ := hunbal 0
      obtain ⟨S₀, hS₀⟩ := width_of_unbalanced h' hk hd2'k σ₀ hσ₀ hper hunbal
      exact sweep hk hgaps' h' δ ee hδ0 hee0 hco rfl hgaprel S₀ hS₀
    · -- some tail is balanced ⇒ classify ⇒ mechanical (not periodic) ⇒ Sturmian (2.10)
      have hbaltail : ∃ T₀, BalancedQ (fun m => h' (T₀ + m)) := by
        by_contra hc; push Not at hc
        apply hunbal
        intro N
        have hnb := hc N
        have hex : ∃ σ, WidthTwoAt (fun m => h' (N + m)) σ := by
          by_contra hc2; push Not at hc2
          exact hnb (balancedQ_of_no_widthTwo _ hc2)
        obtain ⟨σ, hσ⟩ := hex
        exact ⟨2 * N + σ, by omega, widthTwo_shift h' N σ hσ⟩
      obtain ⟨T₀, hbT₀⟩ := hbaltail
      rcases balanced_classification (fun m => h' (T₀ + m)) hbT₀ with hpertail | hmechtail
      · -- periodic tail contradicts non-periodicity of `h'`
        exfalso; apply hper
        obtain ⟨p, hp0, Tτ, hTτ⟩ := hpertail
        refine ⟨p, hp0, T₀ + Tτ, fun n hn => ?_⟩
        have hh := hTτ (n - T₀) (by omega)
        simp only [] at hh
        rw [show T₀ + ((n - T₀) + p) = n + p from by omega,
          show T₀ + (n - T₀) = n from by omega] at hh
        exact hh
      · -- mechanical tail ⇒ Sturmian on the tail sequence `a'' = a'(T₂ + ·)`
        obtain ⟨α, β, Tτ, hirr, hαI, hmech⟩ := hmechtail
        set T₂ : ℕ := T₀ + Tτ with hT₂
        set h'' : ℕ → Bool := fun m => h' (T₂ + m) with hh''def
        set a'' : ℕ → ℕ := fun n => a' (T₂ + n) with ha''def
        have ha''0 : 0 < a'' 0 := by simp only [ha''def, ha'def]; positivity
        have hgaps'' : HasGapsIn δ (δ + ee) a'' := by
          refine ⟨ha''0, fun i => ?_⟩
          have hb := hgaps'.2 (T₂ + i)
          simp only [ha''def, show T₂ + (i + 1) = (T₂ + i) + 1 from by ring]
          exact hb
        have hgaprel'' : ∀ n, gap a'' n = δ + ee * (if h'' (n + 1) then 1 else 0) := by
          intro n
          have hgstep : gap a'' n = gap a' (T₂ + n) := by
            simp only [gap, ha''def]; rw [show T₂ + (n + 1) = (T₂ + n) + 1 from by ring]
          have hh'' : h'' (n + 1) = h' ((T₂ + n) + 1) := by
            simp only [hh''def]; rw [show T₂ + (n + 1) = (T₂ + n) + 1 from by ring]
          rw [hgstep, hgaprel (T₂ + n), hh'']
        have hmech'' : ∀ n, (qCount h' (T₂ + n) : ℤ) - qCount h' T₂ = ⌊(n : ℝ) * α + β⌋ := by
          intro n
          have hm := hmech n
          have s1 : qCount h' (T₂ + n)
              = qCount h' T₀ + qCount (fun m => h' (T₀ + m)) (Tτ + n) := by
            have := qCount_shift h' T₀ (Tτ + n)
            rw [show T₀ + (Tτ + n) = T₂ + n from by omega] at this; exact this
          have s2 : qCount h' T₂ = qCount h' T₀ + qCount (fun m => h' (T₀ + m)) Tτ := by
            have := qCount_shift h' T₀ Tτ
            rw [show T₀ + Tτ = T₂ from by omega] at this; exact this
          rw [s1, s2]; push_cast at hm ⊢; linarith [hm]
        have hmechfinal : ∀ n, (qCount h'' n : ℤ) = ⌊(n : ℝ) * α + β⌋ := by
          intro n
          have hsZ : (qCount h' (T₂ + n) : ℤ)
              = qCount h' T₂ + qCount (fun l => h' (T₂ + l)) n := by
            exact_mod_cast qCount_shift h' T₂ n
          have hm'' := hmech'' n
          have : (qCount (fun l => h' (T₂ + l)) n : ℤ) = ⌊(n : ℝ) * α + β⌋ := by omega
          simpa only [hh''def] using this
        have hcovsturm : TailCovering k a'' :=
          tailCovering_of_sturmian hk hgaps'' hd2'k h'' δ ee hδ0 hee0 hco rfl
            hgaprel'' α β hirr hαI hmechfinal
        have halift : ∀ n, a' (T₂ + n) = 0 + 1 * a'' n := by
          intro n; simp [ha''def]
        exact tailCoveringN_of_rescaled T₂ 1 0 one_pos a'' halift hcovsturm

/-- **Non-existence master lemma** (the paper's case table): for `k ≥ 3` and
`d₂ ≤ k`, every admissible `A` is tail-covering. Case on the size of the tail
alphabet `G∞ = {tail letters} ⊆ [d₁, d₂]`: 1 letter (single-letter case),
2 letters (`tailCoveringN_of_two_letters`), ≥ 3 letters (Slot Lemma). -/
theorem all_tailCovering (k d₁ d₂ : ℕ) (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁)
    (h : d₂ ≤ k) :
    ∀ a : ℕ → ℕ, HasGapsIn d₁ d₂ a → TailCoveringN k a := by
  intro a hgaps
  classical
  set G : Finset ℕ := (Finset.Icc d₁ d₂).filter (· ∈ tailAlphabet a) with hGdef
  have hmemG : ∀ x, x ∈ G ↔ x ∈ tailAlphabet a := by
    intro x
    rw [hGdef, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨fun hx => hx.2, fun hx => ⟨mem_tailAlphabet_bounds hgaps hx, hx⟩⟩
  have htaileqG : tailAlphabet a = (↑G : Set ℕ) := by
    ext x; rw [Finset.mem_coe, hmemG]
  obtain ⟨T, hT⟩ := exists_tail_index hgaps
  have hGne : G.Nonempty := ⟨gap a T, (hmemG _).mpr (hT T le_rfl)⟩
  have h1card : 1 ≤ G.card := Finset.card_pos.mpr hGne
  rcases Nat.lt_or_ge G.card 3 with hlt | hge
  · interval_cases hc : G.card
    · -- one letter
      obtain ⟨δ, hδ⟩ := Finset.card_eq_one.mp hc
      refine tailCoveringN_of_single_letter (by omega) hd₁ hgaps ⟨δ, ?_⟩
      rw [htaileqG, hδ, Finset.coe_singleton]
    · -- two letters
      obtain ⟨x, y, hxy, hG2⟩ := Finset.card_eq_two.mp hc
      refine tailCoveringN_of_two_letters hk hd₁ hgaps h
        ⟨min x y, max x y, by omega, ?_⟩
      rw [htaileqG, hG2, Finset.coe_pair]
      rcases le_total x y with hle | hle
      · rw [min_eq_left hle, max_eq_right hle]
      · rw [min_eq_right hle, max_eq_left hle, Set.pair_comm]
  · -- ≥ 3 letters
    have he := G.orderEmbOfFin (rfl : G.card = G.card)
    have hmem : ∀ i : Fin G.card, G.orderEmbOfFin rfl i ∈ tailAlphabet a :=
      fun i => (hmemG _).mp (G.orderEmbOfFin_mem rfl i)
    have hsm : StrictMono (G.orderEmbOfFin (rfl : G.card = G.card)) :=
      (G.orderEmbOfFin rfl).strictMono
    exact tailCovering_of_three_letters hk hd₁ hgaps h
      ⟨_, _, _, hmem ⟨0, by omega⟩, hmem ⟨1, by omega⟩, hmem ⟨2, by omega⟩,
        hsm (by simp [Fin.lt_def]), hsm (by simp [Fin.lt_def])⟩

/-- **Part 2 of the Main Theorem** (strong non-existence). -/
theorem strong_nonexistence (k d₁ d₂ : ℕ) (hk : 3 ≤ k)
    (hd₁ : 1 ≤ d₁) (h : d₂ ≤ k) (R : ℕ → ℕ) :
    ∃ b : ℕ → ℕ, IsVarLacunaryWith R b ∧
      ∀ a : ℕ → ℕ, HasGapsIn d₁ d₂ a →
        ¬ Disjoint (kFoldSumset k a) (Set.range b) :=
  strong_nonexistence_of_tailCovering k d₁ d₂ R
    (all_tailCovering k d₁ d₂ hk hd₁ h)

end Proof
end Erdos1112
