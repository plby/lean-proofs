import ErdosProblems.Erdos587.ResidueTrichotomy
import ErdosProblems.Erdos587.RankTwoSmoothing
import ErdosProblems.Erdos587.NguyenVuSection8

open Filter MeasureTheory
open scoped Pointwise

namespace Erdos587
namespace NVGeneration

/-! ## Quantitative invariants retained at the stopping time

The ordinary stopping certificate deliberately forgets two quantities that
are indispensable in the last Nguyen--Vu iteration: how much of the unused
reserve remains, and the compensation between growth of the common sumset
and the quartering of the number of blocks.  The following certificate keeps
both quantities explicitly. -/

/-- A stopped generation with a lower bound `r` on the reserve remaining
after the terminal `h*m` elements are removed, an upper bound `U` on the
stopping scale, and a lower bound `W` on the scale-sensitive product
`commonCard * m^3`. -/
def RobustStopCertificate {A : Finset ℕ}
    (h c M U r b W : ℕ) : Prop :=
  ∃ generation : NVGeneration A, ∃ m : ℕ, 0 < m ∧ M ≤ m ∧ m ≤ U ∧
  b ≤ generation.commonCard ∧
  r + h * m ≤ generation.reserve.card ∧
  W ≤ generation.commonCard * m ^ 3 ∧
  ∃ choices : List
      (Finset (Fin generation.values.length) × Finset ℕ),
  ∃ nextCard : ℕ,
    generation.values.length = 4 * m ∧
    choices.length = m ∧
    (∀ x ∈ choices,
      x.1.card = 2 ∧ x.2.card = h ∧ x.2 ⊆ generation.reserve) ∧
    choices.Pairwise NVResourceDisjoint ∧
    (nvFirstUsed choices).card = 2 * m ∧
    (nvSecondUsed choices).card = h * m ∧
    2 * h * m ≤ generation.reserve.card ∧
    (∀ p : Finset (Fin generation.values.length), p.card = 2 →
      ∀ T ⊆ generation.reserve, T.card = h →
        Disjoint p (nvFirstUsed choices) →
        Disjoint T (nvSecondUsed choices) →
        (nvStageValue generation.values (p, T)).card ≤ nextCard) ∧
    nextCard ≤ c * generation.commonCard

/-- One stopping stage, with both robust invariants.  The hypothesis
`c ≥ 64` exactly compensates for replacing `m` by `m/4` in a cubic
quantity. -/
theorem exists_robustStopCertificate_or_final
    {A : Finset ℕ} (h c s M U r b W : ℕ)
    (hh : 0 < h) (hc : 64 ≤ c) (hM : 0 < M)
    (G : NVGeneration A)
    (hlen : G.values.length = 4 ^ (s + 1) * M)
    (hcapacity : h * G.values.length ≤ 2 * G.reserve.card)
    (hreserve : 3 * r + h * G.values.length ≤ 3 * G.reserve.card)
    (hb : b ≤ G.commonCard)
    (hupper : 4 ^ s * M ≤ U)
    (hscale : W ≤ G.commonCard * (4 ^ s * M) ^ 3) :
    RobustStopCertificate (A := A) h c M U r b W ∨
      ∃ G' : NVGeneration A,
        G'.values.length = M ∧
        c ^ (s + 1) * G.commonCard ≤ G'.commonCard ∧
        G'.supportBound = iteratedSupportBound h (s + 1) G.supportBound ∧
        h * G'.values.length ≤ 2 * G'.reserve.card := by
  induction s generalizing G with
  | zero =>
      let m := M
      have hm : 0 < m := by simpa [m] using hM
      have hlen4 : G.values.length = 4 * m := by
        simpa [m] using hlen
      have hstageReserve : h * m ≤ G.reserve.card := by
        rw [hlen4] at hcapacity
        nlinarith
      obtain ⟨G₁, cs, hG₁len, hcardMono, hbound, hrescard,
          hcslen, hspec, hpair, hfirst, hsecond, hterminal⟩ :=
        G.exists_next h m hh hm hlen4 hstageReserve
      by_cases hstop : G₁.commonCard ≤ c * G.commonCard
      · left
        have hcap : 2 * h * m ≤ G.reserve.card := by
          rw [hlen4] at hcapacity
          nlinarith
        have hrFinal : r + h * m ≤ G.reserve.card := by
          rw [hlen4] at hreserve
          nlinarith
        exact ⟨G, m, hm, le_rfl, by simpa [m] using hupper,
          hb, hrFinal, by simpa [m] using hscale,
          cs, G₁.commonCard, hlen4, hcslen, hspec, hpair, hfirst,
          hsecond, hcap, hterminal, hstop⟩
      · right
        have hstep : c * G.commonCard ≤ G₁.commonCard := by omega
        have hreserve₁ : h * G₁.values.length ≤
            2 * G₁.reserve.card := by
          have hresEq : G.reserve.card = G₁.reserve.card + h * m := by
            omega
          rw [hG₁len]
          rw [hlen4, hresEq] at hcapacity
          have hlin : 4 * (h * m) ≤
              2 * G₁.reserve.card + 2 * (h * m) := by
            calc
              4 * (h * m) = h * (4 * m) := by ring
              _ ≤ 2 * (G₁.reserve.card + h * m) := hcapacity
              _ = 2 * G₁.reserve.card + 2 * (h * m) := by ring
          omega
        refine ⟨G₁, by simpa [m] using hG₁len, ?_, ?_, hreserve₁⟩
        · simpa using hstep
        · rw [hbound]
          rfl
  | succ s ih =>
      let m := 4 ^ (s + 1) * M
      have hm : 0 < m := by
        dsimp only [m]
        positivity
      have hlen4 : G.values.length = 4 * m := by
        rw [hlen]
        dsimp only [m]
        rw [pow_succ]
        ring
      have hstageReserve : h * m ≤ G.reserve.card := by
        rw [hlen4] at hcapacity
        nlinarith
      obtain ⟨G₁, cs, hG₁len, hcardMono, hbound, hrescard,
          hcslen, hspec, hpair, hfirst, hsecond, hterminal⟩ :=
        G.exists_next h m hh hm hlen4 hstageReserve
      by_cases hstop : G₁.commonCard ≤ c * G.commonCard
      · left
        have hcap : 2 * h * m ≤ G.reserve.card := by
          rw [hlen4] at hcapacity
          nlinarith
        have hrFinal : r + h * m ≤ G.reserve.card := by
          rw [hlen4] at hreserve
          nlinarith
        exact ⟨G, m, hm,
          (show M ≤ 4 ^ (s + 1) * M by
            exact Nat.le_mul_of_pos_left M (by positivity)),
          by simpa [m] using hupper,
          hb, hrFinal, by simpa [m] using hscale,
          cs, G₁.commonCard, hlen4, hcslen, hspec, hpair, hfirst,
          hsecond, hcap, hterminal, hstop⟩
      · have hstep : c * G.commonCard ≤ G₁.commonCard := by omega
        have hcapacity₁ : h * G₁.values.length ≤
            2 * G₁.reserve.card := by
          have hresEq : G.reserve.card = G₁.reserve.card + h * m := by
            omega
          rw [hG₁len]
          rw [hlen4, hresEq] at hcapacity
          have hlin : 4 * (h * m) ≤
              2 * G₁.reserve.card + 2 * (h * m) := by
            calc
              4 * (h * m) = h * (4 * m) := by ring
              _ ≤ 2 * (G₁.reserve.card + h * m) := hcapacity
              _ = 2 * G₁.reserve.card + 2 * (h * m) := by ring
          omega
        have hreserve₁ : 3 * r + h * G₁.values.length ≤
            3 * G₁.reserve.card := by
          have hresEq : G.reserve.card = G₁.reserve.card + h * m := by
            omega
          rw [hG₁len]
          rw [hlen4, hresEq] at hreserve
          have hlin : 3 * r + 4 * (h * m) ≤
              3 * G₁.reserve.card + 3 * (h * m) := by
            calc
              3 * r + 4 * (h * m) = 3 * r + h * (4 * m) := by ring
              _ ≤ 3 * (G₁.reserve.card + h * m) := hreserve
              _ = 3 * G₁.reserve.card + 3 * (h * m) := by ring
          omega
        have hscale₁ : W ≤
            G₁.commonCard * (4 ^ s * M) ^ 3 := by
          calc
            W ≤ G.commonCard * (4 ^ (s + 1) * M) ^ 3 := hscale
            _ = 64 * G.commonCard * (4 ^ s * M) ^ 3 := by
              rw [pow_succ]
              ring
            _ ≤ c * G.commonCard * (4 ^ s * M) ^ 3 := by
              calc
                64 * G.commonCard * (4 ^ s * M) ^ 3 =
                    64 * (G.commonCard * (4 ^ s * M) ^ 3) := by ring
                _ ≤ c * (G.commonCard * (4 ^ s * M) ^ 3) :=
                  Nat.mul_le_mul_right _ hc
                _ = c * G.commonCard * (4 ^ s * M) ^ 3 := by ring
            _ ≤ G₁.commonCard * (4 ^ s * M) ^ 3 :=
              Nat.mul_le_mul_right _ hstep
        have hupper₁ : 4 ^ s * M ≤ U := by
          calc
            4 ^ s * M ≤ 4 ^ (s + 1) * M := by
              exact Nat.mul_le_mul_right M (Nat.pow_le_pow_right (by norm_num) (by omega))
            _ ≤ U := hupper
        rcases ih G₁ (by simpa [m] using hG₁len) hcapacity₁
            hreserve₁ (hb.trans hcardMono) hupper₁ hscale₁ with
          hcert | ⟨G', hG'len, hgrowth, hG'bound, hG'reserve⟩
        · exact Or.inl hcert
        · right
          refine ⟨G', hG'len, ?_, ?_, hG'reserve⟩
          · calc
              c ^ (s + 2) * G.commonCard =
                  c ^ (s + 1) * (c * G.commonCard) := by
                    rw [pow_succ]
                    ring
              _ ≤ c ^ (s + 1) * G₁.commonCard :=
                Nat.mul_le_mul_left _ hstep
              _ ≤ G'.commonCard := hgrowth
          · rw [hG'bound, hbound]
            rfl

/-- The final-growth alternative is impossible once the common-cardinality
growth exceeds the ambient subset-sum interval. -/
theorem exists_robustStopCertificate_of_growth_contradiction
    {A : Finset ℕ} {N : ℕ} (h c s M U r b W : ℕ)
    (hh : 0 < h) (hc : 64 ≤ c) (hM : 0 < M)
    (G : NVGeneration A) (hAN : A ⊆ Finset.Icc 1 N)
    (hlen : G.values.length = 4 ^ (s + 1) * M)
    (hcapacity : h * G.values.length ≤ 2 * G.reserve.card)
    (hreserve : 3 * r + h * G.values.length ≤ 3 * G.reserve.card)
    (hb : b ≤ G.commonCard)
    (hupper : 4 ^ s * M ≤ U)
    (hscale : W ≤ G.commonCard * (4 ^ s * M) ^ 3)
    (hgrowth : iteratedSupportBound h (s + 1) G.supportBound * N + 1 <
      c ^ (s + 1) * G.commonCard) :
    RobustStopCertificate (A := A) h c M U r b W := by
  rcases exists_robustStopCertificate_or_final h c s M U r b W hh hc hM G
      hlen hcapacity hreserve hb hupper hscale with
    hcert | ⟨G', hG'len, hcard, hbound, _hres⟩
  · exact hcert
  · have hne : G'.values ≠ [] := by
      intro hnil
      rw [hnil] at hG'len
      simp at hG'len
      omega
    have hupper := commonCard_le_supportBound_mul G' hAN hne
    rw [hbound] at hupper
    omega

/-- Initialization of the robust stopping recursion from the original set. -/
theorem exists_initial_robustStopCertificate
    {A : Finset ℕ} {N : ℕ} (h c s M r : ℕ)
    (hh : 0 < h) (hc : 64 ≤ c) (hM : 0 < M) (hA2 : 2 ≤ A.card)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hspace :
      64 * (Nat.log 2 A.card + 1) +
          8 * (Nat.log 2 A.card + 1) * (4 ^ (s + 1) * M) ≤ A.card)
    (hhalf :
      16 * (Nat.log 2 A.card + 1) * (4 ^ (s + 1) * M) ≤ A.card)
    (hreserve :
      3 * r + h * (4 ^ (s + 1) * M) ≤
        3 * (A.card -
          8 * (Nat.log 2 A.card + 1) * (4 ^ (s + 1) * M)))
    (hcapacity :
      h * (4 ^ (s + 1) * M) ≤
        2 * (A.card -
          8 * (Nat.log 2 A.card + 1) * (4 ^ (s + 1) * M)))
    (hgrowth :
      iteratedSupportBound h (s + 1) (8 * (Nat.log 2 A.card + 1)) * N + 1 <
        c ^ (s + 1) * (A.card / 2)) :
    RobustStopCertificate (A := A) h c M (4 ^ s * M) r (A.card / 2)
      ((A.card / 2) * (4 ^ s * M) ^ 3) := by
  obtain ⟨G, hGlen, hGcard, hGsupport, hGreserve⟩ :=
    exists_initial (4 ^ (s + 1) * M) hA2 hspace hhalf
  apply exists_robustStopCertificate_of_growth_contradiction
    h c s M (4 ^ s * M) r (A.card / 2)
      ((A.card / 2) * (4 ^ s * M) ^ 3)
    hh hc hM G hAN hGlen
  · rw [hGlen]
    exact hcapacity.trans (Nat.mul_le_mul_left 2 hGreserve)
  · rw [hGlen]
    exact hreserve.trans (Nat.mul_le_mul_left 3 hGreserve)
  · simp [hGcard]
  · exact le_rfl
  · simp [hGcard]
  · simpa [hGcard, hGsupport] using hgrowth

lemma iteratedSupportBound_le_pow_mul (h s L : ℕ) :
    iteratedSupportBound h s L ≤ 2 ^ s * (L + h) := by
  induction s generalizing L with
  | zero =>
      simp [iteratedSupportBound]
  | succ s ih =>
      rw [iteratedSupportBound]
      calc
        iteratedSupportBound h s (2 * L + h) ≤
            2 ^ s * ((2 * L + h) + h) := ih (2 * L + h)
        _ = 2 ^ (s + 1) * (L + h) := by
          rw [pow_succ]
          ring

lemma four_pow_cube (s : ℕ) : (4 ^ s) ^ 3 = 64 ^ s := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

lemma two_pow_six (s : ℕ) : (2 ^ s) ^ 6 = 64 ^ s := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

lemma log_sixty_four_scale_bounds {N : ℕ} (hN : 0 < N) :
    let s := Nat.log 64 N
    64 ^ s ≤ N ∧ N < 64 ^ (s + 1) := by
  dsimp only
  exact ⟨Nat.pow_log_le_self 64 hN.ne',
    Nat.lt_pow_succ_log_self (by norm_num) N⟩

lemma ambient_le_sixty_four_mul_scale_cube {N : ℕ} (hN : 0 < N) :
    let s := Nat.log 64 N
    N ≤ 64 * (4 ^ s) ^ 3 := by
  dsimp only
  have hupper := (log_sixty_four_scale_bounds hN).2.le
  rw [four_pow_cube]
  simpa only [pow_succ, mul_comm] using hupper

/-- Uniform unused-family extraction from a robust stopping certificate.
Besides the ordinary small-doubling conclusions, the output retains the
cubic scale lower bound and the prescribed lower bound on the genuinely
unused remainder `R'`. -/
theorem RobustStopCertificate.exists_uniform_unused_family
    {A : Finset ℕ} {h c M U r b W : ℕ} (hh : 0 < h)
    (H : RobustStopCertificate (A := A) h c M U r b W) :
    ∃ G : NVGeneration A, ∃ m : ℕ, 0 < m ∧ M ≤ m ∧ m ≤ U ∧
      b ≤ G.commonCard ∧
      W ≤ G.commonCard * m ^ 3 ∧
      ∃ J : Finset (Fin G.values.length), ∃ R' : Finset ℕ,
        J.card = 2 * m ∧ R' ⊆ G.reserve ∧
        r ≤ R'.card ∧ h * m ≤ R'.card ∧
        (∀ i ∈ J, (G.values.get i).card = G.commonCard) ∧
        (∀ i ∈ J, ∀ j ∈ J, i ≠ j →
          (G.values.get i + G.values.get j).card ≤
            c * G.commonCard) ∧
        (∀ i ∈ J, ∀ j ∈ J, i ≠ j →
          ∀ T ⊆ R', T.card = h →
            (G.values.get i + G.values.get j + T).card ≤
              c * G.commonCard) := by
  obtain ⟨G, m, hm, hMm, hmU, hb, hrreserve, hW, cs, nextCard, hGlen, hcslen,
      hspec, hpair, hfirst, hsecond, hreserve, hterminal, hstop⟩ := H
  let J : Finset (Fin G.values.length) := Finset.univ \ nvFirstUsed cs
  let R' : Finset ℕ := G.reserve \ nvSecondUsed cs
  have hfirstSub : nvFirstUsed cs ⊆
      (Finset.univ : Finset (Fin G.values.length)) := by simp
  have hsecondSub : nvSecondUsed cs ⊆ G.reserve := by
    intro x hx
    obtain ⟨d, hd, hxd⟩ := mem_nvSecondUsed_iff.mp hx
    exact (hspec d hd).2.2 hxd
  have hJcard : J.card = 2 * m := by
    dsimp only [J]
    rw [Finset.card_sdiff_of_subset hfirstSub, hfirst, hGlen]
    simp
    omega
  have hR'card : R'.card = G.reserve.card - h * m := by
    dsimp only [R']
    rw [Finset.card_sdiff_of_subset hsecondSub, hsecond]
  have hrR' : r ≤ R'.card := by
    rw [hR'card]
    omega
  have hR'large : h * m ≤ R'.card := by
    rw [hR'card]
    apply Nat.le_sub_of_add_le
    calc
      h * m + h * m = 2 * h * m := by ring
      _ ≤ G.reserve.card := hreserve
  have hTchoice : ∃ T ⊆ R', T.card = h := by
    apply Finset.exists_subset_card_eq
    exact (Nat.le_mul_of_pos_right h hm).trans hR'large
  have hterminal' : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      ∀ T ⊆ R', T.card = h →
        (G.values.get i + G.values.get j + T).card ≤
          c * G.commonCard := by
    intro i hiJ j hjJ hij T hTR' hTcard
    have hiUnused : i ∉ nvFirstUsed cs := (Finset.mem_sdiff.mp hiJ).2
    have hjUnused : j ∉ nvFirstUsed cs := (Finset.mem_sdiff.mp hjJ).2
    have hpdis : Disjoint ({i, j} : Finset (Fin G.values.length))
        (nvFirstUsed cs) := by
      rw [Finset.disjoint_left]
      intro x hx hxused
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hiUnused hxused
      · exact hjUnused hxused
    have hTdis : Disjoint T (nvSecondUsed cs) := by
      rw [Finset.disjoint_left]
      intro x hxT hxused
      exact (Finset.mem_sdiff.mp (hTR' hxT)).2 hxused
    have hpCard : ({i, j} : Finset (Fin G.values.length)).card = 2 := by
      simp [hij]
    have hterm := hterminal {i, j} hpCard T
      (hTR'.trans Finset.sdiff_subset) hTcard hpdis hTdis
    rw [nvStageValue_pair i j T hij] at hterm
    exact hterm.trans hstop
  refine ⟨G, m, hm, hMm, hmU, hb, hW, J, R', hJcard, Finset.sdiff_subset,
    hrR', hR'large, ?_, ?_, hterminal'⟩
  · intro i hi
    exact G.value_card _ (List.get_mem _ _)
  · intro i hi j hj hij
    obtain ⟨T, hTR', hTcard⟩ := hTchoice
    have hfull := hterminal' i hi j hj hij T hTR' hTcard
    exact (Finset.card_le_card_add_right
      (Finset.card_pos.mp (by rw [hTcard]; exact hh))).trans hfull

/-! ## Choosing the Section 5.4 scale after stopping

The uniform pattern pigeonhole consumes a number of stopped blocks which is
linear in the desired dyadic scale.  The constant of proportionality depends
only on `c`.  Choosing the scale *after* the stopping time is what allows the
cubic `commonCard * m ^ 3` invariant above to compensate exactly for all
earlier quartering steps. -/

/-- The `c`-dependent coefficient in the linear block count used by the
uniform standardization and budgeted rank reduction. -/
noncomputable def nvRobustBlockFactor (c : ℕ) : ℕ :=
  nvStoppedUniformPatternBound c *
    GeneralizedAP.nvBudgetRankReductionScale (freimanRank (c ^ 2)) *
    nvStoppedDenseCount c

lemma nvStoppedUniformRankBlockCount_eq (c s : ℕ) :
    nvStoppedUniformRankBlockCount c s =
      nvRobustBlockFactor c * 2 ^ s + 1 := by
  simp only [nvStoppedUniformRankBlockCount,
    nvStoppedUniformStandardCount, nvRobustBlockFactor]
  ring

/-- A positive integer `m` which is larger than the fixed block coefficient
has a dyadic scale `2^s` large enough for all required blocks and within a
fixed factor of `m`. -/
lemma exists_robust_dyadic_scale {K m : ℕ} (hKm : K < m) :
    ∃ s : ℕ,
      (K + 1) * 2 ^ s ≤ m ∧
      m < 2 * (K + 1) * 2 ^ s := by
  let u := m / (K + 1)
  have hKpos : 0 < K + 1 := by omega
  have hKle : K + 1 ≤ m := by omega
  have hu : 0 < u := by
    exact Nat.div_pos hKle hKpos
  refine ⟨Nat.log 2 u, ?_, ?_⟩
  · calc
      (K + 1) * 2 ^ Nat.log 2 u ≤ (K + 1) * u :=
        Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 hu.ne')
      _ ≤ m := Nat.mul_div_le m (K + 1)
  · have huUpper : u + 1 ≤ 2 * 2 ^ Nat.log 2 u := by
      have := Nat.lt_pow_succ_log_self Nat.one_lt_two u
      rw [pow_succ] at this
      omega
    calc
      m < m / (K + 1) * (K + 1) + (K + 1) :=
        Nat.lt_div_mul_add hKpos
      _ = (K + 1) * (u + 1) := by
        simp only [u]
        ring
      _ ≤ (K + 1) * (2 * 2 ^ Nat.log 2 u) :=
        Nat.mul_le_mul_left _ huUpper
      _ = 2 * (K + 1) * 2 ^ Nat.log 2 u := by ring

/-- The fixed cubic loss incurred when replacing the stopped block count by
the dyadic Section 5.4 scale. -/
noncomputable def nvRobustCubicLoss (c : ℕ) : ℕ :=
  (2 * (nvRobustBlockFactor c + 1)) ^ 3

lemma nvRobustCubicLoss_pos (c : ℕ) : 0 < nvRobustCubicLoss c := by
  simp only [nvRobustCubicLoss]
  positivity

/-- Robust Nguyen--Vu structural theorem.  Unlike the fixed-scale wrapper in
`NVDevelopment`, this theorem selects the dyadic rank-reduction scale from
the actual stopping time.  Thus the lower bound needed to exclude rank three
is preserved through every successful growth stage.  The prescribed
remainder size `r` is also retained for the later common-divisor iteration. -/
theorem RobustStopCertificate.exists_nguyen_vu_rank_two_structure
    {A : Finset ℕ} {N h c M U r bmin W : ℕ}
    (H : RobustStopCertificate (A := A) h c M U r bmin W)
    (hh : 0 < h) (hc : 1 ≤ c) (hch : c < h)
    (hblocks : nvRobustBlockFactor c < M)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hscale : nvRobustCubicLoss c *
        nvStoppedBudgetScaledCardFactor c * (A.card * N + 1) < W) :
    ∃ s b : ℕ, ∃ G : NVGeneration A, ∃ m : ℕ,
    ∃ J : Finset (Fin G.values.length), ∃ R' : Finset ℕ,
    ∃ i j : Fin G.values.length, ∃ P Q R : GeneralizedAP,
    ∃ d : ℕ, ∃ t : ℤ, ∃ E F Z : Finset ℤ,
      W ≤ nvRobustCubicLoss c * b * (2 ^ s) ^ 3 ∧
      M < 2 * (nvRobustBlockFactor c + 1) * 2 ^ s ∧
      2 ^ s ≤ U ∧
      bmin ≤ b ∧ b ≤ G.commonCard ∧
      M ≤ m ∧ J.card = 2 * m ∧
      R' ⊆ G.reserve ∧ r ≤ R'.card ∧ h * m ≤ R'.card ∧
      i ∈ J ∧ j ∈ J ∧ i ≠ j ∧
      Q.rank = P.rank ∧ Q.base = 0 ∧ Q.Proper ∧ P.Proper ∧
      P.rank ≤ freimanRank (c ^ 2) ∧
      G.commonCard ≤ P.boxCard ∧
      P.boxCard ≤ nvStoppingModelFactor (c ^ 2) 1 * G.commonCard ∧
      natToIntFinset (G.values.get i) -
        natToIntFinset (G.values.get i) ⊆ P.carrier ∧
      Q.boxCard = GeneralizedAP.nvStandardBoxCard P
        (nvStoppedDensity c)
        (nvDenseCount (nvStoppedDensity c) P.rank) ∧
      Q.carrier ⊆
        nvDenseCount (nvStoppedDensity c) P.rank • P.carrier -
          nvDenseCount (nvStoppedDensity c) P.rank • P.carrier ∧
      R.Proper ∧ R.rank ≤ 2 ∧
      (∀ k : Fin R.rank, 0 < R.length k) ∧
      b ≤ nvStoppedBudgetScaledCardFactor c * R.carrier.card ∧
      b * (2 ^ s) ^ R.rank ≤
        nvStoppedBudgetScaledCardFactor c * R.carrier.card ∧
      d ≤ freimanRank (c ^ 2) ∧
      (({t} : Finset ℤ) + R.carrier) +
        natToIntFinset G.reserve.subsetSum ⊆ natToIntFinset A.subsetSum ∧
      E ⊆ natToIntFinset (G.values.get j) ∧ E.card ≤ c ∧
      F ⊆ natToIntFinset R' ∧ F.card < h ∧
      natToIntFinset R' ⊆
        (F + (E - E)) + (P.carrier + P.carrier - P.carrier) ∧
      Z.card ≤ nvStoppedRemainderTranslateCount h c ∧
      natToIntFinset R' ⊆ Z +
        iteratedDifference (d + 3) R.carrier := by
  obtain ⟨G₀, m₀, hm₀, hMm₀, hm₀U, hbmin, hrreserve, hW, choices, nextCard,
      hG₀len, hchoicesLen, hchoiceSpec, hpair, hfirst, hsecond,
      hreserve, hterminal, hstop⟩ := H
  have hfactorM : nvRobustBlockFactor c < m₀ := hblocks.trans_le hMm₀
  obtain ⟨s, hdyadicLower, hdyadicUpper⟩ :=
    exists_robust_dyadic_scale hfactorM
  let b := G₀.commonCard
  have Habove : StopCertificateAbove (A := A) (r := r) h c m₀ b := by
    exact ⟨G₀, le_rfl, m₀, hm₀, le_rfl, choices, nextCard,
      hG₀len, hchoicesLen, hchoiceSpec, hpair, hfirst, hsecond,
      hrreserve, hreserve, hterminal, hstop⟩
  have hblockCount : nvStoppedUniformRankBlockCount c s ≤ 2 * m₀ := by
    rw [nvStoppedUniformRankBlockCount_eq]
    calc
      nvRobustBlockFactor c * 2 ^ s + 1 ≤
          (nvRobustBlockFactor c + 1) * 2 ^ s := by
        have hspos : 0 < 2 ^ s := by positivity
        nlinarith
      _ ≤ m₀ := hdyadicLower
      _ ≤ 2 * m₀ := by omega
  have hmCube : m₀ ^ 3 ≤
      (2 * (nvRobustBlockFactor c + 1) * 2 ^ s) ^ 3 := by
    exact Nat.pow_le_pow_left hdyadicUpper.le 3
  have hWloss : W ≤ nvRobustCubicLoss c * b * (2 ^ s) ^ 3 := by
    calc
      W ≤ b * m₀ ^ 3 := hW
      _ ≤ b * (2 * (nvRobustBlockFactor c + 1) * 2 ^ s) ^ 3 :=
        Nat.mul_le_mul_left b hmCube
      _ = nvRobustCubicLoss c * b * (2 ^ s) ^ 3 := by
        simp only [nvRobustCubicLoss]
        ring
  have hMdyadic : M < 2 * (nvRobustBlockFactor c + 1) * 2 ^ s :=
    hMm₀.trans_lt hdyadicUpper
  have hsU : 2 ^ s ≤ U := by
    calc
      2 ^ s ≤ (nvRobustBlockFactor c + 1) * 2 ^ s := by
        exact Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ m₀ := hdyadicLower
      _ ≤ U := hm₀U
  have hscale' : nvStoppedBudgetScaledCardFactor c *
      (A.card * N + 1) < b * (2 ^ s) ^ 3 := by
    apply (Nat.mul_lt_mul_left (nvRobustCubicLoss_pos c)).mp
    calc
      nvRobustCubicLoss c *
          (nvStoppedBudgetScaledCardFactor c * (A.card * N + 1)) =
          nvRobustCubicLoss c *
            nvStoppedBudgetScaledCardFactor c * (A.card * N + 1) := by ring
      _ < W := hscale
      _ ≤ nvRobustCubicLoss c * b * (2 ^ s) ^ 3 := hWloss
      _ = nvRobustCubicLoss c * (b * (2 ^ s) ^ 3) := by ring
  obtain ⟨G, m, J, R', i, j, P, Q, R, d, t, E, F, Z,
      hbG, hm₀m, hJcard, hR'sub, hR'card, hrR', hiJ, hjJ, hij,
      hQrank, hQbase, hQproper, hPproper, hPrank, hPcommon, hPbox,
      hPdiff, hQbox, hQambient, hRproper, hRrankTwo, hRpos,
      hcommonR, hscaledB, hdRank, hcontainReserve, hEsub, hEcard,
      hFsub, hFcard, hcover, hZcard, hFinalCover⟩ :=
    Habove.exists_nguyen_vu_rank_two_structure hh hc hch hblockCount hAN hscale'
  exact ⟨s, b, G, m, J, R', i, j, P, Q, R, d, t, E, F, Z,
    hWloss, hMdyadic, hsU, hbmin, hbG, hMm₀.trans hm₀m, hJcard, hR'sub,
    hrR', hR'card,
    hiJ, hjJ, hij, hQrank, hQbase, hQproper, hPproper, hPrank,
    hPcommon, hPbox, hPdiff, hQbox, hQambient, hRproper, hRrankTwo,
    hRpos, hcommonR, hscaledB, hdRank, hcontainReserve, hEsub, hEcard,
    hFsub, hFcard, hcover, hZcard, hFinalCover⟩

/-! ## Residue adjustment at the terminal rank -/

/-- A fixed choice of the absolute constant in the repaired Nguyen--Vu
one-variable congruence lemma. -/
noncomputable def nvQuadraticAdjustmentConstant : ℕ :=
  Classical.choose
    exists_quadratic_adjustment_or_large_common_divisor_with_card

lemma nvQuadraticAdjustmentConstant_spec_with_card :
    ∀ {p q r C : ℕ} (A : Finset ℕ),
      0 < p → 0 < q →
      (usedPositiveResidues q A).card ≤ C →
      ((∃ T ⊆ A,
          T.card ≤ C * (Nat.log 2 q *
            (nvQuadraticAdjustmentConstant *
              (Nat.sqrt (p * q) + 1))) ∧
          ∃ z : ℤ,
            ((r + ∑ a ∈ T, a : ℕ) : ℤ) ≡
              (p : ℤ) * z ^ 2 [ZMOD (q : ℤ)]) ∨
        ∃ d : ℕ, ∃ D : Finset ℕ,
          D ⊆ A ∧ 1 < d ∧ d ∣ q ∧
          A.card ≤ D.card +
            C * (Nat.log 2 q *
              (nvQuadraticAdjustmentConstant *
                (Nat.sqrt (p * q) + 1))) ∧
          ∀ a ∈ D, d ∣ a) :=
  Classical.choose_spec
    exists_quadratic_adjustment_or_large_common_divisor_with_card

lemma nvQuadraticAdjustmentConstant_spec :
    ∀ {p q r C : ℕ} (A : Finset ℕ),
      0 < p → 0 < q →
      (usedPositiveResidues q A).card ≤ C →
      ((∃ T ⊆ A, ∃ z : ℤ,
          ((r + ∑ a ∈ T, a : ℕ) : ℤ) ≡
            (p : ℤ) * z ^ 2 [ZMOD (q : ℤ)]) ∨
        ∃ d : ℕ, ∃ D : Finset ℕ,
          D ⊆ A ∧ 1 < d ∧ d ∣ q ∧
          A.card ≤ D.card +
            C * (Nat.log 2 q *
              (nvQuadraticAdjustmentConstant *
                (Nat.sqrt (p * q) + 1))) ∧
          ∀ a ∈ D, d ∣ a) := by
  intro p q r C A hp hq hres
  rcases nvQuadraticAdjustmentConstant_spec_with_card A hp hq hres with
    ⟨T, hTA, _hTcard, z, hz⟩ | hdiv
  · exact Or.inl ⟨T, hTA, z, hz⟩
  · exact Or.inr hdiv

/-- The concrete witness used to terminate the divisor iteration. -/
def HasPMultipleSquareSubsetSum (p : ℕ) (A : Finset ℕ) : Prop :=
  ∃ S ⊆ A, S.Nonempty ∧ ∃ z : ℕ,
    ∑ a ∈ S, a = p * z ^ 2

lemma not_pMultipleSquareSubsetSumFree_iff
    (p : ℕ) (A : Finset ℕ) :
    ¬ PMultipleSquareSubsetSumFree p A ↔
      HasPMultipleSquareSubsetSum p A := by
  constructor
  · intro hn
    by_contra hw
    apply hn
    intro S hSA hSne z hsum
    exact hw ⟨S, hSA, hSne, z, hsum⟩
  · rintro ⟨S, hSA, hSne, z, hsum⟩ hfree
    exact hfree S hSA hSne z hsum

/-- Replace a square root occurring modulo `g` by its least natural residue.
This is the bounded representative used in Nguyen--Vu's rank-two
archimedean argument. -/
lemma normalize_square_base_mod
    {p g r z₀ : ℕ} {t : ℤ} (hg : 0 < g)
    (hbase : (r : ℤ) = (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (g : ℤ)) :
    ∃ z₁ : ℕ, z₁ < g ∧ ∃ t₁ : ℤ,
      (r : ℤ) = (p : ℤ) * (z₁ : ℤ) ^ 2 + t₁ * (g : ℤ) := by
  let z₁ := z₀ % g
  have hz₁ : z₁ < g := Nat.mod_lt _ hg
  have hzmod : z₀ ≡ z₁ [MOD g] := by
    exact Nat.ModEq.symm (Nat.mod_modEq z₀ g)
  have hzmodZ : (z₀ : ℤ) ≡ (z₁ : ℤ) [ZMOD (g : ℤ)] := by
    exact_mod_cast hzmod
  have hsqmod : (p : ℤ) * (z₀ : ℤ) ^ 2 ≡
      (p : ℤ) * (z₁ : ℤ) ^ 2 [ZMOD (g : ℤ)] := by
    exact (hzmodZ.pow 2).mul_left p
  have hrmod : (r : ℤ) ≡
      (p : ℤ) * (z₁ : ℤ) ^ 2 [ZMOD (g : ℤ)] := by
    have hfirst : (r : ℤ) ≡
        (p : ℤ) * (z₀ : ℤ) ^ 2 [ZMOD (g : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      refine ⟨-t, ?_⟩
      rw [hbase]
      ring
    exact hfirst.trans hsqmod
  rw [Int.modEq_iff_dvd] at hrmod
  obtain ⟨t₁, ht₁⟩ := hrmod
  refine ⟨z₁, hz₁, -t₁, ?_⟩
  push_cast at ht₁ ⊢
  linear_combination -ht₁

/-- Rank-one terminal trichotomy.  The bounded translate cover supplies the
bounded set of residues; residue adjustment shifts the whole progression.
If adjustment succeeds, the elementary next-square estimate gives a genuine
`p`-multiple-square subset sum.  Otherwise almost all reserve elements share
a proper divisor of the progression step. -/
theorem rank_one_square_or_common_divisor
    {A B : Finset ℕ} {N p r q L n C : ℕ}
    {R : GeneralizedAP} {t : ℤ} {Z : Finset ℤ}
    (hp : 0 < p) (hq : 0 < q)
    (hAN : A ⊆ Finset.Icc 1 N) (hBA : B ⊆ A)
    (hR : R.Proper) (hrank : R.rank = 1)
    (hside : ∀ i : Fin R.rank, 0 < R.length i)
    (hqstep : (q : ℤ) = R.positiveForm.step
      ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hfamily : ∀ u ∈ B.subsetSum,
      natAP (r + u) q L ⊆ A.subsetSum)
    (hcover : natToIntFinset B ⊆
      Z + iteratedDifference (n + 1) R.carrier)
    (hZ : Z.card ≤ C)
    (hshort : p * q ≤ L)
    (hlong : 4 * (p * q) *
      (Nat.sqrt ((A.card * N) / (p * q ^ 2)) + 1) ≤ L) :
    HasPMultipleSquareSubsetSum p A ∨
      ∃ d : ℕ, ∃ D : Finset ℕ,
        D ⊆ B ∧ 1 < d ∧ d ∣ q ∧
        B.card ≤ D.card +
          C * (Nat.log 2 q *
            (nvQuadraticAdjustmentConstant *
              (Nat.sqrt (p * q) + 1))) ∧
        ∀ a ∈ D, d ∣ a := by
  have hresR : (usedPositiveResidues q B).card ≤ Z.card :=
    usedPositiveResidues_card_le_rank_one R hrank hq hqstep hcover
  have hresC : (usedPositiveResidues q B).card ≤ C := hresR.trans hZ
  rcases nvQuadraticAdjustmentConstant_spec B hp hq hresC with
    hadjust | ⟨d, D, hDB, hd, hdq, hDcard, hdiv⟩
  · left
    obtain ⟨T, hTB, z, hz⟩ := hadjust
    let u := ∑ a ∈ T, a
    have hu : u ∈ B.subsetSum := by
      rw [Finset.mem_subsetSum_iff]
      exact ⟨T, hTB, rfl⟩
    have hAP := hfamily u hu
    let w := z.natAbs
    have hwSq : (w : ℤ) ^ 2 = z ^ 2 := by
      simp [w, sq]
    have hmodInt : ((r + u : ℕ) : ℤ) ≡
        ((p * w ^ 2 : ℕ) : ℤ) [ZMOD (q : ℤ)] := by
      simpa only [u, Nat.cast_mul, Nat.cast_pow, hwSq] using hz
    have hmod : r + u ≡ p * w ^ 2 [MOD q] := by
      exact_mod_cast hmodInt
    have hbaseAP : r + u ∈ natAP (r + u) q L :=
      mem_natAP_iff.mpr ⟨0, by simp, by simp⟩
    have hbaseMem : r + u ∈ A.subsetSum := hAP hbaseAP
    have hbaseUpper : r + u ≤ A.card * N := by
      exact (Finset.mem_Icc.mp
        (NVGeneration.subsetSum_subset_Icc_of_subset
          (U := A) (A := A) Finset.Subset.rfl hAN le_rfl hbaseMem)).2
    have hsqrt : Nat.sqrt ((r + u) / (p * q ^ 2)) ≤
        Nat.sqrt ((A.card * N) / (p * q ^ 2)) := by
      apply Nat.sqrt_le_sqrt
      exact Nat.div_le_div_right hbaseUpper
    have hlong' : 4 * (p * q) *
        (Nat.sqrt ((r + u) / (p * q ^ 2)) + 1) ≤ L :=
      (Nat.mul_le_mul_left (4 * (p * q))
        (Nat.add_le_add_right hsqrt 1)).trans hlong
    obtain ⟨m, hmAP, hmpos, v, hmv⟩ :=
      exists_p_mul_square_mem_natAP_of_modEq
        p q (r + u) L w hp hq hmod hshort hlong'
    have hmSum : m ∈ A.subsetSum := hAP hmAP
    rw [Finset.mem_subsetSum_iff] at hmSum
    obtain ⟨S, hSA, hsum⟩ := hmSum
    refine ⟨S, hSA, ?_, v, ?_⟩
    · apply Finset.nonempty_iff_ne_empty.mpr
      intro hS
      subst S
      simp at hsum
      omega
    · omega
  · exact Or.inr ⟨d, D, hDB, hd, hdq, hDcard, hdiv⟩

/-- The analytic part of the rank-one terminal argument needs only an AP
family and a bound for the reserve residue classes.  This formulation lets
Nguyen--Vu's unbalanced rank-two branch freeze one coordinate and apply the
same argument along the other coordinate. -/
theorem ap_family_square_or_common_divisor_of_residue_bound
    {A B : Finset ℕ} {N p r q L C : ℕ}
    (hp : 0 < p) (hq : 0 < q)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hfamily : ∀ u ∈ B.subsetSum,
      natAP (r + u) q L ⊆ A.subsetSum)
    (hres : (usedPositiveResidues q B).card ≤ C)
    (hshort : p * q ≤ L)
    (hlong : 4 * (p * q) *
      (Nat.sqrt ((A.card * N) / (p * q ^ 2)) + 1) ≤ L) :
    HasPMultipleSquareSubsetSum p A ∨
      ∃ d : ℕ, ∃ D : Finset ℕ,
        D ⊆ B ∧ 1 < d ∧ d ∣ q ∧
        B.card ≤ D.card +
          C * (Nat.log 2 q *
            (nvQuadraticAdjustmentConstant *
              (Nat.sqrt (p * q) + 1))) ∧
        ∀ a ∈ D, d ∣ a := by
  rcases nvQuadraticAdjustmentConstant_spec B hp hq hres with
    hadjust | ⟨d, D, hDB, hd, hdq, hDcard, hdiv⟩
  · left
    obtain ⟨T, hTB, z, hz⟩ := hadjust
    let u := ∑ a ∈ T, a
    have hu : u ∈ B.subsetSum := by
      rw [Finset.mem_subsetSum_iff]
      exact ⟨T, hTB, rfl⟩
    have hAP := hfamily u hu
    let w := z.natAbs
    have hwSq : (w : ℤ) ^ 2 = z ^ 2 := by
      simp [w, sq]
    have hmodInt : ((r + u : ℕ) : ℤ) ≡
        ((p * w ^ 2 : ℕ) : ℤ) [ZMOD (q : ℤ)] := by
      simpa only [u, Nat.cast_mul, Nat.cast_pow, hwSq] using hz
    have hmod : r + u ≡ p * w ^ 2 [MOD q] := by
      exact_mod_cast hmodInt
    have hbaseAP : r + u ∈ natAP (r + u) q L :=
      mem_natAP_iff.mpr ⟨0, by simp, by simp⟩
    have hbaseMem : r + u ∈ A.subsetSum := hAP hbaseAP
    have hbaseUpper : r + u ≤ A.card * N := by
      exact (Finset.mem_Icc.mp
        (NVGeneration.subsetSum_subset_Icc_of_subset
          (U := A) (A := A) Finset.Subset.rfl hAN le_rfl hbaseMem)).2
    have hsqrt : Nat.sqrt ((r + u) / (p * q ^ 2)) ≤
        Nat.sqrt ((A.card * N) / (p * q ^ 2)) := by
      apply Nat.sqrt_le_sqrt
      exact Nat.div_le_div_right hbaseUpper
    have hlong' : 4 * (p * q) *
        (Nat.sqrt ((r + u) / (p * q ^ 2)) + 1) ≤ L :=
      (Nat.mul_le_mul_left (4 * (p * q))
        (Nat.add_le_add_right hsqrt 1)).trans hlong
    obtain ⟨m, hmAP, hmpos, v, hmv⟩ :=
      exists_p_mul_square_mem_natAP_of_modEq
        p q (r + u) L w hp hq hmod hshort hlong'
    have hmSum : m ∈ A.subsetSum := hAP hmAP
    rw [Finset.mem_subsetSum_iff] at hmSum
    obtain ⟨S, hSA, hsum⟩ := hmSum
    refine ⟨S, hSA, ?_, v, ?_⟩
    · apply Finset.nonempty_iff_ne_empty.mpr
      intro hS
      subst S
      simp at hsum
      omega
    · omega
  · exact Or.inr ⟨d, D, hDB, hd, hdq, hDcard, hdiv⟩

/-- Freeze the first coordinate of a rank-two subset-sum family and apply
the AP residue-adjustment argument along its second coordinate. -/
theorem rank_two_second_axis_square_or_common_divisor
    {A B : Finset ℕ} {N p r q₁ q₂ L₁ L₂ C : ℕ}
    (hp : 0 < p) (hq₂ : 0 < q₂)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hfamily : ∀ u ∈ B.subsetSum, ∀ x ≤ L₁, ∀ y ≤ L₂,
      r + u + q₁ * x + q₂ * y ∈ A.subsetSum)
    (hres : (usedPositiveResidues q₂ B).card ≤ C)
    (hshort : p * q₂ ≤ L₂)
    (hlong : 4 * (p * q₂) *
      (Nat.sqrt ((A.card * N) / (p * q₂ ^ 2)) + 1) ≤ L₂) :
    HasPMultipleSquareSubsetSum p A ∨
      ∃ d : ℕ, ∃ D : Finset ℕ,
        D ⊆ B ∧ 1 < d ∧ d ∣ q₂ ∧
        B.card ≤ D.card +
          C * (Nat.log 2 q₂ *
            (nvQuadraticAdjustmentConstant *
              (Nat.sqrt (p * q₂) + 1))) ∧
        ∀ a ∈ D, d ∣ a := by
  apply ap_family_square_or_common_divisor_of_residue_bound
    hp hq₂ hAN (C := C) (L := L₂)
  · intro u hu y hy
    rw [mem_natAP_iff] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    exact hfamily u hu 0 (by omega) j hj
  · exact hres
  · exact hshort
  · exact hlong

/-- Symmetric unbalanced branch along the first coordinate. -/
theorem rank_two_first_axis_square_or_common_divisor
    {A B : Finset ℕ} {N p r q₁ q₂ L₁ L₂ C : ℕ}
    (hp : 0 < p) (hq₁ : 0 < q₁)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hfamily : ∀ u ∈ B.subsetSum, ∀ x ≤ L₁, ∀ y ≤ L₂,
      r + u + q₁ * x + q₂ * y ∈ A.subsetSum)
    (hres : (usedPositiveResidues q₁ B).card ≤ C)
    (hshort : p * q₁ ≤ L₁)
    (hlong : 4 * (p * q₁) *
      (Nat.sqrt ((A.card * N) / (p * q₁ ^ 2)) + 1) ≤ L₁) :
    HasPMultipleSquareSubsetSum p A ∨
      ∃ d : ℕ, ∃ D : Finset ℕ,
        D ⊆ B ∧ 1 < d ∧ d ∣ q₁ ∧
        B.card ≤ D.card +
          C * (Nat.log 2 q₁ *
            (nvQuadraticAdjustmentConstant *
              (Nat.sqrt (p * q₁) + 1))) ∧
        ∀ a ∈ D, d ∣ a := by
  apply ap_family_square_or_common_divisor_of_residue_bound
    hp hq₁ hAN (C := C) (L := L₁)
  · intro u hu x hx
    rw [mem_natAP_iff] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    simpa [add_assoc] using hfamily u hu i hi 0 (by omega)
  · exact hres
  · exact hshort
  · exact hlong

/-- Rank-two residue bridge, separated from the archimedean square-location
estimate.  The hypothesis `hlocate` is precisely the remaining conclusion of
Nguyen--Vu's unbalanced Proposition 7.2 / balanced Proposition 10.1 split.
All residue selection, realization by distinct reserve elements, and the
common-divisor alternative are discharged here. -/
theorem rank_two_square_or_common_divisor_of_locator
    {A B : Finset ℕ} {p r q₁ q₂ L₁ L₂ n C : ℕ}
    {R : GeneralizedAP} {Z : Finset ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hR : R.Proper) (hrank : R.rank = 2)
    (hside : ∀ i : Fin R.rank, 0 < R.length i)
    (hq₁step : (q₁ : ℤ) = R.positiveForm.step
      ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hq₂step : (q₂ : ℤ) = R.positiveForm.step
      ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hfamily : ∀ u ∈ B.subsetSum, ∀ x ≤ L₁, ∀ y ≤ L₂,
      r + u + q₁ * x + q₂ * y ∈ A.subsetSum)
    (hcover : natToIntFinset B ⊆
      Z + iteratedDifference (n + 1) R.carrier)
    (hZ : Z.card ≤ C)
    (hlocate : ∀ u ∈ B.subsetSum, ∀ z₀ : ℕ, ∀ t : ℤ,
      ((r + u : ℕ) : ℤ) =
        (p : ℤ) * (z₀ : ℤ) ^ 2 +
          t * (q₁.gcd q₂ : ℕ) →
      ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
        0 < p * w ^ 2 ∧
        r + u + q₁ * x + q₂ * y = p * w ^ 2) :
    HasPMultipleSquareSubsetSum p A ∨
      ∃ d : ℕ, ∃ D : Finset ℕ,
        D ⊆ B ∧ 1 < d ∧ d ∣ q₁.gcd q₂ ∧
        B.card ≤ D.card +
          C * (Nat.log 2 (q₁.gcd q₂) *
            (nvQuadraticAdjustmentConstant *
              (Nat.sqrt (p * (q₁.gcd q₂)) + 1))) ∧
        ∀ a ∈ D, d ∣ a := by
  let g := q₁.gcd q₂
  have hg : 0 < g := Nat.gcd_pos_of_pos_left q₂ hq₁
  have hresR : (usedPositiveResidues g B).card ≤ Z.card :=
    usedPositiveResidues_card_le_rank_two R hrank hq₁ hq₂
      hq₁step hq₂step hcover
  have hresC : (usedPositiveResidues g B).card ≤ C := hresR.trans hZ
  rcases nvQuadraticAdjustmentConstant_spec B hp hg hresC with
    hadjust | ⟨d, D, hDB, hd, hdg, hDcard, hdiv⟩
  · left
    obtain ⟨T, hTB, z, hz⟩ := hadjust
    let u := ∑ a ∈ T, a
    have hu : u ∈ B.subsetSum := by
      rw [Finset.mem_subsetSum_iff]
      exact ⟨T, hTB, rfl⟩
    let z₀ := z.natAbs
    have hzSq : (z₀ : ℤ) ^ 2 = z ^ 2 := by
      simp [z₀, sq]
    have hz' : ((r + u : ℕ) : ℤ) ≡
        (p : ℤ) * z ^ 2 [ZMOD (g : ℤ)] := by
      simpa only [u, g] using hz
    rw [Int.modEq_iff_dvd] at hz'
    obtain ⟨v, hv⟩ := hz'
    have hbase : ((r + u : ℕ) : ℤ) =
        (p : ℤ) * (z₀ : ℤ) ^ 2 + (-v) * (g : ℕ) := by
      rw [hzSq]
      push_cast at hv ⊢
      linear_combination -hv
    obtain ⟨x, hx, y, hy, w, hwpos, heq⟩ :=
      hlocate u hu z₀ (-v) (by simpa only [g] using hbase)
    have hmSum : p * w ^ 2 ∈ A.subsetSum := by
      rw [← heq]
      exact hfamily u hu x hx y hy
    rw [Finset.mem_subsetSum_iff] at hmSum
    obtain ⟨S, hSA, hsum⟩ := hmSum
    refine ⟨S, hSA, ?_, w, hsum⟩
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hS
    have hzero : ∑ a ∈ S, a = 0 := by simp [hS]
    exact hwpos.ne' (hzero.symm.trans hsum).symm
  · exact Or.inr ⟨d, D, hDB, hd, by simpa only [g] using hdg,
      by simpa only [g] using hDcard, hdiv⟩

/-! ### The unbalanced rank-two locator -/

noncomputable def nvQuadraticStepConstant : ℕ :=
  Classical.choose exists_quadratic_step_uniform

lemma nvQuadraticStepConstant_spec :
    ∀ {g h p : ℕ} {t z₁ : ℤ},
      0 < h → 0 < p →
      ∃ x ≤ nvQuadraticStepConstant * (Nat.sqrt (p * h) + 1),
        ∃ z₂ : ℤ,
          (g : ℤ) * (x : ℤ) + (p : ℤ) * z₁ ^ 2 +
              t * (g.gcd h : ℤ) ≡
            (p : ℤ) * z₂ ^ 2 [ZMOD (h : ℤ)] :=
  Classical.choose_spec exists_quadratic_step_uniform

noncomputable def nvRankTwoUnbalancedConstant : ℕ :=
  Classical.choose exists_p_mul_square_in_rank_two_unbalanced

lemma nvRankTwoUnbalancedConstant_spec :
    ∀ {p d q₁ q₂ r L₁ L₂ z₀ : ℕ} {t : ℤ},
      0 < p → 0 < d → 0 < q₁ → 0 < q₂ → q₁.Coprime q₂ →
      (r : ℤ) = (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (d : ℤ) →
      nvRankTwoUnbalancedConstant *
          (Nat.sqrt (p * (d * q₂)) + 1) ≤ L₁ →
      p * (d * q₂) ≤ L₂ →
      4 * (p * (d * q₂)) *
          (Nat.sqrt ((r + d * q₁ * L₁) /
            (p * (d * q₂) ^ 2)) + 1) ≤ L₂ →
      ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
        0 < p * w ^ 2 ∧
        r + d * q₁ * x + d * q₂ * y = p * w ^ 2 :=
  Classical.choose_spec exists_p_mul_square_in_rank_two_unbalanced

/-- Normalize the two GAP steps by their gcd and apply the unbalanced
Nguyen--Vu locator. -/
lemma rank_two_unbalanced_locator
    {p r u q₁ q₂ L₁ L₂ z₀ : ℕ} {t : ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (hL₁ : nvRankTwoUnbalancedConstant *
        (Nat.sqrt (p * q₂) + 1) ≤ L₁)
    (hshort : p * q₂ ≤ L₂)
    (hlong : 4 * (p * q₂) *
        (Nat.sqrt ((r + u + q₁ * L₁) / (p * q₂ ^ 2)) + 1) ≤ L₂) :
    ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
      0 < p * w ^ 2 ∧
      r + u + q₁ * x + q₂ * y = p * w ^ 2 := by
  let d := q₁.gcd q₂
  let a := q₁ / d
  let b := q₂ / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left q₂ hq₁
  have hda : d * a = q₁ := by
    dsimp only [d, a]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left q₁ q₂)
  have hdb : d * b = q₂ := by
    dsimp only [d, b]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_right q₁ q₂)
  have ha : 0 < a := by
    apply Nat.div_pos
    · exact Nat.le_of_dvd hq₁ (Nat.gcd_dvd_left q₁ q₂)
    · exact hd
  have hb : 0 < b := by
    apply Nat.div_pos
    · exact Nat.le_of_dvd hq₂ (Nat.gcd_dvd_right q₁ q₂)
    · exact hd
  have hab : a.Coprime b := by
    exact Nat.coprime_div_gcd_div_gcd hd
  obtain ⟨x, hx, y, hy, w, hwpos, heq⟩ :=
    nvRankTwoUnbalancedConstant_spec hp hd ha hb hab
      (by simpa only [d] using hbase)
      (by simpa only [hdb] using hL₁)
      (by simpa only [hdb] using hshort)
      (by simpa only [hda, hdb] using hlong)
  refine ⟨x, hx, y, hy, w, hwpos, ?_⟩
  simpa only [hda, hdb] using heq

/-- Ambient-interval form of the unbalanced locator.  The sharpened
`H/(p*q²)` rank-one estimate removes the step size from the leading square
root and leaves the natural condition `L₂² ≫ pH`. -/
lemma rank_two_unbalanced_locator_of_square_side
    {A : Finset ℕ} {N p r u q₁ q₂ L₁ L₂ z₀ : ℕ} {t : ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hfamily : ∀ x ≤ L₁, ∀ y ≤ L₂,
      r + u + q₁ * x + q₂ * y ∈ A.subsetSum)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (hL₂pos : 0 < L₂)
    (hL₁ : nvRankTwoUnbalancedConstant *
      (Nat.sqrt (p * q₂) + 1) ≤ L₁)
    (hbig : 64 * p * (A.card * N) ≤ L₂ ^ 2) :
    ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
      0 < p * w ^ 2 ∧
      r + u + q₁ * x + q₂ * y = p * w ^ 2 := by
  have hsumBound : A.subsetSum ⊆ Finset.Icc 0 (A.card * N) :=
    NVGeneration.subsetSum_subset_Icc_of_subset
      (U := A) (A := A) Finset.Subset.rfl hAN le_rfl
  have hq₂L₂ : q₂ * L₂ ≤ A.card * N := by
    have hend := hfamily 0 (by simp) L₂ le_rfl
    have := (Finset.mem_Icc.mp (hsumBound hend)).2
    omega
  have hpqL : p * q₂ * L₂ ≤ p * (A.card * N) := by
    calc
      p * q₂ * L₂ = p * (q₂ * L₂) := by ring
      _ ≤ p * (A.card * N) := Nat.mul_le_mul_left p hq₂L₂
  have hpqEight : 8 * (p * q₂) ≤ L₂ := by nlinarith
  let v := Nat.sqrt ((A.card * N) / (p * q₂ ^ 2))
  have hvSq : v ^ 2 ≤ (A.card * N) / (p * q₂ ^ 2) := Nat.sqrt_le' _
  have hdenom : p * q₂ ^ 2 * ((A.card * N) / (p * q₂ ^ 2)) ≤
      A.card * N := Nat.mul_div_le _ _
  have hvAmbient : p * q₂ ^ 2 * v ^ 2 ≤ A.card * N :=
    (Nat.mul_le_mul_left (p * q₂ ^ 2) hvSq).trans hdenom
  have hpqvEight : 8 * (p * q₂) * v ≤ L₂ := by nlinarith
  have hshort : p * q₂ ≤ L₂ := by
    calc
      p * q₂ = 1 * (p * q₂) := by simp
      _ ≤ 8 * (p * q₂) := Nat.mul_le_mul_right _ (by norm_num)
      _ ≤ L₂ := hpqEight
  have hlongH : 4 * (p * q₂) *
      (Nat.sqrt ((A.card * N) / (p * q₂ ^ 2)) + 1) ≤ L₂ := by
    dsimp only [v] at hpqvEight ⊢
    nlinarith
  have hbaseUpper : r + u + q₁ * L₁ ≤ A.card * N := by
    have hend := hfamily L₁ le_rfl 0 (by simp)
    have := (Finset.mem_Icc.mp (hsumBound hend)).2
    omega
  have hsqrt : Nat.sqrt ((r + u + q₁ * L₁) / (p * q₂ ^ 2)) ≤
      Nat.sqrt ((A.card * N) / (p * q₂ ^ 2)) := by
    apply Nat.sqrt_le_sqrt
    exact Nat.div_le_div_right hbaseUpper
  have hlong : 4 * (p * q₂) *
      (Nat.sqrt ((r + u + q₁ * L₁) / (p * q₂ ^ 2)) + 1) ≤ L₂ :=
    (Nat.mul_le_mul_left (4 * (p * q₂))
      (Nat.add_le_add_right hsqrt 1)).trans hlongH
  exact rank_two_unbalanced_locator hp hq₁ hq₂ hbase hL₁ hshort hlong

lemma rank_two_unbalanced_locator_of_square_side_symm
    {A : Finset ℕ} {N p r u q₁ q₂ L₁ L₂ z₀ : ℕ} {t : ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hfamily : ∀ x ≤ L₁, ∀ y ≤ L₂,
      r + u + q₁ * x + q₂ * y ∈ A.subsetSum)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (hL₁pos : 0 < L₁)
    (hL₂ : nvRankTwoUnbalancedConstant *
      (Nat.sqrt (p * q₁) + 1) ≤ L₂)
    (hbig : 64 * p * (A.card * N) ≤ L₁ ^ 2) :
    ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
      0 < p * w ^ 2 ∧
      r + u + q₁ * x + q₂ * y = p * w ^ 2 := by
  have hbase' : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₂.gcd q₁ : ℕ) := by
    simpa only [Nat.gcd_comm] using hbase
  obtain ⟨y, hy, x, hx, w, hw, heq⟩ :=
    rank_two_unbalanced_locator_of_square_side hp hq₂ hq₁ hAN
      (fun y hy x hx ↦ by
        have := hfamily x hx y hy
        simpa only [add_assoc, add_left_comm, add_comm] using this)
      hbase' hL₁pos hL₂ hbig
  refine ⟨x, hx, y, hy, w, hw, ?_⟩
  simpa only [add_assoc, add_left_comm, add_comm] using heq

/-! ### The balanced rank-two locator -/

/-- Normalized connector from the finite-convolution smoothing theorem to
Nguyen--Vu's rank-two progression.  All hypotheses below are explicit
finite inequalities; the eventual parameter choice is handled separately. -/
theorem rank_two_balanced_locator_of_smoothing
    {p r u q₁ q₂ L₁ L₂ z₀ X Hx Z₀ L U k M : ℕ} {t : ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (hU : 0 < U) (hL : 0 < L) (hZ₀ : 0 < Z₀)
    (hMhalf : M ≤ (q₂ / q₁.gcd q₂) / 2)
    (hsupport : k * (U - 1) ≤ Hx)
    (hxside : X + Hx ≤ L₁)
    (hstrip : ∀ x z : ℕ,
      X ≤ x → x ≤ X + Hx → Z₀ ≤ z → z < Z₀ + L →
      0 ≤ (p * (q₁.gcd q₂) : ℕ) * (z : ℤ) ^ 2 +
          (2 * p * z₀ : ℕ) * z -
            (q₁ / q₁.gcd q₂ : ℕ) * x - t ∧
      (p * (q₁.gcd q₂) : ℕ) * (z : ℤ) ^ 2 +
          (2 * p * z₀ : ℕ) * z -
            (q₁ / q₁.gcd q₂ : ℕ) * x - t ≤
        (q₂ / q₁.gcd q₂ : ℕ) * L₂)
    (hlow :
      let q₂' := q₂ / q₁.gcd q₂
      let q' := q₂' / (p * q₁.gcd q₂).gcd q₂'
      4 * (M : ℝ) *
          Real.sqrt
            (L + 4 * ((L : ℝ) * M / q' + 1) * L +
              8 * (L + q') * (1 + Real.log q')) < L)
    (hhigh :
      let q₂' := q₂ / q₁.gcd q₂
      2 * (q₂' : ℝ) * ((q₂' : ℝ) / (2 * (M + 1))) ^ k <
        (U : ℝ) ^ k) :
    ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
      0 < p * w ^ 2 ∧
      r + u + q₁ * x + q₂ * y = p * w ^ 2 := by
  let d := q₁.gcd q₂
  let a := q₁ / d
  let b := q₂ / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left q₂ hq₁
  have hda : d * a = q₁ := by
    dsimp only [d, a]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left q₁ q₂)
  have hdb : d * b = q₂ := by
    dsimp only [d, b]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_right q₁ q₂)
  have ha : 0 < a := by
    apply Nat.div_pos
    · exact Nat.le_of_dvd hq₁ (Nat.gcd_dvd_left q₁ q₂)
    · exact hd
  have hb : 0 < b := by
    apply Nat.div_pos
    · exact Nat.le_of_dvd hq₂ (Nat.gcd_dvd_right q₁ q₂)
    · exact hd
  have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd hd
  obtain ⟨x, hx, y, hy, z, hzLower, _hzUpper, heq⟩ :=
    exists_rank_two_quadratic_eq_smoothed
      (a := p * d) (b := 2 * p * z₀) (q₁ := a) (q₂ := b)
      (L₁ := L₁) (L₂ := L₂) (X := X) (Hx := Hx)
      (Z := Z₀) (L := L) (U := U) (k := k) (M := M) (t := t)
      hb hab hU hL
      (by simpa only [b, d] using hMhalf)
      hsupport hxside
      (by simpa only [a, b, d] using hstrip)
      (by simpa only [b, d] using hlow)
      (by simpa only [b, d] using hhigh)
  let w := z₀ + d * z
  have heqNat : r + u + d * a * x + d * b * y = p * w ^ 2 := by
    dsimp only [w]
    apply p_mul_square_eq_rank_two_of_quadratic_eq p d a b (r + u) z₀ z x y t
    · simpa only [d] using hbase
    · simpa only [Nat.cast_mul, Nat.cast_ofNat] using heq
  refine ⟨x, hx, y, hy, w, ?_, ?_⟩
  · have hw : 0 < w := by
      dsimp only [w]
      have hz : 0 < z := hZ₀.trans_le hzLower
      positivity
    exact Nat.mul_pos hp (pow_pos hw 2)
  · simpa only [hda, hdb] using heqNat

/-- Aggregate first-moment version of the balanced rank-two locator.  This
is the direct interface to the corrected Nguyen--Vu averaged Weyl bound. -/
theorem rank_two_balanced_locator_of_aggregate_smoothing
    {p r u q₁ q₂ L₁ L₂ z₀ X Hx Z₀ L U k M : ℕ} {t : ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (hU : 0 < U) (hL : 0 < L) (hZ₀ : 0 < Z₀)
    (hMhalf : M ≤ (q₂ / q₁.gcd q₂) / 2)
    (hsupport : k * (U - 1) ≤ Hx)
    (hxside : X + Hx ≤ L₁)
    (hstrip : ∀ x z : ℕ,
      X ≤ x → x ≤ X + Hx → Z₀ ≤ z → z < Z₀ + L →
      0 ≤ (p * (q₁.gcd q₂) : ℕ) * (z : ℤ) ^ 2 +
          (2 * p * z₀ : ℕ) * z -
            (q₁ / q₁.gcd q₂ : ℕ) * x - t ∧
      (p * (q₁.gcd q₂) : ℕ) * (z : ℤ) ^ 2 +
          (2 * p * z₀ : ℕ) * z -
            (q₁ / q₁.gcd q₂ : ℕ) * x - t ≤
        (q₂ / q₁.gcd q₂ : ℕ) * L₂)
    (hlow :
      let d := q₁.gcd q₂
      let a := q₁ / d
      let b := q₂ / d
      let v : (ZMod b)ˣ := ZMod.unitOfCoprime a
        (Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left q₂ hq₁))
      let A : ℕ := (((v⁻¹ : (ZMod b)ˣ) : ZMod b) * (p * d)).val
      let B : ℕ := (((v⁻¹ : (ZMod b)ˣ) : ZMod b) * (2 * p * z₀)).val
      let g := A.gcd b
      let A' := A / g
      let b' := b / g
      4 * (∑ m ∈ Finset.Icc 1 M,
        ‖quadraticSum
          (((A' * m : ℕ) : ℝ) / b')
          (((m * (2 * A * Z₀ + B) : ℕ) : ℝ) / b) L‖) < L)
    (hhigh :
      let b := q₂ / q₁.gcd q₂
      2 * (b : ℝ) * ((b : ℝ) / (2 * (M + 1))) ^ k <
        (U : ℝ) ^ k) :
    ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
      0 < p * w ^ 2 ∧
      r + u + q₁ * x + q₂ * y = p * w ^ 2 := by
  let d := q₁.gcd q₂
  let a := q₁ / d
  let b := q₂ / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left q₂ hq₁
  have hda : d * a = q₁ := by
    dsimp only [d, a]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left q₁ q₂)
  have hdb : d * b = q₂ := by
    dsimp only [d, b]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_right q₁ q₂)
  have ha : 0 < a := by
    apply Nat.div_pos
    · exact Nat.le_of_dvd hq₁ (Nat.gcd_dvd_left q₁ q₂)
    · exact hd
  have hb : 0 < b := by
    apply Nat.div_pos
    · exact Nat.le_of_dvd hq₂ (Nat.gcd_dvd_right q₁ q₂)
    · exact hd
  have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd hd
  obtain ⟨x, hx, y, hy, z, hzLower, _hzUpper, heq⟩ :=
    exists_rank_two_quadratic_eq_smoothed_of_aggregate_bounds
      (a := p * d) (b := 2 * p * z₀) (q₁ := a) (q₂ := b)
      (L₁ := L₁) (L₂ := L₂) (X := X) (Hx := Hx)
      (Z := Z₀) (L := L) (U := U) (k := k) (M := M) (t := t)
      hb hab hU hL
      (by simpa only [b, d] using hMhalf)
      hsupport hxside
      (by simpa only [a, b, d] using hstrip)
      (by
        simpa only [a, b, d, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hlow)
      (by simpa only [b, d] using hhigh)
  let w := z₀ + d * z
  have heqNat : r + u + d * a * x + d * b * y = p * w ^ 2 := by
    dsimp only [w]
    apply p_mul_square_eq_rank_two_of_quadratic_eq p d a b (r + u) z₀ z x y t
    · simpa only [d] using hbase
    · simpa only [Nat.cast_mul, Nat.cast_ofNat] using heq
  refine ⟨x, hx, y, hy, w, ?_, ?_⟩
  · have hw : 0 < w := by
      dsimp only [w]
      have hz : 0 < z := hZ₀.trans_le hzLower
      positivity
    exact Nat.mul_pos hp (pow_pos hw 2)
  · simpa only [hda, hdb] using heqNat

/-- Endpoint form of the balanced locator.  Monotonicity of the quadratic
turns two endpoint inequalities into the rectangular strip required by the
finite-convolution theorem. -/
theorem rank_two_balanced_locator_of_endpoint_bounds
    {p r u q₁ q₂ L₁ L₂ z₀ X Hx Z L U k M : ℕ} {t : ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (hU : 0 < U) (hL : 0 < L) (hZ : 0 < Z)
    (hMhalf : M ≤ (q₂ / q₁.gcd q₂) / 2)
    (hsupport : k * (U - 1) ≤ Hx)
    (hxside : X + Hx ≤ L₁)
    (hleft : ((q₁ / q₁.gcd q₂) * (X + Hx) : ℕ) + t ≤
      (p * q₁.gcd q₂ : ℕ) * (Z : ℤ) ^ 2 +
        (2 * p * z₀ : ℕ) * Z)
    (hright :
      (p * q₁.gcd q₂ : ℕ) * ((Z + L : ℕ) : ℤ) ^ 2 +
          (2 * p * z₀ : ℕ) * (Z + L) ≤
        ((q₂ / q₁.gcd q₂) * L₂ : ℕ) +
          ((q₁ / q₁.gcd q₂) * X : ℕ) + t)
    (hlow :
      let q₂' := q₂ / q₁.gcd q₂
      let q' := q₂' / (p * q₁.gcd q₂).gcd q₂'
      4 * (M : ℝ) *
          Real.sqrt
            (L + 4 * ((L : ℝ) * M / q' + 1) * L +
              8 * (L + q') * (1 + Real.log q')) < L)
    (hhigh :
      let q₂' := q₂ / q₁.gcd q₂
      2 * (q₂' : ℝ) * ((q₂' : ℝ) / (2 * (M + 1))) ^ k <
        (U : ℝ) ^ k) :
    ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
      0 < p * w ^ 2 ∧
      r + u + q₁ * x + q₂ * y = p * w ^ 2 := by
  apply rank_two_balanced_locator_of_smoothing
      (X := X) (Hx := Hx) (Z₀ := Z) hp hq₁ hq₂ hbase
      hU hL hZ hMhalf hsupport hxside
  · intro x z hx0 hxL hzZ hzUpper
    have hx : x ≤ X + Hx := hxL
    have hz : Z ≤ z := hzZ
    have hz' : z ≤ Z + L := hzUpper.le
    have hquadLower :
        (p * q₁.gcd q₂ : ℕ) * (Z : ℤ) ^ 2 +
            (2 * p * z₀ : ℕ) * Z ≤
          (p * q₁.gcd q₂ : ℕ) * (z : ℤ) ^ 2 +
            (2 * p * z₀ : ℕ) * z := by
      have hzInt : (Z : ℤ) ≤ (z : ℤ) := by exact_mod_cast hz
      have hzSq : (Z : ℤ) ^ 2 ≤ (z : ℤ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hzInt 2
      gcongr
    have hquadUpper :
        (p * q₁.gcd q₂ : ℕ) * (z : ℤ) ^ 2 +
            (2 * p * z₀ : ℕ) * z ≤
          (p * q₁.gcd q₂ : ℕ) * ((Z + L : ℕ) : ℤ) ^ 2 +
            (2 * p * z₀ : ℕ) * (Z + L) := by
      have hzInt : (z : ℤ) ≤ ((Z + L : ℕ) : ℤ) := by exact_mod_cast hz'
      have hzSq : (z : ℤ) ^ 2 ≤ ((Z + L : ℕ) : ℤ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hzInt 2
      gcongr
      norm_num only [Nat.cast_add] at hzInt ⊢
      exact hzInt
    constructor
    · have hxcast : (x : ℤ) ≤ X + Hx := by exact_mod_cast hx
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hquadLower hleft ⊢
      nlinarith
    · have hxlower : (X : ℤ) ≤ x := by exact_mod_cast hx0
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hquadUpper hright ⊢
      nlinarith
  · exact hlow
  · exact hhigh

/-- The two endpoint inequalities imply the full quadratic strip throughout
the rectangle.  This geometric fact is shared by the reduced-period and
finite-smoothing branches. -/
lemma rank_two_quadratic_strip_of_endpoint_bounds
    {p q₁ q₂ L₁ L₂ z₀ X Hx Z L : ℕ} {t : ℤ}
    (hxside : X + Hx ≤ L₁)
    (hleft : ((q₁ / q₁.gcd q₂) * (X + Hx) : ℕ) + t ≤
      (p * q₁.gcd q₂ : ℕ) * (Z : ℤ) ^ 2 +
        (2 * p * z₀ : ℕ) * Z)
    (hright :
      (p * q₁.gcd q₂ : ℕ) * ((Z + L : ℕ) : ℤ) ^ 2 +
          (2 * p * z₀ : ℕ) * (Z + L) ≤
        ((q₂ / q₁.gcd q₂) * L₂ : ℕ) +
          ((q₁ / q₁.gcd q₂) * X : ℕ) + t) :
    ∀ x z : ℕ, X ≤ x → x ≤ X + Hx → Z ≤ z → z ≤ Z + L →
      0 ≤ (p * q₁.gcd q₂ : ℕ) * (z : ℤ) ^ 2 +
          (2 * p * z₀ : ℕ) * z -
          (q₁ / q₁.gcd q₂ : ℕ) * x - t ∧
      (p * q₁.gcd q₂ : ℕ) * (z : ℤ) ^ 2 +
          (2 * p * z₀ : ℕ) * z -
          (q₁ / q₁.gcd q₂ : ℕ) * x - t ≤
        (q₂ / q₁.gcd q₂ : ℕ) * L₂ := by
  intro x z hx0 hxL hzZ hzUpper
  have hx : x ≤ X + Hx := hxL
  have hz : Z ≤ z := hzZ
  have hquadLower :
      (p * q₁.gcd q₂ : ℕ) * (Z : ℤ) ^ 2 +
          (2 * p * z₀ : ℕ) * Z ≤
        (p * q₁.gcd q₂ : ℕ) * (z : ℤ) ^ 2 +
          (2 * p * z₀ : ℕ) * z := by
    have hzInt : (Z : ℤ) ≤ (z : ℤ) := by exact_mod_cast hz
    have hzSq : (Z : ℤ) ^ 2 ≤ (z : ℤ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hzInt 2
    gcongr
  have hquadUpper :
      (p * q₁.gcd q₂ : ℕ) * (z : ℤ) ^ 2 +
          (2 * p * z₀ : ℕ) * z ≤
        (p * q₁.gcd q₂ : ℕ) * ((Z + L : ℕ) : ℤ) ^ 2 +
          (2 * p * z₀ : ℕ) * (Z + L) := by
    have hzInt : (z : ℤ) ≤ ((Z + L : ℕ) : ℤ) := by
      exact_mod_cast hzUpper
    have hzSq : (z : ℤ) ^ 2 ≤ ((Z + L : ℕ) : ℤ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hzInt 2
    gcongr
    norm_num only [Nat.cast_add] at hzInt ⊢
    exact hzInt
  constructor
  · have hxcast : (x : ℤ) ≤ X + Hx := by exact_mod_cast hx
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      at hquadLower hleft ⊢
    nlinarith
  · have hxlower : (X : ℤ) ≤ x := by exact_mod_cast hx0
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      at hquadUpper hright ⊢
    nlinarith

/-- Endpoint form of the aggregate first-moment balanced locator. -/
theorem rank_two_balanced_locator_of_aggregate_endpoint_bounds
    {p r u q₁ q₂ L₁ L₂ z₀ X Hx Z L U k M : ℕ} {t : ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (hU : 0 < U) (hL : 0 < L) (hZ : 0 < Z)
    (hMhalf : M ≤ (q₂ / q₁.gcd q₂) / 2)
    (hsupport : k * (U - 1) ≤ Hx)
    (hxside : X + Hx ≤ L₁)
    (hleft : ((q₁ / q₁.gcd q₂) * (X + Hx) : ℕ) + t ≤
      (p * q₁.gcd q₂ : ℕ) * (Z : ℤ) ^ 2 +
        (2 * p * z₀ : ℕ) * Z)
    (hright :
      (p * q₁.gcd q₂ : ℕ) * ((Z + L : ℕ) : ℤ) ^ 2 +
          (2 * p * z₀ : ℕ) * (Z + L) ≤
        ((q₂ / q₁.gcd q₂) * L₂ : ℕ) +
          ((q₁ / q₁.gcd q₂) * X : ℕ) + t)
    (hlow :
      let d := q₁.gcd q₂
      let a := q₁ / d
      let b := q₂ / d
      let v : (ZMod b)ˣ := ZMod.unitOfCoprime a
        (Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left q₂ hq₁))
      let A : ℕ := (((v⁻¹ : (ZMod b)ˣ) : ZMod b) * (p * d)).val
      let B : ℕ := (((v⁻¹ : (ZMod b)ˣ) : ZMod b) * (2 * p * z₀)).val
      let g := A.gcd b
      let A' := A / g
      let b' := b / g
      4 * (∑ m ∈ Finset.Icc 1 M,
        ‖quadraticSum
          (((A' * m : ℕ) : ℝ) / b')
          (((m * (2 * A * Z + B) : ℕ) : ℝ) / b) L‖) < L)
    (hhigh :
      let b := q₂ / q₁.gcd q₂
      2 * (b : ℝ) * ((b : ℝ) / (2 * (M + 1))) ^ k <
        (U : ℝ) ^ k) :
    ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
      0 < p * w ^ 2 ∧
      r + u + q₁ * x + q₂ * y = p * w ^ 2 := by
  apply rank_two_balanced_locator_of_aggregate_smoothing
      (X := X) (Hx := Hx) (Z₀ := Z) hp hq₁ hq₂ hbase
      hU hL hZ hMhalf hsupport hxside
  · intro x z hx0 hxL hzZ hzUpper
    have hx : x ≤ X + Hx := hxL
    have hz : Z ≤ z := hzZ
    have hz' : z ≤ Z + L := hzUpper.le
    have hquadLower :
        (p * q₁.gcd q₂ : ℕ) * (Z : ℤ) ^ 2 +
            (2 * p * z₀ : ℕ) * Z ≤
          (p * q₁.gcd q₂ : ℕ) * (z : ℤ) ^ 2 +
            (2 * p * z₀ : ℕ) * z := by
      have hzInt : (Z : ℤ) ≤ (z : ℤ) := by exact_mod_cast hz
      have hzSq : (Z : ℤ) ^ 2 ≤ (z : ℤ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hzInt 2
      gcongr
    have hquadUpper :
        (p * q₁.gcd q₂ : ℕ) * (z : ℤ) ^ 2 +
            (2 * p * z₀ : ℕ) * z ≤
          (p * q₁.gcd q₂ : ℕ) * ((Z + L : ℕ) : ℤ) ^ 2 +
            (2 * p * z₀ : ℕ) * (Z + L) := by
      have hzInt : (z : ℤ) ≤ ((Z + L : ℕ) : ℤ) := by exact_mod_cast hz'
      have hzSq : (z : ℤ) ^ 2 ≤ ((Z + L : ℕ) : ℤ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hzInt 2
      gcongr
      norm_num only [Nat.cast_add] at hzInt ⊢
      exact hzInt
    constructor
    · have hxcast : (x : ℤ) ≤ X + Hx := by exact_mod_cast hx
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
        at hquadLower hleft ⊢
      nlinarith
    · have hxlower : (X : ℤ) ≤ x := by exact_mod_cast hx0
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
        at hquadUpper hright ⊢
      nlinarith
  · exact hlow
  · exact hhigh

/-- Finite data certifying the balanced Nguyen--Vu rectangle. -/
def RankTwoBalancedEndpointData
    (p q₁ q₂ L₁ L₂ z₀ : ℕ) (t : ℤ) : Prop :=
  ∃ X Hx Z L U k M : ℕ,
    0 < U ∧ 0 < L ∧ 0 < Z ∧
    M ≤ (q₂ / q₁.gcd q₂) / 2 ∧
    k * (U - 1) ≤ Hx ∧ X + Hx ≤ L₁ ∧
    ((q₁ / q₁.gcd q₂) * (X + Hx) : ℕ) + t ≤
      (p * q₁.gcd q₂ : ℕ) * (Z : ℤ) ^ 2 +
        (2 * p * z₀ : ℕ) * Z ∧
    (p * q₁.gcd q₂ : ℕ) * ((Z + L : ℕ) : ℤ) ^ 2 +
        (2 * p * z₀ : ℕ) * (Z + L) ≤
      ((q₂ / q₁.gcd q₂) * L₂ : ℕ) +
        ((q₁ / q₁.gcd q₂) * X : ℕ) + t ∧
    (let q₂' := q₂ / q₁.gcd q₂
     let q' := q₂' / (p * q₁.gcd q₂).gcd q₂'
     4 * (M : ℝ) *
        Real.sqrt
          (L + 4 * ((L : ℝ) * M / q' + 1) * L +
            8 * (L + q') * (1 + Real.log q')) < L) ∧
    (let q₂' := q₂ / q₁.gcd q₂
     2 * (q₂' : ℝ) * ((q₂' : ℝ) / (2 * (M + 1))) ^ k <
       (U : ℝ) ^ k)

theorem rank_two_balanced_locator_of_endpoint_data
    {p r u q₁ q₂ L₁ L₂ z₀ : ℕ} {t : ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (hdata : RankTwoBalancedEndpointData p q₁ q₂ L₁ L₂ z₀ t) :
    ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
      0 < p * w ^ 2 ∧
      r + u + q₁ * x + q₂ * y = p * w ^ 2 := by
  rcases hdata with
    ⟨X, Hx, Z, L, U, k, M, hU, hL, hZ, hM, hsupport, hxside,
      hleft, hright, hlow, hhigh⟩
  exact rank_two_balanced_locator_of_endpoint_bounds hp hq₁ hq₂
    hbase hU hL hZ hM hsupport hxside hleft hright hlow hhigh

theorem rank_two_balanced_locator_of_endpoint_data_symm
    {p r u q₁ q₂ L₁ L₂ z₀ : ℕ} {t : ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (hdata : RankTwoBalancedEndpointData p q₂ q₁ L₂ L₁ z₀ t) :
    ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
      0 < p * w ^ 2 ∧
      r + u + q₁ * x + q₂ * y = p * w ^ 2 := by
  have hbase' : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₂.gcd q₁ : ℕ) := by
    simpa only [Nat.gcd_comm] using hbase
  obtain ⟨y, hy, x, hx, w, hw, heq⟩ :=
    rank_two_balanced_locator_of_endpoint_data hp hq₂ hq₁ hbase' hdata
  refine ⟨x, hx, y, hy, w, hw, ?_⟩
  simpa only [add_assoc, add_left_comm, add_comm] using heq

/-- Balanced endpoint data whose low-frequency field is the corrected
aggregate first moment.  The proof `hq₁` is an explicit parameter only
because the canonical inverse of `q₁ / gcd q₁ q₂` is used in the data; by
proof irrelevance the proposition does not depend on its choice. -/
def RankTwoBalancedAggregateEndpointData
    (p q₁ q₂ L₁ L₂ z₀ : ℕ) (hq₁ : 0 < q₁) (t : ℤ) : Prop :=
  ∃ X Hx Z L U k M : ℕ,
    0 < U ∧ 0 < L ∧ 0 < Z ∧
    M ≤ (q₂ / q₁.gcd q₂) / 2 ∧
    k * (U - 1) ≤ Hx ∧ X + Hx ≤ L₁ ∧
    ((q₁ / q₁.gcd q₂) * (X + Hx) : ℕ) + t ≤
      (p * q₁.gcd q₂ : ℕ) * (Z : ℤ) ^ 2 +
        (2 * p * z₀ : ℕ) * Z ∧
    (p * q₁.gcd q₂ : ℕ) * ((Z + L : ℕ) : ℤ) ^ 2 +
        (2 * p * z₀ : ℕ) * (Z + L) ≤
      ((q₂ / q₁.gcd q₂) * L₂ : ℕ) +
        ((q₁ / q₁.gcd q₂) * X : ℕ) + t ∧
    (let d := q₁.gcd q₂
     let a := q₁ / d
     let b := q₂ / d
     let v : (ZMod b)ˣ := ZMod.unitOfCoprime a
       (Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left q₂ hq₁))
     let A : ℕ := (((v⁻¹ : (ZMod b)ˣ) : ZMod b) * (p * d)).val
     let B : ℕ := (((v⁻¹ : (ZMod b)ˣ) : ZMod b) * (2 * p * z₀)).val
     let g := A.gcd b
     let A' := A / g
     let b' := b / g
     4 * (∑ m ∈ Finset.Icc 1 M,
       ‖quadraticSum
         (((A' * m : ℕ) : ℝ) / b')
         (((m * (2 * A * Z + B) : ℕ) : ℝ) / b) L‖) < L) ∧
    (let b := q₂ / q₁.gcd q₂
     2 * (b : ℝ) * ((b : ℝ) / (2 * (M + 1))) ^ k <
       (U : ℝ) ^ k)

theorem rank_two_balanced_locator_of_aggregate_endpoint_data
    {p r u q₁ q₂ L₁ L₂ z₀ : ℕ} {t : ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (hdata : RankTwoBalancedAggregateEndpointData
      p q₁ q₂ L₁ L₂ z₀ hq₁ t) :
    ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
      0 < p * w ^ 2 ∧
      r + u + q₁ * x + q₂ * y = p * w ^ 2 := by
  rcases hdata with
    ⟨X, Hx, Z, L, U, k, M, hU, hL, hZ, hM, hsupport, hxside,
      hleft, hright, hlow, hhigh⟩
  exact rank_two_balanced_locator_of_aggregate_endpoint_bounds
    hp hq₁ hq₂ hbase hU hL hZ hM hsupport hxside hleft hright hlow hhigh

/-! The following canonical Fourier parameters are the quantitative version
of Nguyen--Vu's instruction to take a sufficiently high convolution moment.
The moment is logarithmic in the modulus, so the factor `2^k` absorbs the
number of nonzero Fourier modes without any subpolynomial divisor loss. -/

def nvBalancedMoment (q : ℕ) : ℕ := Nat.log 2 q + 2

def nvBalancedWidth (q H : ℕ) : ℕ :=
  H / nvBalancedMoment q + 1

def nvBalancedCutoff (q H : ℕ) : ℕ :=
  q / nvBalancedWidth q H + 1

lemma nvBalancedMoment_pos (q : ℕ) : 0 < nvBalancedMoment q := by
  simp only [nvBalancedMoment]
  omega

lemma nvBalancedWidth_pos (q H : ℕ) : 0 < nvBalancedWidth q H := by
  simp only [nvBalancedWidth]
  exact Nat.succ_pos _

/-- The genuinely periodic form of the arbitrary-coefficient quadratic
representation theorem.  After removing
`r = gcd (gcd A B) q`, a reduced root is periodic modulo `q / r`, not merely
modulo `q`.  Consequently the quadratic variable can be placed in any
interval containing one reduced period.  This is the composite-modulus
repair needed in the balanced rank-two part of Nguyen--Vu. -/
theorem exists_quadratic_value_in_rectangle_of_reduced_period :
    ∃ Q₀ : ℕ, ∀ {q A B C X Hx Z Hz : ℕ},
      q ≠ 0 →
      q / ((A.gcd B).gcd q) ≤ Hz + 1 →
      (A.gcd B).gcd q + (A.gcd B).gcd q *
          (7 + 8 * (Q₀ + Nat.sqrt
            (ordCompl[2] (q / ((A.gcd B).gcd q))))) ≤ Hx →
      ∃ y ≤ Hx, ∃ w : ℕ, Z ≤ w ∧ w ≤ Z + Hz ∧
        (A : ZMod q) * w ^ 2 + (B : ZMod q) * w + C = X + y := by
  obtain ⟨Q₀, hQ₀⟩ := exists_primitiveQuadraticRootUniformThreshold
  refine ⟨Q₀, ?_⟩
  intro q A B C X Hx Z Hz hq hperiod hbound
  let r := (A.gcd B).gcd q
  let q' := q / r
  let A' := A / r
  let B' := B / r
  let : NeZero q := ⟨hq⟩
  let Cshift : ℕ := (((C : ZMod q) - (X : ZMod q))).val
  let x₀ := Cshift % r
  let C' := Cshift / r
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq
  have hrpos : 0 < r := by
    dsimp only [r]
    exact Nat.gcd_pos_of_pos_right _ hqpos
  have hrdq : r ∣ q := by
    dsimp only [r]
    exact Nat.gcd_dvd_right _ _
  have hrdA : r ∣ A :=
    (Nat.gcd_dvd_left (A.gcd B) q).trans (Nat.gcd_dvd_left A B)
  have hrdB : r ∣ B :=
    (Nat.gcd_dvd_left (A.gcd B) q).trans (Nat.gcd_dvd_right A B)
  have hq'pos : 0 < q' := by
    dsimp only [q']
    exact Nat.div_pos (Nat.le_of_dvd hqpos hrdq) hrpos
  have hcop : (A'.gcd B').Coprime q' := by
    simpa only [A', B', q', r] using
      coprime_reduced_quadratic_coefficients A B q hq
  obtain ⟨v, hv, z', hz'⟩ := hQ₀ hq'pos.ne' hcop (C := C')
  let : NeZero q' := ⟨hq'pos.ne'⟩
  have hperiod' : q' ≤ Hz + 1 := by
    simpa only [q', r] using hperiod
  obtain ⟨w, hZw, hwZ, hwz⟩ :=
    exists_nat_modEq_mem_interval hq'pos z'.val_lt hperiod' (Z := Z)
  have hwz' : (w : ZMod q') = z' := by
    rw [show z' = (z'.val : ZMod q') by
      exact (ZMod.natCast_zmod_val z').symm]
    rw [ZMod.natCast_eq_natCast_iff]
    exact hwz
  have hred : (v : ℤ) ≡
      (A' : ℤ) * (w : ℤ) ^ 2 + (B' : ℤ) * w + C'
        [ZMOD (q' : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [hwz']
    exact hz'.symm
  have hqfac : r * q' = q := by
    dsimp only [q']
    exact Nat.mul_div_cancel' hrdq
  have hAfac : r * A' = A := by
    dsimp only [A']
    exact Nat.mul_div_cancel' hrdA
  have hBfac : r * B' = B := by
    dsimp only [B']
    exact Nat.mul_div_cancel' hrdB
  have hCfac : x₀ + r * C' = Cshift := by
    simpa only [x₀, C'] using Nat.mod_add_div Cshift r
  have hlift := quadratic_root_lifts_of_common_factor
    hqfac hAfac hBfac hCfac hred
  let y := x₀ + r * v
  have hyThreshold : y ≤ r + r *
      (7 + 8 * (Q₀ + Nat.sqrt (ordCompl[2] q'))) := by
    dsimp only [y]
    have hx₀ : x₀ ≤ r := (Nat.mod_lt Cshift hrpos).le
    nlinarith
  have hbound' : r + r *
      (7 + 8 * (Q₀ + Nat.sqrt (ordCompl[2] q'))) ≤ Hx := by
    simpa only [q', r] using hbound
  have hy : y ≤ Hx := hyThreshold.trans hbound'
  have hCshift : (Cshift : ZMod q) = (C : ZMod q) - X := by
    exact ZMod.natCast_zmod_val _
  have hliftZMod : (y : ZMod q) =
      (A : ZMod q) * w ^ 2 + (B : ZMod q) * w + Cshift := by
    have hliftCast : (((y : ℕ) : ℤ) : ZMod q) =
        (((A : ℤ) * (w : ℤ) ^ 2 + (B : ℤ) * w + Cshift : ℤ) :
          ZMod q) :=
      (ZMod.intCast_eq_intCast_iff _ _ q).2 (by simpa only [y] using hlift)
    push_cast at hliftCast
    exact hliftCast
  refine ⟨y, hy, w, hZw, hwZ, ?_⟩
  rw [hCshift] at hliftZMod
  linear_combination -hliftZMod

/-- Reduced-period long-variable branch for the normalized rank-two
congruence.  This is the direct replacement for using a full `q₂`-period in
`exists_rank_two_congruence_long_variable`: the admissible `z` interval need
only contain the period left after the common coefficient factor is removed. -/
theorem exists_rank_two_congruence_reduced_period :
    ∃ Q₀ : ℕ, ∀ {a₀ b₀ a b X Hx Z Hz : ℕ} {t : ℤ},
      (hb : 0 < b) → (hcop : a.Coprime b) →
      let u : (ZMod b)ˣ := ZMod.unitOfCoprime a hcop
      let A : ℕ := (((u⁻¹ : (ZMod b)ˣ) : ZMod b) * a₀).val
      let B : ℕ := (((u⁻¹ : (ZMod b)ˣ) : ZMod b) * b₀).val
      let C : ℕ := (((u⁻¹ : (ZMod b)ˣ) : ZMod b) * (-(t : ZMod b))).val
      let r := (A.gcd B).gcd b
      let b' := b / r
      b' ≤ Hz + 1 →
      r + r * (7 + 8 * (Q₀ + Nat.sqrt (ordCompl[2] b'))) ≤ Hx →
      ∃ x : ℕ, X ≤ x ∧ x ≤ X + Hx ∧
        ∃ z : ℕ, Z ≤ z ∧ z ≤ Z + Hz ∧
          (b : ℤ) ∣ (a₀ : ℤ) * z ^ 2 + (b₀ : ℤ) * z -
            (a : ℤ) * x - t := by
  obtain ⟨Q₀, hQ₀⟩ := exists_quadratic_value_in_rectangle_of_reduced_period
  refine ⟨Q₀, ?_⟩
  intro a₀ b₀ a b X Hx Z Hz t hb hcop
  dsimp only
  intro hperiod hbound
  let : NeZero b := ⟨hb.ne'⟩
  let u : (ZMod b)ˣ := ZMod.unitOfCoprime a hcop
  let A : ℕ := (((u⁻¹ : (ZMod b)ˣ) : ZMod b) * a₀).val
  let B : ℕ := (((u⁻¹ : (ZMod b)ˣ) : ZMod b) * b₀).val
  let C : ℕ := (((u⁻¹ : (ZMod b)ˣ) : ZMod b) * (-(t : ZMod b))).val
  obtain ⟨y, hy, w, hZw, hwZ, hw⟩ :=
    hQ₀ (q := b) (A := A) (B := B) (C := C)
      (X := X) (Hx := Hx) (Z := Z) (Hz := Hz) hb.ne'
      (by simpa only [A, B] using hperiod)
      (by simpa only [A, B] using hbound)
  have hAval : (A : ZMod b) =
      (((u⁻¹ : (ZMod b)ˣ) : ZMod b) * a₀) :=
    ZMod.natCast_zmod_val _
  have hBval : (B : ZMod b) =
      (((u⁻¹ : (ZMod b)ˣ) : ZMod b) * b₀) :=
    ZMod.natCast_zmod_val _
  have hCval : (C : ZMod b) =
      (((u⁻¹ : (ZMod b)ˣ) : ZMod b) * (-(t : ZMod b))) :=
    ZMod.natCast_zmod_val _
  have hu : (a : ZMod b) * (((u⁻¹ : (ZMod b)ˣ) : ZMod b)) = 1 := by
    rw [show (a : ZMod b) = (u : ZMod b) by
      exact (ZMod.coe_unitOfCoprime a hcop).symm]
    rw [← Units.val_mul]
    simp
  have horig : (a₀ : ZMod b) * w ^ 2 + (b₀ : ZMod b) * w =
      (a : ZMod b) * (X + y) + t := by
    rw [hAval, hBval, hCval] at hw
    have hw' : (((u⁻¹ : (ZMod b)ˣ) : ZMod b) *
        ((a₀ : ZMod b) * w ^ 2 + (b₀ : ZMod b) * w - t)) =
          X + y := by
      linear_combination hw
    calc
      (a₀ : ZMod b) * w ^ 2 + (b₀ : ZMod b) * w =
          (a : ZMod b) *
            ((((u⁻¹ : (ZMod b)ˣ) : ZMod b) *
              ((a₀ : ZMod b) * w ^ 2 + (b₀ : ZMod b) * w - t))) + t := by
                rw [← mul_assoc, hu, one_mul]
                ring
      _ = (a : ZMod b) * (X + y) + t := by rw [hw']
  let x := X + y
  refine ⟨x, by simp [x], ?_, w, hZw, hwZ, ?_⟩
  · dsimp only [x]
    omega
  · have hmodeq :
        (a₀ : ℤ) * (w : ℤ) ^ 2 + (b₀ : ℤ) * w ≡
          (a : ℤ) * x + t [ZMOD (b : ℤ)] := by
      rw [← ZMod.intCast_eq_intCast_iff]
      push_cast
      simpa only [x, Nat.cast_add] using horig
    rw [Int.modEq_iff_dvd] at hmodeq
    obtain ⟨k, hk⟩ := hmodeq
    refine ⟨-k, ?_⟩
    linarith

/-- Multiplying two coefficients by the same unit modulo `q` preserves
their common gcd with `q`. -/
lemma gcd_gcd_vals_unit_mul_nat
    (q a b : ℕ) [NeZero q] (v : (ZMod q)ˣ) :
    let A := (((v : ZMod q) * (a : ZMod q))).val
    let B := (((v : ZMod q) * (b : ZMod q))).val
    (A.gcd B).gcd q = (a.gcd b).gcd q := by
  dsimp only
  let A := (((v : ZMod q) * (a : ZMod q))).val
  let B := (((v : ZMod q) * (b : ZMod q))).val
  let c := v.val.val
  have hvCoprime : c.Coprime q := ZMod.val_coe_unit_coprime v
  have hAmod : A ≡ c * a [MOD q] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp only [A, c, Nat.cast_mul, ZMod.natCast_zmod_val]
  have hBmod : B ≡ c * b [MOD q] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp only [B, c, Nat.cast_mul, ZMod.natCast_zmod_val]
  have hBgcd : B.gcd q = b.gcd q := by
    calc
      B.gcd q = (c * b).gcd q := hBmod.gcd_eq
      _ = b.gcd q := hvCoprime.gcd_mul_left_cancel b
  let e := b.gcd q
  have hedq : e ∣ q := by
    dsimp only [e]
    exact Nat.gcd_dvd_right b q
  have hAmodE : A ≡ c * a [MOD e] := hAmod.of_dvd hedq
  have hvCoprimeE : c.Coprime e := hvCoprime.of_dvd_right hedq
  calc
    (A.gcd B).gcd q = A.gcd (B.gcd q) := Nat.gcd_assoc A B q
    _ = A.gcd e := by rw [hBgcd]
    _ = (c * a).gcd e := hAmodE.gcd_eq
    _ = a.gcd e := hvCoprimeE.gcd_mul_left_cancel a
    _ = a.gcd (b.gcd q) := rfl
    _ = (a.gcd b).gcd q := (Nat.gcd_assoc a b q).symm

/-- Archimedean rank-two locator supplied by a full reduced period.  It has
the same normalized quadratic strip as the smoothing locator, but replaces
both Fourier inequalities by the exact reduced-period and primitive
quadratic-value bounds. -/
theorem rank_two_balanced_locator_of_reduced_period :
    ∃ Q₀ : ℕ, ∀ {p r u q₁ q₂ L₁ L₂ z₀ X Hx Z Hz : ℕ} {t : ℤ},
      (hp : 0 < p) → (hq₁ : 0 < q₁) → (hq₂ : 0 < q₂) →
      (hbase : ((r + u : ℕ) : ℤ) =
        (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ)) →
      (hZ : 0 < Z) →
      let d := q₁.gcd q₂
      let a := q₁ / d
      let b := q₂ / d
      let ρ := ((p * d).gcd (2 * p * z₀)).gcd b
      b / ρ ≤ Hz + 1 →
      ρ + ρ * (7 + 8 * (Q₀ + Nat.sqrt (ordCompl[2] (b / ρ)))) ≤ Hx →
      X + Hx ≤ L₁ →
      (∀ x z : ℕ, X ≤ x → x ≤ X + Hx → Z ≤ z → z ≤ Z + Hz →
        0 ≤ (p * d : ℕ) * (z : ℤ) ^ 2 +
            (2 * p * z₀ : ℕ) * z - (a : ℕ) * x - t ∧
        (p * d : ℕ) * (z : ℤ) ^ 2 +
            (2 * p * z₀ : ℕ) * z - (a : ℕ) * x - t ≤
          (b : ℕ) * L₂) →
      ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
        0 < p * w ^ 2 ∧
        r + u + q₁ * x + q₂ * y = p * w ^ 2 := by
  obtain ⟨Q₀, hQ₀⟩ := exists_rank_two_congruence_reduced_period
  refine ⟨Q₀, ?_⟩
  intro p r u q₁ q₂ L₁ L₂ z₀ X Hx Z Hz t hp hq₁ hq₂ hbase hZ
  dsimp only
  intro hperiod hthreshold hxside hstrip
  let d := q₁.gcd q₂
  let a := q₁ / d
  let b := q₂ / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left q₂ hq₁
  have hda : d * a = q₁ := by
    dsimp only [d, a]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left q₁ q₂)
  have hdb : d * b = q₂ := by
    dsimp only [d, b]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_right q₁ q₂)
  have ha : 0 < a := by
    dsimp only [a, d]
    exact Nat.div_pos
      (Nat.le_of_dvd hq₁ (Nat.gcd_dvd_left q₁ q₂)) hd
  have hb : 0 < b := by
    dsimp only [b, d]
    exact Nat.div_pos
      (Nat.le_of_dvd hq₂ (Nat.gcd_dvd_right q₁ q₂)) hd
  have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd hd
  let : NeZero b := ⟨hb.ne'⟩
  let v : (ZMod b)ˣ := (ZMod.unitOfCoprime a hab)⁻¹
  have hρ :
      (((v : ZMod b) * (p * d : ZMod b)).val.gcd
        (((v : ZMod b) * (2 * p * z₀ : ZMod b)).val)).gcd b =
        ((p * d).gcd (2 * p * z₀)).gcd b := by
    simpa only [v, Nat.cast_mul, Nat.cast_ofNat] using
      gcd_gcd_vals_unit_mul_nat b (p * d) (2 * p * z₀) v
  have hperiod' :
      b / ((((v : ZMod b) * (p * d : ZMod b)).val.gcd
        (((v : ZMod b) * (2 * p * z₀ : ZMod b)).val)).gcd b) ≤ Hz + 1 := by
    rw [hρ]
    simpa only [d, b] using hperiod
  have hthreshold' :
      let ρ := (((((v : ZMod b) * (p * d : ZMod b)).val.gcd
        (((v : ZMod b) * (2 * p * z₀ : ZMod b)).val)).gcd b))
      ρ + ρ * (7 + 8 * (Q₀ + Nat.sqrt (ordCompl[2] (b / ρ)))) ≤ Hx := by
    dsimp only
    rw [hρ]
    simpa only [d, b] using hthreshold
  obtain ⟨x, hxX, hxUpper, z, hzZ, hzUpper, hdvd⟩ :=
    hQ₀ (a₀ := p * d) (b₀ := 2 * p * z₀) (a := a) (b := b)
      (X := X) (Hx := Hx) (Z := Z) (Hz := Hz) (t := t) hb hab
      (by simpa only [v, Nat.cast_mul, Nat.cast_ofNat] using hperiod')
      (by simpa only [v, Nat.cast_mul, Nat.cast_ofNat] using hthreshold')
  obtain ⟨y, hy, heq⟩ := exists_rank_two_y_of_dvd hb
    (hstrip x z hxX hxUpper hzZ hzUpper).1
    (hstrip x z hxX hxUpper hzZ hzUpper).2 hdvd
  let w := z₀ + d * z
  have heqNat : r + u + d * a * x + d * b * y = p * w ^ 2 := by
    dsimp only [w]
    apply p_mul_square_eq_rank_two_of_quadratic_eq
      p d a b (r + u) z₀ z x y t
    · simpa only [d] using hbase
    · simpa only [Nat.cast_mul, Nat.cast_ofNat] using heq
  refine ⟨x, hxUpper.trans hxside, y, hy, w, ?_, ?_⟩
  · have hz : 0 < z := hZ.trans_le hzZ
    have hw : 0 < w := by
      dsimp only [w]
      positivity
    exact Nat.mul_pos hp (pow_pos hw 2)
  · simpa only [hda, hdb] using heqNat

/-- A fixed witness for the reduced-period rank-two locator.  Keeping this
constant explicit lets the terminal trichotomy state the period and
smoothing alternatives as one finite disjunction. -/
noncomputable def nvReducedPeriodConstant : ℕ :=
  Classical.choose rank_two_balanced_locator_of_reduced_period

lemma nvReducedPeriodConstant_spec :
    ∀ {p r u q₁ q₂ L₁ L₂ z₀ X Hx Z Hz : ℕ} {t : ℤ},
      (hp : 0 < p) → (hq₁ : 0 < q₁) → (hq₂ : 0 < q₂) →
      (hbase : ((r + u : ℕ) : ℤ) =
        (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ)) →
      (hZ : 0 < Z) →
      let d := q₁.gcd q₂
      let a := q₁ / d
      let b := q₂ / d
      let ρ := ((p * d).gcd (2 * p * z₀)).gcd b
      b / ρ ≤ Hz + 1 →
      ρ + ρ * (7 + 8 * (nvReducedPeriodConstant +
        Nat.sqrt (ordCompl[2] (b / ρ)))) ≤ Hx →
      X + Hx ≤ L₁ →
      (∀ x z : ℕ, X ≤ x → x ≤ X + Hx → Z ≤ z → z ≤ Z + Hz →
        0 ≤ (p * d : ℕ) * (z : ℤ) ^ 2 +
            (2 * p * z₀ : ℕ) * z - (a : ℕ) * x - t ∧
        (p * d : ℕ) * (z : ℤ) ^ 2 +
            (2 * p * z₀ : ℕ) * z - (a : ℕ) * x - t ≤
          (b : ℕ) * L₂) →
      ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
        0 < p * w ^ 2 ∧
        r + u + q₁ * x + q₂ * y = p * w ^ 2 :=
  Classical.choose_spec rank_two_balanced_locator_of_reduced_period

/-- Finite data for the small-conductor branch of the balanced rectangle.
Here the admissible quadratic interval contains a complete reduced period,
so no Fourier estimate is needed. -/
def RankTwoBalancedReducedPeriodData
    (p q₁ q₂ L₁ L₂ z₀ : ℕ) (t : ℤ) : Prop :=
  ∃ X Hx Z Hz : ℕ,
    0 < Z ∧
    (let d := q₁.gcd q₂
     let b := q₂ / d
     let ρ := ((p * d).gcd (2 * p * z₀)).gcd b
     b / ρ ≤ Hz + 1) ∧
    (let d := q₁.gcd q₂
     let b := q₂ / d
     let ρ := ((p * d).gcd (2 * p * z₀)).gcd b
     ρ + ρ * (7 + 8 * (nvReducedPeriodConstant +
       Nat.sqrt (ordCompl[2] (b / ρ)))) ≤ Hx) ∧
    X + Hx ≤ L₁ ∧
    (let d := q₁.gcd q₂
     let a := q₁ / d
     let b := q₂ / d
     ∀ x z : ℕ, X ≤ x → x ≤ X + Hx → Z ≤ z → z ≤ Z + Hz →
       0 ≤ (p * d : ℕ) * (z : ℤ) ^ 2 +
           (2 * p * z₀ : ℕ) * z - (a : ℕ) * x - t ∧
       (p * d : ℕ) * (z : ℤ) ^ 2 +
           (2 * p * z₀ : ℕ) * z - (a : ℕ) * x - t ≤
         (b : ℕ) * L₂)

theorem rank_two_balanced_locator_of_reduced_period_data
    {p r u q₁ q₂ L₁ L₂ z₀ : ℕ} {t : ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (hdata : RankTwoBalancedReducedPeriodData
      p q₁ q₂ L₁ L₂ z₀ t) :
    ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
      0 < p * w ^ 2 ∧
      r + u + q₁ * x + q₂ * y = p * w ^ 2 := by
  rcases hdata with
    ⟨X, Hx, Z, Hz, hZ, hperiod, hthreshold, hxside, hstrip⟩
  exact nvReducedPeriodConstant_spec hp hq₁ hq₂ hbase hZ
    hperiod hthreshold hxside hstrip

theorem rank_two_balanced_locator_of_reduced_period_data_symm
    {p r u q₁ q₂ L₁ L₂ z₀ : ℕ} {t : ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (hdata : RankTwoBalancedReducedPeriodData
      p q₂ q₁ L₂ L₁ z₀ t) :
    ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
      0 < p * w ^ 2 ∧
      r + u + q₁ * x + q₂ * y = p * w ^ 2 := by
  have hbase' : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₂.gcd q₁ : ℕ) := by
    simpa only [Nat.gcd_comm] using hbase
  obtain ⟨y, hy, x, hx, w, hw, heq⟩ :=
    rank_two_balanced_locator_of_reduced_period_data
      hp hq₂ hq₁ hbase' hdata
  refine ⟨x, hx, y, hy, w, hw, ?_⟩
  simpa only [add_assoc, add_left_comm, add_comm] using heq

/-- A single balanced rectangle, split at its true reduced period.  A full
period is handled by the finite quadratic-value theorem; if no period fits,
the caller supplies the pointwise reduced-denominator smoothing inequality.
This is the corrected composite-modulus form of Nguyen--Vu Section 10. -/
theorem rank_two_balanced_locator_of_endpoint_conductor_split
    {p r u q₁ q₂ L₁ L₂ z₀ X Hx Z L U k M : ℕ} {t : ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (hU : 0 < U) (hL : 0 < L) (hZ : 0 < Z)
    (hMhalf : M ≤ (q₂ / q₁.gcd q₂) / 2)
    (hsupport : k * (U - 1) ≤ Hx)
    (hxside : X + Hx ≤ L₁)
    (hleft : ((q₁ / q₁.gcd q₂) * (X + Hx) : ℕ) + t ≤
      (p * q₁.gcd q₂ : ℕ) * (Z : ℤ) ^ 2 +
        (2 * p * z₀ : ℕ) * Z)
    (hright :
      (p * q₁.gcd q₂ : ℕ) * ((Z + L : ℕ) : ℤ) ^ 2 +
          (2 * p * z₀ : ℕ) * (Z + L) ≤
        ((q₂ / q₁.gcd q₂) * L₂ : ℕ) +
          ((q₁ / q₁.gcd q₂) * X : ℕ) + t)
    (hperiodThreshold :
      let d := q₁.gcd q₂
      let b := q₂ / d
      let rho := ((p * d).gcd (2 * p * z₀)).gcd b
      rho + rho * (7 + 8 * (nvReducedPeriodConstant +
        Nat.sqrt (ordCompl[2] (b / rho)))) ≤ Hx)
    (hlow :
      (¬ (let d := q₁.gcd q₂
          let b := q₂ / d
          let rho := ((p * d).gcd (2 * p * z₀)).gcd b
          b / rho ≤ L + 1)) →
      (let d := q₁.gcd q₂
       let b := q₂ / d
       let q' := b / (p * d).gcd b
       4 * (M : ℝ) *
          Real.sqrt
            (L + 4 * ((L : ℝ) * M / q' + 1) * L +
              8 * (L + q') * (1 + Real.log q')) < L))
    (hhigh :
      let b := q₂ / q₁.gcd q₂
      2 * (b : ℝ) * ((b : ℝ) / (2 * (M + 1))) ^ k <
        (U : ℝ) ^ k) :
    ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
      0 < p * w ^ 2 ∧
      r + u + q₁ * x + q₂ * y = p * w ^ 2 := by
  let d := q₁.gcd q₂
  let b := q₂ / d
  let rho := ((p * d).gcd (2 * p * z₀)).gcd b
  have hstrip := rank_two_quadratic_strip_of_endpoint_bounds
    hxside hleft hright
  by_cases hperiod : b / rho ≤ L + 1
  · apply nvReducedPeriodConstant_spec hp hq₁ hq₂ hbase hZ
    · simpa only [d, b, rho] using hperiod
    · simpa only [d, b, rho] using hperiodThreshold
    · exact hxside
    · simpa only [d, b] using hstrip
  · apply rank_two_balanced_locator_of_endpoint_bounds hp hq₁ hq₂ hbase
      hU hL hZ hMhalf hsupport hxside hleft hright
    · apply hlow
      simpa only [d, b, rho] using hperiod
    · exact hhigh

/-- The canonical convolution parameters automatically satisfy the support,
cutoff, and high-frequency inequalities.  Only the low-frequency Weyl bound
and the archimedean rectangle capacity remain to be checked later. -/
theorem canonical_balanced_parameters
    {q H : ℕ} (hq : 6 ≤ q)
    (hH : 2 * nvBalancedMoment q ≤ H) :
    let k := nvBalancedMoment q
    let U := nvBalancedWidth q H
    let M := nvBalancedCutoff q H
    0 < U ∧ M ≤ q / 2 ∧ k * (U - 1) ≤ H ∧
      2 * (q : ℝ) * ((q : ℝ) / (2 * (M + 1))) ^ k <
        (U : ℝ) ^ k := by
  dsimp only
  let k := nvBalancedMoment q
  let U := nvBalancedWidth q H
  let M := nvBalancedCutoff q H
  have hk : 0 < k := nvBalancedMoment_pos q
  have hU : 0 < U := nvBalancedWidth_pos q H
  have htwoDiv : 2 ≤ H / k := by
    apply (Nat.le_div_iff_mul_le hk).2
    simpa only [k] using hH
  have hUthree : 3 ≤ U := by
    change 3 ≤ H / k + 1
    omega
  have hMhalf : M ≤ q / 2 := by
    have hdiv : q / U ≤ q / 3 :=
      Nat.div_le_div_left hUthree (by norm_num)
    have hsix : q / 3 + 1 ≤ q / 2 := by omega
    dsimp only [M, nvBalancedCutoff]
    exact (Nat.add_le_add_right hdiv 1).trans hsix
  have hsupport : k * (U - 1) ≤ H := by
    dsimp only [U, nvBalancedWidth]
    simp only [Nat.add_sub_cancel]
    exact Nat.mul_div_le H k
  have hqPow : 2 * q < 2 ^ k := by
    have hpow := Nat.lt_pow_succ_log_self Nat.one_lt_two q
    dsimp only [k, nvBalancedMoment]
    rw [show Nat.log 2 q + 2 = (Nat.log 2 q + 1) + 1 by omega,
      pow_succ]
    omega
  have hqMU : q < (M + 1) * U := by
    have hraw : q < q / U * U + U := Nat.lt_div_mul_add hU
    have hraw' : q < (q / U + 2) * U := by
      calc
        q < q / U * U + U := hraw
        _ = (q / U + 1) * U := by ring
        _ ≤ (q / U + 2) * U :=
          Nat.mul_le_mul_right U (by omega)
    change q < (q / U + 1 + 1) * U
    exact hraw'
  have hratio :
      (q : ℝ) / (2 * (M + 1)) < (U : ℝ) / 2 := by
    have hMUreal : (q : ℝ) < (M + 1) * U := by exact_mod_cast hqMU
    have hMpos : (0 : ℝ) < M + 1 := by positivity
    have htwo : (0 : ℝ) < 2 := by norm_num
    apply (div_lt_div_iff₀ (mul_pos htwo hMpos) htwo).2
    push_cast at hMUreal ⊢
    nlinarith
  have hratioNonneg : 0 ≤ (q : ℝ) / (2 * (M + 1)) := by positivity
  have hUp : 0 < (U : ℝ) / 2 := by positivity
  have hpowRatio :
      ((q : ℝ) / (2 * (M + 1))) ^ k < ((U : ℝ) / 2) ^ k :=
    pow_lt_pow_left₀ hratio hratioNonneg (by omega)
  have hqPowReal : (2 * q : ℕ) < 2 ^ k := hqPow
  have hsecond :
      2 * (q : ℝ) * ((U : ℝ) / 2) ^ k < (U : ℝ) ^ k := by
    have hcast : (2 * (q : ℝ)) < (2 : ℝ) ^ k := by
      exact_mod_cast hqPowReal
    have hpowTwo : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hUpow : (0 : ℝ) < (U : ℝ) ^ k := by positivity
    rw [div_pow]
    calc
      2 * (q : ℝ) * ((U : ℝ) ^ k / (2 : ℝ) ^ k) =
          (2 * (q : ℝ) * (U : ℝ) ^ k) / (2 : ℝ) ^ k := by ring
      _ < (U : ℝ) ^ k := (div_lt_iff₀ hpowTwo).2 (by
        have hmul := mul_lt_mul_of_pos_right hcast hUpow
        nlinarith)
  refine ⟨hU, hMhalf, hsupport, ?_⟩
  exact (mul_lt_mul_of_pos_left hpowRatio (by positivity)).trans hsecond

/-- A four-term numerical form of the pointwise reduced-denominator Weyl
estimate.  These are exactly the diagonal, short-denominator, logarithmic
linear, and long-period contributions which have to fit below the square of
the quadratic interval length. -/
lemma balanced_pointwise_low_bound_of_four_budgets
    {q' L M : ℕ} (hq' : 0 < q') (hL : 0 < L)
    (hdiag : 320 * (M : ℝ) ^ 2 * L < (L : ℝ) ^ 2)
    (hshort : 256 * (M : ℝ) ^ 3 < q')
    (hlogLinear :
      512 * (M : ℝ) ^ 2 * L * (1 + Real.log q') < (L : ℝ) ^ 2)
    (hlong :
      512 * (M : ℝ) ^ 2 * q' * (1 + Real.log q') < (L : ℝ) ^ 2) :
    4 * (M : ℝ) *
        Real.sqrt
          (L + 4 * ((L : ℝ) * M / q' + 1) * L +
            8 * (L + q') * (1 + Real.log q')) < L := by
  have hq'Real : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hLReal : (0 : ℝ) < L := by exact_mod_cast hL
  have hlog : 0 ≤ Real.log (q' : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ q' by omega))
  let D : ℝ :=
    L + 4 * ((L : ℝ) * M / q' + 1) * L +
      8 * (L + q') * (1 + Real.log q')
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hdiagQuarter :
      80 * (M : ℝ) ^ 2 * L < (L : ℝ) ^ 2 / 4 := by
    nlinarith [hdiag]
  have hshortQuarter :
      64 * (M : ℝ) ^ 3 * (L : ℝ) ^ 2 / q' <
        (L : ℝ) ^ 2 / 4 := by
    apply (div_lt_iff₀ hq'Real).2
    have hmul := mul_lt_mul_of_pos_right hshort (sq_pos_of_pos hLReal)
    nlinarith
  have hlogQuarter :
      128 * (M : ℝ) ^ 2 * L * (1 + Real.log q') <
        (L : ℝ) ^ 2 / 4 := by
    nlinarith [hlogLinear]
  have hlongQuarter :
      128 * (M : ℝ) ^ 2 * q' * (1 + Real.log q') <
        (L : ℝ) ^ 2 / 4 := by
    nlinarith [hlong]
  have hsq : 16 * (M : ℝ) ^ 2 * D < (L : ℝ) ^ 2 := by
    dsimp only [D]
    calc
      16 * (M : ℝ) ^ 2 *
          ((L : ℝ) + 4 * ((L : ℝ) * M / q' + 1) * L +
            8 * (L + q') * (1 + Real.log q')) =
        80 * (M : ℝ) ^ 2 * L +
          64 * (M : ℝ) ^ 3 * (L : ℝ) ^ 2 / q' +
          128 * (M : ℝ) ^ 2 * L * (1 + Real.log q') +
          128 * (M : ℝ) ^ 2 * q' * (1 + Real.log q') := by ring
      _ < (L : ℝ) ^ 2 / 4 + (L : ℝ) ^ 2 / 4 +
          (L : ℝ) ^ 2 / 4 + (L : ℝ) ^ 2 / 4 := by
        gcongr
      _ = (L : ℝ) ^ 2 := by ring
  apply (sq_lt_sq₀ (by positivity) hLReal.le).mp
  rw [mul_pow, Real.sq_sqrt hD]
  dsimp only [D] at hsq ⊢
  nlinarith

lemma le_mul_sq_succ_sqrt_div {c T : ℕ} (hc : 0 < c) :
    T ≤ c * (Nat.sqrt (T / c) + 1) ^ 2 := by
  have hdiv : T < T / c * c + c := Nat.lt_div_mul_add hc
  have hsqrt : T / c + 1 ≤ (Nat.sqrt (T / c) + 1) ^ 2 := by
    have hs : T / c < (Nat.sqrt (T / c) + 1) ^ 2 := by
      simpa only [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' (T / c)
    omega
  calc
    T ≤ T / c * c + c := hdiv.le
    _ = c * (T / c + 1) := by ring
    _ ≤ c * (Nat.sqrt (T / c) + 1) ^ 2 := Nat.mul_le_mul_left c hsqrt

/-- The matching upper estimate for the canonical quadratic left endpoint.
It records precisely the rounding loss introduced by the natural square
root. -/
lemma mul_sq_succ_sqrt_div_le_add {c T : ℕ} (hc : 0 < c) :
    c * (Nat.sqrt (T / c) + 1) ^ 2 ≤
      T + 2 * c * (Nat.sqrt (T / c) + 1) := by
  have hsqrt : Nat.sqrt (T / c) ^ 2 ≤ T / c := Nat.sqrt_le' _
  have hdiv : c * (T / c) ≤ T := Nat.mul_div_le T c
  calc
    c * (Nat.sqrt (T / c) + 1) ^ 2 =
        c * Nat.sqrt (T / c) ^ 2 +
          2 * c * Nat.sqrt (T / c) + c := by ring
    _ ≤ c * (T / c) + 2 * c * Nat.sqrt (T / c) + c := by
      gcongr
    _ ≤ T + 2 * c * Nat.sqrt (T / c) + c := by gcongr
    _ ≤ T + 2 * c * (Nat.sqrt (T / c) + 1) := by nlinarith

/-- Increment form of the Nguyen--Vu quadratic-rectangle capacity estimate.
The starting height `T` cancels against the translate on the right.  The
constant `32` deliberately absorbs all square-root rounding and linear-term
losses, leaving a simple budget for the eventual parameter calculation. -/
lemma quadratic_rectangle_capacity_of_increment_budget
    {c d a b X Hx L L₂ T Z S : ℕ}
    (hc : 0 < c) (hS : 0 < S)
    (hcancel : a * (X + Hx) ≤ T)
    (hZdef : Z = Nat.sqrt (T / c) + 1)
    (hd : d ≤ 2 * c) (hZ : Z ≤ 2 * S) (hL : L ≤ 2 * S)
    (hbudget : a * Hx + 32 * c * S * (L + 1) ≤ b * L₂) :
    c * (Z + L) ^ 2 + d * (Z + L) + c ≤
      b * L₂ + a * X + (T - a * (X + Hx)) := by
  have hZsq : c * Z ^ 2 ≤ T + 2 * c * Z := by
    subst Z
    exact mul_sq_succ_sqrt_div_le_add hc
  have hfourZ : 4 * c * Z ≤ 8 * c * S := by
    nlinarith
  have htwoZL : 2 * c * Z * L ≤ 4 * c * S * L := by
    nlinarith
  have hLsq : c * L ^ 2 ≤ 2 * c * S * L := by
    calc
      c * L ^ 2 = (c * L) * L := by ring
      _ ≤ (c * L) * (2 * S) := Nat.mul_le_mul_left (c * L) hL
      _ = 2 * c * S * L := by ring
  have htwoL : 2 * c * L ≤ 2 * c * S * L := by
    have : 1 ≤ S := by omega
    calc
      2 * c * L = (2 * c * L) * 1 := by ring
      _ ≤ (2 * c * L) * S := Nat.mul_le_mul_left (2 * c * L) this
      _ = 2 * c * S * L := by ring
  have hcS : c ≤ c * S := by
    exact Nat.le_mul_of_pos_right c hS
  have hincrement :
      4 * c * Z + 2 * c * Z * L + c * L ^ 2 + 2 * c * L + c ≤
        32 * c * S * (L + 1) := by
    calc
      4 * c * Z + 2 * c * Z * L + c * L ^ 2 + 2 * c * L + c ≤
          8 * c * S + 4 * c * S * L + 2 * c * S * L +
            2 * c * S * L + c * S := by omega
      _ ≤ 32 * c * S * (L + 1) := by nlinarith
  have hquad :
      c * (Z + L) ^ 2 + d * (Z + L) + c ≤
        T + 32 * c * S * (L + 1) := by
    calc
      c * (Z + L) ^ 2 + d * (Z + L) + c ≤
          c * (Z + L) ^ 2 + (2 * c) * (Z + L) + c := by gcongr
      _ = c * Z ^ 2 + 2 * c * Z * L + c * L ^ 2 +
          2 * c * Z + 2 * c * L + c := by ring
      _ ≤ (T + 2 * c * Z) + 2 * c * Z * L + c * L ^ 2 +
          2 * c * Z + 2 * c * L + c := by gcongr
      _ = T +
          (4 * c * Z + 2 * c * Z * L + c * L ^ 2 + 2 * c * L + c) := by
        ring
      _ ≤ T + 32 * c * S * (L + 1) := Nat.add_le_add_left hincrement T
  have hsum : a * (X + Hx) + (T - a * (X + Hx)) = T :=
    Nat.add_sub_of_le hcancel
  have hsplit : T = a * X + a * Hx + (T - a * (X + Hx)) := by
    calc
      T = a * (X + Hx) + (T - a * (X + Hx)) := hsum.symm
      _ = a * X + a * Hx + (T - a * (X + Hx)) := by ring
  calc
    c * (Z + L) ^ 2 + d * (Z + L) + c ≤
        T + 32 * c * S * (L + 1) := hquad
    _ = a * X + (a * Hx + 32 * c * S * (L + 1)) +
        (T - a * (X + Hx)) := by
          conv_lhs => rw [hsplit]
          ring
    _ ≤ a * X + b * L₂ + (T - a * (X + Hx)) := by gcongr
    _ = b * L₂ + a * X + (T - a * (X + Hx)) := by ring

/-- Canonical choice of the left endpoint of a balanced smoothing rectangle.
Only the upper endpoint and Fourier inequalities remain as hypotheses. -/
theorem rankTwoBalancedEndpointData_of_canonical_left
    {p q₁ q₂ L₁ L₂ z₀ X Hx L U k M : ℕ} {t : ℤ}
    (hp : 0 < p) (hg : 0 < q₁.gcd q₂)
    (hU : 0 < U) (hL : 0 < L)
    (hMhalf : M ≤ (q₂ / q₁.gcd q₂) / 2)
    (hsupport : k * (U - 1) ≤ Hx) (hxside : X + Hx ≤ L₁)
    (hright :
      let Z := Nat.sqrt
        ((((q₁ / q₁.gcd q₂) * (X + Hx)) + t.toNat) /
          (p * q₁.gcd q₂)) + 1
      (p * q₁.gcd q₂ : ℕ) * ((Z + L : ℕ) : ℤ) ^ 2 +
          (2 * p * z₀ : ℕ) * (Z + L) ≤
        ((q₂ / q₁.gcd q₂) * L₂ : ℕ) +
          ((q₁ / q₁.gcd q₂) * X : ℕ) + t)
    (hlow :
      let q₂' := q₂ / q₁.gcd q₂
      let q' := q₂' / (p * q₁.gcd q₂).gcd q₂'
      4 * (M : ℝ) *
          Real.sqrt
            (L + 4 * ((L : ℝ) * M / q' + 1) * L +
              8 * (L + q') * (1 + Real.log q')) < L)
    (hhigh :
      let q₂' := q₂ / q₁.gcd q₂
      2 * (q₂' : ℝ) * ((q₂' : ℝ) / (2 * (M + 1))) ^ k <
        (U : ℝ) ^ k) :
    RankTwoBalancedEndpointData p q₁ q₂ L₁ L₂ z₀ t := by
  let T := ((q₁ / q₁.gcd q₂) * (X + Hx)) + t.toNat
  let Z := Nat.sqrt (T / (p * q₁.gcd q₂)) + 1
  have hc : 0 < p * q₁.gcd q₂ := Nat.mul_pos hp hg
  have hTZ : T ≤ (p * q₁.gcd q₂) * Z ^ 2 := by
    simpa only [T, Z] using le_mul_sq_succ_sqrt_div (c := p * q₁.gcd q₂) hc
  have htToNat : t ≤ (t.toNat : ℤ) := by omega
  have hleft : ((q₁ / q₁.gcd q₂) * (X + Hx) : ℕ) + t ≤
      (p * q₁.gcd q₂ : ℕ) * (Z : ℤ) ^ 2 +
        (2 * p * z₀ : ℕ) * Z := by
    calc
      ((q₁ / q₁.gcd q₂) * (X + Hx) : ℕ) + t ≤
          ((q₁ / q₁.gcd q₂) * (X + Hx) : ℕ) +
            (t.toNat : ℤ) := by
              simpa only [add_comm] using add_le_add_right htToNat
                (((q₁ / q₁.gcd q₂) * (X + Hx) : ℕ) : ℤ)
      _ = (T : ℤ) := by simp only [T, Nat.cast_add, Nat.cast_mul]
      _ ≤ ((p * q₁.gcd q₂) * Z ^ 2 : ℕ) := by exact_mod_cast hTZ
      _ ≤ (p * q₁.gcd q₂ : ℕ) * (Z : ℤ) ^ 2 +
          (2 * p * z₀ : ℕ) * Z := by
        norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        exact le_add_of_nonneg_right (by positivity)
  refine ⟨X, Hx, Z, L, U, k, M, hU, hL, ?_, hMhalf,
    hsupport, hxside, hleft, ?_, hlow, hhigh⟩
  · dsimp only [Z]
    positivity
  · simpa only [Z, T] using hright

/-- Relative-capacity form of the canonical balanced rectangle.  Unlike the
ambient wrapper below, this keeps the positive part of the translation
parameter `t`.  This is the form used in Nguyen--Vu Section 10: after the
left endpoint has been chosen, only the *increment* of the quadratic across
the rectangle must fit in the second GAP direction. -/
theorem rankTwoBalancedEndpointData_of_relative_capacity
    {p q₁ q₂ L₁ L₂ z₀ X Hx L U k M r u : ℕ} {t : ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hz₀ : z₀ < q₁.gcd q₂)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (hU : 0 < U) (hL : 0 < L)
    (hMhalf : M ≤ (q₂ / q₁.gcd q₂) / 2)
    (hsupport : k * (U - 1) ≤ Hx) (hxside : X + Hx ≤ L₁)
    (hcapacity :
      let g := q₁.gcd q₂
      let a := q₁ / g
      let b := q₂ / g
      let T := a * (X + Hx) + t.toNat
      let Z := Nat.sqrt (T / (p * g)) + 1
      p * g * (Z + L) ^ 2 + 2 * p * z₀ * (Z + L) + p * g ≤
        b * L₂ + a * X + t.toNat)
    (hlow :
      let q₂' := q₂ / q₁.gcd q₂
      let q' := q₂' / (p * q₁.gcd q₂).gcd q₂'
      4 * (M : ℝ) *
          Real.sqrt
            (L + 4 * ((L : ℝ) * M / q' + 1) * L +
              8 * (L + q') * (1 + Real.log q')) < L)
    (hhigh :
      let q₂' := q₂ / q₁.gcd q₂
      2 * (q₂' : ℝ) * ((q₂' : ℝ) / (2 * (M + 1))) ^ k <
        (U : ℝ) ^ k) :
    RankTwoBalancedEndpointData p q₁ q₂ L₁ L₂ z₀ t := by
  let g := q₁.gcd q₂
  let a := q₁ / g
  let b := q₂ / g
  let T := a * (X + Hx) + t.toNat
  let Z := Nat.sqrt (T / (p * g)) + 1
  have hg : 0 < g := Nat.gcd_pos_of_pos_left q₂ hq₁
  have htLower : -(p * g : ℕ) ≤ t := by
    have hgInt : (0 : ℤ) < g := by exact_mod_cast hg
    have hz₀g : z₀ ≤ g := hz₀.le
    have hzSqNat : z₀ ^ 2 ≤ g ^ 2 := Nat.pow_le_pow_left hz₀g 2
    have hzSq : (z₀ : ℤ) ^ 2 ≤ (g : ℤ) ^ 2 := by
      exact_mod_cast hzSqNat
    have hpInt : (0 : ℤ) ≤ p := by positivity
    have hrnonneg : (0 : ℤ) ≤ r + u := by positivity
    have hbase' : ((r : ℤ) + u) =
        (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (g : ℤ) := by
      simpa only [Nat.cast_add, g] using hbase
    by_contra hnot
    have htlt : t < -(p * g : ℕ) := lt_of_not_ge hnot
    have htmul : t * (g : ℤ) < (-(p * g : ℕ) : ℤ) * g :=
      mul_lt_mul_of_pos_right htlt hgInt
    have hzmul : (p : ℤ) * (z₀ : ℤ) ^ 2 ≤ p * (g : ℤ) ^ 2 :=
      mul_le_mul_of_nonneg_left hzSq hpInt
    norm_num only [Nat.cast_mul] at htmul
    nlinarith [hbase', htmul, hzmul]
  have hright :
      (p * g : ℕ) * ((Z + L : ℕ) : ℤ) ^ 2 +
          (2 * p * z₀ : ℕ) * (Z + L) ≤
        (b * L₂ : ℕ) + (a * X : ℕ) + t := by
    have hcap :
        p * g * (Z + L) ^ 2 + 2 * p * z₀ * (Z + L) + p * g ≤
          b * L₂ + a * X + t.toNat := by
      simpa only [g, a, b, T, Z] using hcapacity
    by_cases ht : 0 ≤ t
    · have htcast : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg ht
      have hcap' :
          p * g * (Z + L) ^ 2 + 2 * p * z₀ * (Z + L) ≤
            b * L₂ + a * X + t.toNat := by omega
      have hcapInt :
          ((p * g * (Z + L) ^ 2 + 2 * p * z₀ * (Z + L) : ℕ) : ℤ) ≤
            ((b * L₂ + a * X + t.toNat : ℕ) : ℤ) := by
        exact_mod_cast hcap'
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, htcast]
        at hcapInt ⊢
      exact hcapInt
    · have ht' : t ≤ 0 := le_of_not_ge ht
      have htNat : t.toNat = 0 := Int.toNat_of_nonpos ht'
      have hcapInt :
          ((p * g * (Z + L) ^ 2 + 2 * p * z₀ * (Z + L) + p * g : ℕ) : ℤ) ≤
            ((b * L₂ + a * X : ℕ) : ℤ) := by
        exact_mod_cast (by simpa only [htNat, add_zero] using hcap)
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at hcapInt ⊢
      norm_num only [Nat.cast_mul] at htLower
      nlinarith
  apply rankTwoBalancedEndpointData_of_canonical_left hp hg hU hL
      hMhalf hsupport hxside
  · simpa only [g, a, b, T, Z] using hright
  · exact hlow
  · exact hhigh

/-- The purely archimedean part of the relative-capacity construction.  It
chooses the first admissible quadratic height and returns the two endpoint
inequalities, without committing to either the period or smoothing branch. -/
theorem rankTwoBalancedEndpointGeometry_of_relative_capacity
    {p q₁ q₂ L₂ z₀ X Hx L r u : ℕ} {t : ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hz₀ : z₀ < q₁.gcd q₂)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (hcapacity :
      let g := q₁.gcd q₂
      let a := q₁ / g
      let b := q₂ / g
      let T := a * (X + Hx) + t.toNat
      let Z := Nat.sqrt (T / (p * g)) + 1
      p * g * (Z + L) ^ 2 + 2 * p * z₀ * (Z + L) + p * g ≤
        b * L₂ + a * X + t.toNat) :
    ∃ Z : ℕ, 0 < Z ∧
      ((q₁ / q₁.gcd q₂) * (X + Hx) : ℕ) + t ≤
        (p * q₁.gcd q₂ : ℕ) * (Z : ℤ) ^ 2 +
          (2 * p * z₀ : ℕ) * Z ∧
      (p * q₁.gcd q₂ : ℕ) * ((Z + L : ℕ) : ℤ) ^ 2 +
          (2 * p * z₀ : ℕ) * (Z + L) ≤
        ((q₂ / q₁.gcd q₂) * L₂ : ℕ) +
          ((q₁ / q₁.gcd q₂) * X : ℕ) + t := by
  let g := q₁.gcd q₂
  let a := q₁ / g
  let b := q₂ / g
  let T := a * (X + Hx) + t.toNat
  let Z := Nat.sqrt (T / (p * g)) + 1
  have hg : 0 < g := Nat.gcd_pos_of_pos_left q₂ hq₁
  have hc : 0 < p * g := Nat.mul_pos hp hg
  have hTZ : T ≤ (p * g) * Z ^ 2 := by
    simpa only [T, Z] using le_mul_sq_succ_sqrt_div (c := p * g) hc
  have htToNat : t ≤ (t.toNat : ℤ) := by omega
  have hleft : (a * (X + Hx) : ℕ) + t ≤
      (p * g : ℕ) * (Z : ℤ) ^ 2 + (2 * p * z₀ : ℕ) * Z := by
    calc
      (a * (X + Hx) : ℕ) + t ≤
          (a * (X + Hx) : ℕ) + (t.toNat : ℤ) := by
            simpa only [add_comm] using add_le_add_right htToNat
              (((a * (X + Hx) : ℕ) : ℤ))
      _ = (T : ℤ) := by simp only [T, Nat.cast_add, Nat.cast_mul]
      _ ≤ ((p * g) * Z ^ 2 : ℕ) := by exact_mod_cast hTZ
      _ ≤ (p * g : ℕ) * (Z : ℤ) ^ 2 +
          (2 * p * z₀ : ℕ) * Z := by
        norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        exact le_add_of_nonneg_right (by positivity)
  have htLower : -(p * g : ℕ) ≤ t := by
    have hgInt : (0 : ℤ) < g := by exact_mod_cast hg
    have hz₀g : z₀ ≤ g := hz₀.le
    have hzSqNat : z₀ ^ 2 ≤ g ^ 2 := Nat.pow_le_pow_left hz₀g 2
    have hzSq : (z₀ : ℤ) ^ 2 ≤ (g : ℤ) ^ 2 := by
      exact_mod_cast hzSqNat
    have hpInt : (0 : ℤ) ≤ p := by positivity
    have hbase' : ((r : ℤ) + u) =
        (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (g : ℤ) := by
      simpa only [Nat.cast_add, g] using hbase
    by_contra hnot
    have htlt : t < -(p * g : ℕ) := lt_of_not_ge hnot
    have htmul : t * (g : ℤ) < (-(p * g : ℕ) : ℤ) * g :=
      mul_lt_mul_of_pos_right htlt hgInt
    have hzmul : (p : ℤ) * (z₀ : ℤ) ^ 2 ≤ p * (g : ℤ) ^ 2 :=
      mul_le_mul_of_nonneg_left hzSq hpInt
    norm_num only [Nat.cast_mul] at htmul
    have hrnonneg : (0 : ℤ) ≤ r + u := by positivity
    nlinarith [hbase', htmul, hzmul]
  have hright :
      (p * g : ℕ) * ((Z + L : ℕ) : ℤ) ^ 2 +
          (2 * p * z₀ : ℕ) * (Z + L) ≤
        (b * L₂ : ℕ) + (a * X : ℕ) + t := by
    have hcap :
        p * g * (Z + L) ^ 2 + 2 * p * z₀ * (Z + L) + p * g ≤
          b * L₂ + a * X + t.toNat := by
      simpa only [g, a, b, T, Z] using hcapacity
    by_cases ht : 0 ≤ t
    · have htcast : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg ht
      have hcap' :
          p * g * (Z + L) ^ 2 + 2 * p * z₀ * (Z + L) ≤
            b * L₂ + a * X + t.toNat := by omega
      have hcapInt :
          ((p * g * (Z + L) ^ 2 + 2 * p * z₀ * (Z + L) : ℕ) : ℤ) ≤
            ((b * L₂ + a * X + t.toNat : ℕ) : ℤ) := by
        exact_mod_cast hcap'
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, htcast]
        at hcapInt ⊢
      exact hcapInt
    · have ht' : t ≤ 0 := le_of_not_ge ht
      have htNat : t.toNat = 0 := Int.toNat_of_nonpos ht'
      have hcapInt :
          ((p * g * (Z + L) ^ 2 + 2 * p * z₀ * (Z + L) + p * g : ℕ) : ℤ) ≤
            ((b * L₂ + a * X : ℕ) : ℤ) := by
        exact_mod_cast (by simpa only [htNat, add_zero] using hcap)
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at hcapInt ⊢
      norm_num only [Nat.cast_mul] at htLower
      nlinarith
  refine ⟨Z, ?_, ?_, ?_⟩
  · dsimp only [Z]
    positivity
  · simpa only [g, a] using hleft
  · simpa only [g, a, b] using hright

/-- The canonical left endpoint is bounded by the ambient subset-sum scale.
This is the quantitative link between the translated quadratic rectangle and
the original interval `[0,H]`. -/
lemma canonical_rank_two_Z_le_ambient_sqrt
    {p q₁ q₂ L₁ L₂ z₀ X Hx r u H : ℕ} {t : ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hz₀ : z₀ < q₁.gcd q₂)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (hambient : r + u + q₁ * L₁ + q₂ * L₂ ≤ H)
    (hxside : X + Hx ≤ L₁) :
    let g := q₁.gcd q₂
    let a := q₁ / g
    let T := a * (X + Hx) + t.toNat
    Nat.sqrt (T / (p * g)) + 1 ≤
      Nat.sqrt (H / (p * g ^ 2)) + 1 := by
  let g := q₁.gcd q₂
  let a := q₁ / g
  let T := a * (X + Hx) + t.toNat
  have hg : 0 < g := Nat.gcd_pos_of_pos_left q₂ hq₁
  have htNatMul : t.toNat * g ≤ r + u := by
    by_cases ht : 0 ≤ t
    · have htcast : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg ht
      have hleInt : ((t.toNat * g : ℕ) : ℤ) ≤ r + u := by
        have hbase' : ((r : ℤ) + u) =
            (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (g : ℤ) := by
          simpa only [Nat.cast_add, g] using hbase
        norm_num only [Nat.cast_mul, Nat.cast_add, htcast]
        rw [hbase']
        have hpz : (0 : ℤ) ≤ (p : ℤ) * (z₀ : ℤ) ^ 2 := by positivity
        linarith
      exact_mod_cast hleInt
    · have ht' : t ≤ 0 := le_of_not_ge ht
      simp [Int.toNat_of_nonpos ht']
  have hga : g * a = q₁ := by
    dsimp only [g, a]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left q₁ q₂)
  have hTg : T * g ≤ H := by
    calc
      T * g = q₁ * (X + Hx) + t.toNat * g := by
        dsimp only [T]
        rw [← hga]
        ring
      _ ≤ q₁ * L₁ + (r + u) :=
        Nat.add_le_add (Nat.mul_le_mul_left q₁ hxside) htNatMul
      _ ≤ H := by omega
  have hquot : T / (p * g) ≤ H / (p * g ^ 2) := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < p * g ^ 2)).2
    calc
      T / (p * g) * (p * g ^ 2) =
          (p * g * (T / (p * g))) * g := by ring
      _ ≤ T * g := Nat.mul_le_mul_right g (Nat.mul_div_le T (p * g))
      _ ≤ H := hTg
  simpa only [g, a, T] using
    Nat.add_le_add_right (Nat.sqrt_le_sqrt hquot) 1

/-- Canonical balanced endpoint data from the five elementary Nguyen--Vu
budgets: support width, quadratic increment capacity, and the four terms in
the reduced-denominator Weyl estimate.  No divisor-count estimate appears. -/
theorem rankTwoBalancedEndpointData_of_increment_budgets
    {p q₁ q₂ L₁ L₂ z₀ X Hx L S r u : ℕ} {t : ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hz₀ : z₀ < q₁.gcd q₂)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (hq : 6 ≤ q₂ / q₁.gcd q₂)
    (hHx : 2 * nvBalancedMoment (q₂ / q₁.gcd q₂) ≤ Hx)
    (hLpos : 0 < L) (hSpos : 0 < S) (hxside : X + Hx ≤ L₁)
    (hZbound :
      let g := q₁.gcd q₂
      let a := q₁ / g
      let T := a * (X + Hx) + t.toNat
      Nat.sqrt (T / (p * g)) + 1 ≤ 2 * S)
    (hLbound : L ≤ 2 * S)
    (hcapacity :
      let g := q₁.gcd q₂
      let a := q₁ / g
      let b := q₂ / g
      a * Hx + 32 * (p * g) * S * (L + 1) ≤ b * L₂)
    (hdiag :
      let b := q₂ / q₁.gcd q₂
      let M := nvBalancedCutoff b Hx
      320 * (M : ℝ) ^ 2 * L < (L : ℝ) ^ 2)
    (hshort :
      let b := q₂ / q₁.gcd q₂
      let M := nvBalancedCutoff b Hx
      let q' := b / (p * q₁.gcd q₂).gcd b
      256 * (M : ℝ) ^ 3 < q')
    (hlogLinear :
      let b := q₂ / q₁.gcd q₂
      let M := nvBalancedCutoff b Hx
      let q' := b / (p * q₁.gcd q₂).gcd b
      512 * (M : ℝ) ^ 2 * L * (1 + Real.log q') < (L : ℝ) ^ 2)
    (hlong :
      let b := q₂ / q₁.gcd q₂
      let M := nvBalancedCutoff b Hx
      let q' := b / (p * q₁.gcd q₂).gcd b
      512 * (M : ℝ) ^ 2 * q' * (1 + Real.log q') < (L : ℝ) ^ 2) :
    RankTwoBalancedEndpointData p q₁ q₂ L₁ L₂ z₀ t := by
  let g := q₁.gcd q₂
  let a := q₁ / g
  let b := q₂ / g
  let c := p * g
  let T := a * (X + Hx) + t.toNat
  let Z := Nat.sqrt (T / c) + 1
  let k := nvBalancedMoment b
  let U := nvBalancedWidth b Hx
  let M := nvBalancedCutoff b Hx
  let q' := b / c.gcd b
  have hg : 0 < g := Nat.gcd_pos_of_pos_left q₂ hq₁
  have hc : 0 < c := Nat.mul_pos hp hg
  have hb : 0 < b := by
    dsimp only [b, g]
    exact Nat.div_pos
      (Nat.le_of_dvd hq₂ (Nat.gcd_dvd_right q₁ q₂)) hg
  have hq' : 0 < q' := by
    dsimp only [q']
    exact Nat.div_pos (Nat.gcd_le_right c hb) (Nat.gcd_pos_of_pos_right c hb)
  obtain ⟨hU, hMhalf, hsupport, hhigh⟩ :=
    canonical_balanced_parameters (q := b) (H := Hx)
      (by simpa only [b, g] using hq) (by simpa only [b, g] using hHx)
  have hlow : 4 * (M : ℝ) *
      Real.sqrt
        (L + 4 * ((L : ℝ) * M / q' + 1) * L +
          8 * (L + q') * (1 + Real.log q')) < L := by
    apply balanced_pointwise_low_bound_of_four_budgets hq' hLpos
    · simpa only [M, b, g] using hdiag
    · simpa only [M, q', c, b, g] using hshort
    · simpa only [M, q', c, b, g] using hlogLinear
    · simpa only [M, q', c, b, g] using hlong
  have hcancel : a * (X + Hx) ≤ T := by simp [T]
  have hd : 2 * p * z₀ ≤ 2 * c := by
    dsimp only [c]
    simpa only [mul_assoc] using Nat.mul_le_mul_left (2 * p) hz₀.le
  have hcap :
      c * (Z + L) ^ 2 + (2 * p * z₀) * (Z + L) + c ≤
        b * L₂ + a * X + t.toNat := by
    have hraw := quadratic_rectangle_capacity_of_increment_budget
      hc hSpos hcancel (by rfl : Z = Nat.sqrt (T / c) + 1) hd
      (by simpa only [Z, T, c, a, g] using hZbound) hLbound
      (by simpa only [a, b, c, g] using hcapacity)
    have hrem : T - a * (X + Hx) = t.toNat := by simp [T]
    simpa only [hrem] using hraw
  apply rankTwoBalancedEndpointData_of_relative_capacity
      (X := X) (Hx := Hx) (L := L) (U := U) (k := k) (M := M)
      (r := r) (u := u) hp hq₁ hq₂ hz₀ hbase
      (by simpa only [U, b, g] using hU) hLpos
  · simpa only [M, b, g] using hMhalf
  · simpa only [k, U, b, g] using hsupport
  · exact hxside
  · simpa only [g, a, b, c, T, Z] using hcap
  · simpa only [M, q', c, b, g] using hlow
  · simpa only [k, U, M, b, g] using hhigh

/-- Increment-budget wrapper with the corrected conductor split.  The three
Weyl budgets independent of the reduced denominator are unconditional; the
short-denominator budget is needed only when a full reduced period does not
fit in the same quadratic interval. -/
theorem rank_two_balanced_locator_of_increment_budgets_conductor_split
    {p r u q₁ q₂ L₁ L₂ z₀ X Hx L S : ℕ} {t : ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hz₀ : z₀ < q₁.gcd q₂)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (hq : 6 ≤ q₂ / q₁.gcd q₂)
    (hHx : 2 * nvBalancedMoment (q₂ / q₁.gcd q₂) ≤ Hx)
    (hLpos : 0 < L) (hSpos : 0 < S) (hxside : X + Hx ≤ L₁)
    (hZbound :
      let g := q₁.gcd q₂
      let a := q₁ / g
      let T := a * (X + Hx) + t.toNat
      Nat.sqrt (T / (p * g)) + 1 ≤ 2 * S)
    (hLbound : L ≤ 2 * S)
    (hcapacity :
      let g := q₁.gcd q₂
      let a := q₁ / g
      let b := q₂ / g
      a * Hx + 32 * (p * g) * S * (L + 1) ≤ b * L₂)
    (hperiodThreshold :
      let g := q₁.gcd q₂
      let b := q₂ / g
      let rho := ((p * g).gcd (2 * p * z₀)).gcd b
      rho + rho * (7 + 8 * (nvReducedPeriodConstant +
        Nat.sqrt (ordCompl[2] (b / rho)))) ≤ Hx)
    (hdiag :
      let b := q₂ / q₁.gcd q₂
      let M := nvBalancedCutoff b Hx
      320 * (M : ℝ) ^ 2 * L < (L : ℝ) ^ 2)
    (hshort :
      (¬ (let g := q₁.gcd q₂
          let b := q₂ / g
          let rho := ((p * g).gcd (2 * p * z₀)).gcd b
          b / rho ≤ L + 1)) →
      (let g := q₁.gcd q₂
       let b := q₂ / g
       let M := nvBalancedCutoff b Hx
       let q' := b / (p * g).gcd b
       256 * (M : ℝ) ^ 3 < q'))
    (hlogLinear :
      let g := q₁.gcd q₂
      let b := q₂ / g
      let M := nvBalancedCutoff b Hx
      let q' := b / (p * g).gcd b
      512 * (M : ℝ) ^ 2 * L * (1 + Real.log q') < (L : ℝ) ^ 2)
    (hlong :
      let g := q₁.gcd q₂
      let b := q₂ / g
      let M := nvBalancedCutoff b Hx
      let q' := b / (p * g).gcd b
      512 * (M : ℝ) ^ 2 * q' * (1 + Real.log q') < (L : ℝ) ^ 2) :
    ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
      0 < p * w ^ 2 ∧
      r + u + q₁ * x + q₂ * y = p * w ^ 2 := by
  let g := q₁.gcd q₂
  let a := q₁ / g
  let b := q₂ / g
  let c := p * g
  let T := a * (X + Hx) + t.toNat
  let Z := Nat.sqrt (T / c) + 1
  let k := nvBalancedMoment b
  let U := nvBalancedWidth b Hx
  let M := nvBalancedCutoff b Hx
  let q' := b / c.gcd b
  have hg : 0 < g := Nat.gcd_pos_of_pos_left q₂ hq₁
  have hc : 0 < c := Nat.mul_pos hp hg
  have hb : 0 < b := by
    dsimp only [b, g]
    exact Nat.div_pos
      (Nat.le_of_dvd hq₂ (Nat.gcd_dvd_right q₁ q₂)) hg
  have hq' : 0 < q' := by
    dsimp only [q']
    exact Nat.div_pos (Nat.gcd_le_right c hb)
      (Nat.gcd_pos_of_pos_right c hb)
  obtain ⟨hU, hMhalf, hsupport, hhigh⟩ :=
    canonical_balanced_parameters (q := b) (H := Hx)
      (by simpa only [b, g] using hq) (by simpa only [b, g] using hHx)
  have hcancel : a * (X + Hx) ≤ T := by simp [T]
  have hd : 2 * p * z₀ ≤ 2 * c := by
    dsimp only [c]
    simpa only [mul_assoc] using Nat.mul_le_mul_left (2 * p) hz₀.le
  have hcap :
      c * (Z + L) ^ 2 + (2 * p * z₀) * (Z + L) + c ≤
        b * L₂ + a * X + t.toNat := by
    have hraw := quadratic_rectangle_capacity_of_increment_budget
      hc hSpos hcancel (by rfl : Z = Nat.sqrt (T / c) + 1) hd
      (by simpa only [Z, T, c, a, g] using hZbound) hLbound
      (by simpa only [a, b, c, g] using hcapacity)
    have hrem : T - a * (X + Hx) = t.toNat := by simp [T]
    simpa only [hrem] using hraw
  obtain ⟨Z', hZ', hleft, hright⟩ :=
    rankTwoBalancedEndpointGeometry_of_relative_capacity
      (X := X) (Hx := Hx) (L := L) (r := r) (u := u)
      hp hq₁ hq₂ hz₀ hbase
      (by simpa only [g, a, b, c, T, Z] using hcap)
  apply rank_two_balanced_locator_of_endpoint_conductor_split
      (X := X) (Hx := Hx) (Z := Z') (L := L)
      (U := U) (k := k) (M := M)
      hp hq₁ hq₂ hbase
      (by simpa only [U, b, g] using hU) hLpos hZ'
      (by simpa only [M, b, g] using hMhalf)
      (by simpa only [k, U, b, g] using hsupport)
      hxside hleft hright
  · simpa only [g, b] using hperiodThreshold
  · intro hnoPeriod
    apply balanced_pointwise_low_bound_of_four_budgets hq' hLpos
    · simpa only [M, b, g] using hdiag
    · have hs := hshort (by simpa only [g, b] using hnoPeriod)
      simpa only [M, q', c, b, g] using hs
    · simpa only [M, q', c, b, g] using hlogLinear
    · simpa only [M, q', c, b, g] using hlong
  · simpa only [k, U, M, b, g] using hhigh


/-- Canonical balanced endpoint wrapper.  The logarithmic convolution
parameters are now fixed once the normalized second step and the available
first-coordinate width are known.  Thus callers need provide only the
archimedean capacity and the low-frequency estimate. -/
theorem rankTwoBalancedEndpointData_of_canonical_parameters
    {p q₁ q₂ L₁ L₂ z₀ X Hx L r u : ℕ} {t : ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hz₀ : z₀ < q₁.gcd q₂)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (hq : 6 ≤ q₂ / q₁.gcd q₂)
    (hHx : 2 * nvBalancedMoment (q₂ / q₁.gcd q₂) ≤ Hx)
    (hL : 0 < L) (hxside : X + Hx ≤ L₁)
    (hcapacity :
      let g := q₁.gcd q₂
      let a := q₁ / g
      let b := q₂ / g
      let T := a * (X + Hx) + t.toNat
      let Z := Nat.sqrt (T / (p * g)) + 1
      p * g * (Z + L) ^ 2 + 2 * p * z₀ * (Z + L) + p * g ≤
        b * L₂ + a * X + t.toNat)
    (hlow :
      let b := q₂ / q₁.gcd q₂
      let M := nvBalancedCutoff b Hx
      let q' := b / (p * q₁.gcd q₂).gcd b
      4 * (M : ℝ) *
          Real.sqrt
            (L + 4 * ((L : ℝ) * M / q' + 1) * L +
              8 * (L + q') * (1 + Real.log q')) < L) :
    RankTwoBalancedEndpointData p q₁ q₂ L₁ L₂ z₀ t := by
  let b := q₂ / q₁.gcd q₂
  let k := nvBalancedMoment b
  let U := nvBalancedWidth b Hx
  let M := nvBalancedCutoff b Hx
  obtain ⟨hU, hMhalf, hsupport, hhigh⟩ :=
    canonical_balanced_parameters (q := b) (H := Hx)
      (by simpa only [b] using hq) (by simpa only [b] using hHx)
  apply rankTwoBalancedEndpointData_of_relative_capacity
      (X := X) (Hx := Hx) (L := L) (U := U) (k := k) (M := M)
      (r := r) (u := u) hp hq₁ hq₂ hz₀ hbase hU hL
  · simpa only [b] using hMhalf
  · simpa only [k, U] using hsupport
  · exact hxside
  · exact hcapacity
  · simpa only [b, M] using hlow
  · simpa only [b, k, U, M] using hhigh

/-- A coarse natural-number capacity inequality implies the upper endpoint
condition for the canonical balanced rectangle. -/
theorem rankTwoBalancedEndpointData_of_ambient_capacity
    {p q₁ q₂ L₁ L₂ z₀ X Hx L U k M r u H : ℕ} {t : ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hz₀ : z₀ < q₁.gcd q₂)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (hambient : r + u + q₁ * L₁ + q₂ * L₂ ≤ H)
    (hU : 0 < U) (hL : 0 < L)
    (hMhalf : M ≤ (q₂ / q₁.gcd q₂) / 2)
    (hsupport : k * (U - 1) ≤ Hx) (hxside : X + Hx ≤ L₁)
    (hcapacity :
      let g := q₁.gcd q₂
      let a := q₁ / g
      let b := q₂ / g
      let S := Nat.sqrt (H / (p * g ^ 2)) + 1
      p * g * (S + L) ^ 2 + 2 * p * g * (S + L) + p * g ≤
        b * L₂ + a * X)
    (hlow :
      let q₂' := q₂ / q₁.gcd q₂
      let q' := q₂' / (p * q₁.gcd q₂).gcd q₂'
      4 * (M : ℝ) *
          Real.sqrt
            (L + 4 * ((L : ℝ) * M / q' + 1) * L +
              8 * (L + q') * (1 + Real.log q')) < L)
    (hhigh :
      let q₂' := q₂ / q₁.gcd q₂
      2 * (q₂' : ℝ) * ((q₂' : ℝ) / (2 * (M + 1))) ^ k <
        (U : ℝ) ^ k) :
    RankTwoBalancedEndpointData p q₁ q₂ L₁ L₂ z₀ t := by
  let g := q₁.gcd q₂
  let a := q₁ / g
  let b := q₂ / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left q₂ hq₁
  have hgz₀ : z₀ ≤ g := hz₀.le
  have hzSqNat : z₀ ^ 2 ≤ g ^ 2 := Nat.pow_le_pow_left hgz₀ 2
  have htLower : -(p * g : ℕ) ≤ t := by
    have hgInt : (0 : ℤ) < g := by exact_mod_cast hg
    have hzSq : (z₀ : ℤ) ^ 2 ≤ (g : ℤ) ^ 2 := by exact_mod_cast hzSqNat
    have hpInt : (0 : ℤ) ≤ p := by positivity
    have hrnonneg : (0 : ℤ) ≤ r + u := by positivity
    have hbase' : ((r : ℤ) + u) =
        (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (g : ℤ) := by
      simpa only [Nat.cast_add, g] using hbase
    by_contra hnot
    have htlt : t < -(p * g : ℕ) := lt_of_not_ge hnot
    have htmul : t * (g : ℤ) < (-(p * g : ℕ) : ℤ) * g :=
      mul_lt_mul_of_pos_right htlt hgInt
    have hzmul : (p : ℤ) * (z₀ : ℤ) ^ 2 ≤ p * (g : ℤ) ^ 2 :=
      mul_le_mul_of_nonneg_left hzSq hpInt
    norm_num only [Nat.cast_mul] at htmul
    nlinarith [hbase', htmul, hzmul]
  have htNatMul : t.toNat * g ≤ r + u := by
    by_cases ht : 0 ≤ t
    · have htcast : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg ht
      have hleInt : ((t.toNat * g : ℕ) : ℤ) ≤ r + u := by
        have hbase' : ((r : ℤ) + u) =
            (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (g : ℤ) := by
          simpa only [Nat.cast_add, g] using hbase
        norm_num only [Nat.cast_mul, Nat.cast_add, htcast]
        rw [hbase']
        have hpz : (0 : ℤ) ≤ (p : ℤ) * (z₀ : ℤ) ^ 2 := by positivity
        linarith
      exact_mod_cast hleInt
    · have ht' : t ≤ 0 := le_of_not_ge ht
      simp [Int.toNat_of_nonpos ht']
  let T := a * (X + Hx) + t.toNat
  have hTg : T * g ≤ H := by
    have hga : g * a = q₁ := by
      dsimp only [a, g]
      exact Nat.mul_div_cancel' (Nat.gcd_dvd_left q₁ q₂)
    calc
      T * g = q₁ * (X + Hx) + t.toNat * g := by
        dsimp only [T]
        rw [← hga]
        ring
      _ ≤ q₁ * L₁ + (r + u) :=
        Nat.add_le_add (Nat.mul_le_mul_left q₁ hxside) htNatMul
      _ ≤ H := by omega
  let Z := Nat.sqrt (T / (p * g)) + 1
  let S := Nat.sqrt (H / (p * g ^ 2)) + 1
  have hquot : T / (p * g) ≤ H / (p * g ^ 2) := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < p * g ^ 2)).2
    calc
      T / (p * g) * (p * g ^ 2) =
          (p * g * (T / (p * g))) * g := by ring
      _ ≤ T * g := Nat.mul_le_mul_right g (Nat.mul_div_le T (p * g))
      _ ≤ H := hTg
  have hZS : Z ≤ S := by
    dsimp only [Z, S]
    exact Nat.add_le_add_right (Nat.sqrt_le_sqrt hquot) 1
  have hquadMono :
      p * g * (Z + L) ^ 2 + 2 * p * z₀ * (Z + L) ≤
        p * g * (S + L) ^ 2 + 2 * p * g * (S + L) := by
    have hsum : Z + L ≤ S + L := Nat.add_le_add_right hZS L
    have hsq : (Z + L) ^ 2 ≤ (S + L) ^ 2 := Nat.pow_le_pow_left hsum 2
    exact Nat.add_le_add (Nat.mul_le_mul_left (p * g) hsq)
      (Nat.mul_le_mul (Nat.mul_le_mul_left (2 * p) hgz₀) hsum)
  have hright :
      (p * g : ℕ) * ((Z + L : ℕ) : ℤ) ^ 2 +
          (2 * p * z₀ : ℕ) * (Z + L) ≤
        (b * L₂ : ℕ) + (a * X : ℕ) + t := by
    have hnat :
        p * g * (Z + L) ^ 2 + 2 * p * z₀ * (Z + L) + p * g ≤
          b * L₂ + a * X := by
      exact (Nat.add_le_add_right hquadMono (p * g)).trans
        (by simpa only [g, a, b, S] using hcapacity)
    have hnatInt :
        (p * g : ℕ) * ((Z + L : ℕ) : ℤ) ^ 2 +
              (2 * p * z₀ : ℕ) * (Z + L) + (p * g : ℕ) ≤
            (b * L₂ : ℕ) + (a * X : ℕ) := by
      exact_mod_cast hnat
    have hnonneg : (0 : ℤ) ≤ (p * g : ℕ) + t := by
      linarith [htLower]
    calc
      (p * g : ℕ) * ((Z + L : ℕ) : ℤ) ^ 2 +
            (2 * p * z₀ : ℕ) * (Z + L) ≤
          (p * g : ℕ) * ((Z + L : ℕ) : ℤ) ^ 2 +
            (2 * p * z₀ : ℕ) * (Z + L) + ((p * g : ℕ) + t) :=
        le_add_of_nonneg_right hnonneg
      _ = ((p * g : ℕ) * ((Z + L : ℕ) : ℤ) ^ 2 +
            (2 * p * z₀ : ℕ) * (Z + L) + (p * g : ℕ)) + t := by ring
      _ ≤ ((b * L₂ : ℕ) + (a * X : ℕ)) + t := by
        simpa only [add_comm] using add_le_add_right hnatInt t
  apply rankTwoBalancedEndpointData_of_canonical_left hp
    (by simpa only [g] using hg) hU hL hMhalf hsupport hxside
  · simpa only [g, a, b, T, Z] using hright
  · exact hlow
  · exact hhigh

/-- Exhaustive rank-two interface: either one side is long enough for the
one-variable Nguyen--Vu argument, or explicit balanced smoothing data are
available.  The square root residue is normalized modulo the common step
before the alternatives are inspected. -/
theorem rank_two_locator_of_archimedean_alternatives
    {A : Finset ℕ} {N p r u q₁ q₂ L₁ L₂ z₀ : ℕ} {t : ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hL₁pos : 0 < L₁) (hL₂pos : 0 < L₂)
    (hfamily : ∀ x ≤ L₁, ∀ y ≤ L₂,
      r + u + q₁ * x + q₂ * y ∈ A.subsetSum)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (halt : ∀ z : ℕ, z < q₁.gcd q₂ → ∀ v : ℤ,
      ((r + u : ℕ) : ℤ) =
          (p : ℤ) * (z : ℤ) ^ 2 + v * (q₁.gcd q₂ : ℕ) →
      (nvRankTwoUnbalancedConstant * (Nat.sqrt (p * q₂) + 1) ≤ L₁ ∧
          64 * p * (A.card * N) ≤ L₂ ^ 2) ∨
      (nvRankTwoUnbalancedConstant * (Nat.sqrt (p * q₁) + 1) ≤ L₂ ∧
          64 * p * (A.card * N) ≤ L₁ ^ 2) ∨
      RankTwoBalancedEndpointData p q₁ q₂ L₁ L₂ z v) :
    ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
      0 < p * w ^ 2 ∧
      r + u + q₁ * x + q₂ * y = p * w ^ 2 := by
  have hg : 0 < q₁.gcd q₂ := Nat.gcd_pos_of_pos_left q₂ hq₁
  obtain ⟨z, hz, v, hbase'⟩ :=
    normalize_square_base_mod hg hbase
  rcases halt z hz v hbase' with
    ⟨htrans, hbig⟩ | ⟨htrans, hbig⟩ | hbalanced
  · exact rank_two_unbalanced_locator_of_square_side hp hq₁ hq₂
      hAN hfamily hbase' hL₂pos htrans hbig
  · exact rank_two_unbalanced_locator_of_square_side_symm hp hq₁ hq₂
      hAN hfamily hbase' hL₁pos htrans hbig
  · rcases hbalanced with
      ⟨X, Hx, Z, L, U, k, M, hU, hL, hZ, hM, hsupport, hxside, hleft, hright,
        hlow, hhigh⟩
    exact rank_two_balanced_locator_of_endpoint_bounds hp hq₁ hq₂
      hbase' hU hL hZ hM hsupport hxside hleft hright hlow hhigh

/-- Exhaustive Section 10 interface with the composite-modulus repair made
explicit.  The balanced branch is split by the reduced conductor: a full
reduced period is handled algebraically, while the complementary range uses
finite convolution smoothing and the pointwise reduced-denominator Weyl
bound. -/
theorem rank_two_locator_of_period_or_smoothing_alternatives
    {A : Finset ℕ} {N p r u q₁ q₂ L₁ L₂ z₀ : ℕ} {t : ℤ}
    (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hL₁pos : 0 < L₁) (hL₂pos : 0 < L₂)
    (hfamily : ∀ x ≤ L₁, ∀ y ≤ L₂,
      r + u + q₁ * x + q₂ * y ∈ A.subsetSum)
    (hbase : ((r + u : ℕ) : ℤ) =
      (p : ℤ) * (z₀ : ℤ) ^ 2 + t * (q₁.gcd q₂ : ℕ))
    (halt : ∀ z : ℕ, z < q₁.gcd q₂ → ∀ v : ℤ,
      ((r + u : ℕ) : ℤ) =
          (p : ℤ) * (z : ℤ) ^ 2 + v * (q₁.gcd q₂ : ℕ) →
      (nvRankTwoUnbalancedConstant * (Nat.sqrt (p * q₂) + 1) ≤ L₁ ∧
          64 * p * (A.card * N) ≤ L₂ ^ 2) ∨
      (nvRankTwoUnbalancedConstant * (Nat.sqrt (p * q₁) + 1) ≤ L₂ ∧
          64 * p * (A.card * N) ≤ L₁ ^ 2) ∨
      RankTwoBalancedReducedPeriodData p q₁ q₂ L₁ L₂ z v ∨
      RankTwoBalancedEndpointData p q₁ q₂ L₁ L₂ z v) :
    ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
      0 < p * w ^ 2 ∧
      r + u + q₁ * x + q₂ * y = p * w ^ 2 := by
  have hg : 0 < q₁.gcd q₂ := Nat.gcd_pos_of_pos_left q₂ hq₁
  obtain ⟨z, hz, v, hbase'⟩ := normalize_square_base_mod hg hbase
  rcases halt z hz v hbase' with
    ⟨htrans, hbig⟩ | ⟨htrans, hbig⟩ | hperiod | hsmooth
  · exact rank_two_unbalanced_locator_of_square_side hp hq₁ hq₂
      hAN hfamily hbase' hL₂pos htrans hbig
  · exact rank_two_unbalanced_locator_of_square_side_symm hp hq₁ hq₂
      hAN hfamily hbase' hL₁pos htrans hbig
  · exact rank_two_balanced_locator_of_reduced_period_data
      hp hq₁ hq₂ hbase' hperiod
  · rcases hsmooth with
      ⟨X, Hx, Z, L, U, k, M, hU, hL, hZ, hM, hsupport, hxside,
        hleft, hright, hlow, hhigh⟩
    exact rank_two_balanced_locator_of_endpoint_bounds hp hq₁ hq₂
      hbase' hU hL hZ hM hsupport hxside hleft hright hlow hhigh

/-! ## Elementary quantitative consequences of the structural output -/

/-- In rank one, the preserved cubic stopping budget is bounded above by
the progression length times the square of the original stopping scale. -/
lemma rank_one_cubic_budget_upper
    {W C b D F L U : ℕ}
    (hW : W ≤ C * b * D ^ 3)
    (hscaled : b * D ≤ F * (L + 1))
    (hDU : D ≤ U) :
    W ≤ C * F * (L + 1) * U ^ 2 := by
  calc
    W ≤ C * b * D ^ 3 := hW
    _ = C * (b * D) * D ^ 2 := by ring
    _ ≤ C * (F * (L + 1)) * D ^ 2 :=
      Nat.mul_le_mul_right (D ^ 2) (Nat.mul_le_mul_left C hscaled)
    _ ≤ C * (F * (L + 1)) * U ^ 2 :=
      Nat.mul_le_mul_left (C * (F * (L + 1)))
        (Nat.pow_le_pow_left hDU 2)
    _ = C * F * (L + 1) * U ^ 2 := by ring

/-- Rank-two analogue of `rank_one_cubic_budget_upper`. -/
lemma rank_two_cubic_budget_upper
    {W C b D F L₁ L₂ U : ℕ}
    (hW : W ≤ C * b * D ^ 3)
    (hscaled : b * D ^ 2 ≤ F * ((L₁ + 1) * (L₂ + 1)))
    (hDU : D ≤ U) :
    W ≤ C * F * ((L₁ + 1) * (L₂ + 1)) * U := by
  calc
    W ≤ C * b * D ^ 3 := hW
    _ = C * (b * D ^ 2) * D := by ring
    _ ≤ C * (F * ((L₁ + 1) * (L₂ + 1))) * D :=
      Nat.mul_le_mul_right D (Nat.mul_le_mul_left C hscaled)
    _ ≤ C * (F * ((L₁ + 1) * (L₂ + 1))) * U :=
      Nat.mul_le_mul_left (C * (F * ((L₁ + 1) * (L₂ + 1)))) hDU
    _ = C * F * ((L₁ + 1) * (L₂ + 1)) * U := by ring

lemma succ_side_product_le_four_mul {L₁ L₂ : ℕ}
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) :
    (L₁ + 1) * (L₂ + 1) ≤ 4 * (L₁ * L₂) := by
  have h₁ : L₁ + 1 ≤ 2 * L₁ := by omega
  have h₂ : L₂ + 1 ≤ 2 * L₂ := by omega
  calc
    (L₁ + 1) * (L₂ + 1) ≤ (2 * L₁) * (2 * L₂) :=
      Nat.mul_le_mul h₁ h₂
    _ = 4 * (L₁ * L₂) := by ring

/-- If the second coordinate line itself lies in an ambient interval of
length `H`, then the preserved cubic budget controls the second step with
only the first side length left over.  This is the quantitative input for
Nguyen--Vu's unbalanced residue-class branch. -/
lemma rank_two_second_step_budget_upper
    {W C b D F L₁ L₂ U q₂ H : ℕ}
    (hW : W ≤ C * b * D ^ 3)
    (hscaled : b * D ^ 2 ≤ F * ((L₁ + 1) * (L₂ + 1)))
    (hDU : D ≤ U) (hL₂ : 0 < L₂) (hq₂L₂ : q₂ * L₂ ≤ H) :
    q₂ * W ≤ 2 * C * F * (L₁ + 1) * H * U := by
  have hbudget := rank_two_cubic_budget_upper hW hscaled hDU
  have hsucc : L₂ + 1 ≤ 2 * L₂ := by omega
  have hqsucc : q₂ * (L₂ + 1) ≤ 2 * H := by
    calc
      q₂ * (L₂ + 1) ≤ q₂ * (2 * L₂) := Nat.mul_le_mul_left q₂ hsucc
      _ = 2 * (q₂ * L₂) := by ring
      _ ≤ 2 * H := Nat.mul_le_mul_left 2 hq₂L₂
  calc
    q₂ * W ≤ q₂ * (C * F * ((L₁ + 1) * (L₂ + 1)) * U) :=
      Nat.mul_le_mul_left q₂ hbudget
    _ = C * F * (L₁ + 1) * (q₂ * (L₂ + 1)) * U := by ring
    _ ≤ C * F * (L₁ + 1) * (2 * H) * U := by gcongr
    _ = 2 * C * F * (L₁ + 1) * H * U := by ring

/-- Symmetric form of `rank_two_second_step_budget_upper`. -/
lemma rank_two_first_step_budget_upper
    {W C b D F L₁ L₂ U q₁ H : ℕ}
    (hW : W ≤ C * b * D ^ 3)
    (hscaled : b * D ^ 2 ≤ F * ((L₁ + 1) * (L₂ + 1)))
    (hDU : D ≤ U) (hL₁ : 0 < L₁) (hq₁L₁ : q₁ * L₁ ≤ H) :
    q₁ * W ≤ 2 * C * F * (L₂ + 1) * H * U := by
  have hscaled' : b * D ^ 2 ≤ F * ((L₂ + 1) * (L₁ + 1)) := by
    simpa only [mul_comm] using hscaled
  exact rank_two_second_step_budget_upper hW hscaled' hDU hL₁ hq₁L₁

/-- Properness converts the rank-two carrier size into a sharp bound for its
common step.  Combined with the preserved cubic budget, this is the exact
quantity needed in Nguyen--Vu's divisor iteration. -/
lemma rank_two_common_step_budget_upper
    {W C b D F L₁ L₂ U g H : ℕ}
    (hW : W ≤ C * b * D ^ 3)
    (hscaled : b * D ^ 2 ≤ F * ((L₁ + 1) * (L₂ + 1)))
    (hDU : D ≤ U) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (hgspan : g * L₁ * L₂ ≤ H) :
    g * W ≤ 4 * C * F * H * U := by
  have hbudget := rank_two_cubic_budget_upper hW hscaled hDU
  have hcarrier : g * ((L₁ + 1) * (L₂ + 1)) ≤ 4 * H := by
    calc
      g * ((L₁ + 1) * (L₂ + 1)) ≤ g * (4 * (L₁ * L₂)) :=
        Nat.mul_le_mul_left g (succ_side_product_le_four_mul hL₁ hL₂)
      _ = 4 * (g * L₁ * L₂) := by ring
      _ ≤ 4 * H := Nat.mul_le_mul_left 4 hgspan
  calc
    g * W ≤ g * (C * F * ((L₁ + 1) * (L₂ + 1)) * U) :=
      Nat.mul_le_mul_left g hbudget
    _ = C * F * (g * ((L₁ + 1) * (L₂ + 1))) * U := by ring
    _ ≤ C * F * (4 * H) * U := by gcongr
    _ = 4 * C * F * H * U := by ring

/-- Rank-one counterpart of `rank_two_common_step_budget_upper`. -/
lemma rank_one_step_budget_upper
    {W C b D F L U q H : ℕ}
    (hW : W ≤ C * b * D ^ 3)
    (hscaled : b * D ≤ F * (L + 1))
    (hDU : D ≤ U) (hL : 0 < L) (hqL : q * L ≤ H) :
    q * W ≤ 2 * C * F * H * U ^ 2 := by
  have hbudget := rank_one_cubic_budget_upper hW hscaled hDU
  have hsucc : L + 1 ≤ 2 * L := by omega
  have hqsucc : q * (L + 1) ≤ 2 * H := by
    calc
      q * (L + 1) ≤ q * (2 * L) := Nat.mul_le_mul_left q hsucc
      _ = 2 * (q * L) := by ring
      _ ≤ 2 * H := Nat.mul_le_mul_left 2 hqL
  calc
    q * W ≤ q * (C * F * (L + 1) * U ^ 2) :=
      Nat.mul_le_mul_left q hbudget
    _ = C * F * (q * (L + 1)) * U ^ 2 := by ring
    _ ≤ C * F * (2 * H) * U ^ 2 := by gcongr
    _ = 2 * C * F * H * U ^ 2 := by ring

/-- Any requested rank-one side length follows once the preserved cubic
budget dominates its corresponding upper bound. -/
lemma rank_one_side_gt_of_cubic_budget
    {W C b D F L U B : ℕ}
    (hW : W ≤ C * b * D ^ 3)
    (hscaled : b * D ≤ F * (L + 1))
    (hDU : D ≤ U)
    (hlarge : C * F * (B + 1) * U ^ 2 < W) :
    B < L := by
  have hupper := rank_one_cubic_budget_upper hW hscaled hDU
  have hlt : C * F * (B + 1) * U ^ 2 <
      C * F * (L + 1) * U ^ 2 := hlarge.trans_le hupper
  have hCFU : 0 < C * F * U ^ 2 := by
    by_contra hz
    have hz' : C * F * U ^ 2 = 0 := Nat.eq_zero_of_not_pos hz
    have : C * F * (B + 1) * U ^ 2 = 0 := by
      calc
        C * F * (B + 1) * U ^ 2 = (C * F * U ^ 2) * (B + 1) := by ring
        _ = 0 := by rw [hz']; simp
    have hupperZero : C * F * (L + 1) * U ^ 2 = 0 := by
      calc
        C * F * (L + 1) * U ^ 2 = (C * F * U ^ 2) * (L + 1) := by ring
        _ = 0 := by rw [hz']; simp
    rw [this] at hlarge
    rw [hupperZero] at hupper
    omega
  have hfactor : 0 < C * F * U ^ 2 := hCFU
  have : (C * F * U ^ 2) * (B + 1) <
      (C * F * U ^ 2) * (L + 1) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hlt
  have hBL := (Nat.mul_lt_mul_left hfactor).1 this
  omega

/-- Endpoint membership in an ambient interval bounds the total span of a
rank-one natural progression. -/
lemma natAP_span_le_of_subsetSum_bound
    {A : Finset ℕ} {r q L H : ℕ}
    (hbound : A.subsetSum ⊆ Finset.Icc 0 H)
    (hAP : natAP r q L ⊆ A.subsetSum) :
    q * L ≤ H := by
  have hend : r + q * L ∈ A.subsetSum := by
    apply hAP
    exact mem_natAP_iff.mpr ⟨L, le_rfl, rfl⟩
  have := (Finset.mem_Icc.mp (hbound hend)).2
  omega

/-- Endpoint membership similarly bounds the combined span of a natural
rank-two progression. -/
lemma natGAP_two_span_le_of_subsetSum_bound
    {A : Finset ℕ} {r q₁ q₂ L₁ L₂ H : ℕ}
    (hbound : A.subsetSum ⊆ Finset.Icc 0 H)
    (hmem : ∀ x ≤ L₁, ∀ y ≤ L₂,
      r + q₁ * x + q₂ * y ∈ A.subsetSum) :
    q₁ * L₁ + q₂ * L₂ ≤ H := by
  have hend := (Finset.mem_Icc.mp (hbound (hmem L₁ le_rfl L₂ le_rfl))).2
  omega

/-- Properness of a positive rank-two progression forces one normalized step
past the opposite side length.  Quantitatively, the common divisor times the
product of the two side lengths is bounded by the total span.  This is the
collision argument used in Nguyen--Vu's rank-two case. -/
lemma gcd_mul_side_product_le_span_of_injective
    {r q₁ q₂ L₁ L₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hinj : ∀ x₁ ≤ L₁, ∀ y₁ ≤ L₂,
      ∀ x₂ ≤ L₁, ∀ y₂ ≤ L₂,
        r + q₁ * x₁ + q₂ * y₁ = r + q₁ * x₂ + q₂ * y₂ →
        x₁ = x₂ ∧ y₁ = y₂) :
    q₁.gcd q₂ * L₁ * L₂ ≤ q₁ * L₁ + q₂ * L₂ := by
  let g := q₁.gcd q₂
  let a := q₁ / g
  let b := q₂ / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left q₂ hq₁
  have hga : g * a = q₁ := by
    dsimp only [g, a]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left q₁ q₂)
  have hgb : g * b = q₂ := by
    dsimp only [g, b]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_right q₁ q₂)
  have ha : 0 < a := by
    dsimp only [a, g]
    exact Nat.div_pos (Nat.le_of_dvd hq₁ (Nat.gcd_dvd_left q₁ q₂)) hg
  have hb : 0 < b := by
    dsimp only [b, g]
    exact Nat.div_pos (Nat.le_of_dvd hq₂ (Nat.gcd_dvd_right q₁ q₂)) hg
  have halt : L₁ < b ∨ L₂ < a := by
    by_contra hnot
    push_neg at hnot
    have hcollision :
        r + q₁ * b + q₂ * 0 = r + q₁ * 0 + q₂ * a := by
      rw [← hga, ← hgb]
      ring
    have heq := hinj b hnot.1 0 (Nat.zero_le L₂)
      0 (Nat.zero_le L₁) a hnot.2 hcollision
    omega
  rcases halt with hLb | hLa
  · have hgL : g * L₁ ≤ q₂ := by
      rw [← hgb]
      exact Nat.mul_le_mul_left g hLb.le
    calc
      q₁.gcd q₂ * L₁ * L₂ = (g * L₁) * L₂ := by rfl
      _ ≤ q₂ * L₂ := Nat.mul_le_mul_right L₂ hgL
      _ ≤ q₁ * L₁ + q₂ * L₂ := Nat.le_add_left _ _
  · have hgL : g * L₂ ≤ q₁ := by
      rw [← hga]
      exact Nat.mul_le_mul_left g hLa.le
    calc
      q₁.gcd q₂ * L₁ * L₂ = (g * L₂) * L₁ := by
        dsimp only [g]
        ring
      _ ≤ q₁ * L₁ := Nat.mul_le_mul_right L₁ hgL
      _ ≤ q₁ * L₁ + q₂ * L₂ := Nat.le_add_right _ _

lemma carrier_card_eq_rank_one
    (R : GeneralizedAP) (hR : R.Proper) (hrank : R.rank = 1) :
    R.carrier.card = R.length ⟨0, by omega⟩ + 1 := by
  rw [R.card_carrier_of_proper hR]
  have huniv : (Finset.univ : Finset (Fin R.rank)) = {⟨0, by omega⟩} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply Fin.ext
    have hi := i.isLt
    omega
  rw [huniv]
  simp

lemma carrier_card_eq_rank_two
    (R : GeneralizedAP) (hR : R.Proper) (hrank : R.rank = 2) :
    R.carrier.card =
      (R.length ⟨0, by omega⟩ + 1) * (R.length ⟨1, by omega⟩ + 1) := by
  rw [R.card_carrier_of_proper hR]
  let i₀ : Fin R.rank := ⟨0, by omega⟩
  let i₁ : Fin R.rank := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by
    intro h
    have := congrArg Fin.val h
    simp [i₀, i₁] at this
  have huniv : (Finset.univ : Finset (Fin R.rank)) = {i₀, i₁} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    have hlt := i.isLt
    have : i.val = 0 ∨ i.val = 1 := by omega
    rcases this with hzero | hone
    · exact Or.inl (Fin.ext (by simpa [i₀] using hzero))
    · exact Or.inr (Fin.ext (by simpa [i₁] using hone))
  rw [huniv]
  simp [i₀, i₁, hi]

lemma nvStoppedBudgetScaledCardFactor_pos (c : ℕ) (hc : 1 ≤ c) :
    0 < nvStoppedBudgetScaledCardFactor c := by
  have hcpos : 0 < c := by omega
  have hKpos : 0 < c ^ 2 := by positivity
  have hrank : 0 < freimanRank (c ^ 2) := freimanRank_pos _
  have hcyclic : 0 < freimanCyclicCardFactor (c ^ 2) := by
    unfold freimanCyclicCardFactor
    exact Nat.ceil_pos.mpr (by
      have := freimanCyclicDenominator_pos (c ^ 2)
      positivity)
  have hfreiman : 0 < freimanSizeFactor (c ^ 2) := by
    unfold freimanSizeFactor
    dsimp
    positivity
  have hmodel : 0 < nvStoppingModelFactor (c ^ 2) 1 := by
    unfold nvStoppingModelFactor
    dsimp
    positivity
  have hdensity : 0 < nvStoppedDensity c := by
    unfold nvStoppedDensity
    positivity
  have hstandard :
      0 < GeneralizedAP.nvDenseProperFactor (nvStoppedDensity c)
        (freimanRank (c ^ 2)) :=
    GeneralizedAP.nvDenseProperFactor_pos hdensity
  have huniform : 0 <
      GeneralizedAP.nvDenseProperFactor (nvStoppedDensity c)
          (freimanRank (c ^ 2)) *
        (nvStoppedDenseCount c + 1) ^ (freimanRank (c ^ 2)) := by
    positivity
  have hstopped : 0 < nvStoppedRankReductionCardFactor c := by
    unfold nvStoppedRankReductionCardFactor
    dsimp
    exact Nat.mul_pos (pow_pos huniform _) 
      (GeneralizedAP.nvRankReductionFactor_pos _)
  unfold nvStoppedBudgetScaledCardFactor
  exact Nat.mul_pos hstopped
    (GeneralizedAP.nvBudgetRankReductionFactor_pos _)

/-- Convert the scale-sensitive rank-one cardinality estimate into any
requested side-length lower bound. -/
lemma rank_one_side_gt_of_scaled
    {amin M K F D L B : ℕ}
    (hK : 0 < K) (hF : 0 < F)
    (hMD : M < K * D)
    (hscaled : amin * D ≤ F * (L + 1))
    (hlarge : K * F * (B + 1) < amin * M) :
    B < L := by
  have hamin : 0 < amin := by
    by_contra h
    have haz : amin = 0 := Nat.eq_zero_of_not_pos h
    simp only [haz, zero_mul] at hlarge
    exact (Nat.not_lt_zero _ hlarge)
  have hupper : amin * M < K * F * (L + 1) := by
    calc
      amin * M < amin * (K * D) := (Nat.mul_lt_mul_left hamin).2 hMD
      _ = K * (amin * D) := by ring
      _ ≤ K * (F * (L + 1)) := Nat.mul_le_mul_left K hscaled
      _ = K * F * (L + 1) := by ring
  have hmul : K * F * (B + 1) < K * F * (L + 1) :=
    hlarge.trans hupper
  have hKF : 0 < K * F := Nat.mul_pos hK hF
  have := (Nat.mul_lt_mul_left hKF).mp (by
    simpa only [mul_assoc] using hmul)
  omega

/-- The sharp one-dimensional square estimate follows from a single squared
side-length inequality and the ambient bound `q*L ≤ H`. -/
lemma rank_one_location_bounds
    {p q L H : ℕ} (hp : 0 < p) (hq : 0 < q) (hL : 0 < L)
    (hqL : q * L ≤ H) (hbig : 64 * p * H ≤ L ^ 2) :
    p * q ≤ L ∧
      4 * (p * q) * (Nat.sqrt (H / (p * q ^ 2)) + 1) ≤ L := by
  have hpqL : p * q * L ≤ p * H := by
    calc
      p * q * L = p * (q * L) := by ring
      _ ≤ p * H := Nat.mul_le_mul_left p hqL
  have hpqEight : 8 * (p * q) ≤ L := by
    nlinarith
  let x := Nat.sqrt (H / (p * q ^ 2))
  have hxSq : x ^ 2 ≤ H / (p * q ^ 2) := Nat.sqrt_le' _
  have hpq₂ : 0 < p * q ^ 2 := by positivity
  have hdenom : p * q ^ 2 * (H / (p * q ^ 2)) ≤ H :=
    Nat.mul_div_le H (p * q ^ 2)
  have hxAmbient : p * q ^ 2 * x ^ 2 ≤ H := by
    exact (Nat.mul_le_mul_left (p * q ^ 2) hxSq).trans hdenom
  have hpqxEight : 8 * (p * q) * x ≤ L := by
    nlinarith
  constructor
  · calc
      p * q = 1 * (p * q) := by simp
      _ ≤ 8 * (p * q) := Nat.mul_le_mul_right (p * q) (by norm_num)
      _ ≤ L := by simpa only [mul_assoc] using hpqEight
  · dsimp only [x] at hpqxEight ⊢
    nlinarith

lemma square_bound_of_sqrt_succ (n : ℕ) :
    n ≤ (Nat.sqrt n + 1) ^ 2 := by
  exact (Nat.lt_succ_sqrt' n).le

/-- Complete rank-one terminal branch directly in the invariant form emitted
by the robust Nguyen--Vu structure theorem. -/
theorem rank_one_terminal_of_cubic_budget
    {A B : Finset ℕ} {N p n Ccover W C₀ b D F U : ℕ}
    {R : GeneralizedAP} {t : ℤ} {Z : Finset ℤ}
    (hp : 0 < p) (hAN : A ⊆ Finset.Icc 1 N) (hBA : B ⊆ A)
    (hR : R.Proper) (hrank : R.rank = 1)
    (hside : ∀ i : Fin R.rank, 0 < R.length i)
    (hcontain : (({t} : Finset ℤ) + R.carrier) +
      natToIntFinset B.subsetSum ⊆ natToIntFinset A.subsetSum)
    (hcover : natToIntFinset B ⊆
      Z + iteratedDifference (n + 1) R.carrier)
    (hZ : Z.card ≤ Ccover)
    (hW : W ≤ C₀ * b * D ^ 3)
    (hscaled : b * D ^ R.rank ≤ F * R.carrier.card)
    (hDU : D ≤ U)
    (hlarge : C₀ * F *
      (8 * (Nat.sqrt (p * (A.card * N)) + 1) + 1) * U ^ 2 < W) :
    HasPMultipleSquareSubsetSum p A ∨
      ∃ d : ℕ, ∃ E : Finset ℕ,
        E ⊆ B ∧ 1 < d ∧
        B.card ≤ E.card +
          Ccover * (Nat.log 2 (A.card * N) *
            (nvQuadraticAdjustmentConstant *
              (Nat.sqrt (p * (A.card * N)) + 1))) ∧
        ∀ a ∈ E, d ∣ a := by
  obtain ⟨r, q, L, hq, _hrbase, hqstep, hL, hfamily⟩ :=
    exists_natAP_family_of_translated_rank_one_GAP
      R t hR hrank hside hcontain
  have hscaled₁ : b * D ≤ F * (L + 1) := by
    have hcard := carrier_card_eq_rank_one R hR hrank
    rw [hrank, pow_one, hcard] at hscaled
    simpa only [hL] using hscaled
  have hLlarge : 8 * (Nat.sqrt (p * (A.card * N)) + 1) < L :=
    rank_one_side_gt_of_cubic_budget hW hscaled₁ hDU hlarge
  have hLpos : 0 < L := by omega
  have hsumBound : A.subsetSum ⊆ Finset.Icc 0 (A.card * N) :=
    NVGeneration.subsetSum_subset_Icc_of_subset
      (U := A) (A := A) Finset.Subset.rfl hAN le_rfl
  have hzero : 0 ∈ B.subsetSum := by simp
  have hAP₀ : natAP r q L ⊆ A.subsetSum := by
    simpa only [Nat.add_zero] using hfamily 0 hzero
  have hqL : q * L ≤ A.card * N :=
    natAP_span_le_of_subsetSum_bound hsumBound hAP₀
  have hqH : q ≤ A.card * N := by
    calc
      q = q * 1 := by simp
      _ ≤ q * L := Nat.mul_le_mul_left q (by omega)
      _ ≤ A.card * N := hqL
  have hsqrt : p * (A.card * N) ≤
      (Nat.sqrt (p * (A.card * N)) + 1) ^ 2 :=
    square_bound_of_sqrt_succ _
  have hbig : 64 * p * (A.card * N) ≤ L ^ 2 := by
    have hBsq :
        (8 * (Nat.sqrt (p * (A.card * N)) + 1)) ^ 2 < L ^ 2 := by
      nlinarith
    calc
      64 * p * (A.card * N) = 64 * (p * (A.card * N)) := by ring
      _ ≤ 64 * (Nat.sqrt (p * (A.card * N)) + 1) ^ 2 :=
        Nat.mul_le_mul_left 64 hsqrt
      _ = (8 * (Nat.sqrt (p * (A.card * N)) + 1)) ^ 2 := by ring
      _ ≤ L ^ 2 := hBsq.le
  obtain ⟨hshort, hlong⟩ :=
    rank_one_location_bounds hp hq hLpos hqL hbig
  rcases rank_one_square_or_common_divisor (t := t) hp hq hAN hBA hR hrank
      hside hqstep hfamily hcover hZ hshort hlong with
    hsquare | ⟨d, E, hEB, hd, hdq, hcard, hdiv⟩
  · exact Or.inl hsquare
  · refine Or.inr ⟨d, E, hEB, hd, ?_, hdiv⟩
    have hsqrtMono : Nat.sqrt (p * q) ≤
        Nat.sqrt (p * (A.card * N)) :=
      Nat.sqrt_le_sqrt (Nat.mul_le_mul_left p hqH)
    have hloss :
        Ccover * (Nat.log 2 q *
          (nvQuadraticAdjustmentConstant * (Nat.sqrt (p * q) + 1))) ≤
        Ccover * (Nat.log 2 (A.card * N) *
            (nvQuadraticAdjustmentConstant *
              (Nat.sqrt (p * (A.card * N)) + 1))) := by
      gcongr
    exact hcard.trans (Nat.add_le_add_left hloss E.card)

/-- Complete rank-two residue/divisor branch once the archimedean locator is
available.  Its loss is uniformly majorized by the ambient subset-sum
interval, which is the form required by divisor descent. -/
theorem rank_two_terminal_of_locator
    {A B : Finset ℕ} {N p n Ccover : ℕ}
    {R : GeneralizedAP} {t : ℤ} {Z : Finset ℤ}
    (hp : 0 < p) (hAN : A ⊆ Finset.Icc 1 N)
    (hR : R.Proper) (hrank : R.rank = 2)
    (hside : ∀ i : Fin R.rank, 0 < R.length i)
    (hcontain : (({t} : Finset ℤ) + R.carrier) +
      natToIntFinset B.subsetSum ⊆ natToIntFinset A.subsetSum)
    (hcover : natToIntFinset B ⊆
      Z + iteratedDifference (n + 1) R.carrier)
    (hZ : Z.card ≤ Ccover)
    (hlocator : ∀ {r q₁ q₂ L₁ L₂ : ℕ},
      0 < q₁ → 0 < q₂ →
      (∀ u ∈ B.subsetSum, ∀ x ≤ L₁, ∀ y ≤ L₂,
        r + u + q₁ * x + q₂ * y ∈ A.subsetSum) →
      (∀ u ∈ B.subsetSum, ∀ z₀ : ℕ, ∀ v : ℤ,
        ((r + u : ℕ) : ℤ) =
            (p : ℤ) * (z₀ : ℤ) ^ 2 + v * (q₁.gcd q₂ : ℕ) →
          ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
            0 < p * w ^ 2 ∧
            r + u + q₁ * x + q₂ * y = p * w ^ 2)) :
    HasPMultipleSquareSubsetSum p A ∨
      ∃ d : ℕ, ∃ E : Finset ℕ,
        E ⊆ B ∧ 1 < d ∧
        B.card ≤ E.card +
          Ccover * (Nat.log 2 (A.card * N) *
            (nvQuadraticAdjustmentConstant *
              (Nat.sqrt (p * (A.card * N)) + 1))) ∧
        ∀ a ∈ E, d ∣ a := by
  obtain ⟨r, q₁, q₂, L₁, L₂, hq₁, hq₂, _hrbase, hq₁step, hq₂step,
      hL₁, hL₂, hfamily, _hinj⟩ :=
    exists_natGAP_two_family_of_translated_rank_two_GAP
      R t hR hrank hside hcontain
  have hsumBound : A.subsetSum ⊆ Finset.Icc 0 (A.card * N) :=
    NVGeneration.subsetSum_subset_Icc_of_subset
      (U := A) (A := A) Finset.Subset.rfl hAN le_rfl
  have hzero : 0 ∈ B.subsetSum := by simp
  have hspan : q₁ * L₁ + q₂ * L₂ ≤ A.card * N := by
    apply natGAP_two_span_le_of_subsetSum_bound hsumBound
    intro x hx y hy
    simpa only [Nat.add_zero] using hfamily 0 hzero x hx y hy
  have hL₁pos : 0 < L₁ := by simpa only [hL₁] using hside ⟨0, by omega⟩
  have hq₁H : q₁ ≤ A.card * N := by
    have : q₁ ≤ q₁ * L₁ := by
      calc
        q₁ = q₁ * 1 := by simp
        _ ≤ q₁ * L₁ := Nat.mul_le_mul_left q₁ (by omega)
    omega
  have hgH : q₁.gcd q₂ ≤ A.card * N :=
    (Nat.gcd_le_left q₂ hq₁).trans hq₁H
  rcases rank_two_square_or_common_divisor_of_locator hp hq₁ hq₂
      hR hrank hside hq₁step hq₂step hfamily hcover hZ
      (hlocator hq₁ hq₂ hfamily) with
    hsquare | ⟨d, E, hEB, hd, hdg, hcard, hdiv⟩
  · exact Or.inl hsquare
  · refine Or.inr ⟨d, E, hEB, hd, ?_, hdiv⟩
    have hsqrtMono : Nat.sqrt (p * (q₁.gcd q₂)) ≤
        Nat.sqrt (p * (A.card * N)) :=
      Nat.sqrt_le_sqrt (Nat.mul_le_mul_left p hgH)
    have hloss :
        Ccover * (Nat.log 2 (q₁.gcd q₂) *
          (nvQuadraticAdjustmentConstant *
            (Nat.sqrt (p * (q₁.gcd q₂)) + 1))) ≤
        Ccover * (Nat.log 2 (A.card * N) *
          (nvQuadraticAdjustmentConstant *
            (Nat.sqrt (p * (A.card * N)) + 1))) := by
      gcongr
    exact hcard.trans (Nat.add_le_add_left hloss E.card)

/-! ## Abstract common-divisor descent

This is the exact induction used at the end of Nguyen--Vu.  All analytic and
additive-combinatorial work is isolated in the one-step hypothesis. -/

theorem has_pMultipleSquareSubsetSum_of_descent_step
    {N₀ B : ℕ}
    (hstep : ∀ (p N : ℕ) (A : Finset ℕ),
      0 < p → p * N ≤ N₀ → A ⊆ Finset.Icc 1 N → B < A.card →
        HasPMultipleSquareSubsetSum p A ∨
          ∃ d : ℕ, ∃ D : Finset ℕ,
            D ⊆ A ∧ 1 < d ∧ (∀ a ∈ D, d ∣ a) ∧ B < D.card) :
    ∀ (N p : ℕ) (A : Finset ℕ),
      0 < p → p * N ≤ N₀ → A ⊆ Finset.Icc 1 N → B < A.card →
        HasPMultipleSquareSubsetSum p A := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro p A hp hpN hAN hBA
      rcases hstep p N A hp hpN hAN hBA with
        hsquare | ⟨d, D, hDA, hd, hdiv, hBD⟩
      · exact hsquare
      · have hAne : A.Nonempty := by
          exact Finset.card_pos.mp (by omega)
        obtain ⟨a, haA⟩ := hAne
        have hNpos : 0 < N := by
          have haIcc := Finset.mem_Icc.mp (hAN haA)
          omega
        have hdpos : 0 < d := by omega
        have hNlt : N / d < N := Nat.div_lt_self hNpos hd
        let A' := scaleDown d D
        have hA'Icc : A' ⊆ Finset.Icc 1 (N / d) := by
          dsimp only [A']
          exact scaleDown_subset_Icc hdpos hdiv (hDA.trans hAN)
        have hcardA' : A'.card = D.card := by
          dsimp only [A']
          exact card_scaleDown_of_dvd hdiv
        have hBA' : B < A'.card := by simpa only [hcardA'] using hBD
        have hpdN : (p * d) * (N / d) ≤ N₀ := by
          calc
            (p * d) * (N / d) = p * (d * (N / d)) := by ring
            _ ≤ p * N := Nat.mul_le_mul_left p (Nat.mul_div_le N d)
            _ ≤ N₀ := hpN
        obtain ⟨T, hTA', hTne, z, hTsum⟩ :=
          ih (N / d) hNlt (p * d) A' (Nat.mul_pos hp hdpos)
            hpdN hA'Icc hBA'
        obtain ⟨S, hSD, hSsum⟩ :=
          lift_p_mul_square_from_scaleDown hdiv hTA' hTsum
        have hTsumPos : 0 < ∑ t ∈ T, t := by
          apply Finset.sum_pos
          · intro t ht
            exact (Finset.mem_Icc.mp (hA'Icc (hTA' ht))).1
          · exact hTne
        have hSpos : 0 < ∑ a ∈ S, a := by
          rw [hSsum]
          have hzpos : 0 < z := by
            by_contra hz
            have hz0 : z = 0 := Nat.eq_zero_of_not_pos hz
            have hzero : ∑ t ∈ T, t = 0 := by
              rw [hTsum, hz0]
              norm_num
            omega
          positivity
        refine ⟨S, hSD.trans hDA, ?_, d * z, hSsum⟩
        exact Finset.nonempty_iff_ne_empty.mpr (by
          intro hS
          subst S
          simp at hSpos)

/-- The quantitative Nguyen--Vu descent.  A divisor step spends at most one
copy of `L`, while division by `d > 1` lowers the binary logarithm of the
ambient interval by at least one. -/
theorem has_pMultipleSquareSubsetSum_of_logarithmic_descent_step
    {N₀ L : ℕ} (hL : 0 < L)
    (hstep : ∀ (p N : ℕ) (A : Finset ℕ),
      0 < p → p * N ≤ N₀ → A ⊆ Finset.Icc 1 N →
      L * (Nat.log 2 N + 1) < A.card →
        HasPMultipleSquareSubsetSum p A ∨
          ∃ d : ℕ, ∃ D : Finset ℕ,
            D ⊆ A ∧ 1 < d ∧ (∀ a ∈ D, d ∣ a) ∧
            A.card ≤ D.card + L) :
    ∀ (N p : ℕ) (A : Finset ℕ),
      0 < p → p * N ≤ N₀ → A ⊆ Finset.Icc 1 N →
      L * (Nat.log 2 N + 1) < A.card →
        HasPMultipleSquareSubsetSum p A := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro p A hp hpN hAN hlarge
      rcases hstep p N A hp hpN hAN hlarge with
        hsquare | ⟨d, D, hDA, hd, hdiv, hcard⟩
      · exact hsquare
      · have hDlarge : L * Nat.log 2 N < D.card := by
          have hsplit : L * (Nat.log 2 N + 1) =
              L * Nat.log 2 N + L := by ring
          rw [hsplit] at hlarge
          omega
        have hDne : D.Nonempty := by
          exact Finset.card_pos.mp (by omega)
        obtain ⟨a, haD⟩ := hDne
        have haIcc := Finset.mem_Icc.mp (hAN (hDA haD))
        have hdA : d ≤ a := Nat.le_of_dvd haIcc.1 (hdiv a haD)
        have hdN : d ≤ N := hdA.trans haIcc.2
        have hNpos : 0 < N := by omega
        have hdpos : 0 < d := by omega
        have hNlt : N / d < N := Nat.div_lt_self hNpos hd
        have hhalf : N / d ≤ N / 2 :=
          Nat.div_le_div_left (by omega : 2 ≤ d) (by norm_num)
        have hlogHalf : Nat.log 2 (N / 2) = Nat.log 2 N - 1 :=
          Nat.log_div_base 2 N
        have hlogNpos : 0 < Nat.log 2 N := by
          have htwoN : 2 ≤ N := (show 2 ≤ d by omega).trans hdN
          exact Nat.log_pos (by norm_num) htwoN
        have hlogDrop : Nat.log 2 (N / d) + 1 ≤ Nat.log 2 N := by
          have hmono : Nat.log 2 (N / d) ≤ Nat.log 2 (N / 2) :=
            Nat.log_mono_right hhalf
          rw [hlogHalf] at hmono
          omega
        let A' := scaleDown d D
        have hA'Icc : A' ⊆ Finset.Icc 1 (N / d) := by
          dsimp only [A']
          exact scaleDown_subset_Icc hdpos hdiv (hDA.trans hAN)
        have hcardA' : A'.card = D.card := by
          dsimp only [A']
          exact card_scaleDown_of_dvd hdiv
        have hlarge' : L * (Nat.log 2 (N / d) + 1) < A'.card := by
          rw [hcardA']
          exact (Nat.mul_le_mul_left L hlogDrop).trans_lt hDlarge
        have hpdN : (p * d) * (N / d) ≤ N₀ := by
          calc
            (p * d) * (N / d) = p * (d * (N / d)) := by ring
            _ ≤ p * N := Nat.mul_le_mul_left p (Nat.mul_div_le N d)
            _ ≤ N₀ := hpN
        obtain ⟨T, hTA', hTne, z, hTsum⟩ :=
          ih (N / d) hNlt (p * d) A' (Nat.mul_pos hp hdpos)
            hpdN hA'Icc hlarge'
        obtain ⟨S, hSD, hSsum⟩ :=
          lift_p_mul_square_from_scaleDown hdiv hTA' hTsum
        have hTsumPos : 0 < ∑ t ∈ T, t := by
          apply Finset.sum_pos
          · intro t ht
            exact (Finset.mem_Icc.mp (hA'Icc (hTA' ht))).1
          · exact hTne
        have hSpos : 0 < ∑ a ∈ S, a := by
          rw [hSsum]
          have hzpos : 0 < z := by
            by_contra hz
            have hz0 : z = 0 := Nat.eq_zero_of_not_pos hz
            have hzero : ∑ t ∈ T, t = 0 := by
              rw [hTsum, hz0]
              norm_num
            omega
          positivity
        refine ⟨S, hSD.trans hDA, ?_, d * z, hSsum⟩
        exact Finset.nonempty_iff_ne_empty.mpr (by
          intro hS
          subst S
          simp at hSpos)

/-! ## Conversion of the dyadic Nguyen--Vu scale to the stated real bound -/

lemma four_pow_log_sixty_four_le_nthRoot
    {N : ℕ} (hN : 0 < N) :
    (4 ^ Nat.log 64 N : ℝ) ≤ Real.nthRoot 3 N := by
  have hcubeNat : (4 ^ Nat.log 64 N) ^ 3 ≤ N := by
    rw [four_pow_cube]
    exact (log_sixty_four_scale_bounds hN).1
  have hcube : ((4 ^ Nat.log 64 N : ℕ) : ℝ) ^ 3 ≤ (N : ℝ) := by
    exact_mod_cast hcubeNat
  rw [nthRoot_three_natCast]
  have hrootNonneg : 0 ≤ (N : ℝ) ^ ((3 : ℝ)⁻¹) :=
    Real.rpow_nonneg (by positivity) _
  have hrootPow : ((N : ℝ) ^ ((3 : ℝ)⁻¹)) ^ 3 = N :=
    Real.rpow_inv_natCast_pow (n := 3) (by positivity) (by norm_num)
  apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num)
      hrootNonneg
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    hcube.trans_eq hrootPow.symm

lemma nat_log_two_add_one_cast_le_real_log
    {N : ℕ} (hlog : (1 : ℝ) ≤ Real.log N) :
    ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤
      ((Real.log 2)⁻¹ + 1) * Real.log N := by
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hbase := Real.natLog_le_logb N 2
  change (Nat.log 2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 at hbase
  push_cast
  calc
    (Nat.log 2 N : ℝ) + 1 ≤
        Real.log (N : ℝ) / Real.log 2 + 1 := by nlinarith [hbase]
    _ ≤ ((Real.log 2)⁻¹ + 1) * Real.log N := by
      rw [div_eq_mul_inv]
      nlinarith [inv_pos.mpr htwo]

/-- It suffices to prove square forcing at the natural dyadic scale used by
the stopping-time argument.  This wrapper performs all conversions to the
exact `Real.nthRoot`/real-log expression in the formal-conjectures theorem. -/
theorem nguyen_vu_of_eventual_dyadic_square_forcing
    (P K : ℕ) (hP : 0 < P) (hK : 0 < K)
    (hforce : ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Finset.Icc 1 N,
      K * 4 ^ Nat.log 64 N * (Nat.log 2 N + 1) ^ P < A.card →
        ∃ S ⊆ A, S ≠ ∅ ∧ IsSquare (∑ a ∈ S, a)) :
    ∃ᵉ (O > 0) (O' > 0), ∀ᶠ N in atTop,
      (MaxNotSqSum N : ℝ) ≤
        O' * Real.nthRoot 3 N * (N : ℝ).log ^ O := by
  let Clog : ℝ := (Real.log 2)⁻¹ + 1
  let K' : ℝ := K * Clog ^ P
  have hClog : 0 < Clog := by
    dsimp only [Clog]
    have := inv_pos.mpr (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    positivity
  have hK' : 0 < K' := by
    dsimp only [K']
    positivity
  have ht : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevlog : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.log N :=
    tendsto_atTop.mp ht 1
  apply nguyen_vu_of_eventual_square_forcing P hP K' hK'
  filter_upwards [hforce, hevlog] with N hforceN hlog
  intro A hAN hlarge
  have hNpos : 0 < N := by
    by_contra hN
    have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
    subst N
    norm_num at hlog
  have hscale := four_pow_log_sixty_four_le_nthRoot hNpos
  have hrootNonneg : 0 ≤ Real.nthRoot 3 N := by
    exact (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ Nat.log 64 N).trans hscale
  have hlogScale := nat_log_two_add_one_cast_le_real_log hlog
  have hlogNonneg : 0 ≤ Real.log (N : ℝ) := by linarith
  have hClogLog : 0 ≤ Clog * Real.log (N : ℝ) := by positivity
  have hthreshold :
      ((K * 4 ^ Nat.log 64 N * (Nat.log 2 N + 1) ^ P : ℕ) : ℝ) ≤
        K' * Real.nthRoot 3 N * Real.log (N : ℝ) ^ P := by
    push_cast
    calc
      (K : ℝ) * (4 ^ Nat.log 64 N : ℝ) *
          ((Nat.log 2 N : ℝ) + 1) ^ P ≤
        (K : ℝ) * Real.nthRoot 3 N *
          ((Nat.log 2 N : ℝ) + 1) ^ P := by
            gcongr
      _ ≤ (K : ℝ) * Real.nthRoot 3 N *
          (Clog * Real.log (N : ℝ)) ^ P := by
            have hlogScale' : (Nat.log 2 N : ℝ) + 1 ≤
                Clog * Real.log (N : ℝ) := by
              simpa only [Clog, Nat.cast_add, Nat.cast_one] using hlogScale
            have hpowLog : ((Nat.log 2 N : ℝ) + 1) ^ P ≤
                (Clog * Real.log (N : ℝ)) ^ P :=
              pow_le_pow_left₀ (by positivity) hlogScale' P
            exact mul_le_mul_of_nonneg_left hpowLog
              (mul_nonneg (Nat.cast_nonneg K) hrootNonneg)
      _ = K' * Real.nthRoot 3 N * Real.log (N : ℝ) ^ P := by
        simp only [K', mul_pow]
        ring
  have hnatReal :
      ((K * 4 ^ Nat.log 64 N * (Nat.log 2 N + 1) ^ P : ℕ) : ℝ) <
        (A.card : ℝ) := hthreshold.trans_lt hlarge
  have hnat : K * 4 ^ Nat.log 64 N * (Nat.log 2 N + 1) ^ P < A.card := by
    exact_mod_cast hnatReal
  exact hforceN A hAN hnat

/-! ## The quantitative parameter package

The remaining proof uses one deliberately wasteful fixed constant and two
widely separated powers of the binary logarithm.  This is the usual
``take the constant and the logarithmic exponent sufficiently large'' step in
Nguyen--Vu, made into actual natural-number definitions. -/

noncomputable def nvAggregateWeylConstant : ℝ :=
  Classical.choose exists_aggregate_low_bound_of_corrected_weyl_budget

lemma nvAggregateWeylConstant_pos : 0 < nvAggregateWeylConstant :=
  (Classical.choose_spec
    exists_aggregate_low_bound_of_corrected_weyl_budget).1

noncomputable def nvAggregateWeylExponent : ℕ :=
  Classical.choose (Classical.choose_spec
    exists_aggregate_low_bound_of_corrected_weyl_budget).2

lemma nvAggregateWeylExponent_pos : 0 < nvAggregateWeylExponent :=
  (Classical.choose_spec (Classical.choose_spec
    exists_aggregate_low_bound_of_corrected_weyl_budget).2).1

lemma nvAggregateWeylConstant_spec :
    ∀ q A B Z L M : ℕ,
      let r := A.gcd q
      let A' := A / r
      let q' := q / r
      let X := 2 * M * L
      let D := Nat.sqrt (Nat.sqrt X)
      0 < q → 0 < L → 3 ≤ D → q' - 1 ≤ X → q' * D ≤ X →
      16 * (M : ℝ) *
          ((M : ℝ) * L +
            8 * ((M : ℝ) * L ^ 2 * q'.divisors.card / q') +
            4 * nvAggregateWeylConstant * (X : ℝ) *
              Real.log (X : ℝ) ^ nvAggregateWeylExponent) <
        (L : ℝ) ^ 2 →
      4 * (∑ d ∈ Finset.Icc 1 M,
        ‖quadraticSum
          (((A' * d : ℕ) : ℝ) / q')
          (((d * (2 * A * Z + B) : ℕ) : ℝ) / q) L‖) < L :=
  (Classical.choose_spec (Classical.choose_spec
    exists_aggregate_low_bound_of_corrected_weyl_budget).2).2

noncomputable def nvDivisorSubpowerThreshold : ℕ :=
  Classical.choose exists_card_divisors_le_eighth_rpow

lemma nvDivisorSubpowerThreshold_spec :
    ∀ q : ℕ, nvDivisorSubpowerThreshold ≤ q →
      (q.divisors.card : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ) :=
  Classical.choose_spec exists_card_divisors_le_eighth_rpow

noncomputable def nvSection8BoxConstant : ℕ :=
  (2 * (2 ^ (freimanRank (64 ^ 2) + 2)) + 1) ^ 2

noncomputable def nvMasterConstant : ℕ :=
  4096 + nvRobustBlockFactor 64 + nvRobustCubicLoss 64 +
    nvStoppedBudgetScaledCardFactor 64 +
    nvStoppedRemainderTranslateCount 65 64 +
    nvQuadraticAdjustmentConstant + nvQuadraticStepConstant +
    nvRankTwoUnbalancedConstant +
    nvReducedPeriodConstant + nvSection8BoxConstant +
    Nat.ceil nvAggregateWeylConstant + nvAggregateWeylExponent +
    nvDivisorSubpowerThreshold

lemma nvMasterConstant_ge_4096 : 4096 ≤ nvMasterConstant := by
  simp only [nvMasterConstant]
  omega

lemma nvMasterConstant_pos : 0 < nvMasterConstant :=
  (by omega : 0 < 4096).trans_le nvMasterConstant_ge_4096

lemma nvRobustBlockFactor_lt_master :
    nvRobustBlockFactor 64 < nvMasterConstant := by
  simp only [nvMasterConstant]
  omega

lemma nvRobustCubicLoss_le_master :
    nvRobustCubicLoss 64 ≤ nvMasterConstant := by
  simp only [nvMasterConstant]
  omega

lemma nvStoppedBudgetFactor_le_master :
    nvStoppedBudgetScaledCardFactor 64 ≤ nvMasterConstant := by
  simp only [nvMasterConstant]
  omega

lemma nvRemainderTranslateCount_le_master :
    nvStoppedRemainderTranslateCount 65 64 ≤ nvMasterConstant := by
  simp only [nvMasterConstant]
  omega

lemma nvQuadraticAdjustmentConstant_le_master :
    nvQuadraticAdjustmentConstant ≤ nvMasterConstant := by
  simp only [nvMasterConstant]
  omega

lemma nvQuadraticStepConstant_le_master :
    nvQuadraticStepConstant ≤ nvMasterConstant := by
  simp only [nvMasterConstant]
  omega

lemma nvRankTwoUnbalancedConstant_le_master :
    nvRankTwoUnbalancedConstant ≤ nvMasterConstant := by
  simp only [nvMasterConstant]
  omega

lemma nvReducedPeriodConstant_le_master :
    nvReducedPeriodConstant ≤ nvMasterConstant := by
  simp only [nvMasterConstant]
  omega

lemma nvSection8BoxConstant_le_master :
    nvSection8BoxConstant ≤ nvMasterConstant := by
  simp only [nvMasterConstant]
  omega

lemma nvAggregateWeylConstant_le_master :
    nvAggregateWeylConstant ≤ (nvMasterConstant : ℝ) := by
  calc
    nvAggregateWeylConstant ≤ (Nat.ceil nvAggregateWeylConstant : ℕ) :=
      Nat.le_ceil _
    _ ≤ (nvMasterConstant : ℕ) := by
      exact_mod_cast (by simp only [nvMasterConstant]; omega)

lemma nvAggregateWeylExponent_le_master :
    nvAggregateWeylExponent ≤ nvMasterConstant := by
  simp only [nvMasterConstant]
  omega

lemma nvDivisorSubpowerThreshold_le_master :
    nvDivisorSubpowerThreshold ≤ nvMasterConstant := by
  simp only [nvMasterConstant]
  omega

noncomputable def nvInitialLogExponent : ℕ :=
  100 * (nvMasterConstant + 1)

noncomputable def nvLossLogExponent : ℕ :=
  10 * nvInitialLogExponent

lemma nvInitialLogExponent_pos : 0 < nvInitialLogExponent := by
  simp only [nvInitialLogExponent]
  positivity

lemma nvLossLogExponent_pos : 0 < nvLossLogExponent := by
  simp only [nvLossLogExponent]
  exact Nat.mul_pos (by norm_num) nvInitialLogExponent_pos

lemma nvInitialLogExponent_add_one_le_loss :
    nvInitialLogExponent + 1 ≤ nvLossLogExponent := by
  have hI := nvInitialLogExponent_pos
  simp only [nvLossLogExponent]
  omega

def nvBinaryLogScale (N : ℕ) : ℕ := Nat.log 2 N + 1

def nvCubicScale (N : ℕ) : ℕ := 4 ^ Nat.log 64 N

noncomputable def nvInitialPolylog (N : ℕ) : ℕ :=
  nvMasterConstant * nvBinaryLogScale N ^ nvInitialLogExponent

noncomputable def nvOneStepLoss (N : ℕ) : ℕ :=
  nvMasterConstant ^ 10 * nvCubicScale N *
    nvBinaryLogScale N ^ nvLossLogExponent

lemma nvBinaryLogScale_pos (N : ℕ) : 0 < nvBinaryLogScale N := by
  simp only [nvBinaryLogScale]
  omega

lemma nvCubicScale_pos (N : ℕ) : 0 < nvCubicScale N := by
  simp only [nvCubicScale]
  positivity

lemma nvInitialPolylog_pos (N : ℕ) : 0 < nvInitialPolylog N := by
  simp only [nvInitialPolylog]
  exact Nat.mul_pos nvMasterConstant_pos
    (pow_pos (nvBinaryLogScale_pos N) nvInitialLogExponent)

lemma nvOneStepLoss_pos (N : ℕ) : 0 < nvOneStepLoss N := by
  simp only [nvOneStepLoss]
  exact Nat.mul_pos
    (Nat.mul_pos (pow_pos nvMasterConstant_pos 10) (nvCubicScale_pos N))
    (pow_pos (nvBinaryLogScale_pos N) nvLossLogExponent)

lemma binaryLogScale_mono {m n : ℕ} (hmn : m ≤ n) :
    nvBinaryLogScale m ≤ nvBinaryLogScale n := by
  simp only [nvBinaryLogScale]
  exact Nat.add_le_add_right (Nat.log_mono_right hmn) 1

lemma card_le_ambient_of_subset_Icc {A : Finset ℕ} {N : ℕ}
    (hAN : A ⊆ Finset.Icc 1 N) : A.card ≤ N := by
  calc
    A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hAN
    _ ≤ N := by simp

lemma ambient_le_of_mul_le {p N N₀ : ℕ} (hp : 0 < p)
    (hpN : p * N ≤ N₀) : N ≤ N₀ := by
  calc
    N = 1 * N := by simp
    _ ≤ p * N := Nat.mul_le_mul_right N hp
    _ ≤ N₀ := hpN

lemma binaryLogScale_ambient_le {p N N₀ : ℕ} (hp : 0 < p)
    (hpN : p * N ≤ N₀) :
    nvBinaryLogScale N ≤ nvBinaryLogScale N₀ :=
  binaryLogScale_mono (ambient_le_of_mul_le hp hpN)

lemma binaryLogScale_card_le {A : Finset ℕ} {N N₀ p : ℕ}
    (hp : 0 < p) (hpN : p * N ≤ N₀)
    (hAN : A ⊆ Finset.Icc 1 N) :
    nvBinaryLogScale A.card ≤ nvBinaryLogScale N₀ := by
  apply binaryLogScale_mono
  exact (card_le_ambient_of_subset_Icc hAN).trans
    (ambient_le_of_mul_le hp hpN)

lemma nv_bookkeeping_monomial_bound {C S ell I E : ℕ}
    (hC : 4096 ≤ C) (hS : 0 < S) (hell : 0 < ell)
    (hI : 0 < I) (hIE : I + 1 ≤ E) :
    64 * ell + 260 * C * S * ell ^ I +
        192 * C * S * ell ^ (I + 1) ≤
      C ^ 10 * S * ell ^ E := by
  have hCell : 0 < C := by omega
  have hpow₁ : ell ^ 1 ≤ ell ^ E :=
    Nat.pow_le_pow_right hell (by omega)
  have hpowI : ell ^ I ≤ ell ^ E :=
    Nat.pow_le_pow_right hell (by omega)
  have hpowISucc : ell ^ (I + 1) ≤ ell ^ E :=
    Nat.pow_le_pow_right hell hIE
  have hfirst : 64 * ell ≤ 64 * C * S * ell ^ E := by
    calc
      64 * ell = 64 * 1 * 1 * ell ^ 1 := by ring
      _ ≤ 64 * C * S * ell ^ E := by gcongr <;> omega
  have hsecond : 260 * C * S * ell ^ I ≤
      260 * C * S * ell ^ E := by gcongr
  have hthird : 192 * C * S * ell ^ (I + 1) ≤
      192 * C * S * ell ^ E := by gcongr
  have hsum :
      64 * ell + 260 * C * S * ell ^ I +
          192 * C * S * ell ^ (I + 1) ≤
        516 * C * S * ell ^ E := by
    calc
      64 * ell + 260 * C * S * ell ^ I +
          192 * C * S * ell ^ (I + 1) ≤
        64 * C * S * ell ^ E +
          260 * C * S * ell ^ E +
          192 * C * S * ell ^ E := by omega
      _ = 516 * C * S * ell ^ E := by ring
  have hCpow : 516 * C ≤ C ^ 10 := by
    have h516 : 516 ≤ C ^ 9 := by
      calc
        516 ≤ C := by omega
        _ = C ^ 1 := by simp
        _ ≤ C ^ 9 := Nat.pow_le_pow_right hCell (by omega)
    calc
      516 * C ≤ C ^ 9 * C := Nat.mul_le_mul_right C h516
      _ = C ^ 10 := by ring
  exact hsum.trans (by
    calc
      516 * C * S * ell ^ E ≤ C ^ 10 * S * ell ^ E := by
        gcongr
      _ = C ^ 10 * S * ell ^ E := rfl)

lemma nv_initial_length_bookkeeping_le_loss (N : ℕ) :
    64 * nvBinaryLogScale N +
        65 * (4 ^ (Nat.log 64 N + 1) * nvInitialPolylog N) +
        48 * nvBinaryLogScale N *
          (4 ^ (Nat.log 64 N + 1) * nvInitialPolylog N) ≤
      nvOneStepLoss N := by
  have hraw := nv_bookkeeping_monomial_bound
    nvMasterConstant_ge_4096 (nvCubicScale_pos N) (nvBinaryLogScale_pos N)
      nvInitialLogExponent_pos nvInitialLogExponent_add_one_le_loss
  have hfour : 4 ^ (Nat.log 64 N + 1) = 4 * nvCubicScale N := by
    rw [pow_succ]
    simp only [nvCubicScale]
    ring
  rw [hfour]
  simp only [nvInitialPolylog, nvOneStepLoss]
  convert hraw using 1 <;> ring

lemma two_pow_log_sixty_four_le_cubicScale (N : ℕ) :
    2 ^ Nat.log 64 N ≤ nvCubicScale N := by
  simp only [nvCubicScale]
  exact Nat.pow_le_pow_left (by norm_num) _

lemma nv_growth_coefficient_lt_half_loss (N : ℕ) :
    2 ^ (Nat.log 64 N + 1) * (8 * nvBinaryLogScale N + 65) + 1 <
      nvOneStepLoss N / 2 := by
  let S := nvCubicScale N
  let ell := nvBinaryLogScale N
  let C := nvMasterConstant
  have hS : 0 < S := nvCubicScale_pos N
  have hell : 0 < ell := nvBinaryLogScale_pos N
  have hC : 4096 ≤ C := nvMasterConstant_ge_4096
  have htwo : 2 ^ (Nat.log 64 N + 1) ≤ 2 * S := by
    rw [pow_succ]
    simpa only [S, mul_comm] using
      Nat.mul_le_mul_left 2 (two_pow_log_sixty_four_le_cubicScale N)
  have hsmall :
      2 ^ (Nat.log 64 N + 1) * (8 * ell + 65) + 1 ≤
        147 * S * ell := by
    calc
      2 ^ (Nat.log 64 N + 1) * (8 * ell + 65) + 1 ≤
          (2 * S) * (8 * ell + 65) + 1 := by gcongr
      _ ≤ 147 * S * ell := by nlinarith
  have hCself : C ≤ C ^ 10 := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (by omega : 0 < C) (by omega : 1 ≤ 10))
  have hCpow : 2 * 148 ≤ C ^ 10 := by
    have hbase : 2 * 148 ≤ C := by omega
    exact hbase.trans hCself
  have hpell : ell ^ 1 ≤ ell ^ nvLossLogExponent :=
    Nat.pow_le_pow_right hell (by
      have hE := nvLossLogExponent_pos
      omega)
  have hdouble : 2 * (147 * S * ell + 1) ≤
      C ^ 10 * S * ell ^ nvLossLogExponent := by
    have hone : 1 ≤ S * ell := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc
      2 * (147 * S * ell + 1) ≤ 2 * (148 * (S * ell)) := by
        gcongr
        nlinarith
      _ = (2 * 148) * (S * ell ^ 1) := by ring
      _ ≤ C ^ 10 * (S * ell ^ 1) := by gcongr
      _ ≤ C ^ 10 * (S * ell ^ nvLossLogExponent) := by gcongr
      _ = C ^ 10 * S * ell ^ nvLossLogExponent := by ring
  have hhalf : 147 * S * ell <
      (C ^ 10 * S * ell ^ nvLossLogExponent) / 2 := by
    apply Nat.lt_of_succ_le
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hdouble
  simpa only [S, ell, C, nvOneStepLoss] using hsmall.trans_lt hhalf

/-- The concrete initialization used at every stage of the divisor descent.
All logarithmic support, reserve, capacity, and growth inequalities are
discharged from the single displayed cardinality hypothesis. -/
theorem exists_configured_robustStopCertificate
    {A : Finset ℕ} {N N₀ p : ℕ}
    (hp : 0 < p) (hpN : p * N ≤ N₀)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hlarge : nvOneStepLoss N₀ * nvBinaryLogScale N < A.card) :
    RobustStopCertificate (A := A) 65 64 (nvInitialPolylog N₀)
      (nvCubicScale N₀ * nvInitialPolylog N₀)
      (A.card - nvOneStepLoss N₀) (A.card / 2)
      ((A.card / 2) *
        (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 3) := by
  let ell₀ := nvBinaryLogScale N₀
  let ellA := nvBinaryLogScale A.card
  let s := Nat.log 64 N₀
  let M := nvInitialPolylog N₀
  let X := nvCubicScale N₀ * M
  let Lloss := nvOneStepLoss N₀
  let len := 4 ^ (s + 1) * M
  have hellN : 0 < nvBinaryLogScale N := nvBinaryLogScale_pos N
  have hLloss : 0 < Lloss := nvOneStepLoss_pos N₀
  have hLossA : Lloss < A.card := by
    calc
      Lloss = Lloss * 1 := by simp
      _ ≤ Lloss * nvBinaryLogScale N := by gcongr; omega
      _ < A.card := hlarge
  have hA2 : 2 ≤ A.card := by omega
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hAne
  have haIcc := Finset.mem_Icc.mp (hAN ha)
  have hNpos : 0 < N := by omega
  have hN₀pos : 0 < N₀ := by
    have : N ≤ N₀ := ambient_le_of_mul_le hp hpN
    omega
  have hellA₀ : ellA ≤ ell₀ := by
    simpa only [ellA, ell₀] using binaryLogScale_card_le hp hpN hAN
  have hbook₀ := nv_initial_length_bookkeeping_le_loss N₀
  have hlenDef : len = 4 ^ (Nat.log 64 N₀ + 1) * nvInitialPolylog N₀ := rfl
  have hbookA :
      64 * ellA + 65 * len + 48 * ellA * len ≤ Lloss := by
    calc
      64 * ellA + 65 * len + 48 * ellA * len ≤
          64 * ell₀ + 65 * len + 48 * ell₀ * len := by gcongr
      _ ≤ Lloss := by
        simpa only [ell₀, Lloss, hlenDef] using hbook₀
  have hspace :
      64 * (Nat.log 2 A.card + 1) +
          8 * (Nat.log 2 A.card + 1) * (4 ^ (s + 1) * M) ≤ A.card := by
    have hsmall : 64 * ellA + 8 * ellA * len ≤ Lloss := by
      calc
        64 * ellA + 8 * ellA * len ≤
            64 * ellA + 65 * len + 48 * ellA * len := by nlinarith
        _ ≤ Lloss := hbookA
    simpa only [ellA, nvBinaryLogScale, len, s, M] using
      hsmall.trans hLossA.le
  have hhalf :
      16 * (Nat.log 2 A.card + 1) * (4 ^ (s + 1) * M) ≤ A.card := by
    have hsmall : 16 * ellA * len ≤ Lloss := by
      calc
        16 * ellA * len ≤
            64 * ellA + 65 * len + 48 * ellA * len := by nlinarith
        _ ≤ Lloss := hbookA
    simpa only [ellA, nvBinaryLogScale, len, s, M] using
      hsmall.trans hLossA.le
  have hresSmall : 8 * ellA * len ≤ A.card := by
    have : 8 * ellA * len ≤ Lloss := by
      calc
        8 * ellA * len ≤
            64 * ellA + 65 * len + 48 * ellA * len := by nlinarith
        _ ≤ Lloss := hbookA
    exact this.trans hLossA.le
  have hreserve :
      3 * (A.card - Lloss) + 65 * len ≤
        3 * (A.card - 8 * ellA * len) := by
    have hcost : 65 * len + 24 * ellA * len ≤ 3 * Lloss := by
      have : 65 * len + 24 * ellA * len ≤ Lloss := by
        calc
          65 * len + 24 * ellA * len ≤
              64 * ellA + 65 * len + 48 * ellA * len := by nlinarith
          _ ≤ Lloss := hbookA
      omega
    have hcost' : 65 * len + 3 * (8 * ellA * len) ≤ 3 * Lloss := by
      nlinarith [hcost]
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
    apply Nat.le_sub_of_add_le
    calc
      (3 * A.card - 3 * Lloss) + 65 * len +
          3 * (8 * ellA * len) =
        (3 * A.card - 3 * Lloss) +
          (65 * len + 3 * (8 * ellA * len)) := by ring
      _ ≤ (3 * A.card - 3 * Lloss) + 3 * Lloss :=
        Nat.add_le_add_left hcost' _
      _ = 3 * A.card := Nat.sub_add_cancel (Nat.mul_le_mul_left 3 hLossA.le)
  have hcapacity :
      65 * len ≤ 2 * (A.card - 8 * ellA * len) := by
    have hcost : 65 * len + 8 * ellA * len ≤ Lloss := by
      calc
        65 * len + 8 * ellA * len ≤
            64 * ellA + 65 * len + 48 * ellA * len := by nlinarith
        _ ≤ Lloss := hbookA
    have hone : 65 * len ≤ A.card - 8 * ellA * len := by
      apply Nat.le_sub_of_add_le
      exact hcost.trans hLossA.le
    exact hone.trans (by omega)
  have hN₀scale : N₀ < 64 ^ (s + 1) := by
    simpa only [s] using (log_sixty_four_scale_bounds hN₀pos).2
  have hcoef₀ :
      2 ^ (s + 1) * (8 * ell₀ + 65) + 1 < Lloss / 2 := by
    simpa only [s, ell₀, Lloss] using nv_growth_coefficient_lt_half_loss N₀
  have hcoef :
      2 ^ (s + 1) * (8 * ellA + 65) + 1 < A.card / 2 := by
    have hmono :
        2 ^ (s + 1) * (8 * ellA + 65) + 1 ≤
          2 ^ (s + 1) * (8 * ell₀ + 65) + 1 := by gcongr
    have hhalfMono : Lloss / 2 ≤ A.card / 2 := Nat.div_le_div_right hLossA.le
    exact hmono.trans_lt (hcoef₀.trans_le hhalfMono)
  have hiter : iteratedSupportBound 65 (s + 1) (8 * ellA) ≤
      2 ^ (s + 1) * (8 * ellA + 65) :=
    iteratedSupportBound_le_pow_mul 65 (s + 1) (8 * ellA)
  have hgrowth :
      iteratedSupportBound 65 (s + 1) (8 * ellA) * N + 1 <
        64 ^ (s + 1) * (A.card / 2) := by
    let K := 2 ^ (s + 1) * (8 * ellA + 65)
    have hKN :
        iteratedSupportBound 65 (s + 1) (8 * ellA) * N + 1 ≤
          (K + 1) * N := by
      dsimp only [K]
      calc
        iteratedSupportBound 65 (s + 1) (8 * ellA) * N + 1 ≤
            (2 ^ (s + 1) * (8 * ellA + 65)) * N + 1 := by gcongr
        _ ≤ (2 ^ (s + 1) * (8 * ellA + 65) + 1) * N := by
          nlinarith
    have hKA : K + 1 < A.card / 2 := by simpa only [K] using hcoef
    have hAhalfPos : 0 < A.card / 2 := by omega
    have hNN₀ : N ≤ N₀ := ambient_le_of_mul_le hp hpN
    have hprod : (K + 1) * N < (A.card / 2) * 64 ^ (s + 1) := by
      calc
        (K + 1) * N < (A.card / 2) * N :=
          (Nat.mul_lt_mul_right hNpos).2 hKA
        _ ≤ (A.card / 2) * N₀ := Nat.mul_le_mul_left _ hNN₀
        _ < (A.card / 2) * 64 ^ (s + 1) :=
          (Nat.mul_lt_mul_left hAhalfPos).2 hN₀scale
    exact hKN.trans_lt (by simpa only [mul_comm] using hprod)
  simpa only [s, M, X, Lloss, len, ellA, nvCubicScale] using
    (exists_initial_robustStopCertificate
      (A := A) (N := N) 65 64 s M (A.card - Lloss)
      (by norm_num) (by norm_num) (by simpa only [M] using nvInitialPolylog_pos N₀)
      hA2 hAN hspace hhalf hreserve hcapacity hgrowth)

lemma configured_structural_scale
    {A : Finset ℕ} {N N₀ p : ℕ}
    (hp : 0 < p) (hpN : p * N ≤ N₀)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hlarge : nvOneStepLoss N₀ * nvBinaryLogScale N < A.card) :
    nvRobustCubicLoss 64 * nvStoppedBudgetScaledCardFactor 64 *
        (A.card * N + 1) <
      (A.card / 2) *
        (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 3 := by
  let C := nvMasterConstant
  let S := nvCubicScale N₀
  let M := nvInitialPolylog N₀
  have hLossA : nvOneStepLoss N₀ < A.card := by
    calc
      nvOneStepLoss N₀ = nvOneStepLoss N₀ * 1 := by simp
      _ ≤ nvOneStepLoss N₀ * nvBinaryLogScale N := by
        gcongr
        exact nvBinaryLogScale_pos N
      _ < A.card := hlarge
  have hA2 : 2 ≤ A.card := by
    have := nvOneStepLoss_pos N₀
    omega
  have hAhalf : 0 < A.card / 2 := by omega
  have hNpos : 0 < N := by
    have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha⟩ := hAne
    have := Finset.mem_Icc.mp (hAN ha)
    omega
  have hN₀pos : 0 < N₀ := by
    have := ambient_le_of_mul_le hp hpN
    omega
  have hAthree : A.card ≤ 3 * (A.card / 2) := by omega
  have hANpos : 0 < A.card * N := Nat.mul_pos (by omega) hNpos
  have hsum : A.card * N + 1 ≤ 2 * (A.card * N) := by omega
  have hNN₀ : N ≤ N₀ := ambient_le_of_mul_le hp hpN
  have hN₀scale : N₀ ≤ 64 * S ^ 3 := by
    simpa only [S, nvCubicScale] using ambient_le_sixty_four_mul_scale_cube hN₀pos
  have hC : 4096 ≤ C := nvMasterConstant_ge_4096
  have hCpos : 0 < C := by omega
  have hcoeff : 384 * C ^ 2 < C ^ 3 := by
    calc
      384 * C ^ 2 < C * C ^ 2 :=
        (Nat.mul_lt_mul_right (pow_pos hCpos 2)).2 (by omega)
      _ = C ^ 3 := by ring
  have hM : C ≤ M := by
    dsimp only [M, nvInitialPolylog]
    calc
      nvMasterConstant = nvMasterConstant * 1 := by simp
      _ ≤ nvMasterConstant *
          nvBinaryLogScale N₀ ^ nvInitialLogExponent := by
        gcongr
        exact pow_pos (nvBinaryLogScale_pos N₀) nvInitialLogExponent
  have hMpow : C ^ 3 ≤ M ^ 3 := Nat.pow_le_pow_left hM 3
  calc
    nvRobustCubicLoss 64 * nvStoppedBudgetScaledCardFactor 64 *
          (A.card * N + 1) ≤
        C * C * (2 * (A.card * N)) := by
      gcongr
      · exact nvRobustCubicLoss_le_master
      · exact nvStoppedBudgetFactor_le_master
    _ ≤ C * C * (2 * (A.card * N₀)) := by gcongr
    _ ≤ C * C * (2 * (3 * (A.card / 2) * N₀)) := by gcongr
    _ ≤ C * C * (2 * (3 * (A.card / 2) * (64 * S ^ 3))) := by gcongr
    _ = (A.card / 2) * S ^ 3 * (384 * C ^ 2) := by ring
    _ < (A.card / 2) * S ^ 3 * C ^ 3 := by
      exact Nat.mul_lt_mul_of_pos_left hcoeff
        (Nat.mul_pos hAhalf (pow_pos (nvCubicScale_pos N₀) 3))
    _ ≤ (A.card / 2) * S ^ 3 * M ^ 3 := by gcongr
    _ = (A.card / 2) * (S * M) ^ 3 := by ring
    _ = (A.card / 2) *
        (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 3 := rfl

/-- Configured form of the complete stopped Nguyen--Vu structural output. -/
theorem exists_configured_nguyen_vu_rank_two_structure
    {A : Finset ℕ} {N N₀ p : ℕ}
    (hp : 0 < p) (hpN : p * N ≤ N₀)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hlarge : nvOneStepLoss N₀ * nvBinaryLogScale N < A.card) :
    ∃ s b : ℕ, ∃ G : NVGeneration A, ∃ m : ℕ,
    ∃ J : Finset (Fin G.values.length), ∃ R' : Finset ℕ,
    ∃ i j : Fin G.values.length, ∃ P Q R : GeneralizedAP,
    ∃ d : ℕ, ∃ t : ℤ, ∃ E F Z : Finset ℤ,
      (A.card / 2) *
          (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 3 ≤
        nvRobustCubicLoss 64 * b * (2 ^ s) ^ 3 ∧
      nvInitialPolylog N₀ <
        2 * (nvRobustBlockFactor 64 + 1) * 2 ^ s ∧
      2 ^ s ≤ nvCubicScale N₀ * nvInitialPolylog N₀ ∧
      A.card / 2 ≤ b ∧ b ≤ G.commonCard ∧
      nvInitialPolylog N₀ ≤ m ∧ J.card = 2 * m ∧
      R' ⊆ G.reserve ∧ A.card - nvOneStepLoss N₀ ≤ R'.card ∧
      65 * m ≤ R'.card ∧ i ∈ J ∧ j ∈ J ∧ i ≠ j ∧
      Q.rank = P.rank ∧ Q.base = 0 ∧ Q.Proper ∧ P.Proper ∧
      P.rank ≤ freimanRank (64 ^ 2) ∧
      G.commonCard ≤ P.boxCard ∧
      P.boxCard ≤ nvStoppingModelFactor (64 ^ 2) 1 * G.commonCard ∧
      natToIntFinset (G.values.get i) - natToIntFinset (G.values.get i) ⊆
        P.carrier ∧
      Q.boxCard = GeneralizedAP.nvStandardBoxCard P
        (nvStoppedDensity 64) (nvDenseCount (nvStoppedDensity 64) P.rank) ∧
      Q.carrier ⊆ nvDenseCount (nvStoppedDensity 64) P.rank • P.carrier -
        nvDenseCount (nvStoppedDensity 64) P.rank • P.carrier ∧
      R.Proper ∧ R.rank ≤ 2 ∧
      (∀ k : Fin R.rank, 0 < R.length k) ∧
      b ≤ nvStoppedBudgetScaledCardFactor 64 * R.carrier.card ∧
      b * (2 ^ s) ^ R.rank ≤
        nvStoppedBudgetScaledCardFactor 64 * R.carrier.card ∧
      d ≤ freimanRank (64 ^ 2) ∧
      (({t} : Finset ℤ) + R.carrier) +
        natToIntFinset G.reserve.subsetSum ⊆ natToIntFinset A.subsetSum ∧
      E ⊆ natToIntFinset (G.values.get j) ∧ E.card ≤ 64 ∧
      F ⊆ natToIntFinset R' ∧ F.card < 65 ∧
      natToIntFinset R' ⊆
        (F + (E - E)) + (P.carrier + P.carrier - P.carrier) ∧
      Z.card ≤ nvStoppedRemainderTranslateCount 65 64 ∧
      natToIntFinset R' ⊆ Z + iteratedDifference (d + 3) R.carrier := by
  have H := exists_configured_robustStopCertificate hp hpN hAN hlarge
  apply H.exists_nguyen_vu_rank_two_structure (by norm_num) (by norm_num)
      (by norm_num)
  · exact nvRobustBlockFactor_lt_master.trans_le (by
      calc
        nvMasterConstant = nvMasterConstant * 1 := by simp
        _ ≤ nvInitialPolylog N₀ := by
          simp only [nvInitialPolylog]
          gcongr
          exact pow_pos (nvBinaryLogScale_pos N₀) nvInitialLogExponent)
  · exact hAN
  · exact configured_structural_scale hp hpN hAN hlarge

/-! ### Scale-sensitive consequences used by the terminal ranks -/

lemma configured_rank_one_step_bound
    {A : Finset ℕ} {N N₀ p q : ℕ}
    (hp : 0 < p) (hpN : p * N ≤ N₀)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hA2 : 2 ≤ A.card)
    (hqW : q * ((A.card / 2) *
          (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 3) ≤
      2 * nvRobustCubicLoss 64 * nvStoppedBudgetScaledCardFactor 64 *
        (A.card * N) *
          (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 2) :
    p * q ≤ 384 * nvMasterConstant ^ 2 * nvCubicScale N₀ ^ 2 := by
  let C := nvMasterConstant
  let S := nvCubicScale N₀
  let M := nvInitialPolylog N₀
  let X := S * M
  have hS : 0 < S := nvCubicScale_pos N₀
  have hM : 0 < M := nvInitialPolylog_pos N₀
  have hX : 0 < X := Nat.mul_pos hS hM
  have hAhalf : 0 < A.card / 2 := by omega
  have hAthree : A.card ≤ 3 * (A.card / 2) := by omega
  have hN₀pos : 0 < N₀ := by
    have hNpos : 0 < N := by
      have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨a, ha⟩ := hAne
      have := Finset.mem_Icc.mp (hAN ha)
      omega
    have := ambient_le_of_mul_le hp hpN
    omega
  have hscale : N₀ ≤ 64 * S ^ 3 := by
    simpa only [S, nvCubicScale] using ambient_le_sixty_four_mul_scale_cube hN₀pos
  have hSX : S ≤ X := by
    dsimp only [X]
    exact Nat.le_mul_of_pos_right S hM
  have hmul :
      (A.card / 2 * X ^ 2) * (p * q * X) ≤
        (A.card / 2 * X ^ 2) * (384 * C ^ 2 * S ^ 3) := by
    calc
      (A.card / 2 * X ^ 2) * (p * q * X) =
          p * (q * ((A.card / 2) * X ^ 3)) := by ring
      _ ≤ p * (2 * nvRobustCubicLoss 64 *
          nvStoppedBudgetScaledCardFactor 64 * (A.card * N) * X ^ 2) := by
            simpa only [X, S, M] using Nat.mul_le_mul_left p hqW
      _ = 2 * nvRobustCubicLoss 64 *
          nvStoppedBudgetScaledCardFactor 64 * A.card * (p * N) * X ^ 2 := by
            ring
      _ ≤ 2 * C * C * (3 * (A.card / 2)) * N₀ * X ^ 2 := by
            gcongr
            · exact nvRobustCubicLoss_le_master
            · exact nvStoppedBudgetFactor_le_master
      _ ≤ 2 * C * C * (3 * (A.card / 2)) * (64 * S ^ 3) * X ^ 2 := by
            gcongr
      _ = (A.card / 2 * X ^ 2) * (384 * C ^ 2 * S ^ 3) := by ring
  have hpqX : p * q * X ≤ 384 * C ^ 2 * S ^ 3 :=
    Nat.le_of_mul_le_mul_left hmul (Nat.mul_pos hAhalf (pow_pos hX 2))
  have hpqS : p * q * S ≤ 384 * C ^ 2 * S ^ 3 :=
    (Nat.mul_le_mul_left (p * q) hSX).trans hpqX
  have hcancel : S * (p * q) ≤ S * (384 * C ^ 2 * S ^ 2) := by
    calc
      S * (p * q) = p * q * S := by ring
      _ ≤ 384 * C ^ 2 * S ^ 3 := hpqS
      _ = S * (384 * C ^ 2 * S ^ 2) := by ring
  have := Nat.le_of_mul_le_mul_left hcancel hS
  simpa only [C, S] using this

lemma configured_rank_two_common_step_bound
    {A : Finset ℕ} {N N₀ p g : ℕ}
    (hp : 0 < p) (hpN : p * N ≤ N₀)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hA2 : 2 ≤ A.card)
    (hgW : g * ((A.card / 2) *
          (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 3) ≤
      4 * nvRobustCubicLoss 64 * nvStoppedBudgetScaledCardFactor 64 *
        (A.card * N) *
          (nvCubicScale N₀ * nvInitialPolylog N₀)) :
    p * g * nvInitialPolylog N₀ ^ 2 ≤
      768 * nvMasterConstant ^ 2 * nvCubicScale N₀ := by
  let C := nvMasterConstant
  let S := nvCubicScale N₀
  let M := nvInitialPolylog N₀
  let X := S * M
  have hS : 0 < S := nvCubicScale_pos N₀
  have hM : 0 < M := nvInitialPolylog_pos N₀
  have hX : 0 < X := Nat.mul_pos hS hM
  have hAhalf : 0 < A.card / 2 := by omega
  have hAthree : A.card ≤ 3 * (A.card / 2) := by omega
  have hN₀pos : 0 < N₀ := by
    have hNpos : 0 < N := by
      have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨a, ha⟩ := hAne
      have := Finset.mem_Icc.mp (hAN ha)
      omega
    have := ambient_le_of_mul_le hp hpN
    omega
  have hscale : N₀ ≤ 64 * S ^ 3 := by
    simpa only [S, nvCubicScale] using ambient_le_sixty_four_mul_scale_cube hN₀pos
  have hmul :
      (A.card / 2 * X) * (p * g * X ^ 2) ≤
        (A.card / 2 * X) * (768 * C ^ 2 * S ^ 3) := by
    calc
      (A.card / 2 * X) * (p * g * X ^ 2) =
          p * (g * ((A.card / 2) * X ^ 3)) := by ring
      _ ≤ p * (4 * nvRobustCubicLoss 64 *
          nvStoppedBudgetScaledCardFactor 64 * (A.card * N) * X) := by
            simpa only [X, S, M] using Nat.mul_le_mul_left p hgW
      _ = 4 * nvRobustCubicLoss 64 *
          nvStoppedBudgetScaledCardFactor 64 * A.card * (p * N) * X := by
            ring
      _ ≤ 4 * C * C * (3 * (A.card / 2)) * N₀ * X := by
            gcongr
            · exact nvRobustCubicLoss_le_master
            · exact nvStoppedBudgetFactor_le_master
      _ ≤ 4 * C * C * (3 * (A.card / 2)) * (64 * S ^ 3) * X := by
            gcongr
      _ = (A.card / 2 * X) * (768 * C ^ 2 * S ^ 3) := by ring
  have hpgX : p * g * X ^ 2 ≤ 768 * C ^ 2 * S ^ 3 :=
    Nat.le_of_mul_le_mul_left hmul (Nat.mul_pos hAhalf hX)
  have hcancel : S ^ 2 * (p * g * M ^ 2) ≤
      S ^ 2 * (768 * C ^ 2 * S) := by
    calc
      S ^ 2 * (p * g * M ^ 2) = p * g * X ^ 2 := by
        dsimp only [X]
        ring
      _ ≤ 768 * C ^ 2 * S ^ 3 := hpgX
      _ = S ^ 2 * (768 * C ^ 2 * S) := by ring
  have := Nat.le_of_mul_le_mul_left hcancel (pow_pos hS 2)
  simpa only [C, S, M] using this

lemma log_two_le_twice_binaryLogScale_of_le_square
    {q N : ℕ} (hq : 0 < q) (hN : 0 < N) (hqN : q ≤ N ^ 2) :
    Nat.log 2 q ≤ 2 * nvBinaryLogScale N := by
  have hNpow : N < 2 ^ nvBinaryLogScale N := by
    simpa only [nvBinaryLogScale] using
      Nat.lt_pow_succ_log_self Nat.one_lt_two N
  have hqpow : q < 2 ^ (2 * nvBinaryLogScale N) := by
    calc
      q ≤ N ^ 2 := hqN
      _ < (2 ^ nvBinaryLogScale N) ^ 2 :=
        Nat.pow_lt_pow_left hNpow (by norm_num)
      _ = 2 ^ (2 * nvBinaryLogScale N) := by rw [← pow_mul]; ring
  exact (Nat.log_lt_iff_lt_pow Nat.one_lt_two hq.ne').2 hqpow |>.le

lemma sqrt_succ_le_of_le_square {x B : ℕ} (hx : x ≤ B ^ 2) :
    Nat.sqrt x + 1 ≤ B + 1 := by
  have hs := Nat.sqrt_le_sqrt hx
  simpa using Nat.add_le_add_right hs 1

lemma configured_residue_loss_bound
    {N₀ p q : ℕ} (hN₀ : 0 < N₀) (hq : 0 < q)
    (hqN : q ≤ N₀ ^ 2)
    (hpq : p * q ≤
      1024 * nvMasterConstant ^ 2 * nvCubicScale N₀ ^ 2) :
    nvStoppedRemainderTranslateCount 65 64 *
        (Nat.log 2 q *
          (nvQuadraticAdjustmentConstant * (Nat.sqrt (p * q) + 1))) ≤
      nvOneStepLoss N₀ := by
  let C := nvMasterConstant
  let S := nvCubicScale N₀
  let ell := nvBinaryLogScale N₀
  have hC : 4096 ≤ C := nvMasterConstant_ge_4096
  have hCpos : 0 < C := by omega
  have hS : 0 < S := nvCubicScale_pos N₀
  have hell : 0 < ell := nvBinaryLogScale_pos N₀
  have hlog : Nat.log 2 q ≤ 2 * ell := by
    simpa only [ell] using
      log_two_le_twice_binaryLogScale_of_le_square hq hN₀ hqN
  have hsquare : p * q ≤ (32 * C * S) ^ 2 := by
    calc
      p * q ≤ 1024 * C ^ 2 * S ^ 2 := by simpa only [C, S] using hpq
      _ = (32 * C * S) ^ 2 := by ring
  have hsqrt : Nat.sqrt (p * q) + 1 ≤ 33 * C * S := by
    have hraw := sqrt_succ_le_of_le_square hsquare
    have hone : 1 ≤ C * S := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc
      Nat.sqrt (p * q) + 1 ≤ 32 * C * S + 1 := by simpa using hraw
      _ ≤ 33 * C * S := by nlinarith
  have hraw :
      nvStoppedRemainderTranslateCount 65 64 *
          (Nat.log 2 q *
            (nvQuadraticAdjustmentConstant * (Nat.sqrt (p * q) + 1))) ≤
        66 * C ^ 3 * S * ell := by
    calc
      nvStoppedRemainderTranslateCount 65 64 *
          (Nat.log 2 q *
            (nvQuadraticAdjustmentConstant * (Nat.sqrt (p * q) + 1))) ≤
        C * ((2 * ell) * (C * (33 * C * S))) := by
          gcongr
          · exact nvRemainderTranslateCount_le_master
          · exact nvQuadraticAdjustmentConstant_le_master
      _ = 66 * C ^ 3 * S * ell := by ring
  have hcoeff : 66 * C ^ 3 ≤ C ^ 10 := by
    have h66 : 66 ≤ C ^ 7 := by
      calc
        66 ≤ C := by omega
        _ = C ^ 1 := by simp
        _ ≤ C ^ 7 := Nat.pow_le_pow_right hCpos (by omega)
    calc
      66 * C ^ 3 ≤ C ^ 7 * C ^ 3 := Nat.mul_le_mul_right _ h66
      _ = C ^ 10 := by rw [← pow_add]
  have hpell : ell ^ 1 ≤ ell ^ nvLossLogExponent :=
    Nat.pow_le_pow_right hell (by
      have hE := nvLossLogExponent_pos
      omega)
  calc
    nvStoppedRemainderTranslateCount 65 64 *
        (Nat.log 2 q *
          (nvQuadraticAdjustmentConstant * (Nat.sqrt (p * q) + 1))) ≤
      66 * C ^ 3 * S * ell := hraw
    _ = (66 * C ^ 3) * S * ell ^ 1 := by ring
    _ ≤ C ^ 10 * S * ell ^ nvLossLogExponent := by gcongr
    _ = nvOneStepLoss N₀ := by simp only [nvOneStepLoss, C, S, ell]

/-! The fixed polylogarithmic reserve is large enough to force the long
rank-one side required by the elementary square-location argument.  Squaring
the desired comparison avoids any real-valued square-root estimates. -/
lemma configured_rank_one_terminal_dominance
    {A : Finset ℕ} {N N₀ p C₀ F : ℕ}
    (hp : 0 < p) (hpN : p * N ≤ N₀)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hlarge : nvOneStepLoss N₀ * nvBinaryLogScale N < A.card)
    (hC₀ : C₀ ≤ nvMasterConstant) (hF : F ≤ nvMasterConstant) :
    C₀ * F *
        (8 * (Nat.sqrt (p * (A.card * N)) + 1) + 1) *
          (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 2 <
      (A.card / 2) *
        (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 3 := by
  let C := nvMasterConstant
  let S := nvCubicScale N₀
  let ell := nvBinaryLogScale N₀
  let M := nvInitialPolylog N₀
  let X := S * M
  let a := A.card
  let h := a / 2
  let R := Nat.sqrt (p * (a * N))
  have hC : 4096 ≤ C := nvMasterConstant_ge_4096
  have hCpos : 0 < C := by omega
  have hS : 0 < S := nvCubicScale_pos N₀
  have hell : 0 < ell := nvBinaryLogScale_pos N₀
  have hM : 0 < M := nvInitialPolylog_pos N₀
  have hX : 0 < X := Nat.mul_pos hS hM
  have hloss : nvOneStepLoss N₀ < a := by
    calc
      nvOneStepLoss N₀ = nvOneStepLoss N₀ * 1 := by simp
      _ ≤ nvOneStepLoss N₀ * nvBinaryLogScale N := by
        gcongr
        exact nvBinaryLogScale_pos N
      _ < a := by simpa only [a] using hlarge
  have ha2 : 2 ≤ a := by
    have := nvOneStepLoss_pos N₀
    omega
  have hh : 0 < h := by dsimp only [h]; omega
  have hah : a ≤ 3 * h := by dsimp only [h]; omega
  have hNpos : 0 < N := by
    have hAne : A.Nonempty := Finset.card_pos.mp (by simpa only [a] using (by omega : 0 < a))
    obtain ⟨x, hx⟩ := hAne
    have := Finset.mem_Icc.mp (hAN hx)
    omega
  have hN₀pos : 0 < N₀ := by
    have := ambient_le_of_mul_le hp hpN
    omega
  have hN₀scale : N₀ ≤ 64 * S ^ 3 := by
    simpa only [S, nvCubicScale] using
      ambient_le_sixty_four_mul_scale_cube hN₀pos
  have hbase : C ^ 8 * S ≤ h := by
    have hcoeff : 3 * C ^ 8 ≤ C ^ 10 := by
      calc
        3 * C ^ 8 ≤ C ^ 2 * C ^ 8 := by gcongr; nlinarith
        _ = C ^ 10 := by ring
    have hpell : 1 ≤ ell ^ nvLossLogExponent :=
      Nat.one_le_pow nvLossLogExponent ell (by omega)
    have hthree : 3 * (C ^ 8 * S) ≤ 3 * h := by
      calc
        3 * (C ^ 8 * S) = (3 * C ^ 8) * S := by ring
        _ ≤ C ^ 10 * S := Nat.mul_le_mul_right S hcoeff
        _ ≤ C ^ 10 * S * ell ^ nvLossLogExponent := by
          simpa using Nat.mul_le_mul_left (C ^ 10 * S) hpell
        _ = nvOneStepLoss N₀ := by
          simp only [nvOneStepLoss, C, S, ell]
        _ ≤ a := hloss.le
        _ ≤ 3 * h := hah
    exact Nat.le_of_mul_le_mul_left
      (by simpa only [mul_assoc] using hthree) (by norm_num)
  have hMge : C ≤ M := by
    dsimp only [M, nvInitialPolylog]
    calc
      nvMasterConstant = nvMasterConstant * 1 := by simp
      _ ≤ nvMasterConstant *
          nvBinaryLogScale N₀ ^ nvInitialLogExponent := by
        gcongr
        exact Nat.one_le_pow nvInitialLogExponent _ (by omega)
  have hbigCoeff : 62208 * C ^ 4 * S < h * M ^ 2 := by
    have h62208 : 62208 * C ^ 4 < C ^ 8 := by
      have : 62208 < C ^ 4 := by
        calc
          62208 < 4096 ^ 4 := by norm_num
          _ ≤ C ^ 4 := Nat.pow_le_pow_left hC 4
      calc
        62208 * C ^ 4 < C ^ 4 * C ^ 4 :=
          (Nat.mul_lt_mul_right (pow_pos hCpos 4)).2 this
        _ = C ^ 8 := by ring
    calc
      62208 * C ^ 4 * S < C ^ 8 * S := by gcongr
      _ ≤ h := hbase
      _ ≤ h * M ^ 2 := by
        exact Nat.le_mul_of_pos_right h (pow_pos hM 2)
  have hrootSq : R ^ 2 ≤ a * N₀ := by
    calc
      R ^ 2 ≤ p * (a * N) := by
        dsimp only [R]
        exact Nat.sqrt_le' _
      _ = a * (p * N) := by ring
      _ ≤ a * N₀ := Nat.mul_le_mul_left a hpN
  have hapos : 0 < a := by omega
  have hprodPos : 0 < p * (a * N) :=
    Nat.mul_pos hp (Nat.mul_pos hapos hNpos)
  have hRpos : 0 < R := by
    dsimp only [R]
    exact Nat.sqrt_pos.2 hprodPos
  have hrootSuccSq : (R + 1) ^ 2 ≤ 768 * h * S ^ 3 := by
    calc
      (R + 1) ^ 2 ≤ (2 * R) ^ 2 := by gcongr <;> omega
      _ = 4 * R ^ 2 := by ring
      _ ≤ 4 * (a * N₀) := by gcongr
      _ ≤ 4 * ((3 * h) * (64 * S ^ 3)) := by gcongr
      _ = 768 * h * S ^ 3 := by ring
  let T := C₀ * F * (8 * (R + 1) + 1)
  have hT : T ≤ 9 * C ^ 2 * (R + 1) := by
    have hCF : C₀ * F ≤ C ^ 2 := by
      calc
        C₀ * F ≤ C * C := Nat.mul_le_mul hC₀ hF
        _ = C ^ 2 := by ring
    dsimp only [T]
    calc
      C₀ * F * (8 * (R + 1) + 1) ≤
          C ^ 2 * (8 * (R + 1) + 1) := by gcongr
      _ ≤ C ^ 2 * (9 * (R + 1)) := by gcongr; nlinarith
      _ = 9 * C ^ 2 * (R + 1) := by ring
  have hTsq : T ^ 2 < (h * X) ^ 2 := by
    calc
      T ^ 2 ≤ (9 * C ^ 2 * (R + 1)) ^ 2 := Nat.pow_le_pow_left hT 2
      _ = 81 * C ^ 4 * (R + 1) ^ 2 := by ring
      _ ≤ 81 * C ^ 4 * (768 * h * S ^ 3) := by gcongr
      _ = (62208 * C ^ 4 * S) * (h * S ^ 2) := by ring
      _ < (h * M ^ 2) * (h * S ^ 2) := by
        exact Nat.mul_lt_mul_of_pos_right hbigCoeff
          (Nat.mul_pos hh (pow_pos hS 2))
      _ = (h * X) ^ 2 := by
        change (h * M ^ 2) * (h * S ^ 2) = (h * (S * M)) ^ 2
        ring
  have hTlt : T < h * X := by
    exact (Nat.pow_lt_pow_iff_left (by norm_num : 2 ≠ 0)).1 hTsq
  calc
    C₀ * F *
          (8 * (Nat.sqrt (p * (A.card * N)) + 1) + 1) *
            (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 2 =
        T * X ^ 2 := by rfl
    _ < (h * X) * X ^ 2 :=
      Nat.mul_lt_mul_of_pos_right hTlt (pow_pos hX 2)
    _ = (A.card / 2) *
        (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 3 := by
      change (h * X) * X ^ 2 = h * X ^ 3
      ring

/-- Rank one with the configured Nguyen--Vu parameters.  Unlike the earlier
ambient wrapper, this keeps the actual progression step through the residue
argument and therefore spends only `nvOneStepLoss`. -/
theorem configured_rank_one_terminal
    {A B : Finset ℕ} {N N₀ p s b n : ℕ}
    {R : GeneralizedAP} {t : ℤ} {Z : Finset ℤ}
    (hp : 0 < p) (hpN : p * N ≤ N₀)
    (hAN : A ⊆ Finset.Icc 1 N) (hBA : B ⊆ A)
    (hlarge : nvOneStepLoss N₀ * nvBinaryLogScale N < A.card)
    (hR : R.Proper) (hrank : R.rank = 1)
    (hside : ∀ i : Fin R.rank, 0 < R.length i)
    (hcontain : (({t} : Finset ℤ) + R.carrier) +
      natToIntFinset B.subsetSum ⊆ natToIntFinset A.subsetSum)
    (hcover : natToIntFinset B ⊆
      Z + iteratedDifference (n + 1) R.carrier)
    (hZ : Z.card ≤ nvStoppedRemainderTranslateCount 65 64)
    (hW : (A.card / 2) *
        (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 3 ≤
      nvRobustCubicLoss 64 * b * (2 ^ s) ^ 3)
    (hscaled : b * (2 ^ s) ^ R.rank ≤
      nvStoppedBudgetScaledCardFactor 64 * R.carrier.card)
    (hDU : 2 ^ s ≤ nvCubicScale N₀ * nvInitialPolylog N₀) :
    HasPMultipleSquareSubsetSum p A ∨
      ∃ d : ℕ, ∃ D : Finset ℕ,
        D ⊆ B ∧ 1 < d ∧
        B.card ≤ D.card + nvOneStepLoss N₀ ∧
        ∀ a ∈ D, d ∣ a := by
  obtain ⟨r, q, L, hq, _hrbase, hqstep, hL, hfamily⟩ :=
    exists_natAP_family_of_translated_rank_one_GAP
      R t hR hrank hside hcontain
  have hscaled₁ : b * (2 ^ s) ≤
      nvStoppedBudgetScaledCardFactor 64 * (L + 1) := by
    have hcard := carrier_card_eq_rank_one R hR hrank
    rw [hrank, pow_one, hcard] at hscaled
    simpa only [hL] using hscaled
  have hdominance := configured_rank_one_terminal_dominance
    hp hpN hAN hlarge nvRobustCubicLoss_le_master
      nvStoppedBudgetFactor_le_master
  have hLlarge :
      8 * (Nat.sqrt (p * (A.card * N)) + 1) < L :=
    rank_one_side_gt_of_cubic_budget hW hscaled₁ hDU hdominance
  have hLpos : 0 < L := by omega
  have hsumBound : A.subsetSum ⊆ Finset.Icc 0 (A.card * N) :=
    NVGeneration.subsetSum_subset_Icc_of_subset
      (U := A) (A := A) Finset.Subset.rfl hAN le_rfl
  have hzero : 0 ∈ B.subsetSum := by simp
  have hAP₀ : natAP r q L ⊆ A.subsetSum := by
    simpa only [Nat.add_zero] using hfamily 0 hzero
  have hqL : q * L ≤ A.card * N :=
    natAP_span_le_of_subsetSum_bound hsumBound hAP₀
  have hqW : q * ((A.card / 2) *
        (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 3) ≤
      2 * nvRobustCubicLoss 64 * nvStoppedBudgetScaledCardFactor 64 *
        (A.card * N) *
          (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 2 :=
    rank_one_step_budget_upper hW hscaled₁ hDU hLpos hqL
  have hA2 : 2 ≤ A.card := by
    have hloss := nvOneStepLoss_pos N₀
    have hell := nvBinaryLogScale_pos N
    have hmono : nvOneStepLoss N₀ ≤
        nvOneStepLoss N₀ * nvBinaryLogScale N :=
      Nat.le_mul_of_pos_right _ hell
    omega
  have hpq : p * q ≤
      384 * nvMasterConstant ^ 2 * nvCubicScale N₀ ^ 2 :=
    configured_rank_one_step_bound hp hpN hAN hA2 hqW
  have hNpos : 0 < N := by
    have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha⟩ := hAne
    have := Finset.mem_Icc.mp (hAN ha)
    omega
  have hN₀pos : 0 < N₀ := by
    have := ambient_le_of_mul_le hp hpN
    omega
  have hqH : q ≤ A.card * N := by
    calc
      q = q * 1 := by simp
      _ ≤ q * L := Nat.mul_le_mul_left q (by omega)
      _ ≤ A.card * N := hqL
  have hqN₀ : q ≤ N₀ ^ 2 := by
    have hcardN : A.card ≤ N := card_le_ambient_of_subset_Icc hAN
    have hNN₀ : N ≤ N₀ := ambient_le_of_mul_le hp hpN
    calc
      q ≤ A.card * N := hqH
      _ ≤ N * N := Nat.mul_le_mul_right N hcardN
      _ ≤ N₀ * N₀ := Nat.mul_le_mul hNN₀ hNN₀
      _ = N₀ ^ 2 := by ring
  have hsqrt : p * (A.card * N) ≤
      (Nat.sqrt (p * (A.card * N)) + 1) ^ 2 :=
    square_bound_of_sqrt_succ _
  have hbig : 64 * p * (A.card * N) ≤ L ^ 2 := by
    have hBsq :
        (8 * (Nat.sqrt (p * (A.card * N)) + 1)) ^ 2 < L ^ 2 := by
      nlinarith
    calc
      64 * p * (A.card * N) = 64 * (p * (A.card * N)) := by ring
      _ ≤ 64 * (Nat.sqrt (p * (A.card * N)) + 1) ^ 2 := by gcongr
      _ = (8 * (Nat.sqrt (p * (A.card * N)) + 1)) ^ 2 := by ring
      _ ≤ L ^ 2 := hBsq.le
  obtain ⟨hshort, hlong⟩ :=
    rank_one_location_bounds hp hq hLpos hqL hbig
  rcases rank_one_square_or_common_divisor (t := t) hp hq hAN hBA hR hrank
      hside hqstep hfamily hcover hZ hshort hlong with
    hsquare | ⟨d, D, hDB, hd, _hdq, hcard, hdiv⟩
  · exact Or.inl hsquare
  · refine Or.inr ⟨d, D, hDB, hd, ?_, hdiv⟩
    have hpq' : p * q ≤
        1024 * nvMasterConstant ^ 2 * nvCubicScale N₀ ^ 2 :=
      hpq.trans (by gcongr; norm_num)
    have hloss := configured_residue_loss_bound hN₀pos hq hqN₀ hpq'
    exact hcard.trans (Nat.add_le_add_left hloss D.card)

/-- Rank two with the configured common-step budget.  The archimedean
locator is kept as a separate hypothesis; all GAP extraction, properness,
and common-divisor loss estimates are completed here. -/
theorem configured_rank_two_terminal_of_locator
    {A B : Finset ℕ} {N N₀ p s b n : ℕ}
    {R : GeneralizedAP} {t : ℤ} {Z : Finset ℤ}
    (hp : 0 < p) (hpN : p * N ≤ N₀)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hlarge : nvOneStepLoss N₀ * nvBinaryLogScale N < A.card)
    (hR : R.Proper) (hrank : R.rank = 2)
    (hside : ∀ i : Fin R.rank, 0 < R.length i)
    (hcontain : (({t} : Finset ℤ) + R.carrier) +
      natToIntFinset B.subsetSum ⊆ natToIntFinset A.subsetSum)
    (hcover : natToIntFinset B ⊆
      Z + iteratedDifference (n + 1) R.carrier)
    (hZ : Z.card ≤ nvStoppedRemainderTranslateCount 65 64)
    (hW : (A.card / 2) *
        (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 3 ≤
      nvRobustCubicLoss 64 * b * (2 ^ s) ^ 3)
    (hscaled : b * (2 ^ s) ^ R.rank ≤
      nvStoppedBudgetScaledCardFactor 64 * R.carrier.card)
    (hDU : 2 ^ s ≤ nvCubicScale N₀ * nvInitialPolylog N₀)
    (hlocator : ∀ {r q₁ q₂ L₁ L₂ : ℕ},
      0 < q₁ → 0 < q₂ →
      (∀ u ∈ B.subsetSum, ∀ x ≤ L₁, ∀ y ≤ L₂,
        r + u + q₁ * x + q₂ * y ∈ A.subsetSum) →
      (∀ x₁ ≤ L₁, ∀ y₁ ≤ L₂,
        ∀ x₂ ≤ L₁, ∀ y₂ ≤ L₂,
          r + q₁ * x₁ + q₂ * y₁ = r + q₁ * x₂ + q₂ * y₂ →
          x₁ = x₂ ∧ y₁ = y₂) →
      q₁ * L₁ + q₂ * L₂ ≤ A.card * N →
      b * (2 ^ s) ^ 2 ≤
        nvStoppedBudgetScaledCardFactor 64 * ((L₁ + 1) * (L₂ + 1)) →
      (∀ u ∈ B.subsetSum, ∀ z₀ : ℕ, ∀ v : ℤ,
        ((r + u : ℕ) : ℤ) =
            (p : ℤ) * (z₀ : ℤ) ^ 2 + v * (q₁.gcd q₂ : ℕ) →
          ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
            0 < p * w ^ 2 ∧
            r + u + q₁ * x + q₂ * y = p * w ^ 2)) :
    HasPMultipleSquareSubsetSum p A ∨
      ∃ d : ℕ, ∃ D : Finset ℕ,
        D ⊆ B ∧ 1 < d ∧
        B.card ≤ D.card + nvOneStepLoss N₀ ∧
        ∀ a ∈ D, d ∣ a := by
  obtain ⟨r, q₁, q₂, L₁, L₂, hq₁, hq₂, _hrbase, hq₁step, hq₂step,
      hL₁, hL₂, hfamily, hinj⟩ :=
    exists_natGAP_two_family_of_translated_rank_two_GAP
      R t hR hrank hside hcontain
  have hL₁pos : 0 < L₁ := by
    simpa only [hL₁] using hside ⟨0, by omega⟩
  have hL₂pos : 0 < L₂ := by
    simpa only [hL₂] using hside ⟨1, by omega⟩
  have hscaled₂ : b * (2 ^ s) ^ 2 ≤
      nvStoppedBudgetScaledCardFactor 64 * ((L₁ + 1) * (L₂ + 1)) := by
    have hcard := carrier_card_eq_rank_two R hR hrank
    rw [hrank, hcard] at hscaled
    simpa only [hL₁, hL₂] using hscaled
  have hsumBound : A.subsetSum ⊆ Finset.Icc 0 (A.card * N) :=
    NVGeneration.subsetSum_subset_Icc_of_subset
      (U := A) (A := A) Finset.Subset.rfl hAN le_rfl
  have hzero : 0 ∈ B.subsetSum := by simp
  have hspan : q₁ * L₁ + q₂ * L₂ ≤ A.card * N := by
    apply natGAP_two_span_le_of_subsetSum_bound hsumBound
    intro x hx y hy
    simpa only [Nat.add_zero] using hfamily 0 hzero x hx y hy
  have hgspan : q₁.gcd q₂ * L₁ * L₂ ≤ A.card * N :=
    (gcd_mul_side_product_le_span_of_injective hq₁ hq₂ hinj).trans hspan
  have hgW : q₁.gcd q₂ * ((A.card / 2) *
        (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 3) ≤
      4 * nvRobustCubicLoss 64 * nvStoppedBudgetScaledCardFactor 64 *
        (A.card * N) *
          (nvCubicScale N₀ * nvInitialPolylog N₀) :=
    rank_two_common_step_budget_upper hW hscaled₂ hDU hL₁pos hL₂pos hgspan
  have hA2 : 2 ≤ A.card := by
    have hloss := nvOneStepLoss_pos N₀
    have hell := nvBinaryLogScale_pos N
    have hmono : nvOneStepLoss N₀ ≤
        nvOneStepLoss N₀ * nvBinaryLogScale N :=
      Nat.le_mul_of_pos_right _ hell
    omega
  have hpgM : p * q₁.gcd q₂ * nvInitialPolylog N₀ ^ 2 ≤
      768 * nvMasterConstant ^ 2 * nvCubicScale N₀ :=
    configured_rank_two_common_step_bound hp hpN hAN hA2 hgW
  have hg : 0 < q₁.gcd q₂ := Nat.gcd_pos_of_pos_left q₂ hq₁
  have hM : 0 < nvInitialPolylog N₀ := nvInitialPolylog_pos N₀
  have hpg : p * q₁.gcd q₂ ≤
      768 * nvMasterConstant ^ 2 * nvCubicScale N₀ := by
    have hmono : p * q₁.gcd q₂ ≤
        p * q₁.gcd q₂ * nvInitialPolylog N₀ ^ 2 :=
      Nat.le_mul_of_pos_right _ (pow_pos hM 2)
    exact hmono.trans hpgM
  have hpg' : p * q₁.gcd q₂ ≤
      1024 * nvMasterConstant ^ 2 * nvCubicScale N₀ ^ 2 := by
    calc
      p * q₁.gcd q₂ ≤ 768 * nvMasterConstant ^ 2 * nvCubicScale N₀ := hpg
      _ ≤ 1024 * nvMasterConstant ^ 2 * nvCubicScale N₀ := by gcongr; norm_num
      _ ≤ 1024 * nvMasterConstant ^ 2 * nvCubicScale N₀ ^ 2 := by
        gcongr
        have hS := nvCubicScale_pos N₀
        calc
          nvCubicScale N₀ = nvCubicScale N₀ * 1 := by simp
          _ ≤ nvCubicScale N₀ * nvCubicScale N₀ := by gcongr; omega
          _ = nvCubicScale N₀ ^ 2 := by ring
  have hNpos : 0 < N := by
    have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha⟩ := hAne
    have := Finset.mem_Icc.mp (hAN ha)
    omega
  have hN₀pos : 0 < N₀ := by
    have := ambient_le_of_mul_le hp hpN
    omega
  have hgH : q₁.gcd q₂ ≤ A.card * N := by
    calc
      q₁.gcd q₂ ≤ q₁ := Nat.gcd_le_left q₂ hq₁
      _ = q₁ * 1 := by simp
      _ ≤ q₁ * L₁ := Nat.mul_le_mul_left q₁ (by omega)
      _ ≤ q₁ * L₁ + q₂ * L₂ := Nat.le_add_right _ _
      _ ≤ A.card * N := hspan
  have hgN₀ : q₁.gcd q₂ ≤ N₀ ^ 2 := by
    have hcardN : A.card ≤ N := card_le_ambient_of_subset_Icc hAN
    have hNN₀ : N ≤ N₀ := ambient_le_of_mul_le hp hpN
    calc
      q₁.gcd q₂ ≤ A.card * N := hgH
      _ ≤ N * N := Nat.mul_le_mul_right N hcardN
      _ ≤ N₀ * N₀ := Nat.mul_le_mul hNN₀ hNN₀
      _ = N₀ ^ 2 := by ring
  rcases rank_two_square_or_common_divisor_of_locator hp hq₁ hq₂
      hR hrank hside hq₁step hq₂step hfamily hcover hZ
      (hlocator hq₁ hq₂ hfamily hinj hspan hscaled₂) with
    hsquare | ⟨d, D, hDB, hd, _hdg, hcard, hdiv⟩
  · exact Or.inl hsquare
  · refine Or.inr ⟨d, D, hDB, hd, ?_, hdiv⟩
    have hloss := configured_residue_loss_bound hN₀pos hg hgN₀ hpg'
    exact hcard.trans (Nat.add_le_add_left hloss D.card)

lemma configured_rank_zero_impossible
    {A : Finset ℕ} {N N₀ b : ℕ} {R : GeneralizedAP}
    (hlarge : nvOneStepLoss N₀ * nvBinaryLogScale N < A.card)
    (hR : R.Proper) (hrank : R.rank = 0)
    (hb : A.card / 2 ≤ b)
    (hbcarrier : b ≤ nvStoppedBudgetScaledCardFactor 64 * R.carrier.card) :
    False := by
  let C := nvMasterConstant
  let a := A.card
  let h := a / 2
  have hC : 4096 ≤ C := nvMasterConstant_ge_4096
  have hCpos : 0 < C := by omega
  have hloss : nvOneStepLoss N₀ < a := by
    calc
      nvOneStepLoss N₀ = nvOneStepLoss N₀ * 1 := by simp
      _ ≤ nvOneStepLoss N₀ * nvBinaryLogScale N := by
        gcongr
        exact nvBinaryLogScale_pos N
      _ < a := by simpa only [a] using hlarge
  have hthreeC : 3 * C ≤ nvOneStepLoss N₀ := by
    simp only [nvOneStepLoss]
    have hS := nvCubicScale_pos N₀
    have hell := nvBinaryLogScale_pos N₀
    calc
      3 * nvMasterConstant ≤ nvMasterConstant ^ 10 := by
        have h3 : 3 ≤ nvMasterConstant ^ 9 := by
          calc
            3 ≤ nvMasterConstant := by omega
            _ = nvMasterConstant ^ 1 := by simp
            _ ≤ nvMasterConstant ^ 9 :=
              Nat.pow_le_pow_right nvMasterConstant_pos (by omega)
        calc
          3 * nvMasterConstant ≤ nvMasterConstant ^ 9 * nvMasterConstant :=
            Nat.mul_le_mul_right _ h3
          _ = nvMasterConstant ^ 10 := by ring
      _ ≤ nvMasterConstant ^ 10 * nvCubicScale N₀ :=
        Nat.le_mul_of_pos_right _ hS
      _ ≤ nvMasterConstant ^ 10 * nvCubicScale N₀ *
          nvBinaryLogScale N₀ ^ nvLossLogExponent :=
        Nat.le_mul_of_pos_right _
          (pow_pos hell nvLossLogExponent)
  have hah : a ≤ 3 * h := by dsimp only [h]; omega
  have hCh : C < h := by
    have : 3 * C < 3 * h := (hthreeC.trans_lt hloss).trans_le hah
    exact (Nat.mul_lt_mul_left (by norm_num : 0 < 3)).1
      (by simpa only [mul_assoc] using this)
  have hcard : R.carrier.card = 1 := by
    rw [R.card_carrier_of_proper hR]
    have huniv : (Finset.univ : Finset (Fin R.rank)) = ∅ := by
      ext i
      exact Fin.elim0 (hrank ▸ i)
    rw [huniv]
    simp
  have hbC : b ≤ C := by
    calc
      b ≤ nvStoppedBudgetScaledCardFactor 64 * R.carrier.card := hbcarrier
      _ = nvStoppedBudgetScaledCardFactor 64 := by rw [hcard]; simp
      _ ≤ nvMasterConstant := nvStoppedBudgetFactor_le_master
      _ = C := rfl
  have : h ≤ C := by
    simpa only [h] using hb.trans hbC
  omega

/-- Complete one divisor-descent step, conditional only on the quantitative
rank-two archimedean locator.  All structural output and the rank-zero/one
branches are discharged here. -/
theorem configured_nguyen_vu_one_step_of_rank_two_locator
    {A : Finset ℕ} {N N₀ p : ℕ}
    (hp : 0 < p) (hpN : p * N ≤ N₀)
    (hAN : A ⊆ Finset.Icc 1 N)
    (hlarge : nvOneStepLoss N₀ * nvBinaryLogScale N < A.card)
    (hlocator : ∀ {B : Finset ℕ} {s b r q₁ q₂ L₁ L₂ : ℕ},
      B ⊆ A → A.card - nvOneStepLoss N₀ ≤ B.card →
      0 < q₁ → 0 < q₂ →
      (∀ u ∈ B.subsetSum, ∀ x ≤ L₁, ∀ y ≤ L₂,
        r + u + q₁ * x + q₂ * y ∈ A.subsetSum) →
      (∀ x₁ ≤ L₁, ∀ y₁ ≤ L₂,
        ∀ x₂ ≤ L₁, ∀ y₂ ≤ L₂,
          r + q₁ * x₁ + q₂ * y₁ = r + q₁ * x₂ + q₂ * y₂ →
          x₁ = x₂ ∧ y₁ = y₂) →
      q₁ * L₁ + q₂ * L₂ ≤ A.card * N →
      (A.card / 2) *
          (nvCubicScale N₀ * nvInitialPolylog N₀) ^ 3 ≤
        nvRobustCubicLoss 64 * b * (2 ^ s) ^ 3 →
      b * (2 ^ s) ^ 2 ≤
        nvStoppedBudgetScaledCardFactor 64 * ((L₁ + 1) * (L₂ + 1)) →
      2 ^ s ≤ nvCubicScale N₀ * nvInitialPolylog N₀ →
      ∀ u ∈ B.subsetSum, ∀ z₀ : ℕ, ∀ v : ℤ,
        ((r + u : ℕ) : ℤ) =
            (p : ℤ) * (z₀ : ℤ) ^ 2 + v * (q₁.gcd q₂ : ℕ) →
          ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
            0 < p * w ^ 2 ∧
            r + u + q₁ * x + q₂ * y = p * w ^ 2) :
    HasPMultipleSquareSubsetSum p A ∨
      ∃ d : ℕ, ∃ D : Finset ℕ,
        D ⊆ A ∧ 1 < d ∧ (∀ a ∈ D, d ∣ a) ∧
        A.card ≤ D.card + 2 * nvOneStepLoss N₀ := by
  obtain ⟨s, b, G, m, J, B, i, j, P, Q, R, d, t, E, F, Z,
      hW, _hMdyadic, hDU, hbhalf, _hbcommon, _hMm, _hJcard,
      hBreserve, hBcard, _hcapacity, _hiJ, _hjJ, _hij,
      _hQrank, _hQbase, _hQproper, _hPproper, _hPrank,
      _hcommonP, _hPbox, _hdiffP, _hQbox, _hQcarrier,
      hRproper, hRrank, hside, hbcarrier, hscaled, _hd,
      hcontain, _hEsub, _hEcard, _hFsub, _hFcard, _hBcovermid,
      hZcard, hcover⟩ :=
    exists_configured_nguyen_vu_rank_two_structure hp hpN hAN hlarge
  have hBA : B ⊆ A := hBreserve.trans G.reserve_subset
  have hsumSub : B.subsetSum ⊆ G.reserve.subsetSum :=
    Finset.subsetSum_mono hBreserve
  have hcastSub : natToIntFinset B.subsetSum ⊆
      natToIntFinset G.reserve.subsetSum := by
    exact Finset.image_mono _ hsumSub
  have hcontainB : (({t} : Finset ℤ) + R.carrier) +
      natToIntFinset B.subsetSum ⊆ natToIntFinset A.subsetSum :=
    (Finset.add_subset_add_left hcastSub).trans hcontain
  have hcoverB : natToIntFinset B ⊆
      Z + iteratedDifference ((d + 2) + 1) R.carrier := by
    convert hcover using 1 <;> omega
  have hLossA : nvOneStepLoss N₀ < A.card := by
    calc
      nvOneStepLoss N₀ = nvOneStepLoss N₀ * 1 := by simp
      _ ≤ nvOneStepLoss N₀ * nvBinaryLogScale N := by
        gcongr
        exact nvBinaryLogScale_pos N
      _ < A.card := hlarge
  have finishDivisor
      {D : Finset ℕ}
      (hDB : D ⊆ B)
      (hcard : B.card ≤ D.card + nvOneStepLoss N₀) :
      D ⊆ A ∧ A.card ≤ D.card + 2 * nvOneStepLoss N₀ := by
    constructor
    · exact hDB.trans hBA
    · omega
  rcases (show R.rank = 0 ∨ R.rank = 1 ∨ R.rank = 2 by omega) with
    hrank0 | hrank1 | hrank2
  · exact (configured_rank_zero_impossible hlarge hRproper hrank0
      hbhalf hbcarrier).elim
  · rcases configured_rank_one_terminal hp hpN hAN hBA hlarge
        hRproper hrank1 hside hcontainB hcoverB hZcard hW hscaled hDU with
      hsquare | ⟨e, D, hDB, he, hcard, hdiv⟩
    · exact Or.inl hsquare
    · obtain ⟨hDA, hcardA⟩ := finishDivisor hDB hcard
      exact Or.inr ⟨e, D, hDA, he, hdiv, hcardA⟩
  · have hlocator' : ∀ {r q₁ q₂ L₁ L₂ : ℕ},
        0 < q₁ → 0 < q₂ →
        (∀ u ∈ B.subsetSum, ∀ x ≤ L₁, ∀ y ≤ L₂,
          r + u + q₁ * x + q₂ * y ∈ A.subsetSum) →
        (∀ x₁ ≤ L₁, ∀ y₁ ≤ L₂,
          ∀ x₂ ≤ L₁, ∀ y₂ ≤ L₂,
            r + q₁ * x₁ + q₂ * y₁ = r + q₁ * x₂ + q₂ * y₂ →
            x₁ = x₂ ∧ y₁ = y₂) →
        q₁ * L₁ + q₂ * L₂ ≤ A.card * N →
        b * (2 ^ s) ^ 2 ≤
          nvStoppedBudgetScaledCardFactor 64 * ((L₁ + 1) * (L₂ + 1)) →
        ∀ u ∈ B.subsetSum, ∀ z₀ : ℕ, ∀ v : ℤ,
          ((r + u : ℕ) : ℤ) =
              (p : ℤ) * (z₀ : ℤ) ^ 2 + v * (q₁.gcd q₂ : ℕ) →
            ∃ x ≤ L₁, ∃ y ≤ L₂, ∃ w : ℕ,
              0 < p * w ^ 2 ∧
              r + u + q₁ * x + q₂ * y = p * w ^ 2 := by
      intro r q₁ q₂ L₁ L₂ hq₁ hq₂ hfamily hinj hspan hscaled₂
      exact hlocator hBA hBcard hq₁ hq₂ hfamily hinj hspan
        hW hscaled₂ hDU
    rcases configured_rank_two_terminal_of_locator hp hpN hAN hlarge
        hRproper hrank2 hside hcontainB hcoverB hZcard hW hscaled hDU
        hlocator' with
      hsquare | ⟨e, D, hDB, he, hcard, hdiv⟩
    · exact Or.inl hsquare
    · obtain ⟨hDA, hcardA⟩ := finishDivisor hDB hcard
      exact Or.inr ⟨e, D, hDA, he, hdiv, hcardA⟩

end NVGeneration
end Erdos587
