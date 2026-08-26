import ErdosProblems.Erdos489.HeilbronnRohrbach
import ErdosProblems.Erdos489.SieveGaps
import ErdosProblems.Erdos489.DivisorWitness
import ErdosProblems.Erdos489.DistinctWitnesses

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
namespace Erdos489

/-- Avoid the first `R` enumerated forbidden moduli. -/
def finiteDivisorSifted (p : ℕ → Prop) (R n : ℕ) : Prop :=
  ∀ a ∈ (List.range R).map (Nat.nth p), ¬a ∣ n

noncomputable instance finiteDivisorSiftedDecidable
    (p : ℕ → Prop) (R : ℕ) : DecidablePred (finiteDivisorSifted p R) :=
  Classical.decPred _

 theorem finiteDivisorSifted_periodic (p : ℕ → Prop) (R : ℕ) :
    Function.Periodic (finiteDivisorSifted p R)
      ((List.range R).map (Nat.nth p)).prod :=
  avoidList_periodic _

 theorem divisorSifted_imp_finite (p : ℕ → Prop) [DecidablePred p]
    (hp : Set.Infinite {n | p n}) (R n : ℕ) :
    divisorSifted p n → finiteDivisorSifted p R n := by
  intro hn a ha
  rcases List.mem_map.mp ha with ⟨r, hr, rfl⟩
  exact hn.2 _ (Nat.nth_mem_of_infinite hp r)

 theorem finiteDivisorSifted_pos
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (hp2 : ∀ n, p n → 2 ≤ n) (R n : ℕ) (hR : 0 < R)
    (hn : finiteDivisorSifted p R n) : 0 < n := by
  by_contra hn0
  have heq : n = 0 := by omega
  have hmem : Nat.nth p 0 ∈ (List.range R).map (Nat.nth p) :=
    List.mem_map.mpr ⟨0, List.mem_range.mpr hR, rfl⟩
  apply hn (Nat.nth p 0) hmem
  rw [heq]
  exact dvd_zero _

/-- Prefix/full disagreement points below `M`. -/
noncomputable def sieveMismatch (p : ℕ → Prop) (R M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range M).filter fun n =>
    finiteDivisorSifted p R n ∧ ¬divisorSifted p n

 theorem sieveMismatch_card_cast_le
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (hp2 : ∀ n, p n → 2 ≤ n)
    (R M : ℕ) (hR : 0 < R) (ε : ℝ)
    (htail : ∀ T : Finset ℕ, (∀ r ∈ T, R ≤ r) →
      (∑ r ∈ T, ((Nat.nth p r : ℝ)⁻¹)) ≤ ε) :
    ((sieveMismatch p R M).card : ℝ) ≤
      (M : ℝ) * ε + (Nat.count p M : ℝ) := by
  classical
  let S := sieveMismatch p R M
  let rank := divisorWitnessRank p
  let a := Nat.nth p
  have hinterval : ∀ n ∈ S, 0 ≤ n ∧ n ≤ 0 + M := by
    intro n hn
    have hh : n ∈ sieveMismatch p R M := by simpa [S] using hn
    have hnr := Finset.mem_range.mp (Finset.mem_filter.mp hh).1
    omega
  have hfinite : ∀ n ∈ S, finiteDivisorSifted p R n := by
    intro n hn
    have hh : n ∈ sieveMismatch p R M := by simpa [S] using hn
    exact (Finset.mem_filter.mp hh).2.1
  have hnotfull : ∀ n ∈ S, ¬divisorSifted p n := by
    intro n hn
    have hh : n ∈ sieveMismatch p R M := by simpa [S] using hn
    exact (Finset.mem_filter.mp hh).2.2
  have hpos : ∀ n ∈ S, 0 < n := by
    intro n hn
    exact finiteDivisorSifted_pos p hp hp2 R n hR (hfinite n hn)
  have hcov : ∀ n ∈ S, ∃ d, p d ∧ d ∣ n := by
    intro n hn
    have hnf := hnotfull n hn
    rw [divisorSifted] at hnf
    push_neg at hnf
    exact hnf (hpos n hn)
  have hdvd : ∀ n ∈ S, a (rank n) ∣ n := by
    intro n hn
    exact nth_divisorWitnessRank_dvd p n (hcov n hn)
  have hrank : ∀ n ∈ S, R ≤ rank n := by
    intro n hn
    apply le_divisorWitnessRank_of_avoid_prefix p n R (hcov n hn)
    exact hfinite n hn
  have hmass : (∑ r ∈ S.image rank, ((a r : ℝ)⁻¹)) ≤ ε := by
    apply htail
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨n, hn, rfl⟩
    exact hrank n hn
  have ha : ∀ r, 0 < a r := by
    intro r
    dsimp [a]
    have hh := hp2 _ (Nat.nth_mem_of_infinite hp r)
    exact lt_of_lt_of_le (by omega : 0 < 2) hh
  have hcharge0 := interval_label_card_le_reciprocal_mass
    S 0 M a rank ha hinterval hdvd
  have hcharge : (S.card : ℝ) ≤
      (M : ℝ) * ε + ((S.image rank).card : ℝ) := by
    calc
      (S.card : ℝ) ≤ (M : ℝ) *
          (∑ r ∈ S.image rank, ((a r : ℝ)⁻¹)) + (S.image rank).card := hcharge0
      _ ≤ (M : ℝ) * ε + (S.image rank).card := by gcongr
  have himage : (S.image rank).card ≤ Nat.count p M := by
    have hsubset : S.image rank ⊆ Finset.range (Nat.count p M) := by
      intro r hr
      apply Finset.mem_range.mpr
      rcases Finset.mem_image.mp hr with ⟨n, hn, rfl⟩
      have hh : n ∈ sieveMismatch p R M := by simpa [S] using hn
      have hnM := Finset.mem_range.mp (Finset.mem_filter.mp hh).1
      have hale : a (rank n) ≤ n := Nat.le_of_dvd (hpos n hn) (hdvd n hn)
      exact (Nat.lt_nth_iff_count_lt hp).2 (lt_of_le_of_lt hale hnM)
    simpa using Finset.card_le_card hsubset
  dsimp [S] at hcharge ⊢
  calc
    ((sieveMismatch p R M).card : ℝ) ≤
        (M : ℝ) * ε + ((sieveMismatch p R M).image rank).card := by
      simpa using hcharge
    _ ≤ (M : ℝ) * ε + (Nat.count p M : ℝ) := by
      gcongr

/-- Starts below `x` whose length-`H` window contains a finite/full sieve
mismatch. -/
noncomputable def badGapStarts (p : ℕ → Prop) (R H x : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (H + 1)).biUnion fun k =>
    (Finset.range x).filter fun n => n + k ∈ sieveMismatch p R (x + H + 1)

 theorem badGapStarts_subset_range (p : ℕ → Prop) (R H x : ℕ) :
    badGapStarts p R H x ⊆ Finset.range x := by
  classical
  intro n hn
  rcases Finset.mem_biUnion.mp hn with ⟨k, hk, hnk⟩
  exact (Finset.mem_filter.mp hnk).1

 theorem badGapStarts_card_le (p : ℕ → Prop) (R H x : ℕ) :
    (badGapStarts p R H x).card ≤
      (H + 1) * (sieveMismatch p R (x + H + 1)).card := by
  classical
  unfold badGapStarts
  have hfiber : ∀ k ∈ Finset.range (H + 1),
      ((Finset.range x).filter fun n =>
        n + k ∈ sieveMismatch p R (x + H + 1)).card ≤
          (sieveMismatch p R (x + H + 1)).card := by
    intro k hk
    let T := (Finset.range x).filter fun n =>
      n + k ∈ sieveMismatch p R (x + H + 1)
    have himage : T.image (fun n => n + k) ⊆
        sieveMismatch p R (x + H + 1) := by
      intro m hm
      rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
      exact (Finset.mem_filter.mp hn).2
    calc
      ((Finset.range x).filter fun n =>
          n + k ∈ sieveMismatch p R (x + H + 1)).card = T.card := rfl
      _ = (T.image (fun n => n + k)).card :=
        (Finset.card_image_of_injective T (add_left_injective k)).symm
      _ ≤ (sieveMismatch p R (x + H + 1)).card :=
        Finset.card_le_card himage
  have h := Finset.card_biUnion_le_card_mul (Finset.range (H + 1))
    (fun k => (Finset.range x).filter fun n =>
      n + k ∈ sieveMismatch p R (x + H + 1))
    (sieveMismatch p R (x + H + 1)).card hfiber
  simpa using h

/-- Outside `badGapStarts`, full and finite sieves agree throughout the
window inspected by the truncated cost. -/
theorem sieve_window_agree_of_not_bad
    (p : ℕ → Prop) [DecidablePred p]
    (hp : Set.Infinite {n | p n}) (R H x n : ℕ)
    (hnx : n < x) (hgood : n ∉ badGapStarts p R H x) :
    ∀ k, k ≤ H →
      (divisorSifted p (n + k) ↔ finiteDivisorSifted p R (n + k)) := by
  classical
  intro k hk
  have hkRange : k ∈ Finset.range (H + 1) := Finset.mem_range.mpr (by omega)
  constructor
  · exact divisorSifted_imp_finite p hp R (n + k)
  · intro hfinite
    by_contra hfull
    have hm : n + k ∈ sieveMismatch p R (x + H + 1) := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by omega), hfinite, hfull⟩
    apply hgood
    apply Finset.mem_biUnion.mpr
    exact ⟨k, hkRange, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnx, hm⟩⟩

end Erdos489
