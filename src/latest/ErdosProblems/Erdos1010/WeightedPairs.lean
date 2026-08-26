import Mathlib

/-!
# Finite weighted-pair bounds for Erdős 1010

The weights are integers. Unordered pairs are two-element finite subsets,
and negative excesses contribute zero. All sums are finite.
-/

open Finset

namespace Erdos1010

variable {V : Type*} [DecidableEq V]

/-- Total positive excess of unordered pairs over the threshold `k`. -/
def pairExcess (s : Finset V) (w : V → ℤ) (k : ℤ) : ℤ :=
  ∑ p ∈ s.powersetCard 2, max ((∑ v ∈ p, w v) - k) 0

lemma pairExcess_nonneg (s : Finset V) (w : V → ℤ) (k : ℤ) :
    0 ≤ pairExcess s w k := by
  exact sum_nonneg fun _ _ ↦ le_max_right _ _

lemma pairExcess_threshold_antitone (s : Finset V) (w : V → ℤ)
    {k l : ℤ} (hkl : k ≤ l) : pairExcess s w l ≤ pairExcess s w k := by
  exact sum_le_sum fun _ _ ↦ max_le_max (sub_le_sub_left hkl _) le_rfl

lemma pairExcess_eq_zero_of_card_lt (s : Finset V) (w : V → ℤ) (k : ℤ)
    (hs : s.card < 2) : pairExcess s w k = 0 := by
  unfold pairExcess
  rw [powersetCard_eq_empty.mpr hs, sum_empty]

lemma pairExcess_insert (s : Finset V) (w : V → ℤ) (k : ℤ)
    {a : V} (ha : a ∉ s) :
    pairExcess (insert a s) w k = pairExcess s w k +
      ∑ b ∈ s, max (w a + w b - k) 0 := by
  have hsplit : (insert a s).powersetCard 2 =
      s.powersetCard 2 ∪ s.image (fun b ↦ ({a, b} : Finset V)) := by
    rw [powersetCard_succ_insert ha 1, powersetCard_one]
    simp only [map_eq_image, image_image, Function.comp_def,
      Function.Embedding.coeFn_mk]
  have hdis : Disjoint (s.powersetCard 2)
      (s.image (fun b ↦ ({a, b} : Finset V))) := by
    apply disjoint_left.mpr
    intro p hp hq
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hq
    exact ha ((mem_powersetCard.mp hp).1 (by simp))
  unfold pairExcess
  rw [hsplit, sum_union hdis, sum_image]
  · congr 1
    apply sum_congr rfl
    intro b hb
    rw [sum_pair (ne_of_mem_of_not_mem hb ha).symm]
  · intro b hb c hc h
    have heq : ({a, b} : Finset V) = {a, c} := h
    have : b ∈ ({a, c} : Finset V) := heq ▸ (by simp : b ∈ ({a, b} : Finset V))
    exact mem_singleton.mp ((mem_insert.mp this).resolve_left
      (ne_of_mem_of_not_mem hb ha))

lemma pairExcess_eq_zero_of_pair_le (s : Finset V) (w : V → ℤ) (k : ℤ)
    (h : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → w a + w b ≤ k) :
    pairExcess s w k = 0 := by
  apply sum_eq_zero
  intro p hp
  obtain ⟨hp, hc⟩ := mem_powersetCard.mp hp
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hc
  have ha : a ∈ s := hp (by simp)
  have hb : b ∈ s := hp (by simp)
  simp only [sum_pair hab]
  exact max_eq_right (sub_nonpos.mpr (h a ha b hb hab))

/-- A pair of bounded weights has its excess bounded by its product. -/
lemma mul_pair_excess_le {x y k : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxk : x ≤ k) (hyk : y ≤ k) :
    k * max (x + y - k) 0 ≤ x * y := by
  by_cases h : x + y - k ≤ 0
  · rw [max_eq_right h, mul_zero]
    exact mul_nonneg hx hy
  · rw [max_eq_left (by omega)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hxk) (sub_nonneg.mpr hyk)]

/-- Positive pairs intersect when the total weight is at most `2*k+1`. -/
lemma positive_pairs_not_disjoint (s : Finset V) (w : V → ℤ) (k : ℤ)
    (hw : ∀ v ∈ s, 0 ≤ w v) (hs : ∑ v ∈ s, w v ≤ 2 * k + 1)
    {p q : Finset V} (hp : p ⊆ s) (hq : q ⊆ s)
    (hpw : k < ∑ v ∈ p, w v) (hqw : k < ∑ v ∈ q, w v) :
    ¬Disjoint p q := by
  intro hd
  have hsub : p ∪ q ⊆ s := union_subset hp hq
  have hsum := sum_le_sum_of_subset_of_nonneg hsub (fun v hv _ ↦ hw v hv)
  rw [sum_union hd] at hsum
  omega

lemma star_excess_bound (s : Finset V) (w : V → ℤ) (x k e : ℤ)
    (hk : 0 ≤ k) (he : 0 ≤ e) (hx : x ≤ k)
    (hw : ∀ b ∈ s, 0 ≤ w b ∧ w b ≤ k)
    (hs : x + ∑ b ∈ s, w b ≤ 2 * k + e) :
    (∑ b ∈ s, max (x + w b - k) 0) ≤ k + e := by
  let L := s.filter fun b ↦ k < x + w b
  have hL : L ⊆ s := filter_subset _ _
  have hsum : (∑ b ∈ s, max (x + w b - k) 0) =
      ∑ b ∈ L, (x + w b - k) := by
    calc
      _ = ∑ b ∈ L, max (x + w b - k) 0 := by
        symm
        apply sum_subset hL
        intro b hb hbL
        have : x + w b ≤ k := by simpa [L, hb] using hbL
        exact max_eq_right (by omega)
      _ = _ := sum_congr rfl fun b hb ↦ max_eq_left
        (by have := (mem_filter.mp hb).2; omega)
  rw [hsum]
  by_cases hn : 2 ≤ L.card
  · have hsub : (∑ b ∈ L, w b) ≤ ∑ b ∈ s, w b :=
      sum_le_sum_of_subset_of_nonneg hL fun b hb _ ↦ (hw b hb).1
    have hcalc : (∑ b ∈ L, (x + w b - k)) =
        (∑ b ∈ L, w b) + (L.card : ℤ) * (x - k) := by
      simp_rw [show ∀ b, x + w b - k = w b + (x - k) by intro b; ring]
      simp [sum_add_distrib, mul_comm]
      ring
    rw [hcalc]
    have hn' : (2 : ℤ) ≤ L.card := by exact_mod_cast hn
    have := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hn')
      (sub_nonpos.mpr hx)
    nlinarith
  · have hn' : (L.card : ℤ) ≤ 1 := by exact_mod_cast (show L.card ≤ 1 by omega)
    calc
      _ ≤ ∑ _b ∈ L, k := sum_le_sum fun b hb ↦ by
        have := (hw b (hL hb)).2
        omega
      _ = (L.card : ℤ) * k := by simp [mul_comm]
      _ ≤ k := by nlinarith
      _ ≤ k + e := by omega

/-- Removing vertices that cannot occur in a positive pair preserves the excess. -/
lemma pairExcess_restrict (s t : Finset V) (w : V → ℤ) (k : ℤ)
    (ht : t ⊆ s)
    (h : ∀ a ∈ s, ∀ b ∈ s, a ∉ t → w a + w b ≤ k) :
    pairExcess s w k = pairExcess t w k := by
  symm
  apply sum_subset (powersetCard_mono ht)
  intro p hp hpt
  obtain ⟨hps, hc⟩ := mem_powersetCard.mp hp
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hc
  have ha : a ∈ s := hps (by simp)
  have hb : b ∈ s := hps (by simp)
  have ht' : ¬ (a ∈ t ∧ b ∈ t) := by
    simpa [mem_powersetCard, insert_subset_iff, singleton_subset_iff, hab] using hpt
  rw [sum_pair hab]
  apply max_eq_right
  by_cases hat : a ∈ t
  · have hbt : b ∉ t := fun hb ↦ ht' ⟨hat, hb⟩
    have := h b hb a ha hbt
    omega
  · exact sub_nonpos.mpr (h a ha b hb hat)

lemma pairExcess_triple (w : V → ℤ) (k : ℤ) {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    pairExcess {a, b, c} w k = max (w a + w b - k) 0 +
      max (w a + w c - k) 0 + max (w b + w c - k) 0 := by
  rw [pairExcess_insert {b, c} w k (by simp [hab, hac]),
    pairExcess_insert {c} w k (by simp [hbc]),
    pairExcess_eq_zero_of_card_lt {c} w k (by simp)]
  simp only [sum_singleton, sum_pair hbc, zero_add]
  ring

/-- The common bound behind both weighted-pair estimates: `e = 0` or `e = 1`. -/
lemma pairExcess_bound (s : Finset V) (w : V → ℤ) (k e : ℤ)
    (hk : 0 ≤ k) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hw : ∀ v ∈ s, 0 ≤ w v ∧ w v ≤ k)
    (hs : ∑ v ∈ s, w v ≤ 2 * k + e) :
    pairExcess s w k ≤ k + 2 * e := by
  by_cases hs0 : s.Nonempty
  · obtain ⟨a, ha, hmax⟩ := s.exists_max_image w hs0
    by_cases hstar : ∀ b ∈ s.erase a, ∀ c ∈ s.erase a, b ≠ c → w b + w c ≤ k
    · have hzero := pairExcess_eq_zero_of_pair_le (s.erase a) w k hstar
      have hsum : w a + ∑ b ∈ s.erase a, w b ≤ 2 * k + e := by
        rwa [← sum_erase_add _ _ ha, add_comm] at hs
      have hbound := star_excess_bound (s.erase a) w (w a) k e hk he (hw a ha).2
        (fun b hb ↦ hw b (mem_of_mem_erase hb)) hsum
      rw [← insert_erase ha, pairExcess_insert _ _ _ (notMem_erase _ _), hzero, zero_add]
      exact hbound.trans (by omega)
    · push Not at hstar
      obtain ⟨b, hb0, c, hc0, hbc, hpos⟩ := hstar
      have hb := mem_of_mem_erase hb0
      have hc := mem_of_mem_erase hc0
      have hab : a ≠ b := (ne_of_mem_erase hb0).symm
      have hac : a ≠ c := (ne_of_mem_erase hc0).symm
      have htri : ({a, b, c} : Finset V) ⊆ s := by
        simp [insert_subset_iff, ha, hb, hc]
      have hrestrict : pairExcess s w k = pairExcess {a, b, c} w k := by
        apply pairExcess_restrict s {a, b, c} w k htri
        intro d hd v hv hdout
        have hda : d ≠ a := by
          intro h
          exact hdout (by simp [h])
        have hdb : d ≠ b := by
          intro h
          exact hdout (by simp [h])
        have hdc : d ≠ c := by
          intro h
          exact hdout (by simp [h])
        have hfour : ({a, b, c, d} : Finset V) ⊆ s := by
          simp [insert_subset_iff, ha, hb, hc, hd]
        have hsum := sum_le_sum_of_subset_of_nonneg hfour
          (fun v hv _ ↦ (hw v hv).1)
        simp [hab, hac, hbc, hda.symm, hdb.symm, hdc.symm] at hsum
        have hvmax := hmax v hv
        omega
      rw [hrestrict, pairExcess_triple w k hab hac hbc]
      have hba := hmax b hb
      have hca := hmax c hc
      rw [max_eq_left (by omega : 0 ≤ w a + w b - k),
        max_eq_left (by omega : 0 ≤ w a + w c - k),
        max_eq_left (by omega : 0 ≤ w b + w c - k)]
      have hsum := sum_le_sum_of_subset_of_nonneg htri
        (fun v hv _ ↦ (hw v hv).1)
      simp [hab, hac, hbc] at hsum
      omega
  · have : s = ∅ := not_nonempty_iff_eq_empty.mp hs0
    subst s
    rw [pairExcess_eq_zero_of_card_lt ∅ w k (by simp)]
    omega

lemma pairExcess_le (s : Finset V) (w : V → ℤ) (k : ℤ)
    (hk : 0 ≤ k) (hw : ∀ v ∈ s, 0 ≤ w v ∧ w v ≤ k)
    (hs : ∑ v ∈ s, w v ≤ 2 * k) : pairExcess s w k ≤ k := by
  simpa using pairExcess_bound s w k 0 hk le_rfl (by omega) hw (by simpa using hs)

lemma pairExcess_le_add_two (s : Finset V) (w : V → ℤ) (k : ℤ)
    (hk : 0 ≤ k) (hw : ∀ v ∈ s, 0 ≤ w v ∧ w v ≤ k)
    (hs : ∑ v ∈ s, w v ≤ 2 * k + 1) : pairExcess s w k ≤ k + 2 := by
  simpa using pairExcess_bound s w k 1 hk (by omega) le_rfl hw hs

/-- The quadratic estimate for arbitrary total weight; no density hypothesis. -/
lemma pairExcess_quadratic_bound (s : Finset V) (w : V → ℤ) (k : ℤ)
    (hw : ∀ v ∈ s, 0 ≤ w v ∧ w v ≤ k) :
    2 * k * pairExcess s w k ≤ (∑ v ∈ s, w v) ^ 2 - ∑ v ∈ s, (w v) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp [pairExcess_eq_zero_of_card_lt ∅ w k (by simp)]
  | @insert a s ha ih =>
    have hwa := hw a (mem_insert_self _ _)
    have hws : ∀ v ∈ s, 0 ≤ w v ∧ w v ≤ k :=
      fun v hv ↦ hw v (mem_insert_of_mem hv)
    have hi := ih hws
    have hcross : k * (∑ v ∈ s, max (w a + w v - k) 0) ≤
        w a * ∑ v ∈ s, w v := by
      rw [mul_sum, mul_sum]
      exact sum_le_sum fun v hv ↦ mul_pair_excess_le hwa.1 (hws v hv).1
        hwa.2 (hws v hv).2
    rw [pairExcess_insert s w k ha, sum_insert ha, sum_insert ha]
    nlinarith

lemma pairExcess_two_sides_quadratic (A B : Finset V) (w : V → ℤ) (k D : ℤ)
    (hA : ∀ v ∈ A, 0 ≤ w v ∧ w v ≤ k)
    (hB : ∀ v ∈ B, 0 ≤ w v ∧ w v ≤ k)
    (hsA : ∑ v ∈ A, w v = D) (hsB : ∑ v ∈ B, w v = D) :
    k * (pairExcess A w k + pairExcess B w k) ≤ D * (D - 1) := by
  have hqa := pairExcess_quadratic_bound A w k hA
  have hqb := pairExcess_quadratic_bound B w k hB
  have hsqa : D ≤ ∑ v ∈ A, (w v) ^ 2 := by
    rw [← hsA]
    exact sum_le_sum fun v _ ↦ Int.le_self_sq (w v)
  have hsqb : D ≤ ∑ v ∈ B, (w v) ^ 2 := by
    rw [← hsB]
    exact sum_le_sum fun v _ ↦ Int.le_self_sq (w v)
  rw [hsA] at hqa
  rw [hsB] at hqb
  nlinarith

/-- If the hub has the threshold weight and all remaining weight fits below
the threshold, exactly the hub pairs contribute. -/
lemma pairExcess_hub (s : Finset V) (w : V → ℤ) (k : ℤ) (u : V)
    (hu : u ∈ s) (hwu : w u = k) (hw : ∀ v ∈ s.erase u, 0 ≤ w v)
    (hs : ∑ v ∈ s.erase u, w v ≤ k) :
    pairExcess s w k = ∑ v ∈ s.erase u, w v := by
  have hz : pairExcess (s.erase u) w k = 0 := by
    apply pairExcess_eq_zero_of_pair_le
    intro a ha b hb hab
    have hsub : ({a, b} : Finset V) ⊆ s.erase u := by simp [insert_subset_iff, ha, hb]
    have hsum := sum_le_sum_of_subset_of_nonneg hsub (fun v hv _ ↦ hw v hv)
    rw [sum_pair hab] at hsum
    omega
  calc
    pairExcess s w k = pairExcess (insert u (s.erase u)) w k := by rw [insert_erase hu]
    _ = _ := by
      rw [pairExcess_insert _ _ _ (notMem_erase _ _), hz, zero_add]
      apply sum_congr rfl
      intro v hv
      rw [hwu]
      have heq : k + w v - k = w v := by ring
      rw [heq, max_eq_left (hw v hv)]

lemma pair_weight_le_total (s : Finset V) (w : V → ℤ)
    (hw : ∀ v ∈ s, 0 ≤ w v) {a b : V} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    w a + w b ≤ ∑ v ∈ s, w v := by
  have hsub : ({a, b} : Finset V) ⊆ s := by simp [insert_subset_iff, ha, hb]
  have hsum := sum_le_sum_of_subset_of_nonneg hsub (fun v hv _ ↦ hw v hv)
  rwa [sum_pair hab] at hsum

lemma pairExcess_hub_unit_weights (s : Finset V) (w : V → ℤ) (k : ℤ) (u : V)
    (hu : u ∈ s) (hk : 2 ≤ k) (hwu : w u = k)
    (hw : ∀ v ∈ s.erase u, 0 ≤ w v ∧ w v ≤ 1) :
    pairExcess s w k = ∑ v ∈ s.erase u, w v := by
  have hz : pairExcess (s.erase u) w k = 0 := by
    apply pairExcess_eq_zero_of_pair_le
    intro a ha b hb hab
    have := hw a ha
    have := hw b hb
    omega
  calc
    pairExcess s w k = pairExcess (insert u (s.erase u)) w k := by rw [insert_erase hu]
    _ = _ := by
      rw [pairExcess_insert _ _ _ (notMem_erase _ _), hz, zero_add]
      apply sum_congr rfl
      intro v hv
      rw [hwu]
      have heq : k + w v - k = w v := by ring
      rw [heq, max_eq_left (hw v hv).1]

/-- A unit-weight star plus `h` residual units has at most `k-1` pair
excess at threshold `h+1`, provided a residual unit exists. -/
lemma pairExcess_unit_residual (s : Finset V) (e g : V → ℤ) (k h : ℤ)
    (he : ∀ v ∈ s, 0 ≤ e v ∧ e v ≤ 1) (hg : ∀ v ∈ s, 0 ≤ g v)
    (hes : ∑ v ∈ s, e v = k) (hgs : ∑ v ∈ s, g v = h)
    (hk : 1 ≤ k) (hh : 1 ≤ h) :
    pairExcess s (fun v ↦ e v + g v) (h + 1) ≤ k - 1 := by
  obtain ⟨u, hu, hgu⟩ : ∃ u ∈ s, 0 < g u := by
    by_contra! hn
    have hnon : (∑ v ∈ s, g v) ≤ 0 := sum_nonpos hn
    omega
  have hgerase : (∑ v ∈ s.erase u, g v) = h - g u := by
    have hs := sum_erase_add s g hu
    omega
  have hz : pairExcess (s.erase u) (fun v ↦ e v + g v) (h + 1) = 0 := by
    apply pairExcess_eq_zero_of_pair_le
    intro a ha b hb hab
    have hp := pair_weight_le_total (s.erase u) g (fun v hv ↦ hg v (mem_of_mem_erase hv)) ha hb hab
    rw [hgerase] at hp
    have hea := he a (mem_of_mem_erase ha)
    have heb := he b (mem_of_mem_erase hb)
    omega
  have hsplit : pairExcess s (fun v ↦ e v + g v) (h + 1) =
      ∑ v ∈ s.erase u, max (e u + g u + (e v + g v) - (h + 1)) 0 := by
    calc
      _ = pairExcess (insert u (s.erase u)) (fun v ↦ e v + g v) (h + 1) := by
        rw [insert_erase hu]
      _ = _ := by rw [pairExcess_insert _ _ _ (notMem_erase _ _), hz, zero_add]
  rw [hsplit]
  have heu := he u hu
  by_cases heuz : e u = 0
  · have hzero : (∑ v ∈ s.erase u, max (e u + g u + (e v + g v) - (h + 1)) 0) = 0 := by
      apply sum_eq_zero
      intro v hv
      have hp := pair_weight_le_total s g hg hu (mem_of_mem_erase hv) (ne_of_mem_erase hv).symm
      have hev := he v (mem_of_mem_erase hv)
      rw [hgs] at hp
      exact max_eq_right (by omega)
    rw [hzero]
    omega
  · have heu1 : e u = 1 := by omega
    have hbound : (∑ v ∈ s.erase u, max (e u + g u + (e v + g v) - (h + 1)) 0) ≤
        ∑ v ∈ s.erase u, e v := by
      apply sum_le_sum
      intro v hv
      have hp := pair_weight_le_total s g hg hu (mem_of_mem_erase hv) (ne_of_mem_erase hv).symm
      have hev := he v (mem_of_mem_erase hv)
      rw [hgs] at hp
      exact max_le (by omega) hev.1
    have hsum := sum_erase_add s e hu
    omega

lemma sum_truncated_pred_le (s : Finset V) (w : V → ℤ)
    (hw : ∀ v ∈ s, 0 ≤ w v) (hs : 1 ≤ ∑ v ∈ s, w v) :
    (∑ v ∈ s, max (w v - 1) 0) ≤ (∑ v ∈ s, w v) - 1 := by
  obtain ⟨u, hu, hwu⟩ : ∃ u ∈ s, 0 < w u := by
    by_contra! hn
    have hsum : (∑ v ∈ s, w v) ≤ 0 := sum_nonpos hn
    omega
  have hrest : (∑ v ∈ s.erase u, max (w v - 1) 0) ≤ ∑ v ∈ s.erase u, w v := by
    apply sum_le_sum
    intro v hv
    exact max_le (by omega) (hw v (mem_of_mem_erase hv))
  have hsum := sum_erase_add s (fun v ↦ max (w v - 1) 0) hu
  have htotal := sum_erase_add s w hu
  have heq : max (w u - 1) 0 = w u - 1 := max_eq_left (by omega)
  rw [heq] at hsum
  omega

lemma pairExcess_above_hub_le (s : Finset V) (w : V → ℤ) (k h : ℤ) (u : V)
    (hu : u ∈ s) (hwu : w u = k) (hw : ∀ v ∈ s.erase u, 0 ≤ w v)
    (hs : ∑ v ∈ s.erase u, w v = h) (hh : 1 ≤ h) (hhk : h ≤ k + 1) :
    pairExcess s w (k + 1) ≤ h - 1 := by
  have hz : pairExcess (s.erase u) w (k + 1) = 0 := by
    apply pairExcess_eq_zero_of_pair_le
    intro a ha b hb hab
    have := pair_weight_le_total (s.erase u) w hw ha hb hab
    omega
  have hsplit : pairExcess s w (k + 1) = ∑ v ∈ s.erase u, max (w v - 1) 0 := by
    calc
      _ = pairExcess (insert u (s.erase u)) w (k + 1) := by rw [insert_erase hu]
      _ = _ := by
        rw [pairExcess_insert _ _ _ (notMem_erase _ _), hz, zero_add]
        apply sum_congr rfl
        intro v hv
        rw [hwu]
        congr 1
        ring
  rw [hsplit]
  have hbound := sum_truncated_pred_le (s.erase u) w hw (by omega)
  rwa [hs] at hbound

lemma pairExcess_restrict_of_ne (s t : Finset V) (w : V → ℤ) (k : ℤ)
    (ht : t ⊆ s)
    (h : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → a ∉ t → w a + w b ≤ k) :
    pairExcess s w k = pairExcess t w k := by
  symm
  apply sum_subset (powersetCard_mono ht)
  intro p hp hpt
  obtain ⟨hps, hc⟩ := mem_powersetCard.mp hp
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hc
  have ha : a ∈ s := hps (by simp)
  have hb : b ∈ s := hps (by simp)
  have ht' : ¬ (a ∈ t ∧ b ∈ t) := by
    simpa [mem_powersetCard, insert_subset_iff, singleton_subset_iff, hab] using hpt
  rw [sum_pair hab]
  apply max_eq_right
  by_cases hat : a ∈ t
  · have hbt : b ∉ t := fun hb ↦ ht' ⟨hat, hb⟩
    have := h b hb a ha hab.symm hbt
    omega
  · exact sub_nonpos.mpr (h a ha b hb hab hat)

lemma pairExcess_unit_residual_two_supports (s : Finset V) (e g : V → ℤ) (h : ℤ)
    (he : ∀ v ∈ s, 0 ≤ e v ∧ e v ≤ 1) (hg : ∀ v ∈ s, 0 ≤ g v)
    (hgs : ∑ v ∈ s, g v = h) (u v : V) (hu : u ∈ s) (hv : v ∈ s)
    (huv : u ≠ v) (hgu : 0 < g u) (hgv : 0 < g v) :
    pairExcess s (fun v ↦ e v + g v) (h + 1) ≤ 1 := by
  have havoid : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∀ c ∈ s, c ≠ a → c ≠ b →
      0 < g c → (e a + g a) + (e b + g b) ≤ h + 1 := by
    intro a ha b hb hab c hc hca hcb hgc
    have hp := pair_weight_le_total (s.erase c) g (fun w hw ↦ hg w (mem_of_mem_erase hw))
      (mem_erase.mpr ⟨hca.symm, ha⟩) (mem_erase.mpr ⟨hcb.symm, hb⟩) hab
    have hsum := sum_erase_add s g hc
    have hea := he a ha
    have heb := he b hb
    omega
  have ht : ({u, v} : Finset V) ⊆ s := by simp [insert_subset_iff, hu, hv]
  rw [pairExcess_restrict_of_ne s {u, v} _ (h + 1) ht (by
    intro a ha b hb hab hat
    have hau : a ≠ u := by intro h; exact hat (by simp [h])
    have hav : a ≠ v := by intro h; exact hat (by simp [h])
    by_cases hbu : b = u
    · exact havoid a ha b hb hab v hv hav.symm (by simpa [hbu] using huv.symm) hgv
    · exact havoid a ha b hb hab u hu hau.symm (Ne.symm hbu) hgu)]
  rw [pairExcess_insert {v} _ _ (by simp [huv]),
    pairExcess_eq_zero_of_card_lt {v} _ _ (by simp)]
  simp only [zero_add, sum_singleton]
  have hp := pair_weight_le_total s g hg hu hv huv
  have heu := he u hu
  have hev := he v hv
  exact max_le (by omega) (by omega)

lemma exists_positive_pair_of_ne_zero (s : Finset V) (w : V → ℤ) (k : ℤ)
    (h : pairExcess s w k ≠ 0) : ∃ p ∈ s.powersetCard 2, k < ∑ v ∈ p, w v := by
  by_contra! hn
  apply h
  apply sum_eq_zero
  intro p hp
  exact max_eq_right (sub_nonpos.mpr (hn p hp))

lemma pairExcess_eq_one_of_unique (s : Finset V) (w : V → ℤ) (k : ℤ) (U : Finset V)
    (hU : U ∈ s.powersetCard 2) (hwU : (∑ v ∈ U, w v) = k + 1)
    (hunique : ∀ p ∈ s.powersetCard 2, k < ∑ v ∈ p, w v → p = U) :
    pairExcess s w k = 1 := by
  unfold pairExcess
  rw [sum_eq_single U]
  · rw [hwU]
    omega
  · intro p hp hpU
    have hle : (∑ v ∈ p, w v) ≤ k := by
      by_contra! hpos
      exact hpU (hunique p hp hpos)
    exact max_eq_right (sub_nonpos.mpr hle)
  · exact fun h ↦ (h hU).elim

lemma star_excess_bound_center (s : Finset V) (w : V → ℤ) (x k : ℤ)
    (hx0 : 0 ≤ x) (hx : x ≤ k) (hw : ∀ b ∈ s, 0 ≤ w b ∧ w b ≤ k)
    (hs : x + ∑ b ∈ s, w b ≤ 2 * k) :
    (∑ b ∈ s, max (x + w b - k) 0) ≤ x := by
  let L := s.filter fun b ↦ k < x + w b
  have hL : L ⊆ s := filter_subset _ _
  have hsum : (∑ b ∈ s, max (x + w b - k) 0) = ∑ b ∈ L, (x + w b - k) := by
    calc
      _ = ∑ b ∈ L, max (x + w b - k) 0 := by
        symm
        apply sum_subset hL
        intro b hb hbL
        have : x + w b ≤ k := by simpa [L, hb] using hbL
        exact max_eq_right (by omega)
      _ = _ := sum_congr rfl fun b hb ↦ max_eq_left
        (by have := (mem_filter.mp hb).2; omega)
  rw [hsum]
  by_cases hn : 2 ≤ L.card
  · have hsub : (∑ b ∈ L, w b) ≤ ∑ b ∈ s, w b :=
      sum_le_sum_of_subset_of_nonneg hL fun b hb _ ↦ (hw b hb).1
    have hcalc : (∑ b ∈ L, (x + w b - k)) =
        (∑ b ∈ L, w b) + (L.card : ℤ) * (x - k) := by
      simp_rw [show ∀ b, x + w b - k = w b + (x - k) by intro b; ring]
      simp [sum_add_distrib, mul_comm]
      ring
    rw [hcalc]
    have hn' : (2 : ℤ) ≤ L.card := by exact_mod_cast hn
    have := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hn') (sub_nonpos.mpr hx)
    nlinarith
  · have hn' : (L.card : ℤ) ≤ 1 := by exact_mod_cast (show L.card ≤ 1 by omega)
    calc
      _ ≤ ∑ _b ∈ L, x := sum_le_sum fun b hb ↦ by have := (hw b (hL hb)).2; omega
      _ = (L.card : ℤ) * x := by simp [mul_comm]
      _ ≤ x := by nlinarith

lemma pairExcess_star_le_center (s : Finset V) (w : V → ℤ) (k : ℤ) (u : V)
    (hu : u ∈ s) (hw : ∀ v ∈ s, 0 ≤ w v ∧ w v ≤ k) (hs : ∑ v ∈ s, w v ≤ 2 * k)
    (hstar : ∀ a ∈ s.erase u, ∀ b ∈ s.erase u, a ≠ b → w a + w b ≤ k) :
    pairExcess s w k ≤ w u := by
  have hz := pairExcess_eq_zero_of_pair_le (s.erase u) w k hstar
  have hsum : w u + ∑ v ∈ s.erase u, w v ≤ 2 * k := by
    have := sum_erase_add s w hu
    omega
  have hbound := star_excess_bound_center (s.erase u) w (w u) k (hw u hu).1 (hw u hu).2
    (fun v hv ↦ hw v (mem_of_mem_erase hv)) hsum
  calc
    pairExcess s w k = pairExcess (insert u (s.erase u)) w k := by rw [insert_erase hu]
    _ ≤ w u := by rw [pairExcess_insert _ _ _ (notMem_erase _ _), hz, zero_add]; exact hbound

end Erdos1010
