import ErdosProblems.Erdos538.RainbowChecksum

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538

/-- A finite weighted map has a fiber carrying at least its proportional share
of the total weight. -/
theorem exists_weighted_fiber
    {ι β : Type*} [Fintype β] [Nonempty β] [DecidableEq β]
    (s : Finset ι) (f : ι → β) (w : ι → ℚ≥0) :
    ∃ y : β,
      (∑ x ∈ s with f x = y, w x) ≥
        (∑ x ∈ s, w x) / Fintype.card β := by
  classical
  let total : ℚ≥0 := ∑ x ∈ s, w x
  have hcard : (Fintype.card β : ℚ≥0) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card β ≠ 0)
  have hmul : Fintype.card β • (total / Fintype.card β) ≤ total := by
    rw [nsmul_eq_mul]
    calc
      (Fintype.card β : ℚ≥0) * (total / Fintype.card β)
          = total / Fintype.card β * Fintype.card β := by ac_rfl
      _ = total := div_mul_cancel₀ total hcard
      _ ≤ total := le_rfl
  obtain ⟨y, -, hy⟩ :=
    Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
      (s := s) (t := Finset.univ) (f := f) (w := w)
      (b := total / Fintype.card β)
      (by simp) (Finset.univ_nonempty) (by simpa [total] using hmul)
  exact ⟨y, by simpa [total] using hy⟩

/-- A finite weighted map also has a fiber carrying at most its proportional
share of the total weight. -/
theorem exists_weighted_fiber_small
    {ι β : Type*} [Fintype β] [Nonempty β] [DecidableEq β]
    (s : Finset ι) (f : ι → β) (w : ι → ℚ≥0) :
    ∃ y : β,
      (∑ x ∈ s with f x = y, w x) ≤
        (∑ x ∈ s, w x) / Fintype.card β := by
  classical
  let total : ℚ≥0 := ∑ x ∈ s, w x
  have hcard : (Fintype.card β : ℚ≥0) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card β ≠ 0)
  have hmul : total ≤ Fintype.card β • (total / Fintype.card β) := by
    rw [nsmul_eq_mul]
    calc
      total ≤ total := le_rfl
      _ = total / Fintype.card β * Fintype.card β :=
        (div_mul_cancel₀ total hcard).symm
      _ = (Fintype.card β : ℚ≥0) * (total / Fintype.card β) := by ac_rfl
  obtain ⟨y, -, hy⟩ :=
    Finset.exists_sum_fiber_le_of_maps_to_of_sum_le_nsmul
      (s := s) (t := Finset.univ) (f := f) (w := w)
      (b := total / Fintype.card β)
      (by simp) (Finset.univ_nonempty) (by simpa [total] using hmul)
  exact ⟨y, by simpa [total] using hy⟩

/-- Weight of monochromatic pairs `j < i < n`. -/
noncomputable def monochromaticPairWeight (n : ℕ) (c : ℕ → Fin q)
    (W : ℕ → ℕ → ℚ≥0) : ℚ≥0 := by
  classical
  exact ∑ i ∈ Finset.range n,
    ∑ j ∈ Finset.range i with c j = c i, W j i

/-- Total weight of all pairs `j < i < n`. -/
noncomputable def totalPairWeight (n : ℕ) (W : ℕ → ℕ → ℚ≥0) : ℚ≥0 :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, W j i

/-- Weighted max-cut averaging: `n` vertices possess a `q`-coloring for which
at most a `1/q` share of the total pair weight is monochromatic. -/
theorem exists_pair_collision_coloring (n q : ℕ) (hq : 0 < q)
    (W : ℕ → ℕ → ℚ≥0) :
    ∃ c : ℕ → Fin q,
      q • monochromaticPairWeight n c W ≤ totalPairWeight n W := by
  induction n with
  | zero =>
      let c : ℕ → Fin q := fun _ => ⟨0, hq⟩
      exact ⟨c, by simp [monochromaticPairWeight, totalPairWeight]⟩
  | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
      let total : ℚ≥0 := ∑ j ∈ Finset.range n, W j n
      obtain ⟨z, hz⟩ := exists_weighted_fiber_small
        (Finset.range n) c (fun j => W j n)
      have hqcard : Fintype.card (Fin q) = q := Fintype.card_fin q
      have hq0 : (q : ℚ≥0) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
      have hzbase : (∑ j ∈ Finset.range n with c j = z, W j n) ≤ total / q := by
        simpa [total, hqcard] using hz
      have hz' : q • (∑ j ∈ Finset.range n with c j = z, W j n) ≤ total := by
        rw [nsmul_eq_mul]
        calc
          (q : ℚ≥0) * (∑ j ∈ Finset.range n with c j = z, W j n)
              ≤ q * (total / q) := mul_le_mul_right hzbase (q : ℚ≥0)
          _ = total := by
            rw [mul_comm, div_mul_cancel₀ total hq0]
      let c' : ℕ → Fin q := Function.update c n z
      have hc'lt (i : ℕ) (hi : i < n) : c' i = c i := by
        simp [c', Function.update_apply, Nat.ne_of_lt hi]
      have hc'n : c' n = z := by simp [c', Function.update_apply]
      have hold :
          (∑ i ∈ Finset.range n,
            ∑ j ∈ Finset.range i with c' j = c' i, W j i) =
          ∑ i ∈ Finset.range n,
            ∑ j ∈ Finset.range i with c j = c i, W j i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hin : i < n := Finset.mem_range.mp hi
        rw [Finset.sum_filter, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hc'lt i hin, hc'lt j (lt_trans (Finset.mem_range.mp hj) hin)]
      have hnew :
          (∑ j ∈ Finset.range n with c' j = c' n, W j n) =
          ∑ j ∈ Finset.range n with c j = z, W j n := by
        rw [hc'n, Finset.sum_filter, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hc'lt j (Finset.mem_range.mp hj)]
      have hmono : monochromaticPairWeight (n + 1) c' W =
          monochromaticPairWeight n c W +
            ∑ j ∈ Finset.range n with c j = z, W j n := by
        simp only [monochromaticPairWeight, Finset.sum_range_succ]
        rw [hold, hnew]
      have htotal : totalPairWeight (n + 1) W =
          totalPairWeight n W + total := by
        simp [totalPairWeight, total, Finset.sum_range_succ]
      refine ⟨c', ?_⟩
      rw [hmono, htotal, nsmul_add]
      exact add_le_add hc hz'

/-- Total weight of the supports in `supports` satisfying `P`. -/
noncomputable def weightedSupportMass {α : Type*}
    (supports : Finset (Finset α)) (P : Finset α → Prop)
    (w : Finset α → ℚ≥0) : ℚ≥0 := by
  classical
  exact ∑ s ∈ supports with P s, w s

/-- Weight of supports containing a prescribed pair of labels. -/
noncomputable def pairSupportWeight {α : Type*} [DecidableEq α]
    (supports : Finset (Finset α)) (w : Finset α → ℚ≥0) (a b : α) : ℚ≥0 := by
  classical
  exact ∑ s ∈ supports with a ∈ s ∧ b ∈ s, w s

/-- Number, viewed as a nonnegative rational, of label pairs `j < i < n`
contained in a support. -/
noncomputable def supportPairFactor (n : ℕ) (s : Finset ℕ) : ℚ≥0 := by
  classical
  exact ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i,
    if j ∈ s ∧ i ∈ s then 1 else 0

/-- Number, viewed as a nonnegative rational, of monochromatic label pairs
`j < i < n` contained in a support. -/
noncomputable def supportMonoFactor (n : ℕ) (c : ℕ → Fin q)
    (s : Finset ℕ) : ℚ≥0 := by
  classical
  exact ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i,
    if j ∈ s ∧ i ∈ s ∧ c j = c i then 1 else 0

/-- Double-counting all weighted support-pair incidences. -/
theorem totalPairWeight_pairSupportWeight
    (n : ℕ) (supports : Finset (Finset ℕ)) (w : Finset ℕ → ℚ≥0) :
    totalPairWeight n (pairSupportWeight supports w) =
      ∑ s ∈ supports, w s * supportPairFactor n s := by
  classical
  simp only [totalPairWeight, pairSupportWeight,
    supportPairFactor, Finset.sum_filter]
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ i ∈ Finset.range n, ∑ s ∈ supports,
          ∑ j ∈ Finset.range i, if j ∈ s ∧ i ∈ s then w s else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
    _ = ∑ s ∈ supports, ∑ i ∈ Finset.range n,
          ∑ j ∈ Finset.range i, if j ∈ s ∧ i ∈ s then w s else 0 := by
        rw [Finset.sum_comm]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hmem : j ∈ s ∧ i ∈ s <;> simp [hmem]

/-- Double-counting the monochromatic weighted support-pair incidences. -/
theorem monochromaticPairWeight_pairSupportWeight
    (n q : ℕ) (c : ℕ → Fin q)
    (supports : Finset (Finset ℕ)) (w : Finset ℕ → ℚ≥0) :
    monochromaticPairWeight n c (pairSupportWeight supports w) =
      ∑ s ∈ supports, w s * supportMonoFactor n c s := by
  classical
  simp only [monochromaticPairWeight, pairSupportWeight,
    supportMonoFactor, Finset.sum_filter]
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, ∑ s ∈ supports,
          if j ∈ s ∧ i ∈ s ∧ c j = c i then w s else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hcolor : c j = c i
        · simp [hcolor, and_assoc]
        · simp [hcolor]
    _ = ∑ i ∈ Finset.range n, ∑ s ∈ supports, ∑ j ∈ Finset.range i,
          if j ∈ s ∧ i ∈ s ∧ c j = c i then w s else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
    _ = ∑ s ∈ supports, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i,
          if j ∈ s ∧ i ∈ s ∧ c j = c i then w s else 0 := by
        rw [Finset.sum_comm]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hmem : j ∈ s ∧ i ∈ s ∧ c j = c i <;> simp [hmem]

/-- One colliding pair already contributes one to the monochromatic-pair
factor. -/
theorem one_le_supportMonoFactor_of_collision
    {n q i j : ℕ} (c : ℕ → Fin q) (s : Finset ℕ)
    (hi : i < n) (hj : j < i) (hjs : j ∈ s) (his : i ∈ s)
    (hcolor : c j = c i) :
    1 ≤ supportMonoFactor n c s := by
  classical
  unfold supportMonoFactor
  calc
    (1 : ℚ≥0) = if j ∈ s ∧ i ∈ s ∧ c j = c i then 1 else 0 := by
      simp [hjs, his, hcolor]
    _ ≤ ∑ x ∈ Finset.range i,
          if x ∈ s ∧ i ∈ s ∧ c x = c i then 1 else 0 := by
      exact Finset.single_le_sum_of_canonicallyOrdered
        (f := fun x => if x ∈ s ∧ i ∈ s ∧ c x = c i then (1 : ℚ≥0) else 0)
        (s := Finset.range i) (i := j) (Finset.mem_range.mpr hj)
    _ ≤ ∑ y ∈ Finset.range n, ∑ x ∈ Finset.range y,
          if x ∈ s ∧ y ∈ s ∧ c x = c y then 1 else 0 := by
      exact Finset.single_le_sum_of_canonicallyOrdered
        (f := fun y => ∑ x ∈ Finset.range y,
          if x ∈ s ∧ y ∈ s ∧ c x = c y then (1 : ℚ≥0) else 0)
        (s := Finset.range n) (i := i) (Finset.mem_range.mpr hi)

/-- A non-rainbow support contained in `[0,n)` has at least one
monochromatic pair in the preceding count. -/
theorem one_le_supportMonoFactor_of_not_nodup
    {n q : ℕ} (c : ℕ → Fin q) (s : Finset ℕ)
    (hsub : s ⊆ Finset.range n) (hdup : ¬(s.1.map c).Nodup) :
    1 ≤ supportMonoFactor n c s := by
  classical
  have hnotinj : ¬Set.InjOn c s := by
    rwa [← Finset.nodup_map_iff_injOn]
  simp only [Set.InjOn] at hnotinj
  push_neg at hnotinj
  obtain ⟨a, ha, b, hb, heq, hab⟩ := hnotinj
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · exact one_le_supportMonoFactor_of_collision c s
      (Finset.mem_range.mp (hsub hb)) hablt ha hb heq
  · exact one_le_supportMonoFactor_of_collision c s
      (Finset.mem_range.mp (hsub ha)) hbalt hb ha heq.symm

/-- The total weight of non-rainbow supports is bounded by their weighted
number of monochromatic pairs. -/
theorem nonRainbowMass_le_weighted_monoFactor
    {n q : ℕ} (c : ℕ → Fin q) (supports : Finset (Finset ℕ))
    (w : Finset ℕ → ℚ≥0)
    (hsub : ∀ s ∈ supports, s ⊆ Finset.range n) :
    weightedSupportMass supports (fun s => ¬(s.1.map c).Nodup) w ≤
      ∑ s ∈ supports, w s * supportMonoFactor n c s := by
  classical
  unfold weightedSupportMass
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro s hs
  by_cases hdup : ¬(s.1.map c).Nodup
  · rw [if_pos hdup]
    calc
      w s = w s * 1 := by simp
      _ ≤ w s * supportMonoFactor n c s :=
        mul_le_mul_right (one_le_supportMonoFactor_of_not_nodup c s
          (hsub s hs) hdup) (w s)
  · rw [if_neg hdup]
    exact bot_le

/-- Pair-collision coloring plus the preceding union bound: some `q`-coloring
makes the non-rainbow support weight at most the total weighted pair incidence
divided by `q`. -/
theorem exists_coloring_nonRainbow_pair_bound
    (n q : ℕ) (hq : 0 < q) (supports : Finset (Finset ℕ))
    (w : Finset ℕ → ℚ≥0)
    (hsub : ∀ s ∈ supports, s ⊆ Finset.range n) :
    ∃ c : ℕ → Fin q,
      q • weightedSupportMass supports (fun s => ¬(s.1.map c).Nodup) w ≤
        ∑ s ∈ supports, w s * supportPairFactor n s := by
  obtain ⟨c, hc⟩ := exists_pair_collision_coloring n q hq
    (pairSupportWeight supports w)
  have hmono := nonRainbowMass_le_weighted_monoFactor c supports w hsub
  rw [monochromaticPairWeight_pairSupportWeight] at hc
  rw [totalPairWeight_pairSupportWeight] at hc
  exact ⟨c, (nsmul_le_nsmul_right hmono q).trans hc⟩

/-- A sum of membership indicators over any finite test set is at most the
cardinality of the target support. -/
theorem sum_indicator_mem_le_card (t s : Finset ℕ) :
    (∑ x ∈ t, if x ∈ s then (1 : ℚ≥0) else 0) ≤ s.card := by
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast Finset.card_le_card (by
    intro x hx
    exact (Finset.mem_filter.mp hx).2 : t.filter (fun x => x ∈ s) ⊆ s)

/-- The number of ordered-by-label pairs in a support is at most the square of
its cardinality.  This deliberately uses the crude `k²` bound, which suffices
for the rainbow-coloring baseline. -/
theorem supportPairFactor_le_card_sq (n : ℕ) (s : Finset ℕ) :
    supportPairFactor n s ≤ (s.card : ℚ≥0) * s.card := by
  classical
  unfold supportPairFactor
  calc
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i,
        if j ∈ s ∧ i ∈ s then (1 : ℚ≥0) else 0) =
      ∑ i ∈ Finset.range n, if i ∈ s then
        (∑ j ∈ Finset.range i, if j ∈ s then (1 : ℚ≥0) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases his : i ∈ s <;> simp [his]
    _ ≤ ∑ i ∈ Finset.range n,
        if i ∈ s then (s.card : ℚ≥0) else 0 := by
          apply Finset.sum_le_sum
          intro i hi
          by_cases his : i ∈ s
          · simp only [his, ↓reduceIte]
            exact sum_indicator_mem_le_card (Finset.range i) s
          · simp [his]
    _ = (s.card : ℚ≥0) *
        (∑ i ∈ Finset.range n, if i ∈ s then (1 : ℚ≥0) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          by_cases his : i ∈ s <;> simp [his]
    _ ≤ (s.card : ℚ≥0) * s.card :=
      mul_le_mul_right (sum_indicator_mem_le_card (Finset.range n) s)
        (s.card : ℚ≥0)

/-- On an exact-cardinality layer, total weighted pair incidence is at most
`k²` times the layer weight. -/
theorem weighted_pairFactor_le_card_sq_mass
    (n k : ℕ) (supports : Finset (Finset ℕ)) (w : Finset ℕ → ℚ≥0)
    (hcard : ∀ s ∈ supports, s.card = k) :
    (∑ s ∈ supports, w s * supportPairFactor n s) ≤
      (k : ℚ≥0) * k * ∑ s ∈ supports, w s := by
  calc
    (∑ s ∈ supports, w s * supportPairFactor n s) ≤
        ∑ s ∈ supports, w s * ((s.card : ℚ≥0) * s.card) := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_right (supportPairFactor_le_card_sq n s) (w s)
    _ = ∑ s ∈ supports, w s * ((k : ℚ≥0) * k) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hcard s hs]
    _ = (k : ℚ≥0) * k * ∑ s ∈ supports, w s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ac_rfl

/-- Rainbow and non-rainbow supports partition every weighted support family. -/
theorem rainbowMass_add_nonRainbowMass
    {q : ℕ} (c : ℕ → Fin q) (supports : Finset (Finset ℕ))
    (w : Finset ℕ → ℚ≥0) :
    weightedSupportMass supports (fun s => (s.1.map c).Nodup) w +
      weightedSupportMass supports (fun s => ¬(s.1.map c).Nodup) w =
        ∑ s ∈ supports, w s := by
  classical
  unfold weightedSupportMass
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : (s.1.map c).Nodup <;> simp [h]

/-- For an arbitrary nonnegative weighting of exact-`k` supports in `[0,n)`,
there is a coloring into `2k²` colors for which at least half of the weight is
rainbow. -/
theorem exists_coloring_half_rainbow
    (n k : ℕ) (hk : 0 < k) (supports : Finset (Finset ℕ))
    (w : Finset ℕ → ℚ≥0)
    (hsub : ∀ s ∈ supports, s ⊆ Finset.range n)
    (hcard : ∀ s ∈ supports, s.card = k) :
    ∃ c : ℕ → Fin (2 * k * k),
      (∑ s ∈ supports, w s) ≤
        2 • weightedSupportMass supports (fun s => (s.1.map c).Nodup) w := by
  have hq : 0 < 2 * k * k := by positivity
  obtain ⟨c, hc⟩ := exists_coloring_nonRainbow_pair_bound
    n (2 * k * k) hq supports w hsub
  have hpair := weighted_pairFactor_le_card_sq_mass n k supports w hcard
  have hbad : (2 * k * k) •
      weightedSupportMass supports (fun s => ¬(s.1.map c).Nodup) w ≤
      (k : ℚ≥0) * k * ∑ s ∈ supports, w s := hc.trans hpair
  have hkcast : (0 : ℚ≥0) < (k : ℚ≥0) * k := by positivity
  have hbad' : 2 • weightedSupportMass supports
      (fun s => ¬(s.1.map c).Nodup) w ≤ ∑ s ∈ supports, w s := by
    simp only [nsmul_eq_mul] at hbad ⊢
    have hfactor : ((2 * k * k : ℕ) : ℚ≥0) = 2 * ((k : ℚ≥0) * k) := by
      norm_num
      ring
    rw [hfactor] at hbad
    apply (mul_le_mul_iff_of_pos_left hkcast).mp
    convert hbad using 1 <;> ring
  refine ⟨c, ?_⟩
  let good := weightedSupportMass supports
    (fun s => (s.1.map c).Nodup) w
  let bad := weightedSupportMass supports
    (fun s => ¬(s.1.map c).Nodup) w
  have hpartition : good + bad = ∑ s ∈ supports, w s := by
    exact rainbowMass_add_nonRainbowMass c supports w
  have hbadNorm : bad + bad ≤ good + bad := by
    rw [hpartition]
    simpa [bad, two_mul] using hbad'
  have hbadGood : bad ≤ good := by
    exact (add_le_add_iff_right bad).mp (by simpa [add_comm] using hbadNorm)
  rw [nsmul_eq_mul]
  calc
    (∑ s ∈ supports, w s) = good + bad := hpartition.symm
    _ ≤ good + good := add_le_add_right hbadGood good
    _ = (2 : ℚ≥0) * good := by ring

/-- A support is rainbow under `color` and lies in the exact cardinality
layer `k`. -/
def RainbowSupport {α G : Type*} [DecidableEq G]
    (k : ℕ) (color : α → G) (s : Finset α) : Prop :=
  (s.1.map color).Nodup ∧ s.card = k

/-- The additive checksum of the colors on a finite support. -/
def supportChecksum {α G : Type*} [AddCommMonoid G]
    (color : α → G) (s : Finset α) : G :=
  (s.1.map color).sum

/-- For every fixed coloring, some checksum residue retains at least a
`1 / |G|` share of the total weight of the rainbow exact-`k` supports.  The
corresponding one-residue pattern family simultaneously obeys cap two. -/
theorem exists_weighted_rainbowChecksum
    {α G : Type*} [DecidableEq α] [DecidableEq G] [Fintype G]
    [AddCommGroup G]
    (k : ℕ) (supports : Finset (Finset α)) (color : α → G)
    (w : Finset α → ℚ≥0) :
    ∃ z : G,
      PatternCap 2 (RainbowChecksum k {z}) ∧
      weightedSupportMass supports
          (fun s => RainbowChecksum k {z} (s.1.map color)) w ≥
        weightedSupportMass supports (RainbowSupport k color) w /
          Fintype.card G := by
  classical
  let good := supports.filter (RainbowSupport k color)
  obtain ⟨z, hz⟩ := exists_weighted_fiber good
    (supportChecksum color) w
  refine ⟨z, rainbowChecksum_patternCap_two k {z} (by simp), ?_⟩
  rw [Finset.filter_filter] at hz
  simpa [weightedSupportMass, good, RainbowSupport, supportChecksum,
    RainbowChecksum, and_assoc] using hz

/-- Combining half-rainbow coloring with checksum-residue averaging gives a
single cap-two checksum class carrying at least a `1/(4k²)` share of every
weighted exact-`k` support layer. -/
theorem exists_weighted_checksum_quarter_sq
    (n k : ℕ) (hk : 0 < k) (supports : Finset (Finset ℕ))
    (w : Finset ℕ → ℚ≥0)
    (hsub : ∀ s ∈ supports, s ⊆ Finset.range n)
    (hcard : ∀ s ∈ supports, s.card = k) :
    ∃ (color : ℕ → ZMod (2 * k * k)) (z : ZMod (2 * k * k)),
      PatternCap 2 (RainbowChecksum k {z}) ∧
      (∑ s ∈ supports, w s) ≤
        (4 * k * k) • weightedSupportMass supports
          (fun s => RainbowChecksum k {z} (s.1.map color)) w := by
  classical
  let q := 2 * k * k
  have hq : 0 < q := by simp [q, hk]
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  obtain ⟨c, hc⟩ := exists_coloring_half_rainbow n k hk supports w hsub hcard
  let color : ℕ → ZMod q := fun x => ZMod.finEquiv q (c x)
  have hnodup (s : Finset ℕ) :
      (s.1.map color).Nodup ↔ (s.1.map c).Nodup := by
    change (s.1.map ((ZMod.finEquiv q) ∘ c)).Nodup ↔ (s.1.map c).Nodup
    rw [← Multiset.map_map]
    exact Multiset.nodup_map_iff_of_injective (ZMod.finEquiv q).injective
  have hrainbow :
      weightedSupportMass supports (RainbowSupport k color) w =
        weightedSupportMass supports (fun s => (s.1.map c).Nodup) w := by
    unfold weightedSupportMass
    congr 1
    ext s
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hs, hr⟩
      exact ⟨hs, (hnodup s).mp hr.1⟩
    · rintro ⟨hs, hr⟩
      exact ⟨hs, (hnodup s).mpr hr, hcard s hs⟩
  obtain ⟨z, hcap, hz⟩ :=
    exists_weighted_rainbowChecksum k supports color w
  have hqcard : Fintype.card (ZMod q) = q := ZMod.card q
  rw [hrainbow, hqcard] at hz
  have hqcast : (0 : ℚ≥0) < (q : ℚ≥0) := by exact_mod_cast hq
  let selected := weightedSupportMass supports
    (fun s => RainbowChecksum k {z} (s.1.map color)) w
  have hzmul : weightedSupportMass supports
      (fun s => (s.1.map c).Nodup) w ≤ q • selected := by
    simp only [nsmul_eq_mul]
    exact (div_le_iff₀' hqcast).mp (by simpa [selected] using hz)
  refine ⟨color, z, hcap, ?_⟩
  calc
    (∑ s ∈ supports, w s) ≤
        2 • weightedSupportMass supports (fun s => (s.1.map c).Nodup) w := hc
    _ ≤ 2 • (q • selected) := nsmul_le_nsmul_right hzmul 2
    _ = (4 * k * k) • selected := by simp [q, nsmul_eq_mul]; ring

end Erdos538
