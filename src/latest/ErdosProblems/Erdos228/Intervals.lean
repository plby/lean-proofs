import Mathlib

/-!
# Finite grid intervals for Erdős Problem 228

This file isolates the finite, one-dimensional bookkeeping used when the
Rudin--Shapiro cosine sum is small.  There are three independent pieces:

* equally spaced grids and blocks of consecutive indices;
* maximal runs of indices satisfying a decidable predicate, together with the
  elementary bound "runs ≤ changes + 1";
* reflection operations on intervals and a generic way to bound the number of
  runs by the number of level-crossing witnesses.

The analytic construction can instantiate `bad i` with a strict sublevel-set
condition at the `i`-th grid point.  Continuity then supplies a level point in
each cell at which the truth value changes.
-/

namespace Erdos228.Intervals

open Set

/-! ## Equally spaced grids -/

/-- The `k`-th point of the grid of mesh `π / n`. -/
noncomputable def gridPoint (n k : ℕ) : ℝ := (k : ℝ) * Real.pi / n

/-- The closed cell between two consecutive grid points. -/
noncomputable def gridCell (n k : ℕ) : Set ℝ :=
  Icc (gridPoint n k) (gridPoint n (k + 1))

/-- A block of `length` consecutive integer grid indices. -/
def indexBlock (start length : ℕ) : Finset ℕ :=
  (Finset.range length).image (start + ·)

@[simp] theorem mem_indexBlock {start length i : ℕ} :
    i ∈ indexBlock start length ↔ start ≤ i ∧ i < start + length := by
  constructor
  · simp only [indexBlock, Finset.mem_image, Finset.mem_range]
    rintro ⟨j, hj, rfl⟩
    omega
  · rintro ⟨hsi, hi⟩
    simp only [indexBlock, Finset.mem_image, Finset.mem_range]
    exact ⟨i - start, by omega, by omega⟩

@[simp] theorem card_indexBlock (start length : ℕ) :
    (indexBlock start length).card = length := by
  rw [indexBlock, Finset.card_image_of_injective]
  · simp
  · exact fun _ _ h ↦ Nat.add_left_cancel h

theorem gridPoint_zero (n : ℕ) : gridPoint n 0 = 0 := by
  simp [gridPoint]

theorem gridPoint_add (n k l : ℕ) :
    gridPoint n (k + l) = gridPoint n k + gridPoint n l := by
  simp only [gridPoint, Nat.cast_add]
  ring

theorem gridPoint_succ (n k : ℕ) :
    gridPoint n (k + 1) = gridPoint n k + Real.pi / n := by
  rw [gridPoint_add]
  simp [gridPoint]

theorem gridPoint_strictMono {n : ℕ} (hn : 0 < n) :
    StrictMono (gridPoint n) := by
  intro i j hij
  simp only [gridPoint]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hn'
  simpa [mul_div_assoc] using (mul_lt_mul_of_pos_right (by exact_mod_cast hij) hpi)

theorem gridPoint_mono {n : ℕ} (hn : 0 < n) :
    Monotone (gridPoint n) := (gridPoint_strictMono hn).monotone

theorem gridPoint_n {n : ℕ} (hn : 0 < n) : gridPoint n n = Real.pi := by
  simp only [gridPoint]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hn']

theorem gridPoint_sub {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    gridPoint n (n - k) = Real.pi - gridPoint n k := by
  simp only [gridPoint, Nat.cast_sub hk]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hn']

theorem gridCell_width {n k : ℕ} (_hn : 0 < n) :
    gridPoint n (k + 1) - gridPoint n k = Real.pi / n := by
  rw [gridPoint_succ]
  ring

/-! ## Reflection bookkeeping -/

/-- Reflect an oriented interval through the origin. -/
def negInterval (I : ℝ × ℝ) : ℝ × ℝ := (-I.2, -I.1)

/-- Reflect an oriented interval through `π / 2`, i.e. by `θ ↦ π - θ`. -/
noncomputable def piMinusInterval (I : ℝ × ℝ) : ℝ × ℝ :=
  (Real.pi - I.2, Real.pi - I.1)

/-- Translate an oriented interval by `π`, i.e. by `θ ↦ π + θ`. -/
noncomputable def piPlusInterval (I : ℝ × ℝ) : ℝ × ℝ :=
  (Real.pi + I.1, Real.pi + I.2)

theorem negInterval_involutive : Function.Involutive negInterval := by
  intro I
  rcases I with ⟨a, b⟩
  simp [negInterval]

theorem piMinusInterval_involutive : Function.Involutive piMinusInterval := by
  intro I
  rcases I with ⟨a, b⟩
  simp [piMinusInterval]

theorem negInterval_injective : Function.Injective negInterval :=
  negInterval_involutive.injective

theorem piMinusInterval_injective : Function.Injective piMinusInterval :=
  piMinusInterval_involutive.injective

@[simp] theorem mem_Icc_negInterval {a b x : ℝ} :
    x ∈ Icc a b ↔ -x ∈ Icc (negInterval (a, b)).1 (negInterval (a, b)).2 := by
  change (a ≤ x ∧ x ≤ b) ↔ (-b ≤ -x ∧ -x ≤ -a)
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

@[simp] theorem mem_Icc_piMinusInterval {a b x : ℝ} :
    x ∈ Icc a b ↔
      Real.pi - x ∈ Icc (piMinusInterval (a, b)).1 (piMinusInterval (a, b)).2 := by
  change (a ≤ x ∧ x ≤ b) ↔
    (Real.pi - b ≤ Real.pi - x ∧ Real.pi - x ≤ Real.pi - a)
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

@[simp] theorem mem_Icc_piPlusInterval {a b x : ℝ} :
    x ∈ Icc a b ↔
      Real.pi + x ∈ Icc (piPlusInterval (a, b)).1 (piPlusInterval (a, b)).2 := by
  simp [piPlusInterval]

theorem card_image_negInterval (s : Finset (ℝ × ℝ)) :
    (s.image negInterval).card = s.card :=
  Finset.card_image_of_injective s negInterval_injective

theorem card_image_piMinusInterval (s : Finset (ℝ × ℝ)) :
    (s.image piMinusInterval).card = s.card :=
  Finset.card_image_of_injective s piMinusInterval_injective

/-! ## Changes and maximal bad runs -/

/-- Indices at which a predicate changes between `i` and `i+1`.  The first
condition keeps both endpoints in `{0, ..., N-1}`. -/
def changeIndices (N : ℕ) (bad : ℕ → Prop) [DecidablePred bad] : Finset ℕ :=
  (Finset.range N).filter fun i ↦ i + 1 < N ∧ ¬ (bad i ↔ bad (i + 1))

/-- Left endpoints of the maximal consecutive runs on which `bad` holds. -/
def runStarts (N : ℕ) (bad : ℕ → Prop) [DecidablePred bad] : Finset ℕ :=
  (Finset.range N).filter fun i ↦ bad i ∧ (i = 0 ∨ ¬ bad (i - 1))

@[simp] theorem mem_changeIndices {N i : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad] :
    i ∈ changeIndices N bad ↔ i + 1 < N ∧ ¬ (bad i ↔ bad (i + 1)) := by
  simp [changeIndices]
  omega

@[simp] theorem mem_runStarts {N i : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad] :
    i ∈ runStarts N bad ↔
      i < N ∧ bad i ∧ (i = 0 ∨ ¬ bad (i - 1)) := by
  simp [runStarts]

/-- Every nonzero run start is the successor of a change index. -/
theorem runStarts_subset_insert_image (N : ℕ) (bad : ℕ → Prop)
    [DecidablePred bad] :
    runStarts N bad ⊆ insert 0 ((changeIndices N bad).image Nat.succ) := by
  intro i hi
  rw [mem_runStarts] at hi
  by_cases hi0 : i = 0
  · simp [hi0]
  · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
    have hpred : ¬ bad (i - 1) := hi.2.2.resolve_left hi0
    have hsucc : (i - 1) + 1 = i := by omega
    simp only [Finset.mem_insert, Finset.mem_image]
    right
    refine ⟨i - 1, ?_, ?_⟩
    · rw [mem_changeIndices, hsucc]
      refine ⟨hi.1, ?_⟩
      tauto
    · omega

/-- A binary word has at most one more run of `true` values than it has
adjacent changes. -/
theorem card_runStarts_le_card_changeIndices_add_one
    (N : ℕ) (bad : ℕ → Prop) [DecidablePred bad] :
    (runStarts N bad).card ≤ (changeIndices N bad).card + 1 := by
  calc
    (runStarts N bad).card ≤
        (insert 0 ((changeIndices N bad).image Nat.succ)).card :=
      Finset.card_le_card (runStarts_subset_insert_image N bad)
    _ ≤ ((changeIndices N bad).image Nat.succ).card + 1 :=
      Finset.card_insert_le _ _
    _ = (changeIndices N bad).card + 1 := by
      rw [Finset.card_image_of_injective _ Nat.succ_injective]

/-- The interval `[a,b]` is one maximal run of `bad` in `{0, ..., N-1}`. -/
def IsMaximalBadRun (N : ℕ) (bad : ℕ → Prop) (a b : ℕ) : Prop :=
  a ≤ b ∧ b < N ∧
    (∀ i ∈ Finset.range N, a ≤ i → i ≤ b → bad i) ∧
    (a = 0 ∨ ¬ bad (a - 1)) ∧
    (b + 1 = N ∨ ¬ bad (b + 1))

instance instDecidableIsMaximalBadRun (N : ℕ) (bad : ℕ → Prop)
    [DecidablePred bad] (a b : ℕ) : Decidable (IsMaximalBadRun N bad a b) := by
  unfold IsMaximalBadRun
  infer_instance

/-- The finite set of all maximal bad runs, encoded by their endpoints. -/
def maximalBadRuns (N : ℕ) (bad : ℕ → Prop) [DecidablePred bad] :
    Finset (ℕ × ℕ) :=
  ((Finset.range N).product (Finset.range N)).filter fun I ↦
    IsMaximalBadRun N bad I.1 I.2

theorem isMaximalBadRun_start {N a b : ℕ} {bad : ℕ → Prop}
    (h : IsMaximalBadRun N bad a b) : bad a ∧ (a = 0 ∨ ¬ bad (a - 1)) := by
  exact ⟨h.2.2.1 a (Finset.mem_range.2 (h.1.trans_lt h.2.1)) le_rfl h.1,
    h.2.2.2.1⟩

theorem isMaximalBadRun_start_mem {N a b : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad] (h : IsMaximalBadRun N bad a b) :
    a ∈ runStarts N bad := by
  rw [mem_runStarts]
  exact ⟨h.1.trans_lt h.2.1, isMaximalBadRun_start h⟩

/-- Two maximal bad runs with the same left endpoint are equal. -/
theorem IsMaximalBadRun.eq_of_start_eq {N a b c d : ℕ} {bad : ℕ → Prop}
    (h₁ : IsMaximalBadRun N bad a b) (h₂ : IsMaximalBadRun N bad c d)
    (hac : a = c) : (a, b) = (c, d) := by
  subst c
  congr 1
  apply le_antisymm
  · by_contra hnot
    have hdb : d < b := Nat.lt_of_not_ge hnot
    have hbad : bad (d + 1) :=
      h₁.2.2.1 (d + 1) (Finset.mem_range.2 (lt_of_le_of_lt hdb h₁.2.1))
        (Nat.le_succ_of_le h₂.1) hdb
    rcases h₂.2.2.2.2 with heq | hnbad
    · have hNb : N ≤ b := by omega
      exact (Nat.not_le_of_gt h₁.2.1) hNb
    · exact hnbad hbad
  · by_contra hnot
    have hbd : b < d := Nat.lt_of_not_ge hnot
    have hbad : bad (b + 1) :=
      h₂.2.2.1 (b + 1) (Finset.mem_range.2 (lt_of_le_of_lt hbd h₂.2.1))
        (Nat.le_succ_of_le h₁.1) hbd
    rcases h₁.2.2.2.2 with heq | hnbad
    · have hNd : N ≤ d := by omega
      exact (Nat.not_le_of_gt h₂.2.1) hNd
    · exact hnbad hbad

@[simp] theorem mem_maximalBadRuns {N a b : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad] :
    (a, b) ∈ maximalBadRuns N bad ↔ IsMaximalBadRun N bad a b := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (h.1.trans_lt h.2.1), Finset.mem_range.mpr h.2.1⟩, h⟩

/-- Counting maximal runs is the same as counting a subset of their distinct
left endpoints. -/
theorem card_maximalBadRuns_le_card_runStarts
    (N : ℕ) (bad : ℕ → Prop) [DecidablePred bad] :
    (maximalBadRuns N bad).card ≤ (runStarts N bad).card := by
  classical
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro I hI
    rcases I with ⟨a, b⟩
    change (a, b) ∈ maximalBadRuns N bad at hI
    rw [mem_maximalBadRuns] at hI
    exact isMaximalBadRun_start_mem hI
  · intro I hI J hJ hfst
    rcases I with ⟨a, b⟩
    rcases J with ⟨c, d⟩
    change (a, b) ∈ maximalBadRuns N bad at hI
    change (c, d) ∈ maximalBadRuns N bad at hJ
    rw [mem_maximalBadRuns] at hI hJ
    exact IsMaximalBadRun.eq_of_start_eq hI hJ hfst

theorem card_maximalBadRuns_le_card_changeIndices_add_one
    (N : ℕ) (bad : ℕ → Prop) [DecidablePred bad] :
    (maximalBadRuns N bad).card ≤ (changeIndices N bad).card + 1 :=
  (card_maximalBadRuns_le_card_runStarts N bad).trans
    (card_runStarts_le_card_changeIndices_add_one N bad)

/-- Moving left from a bad index eventually reaches the beginning of its bad
run.  The last conjunct records that no good index was crossed. -/
theorem exists_runStart_le {N i : ℕ} {bad : ℕ → Prop} [DecidablePred bad]
    (hiN : i < N) (hi : bad i) :
    ∃ a, a ≤ i ∧ a ∈ runStarts N bad ∧
      ∀ j, a ≤ j → j ≤ i → bad j := by
  induction i with
  | zero =>
      refine ⟨0, le_rfl, ?_, ?_⟩
      · rw [mem_runStarts]
        exact ⟨hiN, hi, Or.inl rfl⟩
      · intro j hj₀ hj₁
        have : j = 0 := by omega
        simpa [this] using hi
  | succ i ih =>
      by_cases hprev : bad i
      · obtain ⟨a, hai, hastart, harun⟩ := ih (by omega) hprev
        refine ⟨a, by omega, hastart, ?_⟩
        intro j haj hji
        by_cases hj : j = i + 1
        · simpa [hj] using hi
        · exact harun j haj (by omega)
      · refine ⟨i + 1, le_rfl, ?_, ?_⟩
        · rw [mem_runStarts]
          refine ⟨hiN, hi, Or.inr ?_⟩
          change ¬ bad i
          exact hprev
        · intro j hj₀ hj₁
          have : j = i + 1 := by omega
          simpa [this] using hi

/-- Every bad grid point belongs to one of the maximal bad runs. -/
theorem exists_maximalBadRun_containing {N i : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad] (hiN : i < N) (hi : bad i) :
    ∃ a b, IsMaximalBadRun N bad a b ∧ a ≤ i ∧ i ≤ b := by
  obtain ⟨a, hai, hastart, harun⟩ := exists_runStart_le hiN hi
  let P : ℕ → Prop := fun b ↦
    b < N ∧ ∀ j ∈ Finset.range N, a ≤ j → j ≤ b → bad j
  let _ : DecidablePred P := fun _ ↦ inferInstance
  have hi_bound : i ≤ N - 1 := by omega
  have hPi : P i := by
    refine ⟨hiN, ?_⟩
    intro j hjN haj hji
    exact harun j haj hji
  let b := Nat.findGreatest P (N - 1)
  have hib : i ≤ b := by
    exact Nat.le_findGreatest hi_bound hPi
  have hPb : P b := by
    exact Nat.findGreatest_spec hi_bound hPi
  have hright : b + 1 = N ∨ ¬ bad (b + 1) := by
    by_cases heq : b + 1 = N
    · exact Or.inl heq
    · right
      intro hbad
      have hsuccN : b + 1 < N := by omega
      have hsuccBound : b + 1 ≤ N - 1 := by omega
      have hPsucc : P (b + 1) := by
        refine ⟨hsuccN, ?_⟩
        intro j hjN haj hjb
        by_cases hj : j = b + 1
        · simpa [hj] using hbad
        · exact hPb.2 j hjN haj (by omega)
      exact (Nat.findGreatest_is_greatest (P := P) (n := N - 1)
        (k := b + 1) (Nat.lt_succ_self b) hsuccBound) hPsucc
  refine ⟨a, b, ?_, hai, hib⟩
  refine ⟨hai.trans hib, hPb.1, hPb.2, ?_, hright⟩
  exact (mem_runStarts.mp hastart).2.2

theorem exists_mem_maximalBadRuns_containing {N i : ℕ} {bad : ℕ → Prop}
    [DecidablePred bad] (hiN : i < N) (hi : bad i) :
    ∃ I ∈ maximalBadRuns N bad, I.1 ≤ i ∧ i ≤ I.2 := by
  obtain ⟨a, b, hab, hai, hib⟩ := exists_maximalBadRun_containing hiN hi
  exact ⟨(a, b), mem_maximalBadRuns.mpr hab, hai, hib⟩

/-! ## Turning changes into level roots -/

/-- A continuous function which lies strictly on one side of a level at one
endpoint and weakly on the other side at the other endpoint attains the level
inside the interval.  Applying this to `fun x ↦ |f x|` is the analytic input
needed for grid-change counting. -/
theorem exists_level_between {f : ℝ → ℝ} (hf : Continuous f)
    {x y level : ℝ} (hxy : x ≤ y)
    (hcross : (f x < level ∧ level ≤ f y) ∨
      (f y < level ∧ level ≤ f x)) :
    ∃ u ∈ Icc x y, f u = level := by
  rcases hcross with h | h
  · rcases intermediate_value_Icc hxy hf.continuousOn ⟨h.1.le, h.2⟩ with ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rcases intermediate_value_Icc' hxy hf.continuousOn ⟨h.1.le, h.2⟩ with ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

theorem exists_abs_level_between {f : ℝ → ℝ} (hf : Continuous f)
    {x y level : ℝ} (hxy : x ≤ y)
    (hcross : (|f x| < level ∧ level ≤ |f y|) ∨
      (|f y| < level ∧ level ≤ |f x|)) :
    ∃ u ∈ Icc x y, |f u| = level :=
  exists_level_between hf.abs hxy hcross

/-- A finite set of natural numbers contained in two adjacent positions has at
most two elements.  The hypothesis is phrased using its minimum so it is easy
to discharge from overlapping grid-cell estimates. -/
theorem card_le_two_of_pairwise_le_succ (s : Finset ℕ)
    (hclose : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → j ≤ i + 1) :
    s.card ≤ 2 := by
  by_cases hs : s.Nonempty
  · let a := s.min' hs
    have has : a ∈ s := Finset.min'_mem s hs
    have hsub : s ⊆ indexBlock a 2 := by
      intro i hi
      have hai : a ≤ i := Finset.min'_le s i hi
      have hia : i ≤ a + 1 := hclose a has i hi hai
      rw [mem_indexBlock]
      omega
    calc
      s.card ≤ (indexBlock a 2).card := Finset.card_le_card hsub
      _ = 2 := card_indexBlock a 2
  · by_contra hcard
    have hpos : 0 < s.card := by omega
    exact hs (Finset.card_pos.mp hpos)

/-- Closed cells in a strictly increasing real grid overlap with multiplicity
at most two. -/
theorem card_filter_root_eq_le_two {n N : ℕ} (hn : 0 < n)
    (bad : ℕ → Prop) [DecidablePred bad] (rootOf : ℕ → ℝ) (x : ℝ)
    (hcell : ∀ i ∈ changeIndices N bad, rootOf i ∈ gridCell n i) :
    ((changeIndices N bad).filter fun i ↦ rootOf i = x).card ≤ 2 := by
  apply card_le_two_of_pairwise_le_succ
  intro i hi j hj hij
  rw [Finset.mem_filter] at hi hj
  have hiCell := hcell i hi.1
  have hjCell := hcell j hj.1
  rw [gridCell, mem_Icc] at hiCell hjCell
  by_contra hnot
  have hij' : i + 1 < j := by omega
  have hgrid : gridPoint n (i + 1) < gridPoint n j :=
    gridPoint_strictMono hn hij'
  rw [hi.2] at hiCell
  rw [hj.2] at hjCell
  linarith

/-- If every change is assigned injectively to a member of a finite root set,
then the number of maximal bad runs is at most `roots.card + 1`. -/
theorem card_maximalBadRuns_le_card_roots_add_one
    (N : ℕ) (bad : ℕ → Prop) [DecidablePred bad]
    (roots : Finset ℝ) (rootOf : ℕ → ℝ)
    (hroot : ∀ i ∈ changeIndices N bad, rootOf i ∈ roots)
    (hinj : Set.InjOn rootOf (changeIndices N bad : Set ℕ)) :
    (maximalBadRuns N bad).card ≤ roots.card + 1 := by
  have hchanges : (changeIndices N bad).card ≤ roots.card :=
    Finset.card_le_card_of_injOn rootOf hroot hinj
  exact (card_maximalBadRuns_le_card_changeIndices_add_one N bad).trans
    (Nat.add_le_add_right hchanges 1)

/-- A version allowing each level root to be used by at most `m` adjacent
cells.  Taking `m = 2` is convenient for closed grid cells, whose only overlap
is at a shared endpoint. -/
theorem card_maximalBadRuns_le_mul_card_roots_add_one
    (N : ℕ) (bad : ℕ → Prop) [DecidablePred bad]
    (roots : Finset ℝ) (rootOf : ℕ → ℝ) (m : ℕ)
    (hroot : ∀ i ∈ changeIndices N bad, rootOf i ∈ roots)
    (hfiber : ∀ x ∈ roots,
      ((changeIndices N bad).filter fun i ↦ rootOf i = x).card ≤ m) :
    (maximalBadRuns N bad).card ≤ m * roots.card + 1 := by
  have hchanges : (changeIndices N bad).card ≤ m * roots.card :=
    Finset.card_le_mul_card_image_of_maps_to hroot m hfiber
  exact (card_maximalBadRuns_le_card_changeIndices_add_one N bad).trans
    (Nat.add_le_add_right hchanges 1)

/-- The ready-to-use closed-cell form of component counting.  A chosen level
root belongs to at most two consecutive closed cells, so no separate fiber
estimate is required from the caller. -/
theorem card_maximalBadRuns_le_two_mul_card_roots_add_one
    {n N : ℕ} (hn : 0 < n) (bad : ℕ → Prop) [DecidablePred bad]
    (roots : Finset ℝ) (rootOf : ℕ → ℝ)
    (hroot : ∀ i ∈ changeIndices N bad, rootOf i ∈ roots)
    (hcell : ∀ i ∈ changeIndices N bad, rootOf i ∈ gridCell n i) :
    (maximalBadRuns N bad).card ≤ 2 * roots.card + 1 := by
  apply card_maximalBadRuns_le_mul_card_roots_add_one N bad roots rootOf 2 hroot
  intro x hx
  exact card_filter_root_eq_le_two hn bad rootOf x hcell

end Erdos228.Intervals
