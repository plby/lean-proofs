/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 899.
https://www.erdosproblems.com/forum/thread/899

Informal authors:
- Imre Ruzsa

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos899.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/899.lean
-/
import Mathlib

/-!
# Erdős Problem 899

Ruzsa's translate-layer proof that an infinite set of natural numbers of
asymptotic density zero has an unbounded positive-difference/count ratio.

The mathematical proof and a detailed formalization guide are in `tex/899.tex`.
-/

open Filter Set
open scoped Pointwise Topology

namespace Erdos899

/-! ## Finite-window counting and increasing enumerations -/

/-- The finite window consisting of the elements of `S` in `[1, N]`. -/
noncomputable def window (S : Set ℕ) (N : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Icc 1 N).filter (fun n ↦ n ∈ S)

/-- The number of elements of `S` in the natural-number interval `[1, N]`. -/
noncomputable def countIn (S : Set ℕ) (N : ℕ) : ℕ :=
  (window S N).card

@[simp] lemma mem_window {S : Set ℕ} {N x : ℕ} :
    x ∈ window S N ↔ 1 ≤ x ∧ x ≤ N ∧ x ∈ S := by
  classical
  simp [window, and_assoc]

lemma countIn_eq_ncard (S : Set ℕ) (N : ℕ) :
    countIn S N = (S ∩ Icc 1 N).ncard := by
  classical
  rw [countIn, window, ← Set.ncard_coe_finset]
  congr 1
  ext n
  simp [and_left_comm, and_comm]

lemma countIn_mono_set {S T : Set ℕ} (hST : S ⊆ T) (N : ℕ) :
    countIn S N ≤ countIn T N := by
  classical
  unfold countIn window
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hST hn.2⟩

lemma countIn_mono_nat (S : Set ℕ) : Monotone (countIn S) := by
  intro M N hMN
  classical
  unfold countIn window
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, hn.1.2.trans hMN⟩, hn.2⟩

/-- The increasing enumeration of an infinite set of natural numbers. -/
noncomputable def enumerate (S : Set ℕ) : ℕ → ℕ :=
  Nat.nth (fun n ↦ n ∈ S)

lemma enumerate_strictMono {S : Set ℕ} (hS : S.Infinite) :
    StrictMono (enumerate S) :=
  Nat.nth_strictMono hS

lemma enumerate_mem {S : Set ℕ} (hS : S.Infinite) (i : ℕ) : enumerate S i ∈ S :=
  Nat.nth_mem_of_infinite hS i

lemma range_enumerate {S : Set ℕ} (hS : S.Infinite) : Set.range (enumerate S) = S :=
  Nat.range_nth_of_infinite hS

lemma countIn_enumerate_ge {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Ici 1) (k : ℕ) :
    k + 1 ≤ countIn S (enumerate S k) := by
  classical
  let F : Fin (k + 1) → ℕ := fun i ↦ enumerate S i
  have hF_inj : Function.Injective F := fun i j hij ↦ by
    apply Fin.ext
    exact (enumerate_strictMono hS).injective hij
  have hF_mem (i : Fin (k + 1)) : F i ∈ S ∩ Icc 1 (enumerate S k) := by
    have hi : i.1 ≤ k := by omega
    exact ⟨enumerate_mem hS i, hpos (enumerate_mem hS i),
      (enumerate_strictMono hS).monotone hi⟩
  rw [countIn_eq_ncard]
  calc
    k + 1 = (Set.range F).ncard := by
      rw [Set.ncard_range_of_injective hF_inj]
      simp
    _ ≤ (S ∩ Icc 1 (enumerate S k)).ncard := by
      apply Set.ncard_le_ncard (ht := (Set.finite_Icc 1 (enumerate S k)).subset inter_subset_right)
      rintro x ⟨i, rfl⟩
      exact hF_mem i

lemma countIn_tendsto_atTop {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Ici 1) :
    Tendsto (countIn S) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro k
  refine ⟨enumerate S k, ?_⟩
  intro N hN
  exact (Nat.le_succ k).trans
    ((countIn_enumerate_ge hS hpos k).trans (countIn_mono_nat S hN))

lemma eventually_countIn_pos {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Ici 1) :
    ∀ᶠ N in atTop, 0 < countIn S N := by
  exact (countIn_tendsto_atTop hS hpos).eventually (eventually_gt_atTop 0)

/-! ## Positive-difference rows -/

/-- Positive differences generated from the anchor `e i`. -/
def row (e : ℕ → ℕ) (i : ℕ) : Set ℕ :=
  {d | ∃ j, i < j ∧ d = e j - e i}

/-- The union of the rows with anchor index strictly below `m`. -/
def rows (e : ℕ → ℕ) (m : ℕ) : Set ℕ :=
  {d | ∃ i, i < m ∧ d ∈ row e i}

/-- The union of the rows with anchor index in `[lo, hi)`. -/
def blockRows (e : ℕ → ℕ) (lo hi : ℕ) : Set ℕ :=
  {d | ∃ i, lo ≤ i ∧ i < hi ∧ d ∈ row e i}

/-- The set of strictly positive pointwise differences of `S`. -/
def posDiff (S : Set ℕ) : Set ℕ :=
  (S - S) ∩ Ici 1

lemma row_subset_posDiff {S : Set ℕ} (hS : S.Infinite) (i : ℕ) :
    row (enumerate S) i ⊆ posDiff S := by
  rintro d ⟨j, hij, rfl⟩
  have hmono := enumerate_strictMono hS hij
  constructor
  · exact Set.sub_mem_sub (enumerate_mem hS j) (enumerate_mem hS i)
  · exact Nat.sub_pos_of_lt hmono

lemma rows_subset_posDiff {S : Set ℕ} (hS : S.Infinite) (m : ℕ) :
    rows (enumerate S) m ⊆ posDiff S := by
  rintro d ⟨i, -, hdi⟩
  exact row_subset_posDiff hS i hdi

lemma blockRows_subset_posDiff {S : Set ℕ} (hS : S.Infinite) (lo hi : ℕ) :
    blockRows (enumerate S) lo hi ⊆ posDiff S := by
  rintro d ⟨i, -, -, hdi⟩
  exact row_subset_posDiff hS i hdi

lemma rows_mono (e : ℕ → ℕ) : Monotone (rows e) := by
  intro m n hmn d
  rintro ⟨i, him, hdi⟩
  exact ⟨i, him.trans_le hmn, hdi⟩

lemma blockRows_mono_right (e : ℕ → ℕ) (lo : ℕ) : Monotone (blockRows e lo) := by
  intro m n hmn d
  rintro ⟨i, hlo, him, hdi⟩
  exact ⟨i, hlo, him.trans_le hmn, hdi⟩

lemma row_sdiff_rows_subset {e : ℕ → ℕ} {m r : ℕ} (_hmr : m ≤ r) :
    row e r \ rows e m ⊆ rows e (r + 1) \ rows e m := by
  intro d hd
  refine ⟨?_, hd.2⟩
  exact ⟨r, Nat.lt_succ_self r, hd.1⟩

lemma row_sdiff_blockRows_subset {e : ℕ → ℕ} {lo hi r : ℕ}
    (hlo : lo ≤ r) (_hhi : hi ≤ r) :
    row e r \ blockRows e lo hi ⊆ blockRows e lo (r + 1) \ blockRows e lo hi := by
  intro d hd
  refine ⟨?_, hd.2⟩
  exact ⟨r, hlo, Nat.lt_succ_self r, hd.1⟩

lemma countIn_sdiff_add_le {S T U : Set ℕ} (hST : S ⊆ U) (hTU : T ⊆ U) (hdisj : Disjoint S T)
    (N : ℕ) : countIn S N + countIn T N ≤ countIn U N := by
  classical
  let s := (Finset.Icc 1 N).filter (fun n ↦ n ∈ S)
  let t := (Finset.Icc 1 N).filter (fun n ↦ n ∈ T)
  let u := (Finset.Icc 1 N).filter (fun n ↦ n ∈ U)
  have hst : Disjoint s t := by
    refine Finset.disjoint_left.mpr ?_
    intro n hns hnt
    simp only [s, Finset.mem_filter] at hns
    simp only [t, Finset.mem_filter] at hnt
    exact Set.disjoint_left.1 hdisj hns.2 hnt.2
  have hsub : s ∪ t ⊆ u := by
    intro n hn
    rcases Finset.mem_union.mp hn with hn | hn
    · simp only [s, Finset.mem_filter] at hn
      simp only [u, Finset.mem_filter]
      exact ⟨hn.1, hST hn.2⟩
    · simp only [t, Finset.mem_filter] at hn
      simp only [u, Finset.mem_filter]
      exact ⟨hn.1, hTU hn.2⟩
  simpa [countIn, window, s, t, u, Finset.card_union_of_disjoint hst] using
    Finset.card_le_card hsub

lemma countIn_row_sdiff_add_le_rows {e : ℕ → ℕ} {m r : ℕ} (hmr : m ≤ r) (N : ℕ) :
    countIn (row e r \ rows e m) N + countIn (rows e m) N ≤
      countIn (rows e (r + 1)) N := by
  apply countIn_sdiff_add_le (fun d hd ↦ (row_sdiff_rows_subset hmr hd).1)
    (rows_mono e (by omega))
  exact Set.disjoint_sdiff_left

lemma countIn_row_sdiff_add_le_blockRows {e : ℕ → ℕ} {lo hi r : ℕ}
    (hlo : lo ≤ r) (hhi : hi ≤ r) (N : ℕ) :
    countIn (row e r \ blockRows e lo hi) N + countIn (blockRows e lo hi) N ≤
      countIn (blockRows e lo (r + 1)) N := by
  apply countIn_sdiff_add_le (fun d hd ↦ (row_sdiff_blockRows_subset hlo hhi hd).1)
    (blockRows_mono_right e lo (by omega)) Set.disjoint_sdiff_left

/-! ## Ruzsa's discrete translate-layer selection -/

/--
Let `u m x` be an increasing family of counts, all bounded by `d x`, and suppose
`d x ≤ K * a x` eventually.  After refining the filter by one frequent event,
one prefix `u m` absorbs every fixed later prefix up to an error smaller than
one third of `a`.

This is the discrete substitute for choosing a subsequence on which a finite
partial layer sum realizes its limsup.
-/
lemma exists_refinement_small_prefix_difference
    {ι : Type*} (l : Filter ι) [NeBot l]
    (a d : ι → ℕ) (u : ℕ → ι → ℕ) (K : ℕ)
    (ha : ∀ᶠ x in l, 0 < a x)
    (hd : ∀ᶠ x in l, d x ≤ K * a x)
    (hud : ∀ m x, u m x ≤ d x)
    (hmono : ∀ ⦃m r⦄, m ≤ r → ∀ x, u m x ≤ u r x) :
    ∃ (m : ℕ) (l' : Filter ι), NeBot l' ∧ l' ≤ l ∧
      ∀ r ≥ m, ∀ᶠ x in l', 3 * (u r x - u m x) < a x := by
  classical
  let T : Set ℕ :=
    {t | t ≤ 3 * K ∧ ∃ m : ℕ, ∃ᶠ x in l, t * a x ≤ 3 * u m x}
  have hT_finite : T.Finite := by
    apply Set.Finite.subset (Set.finite_Iic (3 * K))
    intro t ht
    exact ht.1
  have hT_zero : 0 ∈ T := by
    refine ⟨Nat.zero_le _, 0, ?_⟩
    simpa using (Filter.Eventually.frequently (Filter.Eventually.of_forall
      (fun x ↦ Nat.zero_le (3 * u 0 x))))
  obtain ⟨t, htT, htmax⟩ := Set.exists_max_image T id hT_finite ⟨0, hT_zero⟩
  simp only [id_eq] at htmax
  obtain ⟨htK, m, hm⟩ := htT
  let P : Set ι := {x | t * a x ≤ 3 * u m x}
  let l' : Filter ι := l ⊓ 𝓟 P
  have hl'_ne : NeBot l' := by
    rw [show l' = l ⊓ 𝓟 P from rfl, ← Filter.frequently_mem_iff_neBot]
    exact hm
  refine ⟨m, l', hl'_ne, inf_le_left, ?_⟩
  intro r hmr
  have hnot : ¬∃ᶠ x in l, (t + 1) * a x ≤ 3 * u r x := by
    intro hfreq
    by_cases htop : t < 3 * K
    · have hsuccT : t + 1 ∈ T := by
        exact ⟨Nat.succ_le_iff.mpr htop, r, hfreq⟩
      exact (Nat.not_succ_le_self t) (htmax (t + 1) hsuccT)
    · have hteq : t = 3 * K := Nat.le_antisymm htK (Nat.le_of_not_gt htop)
      have himpossible : ∀ᶠ x in l, 3 * u r x < (t + 1) * a x := by
        filter_upwards [ha, hd] with x hax hdx
        calc
          3 * u r x ≤ 3 * d x := Nat.mul_le_mul_left 3 (hud r x)
          _ ≤ 3 * (K * a x) := Nat.mul_le_mul_left 3 hdx
          _ = t * a x := by simp [hteq, Nat.mul_assoc]
          _ < (t + 1) * a x := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self t) hax
      exact hfreq (himpossible.mono fun x hx hle ↦ (not_le_of_gt hx) hle)
  have hupp : ∀ᶠ x in l, 3 * u r x < (t + 1) * a x := by
    simpa only [not_le] using (Filter.not_frequently.mp hnot)
  rw [Filter.eventually_inf_principal]
  filter_upwards [hupp] with x hxup hxlow
  have humr : u m x ≤ u r x := hmono hmr x
  have hmiddle : 3 * u r x < 3 * u m x + a x := by
    calc
      3 * u r x < (t + 1) * a x := hxup
      _ = t * a x + a x := by rw [Nat.add_mul, one_mul]
      _ ≤ 3 * u m x + a x := Nat.add_le_add_right hxlow _
  rw [Nat.mul_sub_left_distrib]
  omega

/-- A positive-cutoff version of `exists_refinement_small_prefix_difference`. -/
lemma exists_pos_refinement_small_prefix_difference
    {ι : Type*} (l : Filter ι) [NeBot l]
    (a d : ι → ℕ) (u : ℕ → ι → ℕ) (K : ℕ)
    (ha : ∀ᶠ x in l, 0 < a x)
    (hd : ∀ᶠ x in l, d x ≤ K * a x)
    (hud : ∀ m x, u m x ≤ d x)
    (hmono : ∀ ⦃m r⦄, m ≤ r → ∀ x, u m x ≤ u r x) :
    ∃ (m : ℕ) (l' : Filter ι), 0 < m ∧ NeBot l' ∧ l' ≤ l ∧
      ∀ r ≥ m, ∀ᶠ x in l', 3 * (u r x - u m x) < a x := by
  obtain ⟨m, l', hl', hle, hm⟩ :=
    exists_refinement_small_prefix_difference l a d u K ha hd hud hmono
  refine ⟨m + 1, l', Nat.zero_lt_succ m, hl', hle, ?_⟩
  intro r hr
  filter_upwards [hm r (by omega)] with x hx
  have hum : u m x ≤ u (m + 1) x := hmono (Nat.le_succ m) x
  have hur : u (m + 1) x ≤ u r x := hmono hr x
  have hsub : u r x - u (m + 1) x ≤ u r x - u m x := Nat.sub_le_sub_left hum _
  exact (Nat.mul_le_mul_left 3 hsub).trans_lt hx

/-! ## Finite escape lemmas -/

lemma Finset.exists_mem_not_mem_three
    {α : Type*}
    (X E₀ E₁ E₂ : Finset α)
    (h₀ : 3 * E₀.card < X.card)
    (h₁ : 3 * E₁.card < X.card)
    (h₂ : 3 * E₂.card < X.card) :
    ∃ x ∈ X, x ∉ E₀ ∧ x ∉ E₁ ∧ x ∉ E₂ := by
  classical
  by_contra! h
  have hsub : X ⊆ (E₀ ∪ E₁) ∪ E₂ := by
    intro x hx
    by_contra hxU
    simp only [Finset.mem_union, not_or] at hxU
    exact hxU.2 (h x hx hxU.1.1 hxU.1.2)
  have hcard_sub : X.card ≤ ((E₀ ∪ E₁) ∪ E₂).card := Finset.card_le_card hsub
  have hcard_union : ((E₀ ∪ E₁) ∪ E₂).card ≤ E₀.card + E₁.card + E₂.card := by
    calc
      ((E₀ ∪ E₁) ∪ E₂).card ≤ (E₀ ∪ E₁).card + E₂.card :=
        Finset.card_union_le (E₀ ∪ E₁) E₂
      _ ≤ (E₀.card + E₁.card) + E₂.card :=
        Nat.add_le_add_right (Finset.card_union_le E₀ E₁) _
  omega

lemma Set.exists_mem_not_mem_three
    {α : Type*}
    (X E₀ E₁ E₂ : Set α)
    (hX : X.Finite) (hE₀ : E₀.Finite) (hE₁ : E₁.Finite) (hE₂ : E₂.Finite)
    (h₀ : 3 * E₀.ncard < X.ncard)
    (h₁ : 3 * E₁.ncard < X.ncard)
    (h₂ : 3 * E₂.ncard < X.ncard) :
    ∃ x ∈ X, x ∉ E₀ ∧ x ∉ E₁ ∧ x ∉ E₂ := by
  classical
  rw [Set.ncard_eq_toFinset_card X hX, Set.ncard_eq_toFinset_card E₀ hE₀] at h₀
  rw [Set.ncard_eq_toFinset_card X hX, Set.ncard_eq_toFinset_card E₁ hE₁] at h₁
  rw [Set.ncard_eq_toFinset_card X hX, Set.ncard_eq_toFinset_card E₂ hE₂] at h₂
  obtain ⟨x, hx, hx₀, hx₁, hx₂⟩ :=
    Finset.exists_mem_not_mem_three hX.toFinset hE₀.toFinset hE₁.toFinset hE₂.toFinset
      h₀ h₁ h₂
  refine ⟨x, hX.mem_toFinset.mp hx, ?_, ?_, ?_⟩
  · exact fun hx' ↦ hx₀ (hE₀.mem_toFinset.mpr hx')
  · exact fun hx' ↦ hx₁ (hE₁.mem_toFinset.mpr hx')
  · exact fun hx' ↦ hx₂ (hE₂.mem_toFinset.mpr hx')

lemma Set.ncard_le_of_sub_maps
    (S T : Set ℕ) (a : ℕ)
    (hmap : ∀ x ∈ S, x - a ∈ T)
    (ha : ∀ x ∈ S, a ≤ x)
    (hT : T.Finite) :
    S.ncard ≤ T.ncard := by
  apply Set.ncard_le_ncard_of_injOn (fun x : ℕ ↦ x - a) hmap _ hT
  intro x hx y hy hxy
  exact (tsub_left_inj (ha x hx) (ha y hy)).mp hxy

/-! ## Two absorbing anchor blocks -/

/-- Differences made by two elements whose enumeration indices lie in the tail from `n`. -/
def tailDiff (e : ℕ → ℕ) (n : ℕ) : Set ℕ :=
  {d | ∃ p q, n ≤ q ∧ q < p ∧ d = e p - e q}

lemma tailDiff_nonempty {e : ℕ → ℕ} (n : ℕ) :
    (tailDiff e n).Nonempty := by
  refine ⟨e (n + 1) - e n, n + 1, n, le_rfl, Nat.lt_succ_self n, rfl⟩

lemma tailDiff_subset_posDiff {S : Set ℕ} (hS : S.Infinite) (n : ℕ) :
    tailDiff (enumerate S) n ⊆ posDiff S := by
  rintro d ⟨p, q, -, hqp, rfl⟩
  exact row_subset_posDiff hS q ⟨p, hqp, rfl⟩

/--
Under an eventual normalized upper bound for the global difference count,
there are two consecutive nonempty anchor blocks whose representation errors
are both smaller than one third of the ambient count on a common refinement
of `atTop`.
-/
lemma exists_two_absorbing_blocks
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Ici 1) (K : ℕ)
    (hbound : ∀ᶠ N in atTop, countIn (posDiff S) N ≤ K * countIn S N) :
    ∃ (m n : ℕ) (l : Filter ℕ), 0 < m ∧ m < n ∧ NeBot l ∧ l ≤ atTop ∧
      (∀ r ≥ m, ∀ᶠ N in l,
        3 * countIn (row (enumerate S) r \ rows (enumerate S) m) N < countIn S N) ∧
      (∀ r ≥ n, ∀ᶠ N in l,
        3 * countIn (row (enumerate S) r \ blockRows (enumerate S) m n) N < countIn S N) := by
  let e := enumerate S
  let a := countIn S
  let d := countIn (posDiff S)
  let u : ℕ → ℕ → ℕ := fun m N ↦ countIn (rows e m) N
  have ha : ∀ᶠ N in atTop, 0 < a N := eventually_countIn_pos hS hpos
  have hud : ∀ m N, u m N ≤ d N := by
    intro m N
    exact countIn_mono_set (rows_subset_posDiff hS m) N
  have humono : ∀ ⦃m r⦄, m ≤ r → ∀ N, u m N ≤ u r N := by
    intro m r hmr N
    exact countIn_mono_set (rows_mono e hmr) N
  obtain ⟨m, l₁, hmpos, hl₁ne, hl₁le, hfirst⟩ :=
    exists_pos_refinement_small_prefix_difference atTop a d u K ha hbound hud humono
  let v : ℕ → ℕ → ℕ := fun s N ↦ countIn (blockRows e m (m + s)) N
  have hvd : ∀ s N, v s N ≤ d N := by
    intro s N
    exact countIn_mono_set (blockRows_subset_posDiff hS m (m + s)) N
  have hvmono : ∀ ⦃s t⦄, s ≤ t → ∀ N, v s N ≤ v t N := by
    intro s t hst N
    exact countIn_mono_set (blockRows_mono_right e m (Nat.add_le_add_left hst m)) N
  let _ : NeBot l₁ := hl₁ne
  obtain ⟨s, l₂, hspos, hl₂ne, hl₂le, hsecond⟩ :=
    exists_pos_refinement_small_prefix_difference l₁ a d v K
      (ha.filter_mono hl₁le) (hbound.filter_mono hl₁le) hvd hvmono
  let n := m + s
  refine ⟨m, n, l₂, hmpos, by simp [n, hspos], hl₂ne, hl₂le.trans hl₁le, ?_, ?_⟩
  · intro r hmr
    filter_upwards [(hfirst (r + 1) (by omega)).filter_mono hl₂le] with N hsmall
    have hsum := countIn_row_sdiff_add_le_rows (e := e) hmr N
    have hbad : countIn (row e r \ rows e m) N ≤ u (r + 1) N - u m N := by
      dsimp [u]
      omega
    exact (Nat.mul_le_mul_left 3 hbad).trans_lt hsmall
  · intro r hrn
    let z := r + 1 - m
    have hsz : s ≤ z := by
      dsimp [z, n] at *
      omega
    have hidx : m + z = r + 1 := by
      dsimp [z]
      omega
    filter_upwards [hsecond z hsz] with N hsmall
    have hsmall' :
        3 * (countIn (blockRows e m (r + 1)) N - countIn (blockRows e m n) N) <
          countIn S N := by
      simpa only [v, hidx, n] using hsmall
    have hsum := countIn_row_sdiff_add_le_blockRows (e := e) (lo := m) (hi := n) (r := r)
      (by omega) hrn N
    have hbad : countIn (row e r \ blockRows e m n) N ≤
        countIn (blockRows e m (r + 1)) N - countIn (blockRows e m n) N := by
      omega
    exact (Nat.mul_le_mul_left 3 hbad).trans_lt hsmall'

/-! ## The finite three-exceptional-set escape -/

lemma finite_escape
    (e : ℕ → ℕ) (he : StrictMono e)
    {m n p q N : ℕ}
    (_hm : 0 < m) (_hmn : m < n) (_hqp : n ≤ q) (hpq : q < p)
    (hsmall0 : 3 * countIn (Set.range e) (e p + e (n - 1)) < countIn (Set.range e) N)
    (hsmall1 : 3 * countIn (row e p \ rows e m) N < countIn (Set.range e) N)
    (hsmall2 : 3 * countIn (row e q \ blockRows e m n) N < countIn (Set.range e) N) :
    ∃ s u, n ≤ s ∧ n ≤ u ∧
      e p - e q < e u - e s ∧ e u - e s ≤ (e p - e q) + e (n - 1) := by
  classical
  let X := window (Set.range e) N
  let E0 := X.filter (fun x ↦ x ≤ e p + e (n - 1))
  let E1 := X.filter (fun x ↦ e p < x ∧ x - e p ∉ rows e m)
  let E2 := X.filter (fun x ↦ e q < x ∧ x - e q ∉ blockRows e m n)
  have hcardX : X.card = countIn (Set.range e) N := by simp [X, countIn]
  have hcard0 : E0.card ≤ countIn (Set.range e) (e p + e (n - 1)) := by
    let Y := window (Set.range e) (e p + e (n - 1))
    change E0.card ≤ Y.card
    apply Finset.card_le_card
    intro x hx
    have hxE := Finset.mem_filter.mp hx
    have hxX : x ∈ X := hxE.1
    have hxle := hxE.2
    change x ∈ window (Set.range e) N at hxX
    have hxw := mem_window.mp hxX
    change x ∈ window (Set.range e) (e p + e (n - 1))
    exact mem_window.mpr ⟨hxw.1, hxle, hxw.2.2⟩
  have hcard1 : E1.card ≤ countIn (row e p \ rows e m) N := by
    let Y := window (row e p \ rows e m) N
    change E1.card ≤ Y.card
    apply Finset.card_le_card_of_injOn (fun x ↦ x - e p)
    · intro x hx
      have hxE := Finset.mem_filter.mp hx
      have hxX : x ∈ X := hxE.1
      have hxp' := hxE.2.1
      have hxnot := hxE.2.2
      change x ∈ window (Set.range e) N at hxX
      have hxw := mem_window.mp hxX
      change x - e p ∈ window (row e p \ rows e m) N
      apply mem_window.mpr
      refine ⟨Nat.sub_pos_of_lt hxp', (Nat.sub_le x (e p)).trans hxw.2.1, ?_, hxnot⟩
      rcases hxw.2.2 with ⟨j, rfl⟩
      exact ⟨j, (he.lt_iff_lt).mp hxp', rfl⟩
    · intro x hx y hy hxy
      have hxp' := (Finset.mem_filter.mp hx).2.1
      have hyp' := (Finset.mem_filter.mp hy).2.1
      exact (tsub_left_inj (Nat.le_of_lt hxp') (Nat.le_of_lt hyp')).mp hxy
  have hcard2 : E2.card ≤ countIn (row e q \ blockRows e m n) N := by
    let Y := window (row e q \ blockRows e m n) N
    change E2.card ≤ Y.card
    apply Finset.card_le_card_of_injOn (fun x ↦ x - e q)
    · intro x hx
      have hxE := Finset.mem_filter.mp hx
      have hxX : x ∈ X := hxE.1
      have hxq' := hxE.2.1
      have hxnot := hxE.2.2
      change x ∈ window (Set.range e) N at hxX
      have hxw := mem_window.mp hxX
      change x - e q ∈ window (row e q \ blockRows e m n) N
      apply mem_window.mpr
      refine ⟨Nat.sub_pos_of_lt hxq', (Nat.sub_le x (e q)).trans hxw.2.1, ?_, hxnot⟩
      rcases hxw.2.2 with ⟨j, rfl⟩
      exact ⟨j, (he.lt_iff_lt).mp hxq', rfl⟩
    · intro x hx y hy hxy
      have hxq' := (Finset.mem_filter.mp hx).2.1
      have hyq' := (Finset.mem_filter.mp hy).2.1
      exact (tsub_left_inj (Nat.le_of_lt hxq') (Nat.le_of_lt hyq')).mp hxy
  have hsum : E0.card + E1.card + E2.card < X.card := by
    rw [hcardX]
    omega
  have hproper : E0 ∪ E1 ∪ E2 ≠ X := by
    intro heq
    have hlecard : X.card ≤ E0.card + E1.card + E2.card := by
      rw [← heq]
      calc
        (E0 ∪ E1 ∪ E2).card ≤ (E0 ∪ E1).card + E2.card :=
          Finset.card_union_le (E0 ∪ E1) E2
        _ ≤ (E0.card + E1.card) + E2.card :=
          Nat.add_le_add_right (Finset.card_union_le E0 E1) _
    omega
  have hsub : E0 ∪ E1 ∪ E2 ⊆ X := by
    intro x hx
    simp only [Finset.mem_union] at hx
    rcases hx with (hx | hx) | hx
    · exact (Finset.mem_filter.mp hx).1
    · exact (Finset.mem_filter.mp hx).1
    · exact (Finset.mem_filter.mp hx).1
  have hssub : E0 ∪ E1 ∪ E2 ⊂ X := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hproper⟩
  obtain ⟨x, hxX, hxbad⟩ := Finset.exists_of_ssubset hssub
  have hx0 : ¬x ≤ e p + e (n - 1) := by
    intro hx
    apply hxbad
    simp only [Finset.mem_union]
    left
    left
    exact Finset.mem_filter.mpr ⟨hxX, hx⟩
  have hxp : e p < x := by omega
  have hxq : e q < x := (he hpq).trans hxp
  have hx1 : x - e p ∈ rows e m := by
    by_contra h
    apply hxbad
    simp only [Finset.mem_union]
    left
    right
    exact Finset.mem_filter.mpr ⟨hxX, hxp, h⟩
  have hx2 : x - e q ∈ blockRows e m n := by
    by_contra h
    apply hxbad
    simp only [Finset.mem_union]
    right
    exact Finset.mem_filter.mpr ⟨hxX, hxq, h⟩
  rcases hx1 with ⟨i, him, s, his, hxs⟩
  rcases hx2 with ⟨t, hmt, htn, u, htu, hxu⟩
  have hns : n ≤ s := by
    by_contra hsn
    have hsn' : s ≤ n - 1 := by omega
    have hes : e s ≤ e (n - 1) := he.monotone hsn'
    have hesub : e (n - 1) < x - e p := by omega
    have hles : x - e p ≤ e s := hxs.trans_le (Nat.sub_le _ _)
    omega
  have hnu : n ≤ u := by
    by_contra hun
    have hun' : u ≤ n - 1 := by omega
    have heu : e u ≤ e (n - 1) := he.monotone hun'
    have heq_lt_ep : e q < e p := he hpq
    have heusub : e (n - 1) < x - e q := by omega
    have hleu : x - e q ≤ e u := hxu.trans_le (Nat.sub_le _ _)
    omega
  have hit : i < t := him.trans_le hmt
  have heis : e i < e s := he his
  have hetu : e t < e u := he htu
  have heit : e i < e t := he hit
  have heqp : e q < e p := he hpq
  have hid : e u - e s = (e p - e q) + (e t - e i) := by
    omega
  have hincpos : 0 < e t - e i := Nat.sub_pos_of_lt heit
  have htindex : t ≤ n - 1 := by omega
  have hetop : e t ≤ e (n - 1) := he.monotone htindex
  have hincle : e t - e i ≤ e (n - 1) := (Nat.sub_le _ _).trans hetop
  refine ⟨s, u, hns, hnu, ?_, ?_⟩
  · rw [hid]
    omega
  · rw [hid]
    exact Nat.add_le_add_left hincle _

/-! ## Ruzsa's bounded-gap alternative -/

lemma exists_syndetic_tail_of_eventually_bounded
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Ici 1) (K : ℕ)
    (hbound : ∀ᶠ N in atTop, countIn (posDiff S) N ≤ K * countIn S N) :
    ∃ (n C : ℕ), 0 < C ∧ (tailDiff (enumerate S) n).Nonempty ∧
      tailDiff (enumerate S) n ⊆ posDiff S ∧
      ∀ d ∈ tailDiff (enumerate S) n,
        ∃ e ∈ tailDiff (enumerate S) n, d < e ∧ e ≤ d + C := by
  obtain ⟨m, n, l, hm, hmn, hlne, hlat, hfirst, hsecond⟩ :=
    exists_two_absorbing_blocks hS hpos K hbound
  let e := enumerate S
  let C := e (n - 1)
  have hC : 0 < C := hpos (enumerate_mem hS (n - 1))
  refine ⟨n, C, hC, tailDiff_nonempty n,
    tailDiff_subset_posDiff hS n, ?_⟩
  intro d hd
  rcases hd with ⟨p, q, hnq, hqp, rfl⟩
  have hmp : m ≤ p := by omega
  have hboundary : ∀ᶠ N in l,
      3 * countIn S (e p + e (n - 1)) < countIn S N := by
    have htop : ∀ᶠ N in atTop,
        3 * countIn S (e p + e (n - 1)) < countIn S N :=
      (countIn_tendsto_atTop hS hpos).eventually
        (eventually_gt_atTop (3 * countIn S (e p + e (n - 1))))
    exact htop.filter_mono hlat
  let _ : NeBot l := hlne
  obtain ⟨N, hN⟩ := (hboundary.and (hfirst p hmp) |>.and (hsecond q hnq)).exists
  rcases hN with ⟨⟨hN0, hN1⟩, hN2⟩
  have hN0' : 3 * countIn (Set.range e) (e p + e (n - 1)) <
      countIn (Set.range e) N := by
    simpa only [e, range_enumerate hS] using hN0
  have hN1' : 3 * countIn (row e p \ rows e m) N < countIn (Set.range e) N := by
    simpa only [e, range_enumerate hS] using hN1
  have hN2' : 3 * countIn (row e q \ blockRows e m n) N < countIn (Set.range e) N := by
    simpa only [e, range_enumerate hS] using hN2
  obtain ⟨s, u, hns, hnu, hlt, hle⟩ :=
    finite_escape e (enumerate_strictMono hS) hm hmn hnq hqp hN0' hN1' hN2'
  have hsu : s < u := by
    have heqp : e q < e p := enumerate_strictMono hS hqp
    have hdpos : 0 < e p - e q := Nat.sub_pos_of_lt heqp
    have hnewpos : 0 < e u - e s := hdpos.trans hlt
    exact (enumerate_strictMono hS).lt_iff_lt.mp (Nat.sub_pos_iff_lt.mp hnewpos)
  refine ⟨e u - e s, ⟨u, s, hns, hsu, rfl⟩, hlt, ?_⟩
  simpa only [C] using hle

/-! ## Counting a bounded-gap difference chain -/

noncomputable def nextIn (S : Set ℕ)
    (hnext : ∀ d ∈ S, ∃ e ∈ S, d < e ∧ e ≤ d + C) (d : S) : S :=
  ⟨(hnext d d.property).choose, (hnext d d.property).choose_spec.1⟩

lemma lt_nextIn (S : Set ℕ)
    (hnext : ∀ d ∈ S, ∃ e ∈ S, d < e ∧ e ≤ d + C) (d : S) :
    d.1 < (nextIn S hnext d).1 :=
  (hnext d d.property).choose_spec.2.1

lemma nextIn_le (S : Set ℕ)
    (hnext : ∀ d ∈ S, ∃ e ∈ S, d < e ∧ e ≤ d + C) (d : S) :
    (nextIn S hnext d).1 ≤ d.1 + C :=
  (hnext d d.property).choose_spec.2.2

noncomputable def chain (S : Set ℕ)
    (hnext : ∀ d ∈ S, ∃ e ∈ S, d < e ∧ e ≤ d + C) (d0 : S) : ℕ → S
  | 0 => d0
  | n + 1 => nextIn S hnext (chain S hnext d0 n)

@[simp] lemma chain_zero (S : Set ℕ)
    (hnext : ∀ d ∈ S, ∃ e ∈ S, d < e ∧ e ≤ d + C) (d0 : S) :
    chain S hnext d0 0 = d0 := rfl

@[simp] lemma chain_succ (S : Set ℕ)
    (hnext : ∀ d ∈ S, ∃ e ∈ S, d < e ∧ e ≤ d + C) (d0 : S) (n : ℕ) :
    chain S hnext d0 (n + 1) = nextIn S hnext (chain S hnext d0 n) := rfl

lemma chain_strictMono (S : Set ℕ)
    (hnext : ∀ d ∈ S, ∃ e ∈ S, d < e ∧ e ≤ d + C) (d0 : S) :
    StrictMono fun n ↦ (chain S hnext d0 n).1 := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [chain_succ]
  exact lt_nextIn S hnext _

lemma chain_le (S : Set ℕ)
    (hnext : ∀ d ∈ S, ∃ e ∈ S, d < e ∧ e ≤ d + C) (d0 : S) (n : ℕ) :
    (chain S hnext d0 n).1 ≤ d0.1 + n * C := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [chain_succ]
      calc
        (nextIn S hnext (chain S hnext d0 n)).1 ≤ (chain S hnext d0 n).1 + C :=
          nextIn_le S hnext _
        _ ≤ (d0.1 + n * C) + C := Nat.add_le_add_right ih _
        _ = d0.1 + (n + 1) * C := by simp [Nat.add_mul, Nat.add_assoc]

lemma countIn_linear_lower (S : Set ℕ) {d0 C : ℕ}
    (hd0pos : 0 < d0) (hd0 : d0 ∈ S)
    (hnext : ∀ d ∈ S, ∃ e ∈ S, d < e ∧ e ≤ d + C) (k : ℕ) :
    k + 1 ≤ countIn S (d0 + k * C) := by
  classical
  let d0S : S := ⟨d0, hd0⟩
  let f : ℕ → ℕ := fun n ↦ (chain S hnext d0S n).1
  change k + 1 ≤ (window S (d0 + k * C)).card
  rw [← Finset.card_range (k + 1)]
  apply Finset.card_le_card_of_injOn f
  · intro j hj
    have hjk : j ≤ k := by simpa using hj
    apply mem_window.mpr
    refine ⟨?_, ?_, (chain S hnext d0S j).property⟩
    · exact hd0pos.trans_le ((chain_strictMono S hnext d0S).monotone (Nat.zero_le j))
    · calc
        f j ≤ d0 + j * C := chain_le S hnext d0S j
        _ ≤ d0 + k * C := Nat.add_le_add_left (Nat.mul_le_mul_right C hjk) _
  · exact (chain_strictMono S hnext d0S).injective.injOn

lemma density_eventually_mul_lt (a : ℕ → ℕ)
    (hden : Tendsto (fun N ↦ (a N : ℝ) / N) atTop (𝓝 0))
    {M : ℕ} (hM : 0 < M) :
    ∀ᶠ N in atTop, M * a N < N := by
  have hratio : ∀ᶠ N in atTop, (a N : ℝ) / N < 1 / (M : ℝ) :=
    hden.eventually (Iio_mem_nhds (by positivity))
  filter_upwards [hratio, eventually_gt_atTop (0 : ℕ)] with N hN hNpos
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hcross : (a N : ℝ) * M < (N : ℝ) := by
    simpa only [one_mul] using (div_lt_div_iff₀ hNr hMr).mp hN
  have hcross' : (M : ℝ) * (a N : ℝ) < (N : ℝ) := by
    simpa only [mul_comm] using hcross
  exact_mod_cast hcross'

lemma no_eventual_bound_of_linear_scales
    (a d : ℕ → ℕ)
    (hden : Tendsto (fun N ↦ (a N : ℝ) / N) atTop (𝓝 0))
    {d0 C : ℕ} (hC : 0 < C)
    (hlower : ∀ k, k + 1 ≤ d (d0 + k * C)) (K : ℕ) :
    ¬∀ᶠ N in atTop, d N ≤ K * a N := by
  intro hbound
  let Q := d0 + C
  let M := K * Q + 1
  have hM : 0 < M := by simp [M]
  have hdense := density_eventually_mul_lt a hden hM
  rcases (eventually_atTop.1 (hbound.and hdense)) with ⟨L, hL⟩
  let N := d0 + L * C
  have hLN : L ≤ N := by
    dsimp [N]
    nlinarith
  have hp := hL N hLN
  have hlo := hlower L
  have hNupper : N ≤ Q * (L + 1) := by
    dsimp [N, Q]
    nlinarith
  dsimp [N] at hlo hp
  dsimp [M, Q] at hp
  dsimp [Q] at hNupper
  nlinarith

/-- The positive-difference ratio of a positive infinite set has no eventual finite bound. -/
lemma no_eventual_bound_posDiff
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Ici 1)
    (hden : Tendsto (fun N ↦ (countIn S N : ℝ) / N) atTop (𝓝 0)) (K : ℕ) :
    ¬∀ᶠ N in atTop, countIn (posDiff S) N ≤ K * countIn S N := by
  intro hbound
  obtain ⟨n, C, hC, htail_ne, htail_sub, hnext⟩ :=
    exists_syndetic_tail_of_eventually_bounded hS hpos K hbound
  obtain ⟨d0, hd0⟩ := htail_ne
  have hd0pos : 0 < d0 := by
    have := htail_sub hd0
    exact this.2
  have hlower_tail (k : ℕ) :
      k + 1 ≤ countIn (tailDiff (enumerate S) n) (d0 + k * C) :=
    countIn_linear_lower _ hd0pos hd0 hnext k
  have hlower (k : ℕ) : k + 1 ≤ countIn (posDiff S) (d0 + k * C) :=
    (hlower_tail k).trans (countIn_mono_set htail_sub _)
  exact no_eventual_bound_of_linear_scales (countIn S) (countIn (posDiff S))
    hden hC hlower K hbound

/-! ## Conversion to the specified `EReal` limsup -/

lemma limsup_ratio_eq_top
    (a d : ℕ → ℕ)
    (ha : ∀ᶠ N in atTop, 0 < a N)
    (hlarge : ∀ k : ℕ, ∃ᶠ N in atTop, k * a N ≤ d N) :
    atTop.limsup (fun N ↦ (d N : EReal) / (a N : EReal)) = ⊤ := by
  apply (EReal.eq_top_iff_forall_lt _).2
  intro y
  obtain ⟨k, hyk⟩ := exists_nat_gt y
  have hk : (k : EReal) ≤
      atTop.limsup (fun N ↦ (d N : EReal) / (a N : EReal)) := by
    apply le_limsup_of_frequently_le'
    exact (hlarge k).and_eventually ha |>.mono (fun N hN ↦ by
      apply (EReal.le_div_iff_mul_le (by exact_mod_cast hN.2)
        (EReal.natCast_ne_top (a N))).2
      exact_mod_cast hN.1)
  exact (EReal.coe_lt_coe_iff.2 hyk).trans_le hk

theorem erdos_899 : ∀ (A : Set ℕ), A.Infinite →
    Tendsto (fun N => (A ∩ Icc 1 N |>.ncard : ℝ) / N) atTop (𝓝 0) →
    atTop.limsup (fun N => ((A - A : Set ℕ) ∩ Icc 1 N |>.ncard : EReal) /
      (A ∩ Icc 1 N).ncard) = ⊤ := by
  intro A hA hden
  let B : Set ℕ := A \ {0}
  have hB : B.Infinite := hA.sdiff (Set.finite_singleton 0)
  have hBpos : B ⊆ Ici 1 := by
    intro x hx
    have hx0 : x ≠ 0 := by
      exact fun h ↦ hx.2 (by simp [h])
    exact Nat.one_le_iff_ne_zero.mpr hx0
  have hBA : B ⊆ A := sdiff_subset
  have hwindow (N : ℕ) : B ∩ Icc 1 N = A ∩ Icc 1 N := by
    ext x
    constructor
    · intro hx
      exact ⟨hBA hx.1, hx.2⟩
    · intro hx
      refine ⟨⟨hx.1, ?_⟩, hx.2⟩
      simp only [mem_singleton_iff]
      exact Nat.ne_of_gt hx.2.1
  have hcount (N : ℕ) : countIn B N = (A ∩ Icc 1 N).ncard := by
    rw [countIn_eq_ncard, hwindow]
  have hdenB : Tendsto (fun N ↦ (countIn B N : ℝ) / N) atTop (𝓝 0) := by
    simpa only [hcount] using hden
  have hdiff : posDiff B ⊆ A - A := by
    intro d hd
    exact Set.sub_subset_sub hBA hBA hd.1
  have hlargeB : ∀ k : ℕ, ∃ᶠ N in atTop,
      k * countIn B N ≤ countIn (posDiff B) N := by
    intro k
    have hnot := no_eventual_bound_posDiff hB hBpos hdenB k
    exact (not_eventually.mp hnot).mono fun N hN ↦ by omega
  have hlargeA : ∀ k : ℕ, ∃ᶠ N in atTop,
      k * countIn B N ≤ countIn (A - A) N := by
    intro k
    exact (hlargeB k).mono fun N hN ↦
      hN.trans (countIn_mono_set hdiff N)
  have htop := limsup_ratio_eq_top (countIn B) (countIn (A - A))
    (eventually_countIn_pos hB hBpos) hlargeA
  simpa only [countIn_eq_ncard, hwindow] using htop

#print axioms Erdos899.erdos_899

end Erdos899
