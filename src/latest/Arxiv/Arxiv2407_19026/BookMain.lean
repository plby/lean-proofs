import Arxiv.Arxiv2407_19026.Book

/-!
# The moment induction

This file formalizes the degree-regularization and moment-induction parts of
Section 3 of arXiv:2407.19026.
-/

open Finset

noncomputable section

namespace Arxiv2407_19026

/-- Deleting vertices whose red degree is below the threshold leaves a
nonempty subset on which every red degree is above the threshold, while
not decreasing the corresponding edge surplus. -/
lemma exists_degree_regularized_subset {V : Type*} (G : SimpleGraph V)
    (q : ℝ) (X Y : Finset V) (hpos : 0 < excessBetween q G X Y) :
    ∃ X' : Finset V, X'.Nonempty ∧ X' ⊆ X ∧
      excessBetween q G X Y ≤ excessBetween q G X' Y ∧
      ∀ v ∈ X', q * Y.card ≤ (redNeighborsIn G v Y).card := by
  classical
  revert hpos
  apply Finset.strongInduction (p := fun X ↦
    0 < excessBetween q G X Y →
      ∃ X' : Finset V, X'.Nonempty ∧ X' ⊆ X ∧
        excessBetween q G X Y ≤ excessBetween q G X' Y ∧
        ∀ v ∈ X', q * Y.card ≤ (redNeighborsIn G v Y).card)
  intro X ih hpos
  by_cases hall :
      ∀ v ∈ X, q * Y.card ≤ (redNeighborsIn G v Y).card
  · exact ⟨X, left_nonempty_of_excessBetween_pos hpos, Subset.rfl,
      le_rfl, hall⟩
  · push Not at hall
    obtain ⟨v, hvX, hvlow⟩ := hall
    let X₀ := X.erase v
    have hdecomp :
        excessBetween q G X Y =
          excessBetween q G X₀ Y + excessBetween q G {v} Y := by
      have hdisj : Disjoint X₀ {v} := by
        simp [X₀]
      have hunion : X₀ ∪ {v} = X := by
        simp [X₀, hvX]
      rw [← hunion, excessBetween_union_left q G hdisj]
    have hsingle :
        excessBetween q G {v} Y =
          (redNeighborsIn G v Y).card - q * Y.card := by
      rw [excessBetween, redEdgesBetween_singleton_left]
      simp
    have hinc :
        excessBetween q G X Y < excessBetween q G X₀ Y := by
      rw [hdecomp, hsingle]
      linarith
    have hX₀pos : 0 < excessBetween q G X₀ Y :=
      hpos.trans hinc
    have hssub : X₀ ⊂ X := by
      simpa [X₀] using erase_ssubset hvX
    obtain ⟨X', hX'ne, hX'X₀, hexcess, hdeg⟩ :=
      ih X₀ hssub hX₀pos
    exact ⟨X', hX'ne, hX'X₀.trans (erase_subset _ _),
      hinc.le.trans hexcess, hdeg⟩

/-- Increasing positive edge surplus on a smaller nonempty left set cannot
decrease the shifted density. -/
lemma density_sub_le_of_subset_of_excess_le {V : Type*} (G : SimpleGraph V)
    (q : ℝ) {X X' Y : Finset V}
    (hX : X.Nonempty) (hX' : X'.Nonempty) (hY : Y.Nonempty)
    (hsub : X' ⊆ X)
    (hpos : 0 < excessBetween q G X Y)
    (hexcess : excessBetween q G X Y ≤ excessBetween q G X' Y) :
    densityBetween G X Y - q ≤ densityBetween G X' Y - q := by
  let P : ℝ := (X.card : ℝ) * Y.card
  let P' : ℝ := (X'.card : ℝ) * Y.card
  let E : ℝ := excessBetween q G X Y
  let E' : ℝ := excessBetween q G X' Y
  have hP : 0 < P := by
    dsimp [P]
    positivity
  have hP' : 0 < P' := by
    dsimp [P']
    positivity
  have hPP' : P' ≤ P := by
    dsimp [P', P]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast card_le_card hsub) (by positivity)
  have hE : E = P * (densityBetween G X Y - q) := by
    simpa [E, P] using excessBetween_eq_density G q X Y
  have hE' : E' = P' * (densityBetween G X' Y - q) := by
    simpa [E', P'] using excessBetween_eq_density G q X' Y
  have hE'0 : 0 ≤ E' := le_trans hpos.le hexcess
  have hcross : P' * E ≤ P * E' := by
    calc
      P' * E ≤ P * E :=
        mul_le_mul_of_nonneg_right hPP' hpos.le
      _ ≤ P * E' :=
        mul_le_mul_of_nonneg_left hexcess hP.le
  apply le_of_mul_le_mul_left (a := P * P') ?_ (mul_pos hP hP')
  calc
    P * P' * (densityBetween G X Y - q) = P' * E := by
      rw [hE]
      ring
    _ ≤ P * E' := hcross
    _ = P * P' * (densityBetween G X' Y - q) := by
      rw [hE']
      ring

/-- Degree regularization preserves every positive integer moment of the
shifted density. -/
lemma exists_degree_regularized_subset_moment {V : Type*}
    (G : SimpleGraph V) (q : ℝ) (X Y : Finset V) (r : ℕ) (hr : 1 ≤ r)
    (hX : X.Nonempty) (hY : Y.Nonempty)
    (hshift : 0 < densityBetween G X Y - q) :
    ∃ X' : Finset V, X'.Nonempty ∧ X' ⊆ X ∧
      (densityBetween G X Y - q) ^ r * X.card * Y.card ≤
        (densityBetween G X' Y - q) ^ r * X'.card * Y.card ∧
      ∀ v ∈ X', q * Y.card ≤ (redNeighborsIn G v Y).card := by
  have hP : 0 < (X.card : ℝ) * Y.card := by positivity
  have hexcessPos : 0 < excessBetween q G X Y := by
    rw [excessBetween_eq_density]
    positivity
  obtain ⟨X', hX', hsub, hexcess, hdeg⟩ :=
    exists_degree_regularized_subset G q X Y hexcessPos
  have hshiftMono :=
    density_sub_le_of_subset_of_excess_le G q hX hX' hY hsub
      hexcessPos hexcess
  have hshift' : 0 ≤ densityBetween G X' Y - q :=
    hshift.le.trans hshiftMono
  have hpow :
      (densityBetween G X Y - q) ^ (r - 1) ≤
        (densityBetween G X' Y - q) ^ (r - 1) :=
    pow_le_pow_left₀ hshift.le hshiftMono (r - 1)
  have hmul :
      (densityBetween G X Y - q) ^ (r - 1) *
          excessBetween q G X Y ≤
        (densityBetween G X' Y - q) ^ (r - 1) *
          excessBetween q G X' Y :=
    mul_le_mul hpow hexcess hexcessPos.le
      (pow_nonneg hshift' _)
  refine ⟨X', hX', hsub, ?_, hdeg⟩
  calc
    (densityBetween G X Y - q) ^ r * X.card * Y.card =
        (densityBetween G X Y - q) ^ (r - 1) *
          excessBetween q G X Y := by
      rw [excessBetween_eq_density]
      conv_lhs =>
        rw [show r = (r - 1) + 1 by omega, pow_succ]
      ring
    _ ≤ (densityBetween G X' Y - q) ^ (r - 1) *
          excessBetween q G X' Y := hmul
    _ = (densityBetween G X' Y - q) ^ r * X'.card * Y.card := by
      rw [excessBetween_eq_density]
      conv_rhs =>
        rw [show r = (r - 1) + 1 by omega, pow_succ]
      ring

/-- Candidate-packaged degree regularization. -/
lemma Candidate.exists_degree_regularized {V : Type*} {G : SimpleGraph V}
    (C : Candidate G) (q : ℝ) (r : ℕ) (hr : 1 ≤ r)
    (hshift : 0 < C.density - q) :
    ∃ D : Candidate G, D.X ⊆ C.X ∧ D.Y = C.Y ∧
      (C.density - q) ^ r * C.X.card * C.Y.card ≤
        (D.density - q) ^ r * D.X.card * D.Y.card ∧
      ∀ v ∈ D.X, q * D.Y.card ≤
        (redNeighborsIn G v D.Y).card := by
  obtain ⟨X', hX', hsub, hmoment, hdeg⟩ :=
    exists_degree_regularized_subset_moment G q C.X C.Y r hr
      C.X_nonempty C.Y_nonempty (by simpa [Candidate.density] using hshift)
  let D : Candidate G := {
    X := X'
    Y := C.Y
    X_nonempty := hX'
    Y_nonempty := C.Y_nonempty
    disjoint := C.disjoint.mono_left hsub
  }
  refine ⟨D, hsub, rfl, ?_, ?_⟩
  · simpa [Candidate.density, D] using hmoment
  · simpa [D] using hdeg

lemma redEdgesBetween_le_card_mul_card {V : Type*} (G : SimpleGraph V)
    (X Y : Finset V) :
    redEdgesBetween G X Y ≤ X.card * Y.card := by
  rw [redEdgesBetween_eq_sum_card]
  calc
    ∑ v ∈ X, (redNeighborsIn G v Y).card ≤
        ∑ _v ∈ X, Y.card := by
      apply sum_le_sum
      intro v hv
      exact card_le_card (redNeighborsIn_subset G v Y)
    _ = X.card * Y.card := by
      simp [sum_const]

lemma densityBetween_nonneg {V : Type*} (G : SimpleGraph V)
    (X Y : Finset V) :
    0 ≤ densityBetween G X Y := by
  rw [densityBetween]
  positivity

lemma densityBetween_le_one {V : Type*} (G : SimpleGraph V)
    (X Y : Finset V) :
    densityBetween G X Y ≤ 1 := by
  by_cases hX : X = ∅
  · subst X
    simp [densityBetween, redEdgesBetween]
  by_cases hY : Y = ∅
  · subst Y
    simp [densityBetween, redEdgesBetween]
  have hx : (0 : ℝ) < X.card := by
    exact_mod_cast card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hX)
  have hy : (0 : ℝ) < Y.card := by
    exact_mod_cast card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hY)
  rw [densityBetween, div_le_one (mul_pos hx hy)]
  exact_mod_cast redEdgesBetween_le_card_mul_card G X Y

lemma exists_ge_of_mul_sum_le_sum_mul {ι : Type*}
    (Z : Finset ι) (hZ : Z.Nonempty) (w : ι → ℝ) (f : ι → ℝ)
    (a : ℝ) (hw : ∀ z ∈ Z, 0 < w z)
    (havg : a * (∑ z ∈ Z, w z) ≤ ∑ z ∈ Z, f z * w z) :
    ∃ z ∈ Z, a ≤ f z := by
  by_contra hnone
  push Not at hnone
  have hlt :
      (∑ z ∈ Z, f z * w z) <
        ∑ z ∈ Z, a * w z := by
    exact sum_lt_sum_of_nonempty hZ fun z hz ↦
      mul_lt_mul_of_pos_right (hnone z hz) (hw z hz)
  rw [← mul_sum] at hlt
  exact (not_lt_of_ge havg) hlt

lemma sum_density_mul_redDegree_le {V : Type*} (G : SimpleGraph V)
    (X Y W : Finset V) :
    (∑ v ∈ W,
        densityBetween G X (redNeighborsIn G v Y) *
          (redNeighborsIn G v Y).card) ≤
      W.card * Y.card := by
  calc
    (∑ v ∈ W,
        densityBetween G X (redNeighborsIn G v Y) *
          (redNeighborsIn G v Y).card) ≤
        ∑ _v ∈ W, (Y.card : ℝ) := by
      apply sum_le_sum
      intro v hv
      have hd0 :
          0 ≤ densityBetween G X (redNeighborsIn G v Y) :=
        densityBetween_nonneg G X _
      have hd1 :
          densityBetween G X (redNeighborsIn G v Y) ≤ 1 :=
        densityBetween_le_one G X _
      have hcard :
          ((redNeighborsIn G v Y).card : ℝ) ≤ Y.card := by
        exact_mod_cast card_le_card (redNeighborsIn_subset G v Y)
      nlinarith [mul_le_mul hd1 hcard (by positivity)
        (by positivity : (0 : ℝ) ≤ 1)]
    _ = W.card * Y.card := by
      simp [sum_const]

/-- A cardinality bound on the exceptional set implies the weighted
contribution bound needed by `exists_density_preserving_pivot_outside`. -/
lemma Candidate.exceptional_density_sum_le {V : Type*}
    {G : SimpleGraph V} (C : Candidate G) (W : Finset V)
    (η q : ℝ) (hη : 0 ≤ η)
    (hdensity : q ≤ C.density)
    (hWcard : (W.card : ℝ) ≤ η * q * C.X.card) :
    (∑ v ∈ W,
        densityBetween G C.X (redNeighborsIn G v C.Y) *
          (redNeighborsIn G v C.Y).card) ≤
      η * redEdgesBetween G C.X C.Y := by
  have hy : (0 : ℝ) ≤ C.Y.card := by positivity
  have hx : (0 : ℝ) ≤ C.X.card := by positivity
  calc
    (∑ v ∈ W,
        densityBetween G C.X (redNeighborsIn G v C.Y) *
          (redNeighborsIn G v C.Y).card) ≤
        (W.card : ℝ) * C.Y.card :=
      sum_density_mul_redDegree_le G C.X C.Y W
    _ ≤ (η * q * C.X.card) * C.Y.card :=
      mul_le_mul_of_nonneg_right hWcard hy
    _ ≤ η * (C.density * ((C.X.card : ℝ) * C.Y.card)) := by
      have hqd :=
        mul_le_mul_of_nonneg_left hdensity hη
      nlinarith [mul_le_mul_of_nonneg_right hqd
        (mul_nonneg hx hy)]
    _ = η * redEdgesBetween G C.X C.Y := by
      rw [C.density_mul_card]

/-- Weighted pivot selection after removing an exceptional set `W`.
This is the averaging step leading to equation `e:alpha`. -/
lemma Candidate.exists_density_preserving_pivot_outside {V : Type*}
    [DecidableEq V]
    {G : SimpleGraph V} (C : Candidate G) (W : Finset V) (η : ℝ)
    (hWX : W ⊆ C.X) (hη0 : 0 ≤ η) (hη : 0 < C.density - η)
    (hW :
      (∑ v ∈ W,
          densityBetween G C.X (redNeighborsIn G v C.Y) *
            (redNeighborsIn G v C.Y).card) ≤
        η * redEdgesBetween G C.X C.Y)
    (hdeg : ∀ v ∈ C.X \ W,
      0 < (redNeighborsIn G v C.Y).card) :
    ∃ v ∈ C.X \ W,
      C.density - η ≤
        densityBetween G C.X (redNeighborsIn G v C.Y) := by
  classical
  let Z := C.X \ W
  let weight : V → ℝ :=
    fun v ↦ (redNeighborsIn G v C.Y).card
  let value : V → ℝ :=
    fun v ↦ densityBetween G C.X (redNeighborsIn G v C.Y)
  have htotal := density_averaging G C
  have hdisj : Disjoint W Z := by
    exact disjoint_sdiff
  have hunion : W ∪ Z = C.X := by
    exact union_sdiff_of_subset hWX
  have hsumSplit :
      (∑ v ∈ C.X, value v * weight v) =
        (∑ v ∈ W, value v * weight v) +
          ∑ v ∈ Z, value v * weight v := by
    rw [← hunion, sum_union hdisj]
  have hout :
      (redEdgesBetween G C.X C.Y : ℝ) * (C.density - η) ≤
        ∑ v ∈ Z, value v * weight v := by
    dsimp [value, weight] at hsumSplit ⊢
    rw [hsumSplit] at htotal
    nlinarith
  have hweightNat :
      (∑ v ∈ Z, (redNeighborsIn G v C.Y).card) ≤
        redEdgesBetween G C.X C.Y := by
    rw [← sum_card_redNeighborsIn G C.X C.Y]
    exact sum_le_sum_of_subset (sdiff_subset : Z ⊆ C.X)
  have hweight :
      (∑ v ∈ Z, weight v) ≤ redEdgesBetween G C.X C.Y := by
    dsimp [weight]
    exact_mod_cast hweightNat
  have havg :
      (C.density - η) * (∑ v ∈ Z, weight v) ≤
        ∑ v ∈ Z, value v * weight v := by
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left hweight hη.le).trans
        (by simpa [mul_comm] using hout)
  have hZ : Z.Nonempty := by
    have hEpos : (0 : ℝ) < redEdgesBetween G C.X C.Y := by
      have hd : 0 < C.density := by linarith
      have hx : (0 : ℝ) < C.X.card := by exact_mod_cast C.card_X_pos
      have hy : (0 : ℝ) < C.Y.card := by exact_mod_cast C.card_Y_pos
      rw [← C.density_mul_card]
      exact mul_pos hd (mul_pos hx hy)
    by_contra hZempty
    rw [Finset.not_nonempty_iff_eq_empty] at hZempty
    rw [hZempty] at hout
    simp only [sum_empty] at hout
    nlinarith [mul_pos hEpos hη]
  obtain ⟨v, hvZ, hv⟩ :=
    exists_ge_of_mul_sum_le_sum_mul Z hZ weight value
      (C.density - η) (by
        intro z hz
        dsimp [weight]
        exact_mod_cast hdeg z hz) havg
  exact ⟨v, hvZ, hv⟩

/-- Equation `e:moment2` before division by the central shifted density. -/
lemma density_partition_normalized_le {V : Type*} (G : SimpleGraph V)
    (p : ℝ) (hp : 0 ≤ p) {X : Finset V} {v : V} (hv : v ∈ X)
    (Y' : Finset V) (hY' : Y'.Nonempty) :
    (X.card : ℝ) * (densityBetween G X Y' - p) ≤
      ((redNeighborsIn G v X).card : ℝ) *
          (densityBetween G (redNeighborsIn G v X) Y' - p) +
        ((blueNeighborsIn G v X).card : ℝ) *
          (densityBetween G (blueNeighborsIn G v X) Y' - p) +
        1 := by
  have h :=
    density_partition_le G p hp hv Y'
  have hy : (0 : ℝ) < Y'.card := by exact_mod_cast hY'.card_pos
  apply le_of_mul_le_mul_right (a := (Y'.card : ℝ)) ?_ hy
  calc
    ((X.card : ℝ) * (densityBetween G X Y' - p)) * Y'.card =
        (X.card : ℝ) * Y'.card *
          (densityBetween G X Y' - p) := by ring
    _ ≤ ((redNeighborsIn G v X).card : ℝ) * Y'.card *
          (densityBetween G (redNeighborsIn G v X) Y' - p) +
        ((blueNeighborsIn G v X).card : ℝ) * Y'.card *
          (densityBetween G (blueNeighborsIn G v X) Y' - p) +
        Y'.card := h
    _ = (((redNeighborsIn G v X).card : ℝ) *
          (densityBetween G (redNeighborsIn G v X) Y' - p) +
        ((blueNeighborsIn G v X).card : ℝ) *
          (densityBetween G (blueNeighborsIn G v X) Y' - p) +
        1) * Y'.card := by ring

/-- Ratio form of equation `e:moment2`. -/
lemma density_partition_ratio_le {V : Type*} (G : SimpleGraph V)
    (p : ℝ) (hp : 0 ≤ p) {X : Finset V} {v : V} (hv : v ∈ X)
    (Y' : Finset V) (hY' : Y'.Nonempty)
    (hα : 0 < densityBetween G X Y' - p) :
    1 ≤
      ((densityBetween G (redNeighborsIn G v X) Y' - p) /
          (densityBetween G X Y' - p)) *
          ((redNeighborsIn G v X).card : ℝ) / X.card +
        ((densityBetween G (blueNeighborsIn G v X) Y' - p) /
          (densityBetween G X Y' - p)) *
          ((blueNeighborsIn G v X).card : ℝ) / X.card +
        1 / ((densityBetween G X Y' - p) * X.card) := by
  have hX : (0 : ℝ) < X.card := by
    exact_mod_cast card_pos.mpr ⟨v, hv⟩
  have h :=
    density_partition_normalized_le G p hp hv Y' hY'
  apply le_of_mul_le_mul_left
    (a := (densityBetween G X Y' - p) * X.card) ?_ (mul_pos hα hX)
  field_simp [ne_of_gt hα, ne_of_gt hX]
  nlinarith

lemma densityBetween_ge_of_pointwise_redDegree {V : Type*}
    (G : SimpleGraph V) (q : ℝ) (T Y : Finset V)
    (hT : T.Nonempty) (hY : Y.Nonempty)
    (hdeg : ∀ v ∈ T,
      q * Y.card ≤ (redNeighborsIn G v Y).card) :
    q ≤ densityBetween G T Y := by
  have hsum :
      ∑ v ∈ T, q * (Y.card : ℝ) ≤
        ∑ v ∈ T, ((redNeighborsIn G v Y).card : ℝ) :=
    sum_le_sum hdeg
  have hsum' :
      q * (T.card : ℝ) * Y.card ≤
        (redEdgesBetween G T Y : ℝ) := by
    rw [← sum_card_redNeighborsIn G T Y]
    simpa [sum_const, mul_comm, mul_left_comm, mul_assoc] using hsum
  have hden : (0 : ℝ) < T.card * Y.card := by
    have ht : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
    have hy : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
    positivity
  rw [densityBetween, le_div_iff₀ hden]
  simpa [mul_assoc] using hsum'

lemma isBlueBook_spine_containsBlueClique {V : Type*} (G : SimpleGraph V)
    {S T : Finset V} {t : ℕ} (hbook : IsBlueBook G S T)
    (ht : t ≤ S.card) :
    Candidate.ContainsBlueClique (G := G) S t := by
  classical
  obtain ⟨S', hS', hcard⟩ :
      ∃ S' : Finset V, S' ⊆ S ∧ S'.card = t := by
    obtain ⟨S', hS'⟩ := powersetCard_nonempty_of_le ht
    exact ⟨S', (mem_powersetCard.mp hS').1,
      (mem_powersetCard.mp hS').2⟩
  refine ⟨S', hS', ?_⟩
  rw [SimpleGraph.isNIndepSet_iff]
  exact ⟨hbook.1.mono (by
    intro v hv
    exact hS' hv), hcard⟩

/-- An interior point of the closed Ramsey region already satisfies an
eventual Ramsey bound.  The proof finds a defining-core point strictly
northeast of it and applies coordinate monotonicity. -/
lemma eventuallyRamseyBound_of_mem_interior {x y : ℝ}
    (hxy : (x, y) ∈ ramseyRegionInterior)
    (hx : 0 < x) (hy : 0 < y) :
    EventuallyRamseyBound x y := by
  have hnhds : ramseyRegion ∈ nhds (x, y) := by
    exact (mem_interior_iff_mem_nhds.mp hxy)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let z : ℝ × ℝ := (x + ε / 2, y + ε / 2)
  have hzdist : dist z (x, y) < ε := by
    rw [Prod.dist_eq]
    dsimp [z]
    simp only [Real.dist_eq]
    have habsx : |x + ε / 2 - x| = ε / 2 := by
      rw [show x + ε / 2 - x = ε / 2 by ring, abs_of_pos (half_pos hε)]
    have habsy : |y + ε / 2 - y| = ε / 2 := by
      rw [show y + ε / 2 - y = ε / 2 by ring, abs_of_pos (half_pos hε)]
    rw [habsx, habsy, max_self]
    linarith
  have hz : z ∈ ramseyRegion :=
    hball (by simpa [Metric.mem_ball] using hzdist)
  have hzclosure : z ∈ closure ramseyBoundCore := hz
  have hopen : IsOpen (Metric.ball z (ε / 4)) := Metric.isOpen_ball
  have hzopen : z ∈ Metric.ball z (ε / 4) := by
    simp [Metric.mem_ball, hε]
  obtain ⟨w, hwball, hwcore⟩ :=
    (mem_closure_iff.mp hzclosure) (Metric.ball z (ε / 4))
      hopen hzopen
  have hwdist : dist w z < ε / 4 :=
    (Metric.mem_ball.mp hwball)
  have hcoords : x < w.1 ∧ y < w.2 := by
    rw [Prod.dist_eq, max_lt_iff] at hwdist
    have hwx := hwdist.1
    have hwy := hwdist.2
    rw [Real.dist_eq] at hwx hwy
    have hwx' := (abs_lt.mp hwx).1
    have hwy' := (abs_lt.mp hwy).1
    dsimp [z] at hwx' hwy'
    constructor <;> linarith
  exact eventuallyRamseyBound_mono hx.le hcoords.1.le hy.le hcoords.2.le
    hwcore.2.2.2.2

lemma ramseyNumber_le_inv_pow_of_eventuallyRamseyBound {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (h : EventuallyRamseyBound x y)
    {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hlarge : h.choose ≤ k + l) :
    (ramseyNumber k l : ℝ) ≤ x⁻¹ ^ k * y⁻¹ ^ l := by
  have hbound := h.choose_spec k l hk hl hlarge
  have hxy : 0 < x ^ k * y ^ l := mul_pos (pow_pos hx _) (pow_pos hy _)
  have hinv :
      x⁻¹ ^ k * y⁻¹ ^ l = 1 / (x ^ k * y ^ l) := by
    simp only [one_div, mul_inv, inv_pow]
  rw [hinv]
  apply (le_div_iff₀ hxy).2
  simpa [mul_assoc] using hbound

lemma Candidate.good_of_eventualRamseyBound_right {V : Type*}
    {G : SimpleGraph V} (C : Candidate G) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (h : EventuallyRamseyBound x y)
    {k l t : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hlarge : h.choose ≤ k + l)
    (hY : x⁻¹ ^ k * y⁻¹ ^ l ≤ C.Y.card) :
    C.Good k l t := by
  have hR :
      (ramseyNumber k l : ℝ) ≤ C.Y.card :=
    (ramseyNumber_le_inv_pow_of_eventuallyRamseyBound
      hx hy h hk hl hlarge).trans hY
  exact C.good_of_ramsey_right (by exact_mod_cast hR)

/-- The exponential weight on the right side of equation `e:moment`. -/
def bookWeight (x y μ : ℝ) (k l t : ℕ) : ℝ :=
  x⁻¹ ^ k * y⁻¹ ^ l * μ⁻¹ ^ t

/-- The moment invariant in equation `e:moment`. -/
def HasBookMoment {V : Type*} {G : SimpleGraph V} (C : Candidate G)
    (x y μ p ε : ℝ) (r k l t : ℕ) : Prop :=
  bookWeight x y μ k l t ≤
    (C.density + ε / (k + t : ℕ) - p) ^ r *
      C.X.card * C.Y.card

lemma bookWeight_pos {x y μ : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hμ : 0 < μ) (k l t : ℕ) :
    0 < bookWeight x y μ k l t := by
  simp only [bookWeight]
  positivity

lemma bookWeight_red_scale {x y μ : ℝ} (hx : x ≠ 0)
    {k l t : ℕ} (hk : 1 ≤ k) :
    bookWeight x y μ (k - 1) l t =
      x * bookWeight x y μ k l t := by
  simp only [bookWeight]
  have hkpow : x⁻¹ ^ k = x⁻¹ ^ (k - 1) * x⁻¹ := by
    conv_lhs =>
      rw [show k = (k - 1) + 1 by omega, pow_succ]
  rw [hkpow]
  field_simp

lemma bookWeight_blue_scale {x y μ : ℝ} (hμ : μ ≠ 0)
    {k l t b : ℕ} (hbt : b ≤ t) :
    bookWeight x y μ k l (t - b) =
      μ ^ b * bookWeight x y μ k l t := by
  simp only [bookWeight]
  conv_rhs =>
    rw [show t = (t - b) + b by omega, pow_add]
  have hcancel : μ ^ b * μ⁻¹ ^ b = 1 := by
    rw [← mul_pow]
    simp [hμ]
  symm
  calc
    μ ^ b *
        (x⁻¹ ^ k * y⁻¹ ^ l *
          (μ⁻¹ ^ (t - b) * μ⁻¹ ^ b)) =
        (x⁻¹ ^ k * y⁻¹ ^ l * μ⁻¹ ^ (t - b)) *
          (μ ^ b * μ⁻¹ ^ b) := by ring
    _ = x⁻¹ ^ k * y⁻¹ ^ l * μ⁻¹ ^ (t - b) := by
      rw [hcancel]
      ring

lemma mul_inv_pow_le_inv_pow_of_le_div {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a ≤ b / c)
    (n : ℕ) :
    c ^ n * b⁻¹ ^ n ≤ a⁻¹ ^ n := by
  have hcross : a * c ≤ b := (le_div_iff₀ hc).mp h
  have hdiv : c / b ≤ 1 / a := by
    apply (div_le_div_iff₀ hb ha).2
    simpa [mul_comm] using hcross
  have hpow := pow_le_pow_left₀ (div_nonneg hc.le hb.le) hdiv n
  simpa [div_eq_mul_inv, mul_pow] using hpow

lemma bookWeight_scale {x₀ y₀ μ₀ x y μ c : ℝ}
    (hx₀ : 0 < x₀) (hy₀ : 0 < y₀) (hμ₀ : 0 < μ₀)
    (hx : 0 < x) (hy : 0 < y) (hμ : 0 < μ) (hc : 0 < c)
    (hxc : x₀ ≤ x / c) (hyc : y₀ ≤ y / c) (hμc : μ₀ ≤ μ / c)
    (k l t : ℕ) :
    c ^ (k + l + t) * bookWeight x y μ k l t ≤
      bookWeight x₀ y₀ μ₀ k l t := by
  have hk :=
    mul_inv_pow_le_inv_pow_of_le_div hx₀ hx hc hxc k
  have hl :=
    mul_inv_pow_le_inv_pow_of_le_div hy₀ hy hc hyc l
  have ht :=
    mul_inv_pow_le_inv_pow_of_le_div hμ₀ hμ hc hμc t
  have hkl :
      (c ^ k * x⁻¹ ^ k) * (c ^ l * y⁻¹ ^ l) ≤
        x₀⁻¹ ^ k * y₀⁻¹ ^ l :=
    mul_le_mul hk hl (by positivity) (by positivity)
  have hklt :
      ((c ^ k * x⁻¹ ^ k) * (c ^ l * y⁻¹ ^ l)) *
          (c ^ t * μ⁻¹ ^ t) ≤
        (x₀⁻¹ ^ k * y₀⁻¹ ^ l) * μ₀⁻¹ ^ t :=
    mul_le_mul hkl ht (by positivity) (by positivity)
  simpa only [bookWeight, pow_add] using (show
    c ^ (k + l + t) * (x⁻¹ ^ k * y⁻¹ ^ l * μ⁻¹ ^ t) ≤
      x₀⁻¹ ^ k * y₀⁻¹ ^ l * μ₀⁻¹ ^ t by
        calc
          c ^ (k + l + t) *
              (x⁻¹ ^ k * y⁻¹ ^ l * μ⁻¹ ^ t) =
              ((c ^ k * x⁻¹ ^ k) * (c ^ l * y⁻¹ ^ l)) *
                (c ^ t * μ⁻¹ ^ t) := by
            rw [pow_add, pow_add]
            ring
          _ ≤ _ := hklt)

lemma HasBookMoment.shift_pos {V : Type*} {G : SimpleGraph V}
    {C : Candidate G} {x y μ p ε : ℝ} {r k l t : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hμ : 0 < μ) (hr : r ≠ 0)
    (hbase : 0 ≤ C.density + ε / (k + t : ℕ) - p)
    (h : HasBookMoment C x y μ p ε r k l t) :
    0 < C.density + ε / (k + t : ℕ) - p := by
  have hw := bookWeight_pos hx hy hμ k l t
  have hprod :
      0 < (C.density + ε / (k + t : ℕ) - p) ^ r *
        C.X.card * C.Y.card :=
    hw.trans_le h
  have hpow :
      0 < (C.density + ε / (k + t : ℕ) - p) ^ r := by
    by_contra hn
    have hpowle : (C.density + ε / (k + t : ℕ) - p) ^ r ≤ 0 :=
      le_of_not_gt hn
    have hxcard : (0 : ℝ) ≤ C.X.card := by positivity
    have hycard : (0 : ℝ) ≤ C.Y.card := by positivity
    have hnonpos :
        (C.density + ε / (k + t : ℕ) - p) ^ r *
            C.X.card * C.Y.card ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hpowle hxcard) hycard
    exact (not_lt_of_ge hnonpos) hprod
  have hne :
      C.density + ε / (k + t : ℕ) - p ≠ 0 :=
    fun hz ↦ by
      have hzpow :
          (C.density + ε / (k + t : ℕ) - p) ^ r = 0 := by
        rw [hz, zero_pow hr]
      exact (ne_of_gt hpow) hzpow
  exact lt_of_le_of_ne hbase (Ne.symm hne)

/-- Equation `e:moment0`, with the eventual exponential domination and
parameter-rescaling estimates exposed as hypotheses. -/
lemma initial_hasBookMoment {V : Type*} {G : SimpleGraph V}
    (C : Candidate G) (x₀ y₀ μ₀ x y μ p ε : ℝ)
    (r k l t : ℕ) (hn : k + t ≠ 0)
    (hx : 0 < x) (hy : 0 < y) (hμ : 0 < μ)
    (hε : 0 ≤ ε)
    (hdensity : p ≤ C.density)
    (hsize :
      bookWeight x₀ y₀ μ₀ k l t ≤
        (C.X.card : ℝ) * C.Y.card)
    (hscale :
      (1 + ε) ^ (k + l + t) * bookWeight x y μ k l t ≤
        bookWeight x₀ y₀ μ₀ k l t)
    (hdom :
      1 ≤ (ε / (k + t : ℕ)) ^ r * (1 + ε) ^ (k + l + t)) :
    HasBookMoment C x y μ p ε r k l t := by
  have hshift :
      ε / (k + t : ℕ) ≤ C.density + ε / (k + t : ℕ) - p := by
    linarith
  have hnpos : (0 : ℝ) < (k + t : ℕ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hbase0 : 0 ≤ ε / (k + t : ℕ) :=
    div_nonneg hε hnpos.le
  have hpow :=
    pow_le_pow_left₀ hbase0 hshift r
  have hcards : 0 ≤ (C.X.card : ℝ) * C.Y.card := by positivity
  have hsize' :
      bookWeight x₀ y₀ μ₀ k l t ≤
        (C.X.card : ℝ) * C.Y.card := hsize
  calc
    bookWeight x y μ k l t ≤
        ((ε / (k + t : ℕ)) ^ r * (1 + ε) ^ (k + l + t)) *
          bookWeight x y μ k l t := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hdom
          (bookWeight_pos hx hy hμ k l t).le
    _ ≤ (ε / (k + t : ℕ)) ^ r *
          bookWeight x₀ y₀ μ₀ k l t := by
      have hp0 : 0 ≤ (ε / (k + t : ℕ)) ^ r := by positivity
      calc
        ((ε / (k + t : ℕ)) ^ r * (1 + ε) ^ (k + l + t)) *
            bookWeight x y μ k l t =
            (ε / (k + t : ℕ)) ^ r *
              ((1 + ε) ^ (k + l + t) *
                bookWeight x y μ k l t) := by ring
        _ ≤ (ε / (k + t : ℕ)) ^ r *
            bookWeight x₀ y₀ μ₀ k l t :=
          mul_le_mul_of_nonneg_left hscale hp0
    _ ≤ (ε / (k + t : ℕ)) ^ r *
          ((C.X.card : ℝ) * C.Y.card) := by
      exact mul_le_mul_of_nonneg_left hsize' (by positivity)
    _ ≤ (C.density + ε / (k + t : ℕ) - p) ^ r *
          ((C.X.card : ℝ) * C.Y.card) :=
      mul_le_mul_of_nonneg_right hpow hcards
    _ = (C.density + ε / (k + t : ℕ) - p) ^ r *
          C.X.card * C.Y.card := by ring

/-- Common arithmetic for the red and blue moment branches. -/
lemma transfer_moment_of_branch
    (α β γ c q X X' Y Y' : ℝ) (r : ℕ)
    (hβ : 0 ≤ β) (hβα : β ≤ α) (hc : 0 ≤ c)
    (hq : 0 < q) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hY' : 0 ≤ Y')
    (hYratio : q * Y ≤ Y')
    (hbranch : c * α ^ r * X / q ≤ γ ^ r * X') :
    c * (β ^ r * X * Y) ≤ γ ^ r * X' * Y' := by
  have hα : 0 ≤ α := hβ.trans hβα
  have hpow : β ^ r ≤ α ^ r :=
    pow_le_pow_left₀ hβ hβα r
  have hleft0 : 0 ≤ c * α ^ r * X := by positivity
  have hYdiv : Y ≤ Y' / q := by
    exact (le_div_iff₀ hq).2 (by simpa [mul_comm] using hYratio)
  calc
    c * (β ^ r * X * Y) ≤ c * (α ^ r * X * Y) := by
      gcongr
    _ = (c * α ^ r * X) * Y := by ring
    _ ≤ (c * α ^ r * X) * (Y' / q) :=
      mul_le_mul_of_nonneg_left hYdiv hleft0
    _ = (c * α ^ r * X / q) * Y' := by
      field_simp
    _ ≤ (γ ^ r * X') * Y' :=
      mul_le_mul_of_nonneg_right hbranch hY'
    _ = γ ^ r * X' * Y' := rfl

/-- Equation `e:x`: below the right-side Ramsey threshold, the moment
invariant forces exponential growth of the left side. -/
lemma one_add_eps_pow_lt_card_X_of_moment {V : Type*}
    {G : SimpleGraph V} (C : Candidate G)
    (x y μ p ε : ℝ) (r k l t : ℕ)
    (hx : 0 < x) (hy : 0 < y) (hμ : 0 < μ)
    (hx1 : x ≤ 1) (hy1 : y ≤ 1) (hε : 0 ≤ ε)
    (hμscale : (1 + ε) * μ ≤ 1)
    (hshift0 : 0 ≤ C.density + ε / (k + t : ℕ) - p)
    (hshift1 : C.density + ε / (k + t : ℕ) - p ≤ 1)
    (hmoment : HasBookMoment C x y μ p ε r k l t)
    (hY :
      (C.Y.card : ℝ) <
        (x + ε)⁻¹ ^ k * (y + ε)⁻¹ ^ l) :
    (1 + ε) ^ (k + l + t) < C.X.card := by
  let R : ℝ :=
    ((x + ε) / x) ^ k * ((y + ε) / y) ^ l * μ⁻¹ ^ t
  let A : ℝ := (x + ε)⁻¹ ^ k * (y + ε)⁻¹ ^ l
  have hxe : 0 < x + ε := by linarith
  have hye : 0 < y + ε := by linarith
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hpow :
      (C.density + ε / (k + t : ℕ) - p) ^ r ≤ 1 :=
    pow_le_one₀ hshift0 hshift1
  have hcards : 0 ≤ (C.X.card : ℝ) * C.Y.card := by positivity
  have hweightXY :
      bookWeight x y μ k l t ≤
        (C.X.card : ℝ) * C.Y.card := by
    calc
      bookWeight x y μ k l t ≤
          (C.density + ε / (k + t : ℕ) - p) ^ r *
            C.X.card * C.Y.card := hmoment
      _ ≤ 1 * ((C.X.card : ℝ) * C.Y.card) := by
        nlinarith [mul_le_mul_of_nonneg_right hpow hcards]
      _ = (C.X.card : ℝ) * C.Y.card := one_mul _
  have hxid :
      ((x + ε) / x) ^ k * (x + ε)⁻¹ ^ k = x⁻¹ ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hyid :
      ((y + ε) / y) ^ l * (y + ε)⁻¹ ^ l = y⁻¹ ^ l := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hRA : R * A = bookWeight x y μ k l t := by
    dsimp [R, A, bookWeight]
    rw [show ((x + ε) / x) ^ k * ((y + ε) / y) ^ l *
        μ⁻¹ ^ t * ((x + ε)⁻¹ ^ k * (y + ε)⁻¹ ^ l) =
      (((x + ε) / x) ^ k * (x + ε)⁻¹ ^ k) *
        (((y + ε) / y) ^ l * (y + ε)⁻¹ ^ l) * μ⁻¹ ^ t by ring,
      hxid, hyid]
  have hRX : R < C.X.card := by
    by_contra hnot
    have hXle : (C.X.card : ℝ) ≤ R := le_of_not_gt hnot
    have hXYlt :
        (C.X.card : ℝ) * C.Y.card < R * A := by
      calc
        (C.X.card : ℝ) * C.Y.card ≤ R * C.Y.card :=
          mul_le_mul_of_nonneg_right hXle (by positivity)
        _ < R * A :=
          mul_lt_mul_of_pos_left (by simpa [A] using hY) hR
    rw [hRA] at hXYlt
    exact (not_lt_of_ge hweightXY) hXYlt
  have hcx : 1 + ε ≤ (x + ε) / x := by
    apply (le_div_iff₀ hx).2
    nlinarith
  have hcy : 1 + ε ≤ (y + ε) / y := by
    apply (le_div_iff₀ hy).2
    nlinarith
  have hcμ : 1 + ε ≤ μ⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hμ).2 hμscale
  have hc0 : 0 ≤ 1 + ε := by linarith
  have hkpow :
      (1 + ε) ^ k ≤ ((x + ε) / x) ^ k :=
    pow_le_pow_left₀ hc0 hcx k
  have hlpow :
      (1 + ε) ^ l ≤ ((y + ε) / y) ^ l :=
    pow_le_pow_left₀ hc0 hcy l
  have htpow :
      (1 + ε) ^ t ≤ μ⁻¹ ^ t :=
    pow_le_pow_left₀ hc0 hcμ t
  have hkl :
      (1 + ε) ^ k * (1 + ε) ^ l ≤
        ((x + ε) / x) ^ k * ((y + ε) / y) ^ l :=
    mul_le_mul hkpow hlpow (by positivity) (by positivity)
  have hklt :
      ((1 + ε) ^ k * (1 + ε) ^ l) * (1 + ε) ^ t ≤ R := by
    dsimp [R]
    exact mul_le_mul hkl htpow (by positivity) (by positivity)
  have hgrowth :
      (1 + ε) ^ (k + l + t) ≤ R := by
    rw [pow_add, pow_add]
    exact hklt
  exact hgrowth.trans_lt hRX

/-- The exact amplification target used to choose the blue-book spine. -/
def bookAmplificationTarget (ε : ℝ) (r n : ℕ) : ℝ :=
  2 * (((n : ℝ) ^ 2 / ε) ^ r)

/-- The spine parameter from `t:bookmain`, in an algebraically equivalent
logarithmic form. -/
def bookSpineSize (ε : ℝ) (r n : ℕ) : ℕ :=
  ⌈Real.log (bookAmplificationTarget ε r n) / Real.log (1 + ε)⌉₊

/-- The auxiliary blue-clique parameter from `t:bookmain`. -/
def bookCliqueSize (μ ε : ℝ) (r n : ℕ) : ℕ :=
  ⌈5 * (μ + ε)⁻¹ * (bookSpineSize ε r n : ℝ) ^ 2⌉₊

lemma bookAmplificationTarget_gt_one {ε : ℝ} {r n : ℕ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) :
    1 < bookAmplificationTarget ε r n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnSq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hratio : (1 : ℝ) ≤ (n : ℝ) ^ 2 / ε := by
    apply (le_div_iff₀ hε).2
    simpa using hε1.trans hnSq
  have hpow : (1 : ℝ) ≤ (((n : ℝ) ^ 2 / ε) ^ r) :=
    one_le_pow₀ hratio
  dsimp [bookAmplificationTarget]
  nlinarith

lemma bookSpineSize_pos {ε : ℝ} {r n : ℕ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) :
    0 < bookSpineSize ε r n := by
  apply Nat.ceil_pos.mpr
  exact div_pos
    (Real.log_pos (bookAmplificationTarget_gt_one hε hε1 hn))
    (Real.log_pos (by linarith : 1 < 1 + ε))

lemma bookAmplificationTarget_le_pow {ε : ℝ} {r n : ℕ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) :
    bookAmplificationTarget ε r n ≤
      (1 + ε) ^ bookSpineSize ε r n := by
  let B := bookAmplificationTarget ε r n
  let c := 1 + ε
  have hB : 0 < B := by
    dsimp [B]
    exact zero_lt_one.trans
      (bookAmplificationTarget_gt_one hε hε1 hn)
  have hc : 0 < c := by dsimp [c]; linarith
  have hlogc : 0 < Real.log c := by
    exact Real.log_pos (by dsimp [c]; linarith)
  have hceil :
      Real.log B / Real.log c ≤
        (bookSpineSize ε r n : ℝ) := by
    exact Nat.le_ceil _
  have hlog :
      Real.log B ≤ (bookSpineSize ε r n : ℝ) * Real.log c := by
    calc
      Real.log B =
          (Real.log B / Real.log c) * Real.log c := by
        field_simp
      _ ≤ (bookSpineSize ε r n : ℝ) * Real.log c :=
        mul_le_mul_of_nonneg_right hceil hlogc.le
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hB, Real.exp_nat_mul, Real.exp_log hc] at hexp
  simpa [B, c, mul_comm] using hexp

lemma bookCliqueSize_bound (μ ε : ℝ) (r n : ℕ) :
    5 * (μ + ε)⁻¹ * (bookSpineSize ε r n : ℝ) ^ 2 ≤
      bookCliqueSize μ ε r n := by
  exact Nat.le_ceil _

lemma blueBook_moment_amplification {μ ε : ℝ} {r n : ℕ}
    (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) :
    μ ^ bookSpineSize ε r n ≤
      (ε / (n : ℝ) ^ 2) ^ r *
        ((μ + ε) ^ bookSpineSize ε r n / 2) := by
  let b := bookSpineSize ε r n
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hμe : 0 < μ + ε := by positivity
  have hc : (0 : ℝ) ≤ 1 + ε := by positivity
  have hratio :
      1 + ε ≤ (μ + ε) / μ := by
    apply (le_div_iff₀ hμ).2
    nlinarith
  have hratioPow :
      (1 + ε) ^ b ≤ ((μ + ε) / μ) ^ b :=
    pow_le_pow_left₀ hc hratio b
  have hmain :
      2 * (((n : ℝ) ^ 2 / ε) ^ r) ≤
        ((μ + ε) / μ) ^ b := by
    exact (bookAmplificationTarget_le_pow hε hε1 hn).trans hratioPow
  have hnCancel :
      (((n : ℝ) ^ 2 / ε) ^ r) *
          ((ε / (n : ℝ) ^ 2) ^ r) = 1 := by
    rw [← mul_pow]
    have : (n : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hnR)
    field_simp
    simp
  have hμCancel :
      (((μ + ε) / μ) ^ b) * μ ^ b = (μ + ε) ^ b := by
    rw [← mul_pow]
    field_simp
  have hfactor :
      0 ≤ (ε / (n : ℝ) ^ 2) ^ r * μ ^ b / 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hmain hfactor
  calc
    μ ^ b =
        (2 * (((n : ℝ) ^ 2 / ε) ^ r)) *
          ((ε / (n : ℝ) ^ 2) ^ r * μ ^ b / 2) := by
      rw [show (2 : ℝ) * (((n : ℝ) ^ 2 / ε) ^ r) *
          ((ε / (n : ℝ) ^ 2) ^ r * μ ^ b / 2) =
        ((((n : ℝ) ^ 2 / ε) ^ r) *
          ((ε / (n : ℝ) ^ 2) ^ r)) * μ ^ b by ring,
        hnCancel]
      ring
    _ ≤ (((μ + ε) / μ) ^ b) *
          ((ε / (n : ℝ) ^ 2) ^ r * μ ^ b / 2) := hscaled
    _ = (ε / (n : ℝ) ^ 2) ^ r * ((μ + ε) ^ b / 2) := by
      calc
        (((μ + ε) / μ) ^ b) *
            ((ε / (n : ℝ) ^ 2) ^ r * μ ^ b / 2) =
            (ε / (n : ℝ) ^ 2) ^ r *
              ((((μ + ε) / μ) ^ b * μ ^ b) / 2) := by ring
        _ = (ε / (n : ℝ) ^ 2) ^ r * ((μ + ε) ^ b / 2) := by
          rw [hμCancel]

/-- Monotonicity calculation used between equations `e:moment3` and
`e:moment4`. -/
lemma bookMomentProfile_monotoneOn {x μ L : ℝ} {r : ℕ}
    (hx : 0 < x) (hμ : 0 < μ) (hr : 2 ≤ r)
    (hL1 : L < 1)
    (hLcrit : L ≤ μ / (μ + x)) :
    MonotoneOn
      (fun z : ℝ ↦
        x ^ ((r : ℝ)⁻¹) * (1 - z) ^ (1 - (r : ℝ)⁻¹) +
          μ ^ ((r : ℝ)⁻¹) * z ^ (1 - (r : ℝ)⁻¹))
      (Set.Icc 0 L) := by
  let s : ℝ := (r : ℝ)⁻¹
  let a : ℝ := 1 - s
  let f : ℝ → ℝ :=
    (fun z ↦ x ^ s * (1 - z) ^ a) + (fun z ↦ μ ^ s * z ^ a)
  have hrR : (1 : ℝ) < r := by exact_mod_cast hr
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hs1 : s < 1 := by
    dsimp [s]
    exact inv_lt_one_of_one_lt₀ hrR
  have ha : 0 < a := by dsimp [a]; linarith
  have hfcont : ContinuousOn f (Set.Icc 0 L) := by
    dsimp [f]
    apply ContinuousOn.add
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.rpow_const
        (continuousOn_const.sub continuousOn_id)
      intro z hz
      exact Or.inr ha.le
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.rpow_const continuousOn_id
      intro z hz
      exact Or.inr ha.le
  have hfhasderiv :
      ∀ z ∈ interior (Set.Icc 0 L),
        HasDerivAt f
          (a * (μ ^ s * z ^ (a - 1) -
            x ^ s * (1 - z) ^ (a - 1))) z := by
    intro z hz
    rw [interior_Icc] at hz
    have hz0 : 0 < z := hz.1
    have hz1 : z < 1 := hz.2.trans hL1
    have honez : 0 < 1 - z := sub_pos.mpr hz1
    have hleft :=
      (((hasDerivAt_const z (1 : ℝ)).sub (hasDerivAt_id z)).rpow_const
        (p := a) (Or.inl (ne_of_gt honez))).const_mul (x ^ s)
    have hright :=
      ((hasDerivAt_id z).rpow_const
        (p := a) (Or.inl (ne_of_gt hz0))).const_mul (μ ^ s)
    have hleft' :
        HasDerivAt (fun y : ℝ ↦ x ^ s * (1 - y) ^ a)
          (x ^ s * ((0 - 1) * a * (1 - z) ^ (a - 1))) z := by
      simpa only [Pi.sub_apply, id_eq] using hleft
    have hright' :
        HasDerivAt (fun y : ℝ ↦ μ ^ s * y ^ a)
          (μ ^ s * (1 * a * z ^ (a - 1))) z := by
      simpa only [id_eq] using hright
    have hd :
        HasDerivAt f
          (x ^ s * ((0 - 1) * a * (1 - z) ^ (a - 1)) +
            μ ^ s * (1 * a * z ^ (a - 1))) z := by
      exact hleft'.add hright'
    exact hd.congr_deriv (by ring)
  have hfdiff : DifferentiableOn ℝ f (interior (Set.Icc 0 L)) := by
    intro z hz
    exact (hfhasderiv z hz).differentiableAt.differentiableWithinAt
  have hfderiv : ∀ z ∈ interior (Set.Icc 0 L), 0 ≤ deriv f z := by
    intro z hz
    rw [interior_Icc] at hz
    have hz0 : 0 < z := hz.1
    have hz1 : z < 1 := hz.2.trans hL1
    have honez : 0 < 1 - z := sub_pos.mpr hz1
    have hzcrit : z ≤ μ / (μ + x) := hz.2.le.trans hLcrit
    have hcross : x * z ≤ μ * (1 - z) := by
      have hsum : 0 < μ + x := by positivity
      have := (le_div_iff₀ hsum).mp hzcrit
      nlinarith
    have hfrac : x / (1 - z) ≤ μ / z := by
      exact (div_le_div_iff₀ honez hz0).2 hcross
    have hratio :
        (x / (1 - z)) ^ s ≤ (μ / z) ^ s :=
      Real.rpow_le_rpow (div_nonneg hx.le honez.le) hfrac hs.le
    have hxrewrite :
        x ^ s * (1 - z) ^ (a - 1) =
          (x / (1 - z)) ^ s := by
      have ha1 : a - 1 = -s := by dsimp [a]; ring
      rw [ha1, Real.div_rpow hx.le honez.le,
        Real.rpow_neg honez.le]
      simp [div_eq_mul_inv]
    have hμrewrite :
        μ ^ s * z ^ (a - 1) = (μ / z) ^ s := by
      have ha1 : a - 1 = -s := by dsimp [a]; ring
      rw [ha1, Real.div_rpow hμ.le hz0.le,
        Real.rpow_neg hz0.le]
      simp [div_eq_mul_inv]
    have hbracket :
        0 ≤ μ ^ s * z ^ (a - 1) -
          x ^ s * (1 - z) ^ (a - 1) := by
      rw [hxrewrite, hμrewrite]
      linarith
    rw [(hfhasderiv z (by simpa [interior_Icc] using hz)).deriv]
    nlinarith [mul_nonneg ha.le hbracket]
  have hmono :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 L) hfcont hfdiff hfderiv
  intro u hu v hv huv
  simpa [f, s, a] using hmono hu hv huv

/-- The endpoint estimate in equation `e:moment4`.  The second summand is
bounded by `μ + ε` using weighted geometric monotonicity. -/
lemma bookMomentProfile_le {x μ ε z : ℝ} {r : ℕ}
    (hx : 0 < x) (hμ : 0 < μ) (hε : 0 < ε) (hr : 2 ≤ r)
    (hμe1 : μ + ε < 1)
    (hcrit : μ + ε ≤ μ / (μ + x))
    (hz0 : 0 ≤ z) (hz : z ≤ μ + ε) :
    x ^ ((r : ℝ)⁻¹) * (1 - z) ^ (1 - (r : ℝ)⁻¹) +
        μ ^ ((r : ℝ)⁻¹) * z ^ (1 - (r : ℝ)⁻¹) ≤
      x ^ ((r : ℝ)⁻¹) * (1 - μ) ^ (1 - (r : ℝ)⁻¹) +
        μ + ε := by
  let s : ℝ := (r : ℝ)⁻¹
  let a : ℝ := 1 - s
  let L : ℝ := μ + ε
  have hrR : (1 : ℝ) < r := by exact_mod_cast hr
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hs1 : s < 1 := by
    dsimp [s]
    exact inv_lt_one_of_one_lt₀ hrR
  have ha : 0 < a := by dsimp [a]; linarith
  have hL : 0 < L := by dsimp [L]; positivity
  have hμL : μ ≤ L := by dsimp [L]; linarith
  have hmono := bookMomentProfile_monotoneOn
    (x := x) (μ := μ) (L := L) (r := r)
    hx hμ hr (by simpa [L] using hμe1) (by simpa [L] using hcrit)
  have htoL :
      x ^ s * (1 - z) ^ a + μ ^ s * z ^ a ≤
        x ^ s * (1 - L) ^ a + μ ^ s * L ^ a := by
    exact hmono (by simpa [L] using And.intro hz0 hz)
      ⟨hL.le, le_rfl⟩ (by simpa [L] using hz)
  have hbase0 : 0 ≤ 1 - L := by
    dsimp [L]
    linarith
  have hbasele : 1 - L ≤ 1 - μ := by
    dsimp [L]
    linarith
  have hfirst :
      x ^ s * (1 - L) ^ a ≤ x ^ s * (1 - μ) ^ a := by
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hbase0 hbasele ha.le)
      (Real.rpow_nonneg hx.le s)
  have hpowμ : μ ^ s ≤ L ^ s :=
    Real.rpow_le_rpow hμ.le hμL hs.le
  have hsecond : μ ^ s * L ^ a ≤ L := by
    calc
      μ ^ s * L ^ a ≤ L ^ s * L ^ a :=
        mul_le_mul_of_nonneg_right hpowμ (Real.rpow_nonneg hL.le a)
      _ = L := by
        rw [← Real.rpow_add hL]
        have hsa : s + a = 1 := by dsimp [a]; ring
        rw [hsa, Real.rpow_one]
  calc
    x ^ ((r : ℝ)⁻¹) * (1 - z) ^ (1 - (r : ℝ)⁻¹) +
          μ ^ ((r : ℝ)⁻¹) * z ^ (1 - (r : ℝ)⁻¹) =
        x ^ s * (1 - z) ^ a + μ ^ s * z ^ a := by rfl
    _ ≤ x ^ s * (1 - L) ^ a + μ ^ s * L ^ a := htoL
    _ ≤ x ^ s * (1 - μ) ^ a + L := add_le_add hfirst hsecond
    _ = x ^ ((r : ℝ)⁻¹) * (1 - μ) ^ (1 - (r : ℝ)⁻¹) +
          μ + ε := by dsimp [s, a, L]; ring

/-- The final contradiction between `e:moment3`, the small error term, and
the parameter inequality `e:xx`. -/
lemma bookMoment_terminal_contradiction
    {x μ ε q z e : ℝ} {r : ℕ}
    (hx : 0 < x) (hμ : 0 < μ) (hε : 0 < ε)
    (hr : 2 ≤ r) (hμe1 : μ + ε < 1)
    (hcrit : μ + ε ≤ μ / (μ + x))
    (hz0 : 0 ≤ z) (hz : z ≤ μ + ε)
    (he : e ≤ ε)
    (hbase : 0 < q ^ ((r : ℝ)⁻¹) - μ - 2 * ε)
    (hparameter :
      x ≤ (q ^ ((r : ℝ)⁻¹) - μ - 2 * ε) ^ (r : ℝ) *
        (1 - μ) ^ (1 - (r : ℝ)))
    (hmoment :
      q ^ ((r : ℝ)⁻¹) <
        x ^ ((r : ℝ)⁻¹) * (1 - z) ^ (1 - (r : ℝ)⁻¹) +
          μ ^ ((r : ℝ)⁻¹) * z ^ (1 - (r : ℝ)⁻¹) + e) :
    False := by
  let s : ℝ := (r : ℝ)⁻¹
  let a : ℝ := 1 - s
  let B : ℝ := q ^ s - μ - 2 * ε
  let D : ℝ := 1 - μ
  have hrR : 0 < (r : ℝ) := by positivity
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hD : 0 < D := by
    dsimp [D]
    linarith
  have hprofile := bookMomentProfile_le
    (x := x) (μ := μ) (ε := ε) (z := z) (r := r)
    hx hμ hε hr hμe1 hcrit hz0 hz
  have hBlt : B < x ^ s * D ^ a := by
    dsimp [B, D, s, a]
    nlinarith
  have hpow :
      B ^ (r : ℝ) <
        (x ^ s * D ^ a) ^ (r : ℝ) :=
    Real.rpow_lt_rpow (by simpa [B, s] using hbase.le) hBlt hrR
  have hsMul : s * (r : ℝ) = 1 := by
    dsimp [s]
    field_simp
  have haMul : a * (r : ℝ) = (r : ℝ) - 1 := by
    dsimp [a]
    calc
      (1 - s) * (r : ℝ) = (r : ℝ) - s * (r : ℝ) := by ring
      _ = (r : ℝ) - 1 := by rw [hsMul]
  have hpowRight :
      (x ^ s * D ^ a) ^ (r : ℝ) =
        x * D ^ ((r : ℝ) - 1) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hx.le s)
      (Real.rpow_nonneg hD.le a),
      ← Real.rpow_mul hx.le, ← Real.rpow_mul hD.le,
      hsMul, haMul, Real.rpow_one]
  have hcancel :
      D ^ ((r : ℝ) - 1) * D ^ (1 - (r : ℝ)) = 1 := by
    rw [← Real.rpow_add hD]
    ring_nf
    exact Real.rpow_zero D
  have hstrict :
      B ^ (r : ℝ) * D ^ (1 - (r : ℝ)) < x := by
    have hfactor : 0 < D ^ (1 - (r : ℝ)) :=
      Real.rpow_pos_of_pos hD _
    calc
      B ^ (r : ℝ) * D ^ (1 - (r : ℝ)) <
          (x ^ s * D ^ a) ^ (r : ℝ) *
            D ^ (1 - (r : ℝ)) :=
        mul_lt_mul_of_pos_right hpow hfactor
      _ = x := by rw [hpowRight]; nlinarith
  exact (not_lt_of_ge (by simpa [B, D, s] using hparameter)) hstrict

/-- The density slack `δ_n = ε / n` used in the moment induction. -/
def bookDelta (ε : ℝ) (n : ℕ) : ℝ := ε / n

lemma bookDelta_pos {ε : ℝ} {n : ℕ} (hε : 0 < ε) (hn : 1 ≤ n) :
    0 < bookDelta ε n := by
  dsimp [bookDelta]
  positivity

lemma bookDelta_le {ε : ℝ} {m n : ℕ} (hε : 0 ≤ ε)
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    bookDelta ε n ≤ bookDelta ε m := by
  dsimp [bookDelta]
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.zero_lt_of_lt hm
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_of_lt hm) hmn)
  exact (div_le_div_iff₀ hnR hmR).2
    (by
      have hcast : (m : ℝ) ≤ n := by exact_mod_cast hmn
      nlinarith)

lemma bookDelta_le_eps {ε : ℝ} {n : ℕ} (hε : 0 ≤ ε) (hn : 1 ≤ n) :
    bookDelta ε n ≤ ε := by
  simpa [bookDelta] using
    (bookDelta_le (ε := ε) (m := 1) (n := n) hε le_rfl hn)

/-- The exact slack calculation used after the density-preserving pivot. -/
lemma bookDelta_step_gap {ε : ℝ} {n : ℕ} (hε : 0 < ε) (hn : 2 ≤ n) :
    ε / (n : ℝ) ^ 2 ≤
      bookDelta ε (n - 1) - bookDelta ε n - ε / (n : ℝ) ^ 3 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnR0 : (0 : ℝ) < n := by positivity
  have hpredR : (0 : ℝ) < n - 1 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  simp only [bookDelta, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  field_simp [ne_of_gt hnR0, ne_of_gt hpredR]
  nlinarith

lemma bookDelta_sub_le_of_pos {ε : ℝ} {n b : ℕ}
    (hε : 0 ≤ ε) (hnb : 1 ≤ n - b) :
    bookDelta ε n ≤ bookDelta ε (n - b) := by
  exact bookDelta_le hε hnb (Nat.sub_le n b)

/-- Failure of one moment branch gives the corresponding normalized
`1/r`-power estimate.  It is strict whenever that branch has positive
relative size. -/
lemma branch_ratio_le_of_not_moment
    {c q α γ ρ : ℝ} {r : ℕ}
    (hc : 0 < c) (hq : 0 < q) (hα : 0 < α) (hr : 2 ≤ r)
    (hρ : 0 ≤ ρ)
    (hfail : ¬(0 ≤ γ ∧ c * α ^ r / q ≤ γ ^ r * ρ)) :
    γ / α * ρ ≤
        (c / q) ^ ((r : ℝ)⁻¹) *
          ρ ^ (1 - (r : ℝ)⁻¹) ∧
      (0 < ρ → γ / α * ρ <
        (c / q) ^ ((r : ℝ)⁻¹) *
          ρ ^ (1 - (r : ℝ)⁻¹)) := by
  let s : ℝ := (r : ℝ)⁻¹
  let a : ℝ := 1 - s
  have hrR : 0 < (r : ℝ) := by positivity
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hs1 : s < 1 := by
    dsimp [s]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hr)
  have ha : 0 < a := by dsimp [a]; linarith
  have hstrict : 0 < ρ → γ / α * ρ <
      (c / q) ^ s * ρ ^ a := by
    intro hρpos
    by_cases hγ : 0 ≤ γ
    · have hbranch : γ ^ r * ρ < c * α ^ r / q := by
        exact lt_of_not_ge (fun h ↦ hfail ⟨hγ, h⟩)
      have hαpow : 0 < α ^ r := pow_pos hα _
      have hρpow : 0 < ρ ^ (r - 1) := pow_pos hρpos _
      have hmul :=
        mul_lt_mul_of_pos_right hbranch hρpow
      have hpower :
          (γ / α * ρ) ^ r <
            (c / q) * ρ ^ (r - 1) := by
        have hscaled :=
          (div_lt_div_iff_of_pos_right hαpow).2 hmul
        have hρr : ρ ^ r = ρ * ρ ^ (r - 1) := by
          conv_lhs => rw [show r = 1 + (r - 1) by omega, pow_add]
          simp
        calc
          (γ / α * ρ) ^ r =
              ((γ ^ r * ρ) * ρ ^ (r - 1)) / α ^ r := by
            rw [mul_pow, div_pow, hρr]
            field_simp
          _ < ((c * α ^ r / q) * ρ ^ (r - 1)) / α ^ r :=
            hscaled
          _ = (c / q) * ρ ^ (r - 1) := by
            field_simp
      have hA0 : 0 ≤ γ / α * ρ := by positivity
      have hY0 : 0 ≤ (c / q) * ρ ^ (r - 1) := by positivity
      have hroot :
          γ / α * ρ <
            ((c / q) * ρ ^ (r - 1)) ^ s := by
        rw [Real.lt_rpow_inv_iff_of_pos hA0 hY0 hrR]
        simpa [s, Real.rpow_natCast] using hpower
      have hrootEq :
          ((c / q) * ρ ^ (r - 1)) ^ s =
            (c / q) ^ s * ρ ^ a := by
        rw [Real.mul_rpow (div_nonneg hc.le hq.le)
          (pow_nonneg hρ _)]
        congr 1
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hρ]
        congr 2
        dsimp [a, s]
        have hrne : (r : ℝ) ≠ 0 := ne_of_gt hrR
        rw [Nat.cast_sub (show 1 ≤ r by omega)]
        field_simp
        ring
      simpa [hrootEq] using hroot
    · have hγneg : γ < 0 := lt_of_not_ge hγ
      have hleft : γ / α * ρ < 0 :=
        mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos hγneg hα) hρpos
      have hright :
          0 < (c / q) ^ s * ρ ^ a := by positivity
      exact hleft.trans hright
  constructor
  · by_cases hρzero : ρ = 0
    · subst ρ
      have haRaw : 0 < 1 - (r : ℝ)⁻¹ := by
        simpa [a, s] using ha
      rw [Real.zero_rpow (ne_of_gt haRaw)]
      simp
    · exact (hstrict (lt_of_le_of_ne hρ (Ne.symm hρzero))).le
  · intro hρpos
    simpa [s, a] using hstrict hρpos

/-- Equation `e:moment3`, isolated as a real-variable consequence of
`e:moment2` and failure of both induction branches. -/
lemma moment3_of_not_branches
    {x μ q α αR αB ρR ρB X : ℝ} {r : ℕ}
    (hx : 0 < x) (hμ : 0 < μ) (hq : 0 < q) (hα : 0 < α)
    (hr : 2 ≤ r)
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hρsum : 0 < ρR + ρB)
    (hpartition :
      1 ≤ αR / α * ρR + αB / α * ρB + 1 / (α * X))
    (hfailR : ¬(0 ≤ αR ∧ x * α ^ r / q ≤ αR ^ r * ρR))
    (hfailB : ¬(0 ≤ αB ∧ μ * α ^ r / q ≤ αB ^ r * ρB)) :
    q ^ ((r : ℝ)⁻¹) <
      x ^ ((r : ℝ)⁻¹) * ρR ^ (1 - (r : ℝ)⁻¹) +
        μ ^ ((r : ℝ)⁻¹) * ρB ^ (1 - (r : ℝ)⁻¹) +
        q ^ ((r : ℝ)⁻¹) / (α * X) := by
  let s : ℝ := (r : ℝ)⁻¹
  let a : ℝ := 1 - s
  have hs : 0 < s := by
    dsimp [s]
    positivity
  obtain ⟨hRle, hRlt⟩ :=
    branch_ratio_le_of_not_moment hx hq hα hr hρR hfailR
  obtain ⟨hBle, hBlt⟩ :=
    branch_ratio_le_of_not_moment hμ hq hα hr hρB hfailB
  have hbranches :
      αR / α * ρR + αB / α * ρB <
        (x / q) ^ s * ρR ^ a + (μ / q) ^ s * ρB ^ a := by
    by_cases hR : 0 < ρR
    · exact add_lt_add_of_lt_of_le
        (by simpa [s, a] using hRlt hR) (by simpa [s, a] using hBle)
    · have hB : 0 < ρB := by linarith
      exact add_lt_add_of_le_of_lt
        (by simpa [s, a] using hRle) (by simpa [s, a] using hBlt hB)
  have hnormalized :
      1 <
        (x / q) ^ s * ρR ^ a + (μ / q) ^ s * ρB ^ a +
          1 / (α * X) :=
    by linarith
  have hqpow : 0 < q ^ s := Real.rpow_pos_of_pos hq _
  have hscaled :=
    mul_lt_mul_of_pos_left hnormalized hqpow
  have hcancel (c : ℝ) (hc : 0 ≤ c) :
      q ^ s * (c / q) ^ s = c ^ s := by
    rw [← Real.mul_rpow hq.le (div_nonneg hc hq.le)]
    congr 2
    field_simp
  calc
    q ^ ((r : ℝ)⁻¹) = q ^ s := by rfl
    _ < q ^ s *
          ((x / q) ^ s * ρR ^ a + (μ / q) ^ s * ρB ^ a +
            1 / (α * X)) := by simpa only [mul_one] using hscaled
    _ = x ^ s * ρR ^ a + μ ^ s * ρB ^ a +
          q ^ s / (α * X) := by
      calc
        q ^ s *
            ((x / q) ^ s * ρR ^ a + (μ / q) ^ s * ρB ^ a +
              1 / (α * X)) =
            (q ^ s * (x / q) ^ s) * ρR ^ a +
              (q ^ s * (μ / q) ^ s) * ρB ^ a +
              q ^ s / (α * X) := by ring
        _ = x ^ s * ρR ^ a + μ ^ s * ρB ^ a +
              q ^ s / (α * X) := by
          rw [hcancel x hx.le, hcancel μ hμ.le]
    _ = x ^ ((r : ℝ)⁻¹) * ρR ^ (1 - (r : ℝ)⁻¹) +
          μ ^ ((r : ℝ)⁻¹) * ρB ^ (1 - (r : ℝ)⁻¹) +
          q ^ ((r : ℝ)⁻¹) / (α * X) := by rfl

/-- The uniform numerical hypotheses hidden by the phrase “choose `L₀`
sufficiently large” in the proof of `t:bookmain`. -/
structure BookInductionBounds
    (x y μ p ε : ℝ) (r L₀ : ℕ) : Prop where
  eps_le_one : ε ≤ 1
  eps_lt_p : ε < p
  two_eps_le_p : 2 * ε ≤ p
  x_le_one : x ≤ 1
  y_le_one : y ≤ 1
  mu_scale : (1 + ε) * μ ≤ 1
  mu_eps_lt_one : μ + ε < 1
  critical : μ + ε ≤ μ / (μ + x)
  terminal_base : 0 < (p - ε) ^ ((r : ℝ)⁻¹) - μ - 2 * ε
  terminal_parameter :
    x ≤ ((p - ε) ^ ((r : ℝ)⁻¹) - μ - 2 * ε) ^ (r : ℝ) *
      (1 - μ) ^ (1 - (r : ℝ))
  ramsey : EventuallyRamseyBound (x + ε) (y + ε)
  ramsey_start : ramsey.choose ≤ L₀ + 1
  initial_domination :
    ∀ n l : ℕ, 2 ≤ n → L₀ ≤ l →
      1 ≤ (ε / (n : ℝ)) ^ r * (1 + ε) ^ (n + l)
  book_size :
    ∀ n l : ℕ, 4 ≤ n → L₀ ≤ l →
      5 * (bookCliqueSize μ ε r n : ℝ) ^ 2 ≤
        (1 + ε) ^ (n + l)
  exceptional_size :
    ∀ n l k : ℕ, 4 ≤ n → L₀ ≤ l → k ≤ n →
      (ramseyNumber k (bookCliqueSize μ ε r n) : ℝ) ≤
        ε * (p - ε) / (n : ℝ) ^ 3 * (1 + ε) ^ (n + l)
  terminal_error :
    ∀ n l : ℕ, 4 ≤ n → L₀ ≤ l →
      (p - ε) ^ ((r : ℝ)⁻¹) * (n : ℝ) ^ 2 /
          (ε * (1 + ε) ^ (n + l)) ≤ ε

/-- Numerical transfer used in the big-blue branch. -/
lemma transfer_blueBook_moment
    {β γ A P μ X X' Y : ℝ} {r b : ℕ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hA0 : 0 ≤ A) (hAγ : A ≤ γ) (hP0 : 0 ≤ P)
    (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hamp : μ ^ b ≤ A ^ r * P) (hcard : P * X ≤ X') :
    μ ^ b * (β ^ r * X * Y) ≤ γ ^ r * X' * Y := by
  have hβpow : β ^ r ≤ 1 := pow_le_one₀ hβ0 hβ1
  have hApow : A ^ r ≤ γ ^ r :=
    pow_le_pow_left₀ hA0 hAγ r
  have hPX0 : 0 ≤ P * X := mul_nonneg hP0 hX0
  have hγ0 : 0 ≤ γ := hA0.trans hAγ
  calc
    μ ^ b * (β ^ r * X * Y) =
        (μ ^ b * β ^ r * X) * Y := by ring
    _ ≤ ((A ^ r * P) * 1 * X) * Y := by
      gcongr
    _ = (A ^ r * (P * X)) * Y := by ring
    _ ≤ (γ ^ r * X') * Y := by
      gcongr
    _ = γ ^ r * X' * Y := rfl

set_option maxHeartbeats 5000000 in
-- The nested finite-set induction has several large real-arithmetic branch goals.
/-- The well-founded moment induction in `t:bookmain`, with all eventual
numerical estimates collected in `BookInductionBounds`. -/
theorem candidate_good_of_bookMoment {V : Type*} {G : SimpleGraph V}
    (x y μ p ε : ℝ) (r L₀ : ℕ)
    (hx : 0 < x) (hy : 0 < y) (hμ : 0 < μ) (hε : 0 < ε)
    (hr : 2 ≤ r) (B : BookInductionBounds x y μ p ε r L₀)
    {l : ℕ} (hl : 1 ≤ l) (hl₀ : L₀ ≤ l)
    (C : Candidate G) {k t : ℕ} (hk : 1 ≤ k) (ht : 1 ≤ t)
    (hdensity : p - bookDelta ε (k + t) ≤ C.density)
    (hmoment : HasBookMoment C x y μ p ε r k l t) :
    C.Good k l t := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ (k t : ℕ), k + t = n → 1 ≤ k → 1 ≤ t →
      ∀ C : Candidate G,
        p - bookDelta ε n ≤ C.density →
        HasBookMoment C x y μ p ε r k l t →
        C.Good k l t
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        dsimp only [P]
        intro k t hkt hk ht C hdensity hmoment
        subst n
        by_cases hkone : k = 1
        · subst k
          exact C.good_of_k_one l t
        by_cases htone : t = 1
        · subst t
          exact C.good_of_t_one k l
        have hk2 : 2 ≤ k := by omega
        have ht2 : 2 ≤ t := by omega
        have hn4 : 4 ≤ k + t := by omega
        have hbase0 :
            0 ≤ C.density + bookDelta ε (k + t) - p := by
          linarith
        have hbase0' :
            0 ≤ C.density + ε / (k + t : ℕ) - p := by
          simpa [bookDelta] using hbase0
        have hbasepos :=
          hmoment.shift_pos hx hy hμ (by omega) hbase0'
        obtain ⟨D, hDX, hDY, hregular, hdeg⟩ :=
          C.exists_degree_regularized
            (p - bookDelta ε (k + t)) r (by omega) (by
              dsimp [bookDelta]
              linarith)
        have hmomentD :
            HasBookMoment D x y μ p ε r k l t := by
          apply hmoment.trans
          simpa only [HasBookMoment] using (show
            (C.density + ε / (k + t : ℕ) - p) ^ r *
                  C.X.card * C.Y.card ≤
              (D.density + ε / (k + t : ℕ) - p) ^ r *
                  D.X.card * D.Y.card by
            simpa [bookDelta, sub_eq_add_neg, add_comm, add_left_comm,
              add_assoc] using hregular)
        have hdensityD :
            p - bookDelta ε (k + t) ≤ D.density := by
          have h := densityBetween_ge_of_pointwise_redDegree G
            (p - bookDelta ε (k + t)) D.X D.Y
            D.X_nonempty D.Y_nonempty hdeg
          simpa [Candidate.density] using h
        have hgoodD : D.Good k l t := by
          have hramseyLarge :
              B.ramsey.choose ≤ k + l := by
            calc
              B.ramsey.choose ≤ L₀ + 1 := B.ramsey_start
              _ ≤ l + k := by omega
              _ = k + l := by omega
          by_cases hYlarge :
              (x + ε)⁻¹ ^ k * (y + ε)⁻¹ ^ l ≤ D.Y.card
          · exact D.good_of_eventualRamseyBound_right
              (by linarith) (by linarith) B.ramsey hk hl
              hramseyLarge hYlarge
          have hYsmall :
              (D.Y.card : ℝ) <
                (x + ε)⁻¹ ^ k * (y + ε)⁻¹ ^ l :=
            lt_of_not_ge hYlarge
          have hdeltaLe :
              bookDelta ε (k + t) ≤ ε :=
            bookDelta_le_eps hε.le (by omega)
          have hshift1 :
              D.density + ε / (k + t : ℕ) - p ≤ 1 := by
            have hd1 := densityBetween_le_one G D.X D.Y
            change D.density ≤ 1 at hd1
            dsimp [bookDelta] at hdeltaLe
            linarith [B.eps_lt_p.le]
          have hXgrowth :
              (1 + ε) ^ (k + l + t) < D.X.card := by
            exact one_add_eps_pow_lt_card_X_of_moment D
              x y μ p ε r k l t hx hy hμ B.x_le_one B.y_le_one
              hε.le B.mu_scale
              (by
                dsimp [bookDelta] at hdensityD
                linarith)
              hshift1 hmomentD hYsmall
          let n := k + t
          let b := bookSpineSize ε r n
          let m := bookCliqueSize μ ε r n
          let W := D.X.filter fun v ↦
            (μ + ε) * D.X.card ≤ (blueNeighborsIn G v D.X).card
          have hn : n = k + t := rfl
          have hn1 : 1 ≤ n := by dsimp [n]; omega
          have hb : b ≠ 0 := by
            exact Nat.ne_of_gt
              (bookSpineSize_pos hε B.eps_le_one hn1)
          have hXgrowth' :
              (1 + ε) ^ (n + l) < D.X.card := by
            simpa [n, add_assoc, add_left_comm, add_comm] using hXgrowth
          have hXsize : 5 * m ^ 2 ≤ D.X.card := by
            have hreal :
                5 * (m : ℝ) ^ 2 < D.X.card :=
              (B.book_size n l (by dsimp [n]; omega) hl₀).trans_lt
                hXgrowth'
            exact_mod_cast hreal.le
          have hWX : W ⊆ D.X := by
            exact filter_subset _ _
          have hhigh : ∀ v ∈ W,
              (μ + ε) * D.X.card ≤
                (blueNeighborsIn G v D.X).card := by
            intro v hv
            simpa [W] using (mem_filter.mp hv).2
          by_cases hWlarge : ramseyNumber k m ≤ W.card
          · rcases redClique_or_large_blueBook G D.X W
                (μ + ε) k m b
                (by positivity) B.mu_eps_lt_one hb
                (by
                  simpa [m, b, n] using
                    bookCliqueSize_bound μ ε r n)
                hXsize hWX hWlarge hhigh with hred | hbook
            · exact Or.inl
                (Candidate.containsRedClique_mono subset_union_left hred)
            · obtain ⟨S, T, hSX, hTX, hST, hScard, hTcard⟩ := hbook
              by_cases htb : t ≤ b
              · have hblueS :=
                  isBlueBook_spine_containsBlueClique
                    (S := S) (T := T) (t := t) G hST
                    (by rw [hScard]; exact htb)
                exact Or.inr (Or.inl
                  (Candidate.containsBlueClique_mono hSX hblueS))
              have hbt : b ≤ t := (Nat.le_of_lt (lt_of_not_ge htb))
              have hTposR : (0 : ℝ) < T.card := by
                have hfactor :
                    0 < (μ + ε) ^ b / 2 * D.X.card := by
                  exact mul_pos
                    (div_pos (pow_pos (add_pos hμ hε) _) (by norm_num))
                    (by exact_mod_cast D.card_X_pos)
                exact hfactor.trans_le hTcard
              have hTne : T.Nonempty := by
                apply card_pos.mp
                exact_mod_cast hTposR
              let E : Candidate G := {
                X := T
                Y := D.Y
                X_nonempty := hTne
                Y_nonempty := D.Y_nonempty
                disjoint := D.disjoint.mono_left hTX
              }
              have hEdensity :
                  p - bookDelta ε (k + t) ≤ E.density := by
                have hTdeg : ∀ v ∈ T,
                    (p - bookDelta ε (k + t)) * D.Y.card ≤
                      (redNeighborsIn G v D.Y).card :=
                  fun v hv ↦ hdeg v (hTX hv)
                simpa [E, Candidate.density] using
                  densityBetween_ge_of_pointwise_redDegree G
                    (p - bookDelta ε (k + t)) T D.Y
                    hTne D.Y_nonempty hTdeg
              have hnsub : 1 ≤ k + (t - b) := by omega
              have hdeltaSub :
                  bookDelta ε (k + t) ≤
                    bookDelta ε (k + (t - b)) := by
                have hsum : k + (t - b) = (k + t) - b := by omega
                rw [hsum]
                exact bookDelta_sub_le_of_pos hε.le (by omega)
              have hEdensity' :
                  p - bookDelta ε (k + (t - b)) ≤ E.density := by
                linarith
              have hgap :
                  ε / (n : ℝ) ^ 2 ≤
                    E.density + bookDelta ε (k + (t - b)) - p := by
                have hprev :
                    bookDelta ε (n - 1) ≤
                      bookDelta ε (k + (t - b)) := by
                  apply bookDelta_le hε.le (by omega)
                  dsimp [n]
                  omega
                have hstep := bookDelta_step_gap hε (n := n) (by
                  dsimp [n]
                  omega)
                have heta0 : 0 ≤ ε / (n : ℝ) ^ 3 := by positivity
                linarith
              have hmomentE :
                  HasBookMoment E x y μ p ε r k l (t - b) := by
                have hamp := blueBook_moment_amplification
                  (μ := μ) (ε := ε) (r := r) (n := n)
                  hμ (by
                    have := B.mu_scale
                    nlinarith) hε B.eps_le_one hn1
                have hpage :
                    ((μ + ε) ^ b / 2) * D.X.card ≤ E.X.card := by
                  simpa [E] using hTcard
                have htransfer := transfer_blueBook_moment
                  (β := D.density + ε / (k + t : ℕ) - p)
                  (γ := E.density + ε / (k + (t - b) : ℕ) - p)
                  (A := ε / (n : ℝ) ^ 2)
                  (P := (μ + ε) ^ b / 2)
                  (μ := μ) (X := D.X.card) (X' := E.X.card)
                  (Y := D.Y.card) (r := r) (b := b)
                  (by
                    dsimp [bookDelta] at hdensityD
                    linarith)
                  hshift1 (by positivity)
                  (by simpa [bookDelta] using hgap)
                  (by positivity) (by positivity) (by positivity)
                  (by simpa [b] using hamp) hpage
                change bookWeight x y μ k l (t - b) ≤
                  (E.density + ε / (k + (t - b) : ℕ) - p) ^ r *
                    E.X.card * E.Y.card
                rw [bookWeight_blue_scale (ne_of_gt hμ) hbt]
                calc
                  μ ^ b * bookWeight x y μ k l t ≤
                      μ ^ b *
                        ((D.density + ε / (k + t : ℕ) - p) ^ r *
                          D.X.card * D.Y.card) := by
                    exact mul_le_mul_of_nonneg_left hmomentD (by positivity)
                  _ ≤
                      (E.density + ε / (k + (t - b) : ℕ) - p) ^ r *
                        E.X.card * E.Y.card := by
                    simpa [E] using htransfer
              have hgoodE : E.Good k l (t - b) := by
                apply ih (k + (t - b)) (by omega)
                  k (t - b) rfl hk (by omega) E hEdensity' hmomentE
              exact D.good_of_blueBook_pages_good E
                hTX (by simp [E]) hSX (by simpa [E] using hST)
                hScard hbt hgoodE
          · have hq : 0 < p - ε := sub_pos.mpr B.eps_lt_p
            have heta : 0 < ε / (n : ℝ) ^ 3 := by positivity
            have hWcard :
                (W.card : ℝ) ≤
                  (ε / (n : ℝ) ^ 3) * (p - ε) * D.X.card := by
              have hWR :
                  (W.card : ℝ) <
                    ramseyNumber k m := by
                exact_mod_cast lt_of_not_ge hWlarge
              have hRamsey := B.exceptional_size n l k
                (by dsimp [n]; omega) hl₀ (by dsimp [n]; omega)
              have hcoef :
                  0 < ε * (p - ε) / (n : ℝ) ^ 3 := by positivity
              exact (calc
                (W.card : ℝ) < ramseyNumber k m := hWR
                _ ≤ ε * (p - ε) / (n : ℝ) ^ 3 *
                      (1 + ε) ^ (n + l) := by
                  simpa [m] using hRamsey
                _ < ε * (p - ε) / (n : ℝ) ^ 3 * D.X.card :=
                  mul_lt_mul_of_pos_left hXgrowth' hcoef
                _ = (ε / (n : ℝ) ^ 3) * (p - ε) *
                      D.X.card := by ring).le
            have hqDensity : p - ε ≤ D.density := by
              have := bookDelta_le_eps hε.le (n := k + t) (by omega)
              linarith
            have hWsum := D.exceptional_density_sum_le W
              (ε / (n : ℝ) ^ 3) (p - ε) heta.le hqDensity hWcard
            have hdegOutside : ∀ v ∈ D.X \ W,
                0 < (redNeighborsIn G v D.Y).card := by
              intro v hv
              have hvX : v ∈ D.X := (mem_sdiff.mp hv).1
              have hvdeg := hdeg v hvX
              have hqY :
                  0 < (p - bookDelta ε (k + t)) * D.Y.card := by
                have hδ := bookDelta_le_eps hε.le (n := k + t) (by omega)
                have : 0 < p - bookDelta ε (k + t) := by linarith
                have hDYpos : (0 : ℝ) < D.Y.card := by
                  exact_mod_cast D.card_Y_pos
                exact mul_pos this hDYpos
              have hcardR :
                  (0 : ℝ) < (redNeighborsIn G v D.Y).card :=
                hqY.trans_le hvdeg
              exact_mod_cast hcardR
            obtain ⟨v, hv, hpivot⟩ :=
              D.exists_density_preserving_pivot_outside W
                (ε / (n : ℝ) ^ 3) hWX heta.le
                (by
                  have hsmall : ε / (n : ℝ) ^ 3 < ε := by
                    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
                    have : ε / (n : ℝ) ^ 3 ≤ ε := by
                      apply (div_le_iff₀ (by positivity)).2
                      nlinarith [show (1 : ℝ) ≤ (n : ℝ) ^ 3 by
                        exact one_le_pow₀ hnR]
                    have hn4R : (1 : ℝ) < n ^ 3 := by
                      have : (1 : ℝ) < n := by exact_mod_cast (by
                        dsimp [n]
                        omega : 1 < n)
                      exact one_lt_pow₀ this (by norm_num)
                    exact lt_of_le_of_ne this (by
                      intro heq
                      field_simp at heq
                      nlinarith)
                  linarith [hqDensity, B.two_eps_le_p])
                hWsum hdegOutside
            have hvX : v ∈ D.X := (mem_sdiff.mp hv).1
            have hvNotW : v ∉ W := (mem_sdiff.mp hv).2
            let Y' := redNeighborsIn G v D.Y
            let XR := redNeighborsIn G v D.X
            let XB := blueNeighborsIn G v D.X
            have hY'deg := hdeg v hvX
            have hY' : Y'.Nonempty := by
              have hpos : 0 < (Y'.card : ℝ) := by
                have hδ := bookDelta_le_eps hε.le (n := k + t) (by omega)
                have hq0 : 0 < p - bookDelta ε (k + t) := by linarith
                dsimp [Y']
                have hDYpos : (0 : ℝ) < D.Y.card := by
                  exact_mod_cast D.card_Y_pos
                exact (mul_pos hq0 hDYpos).trans_le hY'deg
              apply card_pos.mp
              exact_mod_cast hpos
            let p' := p - bookDelta ε (n - 1)
            let α := densityBetween G D.X Y' - p'
            let αR := densityBetween G XR Y' - p'
            let αB := densityBetween G XB Y' - p'
            let β := D.density + bookDelta ε n - p
            have hαlower : ε / (n : ℝ) ^ 2 ≤ α := by
              have hstep := bookDelta_step_gap hε (n := n)
                (by dsimp [n]; omega)
              dsimp [α, p', Y']
              change D.density - ε / (n : ℝ) ^ 3 ≤
                densityBetween G D.X (redNeighborsIn G v D.Y) at hpivot
              have hdensityN :
                  p - bookDelta ε n ≤ D.density := by
                simpa [n] using hdensityD
              linarith
            have hα : 0 < α := lt_of_lt_of_le (by positivity) hαlower
            have hβ0 : 0 ≤ β := by
              dsimp [β]
              have hdensityN :
                  p - bookDelta ε n ≤ D.density := by
                simpa [n] using hdensityD
              linarith
            have hβα : β ≤ α := by
              have hstep := bookDelta_step_gap hε (n := n)
                (by dsimp [n]; omega)
              have hnonneg : 0 ≤ ε / (n : ℝ) ^ 2 := by positivity
              dsimp [β, α, p', Y']
              change D.density - ε / (n : ℝ) ^ 3 ≤
                densityBetween G D.X (redNeighborsIn G v D.Y) at hpivot
              linarith
            have hp'0 : 0 ≤ p' := by
              have hδ := bookDelta_le_eps hε.le
                (n := n - 1) (by dsimp [n]; omega)
              dsimp [p']
              linarith
            have hpartition := density_partition_ratio_le G p' hp'0
              hvX Y' hY' (by simpa [α] using hα)
            let ρR : ℝ := XR.card / D.X.card
            let ρB : ℝ := XB.card / D.X.card
            have hDXpos : (0 : ℝ) < D.X.card := by
              exact_mod_cast D.card_X_pos
            have hρR0 : 0 ≤ ρR := by dsimp [ρR]; positivity
            have hρB0 : 0 ≤ ρB := by dsimp [ρB]; positivity
            have hcardPartition :
                XR.card + XB.card + 1 = D.X.card := by
              have hc := congrArg Finset.card
                (red_blue_neighbors_union_insert G hvX)
              simpa [XR, XB,
                card_union_of_disjoint (red_blue_neighbors_disjoint G v D.X),
                card_union_of_disjoint
                  (neighbors_union_disjoint_singleton G v D.X)] using hc
            have hDXone : (1 : ℝ) < D.X.card := by
              have hpowone : 1 < (1 + ε) ^ (n + l) := by
                exact one_lt_pow₀ (by linarith) (by omega)
              exact hpowone.trans hXgrowth'
            have hDXoneNat : 1 < D.X.card := by
              exact_mod_cast hDXone
            have hρsum : 0 < ρR + ρB := by
              dsimp [ρR, ρB]
              rw [← add_div]
              apply div_pos
              · exact_mod_cast (by omega : 0 < XR.card + XB.card)
              · exact hDXpos
            have hpartition' :
                1 ≤ αR / α * ρR + αB / α * ρB +
                  1 / (α * D.X.card) := by
              simpa [α, αR, αB, ρR, ρB, XR, XB, div_eq_mul_inv,
                mul_assoc, mul_comm, mul_left_comm] using hpartition
            by_cases hred :
                0 ≤ αR ∧
                  x * α ^ r / (p - ε) ≤ αR ^ r * ρR
            · have hρRpos : 0 < ρR := by
                have hleft :
                    0 < x * α ^ r / (p - ε) := by positivity
                have hright : 0 < αR ^ r * ρR :=
                  hleft.trans_le hred.2
                by_contra hnot
                have : ρR = 0 := le_antisymm (le_of_not_gt hnot) hρR0
                rw [this, mul_zero] at hright
                exact (lt_irrefl 0) hright
              have hXR : XR.Nonempty := by
                apply card_pos.mp
                have : (0 : ℝ) < XR.card := by
                  have hmul := mul_pos hρRpos hDXpos
                  have heq :
                      ρR * (D.X.card : ℝ) = XR.card := by
                    dsimp [ρR]
                    field_simp
                  rwa [heq] at hmul
                exact_mod_cast this
              let R : Candidate G := D.redStep v hXR hY'
              have hbranch :
                  x * α ^ r * D.X.card / (p - ε) ≤
                    αR ^ r * XR.card := by
                have := mul_le_mul_of_nonneg_right hred.2 hDXpos.le
                dsimp [ρR] at this
                field_simp at this ⊢
                nlinarith
              have hmomentR :
                  HasBookMoment R x y μ p ε r (k - 1) l t := by
                change bookWeight x y μ (k - 1) l t ≤
                  (R.density + ε / ((k - 1) + t : ℕ) - p) ^ r *
                    R.X.card * R.Y.card
                rw [bookWeight_red_scale (ne_of_gt hx) hk]
                calc
                  x * bookWeight x y μ k l t ≤
                      x * (β ^ r * D.X.card * D.Y.card) := by
                    have hm : bookWeight x y μ k l t ≤
                        β ^ r * D.X.card * D.Y.card := by
                      simpa [HasBookMoment, β, n, bookDelta] using hmomentD
                    exact mul_le_mul_of_nonneg_left hm hx.le
                  _ ≤ αR ^ r * XR.card * Y'.card := by
                    exact transfer_moment_of_branch
                      α β αR x (p - ε) D.X.card XR.card
                      D.Y.card Y'.card r hβ0 hβα hx.le hq
                      (by positivity) (by positivity) (by positivity)
                      (by
                        dsimp [Y']
                        have hδ := bookDelta_le_eps hε.le
                          (n := k + t) (by omega)
                        have hqle :
                            (p - ε) * D.Y.card ≤
                              (p - bookDelta ε (k + t)) * D.Y.card := by
                          gcongr
                        exact hqle.trans hY'deg)
                      hbranch
                  _ = (R.density + ε / ((k - 1) + t : ℕ) - p) ^ r *
                        R.X.card * R.Y.card := by
                    have hnred : (k - 1) + t = n - 1 := by
                      dsimp [n]
                      omega
                    change αR ^ r * XR.card * Y'.card =
                      (densityBetween G XR Y' +
                          ε / ((k - 1) + t : ℕ) - p) ^ r *
                        XR.card * Y'.card
                    rw [hnred]
                    dsimp [αR, p', bookDelta]
                    ring
              have hRdensity :
                  p - bookDelta ε ((k - 1) + t) ≤ R.density := by
                have hnred : (k - 1) + t = n - 1 := by
                  dsimp [n]
                  omega
                change p - bookDelta ε ((k - 1) + t) ≤
                  densityBetween G XR Y'
                rw [hnred]
                dsimp [αR, p'] at hred
                linarith [hred.1]
              have hgoodR := ih ((k - 1) + t) (by omega)
                (k - 1) t rfl (by omega) ht R hRdensity hmomentR
              have hgoodLift :=
                D.good_of_redStep_good hvX hXR hY' hgoodR
              convert hgoodLift using 1
              all_goals omega
            · by_cases hblue :
                0 ≤ αB ∧
                  μ * α ^ r / (p - ε) ≤ αB ^ r * ρB
              · have hρBpos : 0 < ρB := by
                  have hleft :
                      0 < μ * α ^ r / (p - ε) := by positivity
                  have hright : 0 < αB ^ r * ρB :=
                    hleft.trans_le hblue.2
                  by_contra hnot
                  have : ρB = 0 := le_antisymm (le_of_not_gt hnot) hρB0
                  rw [this, mul_zero] at hright
                  exact (lt_irrefl 0) hright
                have hXB : XB.Nonempty := by
                  apply card_pos.mp
                  have : (0 : ℝ) < XB.card := by
                    have hmul := mul_pos hρBpos hDXpos
                    have heq :
                        ρB * (D.X.card : ℝ) = XB.card := by
                      dsimp [ρB]
                      field_simp
                    rwa [heq] at hmul
                  exact_mod_cast this
                let Q : Candidate G := D.blueStep v hXB hY'
                have hbranch :
                    μ * α ^ r * D.X.card / (p - ε) ≤
                      αB ^ r * XB.card := by
                  have := mul_le_mul_of_nonneg_right hblue.2 hDXpos.le
                  dsimp [ρB] at this
                  field_simp at this ⊢
                  nlinarith
                have hmomentQ :
                    HasBookMoment Q x y μ p ε r k l (t - 1) := by
                  change bookWeight x y μ k l (t - 1) ≤
                    (Q.density + ε / (k + (t - 1) : ℕ) - p) ^ r *
                      Q.X.card * Q.Y.card
                  rw [bookWeight_blue_scale (ne_of_gt hμ)
                    (show 1 ≤ t by omega)]
                  simp only [pow_one]
                  calc
                    μ * bookWeight x y μ k l t ≤
                        μ * (β ^ r * D.X.card * D.Y.card) := by
                      have hm : bookWeight x y μ k l t ≤
                          β ^ r * D.X.card * D.Y.card := by
                        simpa [HasBookMoment, β, n, bookDelta] using hmomentD
                      exact mul_le_mul_of_nonneg_left hm hμ.le
                    _ ≤ αB ^ r * XB.card * Y'.card := by
                      exact transfer_moment_of_branch
                        α β αB μ (p - ε) D.X.card XB.card
                        D.Y.card Y'.card r hβ0 hβα hμ.le hq
                        (by positivity) (by positivity) (by positivity)
                        (by
                          dsimp [Y']
                          have hδ := bookDelta_le_eps hε.le
                            (n := k + t) (by omega)
                          have hqle :
                              (p - ε) * D.Y.card ≤
                                (p - bookDelta ε (k + t)) * D.Y.card := by
                            gcongr
                          exact hqle.trans hY'deg)
                        hbranch
                    _ = (Q.density + ε / (k + (t - 1) : ℕ) - p) ^ r *
                          Q.X.card * Q.Y.card := by
                      have hnblue : k + (t - 1) = n - 1 := by
                        dsimp [n]
                        omega
                      change αB ^ r * XB.card * Y'.card =
                        (densityBetween G XB Y' +
                            ε / (k + (t - 1) : ℕ) - p) ^ r *
                          XB.card * Y'.card
                      rw [hnblue]
                      dsimp [αB, p', bookDelta]
                      ring
                have hQdensity :
                    p - bookDelta ε (k + (t - 1)) ≤ Q.density := by
                  have hnblue : k + (t - 1) = n - 1 := by
                    dsimp [n]
                    omega
                  change p - bookDelta ε (k + (t - 1)) ≤
                    densityBetween G XB Y'
                  rw [hnblue]
                  dsimp [αB, p'] at hblue
                  linarith [hblue.1]
                have hgoodQ := ih (k + (t - 1)) (by omega)
                  k (t - 1) rfl hk (by omega) Q hQdensity hmomentQ
                have hgoodLift :=
                  D.good_of_blueStep_good hvX hXB hY' hgoodQ
                convert hgoodLift using 1
                all_goals omega
              · have hmoment3 := moment3_of_not_branches
                    hx hμ hq hα hr hρR0 hρB0 hρsum
                    hpartition' hred hblue
                have hρsumle : ρR + ρB ≤ 1 := by
                  dsimp [ρR, ρB]
                  rw [← add_div, div_le_one hDXpos]
                  exact_mod_cast (by omega :
                    XR.card + XB.card ≤ D.X.card)
                have hρBbound : ρB ≤ μ + ε := by
                  have hnotHigh :
                      ((blueNeighborsIn G v D.X).card : ℝ) <
                        (μ + ε) * D.X.card := by
                    have := hvNotW
                    simp only [W, mem_filter, hvX, true_and, not_le] at this
                    exact this
                  dsimp [ρB, XB]
                  exact (div_le_iff₀ hDXpos).2 hnotHigh.le
                have hρRbound : ρR ≤ 1 - ρB := by linarith
                have ha0 : 0 ≤ 1 - (r : ℝ)⁻¹ := by
                  have : (r : ℝ)⁻¹ < 1 :=
                    inv_lt_one_of_one_lt₀ (by exact_mod_cast hr)
                  linarith
                have hρpower :
                    ρR ^ (1 - (r : ℝ)⁻¹) ≤
                      (1 - ρB) ^ (1 - (r : ℝ)⁻¹) := by
                  exact Real.rpow_le_rpow hρR0 hρRbound ha0
                have hmoment3' :
                    (p - ε) ^ ((r : ℝ)⁻¹) <
                      x ^ ((r : ℝ)⁻¹) *
                          (1 - ρB) ^ (1 - (r : ℝ)⁻¹) +
                        μ ^ ((r : ℝ)⁻¹) *
                          ρB ^ (1 - (r : ℝ)⁻¹) +
                        (p - ε) ^ ((r : ℝ)⁻¹) /
                          (α * D.X.card) := by
                  have hxpow0 :
                      0 ≤ x ^ ((r : ℝ)⁻¹) :=
                    Real.rpow_nonneg hx.le _
                  exact hmoment3.trans_le (by gcongr)
                have herr :
                    (p - ε) ^ ((r : ℝ)⁻¹) /
                        (α * D.X.card) ≤ ε := by
                  have hden :
                      ε * (1 + ε) ^ (n + l) <
                        α * D.X.card * (n : ℝ) ^ 2 := by
                    have hαscaled :
                        ε ≤ α * (n : ℝ) ^ 2 := by
                      have := mul_le_mul_of_nonneg_right hαlower
                        (sq_nonneg (n : ℝ))
                      field_simp at this
                      nlinarith
                    calc
                      ε * (1 + ε) ^ (n + l) ≤
                          (α * (n : ℝ) ^ 2) *
                            (1 + ε) ^ (n + l) :=
                        mul_le_mul_of_nonneg_right hαscaled (by positivity)
                      _ < (α * (n : ℝ) ^ 2) * D.X.card :=
                        mul_lt_mul_of_pos_left hXgrowth' (by positivity)
                      _ = α * D.X.card * (n : ℝ) ^ 2 := by ring
                  have hdivide :
                      (p - ε) ^ ((r : ℝ)⁻¹) /
                          (α * D.X.card) <
                        (p - ε) ^ ((r : ℝ)⁻¹) * (n : ℝ) ^ 2 /
                          (ε * (1 + ε) ^ (n + l)) := by
                    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
                    have hroot :
                        0 < (p - ε) ^ ((r : ℝ)⁻¹) :=
                      Real.rpow_pos_of_pos hq _
                    have hmul := mul_lt_mul_of_pos_left hden hroot
                    convert hmul using 1
                    all_goals ring
                  exact hdivide.le.trans
                    (B.terminal_error n l (by dsimp [n]; omega) hl₀)
                exact False.elim (bookMoment_terminal_contradiction
                  hx hμ hε hr B.mu_eps_lt_one B.critical
                  hρB0 hρBbound herr B.terminal_base
                  B.terminal_parameter hmoment3')
        exact Candidate.good_of_mono hDX (by simp [hDY]) hgoodD
  exact hP (k + t) k t rfl hk ht C hdensity hmoment

/-- `e:moment0`: the original size hypothesis implies the invariant, and
hence the conclusion of `t:bookmain`, once the uniform bounds have been
fixed. -/
theorem candidate_good_of_bookBounds {V : Type*} {G : SimpleGraph V}
    (x₀ y₀ μ₀ x y μ p ε : ℝ) (r L₀ : ℕ)
    (hx₀ : 0 < x₀) (hy₀ : 0 < y₀) (hμ₀ : 0 < μ₀)
    (hx : 0 < x) (hy : 0 < y) (hμ : 0 < μ) (hε : 0 < ε)
    (hr : 2 ≤ r) (B : BookInductionBounds x y μ p ε r L₀)
    (hxc : x₀ ≤ x / (1 + ε))
    (hyc : y₀ ≤ y / (1 + ε))
    (hμc : μ₀ ≤ μ / (1 + ε))
    {k l t : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (ht : 1 ≤ t)
    (hl₀ : L₀ ≤ l) (C : Candidate G)
    (hdensity : p ≤ C.density)
    (hsize :
      bookWeight x₀ y₀ μ₀ k l t ≤
        (C.X.card : ℝ) * C.Y.card) :
    C.Good k l t := by
  have hc : 0 < 1 + ε := by linarith
  have hscale :
      (1 + ε) ^ (k + l + t) * bookWeight x y μ k l t ≤
        bookWeight x₀ y₀ μ₀ k l t :=
    bookWeight_scale hx₀ hy₀ hμ₀ hx hy hμ hc
      hxc hyc hμc k l t
  have hdom :
      1 ≤ (ε / (k + t : ℕ)) ^ r * (1 + ε) ^ (k + l + t) := by
    simpa [add_assoc, add_left_comm, add_comm] using
      B.initial_domination (k + t) l (by omega) hl₀
  have hmoment :=
    initial_hasBookMoment C x₀ y₀ μ₀ x y μ p ε r k l t
      (by omega) hx hy hμ hε.le hdensity hsize hscale hdom
  have hdensity' :
      p - bookDelta ε (k + t) ≤ C.density := by
    have hdelta : 0 ≤ bookDelta ε (k + t) :=
      (bookDelta_pos hε (by omega)).le
    linarith
  exact candidate_good_of_bookMoment x y μ p ε r L₀
    hx hy hμ hε hr B hl hl₀ C hk ht hdensity' hmoment

end Arxiv2407_19026
