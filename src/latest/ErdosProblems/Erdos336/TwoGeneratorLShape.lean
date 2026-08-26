import Mathlib
import ErdosProblems.Erdos336.LShapeDiagramBound

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Two-generator canonical diagrams are L-shaped
-/

namespace Erdos336

/-- A minimal missing cell of a coordinatewise down-set. -/
def IsInnerCorner (s : Finset (ℕ × ℕ)) (p : ℕ × ℕ) : Prop :=
  p ∉ s ∧ 0 < p.1 ∧ 0 < p.2 ∧
    (p.1 - 1, p.2) ∈ s ∧ (p.1, p.2 - 1) ∈ s

private lemma twoGenLabel_pred_fst
    {G : Type*} [AddCommMonoid G] (a b : G)
    {x y : ℕ} (hx : 0 < x) :
    twoGenLabel a b (x, y) = twoGenLabel a b (x - 1, y) + a := by
  simp only [twoGenLabel]
  have hxs : x - 1 + 1 = x := by omega
  conv_lhs => rw [← hxs, add_nsmul]
  simp
  ac_rfl

private lemma twoGenLabel_pred_snd
    {G : Type*} [AddCommMonoid G] (a b : G)
    {x y : ℕ} (hy : 0 < y) :
    twoGenLabel a b (x, y) = twoGenLabel a b (x, y - 1) + b := by
  simp only [twoGenLabel]
  have hys : y - 1 + 1 = y := by omega
  conv_lhs => rw [← hys, add_nsmul]
  simp
  ac_rfl

/-- Every inner corner of a two-generator canonical diagram has label zero. -/
theorem innerCorner_label_zero
    {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (a b : G)
    (hgen : ∀ g : G, ∃ p : ℕ × ℕ, twoGenLabel a b p = g)
    {q : ℕ × ℕ}
    (hq : IsInnerCorner (canonicalTwoDiagram a b hgen) q) :
    twoGenLabel a b q = 0 := by
  let r := canonicalTwoPair a b hgen (twoGenLabel a b q)
  have hrs : r ∈ canonicalTwoDiagram a b hgen := by
    apply (mem_canonicalTwoDiagram_iff a b hgen r).2
    exact canonicalTwoPair_isCanonical a b hgen _
  have hrlabel : twoGenLabel a b r = twoGenLabel a b q :=
    (canonicalTwoPair_spec a b hgen _).2
  have hrx : r.1 = 0 := by
    by_contra hrxne
    have hrxpos : 0 < r.1 := Nat.pos_of_ne_zero hrxne
    have hrpred : (r.1 - 1, r.2) ∈ canonicalTwoDiagram a b hgen :=
      canonicalTwoDiagram_downward a b hgen hrs (by omega) (by omega)
    have hlabelPred :
        twoGenLabel a b (r.1 - 1, r.2) =
          twoGenLabel a b (q.1 - 1, q.2) := by
      apply add_right_cancel (b := a)
      rw [← twoGenLabel_pred_fst a b hrxpos,
        ← twoGenLabel_pred_fst a b hq.2.1, hrlabel]
    have heqPred := canonicalTwoRep_unique a b
      ((mem_canonicalTwoDiagram_iff a b hgen _).1 hrpred)
      ((mem_canonicalTwoDiagram_iff a b hgen _).1 hq.2.2.2.1)
      hlabelPred
    have heqs : r.1 - 1 = q.1 - 1 ∧ r.2 = q.2 := by
      simpa only [Prod.mk.injEq] using heqPred
    have heq₁ := heqs.1
    have heq₂ := heqs.2
    have hqxpos : 0 < q.1 := hq.2.1
    have hrq : r = q := by
      apply Prod.ext
      · omega
      · exact heq₂
    exact hq.1 (hrq ▸ hrs)
  have hry : r.2 = 0 := by
    by_contra hryne
    have hrypos : 0 < r.2 := Nat.pos_of_ne_zero hryne
    have hrpred : (r.1, r.2 - 1) ∈ canonicalTwoDiagram a b hgen :=
      canonicalTwoDiagram_downward a b hgen hrs (by omega) (by omega)
    have hlabelPred :
        twoGenLabel a b (r.1, r.2 - 1) =
          twoGenLabel a b (q.1, q.2 - 1) := by
      apply add_right_cancel (b := b)
      rw [← twoGenLabel_pred_snd a b hrypos,
        ← twoGenLabel_pred_snd a b hq.2.2.1, hrlabel]
    have heqPred := canonicalTwoRep_unique a b
      ((mem_canonicalTwoDiagram_iff a b hgen _).1 hrpred)
      ((mem_canonicalTwoDiagram_iff a b hgen _).1 hq.2.2.2.2)
      hlabelPred
    have heqs : r.1 = q.1 ∧ r.2 - 1 = q.2 - 1 := by
      simpa only [Prod.mk.injEq] using heqPred
    have heq₁ := heqs.1
    have heq₂ := heqs.2
    have hqypos : 0 < q.2 := hq.2.2.1
    have hrq : r = q := by
      apply Prod.ext
      · exact heq₁
      · omega
    exact hq.1 (hrq ▸ hrs)
  rw [← hrlabel]
  simp [twoGenLabel, hrx, hry]

/-- There is at most one inner corner in a two-generator canonical diagram. -/
theorem innerCorner_unique
    {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (a b : G)
    (hgen : ∀ g : G, ∃ p : ℕ × ℕ, twoGenLabel a b p = g)
    {q t : ℕ × ℕ}
    (hq : IsInnerCorner (canonicalTwoDiagram a b hgen) q)
    (ht : IsInnerCorner (canonicalTwoDiagram a b hgen) t) :
    q = t := by
  have hqlabel := innerCorner_label_zero a b hgen hq
  have htlabel := innerCorner_label_zero a b hgen ht
  by_contra hne
  have hxne : q.1 ≠ t.1 := by
    intro hxeq
    have haxis : twoGenLabel a b (0, q.2) = twoGenLabel a b (0, t.2) := by
      simp only [twoGenLabel, zero_nsmul, zero_add]
      have hfull : q.1 • a + q.2 • b = t.1 • a + t.2 • b := by
        simpa [twoGenLabel] using hqlabel.trans htlabel.symm
      rw [hxeq] at hfull
      exact add_left_cancel hfull
    have hqs : (0, q.2) ∈ canonicalTwoDiagram a b hgen :=
      canonicalTwoDiagram_downward a b hgen hq.2.2.2.1 (by omega) (by omega)
    have hts : (0, t.2) ∈ canonicalTwoDiagram a b hgen :=
      canonicalTwoDiagram_downward a b hgen ht.2.2.2.1 (by omega) (by omega)
    have heq := canonicalTwoRep_unique a b
      ((mem_canonicalTwoDiagram_iff a b hgen _).1 hqs)
      ((mem_canonicalTwoDiagram_iff a b hgen _).1 hts) haxis
    have heqs : (0 : ℕ) = 0 ∧ q.2 = t.2 := by
      simpa only [Prod.mk.injEq] using heq
    apply hne
    exact Prod.ext hxeq heqs.2
  have oriented_contra : ∀ {q t : ℕ × ℕ},
      IsInnerCorner (canonicalTwoDiagram a b hgen) q →
      IsInnerCorner (canonicalTwoDiagram a b hgen) t →
      q.1 < t.1 → False := by
    intro q t hq ht hxt
    have hqlabel := innerCorner_label_zero a b hgen hq
    have htlabel := innerCorner_label_zero a b hgen ht
    have hyt : t.2 < q.2 := by
      by_contra hnot
      have hy : q.2 ≤ t.2 := by omega
      have hqmem : q ∈ canonicalTwoDiagram a b hgen :=
        canonicalTwoDiagram_downward a b hgen ht.2.2.2.1 (by omega) (by omega)
      exact hq.1 hqmem
    let dx := t.1 - q.1
    let dy := q.2 - t.2
    have hdx : 0 < dx := by dsimp [dx]; omega
    have hdy : 0 < dy := by dsimp [dy]; omega
    have haxisLabel :
        twoGenLabel a b (dx, 0) = twoGenLabel a b (0, dy) := by
      simp only [twoGenLabel, zero_nsmul, add_zero, zero_add]
      have hraw : t.1 • a + t.2 • b = q.1 • a + q.2 • b := by
        simpa [twoGenLabel] using htlabel.trans hqlabel.symm
      have htx : q.1 + dx = t.1 := by dsimp [dx]; omega
      have hqy : t.2 + dy = q.2 := by dsimp [dy]; omega
      rw [← htx, add_nsmul, ← hqy, add_nsmul] at hraw
      have hcommon : q.1 • a + t.2 • b + dx • a =
          q.1 • a + t.2 • b + dy • b := by
        simpa [add_assoc, add_comm, add_left_comm] using hraw
      exact add_left_cancel hcommon
    have hqxpos : 0 < q.1 := hq.2.1
    have htypos : 0 < t.2 := ht.2.2.1
    have hdxmem : (dx, 0) ∈ canonicalTwoDiagram a b hgen :=
      canonicalTwoDiagram_downward a b hgen ht.2.2.2.1
        (by dsimp [dx]; omega) (Nat.zero_le _)
    have hdymem : (0, dy) ∈ canonicalTwoDiagram a b hgen :=
      canonicalTwoDiagram_downward a b hgen hq.2.2.2.2
        (Nat.zero_le _) (by dsimp [dy]; omega)
    have heq := canonicalTwoRep_unique a b
      ((mem_canonicalTwoDiagram_iff a b hgen _).1 hdxmem)
      ((mem_canonicalTwoDiagram_iff a b hgen _).1 hdymem) haxisLabel
    have heqs : dx = 0 ∧ (0 : ℕ) = dy := by
      simpa only [Prod.mk.injEq] using heq
    omega
  rcases lt_or_gt_of_ne hxne with hxt | htx
  · exact (oriented_contra hq ht hxt).elim
  · exact (oriented_contra ht hq htx).elim

private theorem exists_fst_axis_exit (s : Finset (ℕ × ℕ)) :
    ∃ n : ℕ, (n, 0) ∉ s := by
  let n := s.sup fun p => p.1
  refine ⟨n + 1, ?_⟩
  intro hm
  have hle : n + 1 ≤ n := by
    dsimp [n]
    exact Finset.le_sup (f := fun p : ℕ × ℕ => p.1) hm
  omega

private theorem exists_snd_axis_exit (s : Finset (ℕ × ℕ)) :
    ∃ n : ℕ, (0, n) ∉ s := by
  let n := s.sup fun p => p.2
  refine ⟨n + 1, ?_⟩
  intro hm
  have hle : n + 1 ≤ n := by
    dsimp [n]
    exact Finset.le_sup (f := fun p : ℕ × ℕ => p.2) hm
  omega

/-- First missing cell on the horizontal axis. -/
noncomputable def firstFstAxisExit (s : Finset (ℕ × ℕ)) : ℕ := by
  classical
  exact Nat.find (exists_fst_axis_exit s)

/-- First missing cell on the vertical axis. -/
noncomputable def firstSndAxisExit (s : Finset (ℕ × ℕ)) : ℕ := by
  classical
  exact Nat.find (exists_snd_axis_exit s)

private theorem fstAxisExit_not_mem (s : Finset (ℕ × ℕ)) :
    (firstFstAxisExit s, 0) ∉ s := by
  classical
  exact Nat.find_spec (exists_fst_axis_exit s)

private theorem sndAxisExit_not_mem (s : Finset (ℕ × ℕ)) :
    (0, firstSndAxisExit s) ∉ s := by
  classical
  exact Nat.find_spec (exists_snd_axis_exit s)

private theorem fstAxis_mem_before (s : Finset (ℕ × ℕ))
    {i : ℕ} (hi : i < firstFstAxisExit s) : (i, 0) ∈ s := by
  classical
  by_contra hnot
  exact Nat.find_min (exists_fst_axis_exit s) hi hnot

private theorem sndAxis_mem_before (s : Finset (ℕ × ℕ))
    {j : ℕ} (hj : j < firstSndAxisExit s) : (0, j) ∈ s := by
  classical
  by_contra hnot
  exact Nat.find_min (exists_snd_axis_exit s) hj hnot

/-- A missing cell above two present axis cells dominates an inner corner of a
down-set. -/
theorem exists_innerCorner_below
    (s : Finset (ℕ × ℕ))
    (hdown : ∀ {p q : ℕ × ℕ}, p ∈ s → q.1 ≤ p.1 → q.2 ≤ p.2 → q ∈ s)
    {p : ℕ × ℕ} (hpx : (p.1, 0) ∈ s) (hpy : (0, p.2) ∈ s)
    (hp : p ∉ s) :
    ∃ q : ℕ × ℕ, IsInnerCorner s q ∧ q.1 ≤ p.1 ∧ q.2 ≤ p.2 := by
  induction hsum : p.1 + p.2 using Nat.strong_induction_on generalizing p with
  | h n ih =>
      have hpxpos : 0 < p.1 := by
        by_contra hz
        have peq : p = (0, p.2) := by apply Prod.ext <;> omega
        exact hp (peq ▸ hpy)
      have hpypos : 0 < p.2 := by
        by_contra hz
        have peq : p = (p.1, 0) := by apply Prod.ext <;> omega
        exact hp (peq ▸ hpx)
      by_cases hleft : (p.1 - 1, p.2) ∈ s
      · by_cases hbelow : (p.1, p.2 - 1) ∈ s
        · exact ⟨p, ⟨hp, hpxpos, hpypos, hleft, hbelow⟩, le_rfl, le_rfl⟩
        · have haxisY : (0, p.2 - 1) ∈ s :=
            hdown hpy (by omega) (by omega)
          obtain ⟨q, hq, hqx, hqy⟩ := ih (p.1 + (p.2 - 1)) (by omega)
            (p := (p.1, p.2 - 1)) (by simpa using hpx) haxisY hbelow rfl
          exact ⟨q, hq, hqx, by omega⟩
      · have haxisX : (p.1 - 1, 0) ∈ s :=
          hdown hpx (by omega) (by omega)
        obtain ⟨q, hq, hqx, hqy⟩ := ih ((p.1 - 1) + p.2) (by omega)
          (p := (p.1 - 1, p.2)) haxisX (by simpa using hpy) hleft rfl
        exact ⟨q, hq, by omega, hqy⟩

/-- The origin is canonical for every pair of generators. -/
theorem zero_mem_canonicalTwoDiagram
    {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (a b : G)
    (hgen : ∀ g : G, ∃ p : ℕ × ℕ, twoGenLabel a b p = g) :
    (0, 0) ∈ canonicalTwoDiagram a b hgen := by
  apply (mem_canonicalTwoDiagram_iff a b hgen _).2
  intro q _
  simp only [RepNoLater]
  by_cases hq : q.1 + q.2 = 0
  · right
    omega
  · left
    omega

/-- Every canonical two-generator minimum-distance diagram is a nondegenerate
L-shape (a rectangle is the case `w=y=0`). -/
theorem canonicalTwoDiagram_isLShape
    {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (a b : G)
    (hgen : ∀ g : G, ∃ p : ℕ × ℕ, twoGenLabel a b p = g) :
    ∃ l h w y : ℕ, w < l ∧ y < h ∧
      canonicalTwoDiagram a b hgen = lShapeFinset l h w y := by
  classical
  let s := canonicalTwoDiagram a b hgen
  let l := firstFstAxisExit s
  let h := firstSndAxisExit s
  have hzero : (0, 0) ∈ s := zero_mem_canonicalTwoDiagram a b hgen
  have hlpos : 0 < l := by
    by_contra hz
    have hleq : l = 0 := by omega
    have hm : (l, 0) ∈ s := by simpa [hleq] using hzero
    exact fstAxisExit_not_mem s hm
  have hhpos : 0 < h := by
    by_contra hz
    have hheq : h = 0 := by omega
    have hm : (0, h) ∈ s := by simpa [hheq] using hzero
    exact sndAxisExit_not_mem s hm
  have hdown : ∀ {p q : ℕ × ℕ}, p ∈ s → q.1 ≤ p.1 → q.2 ≤ p.2 → q ∈ s := by
    intro p q hp hqx hqy
    exact canonicalTwoDiagram_downward a b hgen hp hqx hqy
  have hbound : ∀ {p : ℕ × ℕ}, p ∈ s → p.1 < l ∧ p.2 < h := by
    intro p hp
    constructor
    · by_contra hnot
      have hexit : (l, 0) ∈ s := hdown hp (by omega) (by omega)
      exact fstAxisExit_not_mem s hexit
    · by_contra hnot
      have hexit : (0, h) ∈ s := hdown hp (by omega) (by omega)
      exact sndAxisExit_not_mem s hexit
  by_cases hc : ∃ q : ℕ × ℕ, IsInnerCorner s q
  · obtain ⟨q, hq⟩ := hc
    have hqxl : q.1 < l := (hbound hq.2.2.2.2).1
    have hqyh : q.2 < h := (hbound hq.2.2.2.1).2
    let w := l - q.1
    let y := h - q.2
    have hqxpos : 0 < q.1 := hq.2.1
    have hqypos : 0 < q.2 := hq.2.2.1
    have hwl : w < l := by dsimp [w]; omega
    have hyh : y < h := by dsimp [y]; omega
    refine ⟨l, h, w, y, hwl, hyh, ?_⟩
    ext p
    rw [mem_lShapeFinset]
    have hlw : l - w = q.1 := by
      dsimp [w]
      exact Nat.sub_sub_self (Nat.le_of_lt hqxl)
    have hhy : h - y = q.2 := by
      dsimp [y]
      exact Nat.sub_sub_self (Nat.le_of_lt hqyh)
    rw [hlw, hhy]
    constructor
    · intro hp
      have hb := hbound hp
      refine ⟨hb.1, hb.2, ?_⟩
      rintro ⟨hqx, hqy⟩
      exact hq.1 (hdown hp hqx hqy)
    · rintro ⟨hpl, hph, hnq⟩
      by_contra hp
      have hpx : (p.1, 0) ∈ s := fstAxis_mem_before s hpl
      have hpy : (0, p.2) ∈ s := sndAxis_mem_before s hph
      obtain ⟨r, hr, hrx, hry⟩ := exists_innerCorner_below s hdown hpx hpy hp
      have hrq : r = q := innerCorner_unique a b hgen hr hq
      apply hnq
      simpa [hrq] using And.intro hrx hry
  · refine ⟨l, h, 0, 0, hlpos, hhpos, ?_⟩
    ext p
    rw [mem_lShapeFinset]
    constructor
    · intro hp
      have hb := hbound hp
      exact ⟨hb.1, hb.2, by omega⟩
    · rintro ⟨hpl, hph, -⟩
      by_contra hp
      have hpx : (p.1, 0) ∈ s := fstAxis_mem_before s hpl
      have hpy : (0, p.2) ∈ s := sndAxis_mem_before s hph
      obtain ⟨q, hq, -, -⟩ := exists_innerCorner_below s hdown hpx hpy hp
      exact hc ⟨q, hq⟩

/-- Sharp directed degree--diameter bound for every finite abelian group with
two generators: diameter at most `H` implies `3|G| ≤ (H+2)²`. -/
theorem twoGenerator_card_le_third
    {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (a b : G) {H : ℕ}
    (hcover : ∀ g : G, ∃ p : ℕ × ℕ,
      p.1 + p.2 ≤ H ∧ twoGenLabel a b p = g) :
    3 * Fintype.card G ≤ (H + 2) ^ 2 := by
  let hgen : ∀ g : G, ∃ p : ℕ × ℕ, twoGenLabel a b p = g :=
    fun g => let ⟨p, _, hp⟩ := hcover g; ⟨p, hp⟩
  obtain ⟨l, h, w, y, hw, hy, hshape⟩ :=
    canonicalTwoDiagram_isLShape a b hgen
  exact twoGenerator_card_le_third_of_lShape a b hgen hcover hw hy hshape

end Erdos336
