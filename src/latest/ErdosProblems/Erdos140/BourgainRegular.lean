/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos140.RegularBohr

/-!
# Bourgain regular dilates of finite Bohr sets

The first part of this file proves the rank-only relative-volume estimate

`|B_1| ≤ 4^rank(B) |B_{1/2}|`.

The proof is the finite torus-box argument.  We choose the representative of
each circle coordinate in `[-1/2,1/2)`, split the interval allowed by a Bohr
constraint into four cells, and inject every signature fiber into `B_{1/2}`
by subtracting a fixed member of the fiber.
-/

open Finset
open scoped BigOperators NNReal

namespace Erdos140

noncomputable section

namespace BohrData

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## Canonical representatives and four-cell coding -/

/-- The canonical representative of a point of `ℝ / ℤ` in `[-1/2,1/2)`. -/
def circleRep (z : AddCircle (1 : ℝ)) : ℝ :=
  (QuotientAddGroup.equivIcoMod (p := (1 : ℝ)) (by norm_num) (-1 / 2) z).1

lemma circleRep_mem (z : AddCircle (1 : ℝ)) :
    circleRep z ∈ Set.Ico (-1 / 2 : ℝ) (1 / 2) := by
  let e := QuotientAddGroup.equivIcoMod (p := (1 : ℝ)) (by norm_num) (-1 / 2)
  change -1 / 2 ≤ circleRep z ∧ circleRep z < 1 / 2
  constructor
  · exact (e z).2.1
  · have hz := (e z).2.2
    norm_num at hz ⊢
    exact hz

@[simp] lemma circleRep_coe (z : AddCircle (1 : ℝ)) :
    ((circleRep z : ℝ) : AddCircle (1 : ℝ)) = z := by
  let e := QuotientAddGroup.equivIcoMod (p := (1 : ℝ)) (by norm_num) (-1 / 2)
  have h := e.symm_apply_apply z
  change ((circleRep z : ℝ) : AddCircle (1 : ℝ)) = z
  simpa only [e, circleRep, QuotientAddGroup.equivIcoMod_symm_apply] using h

lemma abs_circleRep_le_half (z : AddCircle (1 : ℝ)) : |circleRep z| ≤ 1 / 2 := by
  have hz := circleRep_mem z
  rw [Set.mem_Ico] at hz
  rw [abs_le]
  constructor <;> linarith

lemma norm_eq_abs_circleRep (z : AddCircle (1 : ℝ)) : ‖z‖ = |circleRep z| := by
  calc
    ‖z‖ = ‖((circleRep z : ℝ) : AddCircle (1 : ℝ))‖ := by rw [circleRep_coe]
    _ = |circleRep z| :=
      (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2
        (by simpa using abs_circleRep_le_half z)

lemma norm_sub_le_abs_circleRep_sub (z w : AddCircle (1 : ℝ)) :
    ‖z - w‖ ≤ |circleRep z - circleRep w| := by
  have hcoe :
      (((circleRep z - circleRep w : ℝ) : ℝ) : AddCircle (1 : ℝ)) = z - w := by
    simp
  rw [← hcoe]
  simpa only [Real.norm_eq_abs] using
    (QuotientAddGroup.norm_mk_le_norm
      (S := AddSubgroup.zmultiples (1 : ℝ)) :
        ‖((circleRep z - circleRep w : ℝ) : AddCircle (1 : ℝ))‖ ≤
          ‖circleRep z - circleRep w‖)

/-- Four consecutive cells in `[-w,w]`, each of diameter at most `w/2`.
The definition is total; its diameter property is used only for nonnegative
`w` and inputs in `[-w,w]`. -/
def fourCell (w r : ℝ) : Fin 4 :=
  if r < -(w / 2) then 0
  else if r < 0 then 1
  else if r < w / 2 then 2
  else 3

lemma abs_sub_le_half_of_fourCell_eq {w r s : ℝ}
    (hw : 0 ≤ w) (hr : |r| ≤ w) (hs : |s| ≤ w)
    (hcell : fourCell w r = fourCell w s) :
    |r - s| ≤ w / 2 := by
  rw [abs_le] at hr hs ⊢
  unfold fourCell at hcell
  split_ifs at hcell
  all_goals try { omega }
  all_goals constructor <;> linarith

/-- The four-cell signature of a point in the unit dilate. -/
def unitSignature (B : BohrData G) (x : ↥(B.dilate 1).carrier) :
    B.freq → Fin 4 :=
  fun γ ↦ fourCell (B.width γ.1 : ℝ) (circleRep (γ.1 x.1))

private lemma sub_mem_half_of_unitSignature_eq (B : BohrData G)
    {x y : ↥(B.dilate 1).carrier}
    (hxy : B.unitSignature x = B.unitSignature y) :
    x.1 - y.1 ∈ (B.dilate (1 / 2)).carrier := by
  rw [mem_carrier]
  intro γ hγ
  have hx := (mem_carrier (B.dilate 1) x.1).mp x.2 γ hγ
  have hy := (mem_carrier (B.dilate 1) y.1).mp y.2 γ hγ
  simp only [width_dilate, one_mul, NNReal.coe_one, NNReal.coe_mul] at hx hy ⊢
  rw [map_sub]
  have hxrep : |circleRep (γ x.1)| ≤ (B.width γ : ℝ) := by
    rwa [← norm_eq_abs_circleRep]
  have hyrep : |circleRep (γ y.1)| ≤ (B.width γ : ℝ) := by
    rwa [← norm_eq_abs_circleRep]
  have hcoord := congrFun hxy ⟨γ, hγ⟩
  calc
    ‖γ x.1 - γ y.1‖ ≤ |circleRep (γ x.1) - circleRep (γ y.1)| :=
      norm_sub_le_abs_circleRep_sub _ _
    _ ≤ (B.width γ : ℝ) / 2 :=
      abs_sub_le_half_of_fourCell_eq (by positivity) hxrep hyrep hcoord
    _ = ((1 / 2 : NNReal) : ℝ) * (B.width γ : ℝ) := by
      norm_num
      ring

private lemma card_unitSignature_fiber_le (B : BohrData G)
    (a : B.freq → Fin 4) :
    Fintype.card {x : ↥(B.dilate 1).carrier // B.unitSignature x = a} ≤
      (B.dilate (1 / 2)).carrier.card := by
  classical
  by_cases hfiber : Nonempty
      {x : ↥(B.dilate 1).carrier // B.unitSignature x = a}
  · let x₀ : {x : ↥(B.dilate 1).carrier // B.unitSignature x = a} :=
      Classical.choice hfiber
    let f : {x : ↥(B.dilate 1).carrier // B.unitSignature x = a} →
        ↥(B.dilate (1 / 2)).carrier :=
      fun x ↦ ⟨x.1.1 - x₀.1.1, sub_mem_half_of_unitSignature_eq B
        (x.2.trans x₀.2.symm)⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      have hval := congr_arg (fun z ↦ z.1) hxy
      dsimp [f] at hval
      exact sub_left_injective hval
    calc
      Fintype.card {x : ↥(B.dilate 1).carrier // B.unitSignature x = a} ≤
          Fintype.card ↥(B.dilate (1 / 2)).carrier :=
        Fintype.card_le_of_injective f hf
      _ = (B.dilate (1 / 2)).carrier.card := Fintype.card_coe _
  · simp only [not_nonempty_iff] at hfiber
    simp

/-- Rank-only relative volume growth between the half and unit dilates. -/
theorem card_unit_le_four_pow_rank_mul_card_half (B : BohrData G) :
    (B.dilate 1).carrier.card ≤
      4 ^ B.rank * (B.dilate (1 / 2)).carrier.card := by
  classical
  let S := B.freq → Fin 4
  let q : ↥(B.dilate 1).carrier → S := B.unitSignature
  have hfiber : ∀ a : S,
      Fintype.card {x : ↥(B.dilate 1).carrier // q x = a} ≤
        (B.dilate (1 / 2)).carrier.card := by
    intro a
    exact card_unitSignature_fiber_le B a
  have hcardS : Fintype.card S = 4 ^ B.rank := by
    dsimp [S, rank]
    rw [Fintype.card_pi]
    simp
  rw [← Fintype.card_coe (B.dilate 1).carrier, ← hcardS]
  by_contra h
  have hlt :
      Fintype.card S * (B.dilate (1 / 2)).carrier.card <
        Fintype.card ↥(B.dilate 1).carrier := by omega
  obtain ⟨a, ha⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (f := q) hlt
  have hfa : #{x | q x = a} ≤ (B.dilate (1 / 2)).carrier.card := by
    rw [← Fintype.card_subtype]
    exact hfiber a
  exact (not_lt_of_ge hfa) ha

/-- A buffered version of the relative-volume estimate.  It is convenient in
the regular-value argument because every permitted perturbation of a scale in
`[1/2,1]` remains between `1/4` and `2`. -/
theorem card_two_le_four_pow_three_rank_mul_card_quarter (B : BohrData G) :
    (B.dilate 2).carrier.card ≤
      4 ^ (3 * B.rank) * (B.dilate (1 / 4)).carrier.card := by
  have h₂ := card_unit_le_four_pow_rank_mul_card_half (B.dilate 2)
  have h₁ := card_unit_le_four_pow_rank_mul_card_half B
  have hhalf := card_unit_le_four_pow_rank_mul_card_half (B.dilate (1 / 2))
  simp only [rank_dilate, dilate_dilate, mul_one] at h₂ hhalf
  norm_num at h₂ hhalf
  calc
    (B.dilate 2).carrier.card ≤ 4 ^ B.rank * B.carrier.card := h₂
    _ ≤ 4 ^ B.rank * (4 ^ B.rank * (B.dilate (1 / 2)).carrier.card) := by
      gcongr
      simpa using h₁
    _ ≤ 4 ^ B.rank *
        (4 ^ B.rank * (4 ^ B.rank * (B.dilate (1 / 4)).carrier.card)) := by
      gcongr
    _ = 4 ^ (3 * B.rank) * (B.dilate (1 / 4)).carrier.card := by
      rw [← mul_assoc, ← pow_add, ← mul_assoc, ← pow_add]
      congr 2
      omega

/-! ## The one-dimensional regular-value lemma -/

/-- A monotone function whose total growth on a buffered interval is less
than `5` has a point in `[1/2,1]` at which every secant contained in the
buffer has slope at most `60`.

This is Bourgain's finite-growth argument.  If every point were bad, attach
to it a bad secant interval.  Vitali selects disjoint intervals whose
six-fold open enlargements cover `[1/2,1]`.  Hence their total length is at
least `1/12`; badness makes the sum of the corresponding increments greater
than `5`, while disjointness and monotonicity telescope that sum below the
total growth. -/
private theorem exists_regular_point_of_monotone
    (f : ℝ → ℝ) (hf : Monotone f)
    (hgrowth : f (5 / 4) - f (1 / 4) < 5) :
    ∃ x ∈ Set.Icc (1 / 2 : ℝ) 1,
      ∀ y ∈ Set.Icc (1 / 4 : ℝ) (5 / 4),
        |f y - f x| ≤ 60 * |y - x| := by
  classical
  by_contra! hregular
  let Bad : Set (ℝ × ℝ) := {p |
    1 / 4 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 5 / 4 ∧
      60 * (p.2 - p.1) < f p.2 - f p.1}
  let center : (ℝ × ℝ) → ℝ := fun p ↦ (p.1 + p.2) / 2
  let radius : (ℝ × ℝ) → ℝ := fun p ↦ (p.2 - p.1) / 2
  have hradius_pos {p : ℝ × ℝ} (hp : p ∈ Bad) : 0 < radius p := by
    dsimp [Bad] at hp
    dsimp [radius]
    linarith
  have hradius_le (p : ℝ × ℝ) (hp : p ∈ Bad) : radius p ≤ 1 / 2 := by
    dsimp [Bad] at hp
    dsimp [radius]
    linarith
  obtain ⟨u, huBad, huDisjoint, huCover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
      Bad center radius (1 / 2) hradius_le 5 (by norm_num)
  have hcentralCover : Set.Icc (1 / 2 : ℝ) 1 ⊆
      ⋃ b : ↥u, Metric.ball (center b.1) (6 * radius b.1) := by
    intro x hx
    obtain ⟨y, hybuf, hxy⟩ := hregular x hx
    let p : ℝ × ℝ := (min x y, max x y)
    have hpbuf : p ∈ Bad := by
      dsimp [Bad, p]
      have hxbuf : x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4) := by
        constructor <;> linarith [hx.1, hx.2]
      rcases le_total x y with hle | hle
      · simp only [min_eq_left hle, max_eq_right hle]
        have habs : |f y - f x| = f y - f x :=
          abs_of_nonneg (sub_nonneg.mpr (hf hle))
        have hdist : |y - x| = y - x := abs_of_nonneg (sub_nonneg.mpr hle)
        rw [habs, hdist] at hxy
        exact ⟨hxbuf.1, lt_of_not_ge (fun heq ↦ by
          have : y = x := le_antisymm heq hle
          subst y
          norm_num at hxy), hybuf.2, hxy⟩
      · simp only [min_eq_right hle, max_eq_left hle]
        have habs : |f y - f x| = f x - f y := by
          rw [abs_sub_comm]
          exact abs_of_nonneg (sub_nonneg.mpr (hf hle))
        have hdist : |y - x| = x - y := by
          rw [abs_sub_comm]
          exact abs_of_nonneg (sub_nonneg.mpr hle)
        rw [habs, hdist] at hxy
        exact ⟨hybuf.1, lt_of_not_ge (fun heq ↦ by
          have : x = y := le_antisymm heq hle
          subst y
          norm_num at hxy), hxbuf.2, hxy⟩
    obtain ⟨b, hbu, hsub⟩ := huCover p hpbuf
    have hxp : x ∈ Metric.closedBall (center p) (radius p) := by
      rw [Real.closedBall_eq_Icc]
      dsimp [center, radius, p]
      constructor <;> rcases le_total x y with hle | hle <;>
        simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, hle] <;> linarith
    have hxb : x ∈ Metric.closedBall (center b) (5 * radius b) := hsub hxp
    rw [Metric.mem_closedBall] at hxb
    rw [Set.mem_iUnion]
    refine ⟨⟨b, hbu⟩, ?_⟩
    rw [Metric.mem_ball]
    have hbr : 0 < radius b := hradius_pos (huBad hbu)
    linarith
  obtain ⟨v, hvCover⟩ := isCompact_Icc.elim_finite_subcover
    (fun b : ↥u ↦ Metric.ball (center b.1) (6 * radius b.1))
    (fun _ ↦ Metric.isOpen_ball) hcentralCover
  have hv_nonempty : v.Nonempty := by
    by_contra hv
    rw [Finset.not_nonempty_iff_eq_empty] at hv
    simpa [hv] using hvCover (show (1 / 2 : ℝ) ∈ Set.Icc (1 / 2) 1 by norm_num)
  have hvolume : (1 / 2 : ℝ) ≤ 6 * ∑ b ∈ v, (b.1.2 - b.1.1) := by
    have hm : MeasureTheory.volume (Set.Icc (1 / 2 : ℝ) 1) ≤
        MeasureTheory.volume (⋃ b ∈ v,
          Metric.ball (center b.1) (6 * radius b.1)) :=
      MeasureTheory.measure_mono hvCover
    have hright : 0 ≤ 6 * ∑ b ∈ v, (b.1.2 - b.1.1) := by
      apply mul_nonneg (by norm_num)
      apply Finset.sum_nonneg
      intro b hb
      have := hradius_pos (huBad b.2)
      dsimp [radius] at this
      linarith
    rw [← ENNReal.ofReal_le_ofReal_iff hright]
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) =
        MeasureTheory.volume (Set.Icc (1 / 2 : ℝ) 1) := by
      rw [Real.volume_Icc]
      norm_num
    rw [hhalf]
    calc
      MeasureTheory.volume (Set.Icc (1 / 2 : ℝ) 1) ≤
          MeasureTheory.volume (⋃ b ∈ v,
            Metric.ball (center b.1) (6 * radius b.1)) := hm
      _ ≤ ∑ b ∈ v, MeasureTheory.volume
          (Metric.ball (center b.1) (6 * radius b.1)) :=
        MeasureTheory.measure_biUnion_finset_le v _
      _ = ENNReal.ofReal (6 * ∑ b ∈ v, (b.1.2 - b.1.1)) := by
        simp only [Real.volume_ball]
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · congr 1
          simp only [center, radius]
          calc
            ∑ b ∈ v, 2 * (6 * ((b.1.2 - b.1.1) / 2)) =
                ∑ b ∈ v, 6 * (b.1.2 - b.1.1) := by
              apply Finset.sum_congr rfl
              intro b hb
              ring
            _ = 6 * ∑ b ∈ v, (b.1.2 - b.1.1) := by
              rw [Finset.mul_sum]
        · intro b hb
          have := hradius_pos (huBad b.2)
          dsimp [radius] at this
          positivity
      _ = ENNReal.ofReal (6 * ∑ b ∈ v, (b.1.2 - b.1.1)) := rfl
  let e : ↥u ↪ (ℝ × ℝ) := ⟨Subtype.val, Subtype.val_injective⟩
  let F : Finset (ℝ × ℝ) := v.map e
  have hball (p : ℝ × ℝ) :
      Metric.closedBall (center p) (radius p) = Set.Icc p.1 p.2 := by
    rw [Real.closedBall_eq_Icc]
    dsimp [center, radius]
    congr <;> ring
  have hF_bounds : ∀ ⦃z⦄, z ∈ F →
      (1 / 4 : ℝ) ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ 5 / 4 := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hz
    have hbad := huBad b.2
    dsimp [Bad] at hbad
    exact ⟨hbad.1, hbad.2.1.le, hbad.2.2.1⟩
  have hF_disjoint : (SetLike.coe F).PairwiseDisjoint
      (fun z ↦ Set.Icc z.1 z.2) := by
    intro z hz w hw hzw
    obtain ⟨bz, hbz, rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨bw, hbw, rfl⟩ := Finset.mem_map.mp hw
    have hne : (bz : ℝ × ℝ) ≠ bw := by
      simpa [e] using hzw
    have hd := huDisjoint bz.2 bw.2 hne
    change Disjoint (Metric.closedBall (center bz) (radius bz))
      (Metric.closedBall (center bw) (radius bw)) at hd
    rw [hball, hball] at hd
    simpa [e] using hd
  have hsum_le : ∑ z ∈ F, (f z.2 - f z.1) ≤ f (5 / 4) - f (1 / 4) := by
    have htel := F.sum_intervalGapsWithin_add_sum_eq_sub rfl
      (a := (1 / 4 : ℝ)) (b := (5 / 4 : ℝ)) f
    calc
      ∑ z ∈ F, (f z.2 - f z.1) ≤ _ := by
        rw [le_add_iff_nonneg_left]
        apply Finset.sum_nonneg
        intro i hi
        apply sub_nonneg.mpr
        apply hf
        exact F.intervalGapsWithin_fst_le_snd rfl _ (by norm_num)
          hF_bounds hF_disjoint
      _ = f (5 / 4) - f (1 / 4) := htel
  have hbad_sum : 60 * ∑ b ∈ v, (b.1.2 - b.1.1) <
      ∑ z ∈ F, (f z.2 - f z.1) := by
    rw [Finset.sum_map]
    simp only [e, Function.Embedding.coeFn_mk]
    rw [Finset.mul_sum]
    exact Finset.sum_lt_sum_of_nonempty hv_nonempty
      (fun b hb ↦ (huBad b.2).2.2.2)
  linarith

private theorem log_card_growth_lt_five_mul_rank (B : BohrData G) :
    Real.log ((B.dilate (5 / 4)).carrier.card : ℝ) -
        Real.log ((B.dilate (1 / 4)).carrier.card : ℝ) <
      5 * (max B.rank 1 : ℕ) := by
  let d : ℕ := max B.rank 1
  have hcard : (B.dilate (5 / 4)).carrier.card ≤
      4 ^ (3 * B.rank) * (B.dilate (1 / 4)).carrier.card := by
    calc
      (B.dilate (5 / 4)).carrier.card ≤ (B.dilate 2).carrier.card :=
        Finset.card_le_card (carrier_dilate_mono
          (show (5 / 4 : NNReal) ≤ 2 by
            rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 4)]
            norm_num))
      _ ≤ 4 ^ (3 * B.rank) * (B.dilate (1 / 4)).carrier.card :=
        card_two_le_four_pow_three_rank_mul_card_quarter B
  have hsmall_pos : (0 : ℝ) < (B.dilate (1 / 4)).carrier.card := by
    exact_mod_cast (B.dilate (1 / 4)).carrier_nonempty.card_pos
  have hlarge_pos : (0 : ℝ) < (B.dilate (5 / 4)).carrier.card := by
    exact_mod_cast (B.dilate (5 / 4)).carrier_nonempty.card_pos
  have hlog := Real.log_le_log hlarge_pos (show
      ((B.dilate (5 / 4)).carrier.card : ℝ) ≤
        ((4 ^ (3 * B.rank) * (B.dilate (1 / 4)).carrier.card : ℕ) : ℝ) by
      exact_mod_cast hcard)
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) hsmall_pos.ne',
    Real.log_pow] at hlog
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast (show 0 < d by simp [d])
  have hrank_le : (B.rank : ℝ) ≤ d := by
    exact_mod_cast (le_max_left B.rank 1)
  have hlog4 : Real.log (4 : ℝ) < 5 / 3 := by
    rw [Real.log_four_eq]
    linarith [Real.log_two_lt_d9]
  have hmain : (3 * B.rank : ℕ) * Real.log (4 : ℝ) < 5 * d := by
    push_cast
    calc
      3 * (B.rank : ℝ) * Real.log 4 ≤ 3 * d * Real.log 4 := by
        gcongr
      _ < 3 * d * (5 / 3) := by gcongr
      _ = 5 * d := by ring
  dsimp [d] at hmain ⊢
  linarith

/-- The normalized log-cardinality of the real-scale dilates. -/
private noncomputable def normalizedLogCard (B : BohrData G) (s : ℝ) : ℝ :=
  Real.log ((B.dilate s.toNNReal).carrier.card : ℝ) /
    (max B.rank 1 : ℕ)

private theorem normalizedLogCard_monotone (B : BohrData G) :
    Monotone B.normalizedLogCard := by
  intro s t hst
  dsimp [normalizedLogCard]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.log_le_log
  · exact_mod_cast (B.dilate s.toNNReal).carrier_nonempty.card_pos
  · exact_mod_cast Finset.card_le_card
      (carrier_dilate_mono (B := B) (Real.toNNReal_mono hst))

private theorem normalizedLogCard_buffer_growth (B : BohrData G) :
    B.normalizedLogCard (5 / 4) - B.normalizedLogCard (1 / 4) < 5 := by
  have h := log_card_growth_lt_five_mul_rank B
  have hd : (0 : ℝ) < (max B.rank 1 : ℕ) := by positivity
  have h54 : Real.toNNReal (5 / 4 : ℝ) = (5 / 4 : NNReal) := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (by norm_num)]
    norm_num
  have h14 : Real.toNNReal (1 / 4 : ℝ) = (1 / 4 : NNReal) := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (by norm_num)]
    norm_num
  dsimp [normalizedLogCard]
  rw [h54, h14]
  rw [div_sub_div_same]
  exact (div_lt_iff₀ hd).2 (by simpa [mul_comm] using h)

/-- **Bourgain regular-dilate theorem.** Every finite Bohr datum has a
rank-regular scalar dilate at a scale between `1/2` and `1`. -/
theorem exists_rankRegular_dilate (B : BohrData G) :
    ∃ rho : NNReal, 1 / 2 ≤ rho ∧ rho ≤ 1 ∧
      (B.dilate rho).IsRankRegular := by
  let d : ℕ := max B.rank 1
  obtain ⟨r, hr, hlip⟩ := exists_regular_point_of_monotone
    B.normalizedLogCard (normalizedLogCard_monotone B)
      (normalizedLogCard_buffer_growth B)
  let rho : NNReal := r.toNNReal
  have hrho : (rho : ℝ) = r := Real.coe_toNNReal r (by linarith [hr.1])
  have hrho_half : (1 / 2 : NNReal) ≤ rho := by
    rw [← NNReal.coe_le_coe, hrho]
    norm_num
    exact hr.1
  have hrho_one : rho ≤ 1 := by
    rw [← NNReal.coe_le_coe, hrho]
    norm_num
    exact hr.2
  refine ⟨rho, hrho_half, hrho_one, ?_⟩
  rw [isRankRegular_dilate_iff]
  dsimp only [rank_dilate]
  intro kappa hkappa
  have hdposN : 0 < d := by simp [d]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hdposN
  have hkappa_one : kappa ≤ 1 := by
    apply hkappa.trans
    rw [div_le_one]
    · exact_mod_cast (show 1 ≤ 100 * d by omega)
    · positivity
  have hkappa_real : (kappa : ℝ) ≤ 1 / (100 * (d : ℝ)) := by
    exact_mod_cast hkappa
  let sminus : NNReal := (1 - kappa) * rho
  let splus : NNReal := (1 + kappa) * rho
  have hkreal : (kappa : ℝ) ≤ 1 / 100 := by
    calc
      (kappa : ℝ) ≤ 1 / (100 * (d : ℝ)) := hkappa_real
      _ ≤ 1 / 100 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        have hd_one : (1 : ℝ) ≤ d := by
          exact_mod_cast (show 1 ≤ d by simp [d])
        nlinarith
  have hrho_real : (1 / 2 : ℝ) ≤ rho ∧ (rho : ℝ) ≤ 1 := by
    exact ⟨by exact_mod_cast hrho_half, by exact_mod_cast hrho_one⟩
  have hsminus_buf : (sminus : ℝ) ∈ Set.Icc (1 / 4 : ℝ) (5 / 4) := by
    dsimp [sminus]
    rw [NNReal.coe_sub hkappa_one]
    simp only [NNReal.coe_one]
    have hk_lower : (99 / 100 : ℝ) ≤ 1 - (kappa : ℝ) := by
      nlinarith
    constructor
    · calc
        (1 / 4 : ℝ) ≤ (99 / 100) * (1 / 2) := by norm_num
        _ ≤ (1 - (kappa : ℝ)) * (rho : ℝ) := by
          exact mul_le_mul hk_lower hrho_real.1 (by norm_num)
            (sub_nonneg.mpr (by exact_mod_cast hkappa_one))
    · calc
        (1 - (kappa : ℝ)) * (rho : ℝ) ≤ 1 * rho :=
          mul_le_mul_of_nonneg_right (sub_le_self 1 (by positivity)) (by positivity)
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hrho_real.2 (by norm_num)
        _ ≤ 5 / 4 := by norm_num
  have hsplus_buf : (splus : ℝ) ∈ Set.Icc (1 / 4 : ℝ) (5 / 4) := by
    dsimp [splus]
    push_cast
    constructor <;> nlinarith
  have hdistminus : |(sminus : ℝ) - r| ≤ (kappa : ℝ) := by
    rw [← hrho]
    dsimp [sminus]
    rw [NNReal.coe_sub hkappa_one]
    simp only [NNReal.coe_one]
    change |(1 - (kappa : ℝ)) * (rho : ℝ) - (rho : ℝ)| ≤ (kappa : ℝ)
    have hrnonneg : (0 : ℝ) ≤ rho := by positivity
    rw [show (1 - (kappa : ℝ)) * (rho : ℝ) - rho = -(kappa * rho) by ring,
      abs_neg, abs_of_nonneg (mul_nonneg (by positivity) hrnonneg)]
    nlinarith [hrho_real.2]
  have hdistplus : |(splus : ℝ) - r| ≤ (kappa : ℝ) := by
    rw [← hrho]
    dsimp [splus]
    push_cast
    have hrnonneg : (0 : ℝ) ≤ rho := by positivity
    rw [show (1 + (kappa : ℝ)) * (rho : ℝ) - rho = kappa * rho by ring,
      abs_of_nonneg (mul_nonneg (by positivity) hrnonneg)]
    nlinarith [hrho_real.2]
  have hlipminus := hlip (sminus : ℝ) hsminus_buf
  have hlipplus := hlip (splus : ℝ) hsplus_buf
  simp only [normalizedLogCard, Real.toNNReal_coe,
    show r.toNNReal = rho by rfl] at hlipminus hlipplus
  change
    |Real.log ((B.dilate sminus).carrier.card : ℝ) / d -
      Real.log ((B.dilate rho).carrier.card : ℝ) / d| ≤
        60 * |(sminus : ℝ) - r| at hlipminus
  change
    |Real.log ((B.dilate splus).carrier.card : ℝ) / d -
      Real.log ((B.dilate rho).carrier.card : ℝ) / d| ≤
        60 * |(splus : ℝ) - r| at hlipplus
  rw [div_sub_div_same, abs_div, abs_of_pos hdpos] at hlipminus hlipplus
  have hlogminus :
      Real.log ((B.dilate rho).carrier.card : ℝ) -
          Real.log ((B.dilate sminus).carrier.card : ℝ) ≤
        60 * d * (kappa : ℝ) := by
    have habs := (div_le_iff₀ hdpos).mp hlipminus
    calc
      _ ≤ |Real.log ((B.dilate sminus).carrier.card : ℝ) -
          Real.log ((B.dilate rho).carrier.card : ℝ)| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      _ ≤ 60 * |(sminus : ℝ) - r| * d := habs
      _ ≤ 60 * (kappa : ℝ) * d := by gcongr
      _ = 60 * d * (kappa : ℝ) := by ring
  have hlogplus :
      Real.log ((B.dilate splus).carrier.card : ℝ) -
          Real.log ((B.dilate rho).carrier.card : ℝ) ≤
        60 * d * (kappa : ℝ) := by
    have habs := (div_le_iff₀ hdpos).mp hlipplus
    calc
      _ ≤ |Real.log ((B.dilate splus).carrier.card : ℝ) -
          Real.log ((B.dilate rho).carrier.card : ℝ)| := le_abs_self _
      _ ≤ 60 * |(splus : ℝ) - r| * d := habs
      _ ≤ 60 * (kappa : ℝ) * d := by gcongr
      _ = 60 * d * (kappa : ℝ) := by ring
  let u : ℝ := 100 * d * (kappa : ℝ)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    calc
      100 * (d : ℝ) * (kappa : ℝ) ≤
          100 * d * (1 / (100 * d)) := by gcongr
      _ = 1 := by field_simp
  have hslope : 60 * d * (kappa : ℝ) = (3 / 5 : ℝ) * u := by
    dsimp [u]
    ring
  constructor
  · change (1 - u) * ((B.dilate rho).carrier.card : ℝ) ≤
      ((B.dilate sminus).carrier.card : ℝ)
    by_cases hu : u = 1
    · rw [hu]
      norm_num
    · have hu_lt : u < 1 := lt_of_le_of_ne hu1 hu
      have honeu : 0 < 1 - u := sub_pos.mpr hu_lt
      have hcenter : (0 : ℝ) < (B.dilate rho).carrier.card := by
        exact_mod_cast (B.dilate rho).carrier_nonempty.card_pos
      have hinner : (0 : ℝ) < (B.dilate sminus).carrier.card := by
        exact_mod_cast (B.dilate sminus).carrier_nonempty.card_pos
      rw [← Real.log_le_log_iff (mul_pos honeu hcenter) hinner]
      rw [Real.log_mul (sub_ne_zero.mpr (Ne.symm hu)) hcenter.ne']
      have hlogone := Real.log_le_sub_one_of_pos honeu
      rw [hslope] at hlogminus
      nlinarith
  · change ((B.dilate splus).carrier.card : ℝ) ≤
      (1 + u) * ((B.dilate rho).carrier.card : ℝ)
    have hcenter : (0 : ℝ) < (B.dilate rho).carrier.card := by
      exact_mod_cast (B.dilate rho).carrier_nonempty.card_pos
    have houter : (0 : ℝ) < (B.dilate splus).carrier.card := by
      exact_mod_cast (B.dilate splus).carrier_nonempty.card_pos
    rw [← Real.log_le_log_iff houter (mul_pos (by linarith) hcenter)]
    rw [Real.log_mul (by linarith) hcenter.ne']
    have hlogone := Real.le_log_one_add_of_nonneg hu0
    have hfrac : (3 / 5 : ℝ) * u ≤ 2 * u / (u + 2) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    rw [hslope] at hlogplus
    linarith

/-- A rank-controlled regular dilate together with the standard
small-translation `L¹` bound for its normalized indicator. -/
theorem exists_rankRegular_dilate_with_translation_bound (B : BohrData G) :
    ∃ rho : NNReal, 1 / 2 ≤ rho ∧ rho ≤ 1 ∧
      ∀ kappa : NNReal,
        kappa ≤ 1 / (100 * (max B.rank 1 : ℕ) : NNReal) →
        ∀ t : G, t ∈ ((B.dilate rho).dilate kappa).carrier →
          ∑ x : G,
              |normalizedIndicator (B.dilate rho).carrier (x - t) -
                normalizedIndicator (B.dilate rho).carrier x| ≤
            200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ) := by
  obtain ⟨rho, hrho0, hrho1, hreg⟩ := exists_rankRegular_dilate B
  refine ⟨rho, hrho0, hrho1, ?_⟩
  intro kappa hkappa t ht
  simpa using sum_abs_normalizedIndicator_translate_le_of_rankRegular
    hreg hkappa ht

end BohrData

end

end Erdos140

#print axioms Erdos140.BohrData.card_unit_le_four_pow_rank_mul_card_half
#print axioms Erdos140.BohrData.card_two_le_four_pow_three_rank_mul_card_quarter
#print axioms Erdos140.BohrData.exists_rankRegular_dilate
#print axioms Erdos140.BohrData.exists_rankRegular_dilate_with_translation_bound
