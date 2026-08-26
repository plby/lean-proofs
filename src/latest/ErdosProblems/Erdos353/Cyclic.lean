/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 353.
Informal authors: Vjekoslav Kovač, Bruno Predojević.
Formal authors: Aristotle, JoshuaB.
Original Lean/Mathlib version: 4.28.0.
Source: https://www.erdosproblems.com/forum/thread/353#post-7095
Exact editor URL: data/urls.yaml, JoshuaB_353_cyclic.
-/
import Mathlib

open MeasureTheory Filter Topology
open scoped BigOperators Real

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Erdos353

namespace CyclicQuad
/- ===================== Defs ===================== -/
/-- A point of the Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)
/-- Signed orientation (twice the signed area) of the triangle `X Y Z`. -/
noncomputable def orient (X Y Z : Pt) : ℝ :=
  (Y 0 - X 0) * (Z 1 - X 1) - (Z 0 - X 0) * (Y 1 - X 1)
/-- Signed area of the quadrilateral with vertices `P Q R S` in this order (shoelace formula). -/
noncomputable def quadArea (P Q R S : Pt) : ℝ :=
  ((P 0 * Q 1 - Q 0 * P 1) + (Q 0 * R 1 - R 0 * Q 1) +
   (R 0 * S 1 - S 0 * R 1) + (S 0 * P 1 - P 0 * S 1)) / 2
/-- Four points are concyclic: they lie on a common circle of positive radius. -/
def Concyclic4 (P Q R S : Pt) : Prop :=
  ∃ (O : Pt) (r : ℝ), 0 < r ∧ dist P O = r ∧ dist Q O = r ∧ dist R O = r ∧ dist S O = r
/-- `P Q R S` form a strictly convex counterclockwise quadrilateral (all turns are left turns). -/
def ConvexQuadCCW (P Q R S : Pt) : Prop :=
  0 < orient P Q R ∧ 0 < orient Q R S ∧ 0 < orient R S P ∧ 0 < orient S P Q
/-- `P Q R S` are the vertices of a (non-degenerate) cyclic quadrilateral of area `1`,
listed in their convex counterclockwise cyclic order. -/
def UnitCyclicQuad (P Q R S : Pt) : Prop :=
  Concyclic4 P Q R S ∧ ConvexQuadCCW P Q R S ∧ quadArea P Q R S = 1
/-- An orientation-preserving rigid motion of the plane (rotation by `(a,b)` with `a²+b²=1`
followed by the translation `(v₁,v₂)`). -/
noncomputable def rigid (a b v1 v2 : ℝ) (p : Pt) : Pt :=
  !₂[a * p 0 - b * p 1 + v1, b * p 0 + a * p 1 + v2]
/-- `C` is a Lebesgue density point of `S` (using closed balls, as in Besicovitch's theorem). -/
def IsDensityPt (S : Set Pt) (C : Pt) : Prop :=
  Tendsto (fun r : ℝ => volume (S ∩ Metric.closedBall C r) / volume (Metric.closedBall C r))
    (𝓝[>] 0) (𝓝 1)
/-- The geometric configuration produced by the first half of the proof:
a non-degenerate triangle `A=(0,0)`, `B=(c,0)`, `C=(xC,yC)` of area `1` with vertices in `S`,
and with `C` a density point of `S`. -/
structure Config (S : Set Pt) (c xC yC : ℝ) : Prop where
  c_pos : 0 < c
  yC_pos : 0 < yC
  /-- `area △ABC = 1`, i.e. `c·yC = 2`. -/
  area : c * yC = 2
  memA : (!₂[(0 : ℝ), (0 : ℝ)] : Pt) ∈ S
  memB : (!₂[c, (0 : ℝ)] : Pt) ∈ S
  memC : (!₂[xC, yC] : Pt) ∈ S
  meas : MeasurableSet S
  dens : IsDensityPt S (!₂[xC, yC] : Pt)
/-- The signed orientation is invariant under orientation-preserving rigid motions. -/
lemma orient_rigid {a b v1 v2 : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (X Y Z : Pt) :
    orient (rigid a b v1 v2 X) (rigid a b v1 v2 Y) (rigid a b v1 v2 Z) = orient X Y Z := by
  classical
  unfold orient rigid; norm_num
  linear_combination ((Y 0 - X 0) * (Z 1 - X 1) - (Z 0 - X 0) * (Y 1 - X 1)) * hab
/-- The shoelace area is invariant under orientation-preserving rigid motions. -/
lemma quadArea_rigid {a b v1 v2 : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (P Q R S : Pt) :
    quadArea (rigid a b v1 v2 P) (rigid a b v1 v2 Q) (rigid a b v1 v2 R) (rigid a b v1 v2 S)
      = quadArea P Q R S := by
  classical
  unfold quadArea
  unfold rigid; norm_num [Fin.sum_univ_succ]; ring_nf
  rw [show b ^ 2 = 1 - a ^ 2 by linarith]; ring
/-- A rigid motion is an isometry. -/
lemma dist_rigid {a b v1 v2 : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (P Q : Pt) :
    dist (rigid a b v1 v2 P) (rigid a b v1 v2 Q) = dist P Q := by
  classical
  norm_num [dist_eq_norm, EuclideanSpace.norm_eq, rigid]
  congr 1
  linear_combination ((P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2) * hab
/-- Being the vertices of a unit cyclic quadrilateral is invariant under orientation-preserving
rigid motions. -/
lemma unitCyclicQuad_rigid_iff {a b v1 v2 : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (P Q R S : Pt) :
    UnitCyclicQuad (rigid a b v1 v2 P) (rigid a b v1 v2 Q) (rigid a b v1 v2 R)
        (rigid a b v1 v2 S)
      ↔ UnitCyclicQuad P Q R S := by
  classical
  constructor <;> intro h
  · refine ⟨?_, ?_, ?_⟩
    · obtain ⟨O, r, hr, hO⟩ := h.1
      have h_surjective : ∀ O' : Pt, ∃ O : Pt, rigid a b v1 v2 O = O' := by
        intro O'
        use !₂[a * (O' 0 - v1) + b * (O' 1 - v2), -b * (O' 0 - v1) + a * (O' 1 - v2)]
        ext i; fin_cases i <;> norm_num [rigid] <;> ring_nf
        · linear_combination' hab * O'.ofLp 0 - hab * v1
        · linear_combination' hab * O'.ofLp 1 - hab * v2
      obtain ⟨O', rfl⟩ := h_surjective O
      exact ⟨O', r, hr, by simpa [dist_rigid hab] using hO⟩
    · exact ⟨by simpa [orient_rigid hab] using h.2.1.1,
        by simpa [orient_rigid hab] using h.2.1.2.1,
        by simpa [orient_rigid hab] using h.2.1.2.2.1,
        by simpa [orient_rigid hab] using h.2.1.2.2.2⟩
    · exact h.2.2 ▸ quadArea_rigid hab P Q R S ▸ rfl
  · constructor
    · obtain ⟨O, r, hr, hO⟩ := h.1
      exact ⟨rigid a b v1 v2 O, r, hr, by simpa [dist_rigid hab] using hO⟩
    · exact ⟨by simpa [ConvexQuadCCW, orient_rigid hab] using h.2.1,
        by rw [quadArea_rigid hab]; exact h.2.2⟩
/- ===================== Config ===================== -/
/-- The closed "upper" right-angled sector `{ p : |p₀| ≤ p₁ }`.  The part of this sector below any
horizontal line is a bounded triangle, hence of finite area. -/
def sectorUp : Set Pt := {p : Pt | |p 0| ≤ p 1}
/-
`rigid` is continuous.
-/
lemma continuous_rigid (a b v1 v2 : ℝ) : Continuous (rigid a b v1 v2) := by
  classical
  refine' Continuous.comp _ _;
  · fun_prop (disch := norm_num);
  · refine' continuous_pi_iff.mpr _;
    intro i; fin_cases i <;> apply_rules [ Continuous.sub, Continuous.add, Continuous.mul, continuous_const, continuous_apply ] ;
    · exact continuous_apply _ |> Continuous.comp <| continuous_induced_dom;
    · exact continuous_apply _ |> Continuous.comp <| continuous_induced_dom;
    · fun_prop;
    · fun_prop
/-- Composition of a rotation `rigid a b 0 0` with a translation `rigid 1 0 v1 v2`. -/
lemma rigid_one_zero_comp (a b v1 v2 : ℝ) (p : Pt) :
    rigid 1 0 v1 v2 (rigid a b 0 0 p) = rigid a b v1 v2 p := by
  classical
  simp [rigid]
/-- Image form of the previous composition lemma. -/
lemma image_rigid_one_zero_comp (a b v1 v2 : ℝ) (A : Set Pt) :
    rigid 1 0 v1 v2 '' (rigid a b 0 0 '' A) = rigid a b v1 v2 '' A := by
  classical
  rw [Set.image_image]
  exact Set.image_congr' (rigid_one_zero_comp a b v1 v2)
/-
The image of a measurable set under a rigid motion is measurable.
-/
lemma measurableSet_rigid_image {a b v1 v2 : ℝ} (hab : a ^ 2 + b ^ 2 = 1)
    {A : Set Pt} (hA : MeasurableSet A) :
    MeasurableSet (rigid a b v1 v2 '' A) := by
  classical
  have h_measurable : Measurable (rigid a b v1 v2) ∧ Measurable (fun p : Pt => rigid (a) (-b) (-(a * v1 - b * v2)) (-(b * v1 + a * v2)) p) := by
    exact ⟨ continuous_rigid a b v1 v2 |> Continuous.measurable, continuous_rigid a ( -b ) ( - ( a * v1 - b * v2 ) ) ( - ( b * v1 + a * v2 ) ) |> Continuous.measurable ⟩;
  have h_measurable : MeasurableEmbedding (rigid a b v1 v2) := by
    refine' h_measurable.1.measurableEmbedding _;
    intro p q h_eq;
    ext i; fin_cases i <;> simp_all +decide [ rigid ]; all_goals grind;
  exact h_measurable.measurableSet_image.mpr hA
/-
A rigid motion preserves Lebesgue measure of sets.
-/
lemma volume_rigid_image {a b v1 v2 : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (A : Set Pt) :
    volume (rigid a b v1 v2 '' A) = volume A := by
  classical
  unfold rigid;
  -- The translation part does not affect the volume, so we can focus on the linear part.
  have h_volume_linear : volume ((fun p : Pt => !₂[a * p 0 - b * p 1, b * p 0 + a * p 1]) '' A) = volume A := by
    have h_volume_linear : volume (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => Matrix.toLin (PiLp.basisFun 2 ℝ (Fin 2)) (PiLp.basisFun 2 ℝ (Fin 2)) (Matrix.of ![![a, -b], ![b, a]]) p) A) = volume A := by
      norm_num [ ← sq, hab ];
    convert h_volume_linear using 4 ; ring_nf!;
    erw [ Matrix.toLin_apply ] ; ext i ; fin_cases i <;> norm_num <;> ring!;
  rw [ ← h_volume_linear ];
  rw [ show ( fun p : Pt => !₂[a * p.ofLp 0 - b * p.ofLp 1 + v1, b * p.ofLp 0 + a * p.ofLp 1 + v2] ) '' A = ( fun p : Pt => p + !₂[v1, v2] ) '' ( ( fun p : Pt => !₂[a * p.ofLp 0 - b * p.ofLp 1, b * p.ofLp 0 + a * p.ofLp 1] ) '' A ) from ?_ ];
  · rw [ Set.image_add_right ];
    rw [ MeasureTheory.measure_preimage_add_right ];
  · ext; simp [Set.mem_image];
    constructor <;> rintro ⟨ x, hx, hx' ⟩ <;> use x, hx <;> simp_all +decide;
    · ext i; fin_cases i <;> norm_num [ ← hx' ] ;
    · convert congr_arg ( fun y => y + !₂[v1, v2] ) hx' using 1 <;> ext i <;> fin_cases i <;> norm_num
/-
**Pigeonhole + rotation.**  Some `90°·k` rotation of `A` has infinite measure inside the upper
sector.
-/
lemma sector_reduction (A : Set Pt) (hA_inf : volume A = ⊤) :
    ∃ a b : ℝ, a ^ 2 + b ^ 2 = 1 ∧ volume (rigid a b 0 0 '' A ∩ sectorUp) = ⊤ := by
  classical
  by_contra h_contra;
  -- Define the four closed quadrant sectors of the plane.
  set sectorUp : Set Pt := {p : Pt | |p 0| ≤ p 1}
  set sectorDown : Set Pt := {p : Pt | |p 0| ≤ -p 1}
  set sectorRight : Set Pt := {p : Pt | |p 1| ≤ p 0}
  set sectorLeft : Set Pt := {p : Pt | |p 1| ≤ -p 0};
  -- By countable subadditivity, we have $volume A \leq volume (A \cap sectorUp) + volume (A \cap sectorDown) + volume (A \cap sectorRight) + volume (A \cap sectorLeft)$.
  have h_subadd : volume A ≤ volume (A ∩ sectorUp) + volume (A ∩ sectorDown) + volume (A ∩ sectorRight) + volume (A ∩ sectorLeft) := by
    have h_subadd : volume A ≤ volume (A ∩ sectorUp ∪ A ∩ sectorDown ∪ A ∩ sectorRight ∪ A ∩ sectorLeft) := by
      refine' MeasureTheory.measure_mono _;
      intro p hp
      simp only [Set.mem_union, Set.mem_inter_iff, sectorUp, sectorDown, sectorRight,
        sectorLeft, Set.mem_ofPred_eq]
      by_cases h : |p 0| ≤ |p 1|
      · rcases le_total 0 (p 1) with hy | hy
        · exact Or.inl (Or.inl (Or.inl ⟨hp, by rwa [abs_of_nonneg hy] at h⟩))
        · exact Or.inl (Or.inl (Or.inr ⟨hp, by rwa [abs_of_nonpos hy] at h⟩))
      · rcases le_total 0 (p 0) with hx | hx
        · exact Or.inl (Or.inr ⟨hp, by simpa [abs_of_nonneg hx] using (le_of_not_ge h)⟩)
        · exact Or.inr ⟨hp, by simpa [abs_of_nonpos hx] using (le_of_not_ge h)⟩
    exact h_subadd.trans ( le_trans ( MeasureTheory.measure_union_le _ _ ) ( add_le_add ( le_trans ( MeasureTheory.measure_union_le _ _ ) ( add_le_add ( MeasureTheory.measure_union_le _ _ ) le_rfl ) ) le_rfl ) );
  -- Since $volume A = ⊤$, at least one of the four summands must be $⊤$.
  obtain ⟨Sec, hSec⟩ : ∃ Sec ∈ [sectorUp, sectorDown, sectorRight, sectorLeft], volume (A ∩ Sec) = ⊤ := by
    contrapose! h_subadd; simp_all +decide ;
    exact ⟨ ⟨ ⟨ lt_top_iff_ne_top.mpr h_subadd.1, lt_top_iff_ne_top.mpr h_subadd.2.1 ⟩, lt_top_iff_ne_top.mpr h_subadd.2.2.1 ⟩, lt_top_iff_ne_top.mpr h_subadd.2.2.2 ⟩;
  -- Each sector is carried INTO `Up` by a `90°·k` rotation `rigid a b 0 0`.
  obtain ⟨a, b, hab, hSecUp⟩ : ∃ a b : ℝ, a ^ 2 + b ^ 2 = 1 ∧ rigid a b 0 0 '' Sec ⊆ sectorUp := by
    simp +zetaDelta at *;
    rcases hSec.1 with ( rfl | rfl | rfl | rfl ) <;> norm_num [ rigid ];
    · exact ⟨ 1, 0, by norm_num, fun p hp => by simpa using hp ⟩;
    · use -1, 0 ; norm_num;
    · use 0, 1 ; norm_num;
    · use 0, -1 ; norm_num;
  -- Therefore, $volume (rigid a b 0 0 '' A ∩ sectorUp) ≥ volume (rigid a b 0 0 '' (A ∩ Sec)) = volume (A ∩ Sec) = ⊤$.
  have h_volume_ge : volume (rigid a b 0 0 '' A ∩ sectorUp) ≥ volume (rigid a b 0 0 '' (A ∩ Sec)) := by
    refine' MeasureTheory.measure_mono _;
    exact Set.image_subset_iff.mpr fun x hx => ⟨ Set.mem_image_of_mem _ hx.1, hSecUp <| Set.mem_image_of_mem _ hx.2 ⟩;
  exact h_contra ⟨ a, b, hab, le_antisymm ( le_top ) ( h_volume_ge.trans' ( by rw [ volume_rigid_image hab ] ; aesop ) ) ⟩
/-- The upper sector is measurable. -/
lemma measurableSet_sectorUp : MeasurableSet sectorUp := by
  classical
  apply measurableSet_le
  · exact (Measurable.abs (by fun_prop))
  · fun_prop
/-- The map `(x,y) ↦ !₂[x,y]` from `ℝ × ℝ` to the Euclidean plane preserves Lebesgue measure. -/
lemma measurePreserving_pair :
    MeasurePreserving (fun p : ℝ × ℝ => (!₂[p.1, p.2] : Pt)) volume volume := by
  classical
  have h1 : MeasurePreserving (⇑(MeasurableEquiv.finTwoArrow (α := ℝ)).symm) volume volume :=
    (MeasureTheory.volume_preserving_finTwoArrow ℝ).symm
  have h2 : MeasurePreserving (WithLp.toLp 2 : (Fin 2 → ℝ) → Pt) volume volume :=
    PiLp.volume_preserving_toLp (Fin 2)
  have := h2.comp h1
  convert this using 2 with p
  ext i
  fin_cases i <;> rfl
/-
**Fubini.**  A measurable set with infinite measure inside the upper sector has, at some
positive height `t₀`, a horizontal slice of positive one-dimensional measure.
-/
lemma exists_pos_slice (A' : Set Pt) (hA' : MeasurableSet A')
    (hsec : volume (A' ∩ sectorUp) = ⊤) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ 0 < (volume : Measure ℝ) {x : ℝ | (!₂[x, t₀] : Pt) ∈ A'} := by
  classical
  -- By Fubini's theorem, we can consider the integral of the measure of the slices over t.
  have h_fubini : ∫⁻ t in Set.Ioi 0, volume {x : ℝ | !₂[x, t] ∈ A' ∧ |x| ≤ t} = ⊤ := by
    have h_fubini : volume (Set.preimage (fun p : ℝ × ℝ => !₂[p.1, p.2]) (A' ∩ sectorUp)) = ∫⁻ t in Set.Ioi 0, volume {x : ℝ | !₂[x, t] ∈ A' ∧ |x| ≤ t} := by
      have h_fubini : volume (Set.preimage (fun p : ℝ × ℝ => !₂[p.1, p.2]) (A' ∩ sectorUp)) = ∫⁻ t, volume {x : ℝ | !₂[x, t] ∈ A' ∧ |x| ≤ t} := by
        exact MeasureTheory.Measure.prod_apply_symm
          (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
          ((hA'.inter measurableSet_sectorUp).preimage measurePreserving_pair.measurable)
      rw [ h_fubini, ← MeasureTheory.lintegral_indicator ] <;> norm_num [ Set.indicator ];
      congr with t ; split_ifs <;> simp_all +decide [ abs_le ];
      exact MeasureTheory.measure_mono_null ( fun x hx => by cases hx; exact Set.mem_singleton_iff.mpr <| by linarith ) ( MeasureTheory.measure_singleton t );
    convert hsec using 1;
    rw [ ← h_fubini, ← MeasureTheory.MeasurePreserving.measure_preimage ( measurePreserving_pair ) ];
    exact MeasurableSet.nullMeasurableSet ( hA'.inter measurableSet_sectorUp );
  contrapose! h_fubini;
  refine' ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.setLIntegral_mono' measurableSet_Ioi fun t ht => _ ) _ );
  use fun t => 0;
  · exact le_trans ( MeasureTheory.measure_mono ( fun x hx => hx.1 ) ) ( h_fubini t ht );
  · norm_num
/-
The part of the upper sector below a horizontal line is a bounded triangle, so removing it from
a set of infinite measure leaves infinite measure above any height `H`.
-/
lemma volume_sector_above (A' : Set Pt) (hsec : volume (A' ∩ sectorUp) = ⊤) (H : ℝ) :
    volume (A' ∩ sectorUp ∩ {p : Pt | H < p 1}) = ⊤ := by
  classical
  -- By subadditivity, we have `volume (A' ∩ sectorUp) ≤ volume (A' ∩ sectorUp ∩ {p | p 1 ≤ H}) + volume (A' ∩ sectorUp ∩ {p | H < p 1})`.
  have h_subadd : volume (A' ∩ sectorUp) ≤ volume (A' ∩ sectorUp ∩ {p | p.ofLp 1 ≤ H}) + volume (A' ∩ sectorUp ∩ {p | H < p.ofLp 1}) := by
    refine' le_trans _ ( MeasureTheory.measure_union_le _ _ );
    exact MeasureTheory.measure_mono fun x hx => by by_cases h : x.ofLp 1 ≤ H <;> aesop;
  contrapose! h_subadd;
  refine' lt_of_le_of_lt ( add_le_add ( MeasureTheory.measure_mono _ ) le_rfl ) _;
  exact { p : Pt | |p 0| ≤ p 1 ∧ p 1 ≤ H };
  · exact fun x hx => ⟨ hx.1.2, hx.2 ⟩;
  · -- The set {p : Pt | |p 0| ≤ p 1 ∧ p 1 ≤ H} is bounded.
    have h_bounded : Bornology.IsBounded {p : Pt | |p 0| ≤ p 1 ∧ p 1 ≤ H} := by
      refine' isBounded_iff_forall_norm_le.mpr ⟨ H ^ 2 + 1, fun p hp => _ ⟩;
      norm_num [ EuclideanSpace.norm_eq ] at *;
      rw [ Real.sqrt_le_left ] <;> nlinarith [ abs_le.mp hp.1, sq_nonneg ( p.ofLp 0 - p.ofLp 1 ), sq_nonneg ( p.ofLp 0 + p.ofLp 1 ) ];
    exact lt_of_lt_of_le ( ENNReal.add_lt_top.mpr ⟨ h_bounded.measure_lt_top, lt_top_iff_ne_top.mpr h_subadd ⟩ ) ( by aesop )
/-
Being a Lebesgue density point is preserved by orientation-preserving rigid motions.
-/
lemma isDensityPt_rigid_image {a b v1 v2 : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (A' : Set Pt) (C : Pt)
    (h : IsDensityPt A' C) :
    IsDensityPt (rigid a b v1 v2 '' A') (rigid a b v1 v2 C) := by
  classical
  unfold IsDensityPt at h ⊢
  apply h.congr'
  filter_upwards [ self_mem_nhdsWithin ] with r hr;
  have h_image : rigid a b v1 v2 '' (A' ∩ Metric.closedBall C r) = (rigid a b v1 v2 '' A') ∩ Metric.closedBall (rigid a b v1 v2 C) r := by
    ext x;
    constructor;
    · rintro ⟨ y, ⟨ hyA', hyC ⟩, rfl ⟩;
      exact ⟨ ⟨ y, hyA', rfl ⟩, by simpa [ dist_rigid hab ] using hyC ⟩;
    · rintro ⟨ ⟨ y, hy, rfl ⟩, hy' ⟩;
      exact ⟨ y, ⟨ hy, by simpa [ dist_rigid hab ] using hy' ⟩, rfl ⟩;
  rw [ ← h_image, volume_rigid_image hab ];
  norm_num [ EuclideanSpace.volume_closedBall ]
/-
**Density.**  There is a Lebesgue density point of `A'` of arbitrarily large height.
-/
lemma exists_densityPt_high (A' : Set Pt) (hA' : MeasurableSet A')
    (hsec : volume (A' ∩ sectorUp) = ⊤) (H : ℝ) :
    ∃ C : Pt, C ∈ A' ∧ IsDensityPt A' C ∧ H < C 1 := by
  classical
  obtain ⟨C, hC⟩ : ∃ C ∈ A' ∩ {p : Pt | H < p 1}, IsDensityPt A' C := by
    have := @Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet;
    specialize this volume hA';
    -- By `volume_sector_above`, `volume (A' ∩ sectorUp ∩ {p | H < p 1}) = ⊤ ≠ 0`.
    have h_volume_pos : volume (A' ∩ {p : Pt | H < p 1} ∩ sectorUp) ≠ 0 := by
      have h_volume_pos : volume (A' ∩ sectorUp ∩ {p : Pt | H < p 1}) = ⊤ := by
        convert volume_sector_above A' hsec H using 1;
      simp_all +decide [ Set.inter_comm, Set.inter_left_comm, Set.inter_assoc ];
    contrapose! h_volume_pos;
    refine' MeasureTheory.measure_mono_null _ this;
    intro x hx; specialize h_volume_pos x; simp_all +decide [ IsDensityPt ] ;
  exact ⟨ C, hC.1.1, hC.2, hC.1.2 ⟩
/-
**Fubini + Steinhaus + density.**  Given a measurable set with infinite measure inside the
upper sector, a translation of it admits a `Config`.
-/
lemma config_from_sector (A' : Set Pt) (hA' : MeasurableSet A')
    (hsec : volume (A' ∩ sectorUp) = ⊤) :
    ∃ v1 v2 c xC yC : ℝ, Config (rigid 1 0 v1 v2 '' A') c xC yC := by
  classical
  obtain ⟨t₀, ht₀_pos, ht₀_slice⟩ := exists_pos_slice A' hA' hsec;
  -- By Steinhaus, `I - I ∈ 𝓝 0`, so there is `θ > 0` with `Metric.ball (0:ℝ) θ ⊆ I - I`.
  obtain ⟨θ, hθ_pos, hθ_subset⟩ : ∃ θ > 0, Metric.ball 0 θ ⊆ {x - y | (x : ℝ) (hx : x ∈ {x : ℝ | (!₂[x, t₀] : Pt) ∈ A'}) (y : ℝ) (hy : y ∈ {x : ℝ | (!₂[x, t₀] : Pt) ∈ A'})} := by
    have h_steinhaus : ∀ {S : Set ℝ}, MeasurableSet S → 0 < volume S → {x - y | (x : ℝ) (hx : x ∈ S) (y : ℝ) (hy : y ∈ S)} ∈ 𝓝 0 := by
      intro S hS hS_pos;
      convert MeasureTheory.Measure.sub_mem_nhds_zero_of_addHaar_pos volume S hS hS_pos using 1;
      exact Set.ext fun x => ⟨ fun ⟨ a, ha, b, hb, hx ⟩ => ⟨ a, ha, b, hb, hx ⟩, fun ⟨ a, ha, b, hb, hx ⟩ => ⟨ a, ha, b, hb, hx ⟩ ⟩;
    have := h_steinhaus ( show MeasurableSet { x : ℝ | !₂[x, t₀] ∈ A' } from ?_ ) ht₀_slice; rw [ Metric.mem_nhds_iff ] at this; aesop;
    exact hA'.preimage ( by exact Continuous.measurable ( by exact by rw [ show ( fun x : ℝ => !₂[x, t₀] : ℝ → Pt ) = fun x => x • ( EuclideanSpace.single 0 1 ) + t₀ • ( EuclideanSpace.single 1 1 ) by ext x i; fin_cases i <;> simp +decide ] ; exact Continuous.add ( continuous_id.smul continuous_const ) continuous_const ) );
  obtain ⟨C, hC_mem, hC_density, hC_height⟩ : ∃ C : Pt, C ∈ A' ∧ IsDensityPt A' C ∧ t₀ + 2 / θ < C 1 := exists_densityPt_high A' hA' hsec (t₀ + 2 / θ);
  -- Set `yC := C 1 - t₀`; then `yC > 2/θ > 0`. Set `c := 2 / yC`; then `0 < c < θ` (since `yC > 2/θ`).
  set yC := C 1 - t₀
  have hyC_pos : 0 < yC := by
    exact sub_pos_of_lt ( lt_of_le_of_lt ( le_add_of_nonneg_right <| by positivity ) hC_height )
  set c := 2 / yC
  have hc_pos : 0 < c := by
    exact div_pos zero_lt_two hyC_pos
  have hc_lt_θ : c < θ := by
    rw [ div_lt_iff₀ ] <;> nlinarith [ mul_div_cancel₀ 2 hθ_pos.ne' ];
  -- Hence `c ∈ Metric.ball 0 θ ⊆ I - I` (because `|c| = c < θ`), so `∃ x₁ ∈ I, ∃ x₂ ∈ I, x₁ - x₂ = c`.
  obtain ⟨x₁, hx₁_mem, x₂, hx₂_mem, hx₁x₂⟩ : ∃ x₁ x₂ : ℝ, x₁ ∈ {x : ℝ | (!₂[x, t₀] : Pt) ∈ A'} ∧ x₂ ∈ {x : ℝ | (!₂[x, t₀] : Pt) ∈ A'} ∧ x₁ - x₂ = c := by
    exact hθ_subset ( mem_ball_zero_iff.mpr <| abs_lt.mpr ⟨ by linarith, by linarith ⟩ ) |> fun ⟨ x₁, hx₁, x₂, hx₂, h ⟩ => ⟨ x₁, x₂, hx₁, hx₂, h ⟩;
  use -hx₁_mem, -t₀, c, C 0 - hx₁_mem, yC;
  constructor;
  any_goals assumption;
  exact div_mul_cancel₀ _ hyC_pos.ne';
  · use !₂[hx₁_mem, t₀];
    exact ⟨ hx₂_mem, by ext i; fin_cases i <;> norm_num [ rigid ] ⟩;
  · use !₂[x₁, t₀];
    exact ⟨ x₂, by ext i; fin_cases i <;> norm_num [ rigid ] ; linarith ⟩;
  · use C; simp [rigid];
    exact ⟨ hC_mem, by ring, by ring ⟩;
  · exact measurableSet_rigid_image ( by norm_num ) hA';
  · convert isDensityPt_rigid_image _ _ _ hC_density using 1;
    · ext i; fin_cases i <;> simp +decide [ rigid ] ;
      · ring;
      · ring;
    · norm_num
/-- **First half of the proof.** Locating the triangle.  After applying a suitable
orientation-preserving rigid motion `g` (rotation `(a,b)` plus translation `(v₁,v₂)`), the image
`g '' A` contains a configuration as in `Config`. -/
lemma exists_config (A : Set Pt) (hA : MeasurableSet A) (hA_inf : volume A = ⊤) :
    ∃ (a b v1 v2 c xC yC : ℝ), a ^ 2 + b ^ 2 = 1 ∧
      Config (rigid a b v1 v2 '' A) c xC yC := by
  classical
  obtain ⟨a, b, hab, hsec⟩ := sector_reduction A hA_inf
  have hA' : MeasurableSet (rigid a b 0 0 '' A) := measurableSet_rigid_image hab hA
  obtain ⟨v1, v2, c, xC, yC, hcfg⟩ := config_from_sector _ hA' hsec
  refine ⟨a, b, v1, v2, c, xC, yC, hab, ?_⟩
  rwa [image_rigid_one_zero_comp] at hcfg
/- ===================== Core ===================== -/
/-!
## The perturbation map
Fix the base `A = (0,0)`, `B = (c,0)` and a triangle apex `C = (xC, yC)` with `c·yC = 2`
(so `area △ABC = 1`).  Given a point `D = (xD, yD)` (thought of as close to `C`, below the
horizontal line through `C`), there is a unique point `E = f(D)` close to `C` such that `A B E D`
is a cyclic quadrilateral of area `1`.  Geometrically, `E` is the second intersection of:
* the line `l`:  `yD·x + (c - xD)·y = 2`  (area `ABED = 1`), and
* the circumcircle `k` of `A B D`:  `x² + y² - c·x + ((c·xD - xD² - yD²)/yD)·y = 0`.
Eliminating `x` via the line equation yields a quadratic `P·y² + Q·y + R = 0` for `yE`, and
`E = f(D)` corresponds to the `+` root.
-/
/-- Coefficient `P = |BD|²` of the quadratic for `yE`. -/
noncomputable def Pcoef (c xD yD : ℝ) : ℝ := (xD - c) ^ 2 + yD ^ 2
/-- Coefficient `Q` of the quadratic for `yE`. -/
noncomputable def Qcoef (c xD yD : ℝ) : ℝ :=
  -4 * (c - xD) + c * yD * (c - xD) + yD * (c * xD - xD ^ 2 - yD ^ 2)
/-- Coefficient `R` of the quadratic for `yE`. -/
noncomputable def Rcoef (c yD : ℝ) : ℝ := 4 - 2 * c * yD
/-- Discriminant of the quadratic for `yE`. -/
noncomputable def discr (c xD yD : ℝ) : ℝ :=
  Qcoef c xD yD ^ 2 - 4 * Pcoef c xD yD * Rcoef c yD
/-- The `y`-coordinate of `E = f(D)`. -/
noncomputable def yEval (c xD yD : ℝ) : ℝ :=
  (-(Qcoef c xD yD) + Real.sqrt (discr c xD yD)) / (2 * Pcoef c xD yD)
/-- The `x`-coordinate of `E = f(D)`. -/
noncomputable def xEval (c xD yD : ℝ) : ℝ :=
  (2 - (c - xD) * yEval c xD yD) / yD
/-- The perturbation map `D ↦ E`. -/
noncomputable def fmap (c : ℝ) (D : Pt) : Pt := !₂[xEval c (D 0) (D 1), yEval c (D 0) (D 1)]
/-
`yEval` is a root of the quadratic `P·y² + Q·y + R = 0` (when the discriminant is nonneg
and `P > 0`).
-/
lemma quad_root (c xD yD : ℝ) (hP : 0 < Pcoef c xD yD) (hdisc : 0 ≤ discr c xD yD) :
    Pcoef c xD yD * yEval c xD yD ^ 2 + Qcoef c xD yD * yEval c xD yD + Rcoef c yD = 0 := by
  classical
  unfold yEval;
  field_simp;
  linarith [ Real.mul_self_sqrt hdisc, show discr c xD yD = Qcoef c xD yD ^ 2 - 4 * Pcoef c xD yD * Rcoef c yD from rfl ]
/-
The line equation (`area ABED = 1`).
-/
lemma eqI (c xD yD : ℝ) (hyD : yD ≠ 0) :
    yD * xEval c xD yD + (c - xD) * yEval c xD yD = 2 := by
  classical
  grind +locals
/-
The circle equation (`E` lies on the circumcircle of `A B D`).
-/
lemma eqII (c xD yD : ℝ) (hyD : yD ≠ 0) (hP : 0 < Pcoef c xD yD) (hdisc : 0 ≤ discr c xD yD) :
    xEval c xD yD ^ 2 + yEval c xD yD ^ 2 - c * xEval c xD yD
      + (c * xD - xD ^ 2 - yD ^ 2) / yD * yEval c xD yD = 0 := by
  classical
  unfold xEval yEval;
  field_simp;
  unfold Pcoef Qcoef discr; ring_nf;
  rw [ Real.sq_sqrt ];
  · unfold Qcoef Pcoef Rcoef; ring;
  · unfold discr at hdisc; linarith;
/-
The fixed point: `f(C) = C` when `c·yC = 2`.
-/
lemma fmap_fixed (c xC yC : ℝ) (hc : 0 < c) (hyC : 0 < yC) (harea : c * yC = 2) :
    xEval c xC yC = xC ∧ yEval c xC yC = yC := by
  classical
  have h_yC : yEval c xC yC = yC := by
    unfold yEval;
    rw [ div_eq_iff ];
    · rw [ show discr c xC yC = ( Qcoef c xC yC ) ^ 2 by
            unfold discr Rcoef Pcoef Qcoef; ring_nf;
            grind ];
      rw [ Real.sqrt_sq_eq_abs, abs_of_nonpos ];
      · unfold Qcoef Pcoef; ring_nf;
        grind;
      · unfold Qcoef;
        nlinarith [ sq_nonneg ( xC - c ), sq_nonneg ( xC - yC ), sq_nonneg ( yC - c ) ];
    · exact mul_ne_zero two_ne_zero ( by unfold Pcoef; nlinarith );
  unfold xEval; simp +decide [ * ] ; ring_nf;
  grind
/-
The shoelace area of `A B E D` equals `1`.
-/
lemma quadArea_ABED (c xD yD : ℝ) (hyD : yD ≠ 0) :
    quadArea (!₂[(0 : ℝ), (0 : ℝ)] : Pt) (!₂[c, (0 : ℝ)] : Pt)
        (!₂[xEval c xD yD, yEval c xD yD] : Pt) (!₂[xD, yD] : Pt) = 1 := by
  classical
  unfold quadArea; norm_num; ring_nf;
  linarith [ eqI c xD yD hyD ]
/-
`A B E D` are concyclic (all four lie on the circumcircle of `A B D`).
-/
lemma concyclic_ABED (c xD yD : ℝ) (hyD : 0 < yD) (hc : 0 < c)
    (hP : 0 < Pcoef c xD yD) (hdisc : 0 ≤ discr c xD yD) :
    Concyclic4 (!₂[(0 : ℝ), (0 : ℝ)] : Pt) (!₂[c, (0 : ℝ)] : Pt)
        (!₂[xEval c xD yD, yEval c xD yD] : Pt) (!₂[xD, yD] : Pt) := by
  classical
  refine' ⟨ !₂[c / 2, ( xD ^ 2 + yD ^ 2 - c * xD ) / ( 2 * yD ) ], Real.sqrt ( ( c / 2 ) ^ 2 + ( ( xD ^ 2 + yD ^ 2 - c * xD ) / ( 2 * yD ) ) ^ 2 ), _, _, _, _, _ ⟩;
  · positivity;
  · norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
  · norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
    ring_nf;
  · norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
    have := eqII c xD yD hyD.ne' hP hdisc;
    grind;
  · norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
    grind +locals
/-
Evaluating the quadratic `P·y² + Q·y + R` at `y = yC` factors as `yC·(yC - yD)·(xD² + yD²)`
(using `c·yC = 2`).
-/
lemma Pq_at_yC (c xD yD yC : ℝ) (harea : c * yC = 2) :
    Pcoef c xD yD * yC ^ 2 + Qcoef c xD yD * yC + Rcoef c yD
      = yC * (yC - yD) * (xD ^ 2 + yD ^ 2) := by
  classical
  unfold Pcoef Qcoef Rcoef;
  grind
/-
In the lower half (`c·yD < 2`, i.e. `yD < yC`), with the discriminant positive and the
sign conditions that hold near `C`, the image height satisfies `yEval < yC`.
-/
lemma yEval_lt_yC (c xD yD yC : ℝ) (hyC : 0 < yC) (harea : c * yC = 2)
    (hyD : 0 < yD) (hlt : yD < yC) (hP : 0 < Pcoef c xD yD) (hdisc : 0 ≤ discr c xD yD)
    (hpos : 0 < 2 * Pcoef c xD yD * yC + Qcoef c xD yD) :
    yEval c xD yD < yC := by
  classical
  -- By `Real.sqrt_lt' hpos`, this is `discr < (2 * Pcoef c xD yD * yC + Qcoef c xD yD)^2`.
  have h_sqrt_lt : discr c xD yD < (2 * Pcoef c xD yD * yC + Qcoef c xD yD)^2 := by
    have h_discr_lt_K2 : discr c xD yD < (2 * Pcoef c xD yD * yC + Qcoef c xD yD) ^ 2 := by
      have h_K2_minus_discr : (2 * Pcoef c xD yD * yC + Qcoef c xD yD) ^ 2 - discr c xD yD = 4 * Pcoef c xD yD * yC * (yC - yD) * (xD ^ 2 + yD ^ 2) := by
        convert congr_arg ( fun x : ℝ => 4 * Pcoef c xD yD * x ) ( Pq_at_yC c xD yD yC harea ) using 1 ; ring_nf;
        · unfold discr Rcoef; ring;
        · ring
      exact lt_of_sub_pos ( h_K2_minus_discr.symm ▸ mul_pos ( mul_pos ( mul_pos ( mul_pos zero_lt_four hP ) hyC ) ( sub_pos.mpr hlt ) ) ( by positivity ) );
    exact h_discr_lt_K2;
  unfold yEval; rw [ div_lt_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg ( discr c xD yD ), Real.mul_self_sqrt hdisc ] ;
/-
Near `C`, `yEval > 0` (it follows from `Qcoef < 0`, which holds near `C`).
-/
lemma yEval_pos (c xD yD : ℝ) (hP : 0 < Pcoef c xD yD)
    (hQ : Qcoef c xD yD < 0) :
    0 < yEval c xD yD := by
  classical
  exact div_pos ( by linarith [ Real.sqrt_nonneg ( discr c xD yD ) ] ) ( by positivity )
/-
Convexity of `A B E D` from the height bounds (using the orientation identities
`orient D A B = c·yD`, `orient A B E = c·yEval`, `orient E D A = 2 - c·yEval`,
`orient B E D = 2 - c·yD`).
-/
lemma convex_ABED (c xD yD : ℝ) (hc : 0 < c) (hyD : 0 < yD) (hyD' : c * yD < 2)
    (hyE : 0 < yEval c xD yD) (hyE' : c * yEval c xD yD < 2) :
    ConvexQuadCCW (!₂[(0 : ℝ), (0 : ℝ)] : Pt) (!₂[c, (0 : ℝ)] : Pt)
        (!₂[xEval c xD yD, yEval c xD yD] : Pt) (!₂[xD, yD] : Pt) := by
  classical
  refine' ⟨ _, _, _, _ ⟩ <;> norm_num [ ConvexQuadCCW, orient ];
  · positivity;
  · unfold xEval yEval at *;
    rw [ div_sub', div_mul_cancel₀ ] <;> linarith;
  · nlinarith [ eqI c xD yD hyD.ne' ];
  · nlinarith
/-- Measurability of `{D ∈ ball C δ | g D ∈ S}` when `g` is continuous on the ball. -/
lemma measurableSet_ball_preimage {S : Set Pt} (C : Pt) (g : Pt → Pt) (δ : ℝ)
    (hcont : ContinuousOn g (Metric.ball C δ)) (hS : MeasurableSet S) :
    MeasurableSet {D : Pt | D ∈ Metric.ball C δ ∧ g D ∈ S} := by
  classical
  have hmg : Measurable (fun x : Metric.ball C δ => g x.1) :=
    (continuousOn_iff_continuous_domRestrict.mp hcont).measurable
  obtain ⟨t, ht⟩ := hmg hS
  refine (ht.1.inter (measurableSet_ball (x := C) (ε := δ))).congr ?_
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hxt, hxb⟩
    refine ⟨hxb, ?_⟩
    have : (⟨x, hxb⟩ : Metric.ball C δ) ∈ Subtype.val ⁻¹' t := hxt
    rw [ht.2] at this; exact this
  · rintro ⟨hxb, hxS⟩
    refine ⟨?_, hxb⟩
    have : (⟨x, hxb⟩ : Metric.ball C δ) ∈ Subtype.val ⁻¹' t := by rw [ht.2]; exact hxS
    exact this
/-
**Abstract measure overlap.**  If `g` is, on a ball around `C`, an injective `C¹` map fixing
`C` with Jacobian determinant bounded below by `m > 0` and `M`-Lipschitz, and `S` has Lebesgue
density `1` at `C`, then arbitrarily close to `C` (and strictly below it) there is a point `D ∈ S`
with `g D ∈ S`.
-/
set_option maxHeartbeats 2000000 in
lemma overlap_of_diffeo
    (S : Set Pt) (C : Pt) (g : Pt → Pt) (g' : Pt → (Pt →L[ℝ] Pt))
    (m M r0 : ℝ) (hm : 0 < m) (hM : 0 < M) (hr0 : 0 < r0)
    (hSmeas : MeasurableSet S)
    (hderiv : ∀ x ∈ Metric.ball C r0, HasFDerivWithinAt g (g' x) (Metric.ball C r0) x)
    (hdet : ∀ x ∈ Metric.ball C r0, m ≤ |(g' x).det|)
    (hinj : Set.InjOn g (Metric.ball C r0))
    (hLip : ∀ x ∈ Metric.ball C r0, dist (g x) C ≤ M * dist x C)
    (hdens : IsDensityPt S C) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : Pt, dist D C < ε ∧ D 1 < C 1 ∧ D ∈ S ∧ g D ∈ S := by
  classical
  contrapose! hdens; simp_all +decide [ dist_eq_norm ] ; (
  contrapose! hdens with hdens';
  -- Choose $\delta \in (0, \min(\epsilon, \min(r_0/M, r_0)))$ such that $\text{volume}(\text{closedBall } C \delta \setminus S) + \text{ENNReal.ofReal}(1/m) \cdot \text{volume}(\text{closedBall } C (M\delta) \setminus S) < \text{ENNReal.ofReal}(\pi \delta^2 / 16)$.
  obtain ⟨δ, hδ_pos, hδ_lt, hδ⟩ : ∃ δ > 0, δ < min ε (min (r0 / M) r0) ∧
    (MeasureTheory.volume (Metric.closedBall C δ \ S)) + (ENNReal.ofReal (1 / m)) * (MeasureTheory.volume (Metric.closedBall C (M * δ) \ S)) <
    ENNReal.ofReal (Real.pi * (δ / 4) ^ 2) := by
      -- By the properties of the density function, we know that
      have h_density : Filter.Tendsto (fun δ => (volume (Metric.closedBall C δ \ S)) / ENNReal.ofReal (δ ^ 2)) (𝓝[>] 0) (𝓝 0) ∧ Filter.Tendsto (fun δ => (volume (Metric.closedBall C (M * δ) \ S)) / ENNReal.ofReal (δ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
        have h_density : Filter.Tendsto (fun δ => (volume (Metric.closedBall C δ \ S)) / ENNReal.ofReal (δ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
          have h_volume_closedBall : ∀ δ > 0, volume (Metric.closedBall C δ) = ENNReal.ofReal (Real.pi * δ ^ 2) := by
            intro δ hδ_pos; erw [ MeasureTheory.Measure.addHaar_closedBall ] ; norm_num [ hδ_pos.le ] ; ring_nf;
            · rw [ mul_comm, ENNReal.ofReal_mul ( by positivity ), ENNReal.ofReal_pow ( by positivity ) ];
            · positivity;
          have h_volume_closedBall : Filter.Tendsto (fun δ => (volume (Metric.closedBall C δ \ S)) / volume (Metric.closedBall C δ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
            have := hdens';
            have h_volume_closedBall : Filter.Tendsto (fun δ => (volume (Metric.closedBall C δ ∩ S)) / volume (Metric.closedBall C δ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
              convert this using 1;
              unfold IsDensityPt; simp +decide [ Set.inter_comm ] ;
            have h_volume_closedBall : ∀ δ > 0, volume (Metric.closedBall C δ \ S) = volume (Metric.closedBall C δ) - volume (Metric.closedBall C δ ∩ S) := by
              intro δ hδ_pos; rw [ ← MeasureTheory.measure_sdiff ] <;> norm_num [ hSmeas ] ;
              · exact MeasurableSet.nullMeasurableSet ( measurableSet_closedBall.inter hSmeas );
              · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( by aesop ) );
            rw [ Filter.tendsto_congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ h_volume_closedBall x hx ] ) ];
            have h_volume_closedBall : Filter.Tendsto (fun δ => 1 - (volume (Metric.closedBall C δ ∩ S)) / volume (Metric.closedBall C δ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
              convert ENNReal.Tendsto.sub tendsto_const_nhds ‹Tendsto ( fun δ => volume ( Metric.closedBall C δ ∩ S ) / volume ( Metric.closedBall C δ ) ) ( 𝓝[>] 0 ) ( 𝓝 1 ) › _ using 1 <;> norm_num;
            refine' h_volume_closedBall.congr' _;
            filter_upwards [ self_mem_nhdsWithin ] with δ hδ;
            rw [ ENNReal.sub_div ] <;> norm_num [ hδ.out.ne' ];
            · rw [ ENNReal.div_self ] <;> norm_num [ hδ.out.ne' ];
              · exact ⟨ hδ, Real.pi_pos ⟩;
              · exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num );
            · exact fun _ _ => ⟨ hδ, Real.pi_pos ⟩;
          have h_volume_closedBall : Filter.Tendsto (fun δ => (volume (Metric.closedBall C δ \ S)) / ENNReal.ofReal (Real.pi * δ ^ 2) * ENNReal.ofReal Real.pi) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
            have h_volume_closedBall : Filter.Tendsto (fun δ => (volume (Metric.closedBall C δ \ S)) / ENNReal.ofReal (Real.pi * δ ^ 2)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
              exact h_volume_closedBall.congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by aesop );
            convert ENNReal.Tendsto.mul_const h_volume_closedBall _ using 1 ; norm_num [ Real.pi_pos.le ];
            norm_num [ ENNReal.ofReal_ne_top ];
          refine' h_volume_closedBall.congr' _;
          filter_upwards [ self_mem_nhdsWithin ] with δ hδ ; simp +decide [ div_eq_mul_inv, mul_comm, Real.pi_pos.le ] ; ring_nf;
          simp +decide [ mul_assoc, mul_comm, ENNReal.mul_inv ];
          rw [ ← mul_assoc, ENNReal.mul_inv_cancel ( by positivity ) ( by norm_num ), one_mul ];
        have h_density_M : Filter.Tendsto (fun δ => (volume (Metric.closedBall C (M * δ) \ S)) / ENNReal.ofReal ((M * δ) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
          exact h_density.comp <| Filter.Tendsto.inf ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ) <| Filter.tendsto_principal_principal.mpr <| by aesop;
        refine' ⟨ h_density, _ ⟩;
        have h_density_M : Filter.Tendsto (fun δ => (volume (Metric.closedBall C (M * δ) \ S)) / ENNReal.ofReal ((M * δ) ^ 2) * ENNReal.ofReal (M ^ 2)) (𝓝[>] 0) (𝓝 0) := by
          convert ENNReal.Tendsto.mul_const h_density_M _ using 1 ; norm_num [ hM.ne' ];
          norm_num [ ENNReal.ofReal_ne_top ];
        refine' h_density_M.congr' _;
        filter_upwards [ self_mem_nhdsWithin ] with δ hδ ; rw [ ENNReal.div_mul ] ; ring_nf ;
        · rw [ ← ENNReal.ofReal_div_of_pos ( by positivity ), mul_div_cancel_left₀ _ ( by positivity ) ];
        · exact Or.inr ( ne_of_gt ( ENNReal.ofReal_pos.mpr ( sq_pos_of_pos hM ) ) );
        · exact Or.inl ENNReal.ofReal_ne_top;
      -- By the properties of the density function, we know that the limit of the ratio is 0.
      have h_limit : Filter.Tendsto (fun δ => (volume (Metric.closedBall C δ \ S) + ENNReal.ofReal (1 / m) * volume (Metric.closedBall C (M * δ) \ S)) / ENNReal.ofReal (δ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
        simp_all +decide [ ENNReal.add_div ];
        convert h_density.1.add ( ENNReal.Tendsto.const_mul h_density.2 _ ) using 2 <;> norm_num [ mul_div_assoc ];
        congr! 1;
        exact ENNReal.inv_ne_top.mpr ( by aesop );
      have := h_limit.eventually ( gt_mem_nhds <| show 0 < ENNReal.ofReal ( Real.pi / 16 ) from by positivity ) ; have := this.and ( Ioo_mem_nhdsGT <| show 0 < Min.min ε ( Min.min ( r0 / M ) r0 ) from lt_min hε <| lt_min ( div_pos hr0 hM ) hr0 ) ; obtain ⟨ δ, hδ₁, hδ₂ ⟩ := this.exists ; use δ ; simp_all +decide ;
      rw [ ENNReal.div_lt_iff ] at hδ₁ <;> norm_num at *;
      · exact hδ₁.trans_le ( by rw [ ← ENNReal.ofReal_mul ( by positivity ) ] ; ring_nf; norm_num );
      · exact Or.inl hδ₂.1.ne';
  -- Let $L := \text{Metric.ball } C \delta \cap \{D | D.ofLp 1 < C.ofLp 1\}$.
  set L := Metric.ball C δ ∩ {D : Pt | D 1 < C 1} with hL_def
  have hL_meas : MeasurableSet L := by
    refine' MeasurableSet.inter ( measurableSet_ball ) _;
    refine' measurableSet_lt _ _ <;> norm_num [ Pi.single_apply ];
    fun_prop (disch := norm_num)
  have hL_pos : MeasureTheory.volume L ≥ ENNReal.ofReal (Real.pi * (δ / 4) ^ 2) := by
    -- Contain a smaller ball in $L$.
    have h_ball_subset_L : Metric.ball (C - (δ / 2 : ℝ) • EuclideanSpace.single 1 1) (δ / 4) ⊆ L := by
      intro x hx; simp_all +decide [ EuclideanSpace.norm_eq ] ; (
      constructor <;> norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
      · rw [ Real.sqrt_lt' ] at * <;> nlinarith [ sq_nonneg ( x.ofLp 1 - C.ofLp 1 + δ / 2 ) ] ;
      · rw [ Real.sqrt_lt' ] at hx <;> nlinarith [ sq_nonneg ( x.ofLp 0 - C.ofLp 0 ), sq_nonneg ( x.ofLp 1 + δ / 2 - C.ofLp 1 ) ] ;)
    generalize_proofs at *; (
    refine' le_trans _ ( MeasureTheory.measure_mono h_ball_subset_L ) ; ring_nf ; norm_num [ Real.pi_pos.le ] ;
    rw [ ← ENNReal.ofReal_pow ( by positivity ) ] ; ring_nf ;
    rw [ ← ENNReal.ofReal_mul ( by positivity ) ] ; ring_nf; norm_num;)
  generalize_proofs at *; (
  -- Let $T := \{D \in L | g D \notin S\}$.
  set T := {D ∈ L | g D ∉ S} with hT_def
  have hT_meas : MeasurableSet T := by
    have hT_meas : MeasurableSet {D ∈ Metric.ball C δ | g D ∉ S} := by
      apply measurableSet_ball_preimage C g δ (by
      exact fun x hx => ( hderiv x ( by exact lt_of_lt_of_le ( by simpa [dist_eq_norm] using hx ) ( by linarith [ min_le_left ε ( min ( r0 / M ) r0 ), min_le_right ε ( min ( r0 / M ) r0 ), min_le_left ( r0 / M ) r0, min_le_right ( r0 / M ) r0 ] ) ) |> HasFDerivWithinAt.continuousWithinAt ) |> ContinuousWithinAt.mono <| Metric.ball_subset_ball <| by linarith [ min_le_left ε ( min ( r0 / M ) r0 ), min_le_right ε ( min ( r0 / M ) r0 ), min_le_left ( r0 / M ) r0, min_le_right ( r0 / M ) r0 ] ;) (hSmeas.compl)
    generalize_proofs at *; (
    convert hT_meas.inter hL_meas using 1 ; ext ; aesop ( simp_config := { singlePass := true } ) ;)
  have hT_bound : MeasureTheory.volume T ≤ (ENNReal.ofReal (1 / m)) * (MeasureTheory.volume (Metric.closedBall C (M * δ) \ S)) := by
    have hT_bound : ENNReal.ofReal m * MeasureTheory.volume T ≤ MeasureTheory.volume (g '' T) := by
      have hT_bound : ∫⁻ x in T, ENNReal.ofReal (|(g' x).det|) ∂MeasureTheory.volume ≤ MeasureTheory.volume (g '' T) := by
        apply_rules [ MeasureTheory.lintegral_abs_det_fderiv_le_addHaar_image ];
        · intro x hx; exact HasFDerivWithinAt.mono ( hderiv x <| by
            exact lt_of_lt_of_le ( mem_ball_iff_norm.mp hx.1.1 ) ( by linarith [ min_le_left ε ( min ( r0 / M ) r0 ), min_le_right ε ( min ( r0 / M ) r0 ), min_le_left ( r0 / M ) r0, min_le_right ( r0 / M ) r0 ] ) ) <| by
            exact fun x hx => Metric.ball_subset_ball ( by linarith [ min_le_left ε ( min ( r0 / M ) r0 ), min_le_right ε ( min ( r0 / M ) r0 ), min_le_left ( r0 / M ) r0, min_le_right ( r0 / M ) r0 ] ) hx.1.1;
        · exact hinj.mono ( fun x hx => by exact Metric.mem_ball.mpr ( lt_of_lt_of_le ( Metric.mem_ball.mp hx.1.1 ) ( by linarith [ min_le_left ε ( min ( r0 / M ) r0 ), min_le_right ε ( min ( r0 / M ) r0 ), min_le_left ( r0 / M ) r0, min_le_right ( r0 / M ) r0 ] ) ) )
      generalize_proofs at *; (
      refine' le_trans _ hT_bound
      generalize_proofs at *; (
      refine' le_trans _ ( MeasureTheory.setLIntegral_mono' hT_meas fun x hx => ENNReal.ofReal_le_ofReal <| hdet x _ ) <;> norm_num [ hδ_pos, hδ_lt ];
      exact lt_of_lt_of_le ( mem_ball_iff_norm.mp hx.1.1 ) ( by linarith [ min_le_left ε ( min ( r0 / M ) r0 ), min_le_right ε ( min ( r0 / M ) r0 ), min_le_left ( r0 / M ) r0, min_le_right ( r0 / M ) r0 ] )))
    generalize_proofs at *; (
    have hT_subset : g '' T ⊆ Metric.closedBall C (M * δ) \ S := by
      simp_all +decide [ Set.subset_def ];
      rintro x y hy₁ hy₂ hy₃ rfl; exact ⟨ by simpa [ dist_eq_norm ] using le_trans ( hLip y <| by simpa [ dist_eq_norm ] using hy₁.trans_le <| by nlinarith [ mul_div_cancel₀ r0 hM.ne' ] ) <| mul_le_mul_of_nonneg_left hy₁.le hM.le, hy₃ ⟩ ;
    generalize_proofs at *; (
    refine' le_trans _ ( mul_le_mul_right ( MeasureTheory.measure_mono hT_subset ) _ );
    convert mul_le_mul_right hT_bound ( ENNReal.ofReal ( 1 / m ) ) using 1 <;> try rfl
    ring_nf
    rw [ ← ENNReal.ofReal_mul ( by positivity ), inv_mul_cancel₀ ( by positivity ), ENNReal.ofReal_one, one_mul ]))
  generalize_proofs at *; (
  -- Since $L \subseteq (L \setminus S) \cup T \cup \{D \in \text{ball } C \delta | D.ofLp 1 < C.ofLp 1 \land D \in S \land g D \in S\}$, we have $\text{volume } L \leq \text{volume } (L \setminus S) + \text{volume } T + \text{volume } \{D \in \text{ball } C \delta | D.ofLp 1 < C.ofLp 1 \land D \in S \land g D \in S\}$.
  have hL_subset : MeasureTheory.volume L ≤ MeasureTheory.volume (Metric.closedBall C δ \ S) + MeasureTheory.volume T + MeasureTheory.volume {D ∈ Metric.ball C δ | D 1 < C 1 ∧ D ∈ S ∧ g D ∈ S} := by
    have hL_subset : L ⊆ (Metric.closedBall C δ \ S) ∪ T ∪ {D ∈ Metric.ball C δ | D 1 < C 1 ∧ D ∈ S ∧ g D ∈ S} := by
      intro D hD; by_cases hD' : D ∈ S <;> by_cases hD'' : g D ∈ S <;> simp_all +decide ;
      linarith [ hD.1 ]
    generalize_proofs at *; (
    refine' le_trans ( MeasureTheory.measure_mono hL_subset ) _;
    exact le_trans ( MeasureTheory.measure_union_le _ _ ) ( add_le_add ( MeasureTheory.measure_union_le _ _ ) le_rfl ))
  generalize_proofs at *; (
  contrapose! hL_subset; simp_all +decide [ Set.ofPred_and ] ; (
  refine' lt_of_le_of_lt _ ( lt_of_lt_of_le hδ hL_pos ) |> lt_of_lt_of_le <| le_rfl; simp_all +decide [ ← Set.inter_assoc ] ;
  rw [ show { a : Pt | dist a C < δ } ∩ { a : Pt | a.ofLp 1 < C.ofLp 1 } ∩ S ∩ { a : Pt | g a ∈ S } = ∅ from Set.eq_empty_of_forall_notMem fun x hx => hL_subset x ( by simpa [dist_eq_norm] using hx.1.1.1.trans_le hδ_lt.1.le ) hx.1.1.2 hx.1.2 hx.2 ] ; norm_num [ add_assoc ] ; gcongr;)))));
/-
`fmap c` is `C¹` near `C = (xC,yC)` (where `c·yC = 2`): the discriminant and `Pcoef` are
positive there, so the explicit formula is smooth.
-/
lemma fmap_contDiffAt (c xC yC : ℝ) (hyC : 0 < yC) (harea : c * yC = 2) :
    ContDiffAt ℝ 1 (fmap c) (!₂[xC, yC] : Pt) := by
  classical
  refine' ContDiffAt.comp _ _ _;
  · fun_prop (disch := norm_num);
  · -- By definition of $fmap$, we know that it is a composition of smooth functions.
    have h_smooth : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => (xEval c p.1 p.2, yEval c p.1 p.2)) (xC, yC) := by
      apply_rules [ ContDiffAt.prodMk, ContDiffAt.div, ContDiffAt.sqrt ];
      any_goals positivity;
      · apply_rules [ ContDiffAt.sub, ContDiffAt.mul, contDiffAt_const, contDiffAt_fst, contDiffAt_snd ];
        · apply_rules [ ContDiffAt.add, ContDiffAt.neg, ContDiffAt.sqrt ];
          any_goals apply_rules [ ContDiffAt.mul, ContDiffAt.sub, contDiffAt_const, contDiffAt_fst, contDiffAt_snd ];
          · apply_rules [ ContDiffAt.add, ContDiffAt.neg, ContDiffAt.mul, contDiffAt_const, contDiffAt_fst, contDiffAt_snd ];
          · apply_rules [ ContDiffAt.add, ContDiffAt.neg, ContDiffAt.mul, contDiffAt_const, contDiffAt_fst, contDiffAt_snd ];
          · exact ContDiffAt.add ( ContDiffAt.pow ( contDiffAt_fst.sub contDiffAt_const ) 2 ) ( ContDiffAt.pow ( contDiffAt_snd ) 2 );
          · unfold discr;
            unfold Qcoef Pcoef Rcoef; norm_num [ show c = 2 / yC by rw [ eq_div_iff hyC.ne' ] ; linarith ] ; ring_nf; norm_num [ hyC.ne' ] ;
            field_simp;
            nlinarith [ sq_nonneg ( xC * yC - 2 ), sq_nonneg ( xC * yC + 2 ), pow_pos hyC 3, pow_pos hyC 4, pow_pos hyC 5, pow_pos hyC 6, pow_pos hyC 7, pow_pos hyC 8 ];
        · apply_rules [ ContDiffAt.inv, ContDiffAt.mul, contDiffAt_const ];
          · exact ContDiffAt.add ( ContDiffAt.pow ( contDiffAt_fst.sub contDiffAt_const ) 2 ) ( ContDiffAt.pow ( contDiffAt_snd ) 2 );
          · exact mul_ne_zero two_ne_zero ( by unfold Pcoef; nlinarith );
      · exact contDiffAt_snd;
      · apply_rules [ ContDiffAt.add, ContDiffAt.neg, ContDiffAt.sqrt ];
        any_goals apply_rules [ ContDiffAt.pow, ContDiffAt.mul, ContDiffAt.sub, contDiffAt_const, contDiffAt_fst, contDiffAt_snd ];
        · apply_rules [ ContDiffAt.sub, ContDiffAt.add, ContDiffAt.mul, contDiffAt_const, contDiffAt_fst, contDiffAt_snd ];
        · exact ContDiffAt.add ( ContDiffAt.pow ( contDiffAt_fst.sub contDiffAt_const ) 2 ) ( ContDiffAt.pow ( contDiffAt_snd ) 2 );
        · unfold discr;
          unfold Qcoef Pcoef Rcoef; norm_num [ show c = 2 / yC by rw [ eq_div_iff hyC.ne' ] ; linarith ] ; ring_nf; norm_num [ hyC.ne' ] ;
          field_simp;
          nlinarith [ sq_nonneg ( xC * yC - 2 ), sq_nonneg ( xC * yC + 2 ), pow_pos hyC 3, pow_pos hyC 4, pow_pos hyC 5, pow_pos hyC 6, pow_pos hyC 7, pow_pos hyC 8 ];
      · exact ContDiffAt.mul contDiffAt_const ( ContDiffAt.add ( ContDiffAt.pow ( contDiffAt_fst.sub contDiffAt_const ) 2 ) ( ContDiffAt.pow ( contDiffAt_snd ) 2 ) );
      · exact mul_ne_zero two_ne_zero ( by unfold Pcoef; nlinarith );
    have h_smooth : ContDiffAt ℝ 1 (fun D : EuclideanSpace ℝ (Fin 2) => (xEval c (D 0) (D 1), yEval c (D 0) (D 1))) !₂[xC, yC] := by
      have h_smooth : ContDiffAt ℝ 1 (fun D : EuclideanSpace ℝ (Fin 2) => (D 0, D 1)) !₂[xC, yC] := by
        fun_prop;
      exact ContDiffAt.comp _ ( by assumption ) h_smooth;
    exact contDiffAt_pi.mpr fun i => by fin_cases i <;> [ exact h_smooth.fst; exact h_smooth.snd ] ;
/-- The partial derivative `∂(yEval)/∂yD` at `C = (xC,yC)` equals `(xC²+yC²)/((xC-c)²+yC²) > 0`.
This is the single non-trivial entry of the Jacobian (the first column is `[1,0]` by
`fmap_fixed`, so the determinant equals this value). -/
lemma yEval_hasDerivAt_y (c xC yC : ℝ) (hc : 0 < c) (hyC : 0 < yC) (harea : c * yC = 2) :
    HasDerivAt (fun y => yEval c xC y)
      ((xC ^ 2 + yC ^ 2) / ((xC - c) ^ 2 + yC ^ 2)) yC := by
  classical
  have hPpos : 0 < Pcoef c xC yC := by unfold Pcoef; positivity
  have hQval : Qcoef c xC yC = -yC * ((xC - c) ^ 2 + yC ^ 2) := by
    unfold Qcoef; linear_combination (2*c - 2*xC) * harea
  have hQneg : Qcoef c xC yC < 0 := by
    rw [hQval]
    have h : (0:ℝ) < (xC - c) ^ 2 + yC ^ 2 := by positivity
    nlinarith [h, hyC]
  have hRz : Rcoef c yC = 0 := by unfold Rcoef; linarith [harea]
  have hdC : discr c xC yC = (Qcoef c xC yC) ^ 2 := by unfold discr; rw [hRz]; ring
  have hdpos : 0 < discr c xC yC := by
    rw [hdC]; nlinarith [mul_pos (neg_pos.mpr hQneg) (neg_pos.mpr hQneg)]
  have hdiff : DifferentiableAt ℝ (fun y => yEval c xC y) yC := by
    unfold yEval discr Qcoef Pcoef Rcoef
    fun_prop (disch := first | positivity | nlinarith [hdpos, hPpos] | assumption)
  set v := deriv (fun y => yEval c xC y) yC with hvdef
  have hf : HasDerivAt (fun y => yEval c xC y) v yC := hdiff.hasDerivAt
  have hyEvalC : yEval c xC yC = yC := (fmap_fixed c xC yC hc hyC harea).2
  have hP' : HasDerivAt (fun y => Pcoef c xC y) (2*yC) yC := by
    unfold Pcoef
    have h := (hasDerivAt_const (𝕜:=ℝ) yC ((xC-c)^2)).add (hasDerivAt_pow 2 yC)
    convert h using 1 <;> try rfl
    push_cast
    ring
  have hQ' : HasDerivAt (fun y => Qcoef c xC y) (c*(c-xC)+(c*xC-xC^2)-3*yC^2) yC := by
    unfold Qcoef
    have hid : HasDerivAt (fun y : ℝ => y) 1 yC := hasDerivAt_id' yC
    have h1 := (hasDerivAt_const (𝕜:=ℝ) yC (-4*(c-xC))).add ((hid.const_mul c).mul_const (c-xC))
    have hsub := (hasDerivAt_const (𝕜:=ℝ) yC (c*xC-xC^2)).sub (hasDerivAt_pow 2 yC)
    have h := h1.add (hid.mul hsub)
    convert h using 1 <;> try rfl
    simp only [Pi.sub_apply]
    push_cast
    ring
  have hR' : HasDerivAt (fun y => Rcoef c y) (-2*c) yC := by
    unfold Rcoef
    have hid : HasDerivAt (fun y : ℝ => y) 1 yC := hasDerivAt_id' yC
    have h := (hasDerivAt_const (𝕜:=ℝ) yC (4:ℝ)).sub ((hid.const_mul 2).const_mul c)
    convert h using 1 <;> (try ext y) <;> (try simp only [Pi.sub_apply]) <;> ring
  have hPnhds : ∀ᶠ y in 𝓝 yC, 0 < Pcoef c xC y :=
    (continuousAt_const).eventually_lt hP'.continuousAt hPpos
  have hdnhds : ∀ᶠ y in 𝓝 yC, 0 ≤ discr c xC y := by
    have hcont : ContinuousAt (fun y => discr c xC y) yC := by
      unfold discr Qcoef Pcoef Rcoef; fun_prop
    exact ((continuousAt_const).eventually_lt hcont hdpos).mono (fun y h => le_of_lt h)
  have hH0 : (fun y => Pcoef c xC y * yEval c xC y^2 + Qcoef c xC y * yEval c xC y + Rcoef c y)
      =ᶠ[𝓝 yC] (fun _ => 0) := by
    filter_upwards [hPnhds, hdnhds] with y hPy hdy using quad_root c xC y hPy hdy
  have hHd0 : HasDerivAt (fun y => Pcoef c xC y * yEval c xC y^2 + Qcoef c xC y * yEval c xC y
      + Rcoef c y) 0 yC :=
    (hasDerivAt_const yC (0:ℝ)).congr_of_eventuallyEq hH0
  have hsq : HasDerivAt (fun y => yEval c xC y ^ 2) (2 * yEval c xC yC * v) yC := by
    convert hf.pow 2 using 1 <;> try rfl
    norm_num
  have hHd : HasDerivAt (fun y => Pcoef c xC y * yEval c xC y^2 + Qcoef c xC y * yEval c xC y
      + Rcoef c y)
      ((2*yC) * (yEval c xC yC)^2 + Pcoef c xC yC * (2 * yEval c xC yC * v)
        + ((c*(c-xC)+(c*xC-xC^2)-3*yC^2) * yEval c xC yC + Qcoef c xC yC * v) + (-2*c)) yC :=
    ((hP'.mul hsq).add (hQ'.mul hf)).add hR'
  have heq := hHd0.unique hHd
  rw [hyEvalC, hQval, show Pcoef c xC yC = (xC-c)^2+yC^2 from rfl] at heq
  have hv_eq : v = (xC ^ 2 + yC ^ 2) / ((xC - c) ^ 2 + yC ^ 2) := by
    rw [eq_div_iff (by positivity)]
    have hc2 : c ^ 2 * yC = 2 * c := by nlinarith [harea]
    have key : yC * (((xC - c) ^ 2 + yC ^ 2) * v) = yC * (xC ^ 2 + yC ^ 2) := by
      nlinarith [heq, hc2]
    have hcancel := mul_left_cancel₀ (ne_of_gt hyC) key
    linarith [hcancel, mul_comm ((xC - c) ^ 2 + yC ^ 2) v]
  rw [hv_eq] at hf
  exact hf
/-
The partial derivative `∂(yEval)/∂xD` at `C = (xC,yC)` equals `0` (when `c·yC = 2`).
This is the lower-left entry of the Jacobian. Proved by implicit differentiation of `quad_root`
with respect to `xD`, exactly as in `yEval_hasDerivAt_y`. The numerator
`∂P/∂xD·yC² + ∂Q/∂xD·yC = yC·(4 - 2·c·yC) = 0`.
-/
lemma yEval_hasDerivAt_x (c xC yC : ℝ) (hc : 0 < c) (hyC : 0 < yC) (harea : c * yC = 2) :
    HasDerivAt (fun x => yEval c x yC) 0 xC := by
  classical
  convert HasDerivAt.congr_of_eventuallyEq _ ?_ using 1;
  exact fun x => yC;
  · exact hasDerivAt_const _ _;
  · filter_upwards [ ( Metric.ball_mem_nhds xC zero_lt_one ) ] with x hx;
    convert fmap_fixed c x yC hc hyC ( by linarith ) |> And.right using 1
/-
The partial derivative `∂(xEval)/∂xD` at `C = (xC,yC)` equals `1` (when `c·yC = 2`).
Since `xEval c x yC = (2 - (c - x)·yEval c x yC)/yC`, and `∂yEval/∂xD = 0` (`yEval_hasDerivAt_x`)
with `yEval c xC yC = yC` (`fmap_fixed`), the derivative is `yC/yC = 1`.
-/
lemma xEval_hasDerivAt_x (c xC yC : ℝ) (hc : 0 < c) (hyC : 0 < yC) (harea : c * yC = 2) :
    HasDerivAt (fun x => xEval c x yC) 1 xC := by
  classical
  convert HasDerivAt.div_const ( HasDerivAt.sub ( hasDerivAt_const _ _ ) ( HasDerivAt.sub ( hasDerivAt_const _ _ ) ( hasDerivAt_id xC ) |> HasDerivAt.mul <| HasDerivAt.congr_of_eventuallyEq ( yEval_hasDerivAt_x c xC yC hc hyC harea ) <| Filter.eventuallyEq_of_mem ( Metric.ball_mem_nhds _ hyC ) fun x hx => rfl ) ) yC using 1 <;> try rfl
  ring_nf
  rw [ fmap_fixed c xC yC hc hyC harea |>.2, mul_inv_cancel₀ hyC.ne' ]
/-- Translation: the derivative of `t ↦ f (a + t)` at `0` is the derivative of `f` at `a`. -/
lemma hasDerivAt_translate {f : ℝ → ℝ} {a d : ℝ} (h : HasDerivAt f d a) :
    HasDerivAt (fun t : ℝ => f (a + t)) d 0 := by
  classical
  have h2 : HasDerivAt f d (a + (0:ℝ)) := by simpa using h
  simpa only [Function.comp_def, one_mul, mul_one] using h2.comp (0:ℝ) ((hasDerivAt_id (0:ℝ)).const_add a)
/-- The value of a directional derivative `fderiv g C (single j 1)` is the derivative of the
restriction of `g` to the line `t ↦ C + t • single j 1`. -/
lemma fderiv_apply_single_eq {g : Pt → ℝ} {C : Pt} {j : Fin 2} (hg : DifferentiableAt ℝ g C)
    {d : ℝ} (hd : HasDerivAt (fun t : ℝ => g (C + t • EuclideanSpace.single j (1:ℝ))) d 0) :
    fderiv ℝ g C (EuclideanSpace.single j (1:ℝ)) = d := by
  classical
  have hline : HasDerivAt (fun t : ℝ => C + t • EuclideanSpace.single j (1:ℝ))
      (EuclideanSpace.single j (1:ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (EuclideanSpace.single j (1:ℝ))).const_add C
  have hf : HasFDerivAt g (fderiv ℝ g C) (C + (0:ℝ) • EuclideanSpace.single j (1:ℝ)) := by
    simpa using hg.hasFDerivAt
  have hcomp : HasDerivAt (fun t : ℝ => g (C + t • EuclideanSpace.single j (1:ℝ)))
      (fderiv ℝ g C (EuclideanSpace.single j (1:ℝ))) 0 :=
    hf.comp_hasDerivAt 0 hline
  exact hcomp.unique hd
/-- The Jacobian determinant of `fmap c` at `C = (xC,yC)` is nonzero (it equals
`(xC²+yC²)/((xC-c)²+yC²) > 0`). -/
lemma fmap_fderiv_det_ne (c xC yC : ℝ) (hc : 0 < c) (hyC : 0 < yC) (harea : c * yC = 2) :
    (fderiv ℝ (fmap c) (!₂[xC, yC] : Pt)).det ≠ 0 := by
  classical
  set C : Pt := !₂[xC, yC] with hC
  have hdiff : DifferentiableAt ℝ (fmap c) C :=
    (fmap_contDiffAt c xC yC hyC harea).differentiableAt (by norm_num)
  set V := (xC ^ 2 + yC ^ 2) / ((xC - c) ^ 2 + yC ^ 2) with hV
  have hVpos : 0 < V := by rw [hV]; positivity
  have hcomp_fderiv : ∀ (i : Fin 2),
      HasFDerivAt (fun D : Pt => (fmap c D) i)
        ((EuclideanSpace.proj i).comp (fderiv ℝ (fmap c) C)) C := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp C hdiff.hasFDerivAt
  have hdiff_comp : ∀ (i : Fin 2), DifferentiableAt ℝ (fun D : Pt => (fmap c D) i) C :=
    fun i => (hcomp_fderiv i).differentiableAt
  have hentry : ∀ (i j : Fin 2),
      (fderiv ℝ (fmap c) C (EuclideanSpace.single j (1:ℝ))) i
        = fderiv ℝ (fun D => (fmap c D) i) C (EuclideanSpace.single j (1:ℝ)) := by
    intro i j
    rw [(hcomp_fderiv i).fderiv]; rfl
  have hM00 : fderiv ℝ (fun D => (fmap c D) 0) C (EuclideanSpace.single 0 (1:ℝ)) = 1 := by
    apply fderiv_apply_single_eq (hdiff_comp 0)
    have heq : (fun t : ℝ => (fmap c (C + t • EuclideanSpace.single (0:Fin 2) (1:ℝ))) 0)
        = fun t => xEval c (xC + t) yC := by
      funext t; rw [hC]; simp [fmap]
    rw [heq]
    exact hasDerivAt_translate (xEval_hasDerivAt_x c xC yC hc hyC harea)
  have hM10 : fderiv ℝ (fun D => (fmap c D) 1) C (EuclideanSpace.single 0 (1:ℝ)) = 0 := by
    apply fderiv_apply_single_eq (hdiff_comp 1)
    have heq : (fun t : ℝ => (fmap c (C + t • EuclideanSpace.single (0:Fin 2) (1:ℝ))) 1)
        = fun t => yEval c (xC + t) yC := by
      funext t; rw [hC]; simp [fmap]
    rw [heq]
    exact hasDerivAt_translate (yEval_hasDerivAt_x c xC yC hc hyC harea)
  have hM11 : fderiv ℝ (fun D => (fmap c D) 1) C (EuclideanSpace.single 1 (1:ℝ)) = V := by
    apply fderiv_apply_single_eq (hdiff_comp 1)
    have heq : (fun t : ℝ => (fmap c (C + t • EuclideanSpace.single (1:Fin 2) (1:ℝ))) 1)
        = fun t => yEval c xC (yC + t) := by
      funext t; rw [hC]; simp [fmap]
    rw [heq, hV]
    exact hasDerivAt_translate (yEval_hasDerivAt_y c xC yC hc hyC harea)
  set b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis with hb
  set L := fderiv ℝ (fmap c) C with hLdef
  have hdet : L.det = (LinearMap.toMatrix b b L.toLinearMap).det := by
    rw [LinearMap.det_toMatrix]
  rw [hdet, Matrix.det_fin_two]
  have hMij : ∀ (i j : Fin 2),
      LinearMap.toMatrix b b L.toLinearMap i j = (L (EuclideanSpace.single j (1:ℝ))) i := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    simp [hb, EuclideanSpace.basisFun_toBasis]
  rw [hMij, hMij, hMij, hMij]
  rw [show (L (EuclideanSpace.single (0:Fin 2) (1:ℝ))) 0 = (1:ℝ) from by
        rw [hLdef, hentry]; exact hM00,
     show (L (EuclideanSpace.single (1:Fin 2) (1:ℝ))) 1 = V from by
        rw [hLdef, hentry]; exact hM11,
     show (L (EuclideanSpace.single (0:Fin 2) (1:ℝ))) 1 = (0:ℝ) from by
        rw [hLdef, hentry]; exact hM10]
  simp only [mul_zero, sub_zero, one_mul]
  exact ne_of_gt hVpos
/-- The determinant of a continuous linear self-map of `Pt` depends continuously on the map. -/
lemma continuous_clm_det : Continuous (fun L : Pt →L[ℝ] Pt => L.det) := by
  classical
  set b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis with hb
  have heq : (fun L : Pt →L[ℝ] Pt => L.det)
      = fun L : Pt →L[ℝ] Pt => (LinearMap.toMatrix b b (L : Pt →ₗ[ℝ] Pt)).det := by
    funext L; rw [LinearMap.det_toMatrix]
  rw [heq]
  apply Continuous.matrix_det
  apply continuous_matrix
  intro i j
  have hcont : Continuous (fun L : Pt →L[ℝ] Pt => (L (EuclideanSpace.single j (1:ℝ)))) :=
    (ContinuousLinearMap.apply ℝ Pt (EuclideanSpace.single j (1:ℝ))).continuous
  have heq2 : (fun L : Pt →L[ℝ] Pt => LinearMap.toMatrix b b (L : Pt →ₗ[ℝ] Pt) i j)
      = fun L : Pt →L[ℝ] Pt => (EuclideanSpace.proj i) (L (EuclideanSpace.single j (1:ℝ))) := by
    funext L
    rw [hb]
    simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_toBasis, EuclideanSpace.proj]
  rw [heq2]
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hcont
/-
**Local diffeomorphism data for `fmap`.**  Near `C = (xC,yC)` (with `c·yC = 2`) the map `fmap c`
is a `C¹` local diffeomorphism: there is a ball `ball C r0` on which it is differentiable with
continuous derivative, injective, with Jacobian determinant bounded below by `m > 0` and is
`M`-Lipschitz toward `C`.  These are exactly the hypotheses needed for `overlap_of_diffeo`.
-/
lemma fmap_isDiffeoData (c xC yC : ℝ) (hc : 0 < c) (hyC : 0 < yC) (harea : c * yC = 2) :
    ∃ (m M r0 : ℝ), 0 < m ∧ 0 < M ∧ 0 < r0 ∧
      (∀ x ∈ Metric.ball (!₂[xC, yC] : Pt) r0,
        HasFDerivWithinAt (fmap c) (fderiv ℝ (fmap c) x) (Metric.ball (!₂[xC, yC] : Pt) r0) x) ∧
      (∀ x ∈ Metric.ball (!₂[xC, yC] : Pt) r0, m ≤ |(fderiv ℝ (fmap c) x).det|) ∧
      Set.InjOn (fmap c) (Metric.ball (!₂[xC, yC] : Pt) r0) ∧
      (∀ x ∈ Metric.ball (!₂[xC, yC] : Pt) r0,
        dist (fmap c x) (!₂[xC, yC] : Pt) ≤ M * dist x (!₂[xC, yC] : Pt)) := by
  classical
  -- Set `C := !₂[xC, yC] : Pt`.
  set C : Pt := !₂[xC, yC];
  obtain ⟨rInj, hrInj_pos, hrInj⟩ : ∃ rInj > 0, Set.InjOn (fmap c) (Metric.ball C rInj) := by
    have h_cont_diff : ContDiffAt ℝ 1 (fmap c) C := by
      exact fmap_contDiffAt c xC yC hyC harea;
    have h_inv_fun : HasStrictFDerivAt (fmap c) (fderiv ℝ (fmap c) C) C := by
      exact h_cont_diff.hasStrictFDerivAt ( by norm_num );
    have := h_inv_fun.isLittleO;
    rw [ Asymptotics.isLittleO_iff ] at this;
    -- Choose $c_1 = \frac{1}{2} \inf_{\|v\|=1} \|Df(C)v\|$.
    obtain ⟨c1, hc1_pos, hc1⟩ : ∃ c1 > 0, ∀ v : Pt, ‖v‖ = 1 → ‖(fderiv ℝ (fmap c) C) v‖ ≥ 2 * c1 := by
      have h_inv_fun : ∀ v : Pt, ‖v‖ = 1 → ‖(fderiv ℝ (fmap c) C) v‖ > 0 := by
        intro v hv; have := fmap_fderiv_det_ne c xC yC hc hyC harea; simp_all +decide [ ContinuousLinearMap.det ] ;
        intro h; have := LinearMap.ker_eq_bot.mp ( show LinearMap.ker ( fderiv ℝ ( fmap c ) C |> ContinuousLinearMap.toLinearMap ) = ⊥ from ?_ ) ; simp_all +decide ;
        · exact absurd ( this ( show ( fderiv ℝ ( fmap c ) C ) v = ( fderiv ℝ ( fmap c ) C ) 0 by aesop ) ) ( by aesop );
        · exact LinearMap.ker_eq_bot_of_injective ( LinearEquiv.injective ( LinearMap.equivOfDetNeZero _ this ) );
      have h_inv_fun : ∃ c1 > 0, ∀ v : Pt, ‖v‖ = 1 → ‖(fderiv ℝ (fmap c) C) v‖ ≥ c1 := by
        have h_compact : IsCompact {v : Pt | ‖v‖ = 1} := by
          convert ( isCompact_sphere ( 0 : Pt ) 1 ) using 1 <;> try rfl
          ext v
          simp only [Set.mem_ofPred_eq, Metric.mem_sphere, dist_zero_right]
        have h_min : ∃ v ∈ {v : Pt | ‖v‖ = 1}, ∀ w ∈ {v : Pt | ‖v‖ = 1}, ‖(fderiv ℝ (fmap c) C) v‖ ≤ ‖(fderiv ℝ (fmap c) C) w‖ := by
          have h_min : ContinuousOn (fun v : Pt => ‖(fderiv ℝ (fmap c) C) v‖) {v : Pt | ‖v‖ = 1} := by
            exact Continuous.continuousOn ( by continuity );
          exact h_compact.exists_isMinOn ⟨ EuclideanSpace.single 0 1, by norm_num ⟩ h_min;
        exact ⟨ ‖( fderiv ℝ ( fmap c ) C ) h_min.choose‖, h_inv_fun _ h_min.choose_spec.1, fun v hv => h_min.choose_spec.2 _ hv ⟩;
      exact ⟨ h_inv_fun.choose / 2, half_pos h_inv_fun.choose_spec.1, fun v hv => by linarith [ h_inv_fun.choose_spec.2 v hv ] ⟩;
    obtain ⟨ r, hr ⟩ := Metric.mem_nhds_iff.mp ( this hc1_pos );
    refine' ⟨ r / 2, half_pos hr.1, fun x hx y hy hxy => _ ⟩;
    have := hr.2 ( show ( x, y ) ∈ Metric.ball ( C, C ) r from ?_ );
    · contrapose! hc1;
      refine' ⟨ ( ‖x - y‖⁻¹ : ℝ ) • ( x - y ), _, _ ⟩ <;> simp_all +decide [ norm_smul, sub_eq_zero ];
      rw [ inv_mul_eq_div, div_lt_iff₀ ] <;> nlinarith [ norm_pos_iff.mpr ( sub_ne_zero.mpr hc1 ), norm_sub_rev ( ( fderiv ℝ ( fmap c ) C ) x ) ( ( fderiv ℝ ( fmap c ) C ) y ) ];
    · simp_all +decide [ Prod.dist_eq ];
      constructor <;> linarith;
  -- Set `m := |(Df C).det| / 2` and `M := ‖Df C‖ + 1`.
  obtain ⟨m, hm_pos, hm⟩ : ∃ m > 0, ∀ᶠ x in nhds C, m ≤ |(fderiv ℝ (fmap c) x).det| := by
    have h_cont_det : ContinuousAt (fun x => |(fderiv ℝ (fmap c) x).det|) C := by
      have h_cont_det : ContinuousAt (fun x => (fderiv ℝ (fmap c) x)) C := by
        have h_cont : ContDiffAt ℝ 1 (fmap c) C := by
          exact fmap_contDiffAt c xC yC hyC harea;
        have := h_cont;
        rw [ contDiffAt_one_iff ] at this;
        obtain ⟨ f', u, hu, hf', hf'' ⟩ := this; exact ContinuousAt.congr ( hf'.continuousAt hu ) ( Filter.eventuallyEq_of_mem hu fun x hx => HasFDerivAt.fderiv ( hf'' x hx ) ▸ rfl ) ;
      exact ContinuousAt.abs ( continuous_clm_det.continuousAt.comp h_cont_det );
    exact ⟨ |(fderiv ℝ (fmap c) C).det| / 2, half_pos ( abs_pos.mpr ( by simpa using fmap_fderiv_det_ne c xC yC hc hyC harea ) ), h_cont_det.eventually ( le_mem_nhds ( half_lt_self ( abs_pos.mpr ( by simpa using fmap_fderiv_det_ne c xC yC hc hyC harea ) ) ) ) ⟩
  obtain ⟨M, hM_pos, hM⟩ : ∃ M > 0, ∀ᶠ x in nhds C, ‖fderiv ℝ (fmap c) x‖ ≤ M := by
    have h_cont : ContinuousAt (fun x => ‖fderiv ℝ (fmap c) x‖) C := by
      have h_cont : ContDiffAt ℝ 1 (fmap c) C := by
        exact fmap_contDiffAt c xC yC hyC harea;
      have := h_cont.continuousAt_fderiv;
      exact ContinuousAt.norm ( this one_ne_zero );
    exact ⟨ ‖fderiv ℝ ( fmap c ) C‖ + 1, by positivity, h_cont.eventually ( ge_mem_nhds <| lt_add_one _ ) ⟩;
  obtain ⟨r0, hr0_pos, hr0⟩ : ∃ r0 > 0, Metric.ball C r0 ⊆ Metric.ball C rInj ∧ (∀ x ∈ Metric.ball C r0, m ≤ |(fderiv ℝ (fmap c) x).det|) ∧ (∀ x ∈ Metric.ball C r0, ‖fderiv ℝ (fmap c) x‖ ≤ M) ∧ (∀ x ∈ Metric.ball C r0, DifferentiableAt ℝ (fmap c) x) := by
    have h_diff : ∀ᶠ x in nhds C, DifferentiableAt ℝ (fmap c) x := by
      have := fmap_contDiffAt c xC yC hyC harea;
      exact this.eventually ( by norm_num ) |> fun h => h.mono fun x hx => hx.differentiableAt ( by norm_num );
    obtain ⟨ r0, hr0 ⟩ := Metric.mem_nhds_iff.mp ( hm.and ( hM.and h_diff ) );
    exact ⟨ Min.min r0 rInj, lt_min hr0.1 hrInj_pos, Metric.ball_subset_ball ( min_le_right _ _ ), fun x hx => hr0.2 ( Metric.ball_subset_ball ( min_le_left _ _ ) hx ) |>.1, fun x hx => hr0.2 ( Metric.ball_subset_ball ( min_le_left _ _ ) hx ) |>.2.1, fun x hx => hr0.2 ( Metric.ball_subset_ball ( min_le_left _ _ ) hx ) |>.2.2 ⟩;
  refine' ⟨ m, M, r0, hm_pos, hM_pos, hr0_pos, _, _, _, _ ⟩;
  · exact fun x hx => DifferentiableAt.hasFDerivAt ( hr0.2.2.2 x hx ) |> HasFDerivAt.hasFDerivWithinAt;
  · exact hr0.2.1;
  · exact hrInj.mono hr0.1;
  · intro x hx
    have h_lip : ‖fmap c x - fmap c C‖ ≤ M * ‖x - C‖ := by
      have := @Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le;
      specialize this (fun x hx => (hr0.2.2.2 x hx).hasFDerivAt.hasFDerivWithinAt) (fun x hx => hr0.2.2.1 x hx) (convex_ball C r0) (Metric.mem_ball_self hr0_pos) hx;
      exact this;
    simpa only [dist_eq_norm, show fmap c C = C from by
                        ext i; fin_cases i <;> simp +decide [ fmap ] ;
                        · exact fmap_fixed c xC yC hc hyC harea |>.1;
                        · exact fmap_fixed c xC yC hc hyC harea |>.2 ] using h_lip
/-
**Sign conditions near `C`.**  All the algebraic sign conditions used to build the cyclic
quadrilateral hold on a small ball around `C = (xC,yC)`: they hold strictly at `C` and are
continuous, so they persist on a neighborhood.
-/
lemma fmap_sign_conditions (c xC yC : ℝ) (hc : 0 < c) (hyC : 0 < yC) (harea : c * yC = 2) :
    ∃ ε1 > 0, ∀ x : Pt, dist x (!₂[xC, yC] : Pt) < ε1 →
      0 < x 1 ∧ 0 < Pcoef c (x 0) (x 1) ∧ 0 ≤ discr c (x 0) (x 1)
        ∧ Qcoef c (x 0) (x 1) < 0 ∧ 0 < 2 * Pcoef c (x 0) (x 1) * yC + Qcoef c (x 0) (x 1) := by
  classical
  convert Metric.eventually_nhds_iff.mp _ using 1;
  refine' Filter.eventually_and.mpr ⟨ _, _ ⟩;
  · have h_proj_cont : Continuous (fun x : Pt => x 1) := by
      fun_prop;
    exact h_proj_cont.continuousAt.eventually ( lt_mem_nhds hyC );
  · refine' Filter.eventually_and.mpr ⟨ _, _ ⟩;
    · refine' Metric.eventually_nhds_iff.mpr _;
      have h_cont : Continuous (fun y : Pt => Pcoef c (y 0) (y 1)) := by
        apply_rules [ Continuous.add, Continuous.mul, continuous_const, continuous_apply ];
        · exact continuous_apply 0 |> Continuous.comp <| continuous_induced_dom;
        · exact continuous_apply 0 |> Continuous.comp <| continuous_induced_dom;
        · fun_prop;
        · fun_prop;
      exact Metric.mem_nhds_iff.mp ( h_cont.continuousAt.eventually ( lt_mem_nhds <| show 0 < Pcoef c xC yC from by unfold Pcoef; nlinarith ) );
    · refine' Filter.eventually_and.mpr ⟨ _, _ ⟩;
      · refine' ContinuousAt.preimage_mem_nhds _ _;
        · unfold discr Qcoef Pcoef Rcoef; fun_prop;
        · refine' Ici_mem_nhds _;
          unfold discr Qcoef Pcoef Rcoef; norm_num; ring_nf;
          rw [ show c = 2 / yC by rw [ eq_div_iff hyC.ne' ] ; linarith ] ; ring_nf;
          field_simp;
          nlinarith [ sq_nonneg ( xC * yC - 2 ), sq_nonneg ( xC * yC ^ 2 - 2 * yC ), sq_nonneg ( xC ^ 2 * yC - 2 * xC ), sq_nonneg ( xC ^ 2 * yC ^ 2 - 4 ), pow_pos hyC 3, pow_pos hyC 4, pow_pos hyC 5, pow_pos hyC 6, pow_pos hyC 7, pow_pos hyC 8 ];
      · refine' Filter.eventually_and.mpr ⟨ _, _ ⟩;
        · refine' ContinuousAt.preimage_mem_nhds ( show ContinuousAt ( fun x : Pt => Qcoef c ( x.ofLp 0 ) ( x.ofLp 1 ) ) ( !₂[xC, yC] ) from _ ) ( Iio_mem_nhds _ );
          · refine' Continuous.continuousAt _;
            apply_rules [ Continuous.sub, Continuous.add, Continuous.mul, continuous_const, continuous_apply ];
            all_goals fun_prop;
          · unfold Qcoef;
            nlinarith! [ sq_nonneg ( xC - c ), sq_nonneg ( yC - c ), mul_pos hc hyC ];
        · refine' ContinuousAt.preimage_mem_nhds ( show ContinuousAt ( fun x : Pt => 2 * Pcoef c ( x.ofLp 0 ) ( x.ofLp 1 ) * yC + Qcoef c ( x.ofLp 0 ) ( x.ofLp 1 ) ) _ from _ ) ( Ioi_mem_nhds _ );
          · unfold Pcoef Qcoef; fun_prop;
          · unfold Pcoef Qcoef; norm_num [ harea ] ; ring_nf ;
            nlinarith [ sq_nonneg ( xC - c ), sq_nonneg ( yC - 1 ), mul_pos hc hyC ]
/-- **The analytic overlap (perturbation + density).**  Given a configuration, there is a point
`D = (xD, yD)` in `S`, lying just below the apex `C` (`0 < yD`, `c·yD < 2`, i.e. `yD < yC`), inside
the region where the perturbation map is a local diffeomorphism (`discr ≥ 0`, `Pcoef > 0`,
`Qcoef < 0`, `2·Pcoef·yC + Qcoef > 0`), and such that its image `E = f(D)` is also in `S`.
This is the heart of the second half of the paper: it combines the inverse/implicit function theorem
(local invertibility of `f`), the change-of-variables formula, and the Lebesgue density of `S` at
`C` in an overlap argument. -/
lemma exists_lower_pair (S : Set Pt) (c xC yC : ℝ) (h : Config S c xC yC) :
    ∃ xD yD : ℝ, (!₂[xD, yD] : Pt) ∈ S
      ∧ (!₂[xEval c xD yD, yEval c xD yD] : Pt) ∈ S
      ∧ 0 < yD ∧ c * yD < 2 ∧ 0 < Pcoef c xD yD ∧ 0 ≤ discr c xD yD
      ∧ Qcoef c xD yD < 0 ∧ 0 < 2 * Pcoef c xD yD * yC + Qcoef c xD yD := by
  classical
  have hc := h.c_pos
  have hyC := h.yC_pos
  have harea := h.area
  obtain ⟨m, M, r0, hm, hM, hr0, hderiv, hdet, hinj, hLip⟩ :=
    fmap_isDiffeoData c xC yC hc hyC harea
  obtain ⟨ε1, hε1, hsign⟩ := fmap_sign_conditions c xC yC hc hyC harea
  have hdens : IsDensityPt S (!₂[xC, yC] : Pt) := h.dens
  set ε := min ε1 r0 with hεdef
  have hεpos : 0 < ε := lt_min hε1 hr0
  obtain ⟨D, hDε, hDbelow, hDS, hfDS⟩ :=
    overlap_of_diffeo S (!₂[xC, yC] : Pt) (fmap c) (fun x => fderiv ℝ (fmap c) x)
      m M r0 hm hM hr0 h.meas hderiv hdet hinj hLip hdens ε hεpos
  have hsignD := hsign D (lt_of_lt_of_le hDε (min_le_left _ _))
  have hD1lt : D 1 < yC := by
    have h2 := hDbelow
    simpa using h2
  refine ⟨D 0, D 1, ?_, ?_, hsignD.1, ?_, hsignD.2.1, hsignD.2.2.1,
    hsignD.2.2.2.1, hsignD.2.2.2.2⟩
  · have hDeq : (!₂[D 0, D 1] : Pt) = D := by
      ext i; fin_cases i <;> simp
    rw [hDeq]; exact hDS
  · have hEeq : (!₂[xEval c (D 0) (D 1), yEval c (D 0) (D 1)] : Pt) = fmap c D := rfl
    rw [hEeq]; exact hfDS
  · have h2 : c * D 1 < c * yC := mul_lt_mul_of_pos_left hD1lt hc
    rwa [harea] at h2
/-- **Second half of the proof.** The perturbation argument: given a configuration, one finds two
further points `D, E ∈ S` such that `A B E D` is a unit cyclic quadrilateral. -/
lemma exists_quad_of_config (S : Set Pt) (c xC yC : ℝ) (h : Config S c xC yC) :
    ∃ D E : Pt, D ∈ S ∧ E ∈ S ∧
      UnitCyclicQuad (!₂[(0 : ℝ), (0 : ℝ)] : Pt) (!₂[c, (0 : ℝ)] : Pt) E D := by
  classical
  obtain ⟨xD, yD, hDS, hES, hyD, hyD', hP, hdisc, hQ, hpos⟩ := exists_lower_pair S c xC yC h
  have hc := h.c_pos
  have hyC := h.yC_pos
  have harea := h.area
  have hyEpos : 0 < yEval c xD yD := yEval_pos c xD yD hP hQ
  have hyDlt : yD < yC := by
    have : c * yD < c * yC := by rw [harea]; exact hyD'
    exact lt_of_mul_lt_mul_left this hc.le
  have hyElt : yEval c xD yD < yC :=
    yEval_lt_yC c xD yD yC hyC harea hyD hyDlt hP hdisc hpos
  have hcyE : c * yEval c xD yD < 2 := by
    have : c * yEval c xD yD < c * yC := by exact mul_lt_mul_of_pos_left hyElt hc
    rwa [harea] at this
  refine ⟨!₂[xD, yD], !₂[xEval c xD yD, yEval c xD yD], hDS, hES, ?_, ?_, ?_⟩
  · exact concyclic_ABED c xD yD hyD hc hP hdisc
  · exact convex_ABED c xD yD hc hyD hyD' hyEpos hcyE
  · exact quadArea_ABED c xD yD hyD.ne'
/- ===================== Main ===================== -/
/-- **Theorem (Kovac-Predojevic).**
Every measurable planar set `A` of infinite Lebesgue measure contains the four vertices of a
cyclic quadrilateral of area `1`. -/
theorem exists_unitCyclicQuad_of_volume_infinite
    (A : Set Pt) (hA : MeasurableSet A) (hA_inf : volume A = ⊤) :
    ∃ P Q R S : Pt, P ∈ A ∧ Q ∈ A ∧ R ∈ A ∧ S ∈ A ∧ UnitCyclicQuad P Q R S := by
  classical
  obtain ⟨a, b, v1, v2, c, xC, yC, hab, hcfg⟩ := exists_config A hA hA_inf
  obtain ⟨D, E, hD, hE, hquad⟩ := exists_quad_of_config (rigid a b v1 v2 '' A) c xC yC hcfg
  obtain ⟨pA, hpA, hpAeq⟩ := hcfg.memA
  obtain ⟨pB, hpB, hpBeq⟩ := hcfg.memB
  obtain ⟨pE, hpE, hpEeq⟩ := hE
  obtain ⟨pD, hpD, hpDeq⟩ := hD
  refine ⟨pA, pB, pE, pD, hpA, hpB, hpE, hpD, ?_⟩
  have key := (unitCyclicQuad_rigid_iff (v1 := v1) (v2 := v2) hab pA pB pE pD).mp
  rw [hpAeq, hpBeq, hpEeq, hpDeq] at key
  exact key hquad

end CyclicQuad
end Erdos353
