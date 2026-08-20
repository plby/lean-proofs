import ErdosProblems.Erdos733.ST.PolygonalArcInteriorTwoRaySectorModel
import ErdosProblems.Erdos733.ST.PolygonalArcEndpointTaperedWedgeModel
import ErdosProblems.Erdos733.ST.PolygonalArcEndpointDiskCappedTaperModel
import ErdosProblems.Erdos733.ST.PolygonalArcEndpointDiskCappedTaperChartTransport
import ErdosProblems.Erdos733.ST.PolygonalArcInitialEndpointDiskCappedTaperSideLabelling
import ErdosProblems.Erdos733.ST.PolygonalArcTerminalEndpointDiskCappedTaperSideLabelling
import ErdosProblems.Erdos733.ST.PolygonalArcInitialEndpointDiskCappedTaperAttachmentStrengthening
import ErdosProblems.Erdos733.ST.PolygonalArcTerminalEndpointDiskCappedTaperAttachmentStrengthening
import ErdosProblems.Erdos733.ST.PolygonalArcInteriorTwoRaySectorOrientationChoice
import ErdosProblems.Erdos733.ST.PolygonalArcInteriorTwoRaySectorChartTransport
import ErdosProblems.Erdos733.ST.PolygonalArcInteriorIncomingFramePositiveHalfTubeSectorRouting
import ErdosProblems.Erdos733.ST.PolygonalArcInteriorIncomingFrameSignedHalfTubeSectorRouting
import ErdosProblems.Erdos733.ST.PolygonalArcInteriorOutgoingFrameSignedHalfTubeSectorRouting
import ErdosProblems.Erdos733.ST.PolygonalArcOpenSegmentSubsetRelativeInterior
import ErdosProblems.Erdos733.ST.PolygonalArcInteriorVertexMemRelativeInterior
import ErdosProblems.Erdos733.ST.PolygonalArcAdjacentOutwardDirectionsNotSameRay
import ErdosProblems.Erdos733.ST.PolygonalArcCollarLocalTopologyData

open Set
open Classical
noncomputable section


private abbrev E := EuclideanSpace ℝ (Fin 2)

private lemma chart_image_open (p d : E) (hd : d ≠ 0) (S : Set E) (hS : IsOpen S) :
    IsOpen ((fun z : E => p + z 0 • d + z 1 • PlanarRot90 d) '' S) := by
  let chart : E → E := fun z => p + z 0 • d + z 1 • PlanarRot90 d
  let invCoord : E → E :=
    fun q => WithLp.toLp 2 (fun i : Fin 2 =>
      if i = 0 then inner ℝ (q - p) d / (‖d‖ ^ 2)
      else inner ℝ (q - p) (PlanarRot90 d) / (‖d‖ ^ 2))
  have hinv_cont : Continuous invCoord := by
    have hplain : Continuous fun q : E =>
        (fun i : Fin 2 =>
          if i = 0 then inner ℝ (q - p) d / (‖d‖ ^ 2)
          else inner ℝ (q - p) (PlanarRot90 d) / (‖d‖ ^ 2)) := by
      apply continuous_pi
      intro i
      by_cases hi : i = 0
      · simp [hi]
        fun_prop
      · simp [hi]
        fun_prop
    exact (PiLp.continuous_toLp (p := (2 : ENNReal))
      (β := fun _ : Fin 2 => ℝ)).comp hplain
  have hleft_inv : ∀ z : E, invCoord (chart z) = z := by
    intro z
    have hrepz :
        chart z - p = z 0 • d + z 1 • PlanarRot90 d := by
      dsimp [chart]
      abel
    have hcoeff :=
      PlanarRot90CoefficientUniqueness (d := d) (v := chart z - p)
        hd hrepz
    apply PiLp.ext
    intro i
    fin_cases i
    · simpa [invCoord] using hcoeff.1.symm
    · simpa [invCoord] using hcoeff.2.symm
  have hright_inv : ∀ q : E, chart (invCoord q) = q := by
    intro q
    have hdecomp :
        q - p = (invCoord q) 0 • d + (invCoord q) 1 • PlanarRot90 d := by
      simpa [invCoord] using PlanarRot90Decomposition d (q - p) hd
    calc
      chart (invCoord q) =
          p + ((invCoord q) 0 • d + (invCoord q) 1 • PlanarRot90 d) := by
        dsimp [chart]
        abel
      _ = p + (q - p) := by rw [← hdecomp]
      _ = q := by abel
  have himage_eq_preimage (T : Set E) :
      chart '' T = invCoord ⁻¹' T := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [hleft_inv z] using hz
    · intro hq
      exact ⟨invCoord q, hq, hright_inv q⟩
  change IsOpen (chart '' S)
  rw [himage_eq_preimage S]
  exact hS.preimage hinv_cont
private lemma chart_injective (p d : E) (hd : d ≠ 0) :
    Function.Injective
      (fun z : E => p + z 0 • d + z 1 • PlanarRot90 d) := by
  let chart : E → E := fun z => p + z 0 • d + z 1 • PlanarRot90 d
  change Function.Injective chart
  intro z w hzw
  have hrepz :
      chart z - p = z 0 • d + z 1 • PlanarRot90 d := by
    dsimp [chart]
    abel
  have hrepw :
      chart z - p = w 0 • d + w 1 • PlanarRot90 d := by
    rw [hzw]
    dsimp [chart]
    abel
  have hcoeffz :=
    PlanarRot90CoefficientUniqueness (d := d) (v := chart z - p) hd hrepz
  have hcoeffw :=
    PlanarRot90CoefficientUniqueness (d := d) (v := chart z - p) hd hrepw
  have hz0 : z 0 = w 0 := by
    rw [hcoeffz.1, hcoeffw.1]
  have hz1 : z 1 = w 1 := by
    rw [hcoeffz.2, hcoeffw.2]
  apply PiLp.ext
  intro k
  fin_cases k
  · exact hz0
  · exact hz1
private lemma chart_continuous (p d : E) :
    Continuous (fun z : E => p + z 0 • d + z 1 • PlanarRot90 d) := by
  have h0 : Continuous fun z : E => z 0 :=
    PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ) 0
  have h1 : Continuous fun z : E => z 1 :=
    PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ) 1
  have hp : Continuous fun _ : E => p := continuous_const
  have hd : Continuous fun _ : E => d := continuous_const
  have hrot : Continuous fun _ : E => PlanarRot90 d := continuous_const
  exact (hp.add (h0.smul hd)).add (h1.smul hrot)
private lemma chart_mem_closure_image (p d : E) {S : Set E} {z : E}
    (hz : z ∈ closure S) :
    p + z 0 • d + z 1 • PlanarRot90 d ∈
      closure ((fun z : E => p + z 0 • d + z 1 • PlanarRot90 d) '' S) := by
  exact
    (image_closure_subset_closure_image
      (f := fun z : E => p + z 0 • d + z 1 • PlanarRot90 d)
      (s := S) (chart_continuous p d)) ⟨z, hz, rfl⟩
private lemma ray_mem_closure (a : ℝ) {S : Set E} {x w : E}
    (hxC : x ∈ Metric.ball (0 : E) a)
    (hS : ∃ μ : ℝ, 0 < μ ∧
      ∀ δ : ℝ, 0 < δ → δ < μ → x + δ • w ∈ Metric.ball (0 : E) a →
        x + δ • w ∈ S) :
    x ∈ closure S := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  rcases hS with ⟨μ, hμ, hSμ⟩
  let B : ℝ := ‖w‖ + 1
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hmargin : 0 < a - dist (0 : E) x := by
    rw [Metric.mem_ball] at hxC
    rw [dist_comm] at hxC
    linarith
  let δ : ℝ :=
    min (min (ε / (2 * B)) ((a - dist (0 : E) x) / (2 * B))) (μ / 2)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ_eps : δ * ‖w‖ < ε := by
    have hδ_le : δ ≤ ε / (2 * B) := by
      dsimp [δ]
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    have hw_le_B : ‖w‖ ≤ B := by
      dsimp [B]
      linarith [norm_nonneg w]
    have hδB : δ * B ≤ ε / 2 := by
      calc
        δ * B ≤ (ε / (2 * B)) * B :=
          mul_le_mul_of_nonneg_right hδ_le hBpos.le
        _ = ε / 2 := by field_simp [hBpos.ne']
    have hδw_le : δ * ‖w‖ ≤ δ * B :=
      mul_le_mul_of_nonneg_left hw_le_B hδ_pos.le
    nlinarith
  have hδ_μ : δ < μ := by
    have hδ_le : δ ≤ μ / 2 := by
      dsimp [δ]
      exact min_le_right _ _
    nlinarith
  let y : E := x + δ • w
  have hdist_y : dist x y = δ * ‖w‖ := by
    dsimp [y]
    rw [dist_eq_norm]
    have hsub : x - (x + δ • w) = -(δ • w) := by abel
    rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hδ_pos]
  have hyC : y ∈ Metric.ball (0 : E) a := by
    dsimp [y]
    rw [Metric.mem_ball] at hxC ⊢
    rw [dist_comm (x + δ • w) (0 : E)]
    have htri := dist_triangle (0 : E) x (x + δ • w)
    rw [hdist_y] at htri
    have hδ_ball : δ * ‖w‖ < a - dist (0 : E) x := by
      have hδ_le : δ ≤ (a - dist (0 : E) x) / (2 * B) := by
        dsimp [δ]
        exact le_trans (min_le_left _ _) (min_le_right _ _)
      have hw_le_B : ‖w‖ ≤ B := by
        dsimp [B]
        linarith [norm_nonneg w]
      have hδB : δ * B ≤ (a - dist (0 : E) x) / 2 := by
        calc
          δ * B ≤ ((a - dist (0 : E) x) / (2 * B)) * B :=
            mul_le_mul_of_nonneg_right hδ_le hBpos.le
          _ = (a - dist (0 : E) x) / 2 := by field_simp [hBpos.ne']
      have hδw_le : δ * ‖w‖ ≤ δ * B :=
        mul_le_mul_of_nonneg_left hw_le_B hδ_pos.le
      nlinarith
    nlinarith
  refine ⟨y, hSμ δ hδ_pos hδ_μ hyC, ?_⟩
  rw [hdist_y]
  exact hδ_eps
private lemma endpoint_germ_subset_closure_left (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
    let L : Set E :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ 0 < z 1 ∧
        z 1 < K * z 0}
    let G : Set E :=
      {z | 0 < z 0 ∧ z 0 < a ∧ z 1 = 0}
    G ⊆ closure L := by
  intro L G z hzG
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hz0 : 0 < z 0 := by simpa [G] using hzG.1
  have hza : z 0 < a := by simpa [G] using hzG.2.1
  have hz1 : z 1 = 0 := by simpa [G] using hzG.2.2
  have hmargin : 0 < a ^ 2 - z 0 ^ 2 := by nlinarith
  let δ : ℝ :=
    min (min (ε / 2) (K * z 0 / 2)) (min (1 / 2) ((a ^ 2 - z 0 ^ 2) / 2))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ_eps : δ < ε := by
    have hδ_le : δ ≤ ε / 2 := by
      dsimp [δ]
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hδ_K : δ < K * z 0 := by
    have hδ_le : δ ≤ K * z 0 / 2 := by
      dsimp [δ]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    nlinarith [mul_pos hK hz0]
  have hδ_sq : δ ^ 2 < a ^ 2 - z 0 ^ 2 := by
    have hδ_le_half : δ ≤ (a ^ 2 - z 0 ^ 2) / 2 := by
      dsimp [δ]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hδ_le_one : δ ≤ 1 / 2 := by
      dsimp [δ]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    nlinarith [hδ_pos, hδ_le_half, hδ_le_one, hmargin]
  let y : E := WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then z 0 else δ)
  refine ⟨y, ?_, ?_⟩
  · dsimp [L, y]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using hz0
    · nlinarith
    · simp [hδ_pos]
    · simp [hδ_K]
  · rw [EuclideanSpace.dist_eq]
    rw [Fin.sum_univ_two]
    simp [y, hz1, Real.dist_eq]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hδ_pos]
    exact hδ_eps
private lemma endpoint_germ_subset_closure_right (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
    let R : Set E :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧
        z 1 < 0}
    let G : Set E :=
      {z | 0 < z 0 ∧ z 0 < a ∧ z 1 = 0}
    G ⊆ closure R := by
  intro R G z hzG
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hz0 : 0 < z 0 := by simpa [G] using hzG.1
  have hza : z 0 < a := by simpa [G] using hzG.2.1
  have hz1 : z 1 = 0 := by simpa [G] using hzG.2.2
  have hmargin : 0 < a ^ 2 - z 0 ^ 2 := by nlinarith
  let δ : ℝ :=
    min (min (ε / 2) (K * z 0 / 2)) (min (1 / 2) ((a ^ 2 - z 0 ^ 2) / 2))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ_eps : δ < ε := by
    have hδ_le : δ ≤ ε / 2 := by
      dsimp [δ]
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hδ_K : δ < K * z 0 := by
    have hδ_le : δ ≤ K * z 0 / 2 := by
      dsimp [δ]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    nlinarith [mul_pos hK hz0]
  have hδ_sq : δ ^ 2 < a ^ 2 - z 0 ^ 2 := by
    have hδ_le_half : δ ≤ (a ^ 2 - z 0 ^ 2) / 2 := by
      dsimp [δ]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hδ_le_one : δ ≤ 1 / 2 := by
      dsimp [δ]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    nlinarith [hδ_pos, hδ_le_half, hδ_le_one, hmargin]
  let y : E := WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then z 0 else -δ)
  refine ⟨y, ?_, ?_⟩
  · dsimp [R, y]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using hz0
    · nlinarith
    · simp
      nlinarith
    · simp [hδ_pos]
  · rw [EuclideanSpace.dist_eq]
    rw [Fin.sum_univ_two]
    simp [y, hz1, Real.dist_eq, abs_of_pos hδ_pos]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hδ_pos]
    exact hδ_eps
private lemma twoRay_base_subset_closure_left (a c s : ℝ)
    (hpos : 0 < s ∨ s = 0 ∧ c < 0) :
    let C : Set E := Metric.ball (0 : E) a
    let Gbase : Set E := {z | z ∈ C ∧ z 1 = 0 ∧ 0 < z 0}
    let L : Set E := {z | z ∈ C ∧ 0 < z 1 ∧ c * z 1 - s * z 0 < 0}
    Gbase ⊆ closure L := by
  intro C Gbase L z hzG
  have hzC : z ∈ Metric.ball (0 : E) a := by simpa [C, Gbase] using hzG.1
  have hz1 : z 1 = 0 := by simpa [Gbase] using hzG.2.1
  have hz0 : 0 < z 0 := by simpa [Gbase] using hzG.2.2
  let w : E :=
    if 0 < s then
      WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then c + 1 else s)
    else
      WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then 0 else 1)
  have hw1_pos : 0 < w 1 := by
    dsimp [w]
    split_ifs with hs
    · simpa using hs
    · norm_num
  have hcross_w : c * w 1 - s * w 0 < 0 := by
    dsimp [w]
    split_ifs with hs
    · simp
      nlinarith
    · simp
      rcases hpos with hspos | ⟨hs0, hc⟩
      · exact (hs hspos).elim
      · nlinarith
  have hcross_z : c * z 1 - s * z 0 ≤ 0 := by
    rw [hz1]
    rcases hpos with hs | ⟨hs0, _⟩
    · nlinarith
    · rw [hs0]
      ring_nf
      norm_num
  refine ray_mem_closure (S := L) (x := z) (w := w) a hzC ?_
  refine ⟨1, by norm_num, ?_⟩
  intro δ hδ_pos _ hyC
  dsimp [L]
  refine ⟨hyC, ?_, ?_⟩
  · rw [hz1]
    nlinarith only [hδ_pos, hw1_pos]
  · have hcross_y :
        c * (z 1 + δ * w 1) - s * (z 0 + δ * w 0) =
          (c * z 1 - s * z 0) + δ * (c * w 1 - s * w 0) := by
      ring
    rw [hcross_y]
    nlinarith only [hcross_z, hδ_pos, hcross_w]
private lemma twoRay_base_subset_closure_right (a c s : ℝ) :
    let C : Set E := Metric.ball (0 : E) a
    let Gbase : Set E := {z | z ∈ C ∧ z 1 = 0 ∧ 0 < z 0}
    let R : Set E := {z | z ∈ C ∧ (z 1 < 0 ∨ 0 < c * z 1 - s * z 0)}
    Gbase ⊆ closure R := by
  intro C Gbase R z hzG
  have hzC : z ∈ Metric.ball (0 : E) a := by simpa [C, Gbase] using hzG.1
  have hz1 : z 1 = 0 := by simpa [Gbase] using hzG.2.1
  let w : E := WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then 0 else -1)
  refine ray_mem_closure (S := R) (x := z) (w := w) a hzC ?_
  refine ⟨1, by norm_num, ?_⟩
  intro δ hδ_pos _ hyC
  dsimp [R]
  refine ⟨hyC, Or.inl ?_⟩
  rw [hz1]
  simp [w]
  linarith only [hδ_pos]
private lemma twoRay_origin_mem_closure_left (a c s : ℝ) (ha : 0 < a)
    (hpos : 0 < s ∨ s = 0 ∧ c < 0) :
    let C : Set E := Metric.ball (0 : E) a
    let L : Set E := {z | z ∈ C ∧ 0 < z 1 ∧ c * z 1 - s * z 0 < 0}
    (0 : E) ∈ closure L := by
  intro C L
  let w : E :=
    if 0 < s then
      WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then c + 1 else s)
    else
      WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then 0 else 1)
  have hw1_pos : 0 < w 1 := by
    dsimp [w]
    split_ifs with hs
    · simpa using hs
    · norm_num
  have hcross_w : c * w 1 - s * w 0 < 0 := by
    dsimp [w]
    split_ifs with hs
    · simp
      nlinarith
    · simp
      rcases hpos with hspos | ⟨hs0, hc⟩
      · exact (hs hspos).elim
      · nlinarith
  have h0C : (0 : E) ∈ Metric.ball (0 : E) a := by
    simpa [Metric.mem_ball] using ha
  refine ray_mem_closure (S := L) (x := (0 : E)) (w := w) a h0C ?_
  refine ⟨1, by norm_num, ?_⟩
  intro δ hδ_pos _ hyC
  dsimp [L]
  refine ⟨hyC, ?_, ?_⟩
  · simpa only [zero_add] using mul_pos hδ_pos hw1_pos
  · have hcross : c * (δ * w 1) - s * (δ * w 0) =
        δ * (c * w 1 - s * w 0) := by ring
    simp only [zero_add]
    rw [hcross]
    exact mul_neg_of_pos_of_neg hδ_pos hcross_w
private lemma twoRay_origin_mem_closure_right (a c s : ℝ) (ha : 0 < a) :
    let C : Set E := Metric.ball (0 : E) a
    let R : Set E := {z | z ∈ C ∧ (z 1 < 0 ∨ 0 < c * z 1 - s * z 0)}
    (0 : E) ∈ closure R := by
  intro C R
  let w : E := WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then 0 else -1)
  have h0C : (0 : E) ∈ Metric.ball (0 : E) a := by
    simpa [Metric.mem_ball] using ha
  refine ray_mem_closure (S := R) (x := (0 : E)) (w := w) a h0C ?_
  refine ⟨1, by norm_num, ?_⟩
  intro δ hδ_pos _ hyC
  dsimp [R]
  refine ⟨hyC, Or.inl ?_⟩
  rw [zero_add]
  simp [w]
  linarith only [hδ_pos]
private lemma twoRay_other_subset_closure_left (a c s : ℝ)
    (hpos : 0 < s ∨ s = 0 ∧ c < 0) :
    let C : Set E := Metric.ball (0 : E) a
    let Gother : Set E :=
      {z | z ∈ C ∧ ∃ t : ℝ, 0 < t ∧ z 0 = t * c ∧ z 1 = t * s}
    let L : Set E := {z | z ∈ C ∧ 0 < z 1 ∧ c * z 1 - s * z 0 < 0}
    Gother ⊆ closure L := by
  intro C Gother L z hzG
  have hzC : z ∈ Metric.ball (0 : E) a := by simpa [C, Gother] using hzG.1
  rcases hzG.2 with ⟨t, ht, hz0, hz1⟩
  let w : E := WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then s else -c)
  have hnorm_dir : 0 < c ^ 2 + s ^ 2 := by
    rcases hpos with hs | ⟨hs0, hc⟩
    · nlinarith
    · nlinarith
  have hmu_pos : 0 < (if 0 < s then t * s / (2 * (|c| + 1)) else 1) := by
    split_ifs with hs
    · positivity
    · norm_num
  refine ray_mem_closure (S := L) (x := z) (w := w) a hzC ?_
  refine ⟨(if 0 < s then t * s / (2 * (|c| + 1)) else 1), hmu_pos, ?_⟩
  intro δ hδ_pos hδ_lt hyC
  dsimp [L]
  refine ⟨hyC, ?_, ?_⟩
  · dsimp [w]
    by_cases hs : 0 < s
    · have hδ_bound : δ < t * s / (2 * (|c| + 1)) := by
        simpa [hs] using hδ_lt
      have hc_abs : c ≤ |c| := le_abs_self c
      rw [hz1]
      simp
      have hδc_le : δ * c ≤ δ * |c| :=
        mul_le_mul_of_nonneg_left hc_abs hδ_pos.le
      have hδ_abs : δ * (|c| + 1) < t * s / 2 := by
        calc
          δ * (|c| + 1) < (t * s / (2 * (|c| + 1))) * (|c| + 1) :=
            mul_lt_mul_of_pos_right hδ_bound (by positivity)
          _ = t * s / 2 := by field_simp [show |c| + 1 ≠ 0 by positivity]
      nlinarith [hδc_le, hδ_abs, hδ_pos, abs_nonneg c]
    · rcases hpos with hspos | ⟨hs0, hc⟩
      · exact (hs hspos).elim
      · rw [hz1, hs0]
        simp
        nlinarith
  · dsimp [w]
    rw [hz0, hz1]
    simp
    have : c * (t * s - δ * c) - s * (t * c + δ * s) =
        -δ * (c ^ 2 + s ^ 2) := by ring
    nlinarith
private lemma twoRay_other_subset_closure_right (a c s : ℝ)
    (hpos : 0 < s ∨ s = 0 ∧ c < 0) :
    let C : Set E := Metric.ball (0 : E) a
    let Gother : Set E :=
      {z | z ∈ C ∧ ∃ t : ℝ, 0 < t ∧ z 0 = t * c ∧ z 1 = t * s}
    let R : Set E := {z | z ∈ C ∧ (z 1 < 0 ∨ 0 < c * z 1 - s * z 0)}
    Gother ⊆ closure R := by
  intro C Gother R z hzG
  have hzC : z ∈ Metric.ball (0 : E) a := by simpa [C, Gother] using hzG.1
  rcases hzG.2 with ⟨t, ht, hz0, hz1⟩
  let w : E := WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then -s else c)
  have hnorm_dir : 0 < c ^ 2 + s ^ 2 := by
    rcases hpos with hs | ⟨hs0, hc⟩
    · nlinarith
    · nlinarith
  refine ray_mem_closure (S := R) (x := z) (w := w) a hzC ?_
  refine ⟨1, by norm_num, ?_⟩
  intro δ hδ_pos _ hyC
  dsimp [R]
  refine ⟨hyC, Or.inr ?_⟩
  dsimp [w]
  rw [hz0, hz1]
  simp
  have : c * (t * s + δ * c) - s * (t * c - δ * s) =
      δ * (c ^ 2 + s ^ 2) := by ring
  nlinarith
private lemma image_disjoint_of_injective {f : E → E} (hf : Function.Injective f)
    {A B : Set E} (hAB : Disjoint A B) :
    Disjoint (f '' A) (f '' B) := by
  rw [Set.disjoint_left]
  rintro q ⟨x, hxA, rfl⟩ ⟨y, hyB, hyx⟩
  have hy_eq : y = x := hf hyx
  rw [hy_eq] at hyB
  exact (Set.disjoint_left.mp hAB) hxA hyB
private lemma chart_axis_eq_lineMap
    (p0 p1 z : EuclideanSpace ℝ (Fin 2)) (hz : z 1 = 0) :
    p0 + z 0 • (p1 - p0) + z 1 • PlanarRot90 (p1 - p0) =
      AffineMap.lineMap p0 p1 (z 0) := by
  apply PiLp.ext
  intro k
  fin_cases k <;>
    simp [AffineMap.lineMap_apply_module, PlanarRot90, hz] <;>
    ring
private lemma chart_axis_param_eq_lineMap
    (p0 p1 : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    p0 + t • (p1 - p0) =
      AffineMap.lineMap p0 p1 t := by
  apply PiLp.ext
  intro k
  fin_cases k <;>
    simp [AffineMap.lineMap_apply_module] <;>
    ring
private lemma leftHalf_inter_subset_of_nonincident
    {γ : PolygonalArc} {η : ℝ}
    {controlRadii : PolygonalArcCollarControlRadii γ η}
    {middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii}
    {forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments}
    {sep :
      PolygonalArcCollarSeparatedTubeData γ controlRadii middleSegments
        forbiddenMargins}
    {vertexLocalPieces :
      PolygonalArcCollarVertexLocalPieceData γ controlRadii middleSegments
        forbiddenMargins sep}
    (i : Fin γ.vertices.length) (C L : Set E)
    (hCsub : C ⊆ vertexLocalPieces.vertexDisk i)
    (j : ℕ) (hj : j + 1 < γ.vertices.length)
    (hne_left : i.1 ≠ j) (hne_right : i.1 ≠ j + 1) :
    sep.leftHalf j hj ∩ C ⊆ L := by
  intro x hx
  exfalso
  have hdisj :=
    vertexLocalPieces.vertexDisk_disjoint_nonincident_tubes i j hj
      hne_left hne_right
  have hxDisk : x ∈ vertexLocalPieces.vertexDisk i := hCsub hx.2
  have hxTube : x ∈ sep.tube j hj := sep.leftHalf_subset_tube j hj hx.1
  exact (Set.disjoint_left.mp hdisj) hxDisk hxTube
private lemma rightHalf_inter_subset_of_nonincident
    {γ : PolygonalArc} {η : ℝ}
    {controlRadii : PolygonalArcCollarControlRadii γ η}
    {middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii}
    {forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments}
    {sep :
      PolygonalArcCollarSeparatedTubeData γ controlRadii middleSegments
        forbiddenMargins}
    {vertexLocalPieces :
      PolygonalArcCollarVertexLocalPieceData γ controlRadii middleSegments
        forbiddenMargins sep}
    (i : Fin γ.vertices.length) (C R : Set E)
    (hCsub : C ⊆ vertexLocalPieces.vertexDisk i)
    (j : ℕ) (hj : j + 1 < γ.vertices.length)
    (hne_left : i.1 ≠ j) (hne_right : i.1 ≠ j + 1) :
    sep.rightHalf j hj ∩ C ⊆ R := by
  intro x hx
  exfalso
  have hdisj :=
    vertexLocalPieces.vertexDisk_disjoint_nonincident_tubes i j hj
      hne_left hne_right
  have hxDisk : x ∈ vertexLocalPieces.vertexDisk i := hCsub hx.2
  have hxTube : x ∈ sep.tube j hj := sep.rightHalf_subset_tube j hj hx.1
  exact (Set.disjoint_left.mp hdisj) hxDisk hxTube

private def localTopologyGood
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (compatibleTubes :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (vertexLocalPieces :
      PolygonalArcCollarVertexLocalPieceData γ controlRadii middleSegments
        forbiddenMargins
        compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData)
    (i : Fin γ.vertices.length) (C L R : Set E) : Prop :=
  let sep :=
    compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
  IsOpen C ∧ IsOpen L ∧ IsOpen R ∧
    C ⊆ vertexLocalPieces.vertexDisk i ∧
    (0 < i.1 → i.1 + 1 < γ.vertices.length →
      C = vertexLocalPieces.vertexDisk i) ∧
    ((i.1 = 0 ∨ i.1 + 1 = γ.vertices.length) →
      γ.vertices[i.1] ∉ C) ∧
    L ⊆ C ∧ R ⊆ C ∧
    IsConnected L ∧ IsConnected R ∧
    Disjoint L γ.carrier ∧ Disjoint R γ.carrier ∧
    Disjoint L R ∧
    (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      sep.leftHalf j hj ∩ C ⊆ L) ∧
    (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      sep.rightHalf j hj ∩ C ⊆ R) ∧
    C \ γ.relativeInterior = L ∪ R ∧
    (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      i = ⟨j, Nat.lt_of_succ_lt hj⟩ →
        (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
            Set.Ioo (0 : ℝ)
              (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
                dist γ.vertices[j] γ.vertices[j + 1]) ⊆ C) ∧
    (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      i = ⟨j + 1, hj⟩ →
        (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
            Set.Ioo
              (1 - controlRadii.radius ⟨j + 1, hj⟩ /
                dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) ⊆ C) ∧
    (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      i = ⟨j, Nat.lt_of_succ_lt hj⟩ →
        vertexLocalPieces.outgoingLeftAttachment j hj ⊆ L) ∧
    (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      i = ⟨j, Nat.lt_of_succ_lt hj⟩ →
        vertexLocalPieces.outgoingRightAttachment j hj ⊆ R) ∧
    (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      i = ⟨j + 1, hj⟩ →
        vertexLocalPieces.incomingLeftAttachment j hj ⊆ L) ∧
    (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      i = ⟨j + 1, hj⟩ →
        vertexLocalPieces.incomingRightAttachment j hj ⊆ R) ∧
    (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      i = ⟨j, Nat.lt_of_succ_lt hj⟩ →
        (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
            Set.Ioo (0 : ℝ)
              (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
                dist γ.vertices[j] γ.vertices[j + 1]) ⊆ closure L) ∧
    (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      i = ⟨j, Nat.lt_of_succ_lt hj⟩ →
        (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
            Set.Ioo (0 : ℝ)
              (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
                dist γ.vertices[j] γ.vertices[j + 1]) ⊆ closure R) ∧
    (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      i = ⟨j + 1, hj⟩ →
        (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
            Set.Ioo
              (1 - controlRadii.radius ⟨j + 1, hj⟩ /
                dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) ⊆ closure L) ∧
    (∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      i = ⟨j + 1, hj⟩ →
        (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
            Set.Ioo
              (1 - controlRadii.radius ⟨j + 1, hj⟩ /
                dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) ⊆ closure R) ∧
    (0 < i.1 → i.1 + 1 < γ.vertices.length →
      γ.vertices[i.1] ∈ closure L) ∧
    (0 < i.1 → i.1 + 1 < γ.vertices.length →
      γ.vertices[i.1] ∈ closure R)

private lemma localTopologyGoodInitial
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (compatibleTubes :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (vertexLocalPieces :
      PolygonalArcCollarVertexLocalPieceData γ controlRadii middleSegments
        forbiddenMargins
        compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData)
    (hlen_pos : 0 < γ.vertices.length)
    (hj0 : 0 + 1 < γ.vertices.length) :
    ∃ C L R : Set E,
      localTopologyGood γ controlRadii middleSegments forbiddenMargins
        compatibleTubes vertexLocalPieces ⟨0, hlen_pos⟩ C L R := by
  let sep :=
    compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
  let d0 : E := γ.vertices[0 + 1] - γ.vertices[0]
  let K0 : ℝ := compatibleTubes.initialConeBound 0 hj0
  let chart0 : E → E :=
    fun z => γ.vertices[0] + z 0 • d0 + z 1 • PlanarRot90 d0
  let a0 : ℝ :=
    controlRadii.radius ⟨0, Nat.lt_of_succ_lt hj0⟩ /
      dist γ.vertices[0] γ.vertices[0 + 1]
  let C0 : Set E :=
    {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a0 ^ 2 ∧ -K0 * z 0 < z 1 ∧
      z 1 < K0 * z 0}
  let L0 : Set E :=
    {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a0 ^ 2 ∧ 0 < z 1 ∧
      z 1 < K0 * z 0}
  let R0 : Set E :=
    {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a0 ^ 2 ∧ -K0 * z 0 < z 1 ∧
      z 1 < 0}
  let G0 : Set E :=
    {z | 0 < z 0 ∧ z 0 < a0 ∧ z 1 = 0}
  have hside :=
    PolygonalArcInitialEndpointDiskCappedTaperSideLabelling γ controlRadii
      middleSegments forbiddenMargins compatibleTubes 0 hj0
  change
    0 < a0 ∧
      IsOpen C0 ∧ IsOpen L0 ∧ IsOpen R0 ∧
      IsConnected L0 ∧ IsConnected R0 ∧
      IsConnected (chart0 '' L0) ∧ IsConnected (chart0 '' R0) ∧
      Disjoint L0 R0 ∧ Disjoint (chart0 '' L0) (chart0 '' R0) ∧
      (0 : E) ∉ C0 ∧ G0 ⊆ C0 ∧ C0 \ G0 = L0 ∪ R0 ∧
      (∀ z : E,
        z 0 ^ 2 + z 1 ^ 2 < a0 ^ 2 →
          chart0 z ∈ Metric.ball γ.vertices[0]
            (controlRadii.radius ⟨0, Nat.lt_of_succ_lt hj0⟩)) ∧
      chart0 '' C0 ⊆ Metric.ball γ.vertices[0]
        (controlRadii.radius ⟨0, Nat.lt_of_succ_lt hj0⟩) ∧
      γ.vertices[0] ∉ chart0 '' C0 ∧
      (∀ {t : ℝ}, 0 < t →
        chart0 (WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t else 0)) ≠
          γ.vertices[0]) ∧
      ((AffineMap.lineMap γ.vertices[0] γ.vertices[0 + 1]) ''
          Set.Ioo (0 : ℝ) a0 ⊆ chart0 '' G0) ∧
      chart0 '' C0 \ chart0 '' G0 = chart0 '' L0 ∪ chart0 '' R0 ∧
      sep.leftHalf 0 hj0 ∩ chart0 '' C0 ⊆ chart0 '' L0 ∧
      sep.rightHalf 0 hj0 ∩ chart0 '' C0 ⊆ chart0 '' R0 at hside
  rcases hside with
    ⟨ha0, hC0open, hL0open, hR0open, hL0conn, hR0conn, hchartL0conn,
      hchartR0conn, hLR0disj, hchartLR0disj, hzero0_not_C, hG0subC,
      hmodel_split, hdisk_coord, hchartC0_ball, hvertex0_not_chartC,
      hcoord0_omit, hgerm0, himage_split0, hleft0, hright0⟩
  have hattach :=
    PolygonalArcInitialEndpointDiskCappedTaperAttachmentStrengthening γ
      controlRadii middleSegments forbiddenMargins compatibleTubes 0 hj0
  change
    sep.leftHalf 0 hj0 ∩
        Metric.ball γ.vertices[0]
          (controlRadii.radius ⟨0, Nat.lt_of_succ_lt hj0⟩) ⊆
      chart0 '' L0 ∧
    sep.rightHalf 0 hj0 ∩
        Metric.ball γ.vertices[0]
          (controlRadii.radius ⟨0, Nat.lt_of_succ_lt hj0⟩) ⊆
      chart0 '' R0 at hattach
  rcases hattach with ⟨hleft0_ball, hright0_ball⟩
  have hdist0 : 0 < dist γ.vertices[0] γ.vertices[0 + 1] := by
    have hsum := controlRadii.adjacent_radii_sum_lt (j := 0) hj0
    have hleft := controlRadii.radius_pos ⟨0, Nat.lt_of_succ_lt hj0⟩
    have hright := controlRadii.radius_pos ⟨0 + 1, hj0⟩
    simpa using lt_trans (add_pos hleft hright) hsum
  have hd0 : d0 ≠ 0 := by
    dsimp [d0]
    have hdist0' : 0 < dist γ.vertices[0] γ.vertices[1] := by
      simpa using hdist0
    exact sub_ne_zero.mpr (dist_pos.mp (by simpa using hdist0')).symm
  have hK0 : 0 < K0 := by
    dsimp [K0]
    exact compatibleTubes.initialConeBound_pos 0 hj0
  have hCsub_disk :
      chart0 '' C0 ⊆ vertexLocalPieces.vertexDisk ⟨0, hlen_pos⟩ := by
    intro x hx
    rw [vertexLocalPieces.vertexDisk_eq]
    simpa using hchartC0_ball hx
  have hLsubC : chart0 '' L0 ⊆ chart0 '' C0 := by
    rintro x ⟨z, hz, rfl⟩
    refine ⟨z, ?_, rfl⟩
    dsimp [L0, C0] at hz ⊢
    exact ⟨hz.1, hz.2.1, by nlinarith [hK0, hz.1, hz.2.2.1], hz.2.2.2⟩
  have hRsubC : chart0 '' R0 ⊆ chart0 '' C0 := by
    rintro x ⟨z, hz, rfl⟩
    refine ⟨z, ?_, rfl⟩
    dsimp [R0, C0] at hz ⊢
    exact ⟨hz.1, hz.2.1, hz.2.2.1, by nlinarith [hK0, hz.1, hz.2.2.2]⟩
  have hchart0_inj : Function.Injective chart0 := by
    dsimp [chart0]
    exact chart_injective γ.vertices[0] d0 hd0
  have hLG0disj : Disjoint L0 G0 := by
    rw [Set.disjoint_left]
    intro z hzL hzG
    dsimp [L0] at hzL
    dsimp [G0] at hzG
    linarith [hzL.2.2.1, hzG.2.2]
  have hRG0disj : Disjoint R0 G0 := by
    rw [Set.disjoint_left]
    intro z hzR hzG
    dsimp [R0] at hzR
    dsimp [G0] at hzG
    linarith [hzR.2.2.2, hzG.2.2]
  have hchartLG0disj : Disjoint (chart0 '' L0) (chart0 '' G0) :=
    image_disjoint_of_injective hchart0_inj hLG0disj
  have hchartRG0disj : Disjoint (chart0 '' R0) (chart0 '' G0) :=
    image_disjoint_of_injective hchart0_inj hRG0disj
  have ha0_lt_one : a0 < 1 := by
    have hrad_lt_dist :
        controlRadii.radius ⟨0, Nat.lt_of_succ_lt hj0⟩ <
          dist γ.vertices[0] γ.vertices[0 + 1] := by
      have hsum := controlRadii.adjacent_radii_sum_lt (j := 0) hj0
      have hright := controlRadii.radius_pos ⟨0 + 1, hj0⟩
      linarith
    have hdist0R : (0 : ℝ) < dist γ.vertices[0] γ.vertices[0 + 1] := by
      simpa using hdist0
    dsimp [a0]
    rw [div_lt_iff₀ hdist0R]
    simpa using hrad_lt_dist
  have hG0_subset_relint : chart0 '' G0 ⊆ γ.relativeInterior := by
    rintro x ⟨z, hzG, rfl⟩
    have hz01 : z 0 ∈ Set.Ioo (0 : ℝ) (1 : ℝ) := by
      dsimp [G0] at hzG
      exact ⟨hzG.1, lt_trans hzG.2.1 ha0_lt_one⟩
    have hline_chart :
        chart0 z = AffineMap.lineMap γ.vertices[0] γ.vertices[0 + 1] (z 0) := by
      dsimp [G0] at hzG
      simpa [chart0, d0] using
        chart_axis_eq_lineMap γ.vertices[0] γ.vertices[0 + 1] z hzG.2.2
    rw [hline_chart]
    apply PolygonalArcOpenSegmentSubsetRelativeInterior γ 0 hj0
    exact lineMap_mem_openSegment (𝕜 := ℝ) γ.vertices[0]
      γ.vertices[0 + 1] hz01
  have hcarrier_chartC_subset_G :
      γ.carrier ∩ chart0 '' C0 ⊆ chart0 '' G0 := by
    rintro x ⟨hxcarrier, hxC⟩
    have hxDisk : x ∈ vertexLocalPieces.vertexDisk ⟨0, hlen_pos⟩ :=
      hCsub_disk hxC
    rcases vertexLocalPieces.vertexDisk_carrier_subset_incident_segments
        ⟨0, hlen_pos⟩ x hxDisk hxcarrier with
      ⟨j, hj, hxseg, hincident⟩
    have hj_eq : j = 0 := by
      rcases hincident with hleft_inc | hright_inc
      · have : (0 : ℕ) = j := by simpa using hleft_inc
        exact this.symm
      · have : (0 : ℕ) = j + 1 := by simpa using hright_inc
        omega
    subst j
    rw [segment_eq_image_lineMap] at hxseg
    rcases hxseg with ⟨t, ht, htx⟩
    rcases hxC with ⟨z, hzC, hzx⟩
    let zt : E := WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then t else 0)
    have hline_chart :
        chart0 zt = AffineMap.lineMap γ.vertices[0] γ.vertices[0 + 1] t := by
      simpa [chart0, d0, zt] using
        chart_axis_param_eq_lineMap γ.vertices[0] γ.vertices[0 + 1] t
    have hz_eq : z = zt := by
      apply hchart0_inj
      rw [hzx, ← htx, ← hline_chart]
    have hztC : zt ∈ C0 := by
      simpa [hz_eq] using hzC
    have ht_pos : 0 < t := by
      dsimp [C0, zt] at hztC
      simpa [zt] using hztC.1
    have ht_sq : t ^ 2 < a0 ^ 2 := by
      dsimp [C0, zt] at hztC
      simpa [zt] using hztC.2.1
    have ht_lt_a0 : t < a0 := by
      nlinarith [ha0, ht_pos, ht_sq]
    refine ⟨zt, ?_, ?_⟩
    · dsimp [G0, zt]
      exact ⟨by simpa [zt] using ht_pos, by simpa [zt] using ht_lt_a0,
        by simp [zt]⟩
    · rw [hline_chart, htx]
  have hrel_subset_carrier : γ.relativeInterior ⊆ γ.carrier := by
    intro x hx
    rw [γ.relativeInterior_eq] at hx
    exact hx.1
  have hwithout0 :
      chart0 '' C0 \ γ.relativeInterior = chart0 '' L0 ∪ chart0 '' R0 := by
    calc
      chart0 '' C0 \ γ.relativeInterior = chart0 '' C0 \ chart0 '' G0 := by
        ext x
        constructor
        · rintro ⟨hxC, hxnotRel⟩
          exact ⟨hxC, fun hxG => hxnotRel (hG0_subset_relint hxG)⟩
        · rintro ⟨hxC, hxnotG⟩
          exact ⟨hxC, fun hxRel =>
            hxnotG (hcarrier_chartC_subset_G ⟨hrel_subset_carrier hxRel, hxC⟩)⟩
      _ = chart0 '' L0 ∪ chart0 '' R0 := himage_split0
  refine ⟨chart0 '' C0, chart0 '' L0, chart0 '' R0, ?_⟩
  refine ⟨?_, ?_, ?_, hCsub_disk, ?_, ?_, hLsubC, hRsubC,
    hchartL0conn, hchartR0conn, ?_, ?_, hchartLR0disj, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact chart_image_open γ.vertices[0] d0 hd0 C0 hC0open
  · exact chart_image_open γ.vertices[0] d0 hd0 L0 hL0open
  · exact chart_image_open γ.vertices[0] d0 hd0 R0 hR0open
  · intro hpos _
    have : (0 : ℕ) < 0 := by simpa using hpos
    omega
  · intro _
    exact hvertex0_not_chartC
  · rw [Set.disjoint_left]
    intro x hxL hxcarrier
    exact (Set.disjoint_left.mp hchartLG0disj) hxL
      (hcarrier_chartC_subset_G ⟨hxcarrier, hLsubC hxL⟩)
  · rw [Set.disjoint_left]
    intro x hxR hxcarrier
    exact (Set.disjoint_left.mp hchartRG0disj) hxR
      (hcarrier_chartC_subset_G ⟨hxcarrier, hRsubC hxR⟩)
  · intro j hj
    by_cases hj_zero : j = 0
    · subst j
      simpa using hleft0
    · exact leftHalf_inter_subset_of_nonincident ⟨0, hlen_pos⟩
        (chart0 '' C0) (chart0 '' L0) hCsub_disk j hj
        (by
          change (0 : ℕ) ≠ j
          omega)
        (by
          change (0 : ℕ) ≠ j + 1
          omega)
  · intro j hj
    by_cases hj_zero : j = 0
    · subst j
      simpa using hright0
    · exact rightHalf_inter_subset_of_nonincident ⟨0, hlen_pos⟩
        (chart0 '' C0) (chart0 '' R0) hCsub_disk j hj
        (by
          change (0 : ℕ) ≠ j
          omega)
        (by
          change (0 : ℕ) ≠ j + 1
          omega)
  · exact hwithout0
  · intro j hj hij
    have hj_eq : j = 0 := by
      have hval := congrArg Fin.val hij
      simpa using hval.symm
    subst j
    intro x hx
    exact Set.image_mono hG0subC (hgerm0 hx)
  · intro j hj hij
    have hval := congrArg Fin.val hij
    have : (0 : ℕ) = j + 1 := by simpa using hval
    omega
  · intro j hj hij
    have hj_eq : j = 0 := by
      have hval := congrArg Fin.val hij
      simpa using hval.symm
    subst j
    rw [vertexLocalPieces.outgoingLeftAttachment_eq]
    rintro x hx
    exact hleft0_ball ⟨hx.2, by
      rw [vertexLocalPieces.vertexDisk_eq] at hx
      simpa using hx.1⟩
  · intro j hj hij
    have hj_eq : j = 0 := by
      have hval := congrArg Fin.val hij
      simpa using hval.symm
    subst j
    rw [vertexLocalPieces.outgoingRightAttachment_eq]
    rintro x hx
    exact hright0_ball ⟨hx.2, by
      rw [vertexLocalPieces.vertexDisk_eq] at hx
      simpa using hx.1⟩
  · intro j hj hij
    have hval := congrArg Fin.val hij
    have : (0 : ℕ) = j + 1 := by simpa using hval
    omega
  · intro j hj hij
    have hval := congrArg Fin.val hij
    have : (0 : ℕ) = j + 1 := by simpa using hval
    omega
  · intro j hj hij x hx
    have hj_eq : j = 0 := by
      have hval := congrArg Fin.val hij
      simpa using hval.symm
    subst j
    rcases hgerm0 hx with ⟨z, hzG, rfl⟩
    exact chart_mem_closure_image γ.vertices[0] d0
      ((endpoint_germ_subset_closure_left a0 K0 ha0 hK0) hzG)
  · intro j hj hij x hx
    have hj_eq : j = 0 := by
      have hval := congrArg Fin.val hij
      simpa using hval.symm
    subst j
    rcases hgerm0 hx with ⟨z, hzG, rfl⟩
    exact chart_mem_closure_image γ.vertices[0] d0
      ((endpoint_germ_subset_closure_right a0 K0 ha0 hK0) hzG)
  · intro j hj hij
    have hval := congrArg Fin.val hij
    have : (0 : ℕ) = j + 1 := by simpa using hval
    omega
  · intro j hj hij
    have hval := congrArg Fin.val hij
    have : (0 : ℕ) = j + 1 := by simpa using hval
    omega
  · intro hpos _
    have : (0 : ℕ) < 0 := by simpa using hpos
    omega
  · intro hpos _
    have : (0 : ℕ) < 0 := by simpa using hpos
    omega

private lemma localTopologyGoodTerminal
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (compatibleTubes :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (vertexLocalPieces :
      PolygonalArcCollarVertexLocalPieceData γ controlRadii middleSegments
        forbiddenMargins
        compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData)
    (lastJ : ℕ) (hlastJ : lastJ + 1 < γ.vertices.length)
    (hlastJ_succ : lastJ + 2 = γ.vertices.length) :
    ∃ C L R : Set E,
      localTopologyGood γ controlRadii middleSegments forbiddenMargins
        compatibleTubes vertexLocalPieces ⟨lastJ + 1, hlastJ⟩ C L R := by
  let sep :=
    compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
  let dT : E := γ.vertices[lastJ] - γ.vertices[lastJ + 1]
  let KT : ℝ := compatibleTubes.terminalConeBound lastJ hlastJ
  let chartT : E → E :=
    fun z => γ.vertices[lastJ + 1] + z 0 • dT + z 1 • PlanarRot90 dT
  let aT : ℝ :=
    controlRadii.radius ⟨lastJ + 1, hlastJ⟩ /
      dist γ.vertices[lastJ + 1] γ.vertices[lastJ]
  let CT : Set E :=
    {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < aT ^ 2 ∧ -KT * z 0 < z 1 ∧
      z 1 < KT * z 0}
  let LT : Set E :=
    {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < aT ^ 2 ∧ 0 < z 1 ∧
      z 1 < KT * z 0}
  let RT : Set E :=
    {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < aT ^ 2 ∧ -KT * z 0 < z 1 ∧
      z 1 < 0}
  let GT : Set E :=
    {z | 0 < z 0 ∧ z 0 < aT ∧ z 1 = 0}
  have hside :=
    PolygonalArcTerminalEndpointDiskCappedTaperSideLabelling γ controlRadii
      middleSegments forbiddenMargins compatibleTubes lastJ hlastJ
  change
    0 < aT ∧
      IsOpen CT ∧ IsOpen LT ∧ IsOpen RT ∧
      IsConnected LT ∧ IsConnected RT ∧
      IsConnected (chartT '' LT) ∧ IsConnected (chartT '' RT) ∧
      Disjoint LT RT ∧ Disjoint (chartT '' LT) (chartT '' RT) ∧
      (0 : E) ∉ CT ∧ GT ⊆ CT ∧ CT \ GT = LT ∪ RT ∧
      (∀ z : E,
        z 0 ^ 2 + z 1 ^ 2 < aT ^ 2 →
          chartT z ∈ Metric.ball γ.vertices[lastJ + 1]
            (controlRadii.radius ⟨lastJ + 1, hlastJ⟩)) ∧
      chartT '' CT ⊆ Metric.ball γ.vertices[lastJ + 1]
        (controlRadii.radius ⟨lastJ + 1, hlastJ⟩) ∧
      γ.vertices[lastJ + 1] ∉ chartT '' CT ∧
      (∀ {t : ℝ}, 0 < t →
        chartT (WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t else 0)) ≠
          γ.vertices[lastJ + 1]) ∧
      ((AffineMap.lineMap γ.vertices[lastJ] γ.vertices[lastJ + 1]) ''
          Set.Ioo
            (1 - controlRadii.radius ⟨lastJ + 1, hlastJ⟩ /
              dist γ.vertices[lastJ] γ.vertices[lastJ + 1]) (1 : ℝ) ⊆
        chartT '' GT) ∧
      chartT '' CT \ chartT '' GT = chartT '' LT ∪ chartT '' RT ∧
      sep.leftHalf lastJ hlastJ ∩ chartT '' CT ⊆ chartT '' RT ∧
      sep.rightHalf lastJ hlastJ ∩ chartT '' CT ⊆ chartT '' LT at hside
  rcases hside with
    ⟨haT, hCTopen, hLTopen, hRTopen, hLTconn, hRTconn, hchartLTconn,
      hchartRTconn, hLRTdisj, hchartLRTdisj, hzeroT_not_C, hGTsubC,
      hmodel_splitT, hdisk_coordT, hchartCT_ball, hvertexT_not_chartC,
      hcoordT_omit, hgermT, himage_splitT, hleftT, hrightT⟩
  have hattach :=
    PolygonalArcTerminalEndpointDiskCappedTaperAttachmentStrengthening γ
      controlRadii middleSegments forbiddenMargins compatibleTubes lastJ hlastJ
  change
    sep.leftHalf lastJ hlastJ ∩
        Metric.ball γ.vertices[lastJ + 1]
          (controlRadii.radius ⟨lastJ + 1, hlastJ⟩) ⊆
      chartT '' RT ∧
    sep.rightHalf lastJ hlastJ ∩
        Metric.ball γ.vertices[lastJ + 1]
          (controlRadii.radius ⟨lastJ + 1, hlastJ⟩) ⊆
      chartT '' LT at hattach
  rcases hattach with ⟨hleftT_ball, hrightT_ball⟩
  have hdistT : 0 < dist γ.vertices[lastJ] γ.vertices[lastJ + 1] := by
    have hsum := controlRadii.adjacent_radii_sum_lt (j := lastJ) hlastJ
    have hleft := controlRadii.radius_pos ⟨lastJ, Nat.lt_of_succ_lt hlastJ⟩
    have hright := controlRadii.radius_pos ⟨lastJ + 1, hlastJ⟩
    simpa using lt_trans (add_pos hleft hright) hsum
  have hdT : dT ≠ 0 := by
    dsimp [dT]
    exact sub_ne_zero.mpr (dist_pos.mp hdistT)
  have hKT : 0 < KT := by
    dsimp [KT]
    exact compatibleTubes.terminalConeBound_pos lastJ hlastJ
  have hCsub_disk :
      chartT '' CT ⊆ vertexLocalPieces.vertexDisk ⟨lastJ + 1, hlastJ⟩ := by
    intro x hx
    rw [vertexLocalPieces.vertexDisk_eq]
    simpa using hchartCT_ball hx
  have hLmodel_subC : chartT '' LT ⊆ chartT '' CT := by
    rintro x ⟨z, hz, rfl⟩
    refine ⟨z, ?_, rfl⟩
    dsimp [LT, CT] at hz ⊢
    exact ⟨hz.1, hz.2.1, by nlinarith [hKT, hz.1, hz.2.2.1], hz.2.2.2⟩
  have hRmodel_subC : chartT '' RT ⊆ chartT '' CT := by
    rintro x ⟨z, hz, rfl⟩
    refine ⟨z, ?_, rfl⟩
    dsimp [RT, CT] at hz ⊢
    exact ⟨hz.1, hz.2.1, hz.2.2.1, by nlinarith [hKT, hz.1, hz.2.2.2]⟩
  have hchartT_inj : Function.Injective chartT := by
    dsimp [chartT]
    exact chart_injective γ.vertices[lastJ + 1] dT hdT
  have hLGTdisj : Disjoint LT GT := by
    rw [Set.disjoint_left]
    intro z hzL hzG
    dsimp [LT] at hzL
    dsimp [GT] at hzG
    linarith [hzL.2.2.1, hzG.2.2]
  have hRGTdisj : Disjoint RT GT := by
    rw [Set.disjoint_left]
    intro z hzR hzG
    dsimp [RT] at hzR
    dsimp [GT] at hzG
    linarith [hzR.2.2.2, hzG.2.2]
  have hchartLGTdisj : Disjoint (chartT '' LT) (chartT '' GT) :=
    image_disjoint_of_injective hchartT_inj hLGTdisj
  have hchartRGTdisj : Disjoint (chartT '' RT) (chartT '' GT) :=
    image_disjoint_of_injective hchartT_inj hRGTdisj
  have haT_lt_one : aT < 1 := by
    have hrad_lt_dist :
        controlRadii.radius ⟨lastJ + 1, hlastJ⟩ <
          dist γ.vertices[lastJ + 1] γ.vertices[lastJ] := by
      have hsum := controlRadii.adjacent_radii_sum_lt (j := lastJ) hlastJ
      have hleft := controlRadii.radius_pos ⟨lastJ, Nat.lt_of_succ_lt hlastJ⟩
      have hdist_comm :
          dist γ.vertices[lastJ + 1] γ.vertices[lastJ] =
            dist γ.vertices[lastJ] γ.vertices[lastJ + 1] := by
        rw [dist_comm]
      rw [hdist_comm]
      linarith
    have hdistTR : (0 : ℝ) < dist γ.vertices[lastJ + 1] γ.vertices[lastJ] := by
      rwa [dist_comm]
    dsimp [aT]
    rw [div_lt_iff₀ hdistTR]
    simpa using hrad_lt_dist
  have hGT_subset_relint : chartT '' GT ⊆ γ.relativeInterior := by
    rintro x ⟨z, hzG, rfl⟩
    have hz01 : (1 - z 0) ∈ Set.Ioo (0 : ℝ) (1 : ℝ) := by
      dsimp [GT] at hzG
      exact ⟨by linarith [lt_trans hzG.2.1 haT_lt_one], by linarith [hzG.1]⟩
    have hline_chart :
        chartT z =
          AffineMap.lineMap γ.vertices[lastJ] γ.vertices[lastJ + 1]
            (1 - z 0) := by
      dsimp [GT] at hzG
      have haxis :
          chartT z =
            AffineMap.lineMap γ.vertices[lastJ + 1] γ.vertices[lastJ]
              (z 0) := by
        simpa [chartT, dT] using
          chart_axis_eq_lineMap γ.vertices[lastJ + 1] γ.vertices[lastJ] z
            hzG.2.2
      have hrev :
          AffineMap.lineMap γ.vertices[lastJ + 1] γ.vertices[lastJ] (z 0) =
            AffineMap.lineMap γ.vertices[lastJ] γ.vertices[lastJ + 1]
              (1 - z 0) := by
        apply PiLp.ext
        intro k
        fin_cases k <;>
          simp [AffineMap.lineMap_apply_module] <;>
          ring
      exact haxis.trans hrev
    rw [hline_chart]
    exact PolygonalArcOpenSegmentSubsetRelativeInterior γ lastJ hlastJ
      (lineMap_mem_openSegment (𝕜 := ℝ) γ.vertices[lastJ]
        γ.vertices[lastJ + 1] hz01)
  have hcarrier_chartC_subset_G :
      γ.carrier ∩ chartT '' CT ⊆ chartT '' GT := by
    rintro x ⟨hxcarrier, hxC⟩
    have hxDisk : x ∈ vertexLocalPieces.vertexDisk ⟨lastJ + 1, hlastJ⟩ :=
      hCsub_disk hxC
    rcases vertexLocalPieces.vertexDisk_carrier_subset_incident_segments
        ⟨lastJ + 1, hlastJ⟩ x hxDisk hxcarrier with
      ⟨j, hj, hxseg, hincident⟩
    have hj_eq : j = lastJ := by
      rcases hincident with hleft_inc | hright_inc
      · have : lastJ + 1 = j := by simpa using hleft_inc
        have : j + 1 = γ.vertices.length := by omega
        omega
      · have : lastJ + 1 = j + 1 := by simpa using hright_inc
        omega
    subst j
    rw [segment_eq_image_lineMap] at hxseg
    rcases hxseg with ⟨t, ht, htx⟩
    rcases hxC with ⟨z, hzC, hzx⟩
    let zt : E := WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then 1 - t else 0)
    have hline_chart :
        chartT zt = AffineMap.lineMap γ.vertices[lastJ] γ.vertices[lastJ + 1] t := by
      have haxis :
          chartT zt =
            AffineMap.lineMap γ.vertices[lastJ + 1] γ.vertices[lastJ]
              (1 - t) := by
        simpa [chartT, dT, zt] using
          chart_axis_param_eq_lineMap γ.vertices[lastJ + 1]
            γ.vertices[lastJ] (1 - t)
      have hrev :
          AffineMap.lineMap γ.vertices[lastJ + 1] γ.vertices[lastJ]
              (1 - t) =
            AffineMap.lineMap γ.vertices[lastJ] γ.vertices[lastJ + 1] t := by
        apply PiLp.ext
        intro k
        fin_cases k <;>
          simp [AffineMap.lineMap_apply_module] <;>
          ring
      exact haxis.trans hrev
    have hz_eq : z = zt := by
      apply hchartT_inj
      rw [hzx, ← htx, ← hline_chart]
    have hztC : zt ∈ CT := by
      simpa [hz_eq] using hzC
    have ht_back_pos : 0 < 1 - t := by
      dsimp [CT, zt] at hztC
      simpa [zt] using hztC.1
    have ht_back_sq : (1 - t) ^ 2 < aT ^ 2 := by
      dsimp [CT, zt] at hztC
      simpa [zt] using hztC.2.1
    have ht_back_lt_aT : 1 - t < aT := by
      nlinarith [haT, ht_back_pos, ht_back_sq]
    refine ⟨zt, ?_, ?_⟩
    · dsimp [GT, zt]
      exact ⟨by simpa [zt] using ht_back_pos,
        by simpa [zt] using ht_back_lt_aT, by simp [zt]⟩
    · rw [hline_chart, htx]
  have hrel_subset_carrier : γ.relativeInterior ⊆ γ.carrier := by
    intro x hx
    rw [γ.relativeInterior_eq] at hx
    exact hx.1
  have hwithoutT :
      chartT '' CT \ γ.relativeInterior = chartT '' RT ∪ chartT '' LT := by
    calc
      chartT '' CT \ γ.relativeInterior = chartT '' CT \ chartT '' GT := by
        ext x
        constructor
        · rintro ⟨hxC, hxnotRel⟩
          exact ⟨hxC, fun hxG => hxnotRel (hGT_subset_relint hxG)⟩
        · rintro ⟨hxC, hxnotG⟩
          exact ⟨hxC, fun hxRel =>
            hxnotG (hcarrier_chartC_subset_G ⟨hrel_subset_carrier hxRel, hxC⟩)⟩
      _ = chartT '' LT ∪ chartT '' RT := himage_splitT
      _ = chartT '' RT ∪ chartT '' LT := by rw [Set.union_comm]
  refine ⟨chartT '' CT, chartT '' RT, chartT '' LT, ?_⟩
  refine ⟨?_, ?_, ?_, hCsub_disk, ?_, ?_, hRmodel_subC, hLmodel_subC,
    hchartRTconn, hchartLTconn, ?_, ?_, hchartLRTdisj.symm, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact chart_image_open γ.vertices[lastJ + 1] dT hdT CT hCTopen
  · exact chart_image_open γ.vertices[lastJ + 1] dT hdT RT hRTopen
  · exact chart_image_open γ.vertices[lastJ + 1] dT hdT LT hLTopen
  · intro hpos hnext
    exfalso
    have hnext' : lastJ + 2 < γ.vertices.length := by
      simpa [Nat.add_assoc] using hnext
    omega
  · intro _
    exact hvertexT_not_chartC
  · rw [Set.disjoint_left]
    intro x hxR hxcarrier
    exact (Set.disjoint_left.mp hchartRGTdisj) hxR
      (hcarrier_chartC_subset_G ⟨hxcarrier, hRmodel_subC hxR⟩)
  · rw [Set.disjoint_left]
    intro x hxL hxcarrier
    exact (Set.disjoint_left.mp hchartLGTdisj) hxL
      (hcarrier_chartC_subset_G ⟨hxcarrier, hLmodel_subC hxL⟩)
  · intro j hj
    by_cases hj_last : j = lastJ
    · subst j
      simpa using hleftT
    · exact leftHalf_inter_subset_of_nonincident ⟨lastJ + 1, hlastJ⟩
        (chartT '' CT) (chartT '' RT) hCsub_disk j hj
        (by
          change lastJ + 1 ≠ j
          omega)
        (by
          change lastJ + 1 ≠ j + 1
          omega)
  · intro j hj
    by_cases hj_last : j = lastJ
    · subst j
      simpa using hrightT
    · exact rightHalf_inter_subset_of_nonincident ⟨lastJ + 1, hlastJ⟩
        (chartT '' CT) (chartT '' LT) hCsub_disk j hj
        (by
          change lastJ + 1 ≠ j
          omega)
        (by
          change lastJ + 1 ≠ j + 1
          omega)
  · exact hwithoutT
  · intro j hj hij
    have hval := congrArg Fin.val hij
    have : lastJ + 1 = j := by simpa using hval
    have : j + 1 = γ.vertices.length := by omega
    omega
  · intro j hj hij
    have hj_eq : j = lastJ := by
      have hval := congrArg Fin.val hij
      have : lastJ + 1 = j + 1 := by simpa using hval
      omega
    subst j
    intro x hx
    exact Set.image_mono hGTsubC (hgermT hx)
  · intro j hj hij
    have hval := congrArg Fin.val hij
    have : lastJ + 1 = j := by simpa using hval
    have : j + 1 = γ.vertices.length := by omega
    omega
  · intro j hj hij
    have hval := congrArg Fin.val hij
    have : lastJ + 1 = j := by simpa using hval
    have : j + 1 = γ.vertices.length := by omega
    omega
  · intro j hj hij
    have hj_eq : j = lastJ := by
      have hval := congrArg Fin.val hij
      have : lastJ + 1 = j + 1 := by simpa using hval
      omega
    subst j
    rw [vertexLocalPieces.incomingLeftAttachment_eq]
    rintro x hx
    exact hleftT_ball ⟨hx.2, by
      rw [vertexLocalPieces.vertexDisk_eq] at hx
      simpa using hx.1⟩
  · intro j hj hij
    have hj_eq : j = lastJ := by
      have hval := congrArg Fin.val hij
      have : lastJ + 1 = j + 1 := by simpa using hval
      omega
    subst j
    rw [vertexLocalPieces.incomingRightAttachment_eq]
    rintro x hx
    exact hrightT_ball ⟨hx.2, by
      rw [vertexLocalPieces.vertexDisk_eq] at hx
      simpa using hx.1⟩
  · intro j hj hij
    have hval := congrArg Fin.val hij
    have : lastJ + 1 = j := by simpa using hval
    have : j + 1 = γ.vertices.length := by omega
    omega
  · intro j hj hij
    have hval := congrArg Fin.val hij
    have : lastJ + 1 = j := by simpa using hval
    have : j + 1 = γ.vertices.length := by omega
    omega
  · intro j hj hij x hx
    have hj_eq : j = lastJ := by
      have hval := congrArg Fin.val hij
      have : lastJ + 1 = j + 1 := by simpa using hval
      omega
    subst j
    rcases hgermT hx with ⟨z, hzG, rfl⟩
    exact chart_mem_closure_image γ.vertices[lastJ + 1] dT
      ((endpoint_germ_subset_closure_right aT KT haT hKT) hzG)
  · intro j hj hij x hx
    have hj_eq : j = lastJ := by
      have hval := congrArg Fin.val hij
      have : lastJ + 1 = j + 1 := by simpa using hval
      omega
    subst j
    rcases hgermT hx with ⟨z, hzG, rfl⟩
    exact chart_mem_closure_image γ.vertices[lastJ + 1] dT
      ((endpoint_germ_subset_closure_left aT KT haT hKT) hzG)
  · intro hpos hnext
    exfalso
    have hnext' : lastJ + 2 < γ.vertices.length := by
      simpa [Nat.add_assoc] using hnext
    omega
  · intro hpos hnext
    exfalso
    have hnext' : lastJ + 2 < γ.vertices.length := by
      simpa [Nat.add_assoc] using hnext
    omega

private lemma outgoingFrameStraightHalfTubeRouting
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (compatibleTubes :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (j : ℕ) (hj : j + 1 < γ.vertices.length)
    (hnext : (j + 1) + 1 < γ.vertices.length)
    (p u v : E) (rho c s : ℝ) (chart : E → E)
    (Cmodel Lmodel Rmodel : Set E)
    (hp : p = γ.vertices[j + 1])
    (huDef : u = γ.vertices[j] - γ.vertices[j + 1])
    (hvDef : v = γ.vertices[j + 2] - γ.vertices[j + 1])
    (hv : v ≠ 0)
    (hchart : chart = fun z => p + z 0 • v + z 1 • PlanarRot90 v)
    (hLmodel : Lmodel =
      {z | z ∈ Cmodel ∧ 0 < z 1 ∧ c * z 1 - s * z 0 < 0})
    (hRmodel : Rmodel =
      {z | z ∈ Cmodel ∧ (z 1 < 0 ∨ 0 < c * z 1 - s * z 0)})
    (hrep : u = c • v + s • PlanarRot90 v)
    (hs0 : s = 0) (hcneg : c < 0)
    (hCeqBall : chart '' Cmodel = Metric.ball p rho) :
    let sep :=
      compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
    sep.leftHalf j hj ∩ Metric.ball p rho ⊆ chart '' Lmodel ∧
      sep.leftHalf (j + 1) hnext ∩ Metric.ball p rho ⊆ chart '' Lmodel ∧
      sep.rightHalf j hj ∩ Metric.ball p rho ⊆ chart '' Rmodel ∧
      sep.rightHalf (j + 1) hnext ∩ Metric.ball p rho ⊆ chart '' Rmodel := by
  let sep :=
    compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
  change
    sep.leftHalf j hj ∩ Metric.ball p rho ⊆ chart '' Lmodel ∧
      sep.leftHalf (j + 1) hnext ∩ Metric.ball p rho ⊆ chart '' Lmodel ∧
      sep.rightHalf j hj ∩ Metric.ball p rho ⊆ chart '' Rmodel ∧
      sep.rightHalf (j + 1) hnext ∩ Metric.ball p rho ⊆ chart '' Rmodel
  have hrep_u : u = c • v := by simpa [hs0] using hrep
  have hrot_u : PlanarRot90 u = c • PlanarRot90 v := by
    rw [hrep_u]
    simpa using PlanarRot90LinearCombination v c 0
  have hnormal_prev : sep.normal j hj = -PlanarRot90 u := by
    rw [compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn j hj]
    rw [huDef]
    apply PiLp.ext
    intro k
    fin_cases k <;> simp [PlanarRot90]
  have hc_sq_pos : 0 < c ^ 2 := sq_pos_of_ne_zero (ne_of_lt hcneg)
  have hchart_inj : Function.Injective chart := by
    rw [hchart]
    exact chart_injective p v hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x ⟨hxLeft, hxBall⟩
    rw [sep.leftHalf_eq j hj] at hxLeft
    rcases hxLeft with ⟨t, ht, r, hr, hx_eq⟩
    let z : E :=
      WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then (1 - t) * c else -c * r)
    have hline_prev :
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t =
          p + (1 - t) • u := by
      have haxis :
          p + (1 - t) • u =
            AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j] (1 - t) := by
        simpa [hp, huDef] using
          chart_axis_param_eq_lineMap γ.vertices[j + 1] γ.vertices[j] (1 - t)
      have hrev :
          AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j] (1 - t) =
            AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t := by
        exact AffineMap.lineMap_apply_one_sub γ.vertices[j + 1] γ.vertices[j] t
      exact (haxis.trans hrev).symm
    have hx_chart : x = chart z := by
      calc
        x = AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            r • sep.normal j hj := hx_eq
        _ = p + (1 - t) • u + r • (-PlanarRot90 u) := by
          rw [hline_prev, hnormal_prev]
        _ = chart z := by
          rw [hchart]
          dsimp [z]
          rw [hrot_u, hrep_u]
          module
    have hxCimage : x ∈ chart '' Cmodel := by
      rw [hCeqBall]
      exact hxBall
    rcases hxCimage with ⟨w, hwC, hwx⟩
    have hwz : w = z := hchart_inj (by simpa [hx_chart] using hwx)
    have hzC : z ∈ Cmodel := by simpa [hwz] using hwC
    refine ⟨z, ?_, hx_chart.symm⟩
    rw [hLmodel]
    refine ⟨hzC, ?_, ?_⟩
    · simp [z]
      nlinarith [hr.1, hcneg]
    · rw [hs0]
      simp [z]
      nlinarith [hr.1, hc_sq_pos]
  · rintro x ⟨hxLeft, hxBall⟩
    rw [sep.leftHalf_eq (j + 1) hnext] at hxLeft
    rcases hxLeft with ⟨t, ht, r, hr, hx_eq⟩
    let z : E := WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then t else r)
    have hx_chart : x = chart z := by
      have hline :
          AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t =
            p + t • v := by
        simpa [hp, hvDef] using
          (chart_axis_param_eq_lineMap γ.vertices[j + 1] γ.vertices[j + 2] t).symm
      calc
        x = AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t +
            r • sep.normal (j + 1) hnext := hx_eq
        _ = p + t • v + r • PlanarRot90 v := by
          rw [hline,
            compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn
              (j + 1) hnext]
          simp [hvDef, PlanarRot90]
        _ = chart z := by
          rw [hchart]
          dsimp [z]
    have hxCimage : x ∈ chart '' Cmodel := by
      rw [hCeqBall]
      exact hxBall
    rcases hxCimage with ⟨w, hwC, hwx⟩
    have hwz : w = z := hchart_inj (by simpa [hx_chart] using hwx)
    have hzC : z ∈ Cmodel := by simpa [hwz] using hwC
    refine ⟨z, ?_, hx_chart.symm⟩
    rw [hLmodel]
    refine ⟨hzC, by simpa [z] using hr.1, ?_⟩
    rw [hs0]
    simp [z]
    nlinarith [hr.1, hcneg]
  · rintro x ⟨hxRight, hxBall⟩
    rw [sep.rightHalf_eq j hj] at hxRight
    rcases hxRight with ⟨t, ht, r, hr, hx_eq⟩
    let z : E :=
      WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then (1 - t) * c else -c * r)
    have hline_prev :
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t =
          p + (1 - t) • u := by
      have haxis :
          p + (1 - t) • u =
            AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j] (1 - t) := by
        simpa [hp, huDef] using
          chart_axis_param_eq_lineMap γ.vertices[j + 1] γ.vertices[j] (1 - t)
      have hrev :
          AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j] (1 - t) =
            AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t := by
        exact AffineMap.lineMap_apply_one_sub γ.vertices[j + 1] γ.vertices[j] t
      exact (haxis.trans hrev).symm
    have hx_chart : x = chart z := by
      calc
        x = AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            r • sep.normal j hj := hx_eq
        _ = p + (1 - t) • u + r • (-PlanarRot90 u) := by
          rw [hline_prev, hnormal_prev]
        _ = chart z := by
          rw [hchart]
          dsimp [z]
          rw [hrot_u, hrep_u]
          module
    have hxCimage : x ∈ chart '' Cmodel := by
      rw [hCeqBall]
      exact hxBall
    rcases hxCimage with ⟨w, hwC, hwx⟩
    have hwz : w = z := hchart_inj (by simpa [hx_chart] using hwx)
    have hzC : z ∈ Cmodel := by simpa [hwz] using hwC
    refine ⟨z, ?_, hx_chart.symm⟩
    rw [hRmodel]
    refine ⟨hzC, Or.inl ?_⟩
    simp [z]
    nlinarith [hr.2, hcneg]
  · rintro x ⟨hxRight, hxBall⟩
    rw [sep.rightHalf_eq (j + 1) hnext] at hxRight
    rcases hxRight with ⟨t, ht, r, hr, hx_eq⟩
    let z : E := WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then t else r)
    have hx_chart : x = chart z := by
      have hline :
          AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t =
            p + t • v := by
        simpa [hp, hvDef] using
          (chart_axis_param_eq_lineMap γ.vertices[j + 1] γ.vertices[j + 2] t).symm
      calc
        x = AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t +
            r • sep.normal (j + 1) hnext := hx_eq
        _ = p + t • v + r • PlanarRot90 v := by
          rw [hline,
            compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn
              (j + 1) hnext]
          simp [hvDef, PlanarRot90]
        _ = chart z := by
          rw [hchart]
          dsimp [z]
    have hxCimage : x ∈ chart '' Cmodel := by
      rw [hCeqBall]
      exact hxBall
    rcases hxCimage with ⟨w, hwC, hwx⟩
    have hwz : w = z := hchart_inj (by simpa [hx_chart] using hwx)
    have hzC : z ∈ Cmodel := by simpa [hwz] using hwC
    refine ⟨z, ?_, hx_chart.symm⟩
    rw [hRmodel]
    exact ⟨hzC, Or.inl (by simpa [z] using hr.2)⟩

private lemma outgoingRaySubsetRelativeInterior
    (γ : PolygonalArc) (j : ℕ)
    (hj : j + 1 < γ.vertices.length)
    (hnext : (j + 1) + 1 < γ.vertices.length)
    (p v : E) (rho : ℝ)
    (hp : p = γ.vertices[j + 1])
    (hvDef : v = γ.vertices[j + 2] - γ.vertices[j + 1])
    (hv : v ≠ 0) (hrho_lt_vnorm : rho < ‖v‖)
    (S : Set E)
    (hS : S =
      {q | q ∈ Metric.ball p rho ∧ ∃ t : ℝ, 0 < t ∧ q = p + t • v}) :
    S ⊆ γ.relativeInterior := by
  rw [hS]
  rintro q ⟨hqBall, t, ht, hq⟩
  have ht_lt_one : t < 1 := by
    have hdist_expr : dist (p + t • v) p = t * ‖v‖ := by
      rw [dist_eq_norm]
      have hsub : p + t • v - p = t • v := by abel
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    rw [hq, Metric.mem_ball, hdist_expr] at hqBall
    nlinarith [hrho_lt_vnorm, norm_pos_iff.mpr hv]
  have hline :
      p + t • v =
        AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t := by
    simpa [hp, hvDef] using
      chart_axis_param_eq_lineMap γ.vertices[j + 1] γ.vertices[j + 2] t
  rw [hq, hline]
  exact PolygonalArcOpenSegmentSubsetRelativeInterior γ (j + 1) hnext
    (lineMap_mem_openSegment (𝕜 := ℝ) γ.vertices[j + 1]
      γ.vertices[j + 2] ⟨ht, ht_lt_one⟩)

private lemma incomingRaySubsetRelativeInterior
    (γ : PolygonalArc) (j : ℕ)
    (hj : j + 1 < γ.vertices.length)
    (p u : E) (rho : ℝ)
    (hp : p = γ.vertices[j + 1])
    (huDef : u = γ.vertices[j] - γ.vertices[j + 1])
    (hu : u ≠ 0) (hrho_lt_unorm : rho < ‖u‖)
    (S : Set E)
    (hS : S =
      {q | q ∈ Metric.ball p rho ∧ ∃ t : ℝ, 0 < t ∧ q = p + t • u}) :
    S ⊆ γ.relativeInterior := by
  rw [hS]
  rintro q ⟨hqBall, t, ht, hq⟩
  have ht_lt_one : t < 1 := by
    have hdist_expr : dist (p + t • u) p = t * ‖u‖ := by
      rw [dist_eq_norm]
      have hsub : p + t • u - p = t • u := by abel
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    rw [hq, Metric.mem_ball, hdist_expr] at hqBall
    nlinarith [hrho_lt_unorm, norm_pos_iff.mpr hu]
  have haxis :
      p + t • u =
        AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j] t := by
    simpa [hp, huDef] using
      chart_axis_param_eq_lineMap γ.vertices[j + 1] γ.vertices[j] t
  have hrev :
      AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j] t =
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] (1 - t) := by
    exact
      (AffineMap.lineMap_apply_one_sub
        γ.vertices[j] γ.vertices[j + 1] t).symm
  rw [hq, haxis, hrev]
  exact PolygonalArcOpenSegmentSubsetRelativeInterior γ j hj
    (lineMap_mem_openSegment (𝕜 := ℝ) γ.vertices[j]
      γ.vertices[j + 1] ⟨by linarith, by linarith⟩)

private lemma outgoingGermSubsetChartRay
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (compatibleTubes :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (vertexLocalPieces :
      PolygonalArcCollarVertexLocalPieceData γ controlRadii middleSegments
        forbiddenMargins
        compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData)
    (i : Fin γ.vertices.length) (j : ℕ)
    (hj : j + 1 < γ.vertices.length)
    (hnext : (j + 1) + 1 < γ.vertices.length)
    (hi_eq : i = ⟨j + 1, hj⟩)
    (p v : E) (rho : ℝ)
    (hp : p = γ.vertices[j + 1])
    (hvDef : v = γ.vertices[j + 2] - γ.vertices[j + 1])
    (hrhoDef : rho = controlRadii.radius ⟨j + 1, hj⟩)
    (S : Set E)
    (hS : S =
      {q | q ∈ Metric.ball p rho ∧ ∃ t : ℝ, 0 < t ∧ q = p + t • v}) :
    (AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2]) ''
        Set.Ioo (0 : ℝ)
          (controlRadii.radius ⟨j + 1, Nat.lt_of_succ_lt hnext⟩ /
            dist γ.vertices[j + 1] γ.vertices[j + 2]) ⊆ S := by
  intro x hx
  have hxEP :=
    vertexLocalPieces.outgoing_germ_subset_endpointPiece (j + 1) hnext hx
  rw [vertexLocalPieces.endpointPiece_eq] at hxEP
  have hxBall : x ∈ Metric.ball p rho := by
    rw [vertexLocalPieces.vertexDisk_eq] at hxEP
    simpa [hp, hrhoDef, hi_eq] using hxEP.1
  rcases hx with ⟨t, ht, htx⟩
  rw [hS]
  refine ⟨hxBall, t, ht.1, ?_⟩
  rw [← htx]
  have hline :
      p + t • v =
        AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t := by
    simpa [hp, hvDef] using
      chart_axis_param_eq_lineMap γ.vertices[j + 1] γ.vertices[j + 2] t
  exact hline.symm

private lemma incomingGermSubsetChartRay
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (compatibleTubes :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (vertexLocalPieces :
      PolygonalArcCollarVertexLocalPieceData γ controlRadii middleSegments
        forbiddenMargins
        compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData)
    (i : Fin γ.vertices.length) (j : ℕ)
    (hj : j + 1 < γ.vertices.length)
    (hi_eq : i = ⟨j + 1, hj⟩)
    (p u : E) (rho : ℝ)
    (hp : p = γ.vertices[j + 1])
    (huDef : u = γ.vertices[j] - γ.vertices[j + 1])
    (hrhoDef : rho = controlRadii.radius ⟨j + 1, hj⟩)
    (S : Set E)
    (hS : S =
      {q | q ∈ Metric.ball p rho ∧ ∃ t : ℝ, 0 < t ∧ q = p + t • u}) :
    (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
        Set.Ioo
          (1 - controlRadii.radius ⟨j + 1, hj⟩ /
            dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) ⊆ S := by
  intro x hx
  have hxEP := vertexLocalPieces.incoming_germ_subset_endpointPiece j hj hx
  rw [vertexLocalPieces.endpointPiece_eq] at hxEP
  have hxBall : x ∈ Metric.ball p rho := by
    rw [vertexLocalPieces.vertexDisk_eq] at hxEP
    simpa [hp, hrhoDef, hi_eq] using hxEP.1
  rcases hx with ⟨t, ht, htx⟩
  rw [hS]
  refine ⟨hxBall, 1 - t, by linarith [ht.2], ?_⟩
  rw [← htx]
  have haxis :
      p + (1 - t) • u =
        AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j] (1 - t) := by
    simpa [hp, huDef] using
      chart_axis_param_eq_lineMap γ.vertices[j + 1] γ.vertices[j] (1 - t)
  have hrev :
      AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j] (1 - t) =
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t := by
    exact AffineMap.lineMap_apply_one_sub γ.vertices[j + 1] γ.vertices[j] t
  exact (haxis.trans hrev).symm

private lemma localTopologyGoodInterior
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (compatibleTubes :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (vertexLocalPieces :
      PolygonalArcCollarVertexLocalPieceData γ controlRadii middleSegments
        forbiddenMargins
        compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData)
    (i : Fin γ.vertices.length) (hi_pos : 0 < i.1)
    (hi_next : i.1 + 1 < γ.vertices.length) :
    ∃ C L R : Set E,
      localTopologyGood γ controlRadii middleSegments forbiddenMargins
        compatibleTubes vertexLocalPieces i C L R := by
  let sep :=
    compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
  let Good :=
    localTopologyGood γ controlRadii middleSegments forbiddenMargins
      compatibleTubes vertexLocalPieces
  change ∃ C L R : Set E, Good i C L R
  · let j : ℕ := i.1 - 1
    have hji : j + 1 = i.1 := by
      dsimp [j]
      omega
    have hj : j + 1 < γ.vertices.length := by
      simpa [hji] using i.2
    have hnext : (j + 1) + 1 < γ.vertices.length := by
      simpa [hji] using hi_next
    have hi_eq : i = ⟨j + 1, hj⟩ := by
      apply Fin.ext
      exact hji.symm
    let p : E := γ.vertices[j + 1]
    let u : E := γ.vertices[j] - γ.vertices[j + 1]
    let v : E := γ.vertices[j + 2] - γ.vertices[j + 1]
    let rho : ℝ := controlRadii.radius ⟨j + 1, hj⟩
    have hrho : 0 < rho := by
      dsimp [rho]
      exact controlRadii.radius_pos ⟨j + 1, hj⟩
    have hdist_prev : 0 < dist γ.vertices[j] γ.vertices[j + 1] := by
      have hsum := controlRadii.adjacent_radii_sum_lt (j := j) hj
      have hleft := controlRadii.radius_pos ⟨j, Nat.lt_of_succ_lt hj⟩
      have hright := controlRadii.radius_pos ⟨j + 1, hj⟩
      nlinarith
    have hdist_next : 0 < dist γ.vertices[j + 1] γ.vertices[j + 2] := by
      have hsum := controlRadii.adjacent_radii_sum_lt (j := j + 1) hnext
      have hleft := controlRadii.radius_pos ⟨j + 1, hj⟩
      have hright := controlRadii.radius_pos ⟨j + 2, hnext⟩
      nlinarith
    have hu : u ≠ 0 := by
      dsimp [u]
      exact sub_ne_zero.mpr (dist_pos.mp hdist_prev)
    have hv : v ≠ 0 := by
      dsimp [v]
      exact sub_ne_zero.mpr (dist_pos.mp hdist_next).symm
    have hrho_lt_unorm : rho < ‖u‖ := by
      have hsum := controlRadii.adjacent_radii_sum_lt (j := j) hj
      have hleft := controlRadii.radius_pos ⟨j, Nat.lt_of_succ_lt hj⟩
      have hdist_eq : dist γ.vertices[j] γ.vertices[j + 1] = ‖u‖ := by
        rw [dist_eq_norm]
      dsimp [rho] at *
      rw [hdist_eq] at hsum
      nlinarith
    have hrho_lt_vnorm : rho < ‖v‖ := by
      have hsum := controlRadii.adjacent_radii_sum_lt (j := j + 1) hnext
      have hright := controlRadii.radius_pos ⟨j + 2, hnext⟩
      have hdist_eq : dist γ.vertices[j + 1] γ.vertices[j + 2] = ‖v‖ := by
        rw [dist_eq_norm]
        dsimp [v]
        have hneg :
            γ.vertices[j + 1] - γ.vertices[j + 2] =
              -(γ.vertices[j + 2] - γ.vertices[j + 1]) := by
          abel
        rw [hneg, norm_neg]
      dsimp [rho] at *
      rw [hdist_eq] at hsum
      nlinarith
    have hvertex_relint : p ∈ γ.relativeInterior := by
      dsimp [p]
      simpa [hi_eq] using
        PolygonalArcInteriorVertexMemRelativeInterior γ i hi_pos hi_next
    have hrel_subset_carrier : γ.relativeInterior ⊆ γ.carrier := by
      intro x hx
      rw [γ.relativeInterior_eq] at hx
      exact hx.1
    have hnot_same :
        ¬ ∃ a : ℝ, 0 < a ∧ v = a • u := by
      have hraw :=
        (PolygonalArcAdjacentOutwardDirectionsNotSameRay γ
          (i := j + 1) (by omega) hnext).2
      simpa [u, v] using hraw
    rcases PolygonalArcInteriorTwoRaySectorChartTransport p u v rho
        hrho hu hv hnot_same with
      ⟨base, other, c, s, hbase_choice, hrep, hsector_pos, hsector⟩
    rcases hbase_choice with hbase_choice | hbase_choice
    · rcases hbase_choice with ⟨rfl, rfl⟩
      let a : ℝ := rho / ‖u‖
      let chart : E → E :=
        fun z => p + z 0 • u + z 1 • PlanarRot90 u
      let Cmodel : Set E := Metric.ball (0 : E) a
      let Gbase : Set E := {z | z ∈ Cmodel ∧ z 1 = 0 ∧ 0 < z 0}
      let Gother : Set E :=
        {z | z ∈ Cmodel ∧ ∃ t : ℝ, 0 < t ∧ z 0 = t * c ∧ z 1 = t * s}
      let Lmodel : Set E :=
        {z | z ∈ Cmodel ∧ 0 < z 1 ∧ c * z 1 - s * z 0 < 0}
      let Rmodel : Set E :=
        {z | z ∈ Cmodel ∧ (z 1 < 0 ∨ 0 < c * z 1 - s * z 0)}
      change
        0 < a ∧
          IsOpen (chart '' Cmodel) ∧ IsOpen (chart '' Lmodel) ∧
          IsOpen (chart '' Rmodel) ∧ IsConnected (chart '' Lmodel) ∧
          IsConnected (chart '' Rmodel) ∧
          Disjoint (chart '' Lmodel) (chart '' Rmodel) ∧
          chart '' Cmodel = Metric.ball p rho ∧
          chart '' Gbase =
            {q | q ∈ Metric.ball p rho ∧ ∃ t : ℝ, 0 < t ∧ q = p + t • u} ∧
          chart '' Gother =
            {q | q ∈ Metric.ball p rho ∧ ∃ t : ℝ, 0 < t ∧ q = p + t • v} ∧
          Disjoint (chart '' Lmodel)
            ((chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set E)) ∧
          Disjoint (chart '' Rmodel)
            ((chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set E)) ∧
          Metric.ball p rho \
              ((chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set E)) =
            chart '' Lmodel ∪ chart '' Rmodel at hsector
      rcases hsector with
        ⟨ha, hCopen, hLopen, hRopen, hLconn, hRconn, hLRdisj,
          hCeqBall, hGbase_eq, hGother_eq, hLbad_disj, hRbad_disj,
          hsplit⟩
      have hCeqDisk : chart '' Cmodel = vertexLocalPieces.vertexDisk i := by
        rw [hCeqBall, vertexLocalPieces.vertexDisk_eq]
        simp [p, rho, hi_eq]
      have hdisk_to_ball {x : E} (hx : x ∈ vertexLocalPieces.vertexDisk i) :
          x ∈ Metric.ball p rho := by
        rw [vertexLocalPieces.vertexDisk_eq] at hx
        simpa [p, rho, hi_eq] using hx
      have hRsubC : chart '' Rmodel ⊆ vertexLocalPieces.vertexDisk i := by
        rintro x ⟨z, hz, rfl⟩
        rw [← hCeqDisk]
        refine ⟨z, ?_, rfl⟩
        exact hz.1
      have hLsubC : chart '' Lmodel ⊆ vertexLocalPieces.vertexDisk i := by
        rintro x ⟨z, hz, rfl⟩
        rw [← hCeqDisk]
        refine ⟨z, ?_, rfl⟩
        exact hz.1
      have hroute :=
        PolygonalArcInteriorIncomingFrameSignedHalfTubeSectorRouting γ
          controlRadii middleSegments forbiddenMargins compatibleTubes
          j hj hnext c s (by simpa [u, v] using hrep) hsector_pos
          (by
            simpa [p, u, rho, chart, Cmodel, a] using hCeqBall)
      change
        sep.leftHalf j hj ∩ Metric.ball p rho ⊆ chart '' Rmodel ∧
          sep.leftHalf (j + 1) hnext ∩ Metric.ball p rho ⊆ chart '' Rmodel ∧
          sep.rightHalf j hj ∩ Metric.ball p rho ⊆ chart '' Lmodel ∧
          sep.rightHalf (j + 1) hnext ∩ Metric.ball p rho ⊆ chart '' Lmodel at hroute
      rcases hroute with ⟨hleft_prev, hleft_next, hright_prev, hright_next⟩
      have hGbase_subset_relint : chart '' Gbase ⊆ γ.relativeInterior :=
        incomingRaySubsetRelativeInterior γ j hj p u rho rfl rfl hu
          hrho_lt_unorm (chart '' Gbase) hGbase_eq
      have hGother_subset_relint : chart '' Gother ⊆ γ.relativeInterior :=
        outgoingRaySubsetRelativeInterior γ j hj hnext p v rho rfl rfl hv
          hrho_lt_vnorm (chart '' Gother) hGother_eq
      have hbad_subset_relint :
          (chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set E) ⊆
            γ.relativeInterior := by
        rintro x ((hxG | hxG) | hxP)
        · exact hGbase_subset_relint hxG
        · exact hGother_subset_relint hxG
        · rw [Set.mem_singleton_iff] at hxP
          simpa [hxP] using hvertex_relint
      have hcarrier_disk_subset_bad :
          γ.carrier ∩ vertexLocalPieces.vertexDisk i ⊆
            (chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set E) := by
        rintro x ⟨hxcarrier, hxDisk⟩
        rcases vertexLocalPieces.vertexDisk_carrier_subset_incident_segments
            i x hxDisk hxcarrier with
          ⟨k, hk, hxseg, hincident⟩
        have hk_cases : k = j ∨ k = j + 1 := by
          rcases hincident with hleft_inc | hright_inc
          · have : j + 1 = k := by
              calc
                j + 1 = i.1 := hji
                _ = k := hleft_inc
            exact Or.inr this.symm
          · have : j + 1 = k + 1 := by
              calc
                j + 1 = i.1 := hji
                _ = k + 1 := hright_inc
            exact Or.inl (by omega)
        rw [segment_eq_image_lineMap] at hxseg
        rcases hxseg with ⟨t, ht, htx⟩
        rcases hk_cases with hk_eq | hk_eq
        · subst k
          by_cases ht_one : t = 1
          · right
            rw [Set.mem_singleton_iff]
            rw [← htx]
            apply PiLp.ext
            intro k
            fin_cases k <;>
              simp [p, AffineMap.lineMap_apply_module, ht_one]
          · refine Or.inl (Or.inl ?_)
            rw [hGbase_eq]
            have ht_lt_one : t < 1 := lt_of_le_of_ne ht.2 ht_one
            refine ⟨hdisk_to_ball hxDisk, 1 - t, by linarith, ?_⟩
            rw [← htx]
            have haxis :
                p + (1 - t) • u =
                  AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j] (1 - t) := by
              simpa [p, u] using
                chart_axis_param_eq_lineMap γ.vertices[j + 1] γ.vertices[j] (1 - t)
            have hrev :
                AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j] (1 - t) =
                  AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t := by
              exact AffineMap.lineMap_apply_one_sub
                γ.vertices[j + 1] γ.vertices[j] t
            exact (haxis.trans hrev).symm
        · subst k
          by_cases ht_zero : t = 0
          · right
            rw [Set.mem_singleton_iff]
            rw [← htx]
            apply PiLp.ext
            intro k
            fin_cases k <;>
              simp [p, AffineMap.lineMap_apply_module, ht_zero]
          · refine Or.inl (Or.inr ?_)
            rw [hGother_eq]
            have ht_pos' : 0 < t := by
              exact lt_of_le_of_ne ht.1 (fun h => ht_zero h.symm)
            refine ⟨hdisk_to_ball hxDisk, t, ht_pos', ?_⟩
            rw [← htx]
            have hline :
                p + t • v =
                  AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t := by
              simpa [p, v] using
                chart_axis_param_eq_lineMap γ.vertices[j + 1] γ.vertices[j + 2] t
            exact hline.symm
      have hR_disj_carrier : Disjoint (chart '' Rmodel) γ.carrier := by
        rw [Set.disjoint_left]
        intro x hxR hxcarrier
        exact (Set.disjoint_left.mp hRbad_disj) hxR
          (hcarrier_disk_subset_bad ⟨hxcarrier, hRsubC hxR⟩)
      have hL_disj_carrier : Disjoint (chart '' Lmodel) γ.carrier := by
        rw [Set.disjoint_left]
        intro x hxL hxcarrier
        exact (Set.disjoint_left.mp hLbad_disj) hxL
          (hcarrier_disk_subset_bad ⟨hxcarrier, hLsubC hxL⟩)
      have hwithout :
          vertexLocalPieces.vertexDisk i \ γ.relativeInterior =
            chart '' Rmodel ∪ chart '' Lmodel := by
        ext x
        constructor
        · rintro ⟨hxDisk, hxNotRel⟩
          have hxBall := hdisk_to_ball hxDisk
          have hxNotBad :
              x ∉ (chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set E) := by
            intro hxBad
            exact hxNotRel (hbad_subset_relint hxBad)
          have hxLR :
              x ∈ chart '' Lmodel ∪ chart '' Rmodel := by
            rw [← hsplit]
            exact And.intro hxBall hxNotBad
          rcases hxLR with hxL | hxR
          · exact Or.inr hxL
          · exact Or.inl hxR
        · rintro (hxR | hxL)
          · refine ⟨hRsubC hxR, ?_⟩
            intro hxRel
            exact (Set.disjoint_left.mp hR_disj_carrier) hxR
              (hrel_subset_carrier hxRel)
          · refine ⟨hLsubC hxL, ?_⟩
            intro hxRel
            exact (Set.disjoint_left.mp hL_disj_carrier) hxL
              (hrel_subset_carrier hxRel)
      have hin_germ_chart_Gbase :
          (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
              Set.Ioo
                (1 - controlRadii.radius ⟨j + 1, hj⟩ /
                  dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) ⊆
            chart '' Gbase := by
        exact incomingGermSubsetChartRay γ controlRadii middleSegments
          forbiddenMargins compatibleTubes vertexLocalPieces i j hj hi_eq p u rho
          rfl rfl rfl (chart '' Gbase) hGbase_eq
      have hout_germ_chart_Gother :
          (AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2]) ''
              Set.Ioo (0 : ℝ)
                (controlRadii.radius ⟨j + 1, Nat.lt_of_succ_lt hnext⟩ /
                  dist γ.vertices[j + 1] γ.vertices[j + 2]) ⊆
            chart '' Gother := by
        exact outgoingGermSubsetChartRay γ controlRadii middleSegments
          forbiddenMargins compatibleTubes vertexLocalPieces i j hj hnext hi_eq p v rho
          rfl rfl rfl (chart '' Gother) hGother_eq
      refine ⟨vertexLocalPieces.vertexDisk i, chart '' Rmodel, chart '' Lmodel, ?_⟩
      refine ⟨vertexLocalPieces.vertexDisk_open i, hRopen, hLopen, ?_, ?_, ?_,
        hRsubC, hLsubC, hRconn, hLconn, hR_disj_carrier, hL_disj_carrier,
        hLRdisj.symm, ?_, ?_, hwithout, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx
        exact hx
      · intro _ _
        rfl
      · intro hend
        rcases hend with hzero | hlast
        · omega
        · omega
      · intro k hk
        by_cases hk_prev : k = j
        · subst k
          rintro x hx
          exact hleft_prev ⟨hx.1, hdisk_to_ball hx.2⟩
        · by_cases hk_next : k = j + 1
          · subst k
            rintro x hx
            exact hleft_next ⟨hx.1, hdisk_to_ball hx.2⟩
          · exact leftHalf_inter_subset_of_nonincident i
              (vertexLocalPieces.vertexDisk i) (chart '' Rmodel) (by intro x hx; exact hx)
              k hk
              (by
                change i.1 ≠ k
                omega)
              (by
                change i.1 ≠ k + 1
                omega)
      · intro k hk
        by_cases hk_prev : k = j
        · subst k
          rintro x hx
          exact hright_prev ⟨hx.1, hdisk_to_ball hx.2⟩
        · by_cases hk_next : k = j + 1
          · subst k
            rintro x hx
            exact hright_next ⟨hx.1, hdisk_to_ball hx.2⟩
          · exact rightHalf_inter_subset_of_nonincident i
              (vertexLocalPieces.vertexDisk i) (chart '' Lmodel) (by intro x hx; exact hx)
              k hk
              (by
                change i.1 ≠ k
                omega)
              (by
                change i.1 ≠ k + 1
                omega)
      · intro k hk hik
        have hk_eq : k = j + 1 := by
          have hval := congrArg Fin.val hik
          have : i.1 = k := by simpa using hval
          omega
        subst k
        intro x hx
        have hxEP :=
          vertexLocalPieces.outgoing_germ_subset_endpointPiece (j + 1) hnext hx
        rw [vertexLocalPieces.endpointPiece_eq] at hxEP
        simpa [hi_eq] using hxEP.1
      · intro k hk hik
        have hk_eq : k = j := by
          have hval := congrArg Fin.val hik
          have : i.1 = k + 1 := by simpa using hval
          omega
        subst k
        intro x hx
        have hxEP := vertexLocalPieces.incoming_germ_subset_endpointPiece j hj hx
        rw [vertexLocalPieces.endpointPiece_eq] at hxEP
        simpa [hi_eq] using hxEP.1
      · intro k hk hik
        have hk_eq : k = j + 1 := by
          have hval := congrArg Fin.val hik
          have : i.1 = k := by simpa using hval
          omega
        subst k
        rw [vertexLocalPieces.outgoingLeftAttachment_eq]
        rintro x hx
        exact hleft_next ⟨hx.2, hdisk_to_ball (by simpa [hi_eq] using hx.1)⟩
      · intro k hk hik
        have hk_eq : k = j + 1 := by
          have hval := congrArg Fin.val hik
          have : i.1 = k := by simpa using hval
          omega
        subst k
        rw [vertexLocalPieces.outgoingRightAttachment_eq]
        rintro x hx
        exact hright_next ⟨hx.2, hdisk_to_ball (by simpa [hi_eq] using hx.1)⟩
      · intro k hk hik
        have hk_eq : k = j := by
          have hval := congrArg Fin.val hik
          have : i.1 = k + 1 := by simpa using hval
          omega
        subst k
        rw [vertexLocalPieces.incomingLeftAttachment_eq]
        rintro x hx
        exact hleft_prev ⟨hx.2, hdisk_to_ball (by simpa [hi_eq] using hx.1)⟩
      · intro k hk hik
        have hk_eq : k = j := by
          have hval := congrArg Fin.val hik
          have : i.1 = k + 1 := by simpa using hval
          omega
        subst k
        rw [vertexLocalPieces.incomingRightAttachment_eq]
        rintro x hx
        exact hright_prev ⟨hx.2, hdisk_to_ball (by simpa [hi_eq] using hx.1)⟩
      · intro k hk hik x hx
        have hk_eq : k = j + 1 := by
          have hval := congrArg Fin.val hik
          have : i.1 = k := by simpa using hval
          omega
        subst k
        rcases hout_germ_chart_Gother hx with ⟨z, hzG, rfl⟩
        exact chart_mem_closure_image p u
          ((twoRay_other_subset_closure_right a c s hsector_pos) hzG)
      · intro k hk hik x hx
        have hk_eq : k = j + 1 := by
          have hval := congrArg Fin.val hik
          have : i.1 = k := by simpa using hval
          omega
        subst k
        rcases hout_germ_chart_Gother hx with ⟨z, hzG, rfl⟩
        exact chart_mem_closure_image p u
          ((twoRay_other_subset_closure_left a c s hsector_pos) hzG)
      · intro k hk hik x hx
        have hk_eq : k = j := by
          have hval := congrArg Fin.val hik
          have : i.1 = k + 1 := by simpa using hval
          omega
        subst k
        rcases hin_germ_chart_Gbase hx with ⟨z, hzG, rfl⟩
        exact chart_mem_closure_image p u
          ((twoRay_base_subset_closure_right a c s) hzG)
      · intro k hk hik x hx
        have hk_eq : k = j := by
          have hval := congrArg Fin.val hik
          have : i.1 = k + 1 := by simpa using hval
          omega
        subst k
        rcases hin_germ_chart_Gbase hx with ⟨z, hzG, rfl⟩
        exact chart_mem_closure_image p u
          ((twoRay_base_subset_closure_left a c s hsector_pos) hzG)
      · intro _ _
        have hp : γ.vertices[i.1] =
            p + (0 : E) 0 • u + (0 : E) 1 • PlanarRot90 u := by
          simp [p, hi_eq]
        rw [hp]
        exact chart_mem_closure_image p u
          (twoRay_origin_mem_closure_right a c s ha)
      · intro _ _
        have hp : γ.vertices[i.1] =
            p + (0 : E) 0 • u + (0 : E) 1 • PlanarRot90 u := by
          simp [p, hi_eq]
        rw [hp]
        exact chart_mem_closure_image p u
          (twoRay_origin_mem_closure_left a c s ha hsector_pos)
    · rcases hbase_choice with ⟨rfl, rfl⟩
      let a : ℝ := rho / ‖v‖
      let chart : E → E :=
        fun z => p + z 0 • v + z 1 • PlanarRot90 v
      let Cmodel : Set E := Metric.ball (0 : E) a
      let Gbase : Set E := {z | z ∈ Cmodel ∧ z 1 = 0 ∧ 0 < z 0}
      let Gother : Set E :=
        {z | z ∈ Cmodel ∧ ∃ t : ℝ, 0 < t ∧ z 0 = t * c ∧ z 1 = t * s}
      let Lmodel : Set E :=
        {z | z ∈ Cmodel ∧ 0 < z 1 ∧ c * z 1 - s * z 0 < 0}
      let Rmodel : Set E :=
        {z | z ∈ Cmodel ∧ (z 1 < 0 ∨ 0 < c * z 1 - s * z 0)}
      change
        0 < a ∧
          IsOpen (chart '' Cmodel) ∧ IsOpen (chart '' Lmodel) ∧
          IsOpen (chart '' Rmodel) ∧ IsConnected (chart '' Lmodel) ∧
          IsConnected (chart '' Rmodel) ∧
          Disjoint (chart '' Lmodel) (chart '' Rmodel) ∧
          chart '' Cmodel = Metric.ball p rho ∧
          chart '' Gbase =
            {q | q ∈ Metric.ball p rho ∧ ∃ t : ℝ, 0 < t ∧ q = p + t • v} ∧
          chart '' Gother =
            {q | q ∈ Metric.ball p rho ∧ ∃ t : ℝ, 0 < t ∧ q = p + t • u} ∧
          Disjoint (chart '' Lmodel)
            ((chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set E)) ∧
          Disjoint (chart '' Rmodel)
            ((chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set E)) ∧
          Metric.ball p rho \
              ((chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set E)) =
            chart '' Lmodel ∪ chart '' Rmodel at hsector
      rcases hsector with
        ⟨ha, hCopen, hLopen, hRopen, hLconn, hRconn, hLRdisj,
          hCeqBall, hGbase_eq, hGother_eq, hLbad_disj, hRbad_disj,
          hsplit⟩
      have hCeqDisk : chart '' Cmodel = vertexLocalPieces.vertexDisk i := by
        rw [hCeqBall, vertexLocalPieces.vertexDisk_eq]
        simp [p, rho, hi_eq]
      have hdisk_to_ball {x : E} (hx : x ∈ vertexLocalPieces.vertexDisk i) :
          x ∈ Metric.ball p rho := by
        rw [vertexLocalPieces.vertexDisk_eq] at hx
        simpa [p, rho, hi_eq] using hx
      have hLsubC : chart '' Lmodel ⊆ vertexLocalPieces.vertexDisk i := by
        rintro x ⟨z, hz, rfl⟩
        rw [← hCeqDisk]
        exact ⟨z, hz.1, rfl⟩
      have hRsubC : chart '' Rmodel ⊆ vertexLocalPieces.vertexDisk i := by
        rintro x ⟨z, hz, rfl⟩
        rw [← hCeqDisk]
        exact ⟨z, hz.1, rfl⟩
      have hroute :
          sep.leftHalf j hj ∩ Metric.ball p rho ⊆ chart '' Lmodel ∧
            sep.leftHalf (j + 1) hnext ∩ Metric.ball p rho ⊆ chart '' Lmodel ∧
            sep.rightHalf j hj ∩ Metric.ball p rho ⊆ chart '' Rmodel ∧
            sep.rightHalf (j + 1) hnext ∩ Metric.ball p rho ⊆ chart '' Rmodel := by
        rcases hsector_pos with hspos | hstraight
        · have hraw :=
            PolygonalArcInteriorOutgoingFrameSignedHalfTubeSectorRouting γ
              controlRadii middleSegments forbiddenMargins compatibleTubes
              j hj hnext c s (by simpa [u, v] using hrep) hspos
              (by
                simpa [p, v, rho, chart, Cmodel, a] using hCeqBall)
          change
            sep.leftHalf j hj ∩ Metric.ball p rho ⊆ chart '' Lmodel ∧
              sep.leftHalf (j + 1) hnext ∩ Metric.ball p rho ⊆ chart '' Lmodel ∧
              sep.rightHalf j hj ∩ Metric.ball p rho ⊆ chart '' Rmodel ∧
              sep.rightHalf (j + 1) hnext ∩ Metric.ball p rho ⊆ chart '' Rmodel at hraw
          exact hraw
        · rcases hstraight with ⟨hs0, hcneg⟩
          exact outgoingFrameStraightHalfTubeRouting γ controlRadii middleSegments
            forbiddenMargins compatibleTubes j hj hnext p u v rho c s chart
            Cmodel Lmodel Rmodel rfl rfl rfl hv rfl rfl rfl hrep hs0 hcneg hCeqBall
      rcases hroute with ⟨hleft_prev, hleft_next, hright_prev, hright_next⟩
      have hGbase_subset_relint : chart '' Gbase ⊆ γ.relativeInterior :=
        outgoingRaySubsetRelativeInterior γ j hj hnext p v rho rfl rfl hv
          hrho_lt_vnorm (chart '' Gbase) hGbase_eq
      have hGother_subset_relint : chart '' Gother ⊆ γ.relativeInterior :=
        incomingRaySubsetRelativeInterior γ j hj p u rho rfl rfl hu
          hrho_lt_unorm (chart '' Gother) hGother_eq
      have hbad_subset_relint :
          (chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set E) ⊆
            γ.relativeInterior := by
        rintro x ((hxG | hxG) | hxP)
        · exact hGbase_subset_relint hxG
        · exact hGother_subset_relint hxG
        · rw [Set.mem_singleton_iff] at hxP
          simpa [hxP] using hvertex_relint
      have hcarrier_disk_subset_bad :
          γ.carrier ∩ vertexLocalPieces.vertexDisk i ⊆
            (chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set E) := by
        rintro x ⟨hxcarrier, hxDisk⟩
        rcases vertexLocalPieces.vertexDisk_carrier_subset_incident_segments
            i x hxDisk hxcarrier with
          ⟨k, hk, hxseg, hincident⟩
        have hk_cases : k = j ∨ k = j + 1 := by
          rcases hincident with hleft_inc | hright_inc
          · have : j + 1 = k := by
              calc
                j + 1 = i.1 := hji
                _ = k := hleft_inc
            exact Or.inr this.symm
          · have : j + 1 = k + 1 := by
              calc
                j + 1 = i.1 := hji
                _ = k + 1 := hright_inc
            exact Or.inl (by omega)
        rw [segment_eq_image_lineMap] at hxseg
        rcases hxseg with ⟨t, ht, htx⟩
        rcases hk_cases with hk_eq | hk_eq
        · subst k
          by_cases ht_one : t = 1
          · right
            rw [Set.mem_singleton_iff]
            rw [← htx]
            apply PiLp.ext
            intro k
            fin_cases k <;>
              simp [p, AffineMap.lineMap_apply_module, ht_one]
          · refine Or.inl (Or.inr ?_)
            rw [hGother_eq]
            have ht_lt_one : t < 1 := lt_of_le_of_ne ht.2 ht_one
            refine ⟨hdisk_to_ball hxDisk, 1 - t, by linarith, ?_⟩
            rw [← htx]
            have haxis :
                p + (1 - t) • u =
                  AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j] (1 - t) := by
              simpa [p, u] using
                chart_axis_param_eq_lineMap γ.vertices[j + 1] γ.vertices[j] (1 - t)
            have hrev :
                AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j] (1 - t) =
                  AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t := by
              exact AffineMap.lineMap_apply_one_sub
                γ.vertices[j + 1] γ.vertices[j] t
            exact (haxis.trans hrev).symm
        · subst k
          by_cases ht_zero : t = 0
          · right
            rw [Set.mem_singleton_iff]
            rw [← htx]
            apply PiLp.ext
            intro k
            fin_cases k <;>
              simp [p, AffineMap.lineMap_apply_module, ht_zero]
          · refine Or.inl (Or.inl ?_)
            rw [hGbase_eq]
            have ht_pos' : 0 < t := lt_of_le_of_ne ht.1 (fun h => ht_zero h.symm)
            refine ⟨hdisk_to_ball hxDisk, t, ht_pos', ?_⟩
            rw [← htx]
            have hline :
                p + t • v =
                  AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t := by
              simpa [p, v] using
                chart_axis_param_eq_lineMap γ.vertices[j + 1] γ.vertices[j + 2] t
            exact hline.symm
      have hL_disj_carrier : Disjoint (chart '' Lmodel) γ.carrier := by
        rw [Set.disjoint_left]
        intro x hxL hxcarrier
        exact (Set.disjoint_left.mp hLbad_disj) hxL
          (hcarrier_disk_subset_bad ⟨hxcarrier, hLsubC hxL⟩)
      have hR_disj_carrier : Disjoint (chart '' Rmodel) γ.carrier := by
        rw [Set.disjoint_left]
        intro x hxR hxcarrier
        exact (Set.disjoint_left.mp hRbad_disj) hxR
          (hcarrier_disk_subset_bad ⟨hxcarrier, hRsubC hxR⟩)
      have hwithout :
          vertexLocalPieces.vertexDisk i \ γ.relativeInterior =
            chart '' Lmodel ∪ chart '' Rmodel := by
        ext x
        constructor
        · rintro ⟨hxDisk, hxNotRel⟩
          have hxBall := hdisk_to_ball hxDisk
          have hxNotBad :
              x ∉ (chart '' Gbase) ∪ (chart '' Gother) ∪ ({p} : Set E) := by
            intro hxBad
            exact hxNotRel (hbad_subset_relint hxBad)
          rw [← hsplit]
          exact ⟨hxBall, hxNotBad⟩
        · rintro (hxL | hxR)
          · refine ⟨hLsubC hxL, ?_⟩
            intro hxRel
            exact (Set.disjoint_left.mp hL_disj_carrier) hxL
              (hrel_subset_carrier hxRel)
          · refine ⟨hRsubC hxR, ?_⟩
            intro hxRel
            exact (Set.disjoint_left.mp hR_disj_carrier) hxR
              (hrel_subset_carrier hxRel)
      have hout_germ_chart_Gbase :
          (AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2]) ''
              Set.Ioo (0 : ℝ)
                (controlRadii.radius ⟨j + 1, Nat.lt_of_succ_lt hnext⟩ /
                  dist γ.vertices[j + 1] γ.vertices[j + 2]) ⊆
            chart '' Gbase := by
        exact outgoingGermSubsetChartRay γ controlRadii middleSegments
          forbiddenMargins compatibleTubes vertexLocalPieces i j hj hnext hi_eq p v rho
          rfl rfl rfl (chart '' Gbase) hGbase_eq
      have hin_germ_chart_Gother :
          (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
              Set.Ioo
                (1 - controlRadii.radius ⟨j + 1, hj⟩ /
                  dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) ⊆
            chart '' Gother := by
        exact incomingGermSubsetChartRay γ controlRadii middleSegments
          forbiddenMargins compatibleTubes vertexLocalPieces i j hj hi_eq p u rho
          rfl rfl rfl (chart '' Gother) hGother_eq
      refine ⟨vertexLocalPieces.vertexDisk i, chart '' Lmodel, chart '' Rmodel, ?_⟩
      refine ⟨vertexLocalPieces.vertexDisk_open i, hLopen, hRopen, ?_, ?_, ?_,
        hLsubC, hRsubC, hLconn, hRconn, hL_disj_carrier, hR_disj_carrier,
        hLRdisj, ?_, ?_, hwithout, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx
        exact hx
      · intro _ _
        rfl
      · intro hend
        rcases hend with hzero | hlast
        · omega
        · omega
      · intro k hk
        by_cases hk_prev : k = j
        · subst k
          rintro x hx
          exact hleft_prev ⟨hx.1, hdisk_to_ball hx.2⟩
        · by_cases hk_next : k = j + 1
          · subst k
            rintro x hx
            exact hleft_next ⟨hx.1, hdisk_to_ball hx.2⟩
          · exact leftHalf_inter_subset_of_nonincident i
              (vertexLocalPieces.vertexDisk i) (chart '' Lmodel) (by intro x hx; exact hx)
              k hk
              (by
                change i.1 ≠ k
                omega)
              (by
                change i.1 ≠ k + 1
                omega)
      · intro k hk
        by_cases hk_prev : k = j
        · subst k
          rintro x hx
          exact hright_prev ⟨hx.1, hdisk_to_ball hx.2⟩
        · by_cases hk_next : k = j + 1
          · subst k
            rintro x hx
            exact hright_next ⟨hx.1, hdisk_to_ball hx.2⟩
          · exact rightHalf_inter_subset_of_nonincident i
              (vertexLocalPieces.vertexDisk i) (chart '' Rmodel) (by intro x hx; exact hx)
              k hk
              (by
                change i.1 ≠ k
                omega)
              (by
                change i.1 ≠ k + 1
                omega)
      · intro k hk hik
        have hk_eq : k = j + 1 := by
          have hval := congrArg Fin.val hik
          have : i.1 = k := by simpa using hval
          omega
        subst k
        intro x hx
        have hxEP :=
          vertexLocalPieces.outgoing_germ_subset_endpointPiece (j + 1) hnext hx
        rw [vertexLocalPieces.endpointPiece_eq] at hxEP
        simpa [hi_eq] using hxEP.1
      · intro k hk hik
        have hk_eq : k = j := by
          have hval := congrArg Fin.val hik
          have : i.1 = k + 1 := by simpa using hval
          omega
        subst k
        intro x hx
        have hxEP := vertexLocalPieces.incoming_germ_subset_endpointPiece j hj hx
        rw [vertexLocalPieces.endpointPiece_eq] at hxEP
        simpa [hi_eq] using hxEP.1
      · intro k hk hik
        have hk_eq : k = j + 1 := by
          have hval := congrArg Fin.val hik
          have : i.1 = k := by simpa using hval
          omega
        subst k
        rw [vertexLocalPieces.outgoingLeftAttachment_eq]
        rintro x hx
        exact hleft_next ⟨hx.2, hdisk_to_ball (by simpa [hi_eq] using hx.1)⟩
      · intro k hk hik
        have hk_eq : k = j + 1 := by
          have hval := congrArg Fin.val hik
          have : i.1 = k := by simpa using hval
          omega
        subst k
        rw [vertexLocalPieces.outgoingRightAttachment_eq]
        rintro x hx
        exact hright_next ⟨hx.2, hdisk_to_ball (by simpa [hi_eq] using hx.1)⟩
      · intro k hk hik
        have hk_eq : k = j := by
          have hval := congrArg Fin.val hik
          have : i.1 = k + 1 := by simpa using hval
          omega
        subst k
        rw [vertexLocalPieces.incomingLeftAttachment_eq]
        rintro x hx
        exact hleft_prev ⟨hx.2, hdisk_to_ball (by simpa [hi_eq] using hx.1)⟩
      · intro k hk hik
        have hk_eq : k = j := by
          have hval := congrArg Fin.val hik
          have : i.1 = k + 1 := by simpa using hval
          omega
        subst k
        rw [vertexLocalPieces.incomingRightAttachment_eq]
        rintro x hx
        exact hright_prev ⟨hx.2, hdisk_to_ball (by simpa [hi_eq] using hx.1)⟩
      · intro k hk hik x hx
        have hk_eq : k = j + 1 := by
          have hval := congrArg Fin.val hik
          have : i.1 = k := by simpa using hval
          omega
        subst k
        rcases hout_germ_chart_Gbase hx with ⟨z, hzG, rfl⟩
        exact chart_mem_closure_image p v
          ((twoRay_base_subset_closure_left a c s hsector_pos) hzG)
      · intro k hk hik x hx
        have hk_eq : k = j + 1 := by
          have hval := congrArg Fin.val hik
          have : i.1 = k := by simpa using hval
          omega
        subst k
        rcases hout_germ_chart_Gbase hx with ⟨z, hzG, rfl⟩
        exact chart_mem_closure_image p v
          ((twoRay_base_subset_closure_right a c s) hzG)
      · intro k hk hik x hx
        have hk_eq : k = j := by
          have hval := congrArg Fin.val hik
          have : i.1 = k + 1 := by simpa using hval
          omega
        subst k
        rcases hin_germ_chart_Gother hx with ⟨z, hzG, rfl⟩
        exact chart_mem_closure_image p v
          ((twoRay_other_subset_closure_left a c s hsector_pos) hzG)
      · intro k hk hik x hx
        have hk_eq : k = j := by
          have hval := congrArg Fin.val hik
          have : i.1 = k + 1 := by simpa using hval
          omega
        subst k
        rcases hin_germ_chart_Gother hx with ⟨z, hzG, rfl⟩
        exact chart_mem_closure_image p v
          ((twoRay_other_subset_closure_right a c s hsector_pos) hzG)
      · intro _ _
        have hp : γ.vertices[i.1] =
            p + (0 : E) 0 • v + (0 : E) 1 • PlanarRot90 v := by
          simp [p, hi_eq]
        rw [hp]
        exact chart_mem_closure_image p v
          (twoRay_origin_mem_closure_left a c s ha hsector_pos)
      · intro _ _
        have hp : γ.vertices[i.1] =
            p + (0 : E) 0 • v + (0 : E) 1 • PlanarRot90 v := by
          simp [p, hi_eq]
        rw [hp]
        exact chart_mem_closure_image p v
          (twoRay_origin_mem_closure_right a c s ha)
-- [TABLET NODE: PolygonalArcCollarLocalTopologyDataExists]
lemma PolygonalArcCollarLocalTopologyDataExists (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (compatibleTubes :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (vertexLocalPieces :
      PolygonalArcCollarVertexLocalPieceData γ controlRadii middleSegments
        forbiddenMargins
        compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData) :
    Nonempty
      (PolygonalArcCollarLocalTopologyData γ controlRadii middleSegments
        forbiddenMargins compatibleTubes vertexLocalPieces) := by
  let E := EuclideanSpace ℝ (Fin 2)
  let Good :=
    localTopologyGood γ controlRadii middleSegments forbiddenMargins
      compatibleTubes vertexLocalPieces
  have hlen_two : 2 ≤ γ.vertices.length := γ.length_ge_two
  have hlen_pos : 0 < γ.vertices.length := by omega
  have hj0 : 0 + 1 < γ.vertices.length := by omega
  have hGoodInitial :
      ∃ C L R : Set E, Good ⟨0, hlen_pos⟩ C L R := by
    exact localTopologyGoodInitial γ controlRadii middleSegments forbiddenMargins
      compatibleTubes vertexLocalPieces hlen_pos hj0
  let lastJ : ℕ := γ.vertices.length - 2
  have hlastJ : lastJ + 1 < γ.vertices.length := by
    dsimp [lastJ]
    omega
  have hlastJ_succ : lastJ + 2 = γ.vertices.length := by
    dsimp [lastJ]
    omega
  have hGoodTerminal :
      ∃ C L R : Set E, Good ⟨lastJ + 1, hlastJ⟩ C L R := by
    exact localTopologyGoodTerminal γ controlRadii middleSegments forbiddenMargins
      compatibleTubes vertexLocalPieces lastJ hlastJ hlastJ_succ
  have hGood : ∀ i : Fin γ.vertices.length, ∃ C L R : Set E, Good i C L R := by
    intro i
    by_cases hi0 : i.1 = 0
    · have hi_eq : i = ⟨0, hlen_pos⟩ := by
        apply Fin.ext
        simpa using hi0
      simpa [hi_eq] using hGoodInitial
    · by_cases hiterm : i.1 + 1 = γ.vertices.length
      · have hi_eq : i = ⟨lastJ + 1, hlastJ⟩ := by
          apply Fin.ext
          dsimp [lastJ] at *
          omega
        simpa [hi_eq] using hGoodTerminal
      · have hi_pos : 0 < i.1 := Nat.pos_of_ne_zero hi0
        have hi_next : i.1 + 1 < γ.vertices.length := by
          have hi_lt : i.1 < γ.vertices.length := i.2
          omega
        exact localTopologyGoodInterior γ controlRadii middleSegments
          forbiddenMargins compatibleTubes vertexLocalPieces i hi_pos hi_next
  let vertexCollar : Fin γ.vertices.length → Set E :=
    fun i => Classical.choose (hGood i)
  let leftSidePiece : Fin γ.vertices.length → Set E :=
    fun i => Classical.choose (Classical.choose_spec (hGood i))
  let rightSidePiece : Fin γ.vertices.length → Set E :=
    fun i =>
      Classical.choose (Classical.choose_spec
        (Classical.choose_spec (hGood i)))
  have hGoodSpec :
      ∀ i : Fin γ.vertices.length,
        Good i (vertexCollar i) (leftSidePiece i) (rightSidePiece i) := by
    intro i
    dsimp [vertexCollar, leftSidePiece, rightSidePiece]
    exact Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (hGood i)))
  refine ⟨
    { vertexCollar := vertexCollar
      leftSidePiece := leftSidePiece
      rightSidePiece := rightSidePiece
      vertexCollar_open := ?_
      leftSidePiece_open := ?_
      rightSidePiece_open := ?_
      vertexCollar_subset_vertexDisk := ?_
      interior_vertexCollar_eq_vertexDisk := ?_
      endpoint_vertexCollar_omits_vertex := ?_
      vertexCollar_subset_eta_neighborhood := ?_
      vertexCollar_carrier_subset_incident_segments := ?_
      outgoing_germ_subset_vertexCollar := ?_
      incoming_germ_subset_vertexCollar := ?_
      outgoing_germ_subset_closure_leftSidePiece := ?_
      outgoing_germ_subset_closure_rightSidePiece := ?_
      incoming_germ_subset_closure_leftSidePiece := ?_
      incoming_germ_subset_closure_rightSidePiece := ?_
      interior_vertex_mem_closure_leftSidePiece := ?_
      interior_vertex_mem_closure_rightSidePiece := ?_
      leftSidePiece_subset_vertexCollar := ?_
      rightSidePiece_subset_vertexCollar := ?_
      leftSidePiece_connected := ?_
      rightSidePiece_connected := ?_
      leftSidePiece_disjoint_carrier := ?_
      rightSidePiece_disjoint_carrier := ?_
      local_sidePieces_disjoint := ?_
      leftHalf_inter_vertexCollar_subset_leftSidePiece := ?_
      rightHalf_inter_vertexCollar_subset_rightSidePiece := ?_
      vertexCollar_without_arc := ?_
      outgoingLeftAttachment_subset_leftSidePiece := ?_
      outgoingRightAttachment_subset_rightSidePiece := ?_
      incomingLeftAttachment_subset_leftSidePiece := ?_
      incomingRightAttachment_subset_rightSidePiece := ?_ }⟩
  · intro i
    rcases hGoodSpec i with ⟨hCopen, _⟩
    exact hCopen
  · intro i
    rcases hGoodSpec i with ⟨_, hLopen, _⟩
    exact hLopen
  · intro i
    rcases hGoodSpec i with ⟨_, _, hRopen, _⟩
    exact hRopen
  · intro i
    rcases hGoodSpec i with ⟨_, _, _, hCsub, _⟩
    exact hCsub
  · intro i hpos hnext
    rcases hGoodSpec i with ⟨_, _, _, _, hinterior, _⟩
    exact hinterior hpos hnext
  · intro i hend
    rcases hGoodSpec i with ⟨_, _, _, _, _, hendpoint, _⟩
    exact hendpoint hend
  · intro i z hz
    rcases hGoodSpec i with ⟨_, _, _, hCsub, _⟩
    exact vertexLocalPieces.vertexDisk_subset_eta_neighborhood i z
      (hCsub hz)
  · intro i z hz hcarrier
    rcases hGoodSpec i with ⟨_, _, _, hCsub, _⟩
    exact vertexLocalPieces.vertexDisk_carrier_subset_incident_segments i z
      (hCsub hz) hcarrier
  · intro j hj
    rcases hGoodSpec ⟨j, Nat.lt_of_succ_lt hj⟩ with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hout, _⟩
    exact hout j hj rfl
  · intro j hj
    rcases hGoodSpec ⟨j + 1, hj⟩ with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hin, _⟩
    exact hin j hj rfl
  · intro j hj x hx
    rcases hGoodSpec ⟨j, Nat.lt_of_succ_lt hj⟩ with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        houtClL, _, _, _, _, _⟩
    exact houtClL j hj rfl hx
  · intro j hj x hx
    rcases hGoodSpec ⟨j, Nat.lt_of_succ_lt hj⟩ with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, houtClR, _, _, _, _⟩
    exact houtClR j hj rfl hx
  · intro j hj x hx
    rcases hGoodSpec ⟨j + 1, hj⟩ with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, hinClL, _, _, _⟩
    exact hinClL j hj rfl hx
  · intro j hj x hx
    rcases hGoodSpec ⟨j + 1, hj⟩ with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, hinClR, _, _⟩
    exact hinClR j hj rfl hx
  · intro i hi_pos hi_next
    rcases hGoodSpec i with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, hvClL, _⟩
    exact hvClL hi_pos hi_next
  · intro i hi_pos hi_next
    rcases hGoodSpec i with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, hvClR⟩
    exact hvClR hi_pos hi_next
  · intro i
    rcases hGoodSpec i with ⟨_, _, _, _, _, _, hLsub, _⟩
    exact hLsub
  · intro i
    rcases hGoodSpec i with ⟨_, _, _, _, _, _, _, hRsub, _⟩
    exact hRsub
  · intro i
    rcases hGoodSpec i with ⟨_, _, _, _, _, _, _, _, hLconn, _⟩
    exact hLconn
  · intro i
    rcases hGoodSpec i with ⟨_, _, _, _, _, _, _, _, _, hRconn, _⟩
    exact hRconn
  · intro i
    rcases hGoodSpec i with ⟨_, _, _, _, _, _, _, _, _, _, hLdisj, _⟩
    exact hLdisj
  · intro i
    rcases hGoodSpec i with ⟨_, _, _, _, _, _, _, _, _, _, _, hRdisj, _⟩
    exact hRdisj
  · intro i
    rcases hGoodSpec i with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hLRdisj, _⟩
    exact hLRdisj
  · intro j hj i
    rcases hGoodSpec i with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hleftHalf, _⟩
    exact hleftHalf j hj
  · intro j hj i
    rcases hGoodSpec i with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hrightHalf, _⟩
    exact hrightHalf j hj
  · intro i
    rcases hGoodSpec i with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hwithout, _⟩
    exact hwithout
  · intro j hj
    rcases hGoodSpec ⟨j, Nat.lt_of_succ_lt hj⟩ with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, houtLeft, _⟩
    exact houtLeft j hj rfl
  · intro j hj
    rcases hGoodSpec ⟨j, Nat.lt_of_succ_lt hj⟩ with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, houtRight, _⟩
    exact houtRight j hj rfl
  · intro j hj
    rcases hGoodSpec ⟨j + 1, hj⟩ with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hinLeft, _⟩
    exact hinLeft j hj rfl
  · intro j hj
    rcases hGoodSpec ⟨j + 1, hj⟩ with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hinRight, _⟩
    exact hinRight j hj rfl
