import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.PlanarRot90ConeAvoidsFiniteRays
import ErdosProblems.Erdos733.ST.PlanarRot90Decomposition
import ErdosProblems.Erdos733.ST.PolygonalArcEndpointDiskCappedTaperChartTransport

open Classical
noncomputable section


-- [TABLET NODE: PlanarFiniteRayCappedSideSectors]
lemma PlanarFiniteRayCappedSideSectors
    (directions : Finset (EuclideanSpace ℝ (Fin 2)))
    (p d : EuclideanSpace ℝ (Fin 2)) (radius : ℝ)
    (hd : d ≠ 0) (hradius : 0 < radius)
    (hnotParallel : ∀ v ∈ directions,
      ¬ ∃ c : ℝ, 0 < c ∧ v = c • d) :
    ∃ kappaMax : ℝ, 0 < kappaMax ∧
      ∀ localRadius localKappa : ℝ,
        0 < localRadius → localRadius ≤ radius →
          0 < localKappa → localKappa ≤ kappaMax →
      let raySet : Set (EuclideanSpace ℝ (Fin 2)) :=
        ({p} : Set (EuclideanSpace ℝ (Fin 2))) ∪
          ⋃ v : {v : EuclideanSpace ℝ (Fin 2) // v ∈ directions},
            {q | ∃ c : ℝ, 0 ≤ c ∧ q = p + c • v.1}
      let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
        fun z => p + z 0 • d + z 1 • PlanarRot90 d
      let a : ℝ := localRadius / ‖d‖
      let leftModel : Set (EuclideanSpace ℝ (Fin 2)) :=
        {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧
          0 < z 1 ∧ z 1 < localKappa * z 0}
      let rightModel : Set (EuclideanSpace ℝ (Fin 2)) :=
        {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧
          -localKappa * z 0 < z 1 ∧ z 1 < 0}
      ∃ leftSector rightSector : Set (EuclideanSpace ℝ (Fin 2)),
        leftSector = chart '' leftModel ∧
          rightSector = chart '' rightModel ∧
          IsOpen leftSector ∧ IsOpen rightSector ∧
          Convex ℝ leftSector ∧ Convex ℝ rightSector ∧
          leftSector ⊆ Metric.ball p localRadius ∧
          rightSector ⊆ Metric.ball p localRadius ∧
          p ∈ closure leftSector ∧ p ∈ closure rightSector ∧
          p ∉ leftSector ∧ p ∉ rightSector ∧
          leftSector ∩ raySet = (∅ : Set (EuclideanSpace ℝ (Fin 2))) ∧
          rightSector ∩ raySet = (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
-- BODY
  obtain ⟨kappaMax, hkappaMax, havoid⟩ :=
    PlanarRot90ConeAvoidsFiniteRays directions d hd hnotParallel
  refine ⟨kappaMax, hkappaMax, ?_⟩
  intro localRadius localKappa hlocalRadius _hlocalRadiusLe
    hlocalKappa hlocalKappaLe
  dsimp only
  let raySet : Set (EuclideanSpace ℝ (Fin 2)) :=
    ({p} : Set (EuclideanSpace ℝ (Fin 2))) ∪
      ⋃ v : {v : EuclideanSpace ℝ (Fin 2) // v ∈ directions},
        {q | ∃ c : ℝ, 0 ≤ c ∧ q = p + c • v.1}
  let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun z => p + z 0 • d + z 1 • PlanarRot90 d
  let a : ℝ := localRadius / ‖d‖
  let leftModel : Set (EuclideanSpace ℝ (Fin 2)) :=
    {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧
      0 < z 1 ∧ z 1 < localKappa * z 0}
  let rightModel : Set (EuclideanSpace ℝ (Fin 2)) :=
    {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧
      -localKappa * z 0 < z 1 ∧ z 1 < 0}
  have hnormd : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have ha : 0 < a := div_pos hlocalRadius hnormd
  have hp1 : p + d ≠ p := by
    intro h
    apply hd
    have := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q - p) h
    simpa using this
  have htransport :=
    PolygonalArcEndpointDiskCappedTaperChartTransport p (p + d)
      localRadius localKappa hp1 hlocalRadius hlocalKappa
  rcases htransport with
    ⟨_ha, _hCoreOpen, hleftOpen, hrightOpen, _hleftConnected,
      _hrightConnected, _hchartLeftConnected, _hchartRightConnected,
      _hmodelDisjoint, _hchartDisjoint, _hzeroNotCore, _hgermSubCore,
      _hcoreSplit, _hcoordBall, hcoreBall, hpNotCore, _haxisOmit,
      _hgerm, _hchartSplit⟩
  have hdist : dist p (p + d) = ‖d‖ := by
    rw [dist_eq_norm]
    have hp : p - (p + d) = -d := by abel
    rw [hp, norm_neg]
  have chartImageOpen (S : Set (EuclideanSpace ℝ (Fin 2)))
      (hS : IsOpen S) : IsOpen (chart '' S) := by
    let invCoord : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun q => WithLp.toLp 2 (fun i : Fin 2 =>
        if i = 0 then inner ℝ (q - p) d / (‖d‖ ^ 2)
        else inner ℝ (q - p) (PlanarRot90 d) / (‖d‖ ^ 2))
    have hinvContinuous : Continuous invCoord := by
      have hplain : Continuous fun q : EuclideanSpace ℝ (Fin 2) =>
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
    have hleftInverse : ∀ z, invCoord (chart z) = z := by
      intro z
      have hrep : chart z - p = z 0 • d + z 1 • PlanarRot90 d := by
        dsimp [chart]
        abel
      have hcoeff :=
        PlanarRot90CoefficientUniqueness (d := d) (v := chart z - p) hd hrep
      apply PiLp.ext
      intro i
      fin_cases i
      · simpa [invCoord] using hcoeff.1.symm
      · simpa [invCoord] using hcoeff.2.symm
    have hrightInverse : ∀ q, chart (invCoord q) = q := by
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
    have himage : chart '' S = invCoord ⁻¹' S := by
      ext q
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [hleftInverse z] using hz
      · intro hq
        exact ⟨invCoord q, hq, hrightInverse q⟩
    rw [himage]
    exact hS.preimage hinvContinuous
  have hleftOpen' : IsOpen (chart '' leftModel) := by
    apply chartImageOpen
    simpa [leftModel, a, hdist] using hleftOpen
  have hrightOpen' : IsOpen (chart '' rightModel) := by
    apply chartImageOpen
    simpa [rightModel, a, hdist] using hrightOpen
  let X : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ :=
    PiLp.projₗ (𝕜 := ℝ) (p := (2 : ENNReal))
      (β := fun _ : Fin 2 => ℝ) 0
  let Y : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ :=
    PiLp.projₗ (𝕜 := ℝ) (p := (2 : ENNReal))
      (β := fun _ : Fin 2 => ℝ) 1
  let Lower : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ := (-localKappa) • X - Y
  let Upper : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ := Y - localKappa • X
  have hballConv : Convex ℝ (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a) :=
    convex_ball _ _
  have hXgt : Convex ℝ {z : EuclideanSpace ℝ (Fin 2) | (0 : ℝ) < X z} :=
    convex_halfSpace_gt X.isLinear 0
  have hYgt : Convex ℝ {z : EuclideanSpace ℝ (Fin 2) | (0 : ℝ) < Y z} :=
    convex_halfSpace_gt Y.isLinear 0
  have hYlt : Convex ℝ {z : EuclideanSpace ℝ (Fin 2) | Y z < (0 : ℝ)} :=
    convex_halfSpace_lt Y.isLinear 0
  have hLowerLt : Convex ℝ {z : EuclideanSpace ℝ (Fin 2) | Lower z < (0 : ℝ)} :=
    convex_halfSpace_lt Lower.isLinear 0
  have hUpperLt : Convex ℝ {z : EuclideanSpace ℝ (Fin 2) | Upper z < (0 : ℝ)} :=
    convex_halfSpace_lt Upper.isLinear 0
  have hballEq : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a =
      {z : EuclideanSpace ℝ (Fin 2) | z 0 ^ 2 + z 1 ^ 2 < a ^ 2} := by
    simpa [Fin.sum_univ_two] using
      (EuclideanSpace.ball_zero_eq (n := Fin 2) a ha.le)
  have hleftConvModel : Convex ℝ leftModel := by
    rw [show leftModel = Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a ∩
        {z | (0 : ℝ) < X z} ∩ {z | (0 : ℝ) < Y z} ∩
          {z | Upper z < (0 : ℝ)} by
      ext z
      dsimp [leftModel, X, Y, Upper]
      rw [hballEq]
      constructor
      · rintro ⟨hx, hdisk, hy, hupp⟩
        exact ⟨⟨⟨hdisk, hx⟩, hy⟩, sub_neg.mpr hupp⟩
      · rintro ⟨⟨⟨hdisk, hx⟩, hy⟩, hupp⟩
        exact ⟨hx, hdisk, hy, sub_neg.mp hupp⟩]
    exact (((hballConv.inter hXgt).inter hYgt).inter hUpperLt)
  have hrightConvModel : Convex ℝ rightModel := by
    rw [show rightModel = Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a ∩
        {z | (0 : ℝ) < X z} ∩ {z | Lower z < (0 : ℝ)} ∩
          {z | Y z < (0 : ℝ)} by
      ext z
      dsimp [rightModel, X, Y, Lower]
      rw [hballEq]
      constructor
      · rintro ⟨hx, hdisk, hlow, hy⟩
        exact ⟨⟨⟨hdisk, hx⟩, sub_neg.mpr hlow⟩, hy⟩
      · rintro ⟨⟨⟨hdisk, hx⟩, hlow⟩, hy⟩
        exact ⟨hx, hdisk, sub_neg.mp hlow, hy⟩]
    exact (((hballConv.inter hXgt).inter hLowerLt).inter hYlt)
  have imageConvex (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : Convex ℝ S) :
      Convex ℝ (chart '' S) := by
    intro x hx y hy u v hu hv huv
    rcases hx with ⟨zx, hzx, rfl⟩
    rcases hy with ⟨zy, hzy, rfl⟩
    refine ⟨u • zx + v • zy, hS hzx hzy hu hv huv, ?_⟩
    have hpcoord (i : Fin 2) : p i = p i * u + p i * v := by
      rw [← mul_add, huv, mul_one]
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [chart, PlanarRot90] <;> ring_nf <;>
      linarith [hpcoord 0, hpcoord 1]
  have hleftConv : Convex ℝ (chart '' leftModel) :=
    imageConvex leftModel hleftConvModel
  have hrightConv : Convex ℝ (chart '' rightModel) :=
    imageConvex rightModel hrightConvModel
  have hleftSubCore : leftModel ⊆
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧
        -localKappa * z 0 < z 1 ∧ z 1 < localKappa * z 0} := by
    rintro z ⟨hz0, hzdisk, hz1, hzupper⟩
    exact ⟨hz0, hzdisk, by nlinarith [mul_pos hlocalKappa hz0], hzupper⟩
  have hrightSubCore : rightModel ⊆
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧
        -localKappa * z 0 < z 1 ∧ z 1 < localKappa * z 0} := by
    rintro z ⟨hz0, hzdisk, hzlower, hz1⟩
    exact ⟨hz0, hzdisk, hzlower, by nlinarith [mul_pos hlocalKappa hz0]⟩
  have hleftBall : chart '' leftModel ⊆ Metric.ball p localRadius := by
    apply Set.Subset.trans (Set.image_mono hleftSubCore)
    simpa [chart, a, sub_eq_add_neg] using hcoreBall
  have hrightBall : chart '' rightModel ⊆ Metric.ball p localRadius := by
    apply Set.Subset.trans (Set.image_mono hrightSubCore)
    simpa [chart, a, sub_eq_add_neg] using hcoreBall
  have hpNotLeft : p ∉ chart '' leftModel := by
    intro hpLeft
    apply hpNotCore
    simpa [chart, a, sub_eq_add_neg] using Set.image_mono hleftSubCore hpLeft
  have hpNotRight : p ∉ chart '' rightModel := by
    intro hpRight
    apply hpNotCore
    simpa [chart, a, sub_eq_add_neg] using Set.image_mono hrightSubCore hpRight
  let germModel : Set (EuclideanSpace ℝ (Fin 2)) :=
    {z | 0 < z 0 ∧ z 0 < a ∧ z 1 = 0}
  have hGclosureLeft : germModel ⊆ closure leftModel := by
    intro z hzG
    rw [Metric.mem_closure_iff]
    intro epsilon hepsilon
    have hz0 : 0 < z 0 := hzG.1
    have hza : z 0 < a := hzG.2.1
    have hz1 : z 1 = 0 := hzG.2.2
    have hmargin : 0 < a ^ 2 - z 0 ^ 2 := by nlinarith
    let delta : ℝ := min (min (epsilon / 2) (localKappa * z 0 / 2))
      (min (1 / 2) ((a ^ 2 - z 0 ^ 2) / 2))
    have hdelta : 0 < delta := by dsimp [delta]; positivity
    have hdeltaEps : delta < epsilon := by
      have hle : delta ≤ epsilon / 2 :=
        le_trans (min_le_left _ _) (min_le_left _ _)
      linarith
    have hdeltaK : delta < localKappa * z 0 := by
      have hle : delta ≤ localKappa * z 0 / 2 :=
        le_trans (min_le_left _ _) (min_le_right _ _)
      nlinarith [mul_pos hlocalKappa hz0]
    have hdeltaSq : delta ^ 2 < a ^ 2 - z 0 ^ 2 := by
      have hleMargin : delta ≤ (a ^ 2 - z 0 ^ 2) / 2 :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      have hleOne : delta ≤ 1 / 2 :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      nlinarith
    let w : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then z 0 else delta)
    refine ⟨w, ?_, ?_⟩
    · exact ⟨by simpa [w] using hz0, by simp [w]; nlinarith [hdeltaSq],
        by simp [w, hdelta], by simp [w, hdeltaK]⟩
    · rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
      simp [w, hz1, Real.dist_eq, Real.sqrt_sq_eq_abs, abs_of_pos hdelta]
      exact hdeltaEps
  have hGclosureRight : germModel ⊆ closure rightModel := by
    intro z hzG
    rw [Metric.mem_closure_iff]
    intro epsilon hepsilon
    have hz0 : 0 < z 0 := hzG.1
    have hza : z 0 < a := hzG.2.1
    have hz1 : z 1 = 0 := hzG.2.2
    have hmargin : 0 < a ^ 2 - z 0 ^ 2 := by nlinarith
    let delta : ℝ := min (min (epsilon / 2) (localKappa * z 0 / 2))
      (min (1 / 2) ((a ^ 2 - z 0 ^ 2) / 2))
    have hdelta : 0 < delta := by dsimp [delta]; positivity
    have hdeltaEps : delta < epsilon := by
      have hle : delta ≤ epsilon / 2 :=
        le_trans (min_le_left _ _) (min_le_left _ _)
      linarith
    have hdeltaK : delta < localKappa * z 0 := by
      have hle : delta ≤ localKappa * z 0 / 2 :=
        le_trans (min_le_left _ _) (min_le_right _ _)
      nlinarith [mul_pos hlocalKappa hz0]
    have hdeltaSq : delta ^ 2 < a ^ 2 - z 0 ^ 2 := by
      have hleMargin : delta ≤ (a ^ 2 - z 0 ^ 2) / 2 :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      have hleOne : delta ≤ 1 / 2 :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      nlinarith
    let w : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then z 0 else -delta)
    refine ⟨w, ?_, ?_⟩
    · exact ⟨by simpa [w] using hz0, by simp [w]; nlinarith [hdeltaSq],
        by simp [w]; nlinarith, by simp [w, hdelta]⟩
    · rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
      simp [w, hz1, Real.dist_eq, Real.sqrt_sq_eq_abs, abs_of_pos hdelta]
      exact hdeltaEps
  have hzeroClosureGerm :
      (0 : EuclideanSpace ℝ (Fin 2)) ∈ closure germModel := by
    rw [Metric.mem_closure_iff]
    intro epsilon hepsilon
    let t : ℝ := min (a / 2) (epsilon / 2)
    have ht : 0 < t := by dsimp [t]; positivity
    have hta : t < a := by
      have hle : t ≤ a / 2 := min_le_left _ _
      linarith
    have htepsilon : t < epsilon := by
      have hle : t ≤ epsilon / 2 := min_le_right _ _
      linarith
    let z : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t else 0)
    refine ⟨z, ?_, ?_⟩
    · constructor
      · simpa [z] using ht
      constructor
      · simpa [z] using hta
      · simp [z]
    · rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
      simp [z, Real.dist_eq, Real.sqrt_sq_eq_abs, abs_of_pos ht]
      exact htepsilon
  have hchartContinuous : Continuous chart := by
    dsimp [chart]
    fun_prop
  have hchartZero : chart 0 = p := by simp [chart]
  have hpClosureGermImage : p ∈ closure (chart '' germModel) := by
    have hmap : chart 0 ∈ closure (chart '' germModel) :=
      map_mem_closure hchartContinuous hzeroClosureGerm
        (fun z hz => ⟨z, hz, rfl⟩)
    simpa [hchartZero] using hmap
  have hGermImageLeft : chart '' germModel ⊆ closure (chart '' leftModel) := by
    rintro _ ⟨z, hz, rfl⟩
    exact map_mem_closure hchartContinuous (hGclosureLeft hz)
      (fun w hw => ⟨w, hw, rfl⟩)
  have hGermImageRight : chart '' germModel ⊆ closure (chart '' rightModel) := by
    rintro _ ⟨z, hz, rfl⟩
    exact map_mem_closure hchartContinuous (hGclosureRight hz)
      (fun w hw => ⟨w, hw, rfl⟩)
  have hpClosureLeft : p ∈ closure (chart '' leftModel) := by
    have h := closure_mono hGermImageLeft hpClosureGermImage
    simpa only [closure_closure] using h
  have hpClosureRight : p ∈ closure (chart '' rightModel) := by
    have h := closure_mono hGermImageRight hpClosureGermImage
    simpa only [closure_closure] using h
  have avoidSector (model : Set (EuclideanSpace ℝ (Fin 2)))
      (hmodel : ∀ z, z ∈ model →
        0 < z 0 ∧ |z 1| < localKappa * z 0)
      (hpNot : p ∉ chart '' model) :
      chart '' model ∩ raySet = (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext q
    constructor
    · rintro ⟨hqModel, hqRay⟩
      rcases hqRay with hqp | hqDirection
      · have hq : q = p := by simpa using hqp
        exact (hpNot (by simpa [hq] using hqModel)).elim
      · rcases Set.mem_iUnion.mp hqDirection with ⟨v, c, hc, hq⟩
        rcases hqModel with ⟨z, hz, rfl⟩
        have hzBounds := hmodel z hz
        have hzMax : |z 1| < kappaMax * z 0 :=
          lt_of_lt_of_le hzBounds.2
            (mul_le_mul_of_nonneg_right hlocalKappaLe hzBounds.1.le)
        have heq : c • v.1 = z 0 • d + z 1 • PlanarRot90 d := by
          calc
            c • v.1 = (p + c • v.1) - p := by abel
            _ = chart z - p := by rw [← hq]
            _ = z 0 • d + z 1 • PlanarRot90 d := by
              dsimp [chart]
              abel
        exact (havoid v.1 v.2 c (z 0) (z 1) hc hzBounds.1 hzMax) heq
    · simp
  have hleftAvoid : chart '' leftModel ∩ raySet = ∅ := by
    apply avoidSector leftModel
    · intro z hz
      exact ⟨hz.1, by rw [abs_of_pos hz.2.2.1]; exact hz.2.2.2⟩
    · exact hpNotLeft
  have hrightAvoid : chart '' rightModel ∩ raySet = ∅ := by
    apply avoidSector rightModel
    · intro z hz
      exact ⟨hz.1, by rw [abs_of_neg hz.2.2.2]; linarith [hz.2.2.1]⟩
    · exact hpNotRight
  exact ⟨chart '' leftModel, chart '' rightModel, rfl, rfl,
    hleftOpen', hrightOpen', hleftConv, hrightConv,
    hleftBall, hrightBall, hpClosureLeft, hpClosureRight,
    hpNotLeft, hpNotRight, hleftAvoid, hrightAvoid⟩
