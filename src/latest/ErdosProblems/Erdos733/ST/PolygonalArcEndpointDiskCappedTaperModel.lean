import Mathlib.Analysis.Convex.PathConnected
import ErdosProblems.Erdos733.ST.Preamble

open Set

-- [TABLET NODE: PolygonalArcEndpointDiskCappedTaperModel]
lemma PolygonalArcEndpointDiskCappedTaperModel (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
    let C : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧ z 1 < K * z 0}
    let L : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ 0 < z 1 ∧ z 1 < K * z 0}
    let R : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧ z 1 < 0}
    let G : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 < a ∧ z 1 = 0}
    IsOpen C ∧ IsOpen L ∧ IsOpen R ∧
      IsConnected L ∧ IsConnected R ∧
      Disjoint L R ∧ (0 : EuclideanSpace ℝ (Fin 2)) ∉ C ∧
      G ⊆ C ∧ C \ G = L ∪ R := by
-- BODY
  intro C L R G
  have hcoord0 : Continuous fun z : EuclideanSpace ℝ (Fin 2) => z 0 :=
    PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ) 0
  have hcoord1 : Continuous fun z : EuclideanSpace ℝ (Fin 2) => z 1 :=
    PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ) 1
  have hsumsq_cont : Continuous fun z : EuclideanSpace ℝ (Fin 2) =>
      z 0 ^ 2 + z 1 ^ 2 :=
    (hcoord0.pow 2).add (hcoord1.pow 2)
  have hlinLower : Continuous fun z : EuclideanSpace ℝ (Fin 2) => -K * z 0 - z 1 :=
    (continuous_const.mul hcoord0).sub hcoord1
  have hlinUpper : Continuous fun z : EuclideanSpace ℝ (Fin 2) => z 1 - K * z 0 :=
    hcoord1.sub (continuous_const.mul hcoord0)
  have hC_open : IsOpen C := by
    dsimp [C]
    repeat' apply IsOpen.inter
    · exact isOpen_lt continuous_const hcoord0
    · exact isOpen_lt hsumsq_cont continuous_const
    · exact isOpen_lt (continuous_const.mul hcoord0) hcoord1
    · exact isOpen_lt hcoord1 (continuous_const.mul hcoord0)
  have hL_open : IsOpen L := by
    dsimp [L]
    repeat' apply IsOpen.inter
    · exact isOpen_lt continuous_const hcoord0
    · exact isOpen_lt hsumsq_cont continuous_const
    · exact isOpen_lt continuous_const hcoord1
    · exact isOpen_lt hcoord1 (continuous_const.mul hcoord0)
  have hR_open : IsOpen R := by
    dsimp [R]
    repeat' apply IsOpen.inter
    · exact isOpen_lt continuous_const hcoord0
    · exact isOpen_lt hsumsq_cont continuous_const
    · exact isOpen_lt (continuous_const.mul hcoord0) hcoord1
    · exact isOpen_lt hcoord1 continuous_const
  let X : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ :=
    PiLp.projₗ (𝕜 := ℝ) (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ) 0
  let Y : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ :=
    PiLp.projₗ (𝕜 := ℝ) (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ) 1
  let Lower : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ := (-K) • X - Y
  let Upper : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ := Y - K • X
  have hBall_conv : Convex ℝ (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a) :=
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
  have hball_eq : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a =
      {z : EuclideanSpace ℝ (Fin 2) | z 0 ^ 2 + z 1 ^ 2 < a ^ 2} := by
    simpa [Fin.sum_univ_two] using (EuclideanSpace.ball_zero_eq (n := Fin 2) a ha.le)
  have hL_conv : Convex ℝ L := by
    rw [show L = Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a ∩
        {z | (0 : ℝ) < X z} ∩ {z | (0 : ℝ) < Y z} ∩
          {z | Upper z < (0 : ℝ)} by
      ext z
      dsimp [L, X, Y, Upper]
      rw [hball_eq]
      constructor
      · rintro ⟨hx, hdisk, hypos, hupper⟩
        exact ⟨⟨⟨hdisk, hx⟩, hypos⟩, sub_neg.mpr hupper⟩
      · rintro ⟨⟨⟨hdisk, hx⟩, hypos⟩, hupper⟩
        exact ⟨hx, hdisk, hypos, sub_neg.mp hupper⟩]
    exact (((hBall_conv.inter hXgt).inter hYgt).inter hUpperLt)
  have hR_conv : Convex ℝ R := by
    rw [show R = Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a ∩
        {z | (0 : ℝ) < X z} ∩ {z | Lower z < (0 : ℝ)} ∩
          {z | Y z < (0 : ℝ)} by
      ext z
      dsimp [R, X, Y, Lower]
      rw [hball_eq]
      constructor
      · rintro ⟨hx, hdisk, hlow, hyneg⟩
        have hlow' : -K * z 0 - z 1 < 0 := sub_neg.mpr hlow
        exact ⟨⟨⟨hdisk, hx⟩, hlow'⟩, hyneg⟩
      · rintro ⟨⟨⟨hdisk, hx⟩, hlow⟩, hyneg⟩
        have hlow' : -K * z 0 < z 1 := sub_neg.mp hlow
        exact ⟨hx, hdisk, hlow', hyneg⟩]
    exact (((hBall_conv.inter hXgt).inter hLowerLt).inter hYlt)
  have hK1_pos : 0 < K + 1 := by nlinarith
  have hden_pos : 0 < 4 * (K + 1) := by positivity
  set y0 : ℝ := K * a / (4 * (K + 1))
  have hy0_pos : 0 < y0 := by
    dsimp [y0]
    positivity
  have hK_div_lt_one : K / (K + 1) < 1 := by
    rw [div_lt_one hK1_pos]
    linarith
  have hy0_eq : y0 = (a / 4) * (K / (K + 1)) := by
    dsimp [y0]
    field_simp [hK1_pos.ne']
  have hy0_lt_quarter : y0 < a / 4 := by
    rw [hy0_eq]
    have ha4 : 0 < a / 4 := by positivity
    simpa using (mul_lt_mul_of_pos_left hK_div_lt_one ha4)
  have hy0_lt_Khalf : y0 < K * (a / 2) := by
    dsimp [y0]
    rw [div_lt_iff₀ hden_pos]
    nlinarith [mul_pos hK ha]
  have hy0_sq_lt : y0 ^ 2 < (a / 4) ^ 2 := by
    have habs : |y0| < |a / 4| := by
      rw [abs_of_pos hy0_pos, abs_of_pos (by positivity : 0 < a / 4)]
      exact hy0_lt_quarter
    exact sq_lt_sq.mpr habs
  have hpoint_disk : (a / 2) ^ 2 + y0 ^ 2 < a ^ 2 := by
    nlinarith [hy0_sq_lt, sq_pos_of_pos ha]
  have hL_nonempty : L.Nonempty := by
    refine ⟨WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then a / 2 else y0), ?_⟩
    dsimp [L]
    have hx : 0 < a / 2 := by positivity
    simp [hx, hy0_pos, hy0_lt_Khalf, hpoint_disk]
  have hR_nonempty : R.Nonempty := by
    refine ⟨WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then a / 2 else -y0), ?_⟩
    dsimp [R]
    have hx : 0 < a / 2 := by positivity
    simp [hx, hy0_pos]
    exact ⟨hpoint_disk, hy0_lt_Khalf⟩
  refine ⟨hC_open, hL_open, hR_open, hL_conv.isConnected hL_nonempty,
    hR_conv.isConnected hR_nonempty, ?_, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro z hzL hzR
    dsimp [L] at hzL
    dsimp [R] at hzR
    linarith
  · dsimp [C]
    simp
  · intro z hz
    dsimp [G] at hz
    dsimp [C]
    rcases hz with ⟨hz0, hza, hz1⟩
    have hsq : z 0 ^ 2 + z 1 ^ 2 < a ^ 2 := by
      rw [hz1]
      nlinarith [hz0, hza, ha]
    have hKz : 0 < K * z 0 := mul_pos hK hz0
    exact ⟨hz0, hsq, by linarith, by linarith⟩
  · ext z
    constructor
    · intro hz
      rcases hz with ⟨hzC, hznotG⟩
      dsimp [C] at hzC
      rcases hzC with ⟨hz0, hzdisk, hzlow, hzhigh⟩
      have hza : z 0 < a := by
        have hsq0 : z 0 ^ 2 < a ^ 2 := by nlinarith [sq_nonneg (z 1)]
        have habs := sq_lt_sq.mp hsq0
        rw [abs_of_pos ha] at habs
        exact lt_of_le_of_lt (le_abs_self (z 0)) habs
      have hzne : z 1 ≠ 0 := by
        intro hz1
        exact hznotG (by dsimp [G]; exact ⟨hz0, hza, hz1⟩)
      rcases lt_or_gt_of_ne hzne with hneg | hpos
      · right
        dsimp [R]
        exact ⟨hz0, hzdisk, hzlow, hneg⟩
      · left
        dsimp [L]
        exact ⟨hz0, hzdisk, hpos, hzhigh⟩
    · intro hz
      rcases hz with hzL | hzR
      · constructor
        · dsimp [L] at hzL
          dsimp [C]
          rcases hzL with ⟨hz0, hzdisk, hzpos, hzhigh⟩
          have hlow : -K * z 0 < z 1 := by
            have hKz : 0 < K * z 0 := mul_pos hK hz0
            linarith
          exact ⟨hz0, hzdisk, hlow, hzhigh⟩
        · dsimp [G]
          intro hG
          rcases hG with ⟨_, _, hz1⟩
          dsimp [L] at hzL
          linarith
      · constructor
        · dsimp [R] at hzR
          dsimp [C]
          rcases hzR with ⟨hz0, hzdisk, hzlow, hzneg⟩
          have hhigh : z 1 < K * z 0 := by
            have hKz : 0 < K * z 0 := mul_pos hK hz0
            linarith
          exact ⟨hz0, hzdisk, hzlow, hhigh⟩
        · dsimp [G]
          intro hG
          rcases hG with ⟨_, _, hz1⟩
          dsimp [R] at hzR
          linarith
