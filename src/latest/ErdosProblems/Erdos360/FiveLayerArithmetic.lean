/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.FiberCoherence

/-!
# Sharp arithmetic for five-layer fibre coherence

These lemmas isolate the finite Presburger arithmetic needed at the strict
`12/5` threshold.  Splitting the symmetry classes into small declarations
keeps every proof within Mathlib's standard computational limits.
-/
namespace Erdos360

lemma ob_hybridT_eq_hybridG {K w : ℕ} (hw : w ≤ K) (hlow : 4*w < 3*K) :
    hybridT K w = hybridG K w := by
  simp [hybridT, hybridG, pairWeight, largestPairWeight,
    max_eq_left hw, min_eq_right hw, if_neg (by omega : ¬3*K ≤ 4*w)]
  omega

lemma ob_hybridT_eq_top {K w : ℕ} (hw : w ≤ K) (hhigh : 3*K ≤ 4*w) :
    hybridT K w = K := by
  simp [hybridT, pairWeight, largestPairWeight,
    max_eq_left hw, min_eq_right hw, if_pos hhigh]
  omega

lemma ob_low_q0 {M K x y z : ℕ} (hMK : M < K)
    (hx : x ≤ M) (hy : y ≤ M) (hz : z ≤ M) (hMlow : 4*M < 3*K) :
    let S := M+K+x+y+z
    let T := hybridT K M + K + hybridT K x + hybridT K y + hybridT K z
    14*S ≤ 40*K + 5*T := by
  dsimp only
  simp [hybridT, pairWeight, largestPairWeight,
    max_eq_left hMK.le, min_eq_right hMK.le,
    max_eq_left (hx.trans hMK.le), min_eq_right (hx.trans hMK.le),
    max_eq_left (hy.trans hMK.le), min_eq_right (hy.trans hMK.le),
    max_eq_left (hz.trans hMK.le), min_eq_right (hz.trans hMK.le),
    if_neg (by omega : ¬3*K ≤ 4*M),
    if_neg (by omega : ¬3*K ≤ 4*x), if_neg (by omega : ¬3*K ≤ 4*y),
    if_neg (by omega : ¬3*K ≤ 4*z)]
  omega

lemma ob_low_q1 {M K x y z : ℕ} (hMK : M < K)
    (hxK : x ≤ K) (hMx : M < x) (hy : y ≤ M) (hz : z ≤ M)
    (hMlow : 4*M < 3*K) :
    let S := M+K+x+y+z
    let T := hybridT K M + K + hybridT K x + hybridT K y + hybridT K z
    14*S ≤ 40*K + 5*T := by
  dsimp only
  simp [hybridT, pairWeight, largestPairWeight,
    max_eq_left hMK.le, min_eq_right hMK.le, max_eq_left hxK, min_eq_right hxK,
    max_eq_left (hy.trans hMK.le), min_eq_right (hy.trans hMK.le),
    max_eq_left (hz.trans hMK.le), min_eq_right (hz.trans hMK.le),
    if_neg (by omega : ¬3*K ≤ 4*M), if_neg (by omega : ¬3*K ≤ 4*y),
    if_neg (by omega : ¬3*K ≤ 4*z)]
  split_ifs <;> omega

lemma ob_low_q2_someLow {M K x y z : ℕ} (hMK : M < K)
    (hxK : x ≤ K) (hyK : y ≤ K) (hMx : M < x) (hMy : M < y)
    (hz : z ≤ M) (hMlow : 4*M < 3*K) (hxlow : 4*x < 3*K) :
    let S := M+K+x+y+z
    let T := hybridT K M + K + hybridT K x + hybridT K y + hybridT K z
    14*S ≤ 40*K + 5*T := by
  dsimp only
  simp [hybridT, pairWeight, largestPairWeight,
    max_eq_left hMK.le, min_eq_right hMK.le, max_eq_left hxK, min_eq_right hxK,
    max_eq_left hyK, min_eq_right hyK,
    max_eq_left (hz.trans hMK.le), min_eq_right (hz.trans hMK.le),
    if_neg (by omega : ¬3*K ≤ 4*M), if_neg (by omega : ¬3*K ≤ 4*x),
    if_neg (by omega : ¬3*K ≤ 4*z)]
  split_ifs <;> omega

lemma ob_low_q2_bothHigh {M K x y z : ℕ} (hMK : M < K)
    (hxK : x ≤ K) (hyK : y ≤ K) (hMx : M < x) (hMy : M < y)
    (hz : z ≤ M) (hMlow : 4*M < 3*K)
    (hxhigh : 3*K ≤ 4*x) (hyhigh : 3*K ≤ 4*y) :
    let S := M+K+x+y+z
    let g := hybridG K M
    let AA := g + 3*(g-K) + (2*(K+hybridA K x+hybridA K y)-K)
    let T := hybridT K M + K + hybridT K x + hybridT K y + hybridT K z
    14*S ≤ 40*K + 5*max AA T := by
  dsimp only
  simp [hybridG, hybridA, hybridT, pairWeight, largestPairWeight,
    max_eq_left hMK.le, min_eq_right hMK.le, max_eq_left hxK, min_eq_right hxK,
    max_eq_left hyK, min_eq_right hyK,
    max_eq_left (hz.trans hMK.le), min_eq_right (hz.trans hMK.le),
    if_neg (by omega : ¬3*K ≤ 4*M), if_pos hxhigh, if_pos hyhigh,
    if_neg (by omega : ¬3*K ≤ 4*z)]
  omega

lemma ob_low_q3_someLow {M K x y z : ℕ} (hMK : M < K)
    (hxK : x ≤ K) (hyK : y ≤ K) (hzK : z ≤ K)
    (hMx : M < x) (hMy : M < y) (hMz : M < z) (hMlow : 4*M < 3*K)
    (hxlow : 4*x < 3*K) (hylow : 4*y < 3*K) :
    let S := M+K+x+y+z
    let T := hybridT K M + K + hybridT K x + hybridT K y + hybridT K z
    14*S ≤ 40*K + 5*T := by
  dsimp only
  simp [hybridT, pairWeight, largestPairWeight,
    max_eq_left hMK.le, min_eq_right hMK.le, max_eq_left hxK, min_eq_right hxK,
    max_eq_left hyK, min_eq_right hyK, max_eq_left hzK, min_eq_right hzK,
    if_neg (by omega : ¬3*K ≤ 4*M), if_neg (by omega : ¬3*K ≤ 4*x),
    if_neg (by omega : ¬3*K ≤ 4*y)]
  split_ifs <;> omega

lemma ob_low_q3_twoHigh {M K x y z : ℕ} (hMK : M < K)
    (hxK : x ≤ K) (hyK : y ≤ K) (hzK : z ≤ K)
    (hMx : M < x) (hMy : M < y) (hMz : M < z) (hMlow : 4*M < 3*K)
    (hxhigh : 3*K ≤ 4*x) (hyhigh : 3*K ≤ 4*y) (hzlow : 4*z < 3*K) :
    let S := M+K+x+y+z
    let g := hybridG K M
    let AA := g+3*(g-K)+(2*(K+hybridA K x+hybridA K y+hybridA K z)-K)
    let T := hybridT K M+K+hybridT K x+hybridT K y+hybridT K z
    14*S ≤ 40*K+5*max AA T := by
  dsimp only
  let gm := hybridG K M
  let gz := hybridG K z
  let ax := hybridA K x
  let ay := hybridA K y
  let az := hybridA K z
  have hgm : 4*M ≤ 2*K+gm := by simp [gm, hybridG]; omega
  have hgmlt : gm < K := by simp [gm, hybridG]; omega
  have hgz : 4*z ≤ 2*K+gz := by simp [gz, hybridG]; omega
  have hax : 3*x ≤ 2*K+ax := by simp [ax, hybridA]; omega
  have hay : 3*y ≤ 2*K+ay := by simp [ay, hybridA]; omega
  have haz : 3*z ≤ 2*K+az := by simp [az, hybridA]; omega
  have havg : 28*(M+K+x+y+z) ≤
      80*K + 5*((gm+K+2*(ax+ay+az)) + (gm+3*K+gz)) := by
    by_cases htriv : 14*(M+K+x+y+z) ≤ 40*K
    · omega
    · omega
  have hsum : (gm+K+2*(ax+ay+az)) + (gm+3*K+gz) ≤
      2*max (gm+K+2*(ax+ay+az)) (gm+3*K+gz) :=
    calc
      _ ≤ max (gm+K+2*(ax+ay+az)) (gm+3*K+gz) +
          max (gm+K+2*(ax+ay+az)) (gm+3*K+gz) :=
        add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = _ := by ring
  have hAA : hybridG K M+3*(hybridG K M-K)+
      (2*(K+hybridA K x+hybridA K y+hybridA K z)-K) =
      gm+K+2*(ax+ay+az) := by simp [gm, ax, ay, az]; omega
  have hT : hybridT K M+K+hybridT K x+hybridT K y+hybridT K z =
      gm+3*K+gz := by
    rw [ob_hybridT_eq_hybridG hMK.le hMlow,
      ob_hybridT_eq_top hxK hxhigh, ob_hybridT_eq_top hyK hyhigh,
      ob_hybridT_eq_hybridG hzK hzlow]
    simp [gm, gz]
    omega
  rw [hAA, hT]
  omega

lemma ob_low_q3_allHigh {M K x y z : ℕ} (hMK : M < K)
    (hxK : x ≤ K) (hyK : y ≤ K) (hzK : z ≤ K)
    (hMx : M < x) (hMy : M < y) (hMz : M < z) (hMlow : 4*M < 3*K)
    (hxhigh : 3*K ≤ 4*x) (hyhigh : 3*K ≤ 4*y) (hzhigh : 3*K ≤ 4*z) :
    let S := M+K+x+y+z
    let g := hybridG K M
    let AA := g+3*(g-K)+(2*(K+hybridA K x+hybridA K y+hybridA K z)-K)
    14*S ≤ 40*K+5*AA := by
  dsimp only
  simp only [hybridG, hybridA]
  omega

lemma ob_high_q0 {M K x y z : ℕ} (hMK : M < K)
    (hx : x ≤ M) (hy : y ≤ M) (hz : z ≤ M) (hMhigh : 3*K ≤ 4*M) :
    let S := M+K+x+y+z
    let C := 4*hybridG K M
    14*S ≤ 40*K+5*C := by
  dsimp only
  simp only [hybridG]
  omega

lemma ob_high_q1 {M K x y z : ℕ} (hMK : M < K)
    (hxK : x ≤ K) (hMx : M < x) (hy : y ≤ M) (hz : z ≤ M)
    (hMhigh : 3*K ≤ 4*M) :
    let S := M+K+x+y+z
    let C := 4*hybridG K M
    14*S ≤ 40*K+5*C := by
  dsimp only
  simp only [hybridG]
  omega

lemma ob_high_q2 {M K x y z : ℕ} (hMK : M < K)
    (hxK : x ≤ K) (hyK : y ≤ K) (hMx : M < x) (hMy : M < y)
    (hz : z ≤ M) (hMhigh : 3*K ≤ 4*M) :
    let S := M+K+x+y+z
    let g := hybridG K M
    let AA := g+3*(g-K)+(2*(K+hybridA K x+hybridA K y)-K)
    let T := hybridT K M+K+hybridT K x+hybridT K y+hybridT K z
    14*S ≤ 40*K+5*max AA T := by
  dsimp only
  let tz := hybridT K z
  have htz : 3*z ≤ 2*K+tz := by
    exact three_mul_le_two_mul_add_hybridT (hz.trans hMK.le)
  have hAA : 16*M+6*x+6*y ≤
      (hybridG K M+3*(hybridG K M-K)+
        (2*(K+hybridA K x+hybridA K y)-K))+18*K := by
    simp only [hybridG, hybridA]
    omega
  have hT : hybridT K M+K+hybridT K x+hybridT K y+hybridT K z =
      4*K+tz := by
    simp [tz, hybridT, pairWeight, largestPairWeight,
      max_eq_left hMK.le, min_eq_right hMK.le,
      max_eq_left hxK, min_eq_right hxK,
      max_eq_left hyK, min_eq_right hyK,
      if_pos hMhigh, if_pos (by omega : 3*K ≤ 4*x),
      if_pos (by omega : 3*K ≤ 4*y)]
    omega
  have havg : 28*(M+K+x+y+z) ≤ 80*K +
      5*((hybridG K M+3*(hybridG K M-K)+
        (2*(K+hybridA K x+hybridA K y)-K))+(4*K+tz)) := by omega
  have hsum := add_le_add
    (le_max_left
      (hybridG K M+3*(hybridG K M-K)+
        (2*(K+hybridA K x+hybridA K y)-K)) (4*K+tz))
    (le_max_right
      (hybridG K M+3*(hybridG K M-K)+
        (2*(K+hybridA K x+hybridA K y)-K)) (4*K+tz))
  rw [hT]
  omega

lemma ob_high_q3 {M K x y z : ℕ} (hMK : M < K)
    (hxK : x ≤ K) (hyK : y ≤ K) (hzK : z ≤ K)
    (hMx : M < x) (hMy : M < y) (hMz : M < z) (hMhigh : 3*K ≤ 4*M) :
    let S := M+K+x+y+z
    let g := hybridG K M
    let AA := g+3*(g-K)+(2*(K+hybridA K x+hybridA K y+hybridA K z)-K)
    14*S ≤ 40*K+5*AA := by
  dsimp only
  simp only [hybridG, hybridA]
  omega

/-! The remaining cases, according to how many of the three non-base,
non-top fibres lie in the distinguished subgroup coset. -/

lemma five_hybrid_three_good {M K x y z : ℕ}
    (hMK : M < K) (hxK : x ≤ K) (hyK : y ≤ K) (hzK : z ≤ K)
    (hxM : x ≤ M) (hyM : y ≤ M) (hzM : z ≤ M) :
    let S := M + K + x + y + z
    let G := hybridG K M + hybridG K x + hybridG K y + hybridG K z
    let T := hybridT K M + hybridT K K + hybridT K x +
      hybridT K y + hybridT K z
    24 * S ≤ 5 * (2 * (S + 4 * K) + max G (max (G + K) T)) := by
  dsimp only
  simp [hybridG, hybridT, pairWeight, largestPairWeight,
    max_eq_left hMK.le, min_eq_right hMK.le,
    max_eq_left hxK, min_eq_right hxK,
    max_eq_left hyK, min_eq_right hyK,
    max_eq_left hzK, min_eq_right hzK]
  split_ifs <;> omega

lemma five_hybrid_two_good {M K x y z : ℕ}
    (hMK : M < K) (hxK : x ≤ K) (hyK : y ≤ K) (hzK : z ≤ K)
    (hxM : x ≤ M) (hyM : y ≤ M) :
    let S := M + K + x + y + z
    let G := hybridG K M + hybridG K x + hybridG K y
    let AH := K + if M < z then hybridA K z else 0
    24 * S ≤ 5 * (2 * (S + 4 * K) +
      max (G + hybridG K M)
        (G + (hybridG K M - K) + (2 * AH - K))) := by
  dsimp only
  simp [hybridG, hybridA]
  split_ifs <;> omega

lemma five_hybrid_one_good_none_above {M K x y z : ℕ}
    (hMK : M < K) (hxK : x ≤ K) (hyK : y ≤ K) (hzK : z ≤ K)
    (hxM : x ≤ M) (hyM : y ≤ M) (hzM : z ≤ M) :
    let S := M + K + x + y + z
    let G := hybridG K M + hybridG K x
    let T := hybridT K M + hybridT K K + hybridT K x +
      hybridT K y + hybridT K z
    24 * S ≤ 5 * (2 * (S + 4 * K) +
      max (G + 2 * (hybridG K M - K) + K) T) := by
  dsimp only
  simp [hybridG, hybridT, pairWeight, largestPairWeight,
    max_eq_left hMK.le, min_eq_right hMK.le,
    max_eq_left hxK, min_eq_right hxK,
    max_eq_left hyK, min_eq_right hyK,
    max_eq_left hzK, min_eq_right hzK]
  split_ifs <;> omega

lemma five_hybrid_one_good_one_above {M K x y z : ℕ}
    (hMK : M < K) (hxK : x ≤ K) (hyK : y ≤ K) (hzK : z ≤ K)
    (hxM : x ≤ M) (hMy : M < y) (hzM : z ≤ M) :
    let S := M + K + x + y + z
    let G := hybridG K M + hybridG K x
    let AH := K + hybridA K y
    let T := hybridT K M + hybridT K K + hybridT K x +
      hybridT K y + hybridT K z
    24 * S ≤ 5 * (2 * (S + 4 * K) +
      max (G + 2 * (hybridG K M - K) + (2 * AH - K)) T) := by
  dsimp only
  simp [hybridG, hybridA, hybridT, pairWeight, largestPairWeight,
    max_eq_left hMK.le, min_eq_right hMK.le,
    max_eq_left hxK, min_eq_right hxK,
    max_eq_left hyK, min_eq_right hyK,
    max_eq_left hzK, min_eq_right hzK]
  split_ifs <;> omega

lemma five_hybrid_one_good_two_above_high {M K x y z : ℕ}
    (hMK : M < K) (hxK : x ≤ K) (hyK : y ≤ K) (hzK : z ≤ K)
    (hxM : x ≤ M) (hMy : M < y) (hMz : M < z)
    (hyHigh : 3 * K ≤ 4 * y) (hzHigh : 3 * K ≤ 4 * z) :
    let S := M + K + x + y + z
    let G := hybridG K M + hybridG K x
    let AH := K + hybridA K y + hybridA K z
    24 * S ≤ 5 * (2 * (S + 4 * K) +
      (G + 2 * (hybridG K M - K) + (2 * AH - K))) := by
  dsimp only
  simp only [hybridG, hybridA]
  omega

lemma five_hybrid_one_good_two_above_low {M K x y z : ℕ}
    (hMK : M < K) (hxK : x ≤ K) (hyK : y ≤ K) (hzK : z ≤ K)
    (hxM : x ≤ M) (hMy : M < y) (hMz : M < z)
    (hyLow : 4 * y < 3 * K) :
    let S := M + K + x + y + z
    let T := hybridT K M + hybridT K K + hybridT K x +
      hybridT K y + hybridT K z
    24 * S ≤ 5 * (2 * (S + 4 * K) + T) := by
  dsimp only
  simp [hybridT, pairWeight, largestPairWeight,
    max_eq_left hMK.le, min_eq_right hMK.le,
    max_eq_left hxK, min_eq_right hxK,
    max_eq_left hyK, min_eq_right hyK,
    max_eq_left hzK, min_eq_right hzK,
    if_neg (by omega : ¬3 * K ≤ 4 * y)]
  split_ifs <;> omega

/-! Symmetry-packaged numerical statements used by the finite-set lemma. -/

lemma five_hybrid_one_good {M K x y z : ℕ}
    (hMK : M < K) (hxK : x ≤ K) (hyK : y ≤ K) (hzK : z ≤ K)
    (hxM : x ≤ M) :
    let S := M + K + x + y + z
    let G := hybridG K M + hybridG K x
    let AH := K + (if M < y then hybridA K y else 0) +
      (if M < z then hybridA K z else 0)
    let T := hybridT K M + hybridT K K + hybridT K x +
      hybridT K y + hybridT K z
    let C := G + 2 * hybridG K M
    let AA := G + 2 * (hybridG K M - K) + (2 * AH - K)
    24 * S ≤ 5 * (2 * (S + 4 * K) + max C (max AA T)) := by
  dsimp only
  by_cases hMy : M < y
  · by_cases hMz : M < z
    · by_cases hyHigh : 3*K ≤ 4*y
      · by_cases hzHigh : 3*K ≤ 4*z
        · have h := five_hybrid_one_good_two_above_high hMK hxK hyK hzK
            hxM hMy hMz hyHigh hzHigh
          simp [hMy, hMz] at h ⊢
          omega
        · have hzLow : 4*z < 3*K := by omega
          have h := five_hybrid_one_good_two_above_low hMK hxK hzK hyK
            hxM hMz hMy hzLow
          simp [hMy, hMz, add_comm, add_left_comm, add_assoc] at h ⊢
          omega
      · have hyLow : 4*y < 3*K := by omega
        have h := five_hybrid_one_good_two_above_low hMK hxK hyK hzK
          hxM hMy hMz hyLow
        simp [hMy, hMz] at h ⊢
        omega
    · have hzM : z ≤ M := by omega
      have h := five_hybrid_one_good_one_above hMK hxK hyK hzK hxM hMy hzM
      simp [hMy, hMz] at h ⊢
      omega
  · have hyM : y ≤ M := by omega
    by_cases hMz : M < z
    · have h := five_hybrid_one_good_one_above hMK hxK hzK hyK hxM hMz hyM
      simp [hMy, hMz, add_comm, add_left_comm, add_assoc] at h ⊢
      omega
    · have hzM : z ≤ M := by omega
      have h := five_hybrid_one_good_none_above hMK hxK hyK hzK hxM hyM hzM
      simp [hMy, hMz] at h ⊢
      omega

def fiveHybridOnlyBaseGoal (M K x y z : ℕ) : Prop :=
  let S := M + K + x + y + z
  let g := hybridG K M
  let AH := K + (if M < x then hybridA K x else 0) +
    (if M < y then hybridA K y else 0) +
    (if M < z then hybridA K z else 0)
  let T := hybridT K M + K + hybridT K x + hybridT K y + hybridT K z
  let C := 4 * g
  let AA := g + 3 * (g - K) + (2 * AH - K)
  24 * S ≤ 5 * (2 * (S + 4 * K) + max C (max AA T))

lemma five_hybrid_only_base_high {M K x y z : ℕ}
    (hMK : M < K) (hxK : x ≤ K) (hyK : y ≤ K) (hzK : z ≤ K)
    (hMhigh : 3*K ≤ 4*M) : fiveHybridOnlyBaseGoal M K x y z := by
  dsimp [fiveHybridOnlyBaseGoal]
  by_cases hMx : M < x
  · by_cases hMy : M < y
    · by_cases hMz : M < z
      · have h := ob_high_q3 hMK hxK hyK hzK hMx hMy hMz hMhigh
        simp [hMx, hMy, hMz] at h ⊢
        omega
      · have hzM : z ≤ M := by omega
        have h := ob_high_q2 hMK hxK hyK hMx hMy hzM hMhigh
        simp [hMx, hMy, hMz] at h ⊢
        omega
    · have hyM : y ≤ M := by omega
      by_cases hMz : M < z
      · have h := ob_high_q2 hMK hxK hzK hMx hMz hyM hMhigh
        simp [hMx, hMy, hMz, add_comm, add_left_comm, add_assoc] at h ⊢
        omega
      · have hzM : z ≤ M := by omega
        have h := ob_high_q1 hMK hxK hMx hyM hzM hMhigh
        simp [hMx, hMy, hMz] at h ⊢
        omega
  · have hxM : x ≤ M := by omega
    by_cases hMy : M < y
    · by_cases hMz : M < z
      · have h := ob_high_q2 hMK hyK hzK hMy hMz hxM hMhigh
        simp [hMx, hMy, hMz, add_comm, add_left_comm, add_assoc] at h ⊢
        omega
      · have hzM : z ≤ M := by omega
        have h := ob_high_q1 hMK hyK hMy hxM hzM hMhigh
        simp [hMx, hMy, hMz, add_comm, add_left_comm, add_assoc] at h ⊢
        omega
    · have hyM : y ≤ M := by omega
      by_cases hMz : M < z
      · have h := ob_high_q1 hMK hzK hMz hxM hyM hMhigh
        simp [hMx, hMy, hMz, add_comm, add_left_comm, add_assoc] at h ⊢
        omega
      · have hzM : z ≤ M := by omega
        have h := ob_high_q0 hMK hxM hyM hzM hMhigh
        simp [hMx, hMy, hMz] at h ⊢
        omega

lemma five_hybrid_only_base_low_all_above {M K x y z : ℕ}
    (hMK : M < K) (hxK : x ≤ K) (hyK : y ≤ K) (hzK : z ≤ K)
    (hMlow : 4*M < 3*K) (hMx : M < x) (hMy : M < y) (hMz : M < z) :
    fiveHybridOnlyBaseGoal M K x y z := by
  dsimp [fiveHybridOnlyBaseGoal]
  by_cases hxHigh : 3*K ≤ 4*x
  · by_cases hyHigh : 3*K ≤ 4*y
    · by_cases hzHigh : 3*K ≤ 4*z
      · have h := ob_low_q3_allHigh hMK hxK hyK hzK hMx hMy hMz
          hMlow hxHigh hyHigh hzHigh
        simp [hMx, hMy, hMz] at h ⊢
        omega
      · have hzLow : 4*z < 3*K := by omega
        have h := ob_low_q3_twoHigh hMK hxK hyK hzK hMx hMy hMz
          hMlow hxHigh hyHigh hzLow
        simp [hMx, hMy, hMz] at h ⊢
        omega
    · have hyLow : 4*y < 3*K := by omega
      by_cases hzHigh : 3*K ≤ 4*z
      · have h := ob_low_q3_twoHigh hMK hxK hzK hyK hMx hMz hMy
          hMlow hxHigh hzHigh hyLow
        simp [hMx, hMy, hMz, add_comm, add_left_comm, add_assoc] at h ⊢
        omega
      · have hzLow : 4*z < 3*K := by omega
        have h := ob_low_q3_someLow hMK hyK hzK hxK hMy hMz hMx
          hMlow hyLow hzLow
        simp [hMx, hMy, hMz, add_comm, add_left_comm, add_assoc] at h ⊢
        omega
  · have hxLow : 4*x < 3*K := by omega
    by_cases hyHigh : 3*K ≤ 4*y
    · by_cases hzHigh : 3*K ≤ 4*z
      · have h := ob_low_q3_twoHigh hMK hyK hzK hxK hMy hMz hMx
          hMlow hyHigh hzHigh hxLow
        simp [hMx, hMy, hMz, add_comm, add_left_comm, add_assoc] at h ⊢
        omega
      · have hzLow : 4*z < 3*K := by omega
        have h := ob_low_q3_someLow hMK hxK hzK hyK hMx hMz hMy
          hMlow hxLow hzLow
        simp [hMx, hMy, hMz, add_comm, add_left_comm, add_assoc] at h ⊢
        omega
    · have hyLow : 4*y < 3*K := by omega
      have h := ob_low_q3_someLow hMK hxK hyK hzK hMx hMy hMz
        hMlow hxLow hyLow
      simp [hMx, hMy, hMz] at h ⊢
      omega

lemma five_hybrid_only_base_low_two_above {M K x y z : ℕ}
    (hMK : M < K) (hxK : x ≤ K) (hyK : y ≤ K) (hzK : z ≤ K)
    (hMlow : 4*M < 3*K) (hMx : M < x) (hMy : M < y) (hzM : z ≤ M) :
    fiveHybridOnlyBaseGoal M K x y z := by
  dsimp [fiveHybridOnlyBaseGoal]
  have hMz : ¬ M < z := by omega
  by_cases hxHigh : 3*K ≤ 4*x
  · by_cases hyHigh : 3*K ≤ 4*y
    · have h := ob_low_q2_bothHigh hMK hxK hyK hMx hMy hzM hMlow hxHigh hyHigh
      simp [hMx, hMy, hMz] at h ⊢
      omega
    · have hyLow : 4*y < 3*K := by omega
      have h := ob_low_q2_someLow hMK hyK hxK hMy hMx hzM hMlow hyLow
      simp [hMx, hMy, hMz, add_comm, add_left_comm, add_assoc] at h ⊢
      omega
  · have hxLow : 4*x < 3*K := by omega
    have h := ob_low_q2_someLow hMK hxK hyK hMx hMy hzM hMlow hxLow
    simp [hMx, hMy, hMz] at h ⊢
    omega

lemma five_hybrid_only_base_low_one_above {M K x y z : ℕ}
    (hMK : M < K) (hxK : x ≤ K) (hyM : y ≤ M) (hzM : z ≤ M)
    (hMlow : 4*M < 3*K) (hMx : M < x) :
    fiveHybridOnlyBaseGoal M K x y z := by
  dsimp [fiveHybridOnlyBaseGoal]
  have hMy : ¬ M < y := by omega
  have hMz : ¬ M < z := by omega
  have h := ob_low_q1 hMK hxK hMx hyM hzM hMlow
  simp [hMx, hMy, hMz] at h ⊢
  omega

lemma five_hybrid_only_base_low_none_above {M K x y z : ℕ}
    (hMK : M < K) (hxM : x ≤ M) (hyM : y ≤ M) (hzM : z ≤ M)
    (hMlow : 4*M < 3*K) : fiveHybridOnlyBaseGoal M K x y z := by
  dsimp [fiveHybridOnlyBaseGoal]
  have hMx : ¬ M < x := by omega
  have hMy : ¬ M < y := by omega
  have hMz : ¬ M < z := by omega
  have h := ob_low_q0 hMK hxM hyM hzM hMlow
  simp [hMx, hMy, hMz] at h ⊢
  omega

lemma five_hybrid_only_base {M K x y z : ℕ}
    (hMK : M < K) (hxK : x ≤ K) (hyK : y ≤ K) (hzK : z ≤ K) :
    fiveHybridOnlyBaseGoal M K x y z := by
  by_cases hMhigh : 3*K ≤ 4*M
  · exact five_hybrid_only_base_high hMK hxK hyK hzK hMhigh
  · have hMlow : 4*M < 3*K := by omega
    by_cases hMx : M < x
    · by_cases hMy : M < y
      · by_cases hMz : M < z
        · exact five_hybrid_only_base_low_all_above hMK hxK hyK hzK
            hMlow hMx hMy hMz
        · have hzM : z ≤ M := by omega
          exact five_hybrid_only_base_low_two_above hMK hxK hyK hzK
            hMlow hMx hMy hzM
      · have hyM : y ≤ M := by omega
        by_cases hMz : M < z
        · have h := five_hybrid_only_base_low_two_above hMK hxK hzK hyK
              hMlow hMx hMz hyM
          simpa [fiveHybridOnlyBaseGoal, add_comm, add_left_comm, add_assoc] using h
        · have hzM : z ≤ M := by omega
          exact five_hybrid_only_base_low_one_above hMK hxK hyM hzM hMlow hMx
    · have hxM : x ≤ M := by omega
      by_cases hMy : M < y
      · by_cases hMz : M < z
        · have h := five_hybrid_only_base_low_two_above hMK hyK hzK hxK
              hMlow hMy hMz hxM
          simpa [fiveHybridOnlyBaseGoal, add_comm, add_left_comm, add_assoc] using h
        · have hzM : z ≤ M := by omega
          have h := five_hybrid_only_base_low_one_above hMK hyK hxM hzM hMlow hMy
          simpa [fiveHybridOnlyBaseGoal, add_comm, add_left_comm, add_assoc] using h
      · have hyM : y ≤ M := by omega
        by_cases hMz : M < z
        · have h := five_hybrid_only_base_low_one_above hMK hzK hxM hyM hMlow hMz
          simpa [fiveHybridOnlyBaseGoal, add_comm, add_left_comm, add_assoc] using h
        · have hzM : z ≤ M := by omega
          exact five_hybrid_only_base_low_none_above hMK hxM hyM hzM hMlow

end Erdos360
