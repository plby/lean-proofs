import Arxiv.Arxiv2411_18291.RootedCliqueBounds
import Arxiv.Arxiv2411_18291.TypicalCliqueCount

/-!
# Precise rooted clique counts from typicality

Use a small adjustable error at every extension step, retaining both sides
of the count. The final relative error is explicit and tends to zero with
the typicality error and the collision correction.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {r q k a h : ℕ}

theorem IsTypical.cliqueNextVertices_upper {G : Hypergraph V (r + 1)} {c : ℝ}
    (hT : IsTypical G c h) (U : Block V k) (hkh : k.choose r ≤ h) :
    ((cliqueNextVertices G U).card : ℝ) ≤ (1 + c) * (Fintype.card V * density G ^ k.choose r) := by
  have ht := hT (cliqueEdges r U) (by simpa only [card_cliqueEdges] using hkh)
  rw [card_cliqueEdges] at ht
  have hc : ((cliqueNextVertices G U).card : ℝ) ≤
      (commonNeighbors G (cliqueEdges r U)).card := by
    exact_mod_cast card_le_card
      (sdiff_subset (s := commonNeighbors G (cliqueEdges r U)) (t := U.val))
  have hu := (abs_le.mp ht).2
  nlinarith

theorem IsTypical.cliqueNextVertices_relative_lower {G : Hypergraph V (r + 1)} {c η : ℝ}
    (hT : IsTypical G c h) (hqh : q.choose (r + 1) ≤ h) (hcη : c ≤ η)
    (hsize : (q : ℝ) ≤ (η - c) * (Fintype.card V * density G ^ q.choose (r + 1)))
    (hk : k < q) (U : Block V k) :
    (1 - η) * (Fintype.card V * density G ^ k.choose r) ≤
      ((cliqueNextVertices G U).card : ℝ) := by
  have hchoose := choose_face_le_clique r hk
  have hpow : density G ^ q.choose (r + 1) ≤ density G ^ k.choose r :=
    pow_le_pow_of_le_one (density_nonneg G) (density_le_one G) hchoose
  have hkbound : (k : ℝ) ≤ (η - c) * (Fintype.card V * density G ^ k.choose r) := by
    calc
      (k : ℝ) ≤ q := by exact_mod_cast hk.le
      _ ≤ _ := hsize
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)) (sub_nonneg.mpr hcη)
  have hl := hT.cliqueNextVertices_lower U (hchoose.trans hqh)
  nlinarith

theorem IsTypical.rootedCliques_factorial_bounds {G : Hypergraph V (r + 1)} {c η : ℝ}
    (hT : IsTypical G c h) (hqh : q.choose (r + 1) ≤ h) (hcη : c ≤ η)
    (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hsize : (q : ℝ) ≤ (η - c) * (Fintype.card V * density G ^ q.choose (r + 1)))
    (I : Block V a) (t : ℕ) (ht : a + t ≤ q) :
    (1 - η) ^ t * ((Fintype.card V : ℝ) ^ t *
      density G ^ ((a + t).choose (r + 1) - a.choose (r + 1))) ≤
        (t.factorial : ℝ) * (rootedCliques G I (a + t)).card ∧
    (t.factorial : ℝ) * (rootedCliques G I (a + t)).card ≤
      (1 + η) ^ t * ((Fintype.card V : ℝ) ^ t *
        density G ^ ((a + t).choose (r + 1) - a.choose (r + 1))) := by
  have hd := density_nonneg G
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  constructor
  · have hl := rootedCliques_factorial_lower G I q
      (mul_nonneg (sub_nonneg.mpr hη1) hn) hd (by
        intro k _ hk U _
        simpa only [mul_assoc] using hT.cliqueNextVertices_relative_lower hqh hcη hsize hk U)
      t ht
    simpa only [mul_pow, mul_assoc] using hl
  · have hu := rootedCliques_factorial_upper G I q
      (mul_nonneg (show 0 ≤ 1 + η by linarith) hn) hd (by
        intro k _ hk U _
        have hnext := hT.cliqueNextVertices_upper U ((choose_face_le_clique r hk).trans hqh)
        calc
          _ ≤ (1 + c) * (Fintype.card V * density G ^ k.choose r) := hnext
          _ ≤ (1 + η) * (Fintype.card V * density G ^ k.choose r) :=
            mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hn (pow_nonneg hd _))
          _ = _ := (mul_assoc _ _ _).symm)
      t ht
    simpa only [mul_pow, mul_assoc] using hu

theorem IsTypical.rootedCliques_relative_error {G : Hypergraph V (r + 1)} {c η : ℝ}
    (hT : IsTypical G c h) (hqh : q.choose (r + 1) ≤ h) (hcη : c ≤ η)
    (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hsize : (q : ℝ) ≤ (η - c) * (Fintype.card V * density G ^ q.choose (r + 1)))
    (I : Block V a) (t : ℕ) (ht : a + t ≤ q) :
    |(t.factorial : ℝ) * (rootedCliques G I (a + t)).card -
      (Fintype.card V : ℝ) ^ t * density G ^ ((a + t).choose (r + 1) - a.choose (r + 1))| ≤
      (η * q * 2 ^ q) * ((Fintype.card V : ℝ) ^ t *
        density G ^ ((a + t).choose (r + 1) - a.choose (r + 1))) := by
  have htq : t ≤ q := by omega
  have habminus : |(1 - η) - (1 : ℝ)| ≤ η := by
    rw [show (1 - η) - (1 : ℝ) = -η by ring, abs_neg, abs_of_nonneg hη]
  have habplus : |(1 + η) - (1 : ℝ)| ≤ η := by
    rw [show (1 + η) - (1 : ℝ) = η by ring, abs_of_nonneg hη]
  have hpminus : |(1 - η) ^ t - 1| ≤ η * q * 2 ^ q := by
    simpa only [one_pow, mul_one] using relative_pow_error (sub_nonneg.mpr hη1)
      (by norm_num : (0 : ℝ) ≤ 1) hη hη1 (by simpa only [mul_one] using habminus) htq
  have hpplus : |(1 + η) ^ t - 1| ≤ η * q * 2 ^ q := by
    simpa only [one_pow, mul_one] using relative_pow_error (show 0 ≤ 1 + η by linarith)
      (by norm_num : (0 : ℝ) ≤ 1) hη hη1 (by simpa only [mul_one] using habplus) htq
  obtain ⟨hlo, hup⟩ := hT.rootedCliques_factorial_bounds hqh hcη hη hη1 hsize I t ht
  have hmain : 0 ≤ (Fintype.card V : ℝ) ^ t *
      density G ^ ((a + t).choose (r + 1) - a.choose (r + 1)) :=
    mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (density_nonneg G) _)
  apply abs_le.mpr
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right (abs_le.mp hpminus).1 hmain]
  · nlinarith [mul_le_mul_of_nonneg_right (abs_le.mp hpplus).2 hmain]

end Arxiv2411_18291
