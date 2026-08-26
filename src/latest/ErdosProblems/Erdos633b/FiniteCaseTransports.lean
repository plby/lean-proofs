import ErdosProblems.Erdos633b.FiniteGeometricCertificates
import ErdosProblems.Erdos633b.FiniteOuterExhaustion
import ErdosProblems.Erdos633b.GroupTwoSecondOrder24
import ErdosProblems.Erdos633b.GroupTwoThirdOrder8
import ErdosProblems.Erdos633b.GroupTwoFirstOrder30
import ErdosProblems.Erdos633b.GroupTwoSecondOrder30
import ErdosProblems.Erdos633b.GroupTwoSecondOrder15
import ErdosProblems.Erdos633b.Boundary30DoubleExclusion
import ErdosProblems.Erdos633b.GroupTwoFirstOrder15
import ErdosProblems.Erdos633b.Boundary48Exclusion
import ErdosProblems.Erdos633b.GroupTwoFirstOrder20One
import ErdosProblems.Erdos633b.GroupTwoThirdOrder20One

/-! Actual geometric relabelings of existing finite boundary/area exclusions. -/

namespace Erdos633b

theorem Triangle.angle_weights_after_reindex (S : Triangle) (e : Equiv.Perm (Fin 3))
    (N : ℕ) (w v : Fin 3 → ℕ)
    (hw : ∀ i, S.angle i = (w i : ℝ) * (Real.pi / N))
    (he : ∀ i, w (e.symm i) = v i) :
    ∀ i, Triangle.angle (S.reindex e) i = (v i : ℝ) * (Real.pi / N) := by
  intro i
  rw [Triangle.angle_reindex, hw, he]

namespace Tiling

theorem finite_pair_01_impossible {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hw : ∀ i, d.tile.angle i = (angleTableWeights (12, 1, 3) i : ℝ) * (Real.pi / 12))
    (ha : ∀ i, T.angle i = (angleTableWeights (12, 1, 5) i : ℝ) * (Real.pi / 12)) : False := by
  let e : Equiv.Perm (Fin 3) := Equiv.refl _
  let f : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  let d' : Tiling (T.reindex f) n := (d.reindexTile e).reindexOuter f
  apply d'.groupTwo_finite_24_1_2_impossible
  · exact d.tile.angle_weights_after_reindex e 12 (angleTableWeights (12, 1, 3))
      FiniteSecondOrder24.tileWeights hw (by intro i; fin_cases i <;> decide)
  · exact T.angle_weights_after_reindex f 12 (angleTableWeights (12, 1, 5))
      FiniteSecondOrder24.outerWeights ha (by intro i; fin_cases i <;> decide)

theorem finite_pair_02_impossible {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hw : ∀ i, d.tile.angle i = (angleTableWeights (12, 1, 3) i : ℝ) * (Real.pi / 12))
    (ha : ∀ i, T.angle i = (angleTableWeights (12, 3, 4) i : ℝ) * (Real.pi / 12)) : False := by
  let e : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let f : Equiv.Perm (Fin 3) := Equiv.refl _
  let d' : Tiling (T.reindex f) n := (d.reindexTile e).reindexOuter f
  apply d'.groupTwo_finite_8_1_3_impossible
  · exact d.tile.angle_weights_after_reindex e 12 (angleTableWeights (12, 1, 3))
      FiniteThirdOrder8.tileWeights hw (by intro i; fin_cases i <;> decide)
  · exact T.angle_weights_after_reindex f 12 (angleTableWeights (12, 3, 4))
      FiniteThirdOrder8.outerWeights ha (by intro i; fin_cases i <;> decide)

theorem finite_pair_07_impossible {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hw : ∀ i, d.tile.angle i = (angleTableWeights (14, 1, 5) i : ℝ) * (Real.pi / 14))
    (ha : ∀ i, T.angle i = (angleTableWeights (14, 2, 5) i : ℝ) * (Real.pi / 14)) : False := by
  let e : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let f : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let d' : Tiling (T.reindex f) n := (d.reindexTile e).reindexOuter f
  apply d'.finite_area_14_impossible
  · exact d.tile.angle_weights_after_reindex e 14 (angleTableWeights (14, 1, 5))
      FiniteArea14.tileWeights hw (by intro i; fin_cases i <;> decide)
  · exact T.angle_weights_after_reindex f 14 (angleTableWeights (14, 2, 5))
      FiniteArea14.outerWeights ha (by intro i; fin_cases i <;> decide)

theorem finite_pair_08_impossible {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hw : ∀ i, d.tile.angle i = (angleTableWeights (15, 1, 4) i : ℝ) * (Real.pi / 15))
    (ha : ∀ i, T.angle i = (angleTableWeights (15, 1, 2) i : ℝ) * (Real.pi / 15)) : False := by
  let e : Equiv.Perm (Fin 3) := Equiv.refl _
  let f : Equiv.Perm (Fin 3) := Equiv.refl _
  let d' : Tiling (T.reindex f) n := (d.reindexTile e).reindexOuter f
  apply d'.groupTwo_finite_30_1_1_impossible
  · exact d.tile.angle_weights_after_reindex e 15 (angleTableWeights (15, 1, 4))
      FiniteFirstOrder30.tileWeights hw (by intro i; fin_cases i <;> decide)
  · exact T.angle_weights_after_reindex f 15 (angleTableWeights (15, 1, 2))
      FiniteFirstOrder30.outerWeights ha (by intro i; fin_cases i <;> decide)

theorem finite_pair_09_impossible {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hw : ∀ i, d.tile.angle i = (angleTableWeights (15, 1, 4) i : ℝ) * (Real.pi / 15))
    (ha : ∀ i, T.angle i = (angleTableWeights (15, 1, 6) i : ℝ) * (Real.pi / 15)) : False := by
  let e : Equiv.Perm (Fin 3) := Equiv.refl _
  let f : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  let d' : Tiling (T.reindex f) n := (d.reindexTile e).reindexOuter f
  apply d'.groupTwo_finite_30_1_2_impossible
  · exact d.tile.angle_weights_after_reindex e 15 (angleTableWeights (15, 1, 4))
      FiniteSecondOrder30.tileWeights hw (by intro i; fin_cases i <;> decide)
  · exact T.angle_weights_after_reindex f 15 (angleTableWeights (15, 1, 6))
      FiniteSecondOrder30.outerWeights ha (by intro i; fin_cases i <;> decide)

theorem finite_pair_10_impossible {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hw : ∀ i, d.tile.angle i = (angleTableWeights (15, 1, 4) i : ℝ) * (Real.pi / 15))
    (ha : ∀ i, T.angle i = (angleTableWeights (15, 2, 4) i : ℝ) * (Real.pi / 15)) : False := by
  let e : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let f : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let d' : Tiling (T.reindex f) n := (d.reindexTile e).reindexOuter f
  apply d'.groupTwo_finite_15_2_2_impossible
  · exact d.tile.angle_weights_after_reindex e 15 (angleTableWeights (15, 1, 4))
      FiniteSecondOrder15.tileWeights hw (by intro i; fin_cases i <;> decide)
  · exact T.angle_weights_after_reindex f 15 (angleTableWeights (15, 2, 4))
      FiniteSecondOrder15.outerWeights ha (by intro i; fin_cases i <;> decide)

theorem finite_pair_11_impossible {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hw : ∀ i, d.tile.angle i = (angleTableWeights (15, 1, 4) i : ℝ) * (Real.pi / 15))
    (ha : ∀ i, T.angle i = (angleTableWeights (15, 2, 5) i : ℝ) * (Real.pi / 15)) : False := by
  let e : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let f : Equiv.Perm (Fin 3) := (Equiv.swap 1 2).trans (Equiv.swap 0 1)
  let d' : Tiling (T.reindex f) n := (d.reindexTile e).reindexOuter f
  apply d'.boundary30Double_impossible
  · exact d.tile.angle_weights_after_reindex e 15 (angleTableWeights (15, 1, 4))
      boundary30DoubleTileWeights hw (by intro i; fin_cases i <;> decide)
  · exact T.angle_weights_after_reindex f 15 (angleTableWeights (15, 2, 5))
      boundary30DoubleOuterWeights ha (by intro i; fin_cases i <;> decide)

theorem finite_pair_12_impossible {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hw : ∀ i, d.tile.angle i = (angleTableWeights (15, 1, 4) i : ℝ) * (Real.pi / 15))
    (ha : ∀ i, T.angle i = (angleTableWeights (15, 3, 4) i : ℝ) * (Real.pi / 15)) : False := by
  let e : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let f : Equiv.Perm (Fin 3) := (Equiv.swap 0 1).trans (Equiv.swap 1 2)
  let d' : Tiling (T.reindex f) n := (d.reindexTile e).reindexOuter f
  apply d'.groupTwo_finite_15_2_1_impossible
  · exact d.tile.angle_weights_after_reindex e 15 (angleTableWeights (15, 1, 4))
      FiniteFirstOrder15.tileWeights hw (by intro i; fin_cases i <;> decide)
  · exact T.angle_weights_after_reindex f 15 (angleTableWeights (15, 3, 4))
      FiniteFirstOrder15.outerWeights ha (by intro i; fin_cases i <;> decide)

theorem finite_pair_34_impossible {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hw : ∀ i, d.tile.angle i = (angleTableWeights (24, 3, 5) i : ℝ) * (Real.pi / 24))
    (ha : ∀ i, T.angle i = (angleTableWeights (24, 3, 10) i : ℝ) * (Real.pi / 24)) : False := by
  let e : Equiv.Perm (Fin 3) := Equiv.refl _
  let f : Equiv.Perm (Fin 3) := Equiv.refl _
  let d' : Tiling (T.reindex f) n := (d.reindexTile e).reindexOuter f
  apply d'.boundary48_impossible
  · exact d.tile.angle_weights_after_reindex e 24 (angleTableWeights (24, 3, 5))
      boundary48TileWeights hw (by intro i; fin_cases i <;> decide)
  · exact T.angle_weights_after_reindex f 24 (angleTableWeights (24, 3, 10))
      boundary48OuterWeights ha (by intro i; fin_cases i <;> decide)

theorem finite_pair_40_impossible {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hw : ∀ i, d.tile.angle i = (angleTableWeights (30, 3, 7) i : ℝ) * (Real.pi / 30))
    (ha : ∀ i, T.angle i = (angleTableWeights (30, 3, 6) i : ℝ) * (Real.pi / 30)) : False := by
  let e : Equiv.Perm (Fin 3) := Equiv.refl _
  let f : Equiv.Perm (Fin 3) := Equiv.refl _
  let d' : Tiling (T.reindex f) n := (d.reindexTile e).reindexOuter f
  apply d'.groupTwo_finite_20_1_1_impossible
  · exact d.tile.angle_weights_after_reindex e 30 (angleTableWeights (30, 3, 7))
      FiniteFirstOrder20One.tileWeights hw (by intro i; fin_cases i <;> decide)
  · exact T.angle_weights_after_reindex f 30 (angleTableWeights (30, 3, 6))
      FiniteFirstOrder20One.outerWeights ha (by intro i; fin_cases i <;> decide)

theorem finite_pair_41_impossible {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hw : ∀ i, d.tile.angle i = (angleTableWeights (30, 3, 7) i : ℝ) * (Real.pi / 30))
    (ha : ∀ i, T.angle i = (angleTableWeights (30, 3, 10) i : ℝ) * (Real.pi / 30)) : False := by
  let e : Equiv.Perm (Fin 3) := Equiv.refl _
  let f : Equiv.Perm (Fin 3) := Equiv.refl _
  let d' : Tiling (T.reindex f) n := (d.reindexTile e).reindexOuter f
  apply d'.groupTwo_finite_20_1_3_impossible
  · exact d.tile.angle_weights_after_reindex e 30 (angleTableWeights (30, 3, 7))
      FiniteThirdOrder20One.tileWeights hw (by intro i; fin_cases i <;> decide)
  · exact T.angle_weights_after_reindex f 30 (angleTableWeights (30, 3, 10))
      FiniteThirdOrder20One.outerWeights ha (by intro i; fin_cases i <;> decide)

end Tiling
end Erdos633b
