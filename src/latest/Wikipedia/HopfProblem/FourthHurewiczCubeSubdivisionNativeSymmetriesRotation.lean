import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTetrahedronRotation

/-!
# Coordinate-plane rotations of arbitrary native cubes

The perimeter-preserving square homotopy is inserted in any ordered pair
of distinct coordinates. Every other coordinate stays fixed. Thus every
intermediate map preserves the whole cube boundary, in every dimension.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

open SecondHurewicz.SimplyConnected

variable {N : Type*} [DecidableEq N]

/-- Extract an ordered pair of coordinates from the native cube. -/
def nativeCubePair (i j : N) : C(N → I, Fin 2 → I) where
  toFun u := ![u i, u j]
  continuous_toFun := by
    apply continuous_pi
    intro k
    fin_cases k <;> exact continuous_apply _

/-- Insert the genuine square quarter-turn homotopy in coordinates `i,j`. -/
def nativeCubeQuarterTurnHomotopyMap (i j : N) : C(I × (N → I), N → I) where
  toFun z k := if k = i then quarterTurnHomotopyMap (z.1, nativeCubePair i j z.2) 0
    else if k = j then quarterTurnHomotopyMap (z.1, nativeCubePair i j z.2) 1
    else z.2 k
  continuous_toFun := by
    apply continuous_pi
    intro k
    by_cases hi : k = i
    · simp only [if_pos hi]
      exact (continuous_apply (0 : Fin 2)).comp (quarterTurnHomotopyMap.continuous.comp
        (continuous_fst.prodMk ((nativeCubePair i j).continuous.comp continuous_snd)))
    · by_cases hj : k = j
      · simp only [if_neg hi, if_pos hj]
        exact (continuous_apply (1 : Fin 2)).comp (quarterTurnHomotopyMap.continuous.comp
          (continuous_fst.prodMk ((nativeCubePair i j).continuous.comp continuous_snd)))
      · simp only [if_neg hi, if_neg hj]
        exact (continuous_apply k).comp continuous_snd

@[simp] theorem nativeCubeQuarterTurnHomotopyMap_zero (i j : N) (u : N → I) :
    nativeCubeQuarterTurnHomotopyMap i j (0, u) = u := by
  funext k
  change (if k = i then quarterTurnHomotopyMap (0, nativeCubePair i j u) 0
    else if k = j then quarterTurnHomotopyMap (0, nativeCubePair i j u) 1 else u k) = u k
  simp only [quarterTurnHomotopyMap_zero]
  change (if k = i then u i else if k = j then u j else u k) = u k
  split_ifs with hi hj <;> simp_all

@[simp] theorem nativeCubeQuarterTurnHomotopyMap_one (i j : N) (u : N → I) :
    nativeCubeQuarterTurnHomotopyMap i j (1, u) =
      fun k => if k = i then u j else if k = j then σ (u i) else u k := by
  funext k
  simp [nativeCubeQuarterTurnHomotopyMap, nativeCubePair]

/-- A boundary point is witnessed either in the rotated square or in an
unchanged coordinate. -/
theorem nativeCubeQuarterTurnHomotopyMap_boundary (i j : N) (hij : i ≠ j)
    (t : I) (u : N → I) (hu : u ∈ Cube.boundary N) :
    nativeCubeQuarterTurnHomotopyMap i j (t, u) ∈ Cube.boundary N := by
  have hp (h : nativeCubePair i j u ∈ Cube.boundary (Fin 2)) :
      nativeCubeQuarterTurnHomotopyMap i j (t, u) ∈ Cube.boundary N := by
    obtain ⟨k, hk⟩ := quarterTurnHomotopyMap_boundary t (nativeCubePair i j u) h
    fin_cases k
    · exact ⟨i, by simpa [nativeCubeQuarterTurnHomotopyMap] using hk⟩
    · exact ⟨j, by simpa [nativeCubeQuarterTurnHomotopyMap, hij.symm] using hk⟩
  obtain ⟨k, hk⟩ := hu
  by_cases hi : k = i
  · subst k
    exact hp ⟨0, by simpa [nativeCubePair] using hk⟩
  · by_cases hj : k = j
    · subst k
      exact hp ⟨1, by simpa [nativeCubePair] using hk⟩
    · exact ⟨k, by simpa [nativeCubeQuarterTurnHomotopyMap, hi, hj] using hk⟩

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- Precomposition by the quarter turn in the ordered plane `i,j`: the new
`i` coordinate is the old `j`, and the new `j` is the reversed old `i`. -/
def nativeCubeQuarterTurnLoop (p : GenLoop N X x) (i j : N) (hij : i ≠ j) :
    GenLoop N X x :=
  ⟨⟨fun u => p (nativeCubeQuarterTurnHomotopyMap i j (1, u)),
      p.val.continuous.comp ((nativeCubeQuarterTurnHomotopyMap i j).continuous.comp
        (continuous_const.prodMk continuous_id))⟩,
    fun u hu => p.property _ (nativeCubeQuarterTurnHomotopyMap_boundary i j hij 1 u hu)⟩

@[simp] theorem nativeCubeQuarterTurnLoop_apply (p : GenLoop N X x)
    (i j : N) (hij : i ≠ j) (u : N → I) :
    nativeCubeQuarterTurnLoop p i j hij u =
      p (fun k => if k = i then u j else if k = j then σ (u i) else u k) := by
  change p (nativeCubeQuarterTurnHomotopyMap i j (1, u)) = _
  rw [nativeCubeQuarterTurnHomotopyMap_one]

/-- The actual generalized-loop homotopy is relative to every cube face. -/
def nativeCubeQuarterTurnHomotopy (p : GenLoop N X x) (i j : N) (hij : i ≠ j) :
    p.val.HomotopyRel (nativeCubeQuarterTurnLoop p i j hij).val (Cube.boundary N) where
  toFun z := p (nativeCubeQuarterTurnHomotopyMap i j z)
  continuous_toFun := p.val.continuous.comp (nativeCubeQuarterTurnHomotopyMap i j).continuous
  map_zero_left u := congrArg p (nativeCubeQuarterTurnHomotopyMap_zero i j u)
  map_one_left _ := rfl
  prop' t u hu :=
    (p.property _ (nativeCubeQuarterTurnHomotopyMap_boundary i j hij t u hu)).trans
      (p.property u hu).symm

theorem nativeCubeQuarterTurnLoop_class (p : GenLoop N X x) (i j : N) (hij : i ≠ j) :
    (⟦nativeCubeQuarterTurnLoop p i j hij⟧ : HomotopyGroup N X x) = ⟦p⟧ := by
  exact (Quotient.sound (show GenLoop.Homotopic p (nativeCubeQuarterTurnLoop p i j hij)
    from ⟨nativeCubeQuarterTurnHomotopy p i j hij⟩)).symm

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
