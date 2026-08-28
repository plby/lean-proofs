import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTetrahedronRotation

/-!
# Genuine coordinate-plane rotations of the native three-cube

The previously constructed perimeter-preserving square homotopy is inserted
in any ordered pair of distinct coordinates. The remaining coordinate is
fixed throughout. Every intermediate map preserves the whole cube boundary,
so precomposition gives a homotopy relative to that boundary for every
native three-dimensional generalized loop.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open SecondHurewicz.SimplyConnected

/-- Extract an ordered pair of coordinates from the literal native cube. -/
def nativeCubePair (i j : Fin 3) : C(Fin 3 → I, Fin 2 → I) where
  toFun u := ![u i, u j]
  continuous_toFun := by
    apply continuous_pi
    intro k
    fin_cases k <;> exact continuous_apply _

/-- Insert the genuine square quarter-turn homotopy in coordinates `i,j`. -/
def nativeCubeQuarterTurnHomotopyMap (i j : Fin 3) :
    C(I × (Fin 3 → I), Fin 3 → I) where
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

@[simp] theorem nativeCubeQuarterTurnHomotopyMap_zero (i j : Fin 3)
    (u : Fin 3 → I) : nativeCubeQuarterTurnHomotopyMap i j (0, u) = u := by
  funext k
  change (if k = i then quarterTurnHomotopyMap (0, nativeCubePair i j u) 0
    else if k = j then quarterTurnHomotopyMap (0, nativeCubePair i j u) 1 else u k) = u k
  simp only [quarterTurnHomotopyMap_zero]
  change (if k = i then u i else if k = j then u j else u k) = u k
  split_ifs with hi hj <;> simp_all

@[simp] theorem nativeCubeQuarterTurnHomotopyMap_one (i j : Fin 3)
    (u : Fin 3 → I) :
    nativeCubeQuarterTurnHomotopyMap i j (1, u) =
      fun k => if k = i then u j else if k = j then σ (u i) else u k := by
  funext k
  simp [nativeCubeQuarterTurnHomotopyMap, nativeCubePair]

/-- At a boundary point either the rotated pair meets its perimeter or the
unchanged coordinate still lies on a face. -/
theorem nativeCubeQuarterTurnHomotopyMap_boundary (i j : Fin 3) (hij : i ≠ j)
    (t : I) (u : Fin 3 → I) (hu : u ∈ Cube.boundary (Fin 3)) :
    nativeCubeQuarterTurnHomotopyMap i j (t, u) ∈ Cube.boundary (Fin 3) := by
  have hp (h : nativeCubePair i j u ∈ Cube.boundary (Fin 2)) :
      nativeCubeQuarterTurnHomotopyMap i j (t, u) ∈ Cube.boundary (Fin 3) := by
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

/-- Precomposition by the clockwise quarter turn in the ordered plane `i,j`:
the new `i` coordinate is the old `j`, and the new `j` is the reversed old `i`. -/
def nativeCubeQuarterTurnLoop (p : GenLoop (Fin 3) X x)
    (i j : Fin 3) (hij : i ≠ j) : GenLoop (Fin 3) X x :=
  ⟨⟨fun u => p (nativeCubeQuarterTurnHomotopyMap i j (1, u)),
      p.val.continuous.comp ((nativeCubeQuarterTurnHomotopyMap i j).continuous.comp
        (continuous_const.prodMk continuous_id))⟩,
    fun u hu => p.property _ (nativeCubeQuarterTurnHomotopyMap_boundary i j hij 1 u hu)⟩

@[simp] theorem nativeCubeQuarterTurnLoop_apply (p : GenLoop (Fin 3) X x)
    (i j : Fin 3) (hij : i ≠ j) (u : Fin 3 → I) :
    nativeCubeQuarterTurnLoop p i j hij u =
      p (fun k => if k = i then u j else if k = j then σ (u i) else u k) := by
  change p (nativeCubeQuarterTurnHomotopyMap i j (1, u)) = _
  rw [nativeCubeQuarterTurnHomotopyMap_one]

/-- The explicit native generalized-loop homotopy, relative to every face. -/
def nativeCubeQuarterTurnHomotopy (p : GenLoop (Fin 3) X x)
    (i j : Fin 3) (hij : i ≠ j) :
    p.val.HomotopyRel (nativeCubeQuarterTurnLoop p i j hij).val (Cube.boundary (Fin 3)) where
  toFun z := p (nativeCubeQuarterTurnHomotopyMap i j z)
  continuous_toFun := p.val.continuous.comp (nativeCubeQuarterTurnHomotopyMap i j).continuous
  map_zero_left u := congrArg p (nativeCubeQuarterTurnHomotopyMap_zero i j u)
  map_one_left _ := rfl
  prop' t u hu :=
    (p.property _ (nativeCubeQuarterTurnHomotopyMap_boundary i j hij t u hu)).trans
      (p.property u hu).symm

theorem nativeCubeQuarterTurnLoop_class (p : GenLoop (Fin 3) X x)
    (i j : Fin 3) (hij : i ≠ j) :
    (⟦nativeCubeQuarterTurnLoop p i j hij⟧ : π_ 3 X x) = ⟦p⟧ := by
  exact (Quotient.sound (show GenLoop.Homotopic p (nativeCubeQuarterTurnLoop p i j hij)
    from ⟨nativeCubeQuarterTurnHomotopy p i j hij⟩)).symm

theorem nativeCubeQuarterTurnLoop_additiveClass (p : GenLoop (Fin 3) X x)
    (i j : Fin 3) (hij : i ≠ j) :
    Additive.ofMul (⟦nativeCubeQuarterTurnLoop p i j hij⟧ : π_ 3 X x) =
      Additive.ofMul (⟦p⟧ : π_ 3 X x) :=
  congrArg Additive.ofMul (nativeCubeQuarterTurnLoop_class p i j hij)

/-- The forward rotation in the last two native cube coordinates. -/
@[simp] theorem nativeCubeQuarterTurnLoop_plane12 (p : GenLoop (Fin 3) X x)
    (u : Fin 3 → I) :
    nativeCubeQuarterTurnLoop p 1 2 (by decide) u = p ![u 0, u 2, σ (u 1)] := by
  rw [nativeCubeQuarterTurnLoop_apply]
  congr 1
  funext k
  fin_cases k <;> rfl

/-- The reverse rotation used by the upper cube chamber. -/
@[simp] theorem nativeCubeQuarterTurnLoop_plane21 (p : GenLoop (Fin 3) X x)
    (u : Fin 3 → I) :
    nativeCubeQuarterTurnLoop p 2 1 (by decide) u = p ![u 0, σ (u 2), u 1] := by
  rw [nativeCubeQuarterTurnLoop_apply]
  congr 1
  funext k
  fin_cases k <;> rfl

end Wikipedia.HopfProblem.ThirdHurewicz
