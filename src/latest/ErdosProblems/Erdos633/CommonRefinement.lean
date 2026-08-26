import ErdosProblems.Erdos633.SquareSubdivision

/-!
# Common refinement of rationally scaled similar triangles

This proves the finite-refinement step used by the exceptional constructions:
if each piece of a genuine dissection is isometric to a positive rational
multiple of one triangle, all pieces can be refined to congruent triangles.
The common scale and the exact sum-of-squares tile count are exhibited.
-/

namespace Erdos633

/-- An integral ratio of positive scales gives a square congruent subdivision. -/
noncomputable def Triangle.scaleTiling (R : Triangle) (ε q : ℝ)
    (hε : 0 < ε) (hq : 0 < q) (n : ℕ) (hn0 : 0 < n) (hn : (n : ℝ) * ε = q) :
    CongruentTiling
      (R.mapSimilarity 0 (q : ℂ) (by exact_mod_cast ne_of_gt hq))
      (R.mapSimilarity 0 (ε : ℂ) (by exact_mod_cast ne_of_gt hε)) (n ^ 2) := by
  let T := (R.mapSimilarity 0 (ε : ℂ)
    (by exact_mod_cast ne_of_gt hε)).integerDilateTiling n hn0
  apply T.of_carrier_eq
  congr 1
  rw [Triangle.mapSimilarity_comp]
  have hc : (n : ℂ) * (ε : ℂ) = (q : ℂ) := by exact_mod_cast hn
  simp only [mul_zero, add_zero, hc]


theorem TriangleDissection.refine_rational_scales {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (R : Triangle) (r : Fin N → ℚ)
    (hr : ∀ i, 0 < r i)
    (hshape : ∀ i, ∃ e : ℂ ≃ᵢ ℂ,
      e '' (R.mapSimilarity 0 (r i : ℂ) (by exact_mod_cast ne_of_gt (hr i))).carrier =
        (T.tile i).carrier) :
    ∃ (d : ℕ) (hd : 0 < d) (k : Fin N → ℕ),
      (∀ i, 0 < k i) ∧ (∀ i, r i = (k i : ℚ) / d) ∧
      Nonempty (CongruentTiling P
        (R.mapSimilarity 0 (d : ℂ)⁻¹ (inv_ne_zero (by exact_mod_cast ne_of_gt hd)))
        (∑ i, k i ^ 2)) := by
  obtain ⟨d, hd, k, hk, hrat⟩ := positive_rationals_common_denominator r hr
  choose e he using hshape
  let Q := R.mapSimilarity 0 (d : ℂ)⁻¹ (inv_ne_zero (by exact_mod_cast ne_of_gt hd))
  have hscale (i : Fin N) : (k i : ℂ) * (d : ℂ)⁻¹ = (r i : ℂ) := by
    have h := congrArg (fun q : ℚ => (q : ℂ)) (hrat i)
    push_cast at h
    simpa only [div_eq_mul_inv] using h.symm
  have hparent (i : Fin N) :
      Q.mapSimilarity 0 (k i : ℂ) (by exact_mod_cast ne_of_gt (hk i)) =
        R.mapSimilarity 0 (r i : ℂ) (by exact_mod_cast ne_of_gt (hr i)) := by
    dsimp [Q]
    rw [Triangle.mapSimilarity_comp]
    simp only [mul_zero, zero_add]
    congr 1
    exact hscale i
  have S (i : Fin N) : CongruentTiling (T.tile i) Q (k i ^ 2) := by
    apply ((Q.integerDilateTiling (k i) (hk i)).mapIsometry (e i)).of_carrier_eq
    rw [Triangle.mapIsometry_carrier, hparent]
    exact he i
  exact ⟨d, hd, k, hk, hrat, ⟨T.refine (fun i => k i ^ 2) S⟩⟩

end Erdos633
