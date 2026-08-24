import ErdosProblems.Erdos587.MultiscaleDenseFiber
import ErdosProblems.Erdos587.PolynomialSubsetProgression
import ErdosProblems.Erdos587.GAPSpanControl

/-!
Homogeneous subset-sum progressions with constant filling costs and fixed
translation-to-span control, under explicit multiscale growth certificates.
-/

open scoped Pointwise BigOperators

namespace Erdos587.CFP

theorem exists_homogeneous_GAP_in_subsetSums_multiscale
    (P : GeneralizedAP) (A : Finset ℤ) (hzero : (0 : ℤ) ∈ P.carrier)
    (hA : A ⊆ P.carrier) (h K n M r : ℕ) (T : ℕ → ℕ) (hh : 0 < h) (hM : 0 < M)
    (hproper : P.TProper (2 ^ n * h)) (hpos : ∀ i, 0 < P.length i)
    (hratio : ∀ j < n, T (j + 1) ≤ K * T j)
    (hinitial : (2 * h) * (Nat.log 2 (T 0) + 1) ≤ 2 ^ n * h)
    (hmodel : (P.dilate (2 ^ n * h)).boxCard ≤ M * T n)
    (hdense : ∀ D ⊆ A, A.card ≤ D.card + r → ∀ j ≤ n,
      2 * T j < 4 * ((2 ^ j * h) • insert 0 D).card)
    (hstable : ∀ D ⊆ A, A.card ≤ D.card + r →
      generatedSubgroup P.centeredCoordinates D = generatedSubgroup P.centeredCoordinates A) :
    let H := 2 ^ n * h
    let c := 4 * K + 1
    let D := 4 * M * c ^ P.rank
    let q := denseBoxCount D P.rank
    let F := denseStandardFactor D P.rank
    let B := denseStepBound D P.rank
    F ≤ H → q * (c * H) + B ^ P.rank ≤ r →
    ∃ W ⊆ A, W.card ≤ q * (c * H) + B ^ P.rank ∧ ∃ Q : GeneralizedAP,
      Q.rank = P.rank ∧ Q.Proper ∧ Q.HasHomogeneousBase ∧ Q.carrier ⊆ W.subsetSum ∧
      Q.StepMultipliersBoundedByConstant P B ∧
      (∀ i : Fin Q.rank, ∀ j : Fin P.rank, i.val = j.val →
        Q.length i = H * P.length j / F) ∧
      Q.carrier.card = ∏ i : Fin P.rank, (H * P.length i / F + 1) ∧
      Q.upperEndpoint ≤ (((q * c + B ^ P.rank) * (2 * F) : ℕ) : ℤ) * Q.coefficientSpan := by
  classical
  let H := 2 ^ n * h
  let c := 4 * K + 1
  let D := 4 * M * c ^ P.rank
  let q := denseBoxCount D P.rank
  let F := denseStandardFactor D P.rank
  let B := denseStepBound D P.rank
  dsimp only
  intro hscale hbudget
  have hH : 0 < H := by dsimp [H]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hF : 0 < F := denseStandardFactor_pos hD
  obtain ⟨U, hUA, hUcard, Xs, hlen, hXs, z, hsum⟩ :=
    exists_disjoint_multiscale_dense_fibers P A hzero hA h K n M r q T hh hratio
      hinitial ((Nat.le_add_right _ _).trans hbudget) hmodel hdense
  obtain ⟨S, hSrank, hSproper, hSsub, hSstep, hSside, hScard⟩ :=
    exists_standardized_GAP_of_dense_summands (P.dilate H) D hD hproper Xs hlen
      (fun X hX => (hXs X hX).1) (fun X hX => (hXs X hX).2)
  let Q₀ := S.translateBy z
  have hQrank : Q₀.rank = P.rank := hSrank
  have hQproper : Q₀.Proper := S.proper_translateBy hSproper z
  have hQsum : Q₀.carrier ⊆ U.subsetSum := by
    rw [S.carrier_translateBy]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hsum (Finset.mem_add.mpr
      ⟨z, Finset.mem_singleton_self z, x, hSsub hx, add_comm z x⟩)
  have hQstep : Q₀.StepMultipliersBoundedByConstant P B := hSstep
  have hQside : ∀ i : Fin Q₀.rank, ∀ j : Fin P.rank, i.val = j.val →
      Q₀.length i = H * P.length j / F := hSside
  have hQpos : ∀ i, 0 < Q₀.length i := by
    intro i
    rw [hQside i (Fin.cast hQrank i) rfl]
    exact standardized_side_pos (hpos _) hF hscale
  have hmult : ∀ j : Fin P.rank, ∃ a : ℤ, a ≠ 0 ∧ |a| ≤ (B : ℤ) ∧
      Q₀.step (Fin.cast hQrank.symm j) = a * P.step j := by
    intro j
    exact standardized_step_multiplier_nonzero P Q₀ hQproper hQpos B hQstep
      (Fin.cast hQrank.symm j) j rfl
  choose a hane habs haeq using hmult
  have hsteps : ∀ i : Fin Q₀.rank, ∀ j : Fin P.rank, i.val = j.val →
      Q₀.step i = a j * P.step j := by
    intro i j hij
    have hidx : Fin.cast hQrank.symm j = i := Fin.ext hij.symm
    simpa only [hidx] using haeq j
  obtain ⟨V, hV, hVcard, hproper', hhom, hsum'⟩ :=
    exists_homogeneous_translate_from_reserve P Q₀ A U hzero hA hUA hQproper hQsum
      hQrank a hane B r habs hsteps ((Nat.add_le_add_right hUcard _).trans hbudget) hstable
  let W := U ∪ V
  let Q := Q₀.translateBy (∑ x ∈ V, x)
  have hWA : W ⊆ A := Finset.union_subset hUA (hV.trans Finset.sdiff_subset)
  have hWcard : W.card ≤ q * (c * H) + B ^ P.rank := by
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add hUcard (by omega))
  have hWlinear : W.card ≤ (q * c + B ^ P.rank) * H := by
    have hreserve : B ^ P.rank ≤ B ^ P.rank * H := by
      simpa using Nat.mul_le_mul_left (B ^ P.rank) hH
    nlinarith [hWcard]
  have hspan : (H : ℤ) * P.coefficientSpan ≤ (2 * F : ℕ) * Q.coefficientSpan := by
    apply P.coefficientSpan_lower_of_multipliers Q hQrank a hane H (2 * F) hsteps
    intro i j hij
    change H * P.length j ≤ 2 * F * Q₀.length i
    rw [hQside i j hij]
    exact standardized_side_lower (hpos j) hF hscale
  refine ⟨W, hWA, hWcard, Q, hQrank, hproper', hhom, hsum', hQstep, hQside, ?_, ?_⟩
  · rw [Q₀.card_carrier_translateBy, S.card_carrier_translateBy]
    exact hScard
  · exact P.upperEndpoint_le_span_multiple Q W H (q * c + B ^ P.rank) (2 * F)
      hzero (hWA.trans hA) hsum' hWlinear hspan

end Erdos587.CFP
