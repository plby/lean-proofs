import Wikipedia.SzemeredisTheorem.Hypergraph.APCorrespondence
import Wikipedia.SzemeredisTheorem.Transference.APCut
import Wikipedia.SzemeredisTheorem.Transference.SimplexTelescoping

/-!
# Cut control of arithmetic-progression simplex counts

For one edge in the arithmetic-progression simplex, the remaining edge
weights form a product of deleted-coordinate cut tests.  The distinguished
edge is an automorphic weighted sum when the modulus is coprime to the
relevant factorial.  This file makes that reduction exact and then applies
cut discrepancy edge by edge.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The factors other than colour `j` in the ordered telescoping term.
The first factor selects the old weight below `j`; the second selects the
new weight above `j`.  At `i = j` both factors are one. -/
def orderedAPEdgeFactor
    (k N : ℕ) (f g : ZMod N → ℝ)
    (j i : Fin k) (x : Fin k → ZMod N) : ℝ :=
  (if i < j then
      f (apSimplexForm k N i (deleteCoordinate x i))
    else 1) *
  (if j < i then
      g (apSimplexForm k N i (deleteCoordinate x i))
    else 1)

@[simp]
theorem orderedAPEdgeFactor_self
    (k N : ℕ) (f g : ZMod N → ℝ)
    (j : Fin k) (x : Fin k → ZMod N) :
    orderedAPEdgeFactor k N f g j j x = 1 := by
  simp [orderedAPEdgeFactor]

/-- Replacing a coordinate does not change the deleted vector at that
coordinate. -/
@[simp]
theorem deleteCoordinate_update_same
    {k : ℕ} {G : Type*} [DecidableEq G]
    (x : Fin k → G) (i : Fin k) (a : G) :
    deleteCoordinate (Function.update x i a) i =
      deleteCoordinate x i := by
  funext q
  simp [deleteCoordinate, q.2]

/-- Inserting a replacement into the erased tuple is `Function.update`. -/
theorem insertNth_eraseCoordinate_eq_update
    {n : ℕ} {G : Type*}
    (i : Fin (n + 1)) (a : G) (x : Fin (n + 1) → G) :
    Fin.insertNth i a (eraseCoordinate i x) =
      Function.update x i a := by
  exact Fin.insertNth_removeNth i a x

/-- Replacing coordinate `t` before inserting the distinguished coordinate
`j` only replaces coordinate `j.succAbove t` of the resulting full tuple. -/
theorem insertNth_insertNth_eraseCoordinate
    {n : ℕ} {G : Type*} [DecidableEq G]
    (j : Fin (n + 2)) (t : Fin (n + 1))
    (a b : G) (y : Fin (n + 1) → G) :
    Fin.insertNth j a
        (Fin.insertNth t b (eraseCoordinate t y)) =
      (Function.update (Fin.insertNth j a y)
        (j.succAbove t) b : Fin (n + 2) → G) := by
  rw [insertNth_eraseCoordinate_eq_update, Fin.insertNth_update]

/-- The cut-test family obtained by fixing the distinguished coordinate.
Its `t`-th member is the edge of colour `j.succAbove t`, evaluated after
putting an irrelevant zero in the omitted coordinate. -/
def apMixedCutTest
    (n N : ℕ) (f g : ZMod N → ℝ)
    (j : Fin (n + 2)) (a : ZMod N) :
    CutTestFamily (ZMod N) (n + 1) :=
  fun t z =>
    orderedAPEdgeFactor (n + 2) N f g j (j.succAbove t)
      (Fin.insertNth j a (Fin.insertNth t 0 z))

/-- Evaluating the reconstructed cut test on the erased tuple recovers the
corresponding edge factor of the original full tuple. -/
theorem apMixedCutTest_eraseCoordinate
    (n N : ℕ) (f g : ZMod N → ℝ)
    (j : Fin (n + 2)) (a : ZMod N)
    (t : Fin (n + 1)) (y : Fin (n + 1) → ZMod N) :
    apMixedCutTest n N f g j a t (eraseCoordinate t y) =
      orderedAPEdgeFactor (n + 2) N f g j (j.succAbove t)
        (Fin.insertNth j a y) := by
  rw [apMixedCutTest, insertNth_insertNth_eraseCoordinate]
  unfold orderedAPEdgeFactor
  simp only [deleteCoordinate_update_same]

/-- Pointwise `[0,1]` bounds on `f` and `g` give bounded reconstructed cut
tests. -/
theorem apMixedCutTest_bounded
    (n N : ℕ) (f g : ZMod N → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    (j : Fin (n + 2)) (a : ZMod N) :
    IsBoundedCutTest (apMixedCutTest n N f g j a) := by
  constructor
  · intro t z
    unfold apMixedCutTest orderedAPEdgeFactor
    by_cases htj : j.succAbove t < j
    · have hjt : ¬j < j.succAbove t :=
        not_lt_of_ge (le_of_lt htj)
      simp [htj, hjt, hf0]
    · by_cases hjt : j < j.succAbove t
      · simp [htj, hjt, hg0]
      · exact (Fin.succAbove_ne j t
          (le_antisymm (not_lt.mp hjt) (not_lt.mp htj))).elim
  · intro t z
    unfold apMixedCutTest orderedAPEdgeFactor
    by_cases htj : j.succAbove t < j
    · have hjt : ¬j < j.succAbove t :=
        not_lt_of_ge (le_of_lt htj)
      simpa [htj, hjt] using
        hf1 (apSimplexForm (n + 2) N (j.succAbove t)
          (deleteCoordinate
            (Fin.insertNth j a (Fin.insertNth t 0 z))
            (j.succAbove t)))
    · by_cases hjt : j < j.succAbove t
      · simpa [htj, hjt] using
          hg1 (apSimplexForm (n + 2) N (j.succAbove t)
            (deleteCoordinate
              (Fin.insertNth j a (Fin.insertNth t 0 z))
              (j.succAbove t)))
      · exact (Fin.succAbove_ne j t
          (le_antisymm (not_lt.mp hjt) (not_lt.mp htj))).elim

/-- The full product of ordered edge factors is the pair of filtered
products occurring in the telescoping term. -/
theorem prod_orderedAPEdgeFactor
    (k N : ℕ) (f g : ZMod N → ℝ)
    (j : Fin k) (x : Fin k → ZMod N) :
    (∏ i : Fin k, orderedAPEdgeFactor k N f g j i x) =
      (∏ i ∈ (Finset.univ : Finset (Fin k)) with i < j,
        f (apSimplexForm k N i (deleteCoordinate x i))) *
      ∏ i ∈ (Finset.univ : Finset (Fin k)) with j < i,
        g (apSimplexForm k N i (deleteCoordinate x i)) := by
  rw [Finset.prod_filter, Finset.prod_filter,
    ← Finset.prod_mul_distrib]
  rfl

/-- The product of the reconstructed deleted-coordinate tests is exactly
the product of all non-distinguished factors. -/
theorem prod_apMixedCutTest_eraseCoordinate
    (n N : ℕ) (f g : ZMod N → ℝ)
    (j : Fin (n + 2)) (a : ZMod N)
    (y : Fin (n + 1) → ZMod N) :
    (∏ t : Fin (n + 1),
        apMixedCutTest n N f g j a t
          (eraseCoordinate t y)) =
      (∏ i ∈ (Finset.univ : Finset (Fin (n + 2))) with i < j,
        f (apSimplexForm (n + 2) N i
          (deleteCoordinate (Fin.insertNth j a y) i))) *
      ∏ i ∈ (Finset.univ : Finset (Fin (n + 2))) with j < i,
        g (apSimplexForm (n + 2) N i
          (deleteCoordinate (Fin.insertNth j a y) i)) := by
  simp_rw [apMixedCutTest_eraseCoordinate]
  calc
    (∏ t : Fin (n + 1),
        orderedAPEdgeFactor (n + 2) N f g j
          (j.succAbove t) (Fin.insertNth j a y)) =
        ∏ i : Fin (n + 2),
          orderedAPEdgeFactor (n + 2) N f g j i
            (Fin.insertNth j a y) := by
      symm
      calc
        (∏ i : Fin (n + 2),
            orderedAPEdgeFactor (n + 2) N f g j i
              (Fin.insertNth j a y)) =
            orderedAPEdgeFactor (n + 2) N f g j j
                (Fin.insertNth j a y) *
              ∏ t : Fin (n + 1),
                orderedAPEdgeFactor (n + 2) N f g j
                  (j.succAbove t) (Fin.insertNth j a y) :=
          Fin.prod_univ_succAbove _ j
        _ = ∏ t : Fin (n + 1),
              orderedAPEdgeFactor (n + 2) N f g j
                (j.succAbove t) (Fin.insertNth j a y) := by
          rw [orderedAPEdgeFactor_self, one_mul]
    _ = _ := prod_orderedAPEdgeFactor
      (n + 2) N f g j (Fin.insertNth j a y)

/-- Inserting the distinguished coordinate exposes the AP face as its
automorphically weighted sum of the remaining coordinates. -/
theorem apSimplexForm_deleteCoordinate_insertNth
    (n N : ℕ) (j : Fin (n + 2))
    (a : ZMod N) (y : Fin (n + 1) → ZMod N) :
    apSimplexForm (n + 2) N j
        (deleteCoordinate (Fin.insertNth j a y) j) =
      ∑ t : Fin (n + 1),
        ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
          ZMod N) * y t) := by
  rw [apSimplexForm_deleteCoordinate_eq_weightedSum]
  simp

/-- A normalized average over a tuple can be computed by first fixing one
coordinate and then averaging the remaining tuple. -/
theorem mean_insertNth
    {G : Type*} [Fintype G] (n : ℕ)
    (j : Fin (n + 1)) (F : (Fin (n + 1) → G) → ℝ) :
    mean F =
      mean₂ (fun a : G => fun y : Fin n → G =>
        F (Fin.insertNth j a y)) := by
  calc
    mean F =
        mean (fun p : G × (Fin n → G) =>
          F (Fin.insertNth j p.1 p.2)) := by
      unfold mean
      apply Fintype.expect_equiv
        (Fin.insertNthEquiv (fun _ : Fin (n + 1) => G) j).symm
      intro x
      congr 1
      simp
    _ = mean₂ (fun a : G => fun y : Fin n → G =>
          F (Fin.insertNth j a y)) := by
      simpa [mean, mean₂] using
        (Finset.expect_product
          (Finset.univ : Finset G)
          (Finset.univ : Finset (Fin n → G))
          (fun p : G × (Fin n → G) =>
            F (Fin.insertNth j p.1 p.2)))

/-- After fixing coordinate `j`, the `j`-th mixed telescoping term is
literally a linear cut correlation integrand. -/
theorem mixedSimplexTerm_ap_insertNth
    (n N : ℕ) (f g : ZMod N → ℝ)
    (j : Fin (n + 2)) (a : ZMod N)
    (y : Fin (n + 1) → ZMod N) :
    mixedSimplexTerm
        (apSimplexSystem (n + 2) N f)
        (apSimplexSystem (n + 2) N g) j
        (Fin.insertNth j a y) =
      (f (∑ t : Fin (n + 1),
          ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
            ZMod N) * y t)) -
        g (∑ t : Fin (n + 1),
          ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
            ZMod N) * y t))) *
      ∏ t : Fin (n + 1),
        apMixedCutTest n N f g j a t
          (eraseCoordinate t y) := by
  unfold mixedSimplexTerm
  change
    (f (apSimplexForm (n + 2) N j
        (deleteCoordinate (Fin.insertNth j a y) j)) -
      g (apSimplexForm (n + 2) N j
        (deleteCoordinate (Fin.insertNth j a y) j))) *
      (∏ i ∈ (Finset.univ : Finset (Fin (n + 2))) with i < j,
        f (apSimplexForm (n + 2) N i
          (deleteCoordinate (Fin.insertNth j a y) i))) *
      (∏ i ∈ (Finset.univ : Finset (Fin (n + 2))) with j < i,
        g (apSimplexForm (n + 2) N i
          (deleteCoordinate (Fin.insertNth j a y) i))) = _
  rw [apSimplexForm_deleteCoordinate_insertNth,
    prod_apMixedCutTest_eraseCoordinate]
  ring

/-- A mixed AP-simplex correlation is the average, over the distinguished
coordinate, of transported linear cut correlations. -/
theorem mixedSimplexCorrelation_ap_eq_mean_linearCutCorrelation
    (n N : ℕ) [NeZero N]
    (hN : Nat.Coprime N (Nat.factorial (n + 1)))
    (f g : ZMod N → ℝ) (j : Fin (n + 2)) :
    mixedSimplexCorrelation
        (apSimplexSystem (n + 2) N f)
        (apSimplexSystem (n + 2) N g) j =
      mean (fun a : ZMod N =>
        linearCutCorrelation (n + 1)
          (apFaceScalingEquiv hN j) f g
          (apMixedCutTest n N f g j a)) := by
  unfold mixedSimplexCorrelation
  rw [mean_insertNth (n + 1) j]
  unfold mean₂
  apply congrArg mean
  funext a
  unfold linearCutCorrelation
  apply congrArg mean
  funext y
  change
    mixedSimplexTerm
        (apSimplexSystem (n + 2) N f)
        (apSimplexSystem (n + 2) N g) j
        (Fin.insertNth j a y) =
      (f (∑ i, apFaceScalingEquiv hN j i (y i)) -
        g (∑ i, apFaceScalingEquiv hN j i (y i))) *
      ∏ i, apMixedCutTest n N f g j a i
        (eraseCoordinate i y)
  rw [mixedSimplexTerm_ap_insertNth]
  simp only [apFaceScalingEquiv_apply]

/-- Cut discrepancy controls every mixed AP-simplex correlation when the
remaining edge weights lie in `[0,1]`. -/
theorem abs_mixedSimplexCorrelation_ap_le
    (n N : ℕ) [NeZero N]
    (hN : Nat.Coprime N (Nat.factorial (n + 1)))
    (f g : ZMod N → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    {ε : ℝ} (hcut : CutDiscrepancyLe (n + 1) f g ε)
    (j : Fin (n + 2)) :
    |mixedSimplexCorrelation
        (apSimplexSystem (n + 2) N f)
        (apSimplexSystem (n + 2) N g) j| ≤ ε := by
  rw [mixedSimplexCorrelation_ap_eq_mean_linearCutCorrelation
    n N hN f g j]
  calc
    |mean (fun a : ZMod N =>
        linearCutCorrelation (n + 1)
          (apFaceScalingEquiv hN j) f g
          (apMixedCutTest n N f g j a))| ≤
        mean (fun a : ZMod N =>
          |linearCutCorrelation (n + 1)
            (apFaceScalingEquiv hN j) f g
            (apMixedCutTest n N f g j a)|) := by
      exact Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun _a : ZMod N => ε) := by
      apply mean_mono
      intro a
      exact hcut.abs_linearCutCorrelation_le
        (apFaceScalingEquiv hN j)
        (apMixedCutTest n N f g j a)
        (apMixedCutTest_bounded n N f g
          hf0 hf1 hg0 hg1 j a)
    _ = ε := mean_const _

/-- Uniform mixed-correlation control for the two AP simplex systems. -/
theorem apSimplexSystem_mixedCorrelationLe
    (n N : ℕ) [NeZero N]
    (hN : Nat.Coprime N (Nat.factorial (n + 1)))
    (f g : ZMod N → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    {ε : ℝ} (hcut : CutDiscrepancyLe (n + 1) f g ε) :
    MixedSimplexCorrelationLe
      (apSimplexSystem (n + 2) N f)
      (apSimplexSystem (n + 2) N g) ε := by
  intro j
  exact abs_mixedSimplexCorrelation_ap_le
    n N hN f g hf0 hf1 hg0 hg1 hcut j

/-- Dense AP counting lemma in cut-discrepancy form.  For progression
length `n+2`, the loss is exactly one `ε` for each simplex colour. -/
theorem cyclicAPCount_abs_sub_le_of_cutDiscrepancy
    (n N : ℕ) [NeZero N]
    (hN : Nat.Coprime N (Nat.factorial (n + 1)))
    (f g : ZMod N → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    {ε : ℝ} (hcut : CutDiscrepancyLe (n + 1) f g ε) :
    |cyclicAPCount (n + 2) N f -
        cyclicAPCount (n + 2) N g| ≤
      ((n + 2 : ℕ) : ℝ) * ε := by
  rw [← apSimplexSystem_simplexCount_eq_cyclicAPCount n N f,
    ← apSimplexSystem_simplexCount_eq_cyclicAPCount n N g]
  exact simplexCount_abs_sub_le_of_mixedCorrelation
    (apSimplexSystem (n + 2) N f)
    (apSimplexSystem (n + 2) N g)
    (apSimplexSystem_mixedCorrelationLe
      n N hN f g hf0 hf1 hg0 hg1 hcut)

end Wikipedia.SzemeredisTheorem
