/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos842.AlonTarsi
import ErdosProblems.Erdos842.CanonicalArcs
import ErdosProblems.Erdos842.Parity

/-!
# From the canonical coefficient to a coloring

This file joins the indexed-arc parity interface to the Alon--Tarsi coloring interface.  The two
interfaces use definitionally identical polynomials and central exponents under different names;
the bridge records those rewrites explicitly and then uses the exact occurrence-support theorem.
-/

open SimpleGraph

namespace Erdos842

/-- A nonzero central coefficient of the canonical indexed-arc polynomial gives a three-coloring
of the canonical cycle-plus-triangles graph. -/
theorem canonicalGraph_colorable_of_centralCoeff_ne_zero
    (n : ℕ) (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (hcoeff :
      MvPolynomial.coeff (canonicalIndexedArcs n triangleCoord).centralExponent
        (canonicalIndexedArcs n triangleCoord).polynomial ≠ 0) :
    (canonicalGraph n triangleCoord).Colorable 3 := by
  have hcoeff' :
      MvPolynomial.coeff (centralExponent (V := Fin (3 * n)))
        (occurrencePolynomial (canonicalOccurrenceTail n triangleCoord)
          (canonicalOccurrenceHead n triangleCoord)) ≠ 0 := by
    rw [← canonicalIndexedArcs_centralExponent n triangleCoord,
      ← canonicalIndexedArcs_polynomial n triangleCoord]
    exact hcoeff
  have hsupport := coloring_of_centralCoeff_ne_zero
    (canonicalOccurrenceTail n triangleCoord)
    (canonicalOccurrenceHead n triangleCoord)
    (canonicalOccurrence_card n) hcoeff'
  rwa [occurrenceSupport_canonicalOccurrence_eq] at hsupport

/-- Modulo-four specialization convenient for the parity argument: a central coefficient congruent
to two modulo four is nonzero and hence colors the canonical graph. -/
theorem canonicalGraph_colorable_of_centralCoeff_modEq_two
    (n : ℕ) (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (hcoeff :
      MvPolynomial.coeff (canonicalIndexedArcs n triangleCoord).centralExponent
          (canonicalIndexedArcs n triangleCoord).polynomial ≡ 2 [ZMOD 4]) :
    (canonicalGraph n triangleCoord).Colorable 3 := by
  apply canonicalGraph_colorable_of_centralCoeff_ne_zero n triangleCoord
  exact (canonicalIndexedArcs n triangleCoord).coeff_central_ne_zero_of_modEq_two hcoeff

/-- A coefficient theorem for every edge-disjoint canonical coordinate colors every graph in the
exact public model. -/
theorem IsCyclePlusTriangles.colorable_of_canonical_centralCoeff_ne_zero
    {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (hG : IsCyclePlusTriangles G n)
    (hcoeff : ∀ triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3,
      Disjoint (cycleGraph (3 * n)) (triangleFactor n triangleCoord) →
        MvPolynomial.coeff (canonicalIndexedArcs n triangleCoord).centralExponent
          (canonicalIndexedArcs n triangleCoord).polynomial ≠ 0) :
    G.Colorable 3 := by
  apply hG.colorable_of_canonical
  intro triangleCoord hdisj
  exact canonicalGraph_colorable_of_centralCoeff_ne_zero n triangleCoord
    (hcoeff triangleCoord hdisj)

/-- Chromatic-number form of
`IsCyclePlusTriangles.colorable_of_canonical_centralCoeff_ne_zero`. -/
theorem IsCyclePlusTriangles.chromaticNumber_le_of_canonical_centralCoeff_ne_zero
    {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (hG : IsCyclePlusTriangles G n)
    (hcoeff : ∀ triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3,
      Disjoint (cycleGraph (3 * n)) (triangleFactor n triangleCoord) →
        MvPolynomial.coeff (canonicalIndexedArcs n triangleCoord).centralExponent
          (canonicalIndexedArcs n triangleCoord).polynomial ≠ 0) :
    G.chromaticNumber ≤ 3 := by
  exact SimpleGraph.chromaticNumber_le_iff_colorable.mpr
    (hG.colorable_of_canonical_centralCoeff_ne_zero hcoeff)

end Erdos842
