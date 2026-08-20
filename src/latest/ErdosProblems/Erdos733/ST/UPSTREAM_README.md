# Formalization of the crossing lemma and its discrete-geometric applications

A Lean 4 / Mathlib formalization of the crossing lemma and three of its classical
consequences, culminating in the Spencer–Szemerédi–Trotter **unit-distance bound**
$O(n^{4/3})$, via Székely's crossing-number argument.

Produced by a single autonomous run of **Trellis**. The proof tree has one
declaration per node — `Tablet/<Node>.lean`, with a matching `Tablet/<Node>.tex`
natural-language statement and proof — and `Tablet.lean` imports them all. It is
sorry-free, uses only the standard Mathlib axioms (`propext`, `Classical.choice`,
`Quot.sound`; see [`APPROVED_AXIOMS.json`](APPROVED_AXIOMS.json)), and builds
against a pinned Mathlib. The git history is the full run, one commit per checkpoint.

The reference paper — *Self-contained Proofs of the Crossing Lemma and Three
Discrete-geometric Applications* — is in
[`paper/crossing_bounds.tex`](paper/crossing_bounds.tex).

## Paper targets

| Label | Node | Statement |
|---|---|---|
| `thm:crossing-lemma` | `CrossingLemma` | For a simple graph $G$ on $n\ge 1$ vertices with $e$ edges, if $e\ge 4n$ then $\mathrm{cr}(G)\ge e^{3}/(100\,n^{2})$. |
| `thm:ST` | `SzemerediTrotter` | There is an absolute constant $C>0$ such that for every finite point set $P$ and every finite set $L$ of lines in the plane, $I(P,L)\le C\bigl((|P|\,|L|)^{2/3}+|P|+|L|\bigr)$. |
| `thm:rich-lines` | `RichLinesBound` | There is an absolute constant $C>0$ such that whenever $2\le k\le\sqrt{|P|}$, the number of lines containing at least $k$ points of $P$ is at most $C\,|P|^{2}/k^{3}$. |
| `thm:unit-distances` | `unit_distance_upper_bound` | There is an absolute constant $C>0$ such that every finite point set $P$ in the plane determines at most $C\,|P|^{4/3}$ unit distances. |

The target statements, verbatim from the tip of this repository:

```lean
-- Tablet/CrossingLemma.lean
theorem CrossingLemma {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet]
    (hn : 1 ≤ Fintype.card V)
    (he : 4 * Fintype.card V ≤ G.edgeFinset.card) :
    (G.edgeFinset.card : ℝ) ^ 3 / (100 * (Fintype.card V : ℝ) ^ 2) ≤
      (CrossingNumber G : ℝ)

-- Tablet/SzemerediTrotter.lean
theorem SzemerediTrotter :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Finset (EuclideanSpace ℝ (Fin 2)))
        (L : Finset {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) // IsAffineLine ℓ}),
        (LineIncidences P L : ℝ) ≤
          C * (((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3) +
            (P.card : ℝ) + (L.card : ℝ))

-- Tablet/RichLinesBound.lean
theorem RichLinesBound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Finset (EuclideanSpace ℝ (Fin 2))) (k : ℕ),
        2 ≤ k → (k : ℝ) ≤ Real.sqrt (P.card : ℝ) →
          ∃ L : Finset {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) // IsAffineLine ℓ},
            (∀ ℓ, ℓ ∈ L ↔
              k ≤ (P.filter (fun p =>
                p ∈ (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))).card) ∧
            (L.card : ℝ) ≤ C * (P.card : ℝ) ^ 2 / (k : ℝ) ^ 3

-- Tablet/unit_distance_upper_bound.lean
theorem unit_distance_upper_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
        (unitDist P : ℝ) ≤ C * (P.card : ℝ) ^ ((4 : ℝ) / 3)
```

The unit-distance target uses one project definition — `unitDist P`, half the number
of ordered off-diagonal pairs of $P$ at distance $1$:

```lean
-- Tablet/unitDist.lean
noncomputable def unitDist (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card / 2
```

## Building

```sh
lake exe cache get   # fetch the pinned Mathlib build cache
lake build
```

The Lean toolchain and Mathlib revision are pinned in
[`lean-toolchain`](lean-toolchain) and [`lake-manifest.json`](lake-manifest.json).
