# Erdős #1050 Transcendence Reading Packet

This folder collects downloadable papers relevant to the open transcendence problem

```text
  Transcendental (sum n >= 1, 1 / (2^n + t))
```

or, after finite rational shifts, the q-logarithm target

```text
  Transcendental (qlog2 alpha),  qlog2 alpha = sum n >= 1, alpha^n / (2^n - 1).
```

The repository already formalizes Borwein-style irrationality for Erdős #1050 in
`LeanGallery/NumberTheory/Erdos1050`; these papers are for exploring possible
transcendence directions.

## Reading Order

1. `1601.02688-zudilin-generalized-q-logarithm.pdf`
   Direct q-log/q-harmonic context. Proves irrationality of a generalized q-logarithm
   and explains why standard q-hypergeometric/Siegel-Shidlovsky methods do not
   apply cleanly.

2. `2211.03030-dixit-kumar-pathak-q-exponential-linear-independence.pdf`
   Short and close to our objects. It proves linear independence/non-rationality
   results for q-exponential/q-log-type values at algebraic points. Useful to check
   whether the logarithmic-derivative identity can be pushed further.

3. `math0304021-sondow-zudilin-euler-q-logarithms.pdf`
   Background on q-logarithms and arithmetic questions around their values.

4. `1603.06771-dreyfus-hardouin-roques-q-difference-functional-relations.pdf`
   Difference-Galois framework for algebraic relations among q-difference solutions.
   More structural, but potentially relevant because qlog satisfies a first-order
   q-difference equation.

5. `1910.01874-adamczewski-dreyfus-hardouin-hypertranscendence-difference-equations.pdf`
   Hypertranscendence and algebraic independence for solutions of linear difference
   equations. Useful for function-level constraints, less directly about single values.

6. `2512.14077-lam-p-adic-valuation-generating-functions.pdf`
   Recent Mahler-method paper for a non-automatic arithmetic coefficient function.
   Adjacent because the Lambert expansion of the Erdős-Borwein constant has divisor
   coefficients, not automatic coefficients.

7. `2012.08283-adamczewski-faverjon-mahler-several-variables.pdf`
   Modern multivariable Mahler-method machinery. Mostly a comparison point: qlog is
   q-difference/Lambert-series flavored, not a standard Mahler function.

8. `0806.1563-coons-borwein-transcendence-power-series-number-theoretic-functions.pdf`
   Function-field style transcendence for arithmetic power series. It is not a value
   transcendence theorem, but it helps delimit what function-level transcendence can
   and cannot prove.

## Formalization Status Snapshot

No formalization of these papers themselves was found locally. Mathlib does have:

* `Transcendental` / `AlgebraicIndependent` API:
  `Mathlib/RingTheory/AlgebraicIndependent/*`
* formal power series `exp`, `log`, derivative, substitution:
  `Mathlib/RingTheory/PowerSeries/*`
* Liouville-number material:
  `Mathlib/NumberTheory/Transcendental/Liouville/*`
* an analytical component toward Lindemann-Weierstrass:
  `Mathlib/NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean`
* Mahler measure, unrelated to Mahler's method:
  `Mathlib/NumberTheory/MahlerMeasure.lean`

What appears missing for these papers:

* a q-difference-equation framework;
* Mahler-method infrastructure;
* Skolem-Mahler-Lech;
* height theory over number fields in the form used by modern transcendence proofs;
* parametrized difference Galois theory;
* the Fatou/Duffin-Schaeffer theorem for bounded-coefficient power series.

## Tractability Estimate

Formalizing the reduction

```text
  sum 1/(2^n + t) = rational head + rational scalar * qlog2 alpha
```

is tractable and close to the existing Erdős #1050 code.

Formalizing Zudilin's q-log irrationality paper is plausible but substantial: it is
mostly Padé/Hankel determinant/integrality/asymptotic work, in the same broad style
as the Borwein formalization already in this repo.

Formalizing Dixit-Kumar-Pathak looks like the best next serious target among the
papers: it is short and relies on a Diophantine lemma plus q-series estimates. The
main missing imported theorem is Skolem-Mahler-Lech.

Formalizing the q-difference Galois or modern Mahler-method papers is currently a
large research-formalization project, not a near-term Lean port. The required
infrastructure is not present in Mathlib.
