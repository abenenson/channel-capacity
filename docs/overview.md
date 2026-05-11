# Capacity-achieving prior uniqueness

For the library spec and file layout, see [../README.md](../README.md). This
document covers the mathematical reasoning behind the three uniqueness
theorems the library proves: what they say, why the hypotheses are shaped the
way they are, and where the real analytic content lives.

## 1. What the library proves

For a Markov kernel `k : α ⇝ β` between measurable spaces, Shannon's
*channel capacity* is the supremum

```
C(k) = sup_{p ∈ P(α)} I(p, k)
```

of the mutual information `I(p, k)` between the input `p` and the joint law
`p ⊗ k`, taken over probability measures on the input alphabet. Three
classical questions follow: when is the supremum attained, when is the
attaining input unique, and what structural hypothesis on `k` is both
sufficient and honest?

In the finite-alphabet setting the answer is textbook. The input
simplex is compact, the mutual-information functional is continuous and
concave, and uniqueness holds whenever the channel is structurally
non-degenerate enough to rule out
two distinct inputs inducing the same output distribution. In the
general measure-theoretic setting the picture is less uniform:
compactness of `P(α)`, continuity or upper semicontinuity of
`p ↦ I(p, k)` with respect to a useful topology, and the right analogue
of "full-rank rows" each require work, and different regularity
packages (finite-dimensional density parameterization, bounded-
information hypotheses, weak-* upper semicontinuity from a topological
input constraint) produce different theorems.

The library gives three aligned uniqueness theorems that bracket the
answer:

1. A **finite-alphabet theorem** that discharges compactness, continuity,
   and strict concavity internally. The only external hypothesis is that
   the kernel's row matrix has trivial real kernel.
2. A **compact-Polish theorem** built on a regularity class
   `Kernel.ContinuousPositiveDensity` — all rows share a strictly positive
   jointly continuous density against a finite reference measure — plus
   injectivity of the prior pushforward.
3. A **general packaging theorem** that isolates the abstract hypotheses
   (compactness of `P(α)`, upper semicontinuity of the mutual-information
   functional, a `WellConditionedForCapacity` bundle, and injective prior
   pushforward) and lets the caller discharge them however they can.

The finite theorem is closest to Mathlib's existing finite-probability surface.
The compact-Polish theorem is the strongest concrete measure-theoretic result.
The general theorem is the packaging that the other two specialize.

The motivating application is a Shannon-correspondence for governance
channels in a separate legitimacy framework; that development consumes
this library as a dependency and is documented in its own paper. The
present library stands on its own information-theoretic terms.

## 2. Preliminaries

We work in Lean 4 against Mathlib. A Markov kernel `k` from `α` to `β` is
an element of `ProbabilityTheory.Kernel α β` carrying the `IsMarkovKernel`
instance. Given a probability measure `p` on `α` we form the joint law
`p ⊗ k` on `α × β` via Mathlib's `Measure.compProd`, and the output
marginal `outputPrior k p ∈ P(β)` via `p.bind k`.

Mutual information is defined directly against Mathlib's Kullback-Leibler
divergence:

```lean
noncomputable def mutualInformation
    (p : ProbabilityMeasure α) (k : Kernel α β) [IsMarkovKernel k] : ℝ :=
  (InformationTheory.klDiv (jointLaw k p).toMeasure
    (independentJointLaw k p).toMeasure).toReal
```

where `jointLaw k p` is `p ⊗ₘ k` and `independentJointLaw k p` is the
product of its marginals. Channel capacity is then

```lean
noncomputable def channelCapacity (k : Kernel α β) [IsMarkovKernel k] : ℝ :=
  sSup (Set.range fun p : ProbabilityMeasure α => mutualInformation p k)
```

Two non-degeneracy predicates appear throughout:

```lean
def Kernel.InjectivePriorPushforward (k : Kernel α β) [IsMarkovKernel k] : Prop :=
  Function.Injective fun p : ProbabilityMeasure α => outputPrior k p

def Kernel.RowMatrixFullRank (k : Kernel α β) : Prop :=
  Function.Injective fun w : α → ℝ =>
    fun b => ∑ a, w a * (k a {b}).toReal
```

`InjectivePriorPushforward` is the clean measure-theoretic analogue of
"distinct inputs give distinct outputs". `RowMatrixFullRank` is the
finite-alphabet linear-algebra form: the real linear map induced by the
row matrix is injective.

One auxiliary primitive, `ProbabilityMeasure.convexCombination` in
`Basic.lean`, is a subtype-level wrapper for `t·μ + (1-t)·ν` used by the
strict-concavity arguments. Mathlib equips `Measure` with affine
structure but does not yet place it on the `ProbabilityMeasure` subtype,
so the wrapper is defined locally.

## 3. The finite theorem

The finite theorem lives in `ChannelCapacity/Finite.lean` and is the
cleanest statement in the library.

```lean
theorem exists_unique_capacity_achieving_prior_of_finite
    {α β : Type*}
    [Fintype α] [Finite β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [Nonempty α]
    (k : Kernel α β) [IsMarkovKernel k]
    (h : Kernel.RowMatrixFullRank k) :
    ∃! p : ProbabilityMeasure α, mutualInformation p k = channelCapacity k
```

The only non-degeneracy hypothesis is `RowMatrixFullRank`. No topology,
compactness, semicontinuity, or abstract bundle hypothesis appears in
the statement: they are all discharged inside the proof.

### Proof outline

The proof is assembled from four Mathlib-native ingredients and one
bridge lemma.

**Finite entropy formula.** On a finite alphabet, mutual information
reduces to the discrete Shannon formula

```
I(p, k) = H(outputPrior k p) - Σ_a p(a) · H(k(a))
```

where `H(μ) = Σ_x -μ({x}) log μ({x})`. This follows because
`toMeasure_eq_count_withDensity` rewrites each probability measure on a
finite alphabet as a counting-measure-with-density, at which point KL
against the product marginal collapses to the discrete entropy
expression. Conditional entropy is linear in `p`.

**Strict concavity.** Strict concavity of the output-entropy term
follows from `Real.strictConcaveOn_negMulLog` applied pointwise to the
output distribution. Because `p ↦ outputPrior k p` is *affine*, the
composition is strictly concave as a function of `p` precisely when that
affine map does not collapse two distinct inputs to the same output.
This is the single place where `RowMatrixFullRank` is used: full-rank
rows imply `InjectivePriorPushforward`, which rules out the degenerate
case. The bridge lemma is
`Kernel.injectivePriorPushforward_of_rowMatrixFullRank` in `Finite.lean`.

**Compactness.** Mathlib equips `ProbabilityMeasure α` for finite
discrete `α` with the weak topology, under which `ProbabilityMeasure α`
is compact via `MeasureTheory.Measure.Prokhorov` specialized to a finite
measurable space.

**Continuity.** `continuous_mutualInformation_of_finite` in `Finite.lean`
shows `p ↦ I(p, k)` is continuous on `P(α)` for finite `α, β`. The
finite entropy formula pays dividends here: all singularities of the
`klDiv` integrand are absorbed into `negMulLog`'s continuous extension
to `0`.

**Assembly.** A continuous real-valued function on a nonempty compact
space attains its supremum (existence); a strictly concave function on a
convex set attains its maximum at at most one point (uniqueness).
Combining these gives the headline theorem, proved in `Finite.lean`.

### Remarks

`RowMatrixFullRank` is decidable for rational-valued kernels and
checkable by `native_decide` in concrete instances. The theorem's
signature uses only `Fintype`, `Finite`, `MeasurableSingletonClass`,
`IsMarkovKernel`, and Mathlib's existing information-theoretic
infrastructure; nothing in the statement depends on structures local to
this library.

## 4. The compact-Polish theorem

The compact-Polish theorem lifts uniqueness to compact Polish input and
output alphabets. It lives in `ChannelCapacity/Discharged.lean` and
packages the absolute-continuity, positivity, and joint-continuity data
into a single structure class.

### The regularity class

```lean
structure ContinuousPositiveDensity
    (k : Kernel α β) (ν : Measure β)
    [IsMarkovKernel k] [OpensMeasurableSpace α] where
  density : α → β → NNReal
  continuous_density : Continuous (Function.uncurry density)
  eq_withDensity : ∀ a, k a = ν.withDensity (fun b => (density a b : ℝ≥0∞))
  density_pos : ∀ a b, 0 < density a b
  mutualInformation_usc :
    UpperSemicontinuous fun p : ProbabilityMeasure α => mutualInformation p k
```

A kernel inhabits this class with respect to a finite reference measure
`ν` when all rows have a common density `f_a`, the bivariate density
`(a, b) ↦ f_a(b)` is jointly continuous, and `f_a(b) > 0` for all
`a, b`. The last field, `mutualInformation_usc`, is carried rather than
derived; Section 4.3 below discusses why.

### The headline theorem

```lean
theorem exists_unique_capacity_achieving_prior_discharged
    {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace α] [TopologicalSpace β]
    [CompactSpace α] [CompactSpace β]
    [PolishSpace α] [PolishSpace β]
    [BorelSpace α] [BorelSpace β]
    [OpensMeasurableSpace α] [OpensMeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    [Nonempty α]
    (k : Kernel α β) [IsMarkovKernel k]
    (ν : Measure β) [IsFiniteMeasure ν]
    (hDensity : Kernel.ContinuousPositiveDensity k ν)
    (hInj : Kernel.InjectivePriorPushforward k) :
    ∃! p : ProbabilityMeasure α, mutualInformation p k = channelCapacity k
```

This theorem is the discharged specialization of the abstract packaging
theorem `exists_unique_capacity_achieving_prior` in `Capacity.lean`. The
packaging theorem takes an injectivity hypothesis, a
`WellConditionedForCapacity` bundle, nonemptiness and compactness of
`P(α)`, and upper semicontinuity of the mutual-information functional.
The discharged theorem supplies each of these from
`ContinuousPositiveDensity` data and the compact-Polish ambient
structure.

### What is discharged and what is carried

We enumerate the abstract hypotheses in the order they appear and state
exactly which are derived from the density data and which remain
structural.

**Absolute continuity of rows.** From density positivity and the
`withDensity` representation, each row `k(a)` is absolutely continuous
with respect to `ν`, and via `outputPrior_eq_withDensity_outputDensity`
with respect to `outputPrior k p` for any input `p`. Proved
unconditionally by `row_absolutelyContinuous_outputPrior` in
`Discharged.lean`.

**Uniform density bounds.** Joint continuity on a compact product
`α × β` yields a strictly positive uniform lower bound `c` and a finite
uniform upper bound `C` (`exists_uniform_density_bounds`). Combined
with the elementary inequality `x log x + 1 - x ≤ x² + 1`
(`klFun_le_sq_add_one`), this produces

```
D_KL(k(a) ‖ outputPrior k p) ≤ (C / c)² + 1
```

for all `a` and `p` (`row_klDiv_le_outputPrior_bound`).

**Finiteness of the reference KL.** The uniform bound plus the
kernel-side chain rule `klDiv_compProd_right` (proved in
`KernelCompositionKullbackLeibler.lean`) gives finiteness of the joint
KL between `p ⊗ k` and a fixed `OutputMarginalReference`
(`hFiniteRefKL_of_continuousPositiveDensity`).

**Chain rule.** Discharged unconditionally on an injectivity-compatible
`OutputMarginalReference` (`hChainRule_of_outputMarginalReference`).

These three ingredients assemble a `WellConditionedForCapacity`
inhabitant (`wellConditionedForCapacity_of_continuousPositiveDensity`).
Compactness of `P(α)` follows from Prokhorov on the compact Polish
input space.

**Upper semicontinuity.** This is the field carried rather than
discharged. In the finite case, `continuous_mutualInformation_of_finite`
gives continuity and hence upper semicontinuity, and populating the
field is mechanical (see the worked example below). For general
compact-Polish `α, β` with a strictly positive jointly continuous
density, a derived theorem of the form
`upperSemicontinuous_mutualInformation_of_continuousPositiveDensity`
has not yet been proved; a candidate route uses the uniform density
bounds plus dominated convergence to reduce mutual information to a
continuous functional of the output density in an appropriate weak
topology, but the analytic work of controlling the KL integrand away
from the boundary is nontrivial and is not in the library.

We call out this distinction so that users of the discharged theorem
are not misled. The `ContinuousPositiveDensity` bundle contains one
hypothesis that is not discharged from the others — for concrete
specializations (finite or otherwise) it must be supplied, typically
by specialization to a case where continuity is known directly.

## 5. Worked example and sharpness

### 5.1 `Fin 2 → Fin 2` — non-vacuity of the discharged theorem

`ChannelCapacity/DischargedExample.lean` constructs the binary channel

```
k(0) = (3/4, 1/4),   k(1) = (1/4, 3/4)
```

with counting measure as the reference `ν` on `{0, 1}`:

```lean
noncomputable def twoByTwoDensity (i j : Fin 2) : NNReal :=
  if i = j then 3 / 4 else 1 / 4
```

All five `ContinuousPositiveDensity` fields are verified:

- `continuous_density` by `fun_prop` on a finite discrete domain;
- `eq_withDensity` by `toMeasure_eq_count_withDensity` on the row PMF;
- `density_pos` by enumeration;
- `mutualInformation_usc` from
  `continuous_mutualInformation_of_finite.upperSemicontinuous`
  specialized to the finite case.

`RowMatrixFullRank` is discharged by `nlinarith` on a two-equation
linear system (`twoByTwo_rowMatrixFullRank`), and
`Kernel.injectivePriorPushforward_of_rowMatrixFullRank` converts it to
`InjectivePriorPushforward`. Applying
`exists_unique_capacity_achieving_prior_discharged` witnesses that the
two uniqueness theorems are jointly non-vacuous. The capacity-achieving
prior is in fact the uniform prior by symmetry, though this
identification is outside the formal statement.

### 5.2 `Fin 6 → Fin 3` — row separation is not enough

`ChannelCapacity/Counterexample.lean` exhibits a `Fin 6 → Fin 3` channel
whose rows are the six permutations of `(1/2, 1/3, 1/6)`. The file
proves:

- all six rows are pairwise distinct as probability measures on
  `{0, 1, 2}` (`RowSeparating`);
- the prior pushforward is *not* injective: the prior uniformly
  supported on `{0, 3, 4}` and the prior uniformly supported on
  `{1, 2, 5}` both push forward to the uniform distribution on
  `{0, 1, 2}` (`pushforward_prior₁`, `pushforward_prior₂`).

The outputs are checked by closed-form rational arithmetic plus a
`native_decide` sanity check on a rational mirror. The conclusion is

```lean
theorem permutationKernel_not_injectivePriorPushforward :
    ¬ ChannelCapacity.Kernel.InjectivePriorPushforward permutationKernel
```

This is the load-bearing sharpness content in the library: the
non-degeneracy hypothesis in the uniqueness theorems cannot be weakened
to `RowSeparating`. Two distinct input distributions can produce the
same output, and no uniqueness result along these lines can be stated
at that weaker hypothesis. `InjectivePriorPushforward` is strictly
stronger than pairwise distinctness of rows, and the theorems need the
stronger form.

## 6. Why the three layers exist

The layered structure is deliberate and each layer earns its place.

**The finite theorem is the self-contained finite result.** Its signature uses
only Mathlib vocabulary and the proof depends only on Mathlib-native
lemmas. A user who needs uniqueness for a finite-alphabet channel gets
a clean theorem with a single linear-algebra hypothesis and no bundle
machinery in the signature.

**The compact-Polish theorem exists to be the strongest concrete
measure-theoretic result.** Real channel models are rarely finite, and
most tractable continuous channel models come with a positive
continuous density against a natural reference measure. The
`ContinuousPositiveDensity` class is the minimum structural bundle
under which the absolute-continuity and chain-rule machinery close, and
the theorem is the honest package: four of five fields discharged
from density data plus compactness, with the fifth field carried and
labelled.

**The general theorem exists to be the packaging.** Users with their
own regularity framework — different density class, different
topological input constraint, bounded-information hypotheses — can
apply `exists_unique_capacity_achieving_prior` directly, supply their
own discharge for the abstract hypotheses, and avoid coupling their
work to `ContinuousPositiveDensity`. The compact-Polish theorem is
then an instance of how to use it.

The honest scope of the library is: the finite case is complete; the
compact-Polish case is complete modulo the one carried field; and the
general packaging is an abstract interface rather than a content
theorem.

The counterexample in Section 5.2 earns its place for the same reason.
A naive reading of "full-rank rows" in the measure-theoretic setting
would try `RowSeparating` — all rows pairwise distinct. The `Fin 6 → Fin 3`
permutation channel shows that this is strictly weaker than
`InjectivePriorPushforward`: pairwise-distinct rows on the output side
can admit distinct priors with the same output marginal. The uniqueness
theorems need the stronger condition, and the counterexample witnesses
why weakening it is not an option.

## 7. Pointers

**Library entry points**

- Usage and file inventory: [`../README.md`](../README.md).
- Build: `lake build` at the repository root.

**Theorem locations**

| Theorem | File |
|---|---|
| `exists_unique_capacity_achieving_prior_of_finite` | `ChannelCapacity/Finite.lean` |
| `exists_unique_capacity_achieving_prior_discharged` | `ChannelCapacity/Discharged.lean` |
| `exists_unique_capacity_achieving_prior` | `ChannelCapacity/Capacity.lean` |
| `continuous_mutualInformation_of_finite` | `ChannelCapacity/Finite.lean` |
| `Kernel.injectivePriorPushforward_of_rowMatrixFullRank` | `ChannelCapacity/Finite.lean` |
| `ContinuousPositiveDensity` structure | `ChannelCapacity/Discharged.lean` |
| `wellConditionedForCapacity_of_continuousPositiveDensity` | `ChannelCapacity/Discharged.lean` |
| `row_absolutelyContinuous_outputPrior`, `row_klDiv_le_outputPrior_bound` | `ChannelCapacity/Discharged.lean` |
| `klFun_le_sq_add_one`, `exists_uniform_density_bounds` | `ChannelCapacity/Discharged.lean` |
| `rnDeriv_compProd_right`, `klDiv_compProd_right` | `ChannelCapacity/KernelCompositionKullbackLeibler.lean` |

**Examples and counterexamples**

- Non-vacuity witness: `ChannelCapacity/DischargedExample.lean`
  (`twoByTwoDensity`, `twoByTwo_rowMatrixFullRank`).
- Sharpness of the non-degeneracy hypothesis:
  `ChannelCapacity/Counterexample.lean`
  (`permutationKernel_not_injectivePriorPushforward`).

**Reusable components**

- `exists_unique_capacity_achieving_prior_of_finite` and its supporting
  lemmas in `Finite.lean` give the self-contained finite-alphabet theorem.
- The `rnDeriv_compProd_right` / `klDiv_compProd_right` lemmas in
  `KernelCompositionKullbackLeibler.lean` have no channel-specific
  dependencies.
- The `ProbabilityMeasure.convexCombination` wrapper in `Basic.lean`
  isolates a small local API gap around convex combinations of probability
  measures.

**Open mathematical work**

- A general compact-Polish discharge of upper semicontinuity of
  `p ↦ I(p, k)` under `ContinuousPositiveDensity` hypotheses alone,
  without finite specialization. This would move the
  `mutualInformation_usc` field from carried to derived and close the
  honest-scope gap in Section 4.3.

**Motivating application**

The library's motivating application is a Shannon-correspondence for
governance channels in a separate legitimacy framework; see the
legitimacy paper for that development. That work consumes this library
as a dependency and does not alter or extend it.
