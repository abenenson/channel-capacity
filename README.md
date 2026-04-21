# channel-capacity

Lean 4 formalization of **Shannon capacity-achieving prior uniqueness** for Markov kernels.

The library has two layers:

- a **finite-alphabet theorem** with compactness, continuity, and strict concavity discharged
  internally on Mathlib's canonical weak topology for `ProbabilityMeasure`;
- a broader **measure-theoretic packaging theorem** that isolates the abstract hypotheses needed
  for future upstream generalization.

> **Status:** Lean `v4.29.1`, Mathlib only, zero `sorry`/`admit`/axiom, Mathlib-upstream candidate.

## Main objects

```lean
noncomputable def mutualInformation
    (p : ProbabilityMeasure α) (k : Kernel α β) [IsMarkovKernel k] : ℝ

def Kernel.InjectivePriorPushforward (k : Kernel α β) [IsMarkovKernel k] : Prop

noncomputable def channelCapacity (k : Kernel α β) [IsMarkovKernel k] : ℝ
```

`mutualInformation` is defined measure-theoretically as the KL divergence between the joint law
`p ⊗ k` and the product of its marginals.

## Headline theorem

```lean
theorem exists_unique_capacity_achieving_prior_of_finite
    {α β : Type*}
    [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [Nonempty α]
    (k : Kernel α β) [IsMarkovKernel k]
    (h : Kernel.RowMatrixFullRank k) :
    ∃! p : ProbabilityMeasure α, mutualInformation p k = channelCapacity k
```

This theorem lives in `ChannelCapacity.Finite`. It proves uniqueness directly from:

- a finite entropy formula for mutual information;
- strict concavity of output entropy via `Real.strictConcaveOn_negMulLog`;
- linearity of conditional entropy in the prior;
- compactness of `ProbabilityMeasure α` for finite discrete alphabets via Mathlib's
  `MeasureTheory.Measure.Prokhorov`;
- injectivity of the prior pushforward map derived from `Kernel.RowMatrixFullRank`.

## General theorem

```lean
theorem exists_unique_capacity_achieving_prior
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (k : Kernel α β) [IsMarkovKernel k]
    (h : Kernel.InjectivePriorPushforward k)
    (hWC : Kernel.WellConditionedForCapacity k)
    [TopologicalSpace (ProbabilityMeasure α)]
    (hNonempty : (Set.univ : Set (ProbabilityMeasure α)).Nonempty)
    (hCompact : IsCompact (Set.univ : Set (ProbabilityMeasure α)))
    (hUsc : UpperSemicontinuous fun p : ProbabilityMeasure α => mutualInformation p k) :
    ∃! p : ProbabilityMeasure α, mutualInformation p k = channelCapacity k
```

This remains in `ChannelCapacity.Capacity` as the measure-theoretic companion theorem. It is useful
as a staging result, but the finite theorem above is the current Mathlib-facing upstream candidate.

## Counterexample

`ChannelCapacity.Counterexample` is kept as an explicit opt-in import rather than part of the
top-level library surface. It contains the `Fin 6 → Fin 3` permutation channel whose rows are the
six permutations of `(1/2, 1/3, 1/6)`. The file proves:

- the rows are pairwise distinct (`RowSeparating`);
- the prior pushforward map is **not** injective;
- two distinct priors have the same induced output law.

The point of the example is that `RowSeparating` is weaker than
`InjectivePriorPushforward`: pairwise-distinct rows do not by themselves rule out distinct priors
with the same output law.

## File layout

- `ChannelCapacity/Basic.lean`: mutual information and joint/output laws
- `ChannelCapacity/Finite.lean`: finite entropy formula, continuity, strict concavity, and the
  fully discharged finite uniqueness theorem
- `ChannelCapacity/NonDegeneracy.lean`: injective pushforward and row separation
- `ChannelCapacity/StrictConcavity.lean`: strict concavity on probability measures
- `ChannelCapacity/Capacity.lean`: capacity and uniqueness packaging
- `ChannelCapacity/KernelCompositionKullbackLeibler.lean`: generic KL/kernel lemmas with no
  channel-specific dependencies, extracted toward a standalone Mathlib PR
- `ChannelCapacity/Counterexample.lean`: permutation-channel counterexample, not re-exported by
  `ChannelCapacity`

## Sources and precedents

- Mathlib kernel, product-measure, KL-divergence, and semicontinuity libraries; in particular the
  APIs around `ProbabilityTheory.Kernel`, `Measure.compProd`, `InformationTheory.klDiv`,
  `ProbabilityMeasure.continuous_integral_continuousMap`, `Real.strictConcaveOn_negMulLog`, and
  compactness of `ProbabilityMeasure` on compact spaces
- Mathlib finite-simplex and convex-analysis infrastructure, used as structural prior art even
  where the final proof is phrased directly on `ProbabilityMeasure`
- SFT/OmegaFlow as proof-structure prior art for KL strict concavity and compactness packaging;
  this repository does not import it
- C. E. Shannon, "A Mathematical Theory of Communication" (1948)
- I. M. Gel'fand and A. M. Yaglom, work on mutual information for general random objects
- S. Arimoto, "An Algorithm for Computing the Capacity of Arbitrary Discrete Memoryless Channels"
  (1972)
- R. E. Blahut, "Computation of Channel Capacity and Rate-Distortion Functions" (1972)

## License

Dual MIT OR Apache-2.0.
