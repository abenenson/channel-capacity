# channel-capacity

Lean 4 formalization of **Shannon capacity-achieving prior uniqueness** for a Markov kernel, with
the correct non-degeneracy surface centered on injectivity of the prior-to-output map.

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

## Main theorem

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

The topological existence argument is packaged separately. Uniqueness is derived internally from
`InjectivePriorPushforward` together with the measure-theoretic bundle
`WellConditionedForCapacity`, so no standalone strict-concavity hypothesis appears in the final
statement.

## Counterexample

`ChannelCapacity/Counterexample.lean` contains the `Fin 6 → Fin 3` permutation channel whose rows
are the six permutations of `(1/2, 1/3, 1/6)`. The file proves:

- the rows are pairwise distinct (`RowSeparating`);
- the prior pushforward map is **not** injective;
- two distinct priors have the same induced output law.

The point of the example is that `RowSeparating` is weaker than
`InjectivePriorPushforward`: pairwise-distinct rows do not by themselves rule out distinct priors
with the same output law.

## File layout

- `ChannelCapacity/Basic.lean`: mutual information and joint/output laws
- `ChannelCapacity/NonDegeneracy.lean`: injective pushforward and row separation
- `ChannelCapacity/StrictConcavity.lean`: strict concavity on probability measures
- `ChannelCapacity/Capacity.lean`: capacity and uniqueness packaging
- `ChannelCapacity/Counterexample.lean`: permutation-channel counterexample

## Sources and precedents

- Mathlib kernel, product-measure, KL-divergence, and semicontinuity libraries; in particular the
  APIs around `ProbabilityTheory.Kernel`, `Measure.compProd`, `InformationTheory.klDiv`, and
  `UpperSemicontinuousOn.exists_isMaxOn`
- C. E. Shannon, "A Mathematical Theory of Communication" (1948)
- I. M. Gel'fand and A. M. Yaglom, work on mutual information for general random objects
- S. Arimoto, "An Algorithm for Computing the Capacity of Arbitrary Discrete Memoryless Channels"
  (1972)
- R. E. Blahut, "Computation of Channel Capacity and Rate-Distortion Functions" (1972)

## License

Dual MIT OR Apache-2.0.
