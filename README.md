# channel-capacity

Lean 4 formalization of **Shannon capacity-achieving prior uniqueness** for a Markov kernel, with
the correct non-degeneracy surface centered on injectivity of the prior-to-output map.

> **Status:** Lean `v4.29.1`, Mathlib only, zero sorries intended, Mathlib-upstream candidate.

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
    (k : Kernel α β) [IsMarkovKernel k] (h : k.InjectivePriorPushforward)
    [TopologicalSpace (ProbabilityMeasure α)]
    (hNonempty : (Set.univ : Set (ProbabilityMeasure α)).Nonempty)
    (hCompact : IsCompact (Set.univ : Set (ProbabilityMeasure α)))
    (hUsc : UpperSemicontinuous fun p : ProbabilityMeasure α => mutualInformation p k)
    (hStrict : k.StrictlyConcaveMutualInformation h) :
    ∃! p : ProbabilityMeasure α, mutualInformation p k = channelCapacity k
```

The topological existence argument is fully packaged. The strict-concavity hypothesis is expressed
on the simplex of probability measures via explicit convex combinations.

## Counterexample

`ChannelCapacity/Counterexample.lean` contains the `Fin 6 → Fin 3` permutation channel whose rows
are the six permutations of `(1/2, 1/3, 1/6)`. The file proves:

- the rows are pairwise distinct (`RowSeparating`);
- the prior pushforward map is **not** injective;
- two distinct priors have the same induced output law.

This records the v2 correction: `RowSeparating` is weaker than the right hypothesis
`InjectivePriorPushforward`.

## File layout

- `ChannelCapacity/Basic.lean`: mutual information and joint/output laws
- `ChannelCapacity/NonDegeneracy.lean`: injective pushforward and row separation
- `ChannelCapacity/StrictConcavity.lean`: strict concavity on probability measures
- `ChannelCapacity/Capacity.lean`: capacity and uniqueness packaging
- `ChannelCapacity/Counterexample.lean`: permutation-channel counterexample and toy discharge

## Sources and precedents

- Mathlib:
  `ProbabilityTheory.Kernel`, `Measure.compProd`, `InformationTheory.klDiv`,
  `UpperSemicontinuousOn.exists_isMaxOn`
- OmegaFlow:
  the probability-measure convex combination interface and compactness/uniqueness packaging were
  rewritten here in a smaller Mathlib-idiomatic form, following the same overall proof pattern
  while avoiding the PathSpace/kernel-category abstraction layer

## License

Dual MIT OR Apache-2.0.
