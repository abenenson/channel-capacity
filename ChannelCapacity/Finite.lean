/- 
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import ChannelCapacity.Capacity
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# ChannelCapacity.Finite

Finite-alphabet capacity-achieving prior uniqueness.

This file specializes the general development to finite measurable alphabets. In that setting,
Shannon entropy gives an explicit formula for mutual information, so continuity and strict
concavity can be proved internally without passing abstract topology or semicontinuity hypotheses
through the public theorem statement.
-/

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal

namespace ChannelCapacity

variable {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]

namespace ProbabilityMeasure

/-- Shannon entropy on a finite measurable alphabet, in nats. -/
noncomputable def entropy (μ : ProbabilityMeasure α) : ℝ :=
  ∑ a, Real.negMulLog ((μ.toMeasure {a}).toReal)

end ProbabilityMeasure

namespace Kernel

/-- A concrete finite non-degeneracy condition: the row matrix has trivial kernel over `ℝ`. -/
def RowMatrixFullRank (k : Kernel α β) : Prop :=
  Function.Injective fun w : α → ℝ =>
    fun b => ∑ a, w a * (k a {b}).toReal

end Kernel

section DiscreteKL

omit [Fintype α] in
theorem toMeasure_eq_count_withDensity (μ : ProbabilityMeasure α) :
    [Countable α] → μ.toMeasure = Measure.count.withDensity (fun a => μ.toMeasure {a}) := by
  intro _instCountable
  ext s hs
  rw [MeasureTheory.withDensity_apply _ hs, ← MeasureTheory.lintegral_indicator hs,
    MeasureTheory.lintegral_count]
  simpa using (μ.toMeasure.tsum_indicator_apply_singleton s hs).symm

omit [Fintype α] in
theorem rnDeriv_count_ae (μ : ProbabilityMeasure α) :
    [Countable α] →
      μ.toMeasure.rnDeriv Measure.count =ᵐ[Measure.count] fun a => μ.toMeasure {a} := by
  intro _instCountable
  have hcount :
      Measure.count.withDensity (fun a : α => μ.toMeasure {a}) = μ.toMeasure :=
    (toMeasure_eq_count_withDensity (μ := μ)).symm
  simpa [hcount] using
    (Measure.rnDeriv_withDensity
      (ν := Measure.count)
      (f := fun a : α => μ.toMeasure {a})
      (measurable_of_countable (fun a : α => μ.toMeasure {a})))

omit [Fintype α] [MeasurableSingletonClass α] in
theorem klFun_singletonMass (μ : ProbabilityMeasure α) (a : α) :
    InformationTheory.klFun ((μ.toMeasure {a}).toReal) =
      1 - (μ.toMeasure {a}).toReal - Real.negMulLog ((μ.toMeasure {a}).toReal) := by
  rw [InformationTheory.klFun, Real.negMulLog]
  ring

theorem toReal_klDiv_count (μ : ProbabilityMeasure α) :
    (InformationTheory.klDiv μ.toMeasure Measure.count).toReal =
      (Fintype.card α : ℝ) - 1 - ProbabilityMeasure.entropy μ := by
  let _instCountable : Countable α := by infer_instance
  have h_ac : μ.toMeasure ≪ Measure.count := by
    rw [toMeasure_eq_count_withDensity (μ := μ)]
    exact withDensity_absolutelyContinuous _ _
  have h_rn : ∀ a : α, μ.toMeasure.rnDeriv Measure.count a = μ.toMeasure {a} := by
    simpa using (Measure.ae_count_iff.mp (rnDeriv_count_ae (μ := μ)))
  rw [InformationTheory.toReal_klDiv_eq_integral_klFun h_ac, MeasureTheory.integral_count]
  simp_rw [h_rn, klFun_singletonMass (μ := μ)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hprob_enn : ∑ a, μ.toMeasure {a} = (1 : ℝ≥0∞) := by
    calc
      ∑ a, μ.toMeasure {a} = ∑' a : α, μ.toMeasure {a} := by
        rw [← tsum_fintype
          (L := SummationFilter.unconditional _)
          (f := fun a : α => μ.toMeasure {a})]
      _ = μ.toMeasure Set.univ := by
        simpa only [Set.indicator_univ] using
          μ.toMeasure.tsum_indicator_apply_singleton Set.univ MeasurableSet.univ
      _ = 1 := by exact μ.prop.measure_univ
  have hprob : ∑ a, (μ.toMeasure {a}).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun a _ha => measure_ne_top _ _), hprob_enn, ENNReal.toReal_one]
  rw [ProbabilityMeasure.entropy, hprob, Finset.card_univ]
  ring

theorem sum_toReal_singletonMass (μ : ProbabilityMeasure α) :
    ∑ a, (μ.toMeasure {a}).toReal = 1 := by
  have hprob_enn : ∑ a, μ.toMeasure {a} = (1 : ℝ≥0∞) := by
    calc
      ∑ a, μ.toMeasure {a} = ∑' a : α, μ.toMeasure {a} := by
        rw [← tsum_fintype
          (L := SummationFilter.unconditional _)
          (f := fun a : α => μ.toMeasure {a})]
      _ = μ.toMeasure Set.univ := by
        simpa only [Set.indicator_univ] using
          μ.toMeasure.tsum_indicator_apply_singleton Set.univ MeasurableSet.univ
      _ = 1 := by exact μ.prop.measure_univ
  rw [← ENNReal.toReal_sum (fun a _ha => measure_ne_top _ _), hprob_enn, ENNReal.toReal_one]

end DiscreteKL

section EntropyFormula

/-- The probability measure associated to a kernel row. -/
noncomputable def Kernel.rowProbabilityMeasure (k : Kernel α β) [IsMarkovKernel k] (a : α) :
    ProbabilityMeasure β :=
  ⟨k a, ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure (κ := k) a⟩

/-- Row entropy for a finite Markov kernel. -/
noncomputable def Kernel.rowEntropy (k : Kernel α β) [IsMarkovKernel k] (a : α) : ℝ :=
  ProbabilityMeasure.entropy (Kernel.rowProbabilityMeasure k a)

/-- Conditional output entropy, linear in the prior. -/
noncomputable def conditionalEntropy (p : ProbabilityMeasure α) (k : Kernel α β)
    [IsMarkovKernel k] : ℝ :=
  ∑ a, (p.toMeasure {a}).toReal * Kernel.rowEntropy k a

omit [Fintype α] [MeasurableSingletonClass α] in
theorem absolutelyContinuous_count (μ : ProbabilityMeasure α) [Countable α] :
    μ.toMeasure ≪ Measure.count := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero => ?_
  rw [Measure.count_eq_zero_iff] at hs_zero
  simp [hs_zero]

omit [Fintype β] in
theorem outputPrior_apply_singleton (k : Kernel α β) [IsMarkovKernel k]
    (p : ProbabilityMeasure α) (b : β) :
    (outputPrior k p).toMeasure {b} = ∑ a, p.toMeasure {a} * k a {b} := by
  calc
    (outputPrior k p).toMeasure {b}
      = (Measure.sum fun a : α => p.toMeasure {a} • k a) {b} := by
          rw [outputPrior_toMeasure, Measure.comp_eq_sum_of_countable]
    _ = ∑' a : α, (p.toMeasure {a} • k a) {b} := by
          rw [Measure.sum_apply _ (measurableSet_singleton b)]
    _ = ∑' a : α, p.toMeasure {a} * k a {b} := by
          simp [Measure.smul_apply]
    _ = ∑ a, p.toMeasure {a} * k a {b} := by
          rw [tsum_fintype]

omit [Fintype β] in
theorem klDiv_count_ne_top (μ : ProbabilityMeasure β) [Finite β] :
    InformationTheory.klDiv μ.toMeasure Measure.count ≠ ∞ := by
  let _instFintypeβ : Fintype β := Fintype.ofFinite β
  let _instCountableβ : Countable β := by infer_instance
  have h_ac : μ.toMeasure ≪ Measure.count := absolutelyContinuous_count μ
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac h_ac, MeasureTheory.lintegral_count,
    tsum_fintype]
  exact ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top

omit [Fintype α] [Fintype β] in
theorem joint_klDiv_count_ne_top (k : Kernel α β) [IsMarkovKernel k] [Finite α] [Finite β]
    (p : ProbabilityMeasure α) :
    InformationTheory.klDiv
        (jointLaw k p).toMeasure
        (p.toMeasure ⊗ₘ Kernel.const α Measure.count) ≠ ∞ := by
  let _instFintypeα : Fintype α := Fintype.ofFinite α
  let _instFintypeβ : Fintype β := Fintype.ofFinite β
  let _instCountableα : Countable α := by infer_instance
  let _instCountableβ : Countable β := by infer_instance
  have h_rows : ∀ᵐ a ∂p.toMeasure, k a ≪ Measure.count := by
    exact ae_of_all _ fun a => absolutelyContinuous_count (Kernel.rowProbabilityMeasure k a)
  have h_kl :
      InformationTheory.klDiv
          (jointLaw k p).toMeasure
          (p.toMeasure ⊗ₘ Kernel.const α Measure.count) =
        ∫⁻ a, InformationTheory.klDiv (k a) Measure.count ∂p.toMeasure := by
    rw [jointLaw_toMeasure]
    apply ProbabilityTheory.klDiv_compProd_right
    exact Measure.AbsolutelyContinuous.compProd_right h_rows
  rw [h_kl, MeasureTheory.lintegral_fintype]
  exact ENNReal.sum_ne_top.2 fun a _ha =>
    ENNReal.mul_ne_top
      (klDiv_count_ne_top (Kernel.rowProbabilityMeasure k a))
      (measure_ne_top _ _)

omit [Fintype β] in
theorem toReal_joint_klDiv_count (k : Kernel α β) [IsMarkovKernel k] [Finite β]
    (p : ProbabilityMeasure α) :
    (InformationTheory.klDiv
        (jointLaw k p).toMeasure
        (p.toMeasure ⊗ₘ Kernel.const α Measure.count)).toReal =
      ∑ a, (p.toMeasure {a}).toReal *
        (InformationTheory.klDiv (k a) Measure.count).toReal := by
  let _instFintypeβ : Fintype β := Fintype.ofFinite β
  let _instCountableα : Countable α := by infer_instance
  let _instCountableβ : Countable β := by infer_instance
  have h_rows : ∀ᵐ a ∂p.toMeasure, k a ≪ Measure.count := by
    exact ae_of_all _ fun a => absolutelyContinuous_count (Kernel.rowProbabilityMeasure k a)
  have h_kl :
      InformationTheory.klDiv
          (jointLaw k p).toMeasure
          (p.toMeasure ⊗ₘ Kernel.const α Measure.count) =
        ∫⁻ a, InformationTheory.klDiv (k a) Measure.count ∂p.toMeasure := by
    apply ProbabilityTheory.klDiv_compProd_right
    exact Measure.AbsolutelyContinuous.compProd_right h_rows
  rw [h_kl]
  have hsum :
      ∫⁻ a, InformationTheory.klDiv (k a) Measure.count ∂p.toMeasure =
        ∑ a, InformationTheory.klDiv (k a) Measure.count * p.toMeasure {a} := by
    simpa [mul_comm] using
      (MeasureTheory.lintegral_fintype
        (μ := p.toMeasure)
        (f := fun a : α => InformationTheory.klDiv (k a) Measure.count))
  have hsum_toReal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_sum] at hsum_toReal
  · simpa [ENNReal.toReal_mul, Kernel.rowProbabilityMeasure, toReal_klDiv_count, mul_comm] using
      hsum_toReal
  · intro a _ha
    exact ENNReal.mul_ne_top
      (klDiv_count_ne_top (Kernel.rowProbabilityMeasure k a))
      (measure_ne_top _ _)

theorem mutualInformation_eq_entropy_outputPrior_sub_conditionalEntropy
    (k : Kernel α β) [IsMarkovKernel k] [Finite β] (p : ProbabilityMeasure α) :
    mutualInformation p k =
      ProbabilityMeasure.entropy (outputPrior k p) - conditionalEntropy p k := by
  let _instCountableα : Countable α := by infer_instance
  let _instCountableβ : Countable β := by infer_instance
  let _instDiscreteMeasurableα : DiscreteMeasurableSpace α := by infer_instance
  let _instStandardBorelα : StandardBorelSpace α := by infer_instance
  let _instNonemptyα : Nonempty α := p.nonempty
  have h_chain :=
    klDiv_mutualInformation_chain (k := k) (p := p) (ν := Measure.count)
  have h_left_fin : InformationTheory.klDiv
      (jointLaw k p).toMeasure
      (p.toMeasure ⊗ₘ Kernel.const α Measure.count) ≠ ∞ :=
    joint_klDiv_count_ne_top k p
  have h_out_fin : InformationTheory.klDiv (outputPrior k p).toMeasure Measure.count ≠ ∞ :=
    klDiv_count_ne_top (outputPrior k p)
  have h_mi_fin :
      InformationTheory.klDiv
          (jointLaw k p).toMeasure
          (independentJointLaw k p).toMeasure ≠ ∞ := by
    intro h_top
    have h_left_top :
        InformationTheory.klDiv
            (jointLaw k p).toMeasure
            (p.toMeasure ⊗ₘ Kernel.const α Measure.count) = ∞ := by
      calc
        InformationTheory.klDiv
            (jointLaw k p).toMeasure
            (p.toMeasure ⊗ₘ Kernel.const α Measure.count)
            =
              InformationTheory.klDiv
                (jointLaw k p).toMeasure
                (independentJointLaw k p).toMeasure +
                  InformationTheory.klDiv (outputPrior k p).toMeasure Measure.count := h_chain
        _ = ∞ + InformationTheory.klDiv (outputPrior k p).toMeasure Measure.count := by rw [h_top]
        _ = ∞ := by simp
    exact h_left_fin h_left_top
  have h_chain_real : (InformationTheory.klDiv
      (jointLaw k p).toMeasure
      (p.toMeasure ⊗ₘ Kernel.const α Measure.count)).toReal =
        mutualInformation p k +
          (InformationTheory.klDiv (outputPrior k p).toMeasure Measure.count).toReal := by
    have h_chain_real' := congrArg ENNReal.toReal h_chain
    rw [ENNReal.toReal_add h_mi_fin h_out_fin] at h_chain_real'
    simpa [mutualInformation, jointLaw_toMeasure, independentJointLaw_toMeasure,
      outputPrior_toMeasure]
      using h_chain_real'
  have h_row_kl :
      ∀ a : α,
        (InformationTheory.klDiv (k a) Measure.count).toReal =
          (Fintype.card β : ℝ) - 1 - Kernel.rowEntropy k a := by
    intro a
    simpa [Kernel.rowEntropy, Kernel.rowProbabilityMeasure] using
      (toReal_klDiv_count (Kernel.rowProbabilityMeasure k a))
  rw [toReal_joint_klDiv_count, toReal_klDiv_count] at h_chain_real
  simp_rw [h_row_kl] at h_chain_real
  rw [conditionalEntropy, ProbabilityMeasure.entropy]
  rw [ProbabilityMeasure.entropy] at h_chain_real
  simp_rw [mul_sub, mul_one] at h_chain_real
  have hprob := sum_toReal_singletonMass p
  have hcoeff :
      ∑ x, ((p.toMeasure {x}).toReal * (Fintype.card β : ℝ) - (p.toMeasure {x}).toReal) =
        (Fintype.card β : ℝ) - 1 := by
    calc
      ∑ x, ((p.toMeasure {x}).toReal * (Fintype.card β : ℝ) - (p.toMeasure {x}).toReal) =
          (∑ x, (p.toMeasure {x}).toReal * (Fintype.card β : ℝ)) -
            ∑ x, (p.toMeasure {x}).toReal := by
              rw [Finset.sum_sub_distrib]
      _ = (∑ x, (p.toMeasure {x}).toReal) * (Fintype.card β : ℝ) -
            ∑ x, (p.toMeasure {x}).toReal := by
              rw [Finset.sum_mul]
      _ = 1 * (Fintype.card β : ℝ) - 1 := by rw [hprob]
      _ = (Fintype.card β : ℝ) - 1 := by ring
  have hsplit :
      ∑ x, ((p.toMeasure {x}).toReal * (Fintype.card β : ℝ) - (p.toMeasure {x}).toReal -
          (p.toMeasure {x}).toReal * Kernel.rowEntropy k x) =
        ∑ x, ((p.toMeasure {x}).toReal * (Fintype.card β : ℝ) - (p.toMeasure {x}).toReal) -
          ∑ x, (p.toMeasure {x}).toReal * Kernel.rowEntropy k x := by
    rw [Finset.sum_sub_distrib]
  rw [hsplit, hcoeff] at h_chain_real
  ring_nf at h_chain_real
  have h_target :
      mutualInformation p k =
        ∑ a, Real.negMulLog ((outputPrior k p).toMeasure {a}).toReal -
          ∑ a, (p.toMeasure {a}).toReal * Kernel.rowEntropy k a := by
    linarith [h_chain_real]
  simpa using h_target

end EntropyFormula

end ChannelCapacity
