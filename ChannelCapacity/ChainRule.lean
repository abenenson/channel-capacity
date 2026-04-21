/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import ChannelCapacity.Basic

import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Posterior
import Mathlib.Probability.Kernel.RadonNikodym

/-!
# ChannelCapacity.ChainRule

Bridge lemmas relating mutual information to KL divergences against fixed output references.

The main theorem rewrites the KL divergence from the joint law `p ⊗ k` to the product
`p ⊗ const ν` as the mutual information plus the KL divergence of the induced output law
against `ν`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ChannelCapacity

open InformationTheory

lemma klDiv_map_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ ν : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  rw [klDiv_eq_lintegral_klFun, klDiv_eq_lintegral_klFun]
  by_cases hμν : μ ≪ ν
  · have hmap : μ.map e ≪ ν.map e := e.measurableEmbedding.absolutelyContinuous_map hμν
    simp only [hμν, hmap, ↓reduceIte]
    rw [e.measurableEmbedding.lintegral_map]
    refine lintegral_congr_ae ?_
    filter_upwards [e.measurableEmbedding.rnDeriv_map μ ν] with x hx
    simp [hx]
  · have hmap : ¬ μ.map e ≪ ν.map e := by
      intro h
      have h' := e.symm.measurableEmbedding.absolutelyContinuous_map h
      exact hμν (by simpa using h')
    simp [hμν, hmap]

theorem rnDeriv_compProd_right
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    {μ : Measure α} {κ η : Kernel α β}
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η] fun p ↦ κ.rnDeriv η p.1 p.2 := by
  have hs : μ ⊗ₘ κ.singularPart η ⟂ₘ μ ⊗ₘ η :=
    MeasureTheory.Measure.MutuallySingular.compProd_of_right _ _
      (.of_forall <| Kernel.mutuallySingular_singularPart _ _)
  have hadd :
      μ ⊗ₘ κ = μ ⊗ₘ κ.singularPart η
        + (μ ⊗ₘ η).withDensity (fun p ↦ κ.rnDeriv η p.1 p.2) := by
    calc
      μ ⊗ₘ κ
        = μ ⊗ₘ (Kernel.withDensity η (Kernel.rnDeriv κ η) + Kernel.singularPart κ η) := by
            rw [Kernel.rnDeriv_add_singularPart]
      _ = μ ⊗ₘ Kernel.withDensity η (Kernel.rnDeriv κ η) + μ ⊗ₘ Kernel.singularPart κ η := by
            rw [Measure.compProd_add_right]
      _ = (μ ⊗ₘ η).withDensity (fun p ↦ κ.rnDeriv η p.1 p.2)
          + μ ⊗ₘ Kernel.singularPart κ η := by
            rw [Measure.compProd_withDensity]
            exact κ.measurable_rnDeriv η
      _ = μ ⊗ₘ Kernel.singularPart κ η
          + (μ ⊗ₘ η).withDensity (fun p ↦ κ.rnDeriv η p.1 p.2) := by
            rw [add_comm]
  exact (Measure.eq_rnDeriv (κ.measurable_rnDeriv η) hs hadd).symm

theorem klDiv_compProd_right
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    {μ : Measure α} {κ η : Kernel α β}
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
  have h_kernel_ac : ∀ᵐ a ∂μ, κ a ≪ η a :=
    (Measure.absolutelyContinuous_compProd_right_iff).mp h_ac
  have hmeas :
      Measurable
        (fun p : α × β ↦ ENNReal.ofReal (klFun ((κ.rnDeriv η p.1 p.2).toReal))) := by
    exact (measurable_klFun.comp (κ.measurable_rnDeriv η).ennreal_toReal).ennreal_ofReal
  rw [klDiv_eq_lintegral_klFun_of_ac h_ac]
  calc
    ∫⁻ p, ENNReal.ofReal (klFun (((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p).toReal)) ∂μ ⊗ₘ η
      = ∫⁻ p, ENNReal.ofReal (klFun ((κ.rnDeriv η p.1 p.2).toReal)) ∂μ ⊗ₘ η := by
          refine lintegral_congr_ae ?_
          exact (rnDeriv_compProd_right (μ := μ) (κ := κ) (η := η)).mono fun p hp => by
            simp [hp]
    _ = ∫⁻ a, ∫⁻ b, ENNReal.ofReal (klFun ((κ.rnDeriv η a b).toReal)) ∂η a ∂μ := by
          rw [Measure.lintegral_compProd hmeas]
    _ = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [h_kernel_ac] with a ha
          rw [klDiv_eq_lintegral_klFun_of_ac ha]
          refine lintegral_congr_ae ?_
          exact (κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := a)).mono fun x hx => by
            simp [hx]

theorem klDiv_mutualInformation_chain
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace α] [Nonempty α]
    (k : Kernel α β) [IsMarkovKernel k] (p : ProbabilityMeasure α) (ν : Measure β)
    [IsFiniteMeasure ν] :
    klDiv (jointLaw k p).toMeasure (p.toMeasure ⊗ₘ Kernel.const α ν) =
      klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure +
        klDiv (outputPrior k p).toMeasure ν := by
  let e : (α × β) ≃ᵐ (β × α) := MeasurableEquiv.prodComm
  let post : Kernel β α := k†p.toMeasure
  have hswap_joint :
      ((jointLaw k p).toMeasure).map e = (outputPrior k p).toMeasure ⊗ₘ post := by
    simpa [jointLaw_toMeasure, outputPrior_toMeasure, e, post] using
      (ProbabilityTheory.compProd_posterior_eq_map_swap (κ := k) (μ := p.toMeasure)).symm
  have hswap_const :
      (p.toMeasure ⊗ₘ Kernel.const α ν).map e = ν ⊗ₘ Kernel.const β p.toMeasure := by
    simpa [e] using
      (by
        rw [Measure.compProd_const, Measure.prod_swap, ← Measure.compProd_const] :
          (p.toMeasure ⊗ₘ Kernel.const α ν).map Prod.swap =
            ν ⊗ₘ Kernel.const β p.toMeasure)
  have hswap_indep :
      ((independentJointLaw k p).toMeasure).map e =
        (outputPrior k p).toMeasure ⊗ₘ Kernel.const β p.toMeasure := by
    simpa [independentJointLaw_toMeasure, e] using
      (by
        rw [independentJointLaw_toMeasure, Measure.compProd_const, Measure.prod_swap,
          ← Measure.compProd_const] :
          (independentJointLaw k p).toMeasure.map Prod.swap =
            (outputPrior k p).toMeasure ⊗ₘ Kernel.const β p.toMeasure)
  have hleft :
      klDiv (jointLaw k p).toMeasure (p.toMeasure ⊗ₘ Kernel.const α ν) =
        klDiv ((outputPrior k p).toMeasure ⊗ₘ post) (ν ⊗ₘ Kernel.const β p.toMeasure) := by
    calc
      klDiv (jointLaw k p).toMeasure (p.toMeasure ⊗ₘ Kernel.const α ν) =
          klDiv (((jointLaw k p).toMeasure).map e) ((p.toMeasure ⊗ₘ Kernel.const α ν).map e) := by
            symm
            exact klDiv_map_measurableEquiv e (jointLaw k p).toMeasure
              (p.toMeasure ⊗ₘ Kernel.const α ν)
      _ = klDiv ((outputPrior k p).toMeasure ⊗ₘ post) (ν ⊗ₘ Kernel.const β p.toMeasure) := by
        rw [hswap_joint, hswap_const]
  have hright :
      klDiv ((outputPrior k p).toMeasure ⊗ₘ post)
          ((outputPrior k p).toMeasure ⊗ₘ Kernel.const β p.toMeasure) =
        klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure := by
    calc
      klDiv ((outputPrior k p).toMeasure ⊗ₘ post)
          ((outputPrior k p).toMeasure ⊗ₘ Kernel.const β p.toMeasure) =
          klDiv (((jointLaw k p).toMeasure).map e)
            (((independentJointLaw k p).toMeasure).map e) := by
            rw [hswap_joint, hswap_indep]
      _ = klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure := by
        exact klDiv_map_measurableEquiv e (jointLaw k p).toMeasure
          (independentJointLaw k p).toMeasure
  calc
    klDiv (jointLaw k p).toMeasure (p.toMeasure ⊗ₘ Kernel.const α ν) =
        klDiv ((outputPrior k p).toMeasure ⊗ₘ post) (ν ⊗ₘ Kernel.const β p.toMeasure) := hleft
    _ = klDiv (outputPrior k p).toMeasure ν +
          klDiv ((outputPrior k p).toMeasure ⊗ₘ post)
            ((outputPrior k p).toMeasure ⊗ₘ Kernel.const β p.toMeasure) := by
          rw [InformationTheory.klDiv_compProd_eq_add]
    _ = klDiv (outputPrior k p).toMeasure ν +
          klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure := by
          rw [hright]
    _ = klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure +
          klDiv (outputPrior k p).toMeasure ν := by
          rw [add_comm]

end ChannelCapacity
