/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasCausal.BlockInformation
import CapacityAtlasForMathlib.InformationTheory.CodingConverse
import CapacityAtlasForMathlib.InformationTheory.FiniteChannelOptimization

open scoped BigOperators
open CapacityAtlas

namespace CapacityAtlasCausal

attribute [local instance] Classical.propDecidable

variable {X S Y : Type*} [Fintype X] [Fintype S] [Fintype Y] [Nonempty X]

/-- Fano bounds the message count for every deterministic causal code. -/
theorem blockCode_log_messageCount_le (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) {blocklength : ℕ}
    (code : CausalState.BlockCode state channels blocklength) :
    Real.log code.messageCount ≤
      (blocklength : ℝ) * (CausalState.strategyChannel state channels).informationCapacityBits *
        Real.log 2 + Real.log 2 +
          code.averageErrorProbability * Real.log code.messageCount := by
  letI : Nonempty (Fin code.messageCount) := Fin.pos_iff_nonempty.mp code.messageCount_pos
  let messageChannel := (CausalState.blockChannel state channels blocklength).encoded code.encode
  have hfano := messageChannel.fano_uniform code.decode
  change Real.log (Fintype.card (Fin code.messageCount)) ≤
    messageChannel.mutualInformation (FiniteDistribution.uniform (Fin code.messageCount)) +
      Real.log 2 + code.averageErrorProbability *
        Real.log (Fintype.card (Fin code.messageCount)) at hfano
  have hmutual := block_mutualInformation_le state channels blocklength code.encode
    (FiniteDistribution.uniform (Fin code.messageCount))
  simp only [Fintype.card_fin] at hfano
  dsimp [messageChannel] at hfano
  linarith

/-- The rate bound is normalized per physical channel use. -/
theorem blockCode_rate_bound (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) {blocklength : ℕ}
    (code : CausalState.BlockCode state channels blocklength) (hblocklength : 0 < blocklength) :
    (1 - code.averageErrorProbability) * code.rate ≤
      (CausalState.strategyChannel state channels).informationCapacityBits +
        (blocklength : ℝ)⁻¹ := by
  have hlogBound := blockCode_log_messageCount_le state channels code
  have hblocklengthReal : 0 < (blocklength : ℝ) := by exact_mod_cast hblocklength
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hrearranged :
      (1 - code.averageErrorProbability) * Real.log code.messageCount ≤
        (blocklength : ℝ) * (CausalState.strategyChannel state channels).informationCapacityBits *
          Real.log 2 + Real.log 2 := by
    linarith
  unfold CausalState.BlockCode.rate Real.logb
  calc
    (1 - code.averageErrorProbability) *
        (Real.log code.messageCount / Real.log 2 / (blocklength : ℝ)) =
        ((1 - code.averageErrorProbability) * Real.log code.messageCount) /
          ((blocklength : ℝ) * Real.log 2) := by
      field_simp [hblocklengthReal.ne', hlogTwo.ne']
    _ ≤ ((blocklength : ℝ) *
          (CausalState.strategyChannel state channels).informationCapacityBits * Real.log 2 +
          Real.log 2) / ((blocklength : ℝ) * Real.log 2) :=
      div_le_div_of_nonneg_right hrearranged (mul_pos hblocklengthReal hlogTwo).le
    _ = (CausalState.strategyChannel state channels).informationCapacityBits +
        (blocklength : ℝ)⁻¹ := by
      field_simp [hblocklengthReal.ne', hlogTwo.ne']

/-- Past state dependence cannot increase the achievable rate beyond strategy capacity. -/
theorem achievableRate_le_strategyCapacity (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) {rate : ℝ}
    (hachievable : CausalState.AchievableRate state channels rate) :
    rate ≤ (CausalState.strategyChannel state channels).informationCapacityBits := by
  let capacity := (CausalState.strategyChannel state channels).informationCapacityBits
  by_contra hrateCapacity
  have hstrict : capacity < rate := lt_of_not_ge hrateCapacity
  have hcapacityNonnegative : 0 ≤ capacity :=
    (CausalState.strategyChannel state channels).informationCapacityBits_nonnegative
  have hratePositive : 0 < rate := lt_of_le_of_lt hcapacityNonnegative hstrict
  let gap := rate - capacity
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hgapRate : gap ≤ rate := by dsimp [gap]; linarith
  let ε := gap / (4 * rate)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεlt : ε < 1 := by
    apply (div_lt_one (mul_pos (by norm_num) hratePositive)).2
    linarith
  have hεRate : ε * rate = gap / 4 := by
    dsimp [ε]
    field_simp [hratePositive.ne']
  obtain ⟨firstBlocklength, hfirstPositive, hcodes⟩ := hachievable ε hε
  obtain ⟨blocklength, hblocklengthLarge⟩ :=
    exists_nat_gt (max (firstBlocklength : ℝ) (4 / gap))
  have hfirstBlocklength : firstBlocklength ≤ blocklength := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hblocklengthLarge).le
  have hblocklengthPositive : 0 < blocklength :=
    lt_of_lt_of_le hfirstPositive hfirstBlocklength
  have hblocklengthReal : 0 < (blocklength : ℝ) := by exact_mod_cast hblocklengthPositive
  have hfourDiv : 4 / gap < (blocklength : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hblocklengthLarge
  have hfourProduct : 4 < (blocklength : ℝ) * gap := (div_lt_iff₀ hgap).mp hfourDiv
  have hinversePositive : 0 < (blocklength : ℝ)⁻¹ := inv_pos.mpr hblocklengthReal
  have hinverseProduct : (blocklength : ℝ) * (blocklength : ℝ)⁻¹ = 1 :=
    mul_inv_cancel₀ hblocklengthReal.ne'
  have hinverseSmall : (blocklength : ℝ)⁻¹ < gap / 4 := by nlinarith
  obtain ⟨code, herror, hcodeRate⟩ := hcodes blocklength hfirstBlocklength
  have hfactorNonnegative : 0 ≤ 1 - code.averageErrorProbability := by linarith
  have hlower :
      (1 - ε) * rate ≤ (1 - code.averageErrorProbability) * code.rate := by
    calc
      (1 - ε) * rate ≤ (1 - code.averageErrorProbability) * rate :=
        mul_le_mul_of_nonneg_right (by linarith) hratePositive.le
      _ ≤ (1 - code.averageErrorProbability) * code.rate :=
        mul_le_mul_of_nonneg_left hcodeRate hfactorNonnegative
  have hupper := blockCode_rate_bound state channels code hblocklengthPositive
  have hcombined : (1 - ε) * rate ≤ capacity + (blocklength : ℝ)⁻¹ := hlower.trans hupper
  dsimp [gap] at hgap hεRate hinverseSmall
  nlinarith

/-- Shannon strategy coding and the causal converse identify operational capacity. -/
theorem causalStateCapacity (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) :
    CausalState.operationalCapacityBits state channels =
      (CausalState.strategyChannel state channels).informationCapacityBits := by
  let strategy := CausalState.strategyChannel state channels
  have hzero : CausalState.AchievableRate state channels 0 :=
    CausalState.achievableRate_of_strategyChannel (strategy.achievableRate_of_nonpos le_rfl)
  have hbounded : BddAbove {rate | CausalState.AchievableRate state channels rate} :=
    ⟨strategy.informationCapacityBits, fun _ hrate ↦
      achievableRate_le_strategyCapacity state channels hrate⟩
  unfold CausalState.operationalCapacityBits
  apply le_antisymm
  · exact csSup_le ⟨0, hzero⟩ (fun _ hrate ↦
      achievableRate_le_strategyCapacity state channels hrate)
  · apply le_of_forall_lt_imp_le_of_dense
    intro rate hrate
    exact le_csSup hbounded (CausalState.achievableRate_of_strategyChannel
      (strategy.achievableRate_of_lt_informationCapacityBits hrate))

/-- The finite strategy alphabet admits an input attaining causal operational capacity. -/
theorem exists_capacityAchieving_strategy (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) :
    ∃ input : FiniteDistribution (S → X),
      (CausalState.strategyChannel state channels).mutualInformationBits input =
        CausalState.operationalCapacityBits state channels := by
  rw [causalStateCapacity state channels]
  exact (CausalState.strategyChannel state channels).exists_capacityAchieving_input

end CapacityAtlasCausal
