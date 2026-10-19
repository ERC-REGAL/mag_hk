import MagHK.PotentialInfinity
import Mathlib.Analysis.Asymptotics.Lemmas

/-! The displayed inverse-radius remainder follows from the actual bounded
profile. In fact its first correction coefficient is exactly minus nine. -/
noncomputable section
namespace MagHK.PotentialAsymptotics
open MagHK.Noninteracting MagHK.RadialEndpoints MagHK.PotentialInfinity Filter
open scoped Topology

theorem radius_mul_square_error (r : ℝ) :
    r * (profileH r ^ 2 - 1) = -profileH r * (Real.sqrt (1 + r ^ 2))⁻¹ := by
  have hs : 0 < Real.sqrt (1 + r ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs2 := Real.sq_sqrt (show 0 ≤ 1 + r ^ 2 by positivity)
  rw [profileH_square]
  unfold profileH
  field_simp
  rw [hs2]
  ring

theorem radius_mul_square_error_tendsto :
    Tendsto (fun r : ℝ => r * (profileH r ^ 2 - 1)) atTop (𝓝 0) := by
  have h := profileH_tendsto_atTop.neg.mul inverseRadius_tendsto
  have h' : Tendsto (fun r : ℝ => -profileH r * (Real.sqrt (1 + r ^ 2))⁻¹) atTop (𝓝 0) := by
    simpa using h
  apply h'.congr'
  exact Eventually.of_forall (fun r => (radius_mul_square_error r).symm)

theorem radius_mul_error_tendsto :
    Tendsto (fun r : ℝ => r * (profileH r - 1)) atTop (𝓝 0) := by
  have h := radius_mul_square_error_tendsto.div
    (profileH_tendsto_atTop.add_const 1) (by norm_num)
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  have hd : profileH r + 1 ≠ 0 := by have := (profileH_bounds r hr).1; positivity
  simp only [Pi.div_apply]
  field_simp
  ring

theorem numerator_error_tendsto (t : ℝ) (ht : 0 < t) :
    Tendsto (fun r => r * (normalizedNumerator t r - 21)) atTop (𝓝 3) := by
  have h := ((radius_mul_profileHPrime_tendsto.add
    (profileH_tendsto_atTop.const_mul 3)).add radius_mul_square_error_tendsto).add
      ((profileA_tendsto_atTop t ht).const_mul 2)
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold normalizedNumerator
  field_simp
  ring

theorem denominator_error_tendsto :
    Tendsto (fun r => r * (normalizedDenominator r - 1)) atTop (𝓝 1) := by
  have h := radius_mul_error_tendsto.const_add 1
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold normalizedDenominator
  field_simp
  ring

/-- A stronger asymptotic than the displayed O(1/r) remainder. -/
theorem profileU_first_correction (t : ℝ) (ht : 0 < t) :
    Tendsto (fun r => r * (profileU t r - 21 / 2)) atTop (𝓝 (-9)) := by
  have h := ((numerator_error_tendsto t ht).sub
    (denominator_error_tendsto.const_mul 21)).div
      (normalizedDenominator_tendsto.const_mul 2) (by norm_num)
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [profileU_normalized t r hr]
  simp only [Pi.div_apply]
  have hd : normalizedDenominator r ≠ 0 := by
    have hh := (profileH_bounds r hr.le).1
    unfold normalizedDenominator
    positivity
  field_simp
  ring

theorem profileU_remainder_isBigO (t : ℝ) (ht : 0 < t) :
    Asymptotics.IsBigO atTop (fun r => profileU t r - 21 / 2) (fun r : ℝ => r⁻¹) := by
  apply Asymptotics.isBigO_of_div_tendsto_nhds ?_ (-9 : ℝ) ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact fun hz => False.elim ((inv_ne_zero hr.ne') hz)
  · change Tendsto (fun r : ℝ => (profileU t r - 21 / 2) / r⁻¹) atTop (𝓝 (-9))
    simpa only [div_inv_eq_mul, mul_comm] using profileU_first_correction t ht

end MagHK.PotentialAsymptotics
