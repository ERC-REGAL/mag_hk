import MagHK.MonopoleRadial
import MagHK.MonopoleTrial

/-! Concrete Friedrichs-form input for the monopole oscillator radial orbital.
The integrals use the literal spherical radial measure r² dr. -/
noncomputable section
namespace MagHK.MonopoleRadialDomain
open MeasureTheory Set
open MagHK.Monopole MagHK.MonopoleTrial
open scoped ContDiff

theorem radialOrbital_contDiffOn : ContDiffOn ℝ 2 radialOrbital (Ioi 0) := by
  intro r hr
  have hp : ContDiffAt ℝ 2 (fun s : ℝ => s ^ ell) r :=
    Real.contDiffAt_rpow_const_of_ne (ne_of_gt hr)
  have he : ContDiff ℝ 2 (fun s : ℝ => Real.exp (-s ^ 2 / 2)) := by fun_prop
  exact (((contDiffAt_const.mul hp).mul he.contDiffAt).contDiffWithinAt :
    ContDiffWithinAt ℝ 2 radialOrbital (Ioi 0) r)

theorem radialOrbital_bounded_origin : ∃ C : ℝ, ∀ r, 0 < r → r ≤ 1 →
    |radialOrbital r| ≤ C := by
  refine ⟨Real.sqrt (2 / Real.Gamma (1 + Real.sqrt 3 / 2)), ?_⟩
  intro r hr hr1
  rw [abs_of_pos (radialOrbital_positive r hr)]
  have hp := Real.rpow_le_one hr.le hr1 lowest_sector_limit_circle.1.le
  have he : Real.exp (-r ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg r])
  change Real.sqrt _ * r ^ ell * Real.exp _ ≤ _
  calc
    _ ≤ Real.sqrt (2 / Real.Gamma (1 + Real.sqrt 3 / 2)) * 1 * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg _)) he
        (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

theorem radialOrbital_unweighted_sq_integrable :
    IntegrableOn (fun r => radialOrbital r ^ 2) (Ioi (0 : ℝ)) := by
  apply radial_inverse_square_integrable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [← radialOrbital_squared_density r hr]
  field_simp [ne_of_gt (show 0 < r from hr)]

theorem radialOrbital_fourth_weight_integrable :
    IntegrableOn (fun r => r ^ 4 * radialOrbital r ^ 2) (Ioi (0 : ℝ)) := by
  have hell := lowest_sector_limit_circle.1
  apply ((integrableOn_rpow_mul_exp_neg_rpow
    (by linarith : (-1 : ℝ) < 2 * ell + 4)
    (by norm_num : (0 : ℝ) < 2)).const_mul
      (2 / Real.Gamma (ell + 3 / 2))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have he : r ^ 4 * radialOrbital r ^ 2 = r ^ 2 * radialDensity r := by
    rw [← radialOrbital_squared_density r hr]
    ring
  rw [he]
  unfold radialDensity
  rw [show 2 * ell + 4 = 2 + (2 * ell + 2) by ring, Real.rpow_add hr,
    Real.rpow_two]
  ring

theorem radialOrbital_derivative_energy_integrable :
    IntegrableOn (fun r => r ^ 2 * deriv radialOrbital r ^ 2) (Ioi (0 : ℝ)) := by
  have hi := ((radialOrbital_unweighted_sq_integrable.const_mul (ell ^ 2)).sub
    (radialOrbital_squared_integrable.const_mul (2 * ell))).add
      radialOrbital_fourth_weight_integrable
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  change ell ^ 2 * radialOrbital r ^ 2 - 2 * ell * (r ^ 2 * radialOrbital r ^ 2) +
    r ^ 4 * radialOrbital r ^ 2 = r ^ 2 * deriv radialOrbital r ^ 2
  rw [(radialOrbital_hasDerivAt r hr).deriv]
  field_simp [ne_of_gt (show 0 < r from hr)]
  ring

theorem radialOrbital_finite_energy : Integrable
    (fun r => deriv radialOrbital r ^ 2 + (1 / (2 * r ^ 2) + r ^ 2) *
      radialOrbital r ^ 2) radialVolume := by
  have hm : Measurable (fun r : ℝ => Real.toNNReal (r ^ 2)) := by fun_prop
  apply (integrable_withDensity_iff_integrable_smul hm).mpr
  have hi := (radialOrbital_derivative_energy_integrable.add
    (radialOrbital_unweighted_sq_integrable.const_mul (1 / 2))).add
      radialOrbital_fourth_weight_integrable
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  change r ^ 2 * deriv radialOrbital r ^ 2 + 1 / 2 * radialOrbital r ^ 2 +
    r ^ 4 * radialOrbital r ^ 2 =
    (Real.toNNReal (r ^ 2) : ℝ) *
      (deriv radialOrbital r ^ 2 + (1 / (2 * r ^ 2) + r ^ 2) * radialOrbital r ^ 2)
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  field_simp [ne_of_gt (show 0 < r from hr)]
  ring

end MagHK.MonopoleRadialDomain
