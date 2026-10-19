import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp

/-!
The analytic radial-flow step of the monopole proof. The actual weighted
L¹ condition and the stationary radial differential equation force zero
current. The reduction of a rotation-invariant distributional current to
these one-dimensional hypotheses is a separate geometric/PDE obligation.
-/

namespace MagHK.Monopole

open MeasureTheory Set Filter

theorem stationary_radial_flux_constant (a : ℝ → ℝ)
    (hstationary : ∀ r > 0, HasDerivAt (fun s => s ^ 2 * a s) 0 r) :
    ∀ r > 0, r ^ 2 * a r = a 1 := by
  have hd : DifferentiableOn ℝ (fun s => s ^ 2 * a s) (Ioi (0 : ℝ)) := by
    intro r hr
    exact (hstationary r hr).differentiableAt.differentiableWithinAt
  have he : EqOn (deriv (fun s => s ^ 2 * a s)) 0 (Ioi (0 : ℝ)) := by
    intro r hr
    exact (hstationary r hr).deriv
  intro r hr
  have h := isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0 : ℝ)).isPreconnected
    hd he hr (show (1 : ℝ) ∈ Ioi (0 : ℝ) by norm_num)
  simpa using h

/-- An integrable constant on the infinite half-line must be zero. -/
theorem radial_flux_constant_zero (c : ℝ)
    (hc : IntegrableOn (fun _ : ℝ => c) (Ioi (0 : ℝ))) : c = 0 := by
  have h := (integrableOn_const_iff (C := c)).mp hc
  simpa only [Real.volume_Ioi, lt_self_iff_false, or_false, enorm_eq_zero] using h

/-- The radial current vanishes from the literal weighted L¹ hypothesis. -/
theorem stationary_integrable_radial_current_zero (a : ℝ → ℝ)
    (hstationary : ∀ r > 0, HasDerivAt (fun s => s ^ 2 * a s) 0 r)
    (hint : IntegrableOn (fun r => r ^ 2 * |a r|) (Ioi (0 : ℝ))) :
    ∀ r > 0, a r = 0 := by
  have hflux := stationary_radial_flux_constant a hstationary
  have habs : ∀ r > 0, r ^ 2 * |a r| = |a 1| := by
    intro r hr
    rw [← abs_of_nonneg (sq_nonneg r), ← abs_mul, hflux r hr]
  have hc : IntegrableOn (fun _ : ℝ => |a 1|) (Ioi (0 : ℝ)) := by
    apply hint.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact habs r hr
  have hzero := abs_eq_zero.mp (radial_flux_constant_zero |a 1| hc)
  intro r hr
  have h := hflux r hr
  rw [hzero] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 (ne_of_gt hr))

/-- A version suited to a weak stationary continuity equation, which yields
a constant radial flux only almost everywhere. -/
theorem integrable_constant_radial_flux_ae_zero (a : ℝ → ℝ) (c : ℝ)
    (hflux : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), r ^ 2 * a r = c)
    (hint : IntegrableOn (fun r => r ^ 2 * |a r|) (Ioi (0 : ℝ))) :
    c = 0 ∧ a =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  have hc : IntegrableOn (fun _ : ℝ => |c|) (Ioi (0 : ℝ)) := by
    apply hint.congr
    filter_upwards [hflux] with r hr
    rw [← abs_of_nonneg (sq_nonneg r), ← abs_mul, hr]
  have hc0 := abs_eq_zero.mp (radial_flux_constant_zero |c| hc)
  refine ⟨hc0, ?_⟩
  filter_upwards [hflux, ae_restrict_mem measurableSet_Ioi] with r hr hrpos
  change a r = 0
  rw [hc0] at hr
  exact (mul_eq_zero.mp hr).resolve_left (pow_ne_zero 2 (ne_of_gt hrpos))

end MagHK.Monopole
