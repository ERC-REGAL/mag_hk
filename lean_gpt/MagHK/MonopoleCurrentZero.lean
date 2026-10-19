import MagHK.RadialCurrent
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The distributional derivative operator on a connected open interval
has only constants in its kernel. This universal background fact is stated
separately from the concrete stationary-current application. -/
noncomputable section
namespace MagHK.MonopoleCurrentZero
open MeasureTheory Set
open scoped ContDiff

/-- The standard kernel theorem for the distributional derivative, stated
through literal smooth compactly supported tests and ordinary integrals.
There is no radial field or quantum state in this operator-theory input. -/
def StandardDistributionKernelLibrary : Prop :=
  ∀ (s : Set ℝ), IsOpen s → IsPreconnected s → ∀ f : ℝ → ℝ,
    LocallyIntegrableOn f s →
    (∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → Function.support χ ⊆ s →
      (∫ x in s, deriv χ x * f x) = 0) →
    ∃ c : ℝ, ∀ᵐ x ∂volume.restrict s, f x = c

theorem stationary_radial_flux_constant (weak : StandardDistributionKernelLibrary)
    (a : ℝ → ℝ) (ha : ContinuousOn a (Ioi (0 : ℝ)))
    (hweak : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      Function.support χ ⊆ Ioi 0 →
      (∫ r in Ioi (0 : ℝ), deriv χ r * (r ^ 2 * a r)) = 0) :
    ∃ c : ℝ, ∀ r > 0, r ^ 2 * a r = c := by
  have hg : ContinuousOn (fun r => r ^ 2 * a r) (Ioi (0 : ℝ)) :=
    (continuous_pow 2).continuousOn.mul ha
  obtain ⟨c, hc⟩ := weak (Ioi 0) isOpen_Ioi (convex_Ioi (0 : ℝ)).isPreconnected
    (fun r => r ^ 2 * a r) (hg.locallyIntegrableOn measurableSet_Ioi) hweak
  have he := Measure.eqOn_open_of_ae_eq hc isOpen_Ioi hg continuousOn_const
  exact ⟨c, fun r hr => he hr⟩

theorem stationary_radial_inverse_square (weak : StandardDistributionKernelLibrary)
    (a : ℝ → ℝ) (ha : ContinuousOn a (Ioi (0 : ℝ)))
    (hweak : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      Function.support χ ⊆ Ioi 0 →
      (∫ r in Ioi (0 : ℝ), deriv χ r * (r ^ 2 * a r)) = 0) :
    ∃ c : ℝ, ∀ r > 0, a r = c / r ^ 2 := by
  obtain ⟨c, hc⟩ := stationary_radial_flux_constant weak a ha hweak
  refine ⟨c, fun r hr => ?_⟩
  apply (eq_div_iff (pow_ne_zero 2 (ne_of_gt hr))).mpr
  simpa only [mul_comm] using hc r hr

end MagHK.MonopoleCurrentZero
