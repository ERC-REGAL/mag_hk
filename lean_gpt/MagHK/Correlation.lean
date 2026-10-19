import MagHK.Monopole
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
The angular obstruction in the monopole correlation argument, including
almost-everywhere equations. This module proves that a separated radial
product cannot solve the reduced Coulomb eigen-equation. Identifying a
singlet determinant with that separated form still requires the rotation
representation and spherical-coordinate constructions.
-/

namespace MagHK.Monopole

open MeasureTheory Set Filter

noncomputable def coulombAngular (s t μ : ℝ) : ℝ :=
  1 / Real.sqrt (s ^ 2 + t ^ 2 - 2 * s * t * μ)

theorem coulombAngular_denominator_pos (s t μ : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hμ : μ < 1) :
    0 < s ^ 2 + t ^ 2 - 2 * s * t * μ := by
  have hprod : 0 < 2 * s * t * (1 - μ) := by positivity
  nlinarith [sq_nonneg (s - t)]

theorem coulombAngular_continuousOn (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    ContinuousOn (coulombAngular s t) (Ioo (-1 : ℝ) 1) := by
  apply continuousOn_const.div
    ((continuous_const.add continuous_const).sub
      (continuous_const.mul continuous_id)).sqrt.continuousOn
  intro μ hμ
  exact ne_of_gt (Real.sqrt_pos.2 (coulombAngular_denominator_pos s t μ hs ht hμ.2))

/-- Continuity rules out an a.e. constant Coulomb angular multiplier. -/
theorem no_ae_constant_coulomb (s t K : ℝ) (hs : 0 < s) (ht : 0 < t) :
    ¬ (∀ᵐ μ ∂volume.restrict (Ioo (-1 : ℝ) 1), coulombAngular s t μ = K) := by
  intro h
  have heq := Measure.eqOn_open_of_ae_eq h isOpen_Ioo
    (coulombAngular_continuousOn s t hs ht) continuousOn_const
  exact no_constant_coulomb_angular_factor s t K hs ht heq

/-- The obstruction holds for complex radial coefficients as well. -/
theorem no_ae_coulomb_multiple (s t : ℝ) (A B : ℂ)
    (hs : 0 < s) (ht : 0 < t) (hA : A ≠ 0) :
    ¬ (∀ᵐ μ ∂volume.restrict (Ioo (-1 : ℝ) 1),
      (coulombAngular s t μ : ℂ) * A = B) := by
  intro h
  have hc : ContinuousOn (fun μ => (coulombAngular s t μ : ℂ) * A)
      (Ioo (-1 : ℝ) 1) :=
    (Complex.continuous_ofReal.comp_continuousOn
      (coulombAngular_continuousOn s t hs ht)).mul continuousOn_const
  have heq := Measure.eqOn_open_of_ae_eq h isOpen_Ioo hc continuousOn_const
  have heq0 := heq (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 by constructor <;> norm_num)
  have heqh := heq (show -(1 : ℝ) / 2 ∈ Ioo (-1 : ℝ) 1 by constructor <;> norm_num)
  have hcoul : coulombAngular s t (-(1 : ℝ) / 2) = coulombAngular s t 0 := by
    exact Complex.ofReal_injective (mul_right_cancel₀ hA (heqh.trans heq0.symm))
  have hstrict := coulomb_angular_nonconstant s t hs ht
  have hh : s ^ 2 + t ^ 2 - 2 * s * t * (-(1 : ℝ) / 2) =
      s ^ 2 + t ^ 2 + s * t := by ring
  simp only [coulombAngular, hh, mul_zero, sub_zero] at hcoul
  exact (ne_of_lt hstrict) hcoul

theorem angular_factor_nonzero (μ : ℝ) (θ : ℂ) (hμ : μ < 1)
    (hθ : Complex.normSq θ = (1 - μ) / (16 * Real.pi ^ 2)) : θ ≠ 0 := by
  intro hz
  have hp : 0 < (1 - μ) / (16 * Real.pi ^ 2) := by
    apply div_pos (sub_pos.2 hμ)
    positivity
  simp only [hz, map_zero] at hθ
  linarith

/-- No division by the angular factor at its zeros is needed. -/
theorem no_ae_separated_equation (s t E : ℝ) (A B : ℂ) (θ : ℝ → ℂ)
    (hs : 0 < s) (ht : 0 < t) (hA : A ≠ 0)
    (hθ : ∀ᵐ μ ∂volume.restrict (Ioo (-1 : ℝ) 1), θ μ ≠ 0) :
    ¬ (∀ᵐ μ ∂volume.restrict (Ioo (-1 : ℝ) 1),
      (B + ((coulombAngular s t μ : ℂ) - E) * A) * θ μ = 0) := by
  intro heq
  apply no_ae_coulomb_multiple s t A ((E : ℂ) * A - B) hs ht hA
  filter_upwards [heq, hθ] with μ h hne
  have hz := (mul_eq_zero.mp h).resolve_right hne
  linear_combination hz

/-- A nonzero radial orbital cannot satisfy the separated equation on
almost every radius pair and angle. The radial kinetic coefficient B is
arbitrary, so no differentiability of the hypothetical orbital is used. -/
theorem radial_factor_zero_of_separated_equation
    (f : ℝ → ℂ) (B : ℝ → ℝ → ℂ) (θ : ℝ → ℝ → ℝ → ℂ) (E : ℝ)
    (hθ : ∀ s > 0, ∀ t > 0,
      ∀ᵐ μ ∂volume.restrict (Ioo (-1 : ℝ) 1), θ s t μ ≠ 0)
    (heq : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ᵐ μ ∂volume.restrict (Ioo (-1 : ℝ) 1),
        (B s t + ((coulombAngular s t μ : ℂ) - E) * (f s * f t)) * θ s t μ = 0) :
    f =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  have hprod : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), f s * f t = 0 := by
    filter_upwards [heq, ae_restrict_mem measurableSet_Ioi] with s hs hspos
    filter_upwards [hs, ae_restrict_mem measurableSet_Ioi] with t ht htpos
    by_contra hne
    exact no_ae_separated_equation s t E (f s * f t) (B s t) (θ s t)
      hspos htpos hne (hθ s hspos t htpos) ht
  by_contra hnonzero
  apply hnonzero
  filter_upwards [hprod] with s hs
  change f s = 0
  by_contra hsne
  apply hnonzero
  filter_upwards [hs] with t ht
  exact (mul_eq_zero.mp ht).resolve_left hsne

/-- The normalization condition contradicts the reduced eigen-equation.
The almost-everywhere angular nonvanishing follows from its exact
probability density, including for a complex angular phase. -/
theorem no_normalized_separated_coulomb_eigenfunction
    (f : ℝ → ℂ) (B : ℝ → ℝ → ℂ) (θ : ℝ → ℝ → ℝ → ℂ) (E : ℝ)
    (hnorm : ∫ s in Ioi (0 : ℝ), s ^ 2 * Complex.normSq (f s) = 1)
    (hθ : ∀ s > 0, ∀ t > 0, ∀ μ ∈ Ioo (-1 : ℝ) 1,
      Complex.normSq (θ s t μ) = (1 - μ) / (16 * Real.pi ^ 2)) :
    ¬ (∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ᵐ μ ∂volume.restrict (Ioo (-1 : ℝ) 1),
        (B s t + ((coulombAngular s t μ : ℂ) - E) * (f s * f t)) * θ s t μ = 0) := by
  intro heq
  have hθne : ∀ s > 0, ∀ t > 0,
      ∀ᵐ μ ∂volume.restrict (Ioo (-1 : ℝ) 1), θ s t μ ≠ 0 := by
    intro s hs t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with μ hμ
    exact angular_factor_nonzero μ (θ s t μ) hμ.2 (hθ s hs t ht μ hμ)
  have hf := radial_factor_zero_of_separated_equation f B θ E hθne heq
  have hint : (∫ s in Ioi (0 : ℝ), s ^ 2 * Complex.normSq (f s)) = 0 := by
    calc
      _ = ∫ _s in Ioi (0 : ℝ), (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [hf] with s hs
        change f s = 0 at hs
        simp [hs]
      _ = 0 := integral_zero _ _
  linarith

end MagHK.Monopole
