import MagHK.MonopoleOrbital

/-! The actual trial radial orbital solves the lowest monopole radial ODE. -/
noncomputable section
namespace MagHK.Monopole
open Filter
open scoped Topology

theorem radialOrbital_hasDerivAt (s : ℝ) (hs : 0 < s) :
    HasDerivAt radialOrbital ((ell / s - s) * radialOrbital s) s := by
  have hp := Real.hasDerivAt_rpow_const (p := ell) (Or.inl (ne_of_gt hs))
  have he := ((((hasDerivAt_id s).pow 2).neg).div_const 2).exp
  have h := (hp.const_mul (Real.sqrt (2 / Real.Gamma (1 + Real.sqrt 3 / 2)))).mul he
  apply h.congr_deriv
  simp only [Pi.neg_apply, Pi.pow_apply, id_eq, radialOrbital]
  change _ = (ell / s - s) *
    (Real.sqrt (2 / Real.Gamma (1 + Real.sqrt 3 / 2)) * s ^ ell * Real.exp (-s ^ 2 / 2))
  rw [Real.rpow_sub hs, Real.rpow_one]
  field_simp
  ring

theorem radialOrbitalPrime_hasDerivAt (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun r => (ell / r - r) * radialOrbital r)
      (((ell / s - s) ^ 2 - ell / s ^ 2 - 1) * radialOrbital s) s := by
  have hu := ((hasDerivAt_const s ell).div (hasDerivAt_id s) (ne_of_gt hs)).sub
    (hasDerivAt_id s)
  have h := hu.mul (radialOrbital_hasDerivAt s hs)
  apply h.congr_deriv
  simp only [Pi.sub_apply, Pi.div_apply, id_eq]
  ring

theorem radialOrbital_second_derivative (s : ℝ) (hs : 0 < s) :
    deriv (deriv radialOrbital) s =
      ((ell / s - s) ^ 2 - ell / s ^ 2 - 1) * radialOrbital s := by
  have heq : deriv radialOrbital =ᶠ[𝓝 s] fun r => (ell / r - r) * radialOrbital r := by
    filter_upwards [eventually_gt_nhds hs] with r hr
    exact (radialOrbital_hasDerivAt r hr).deriv
  rw [heq.deriv_eq, (radialOrbitalPrime_hasDerivAt s hs).deriv]

theorem radialOrbital_eigen_equation (s : ℝ) (hs : 0 < s) :
    -deriv (deriv radialOrbital) s - 2 / s * deriv radialOrbital s +
      (1 / (2 * s ^ 2) + s ^ 2) * radialOrbital s =
        (2 + Real.sqrt 3) * radialOrbital s := by
  rw [radialOrbital_second_derivative s hs, (radialOrbital_hasDerivAt s hs).deriv]
  have he : 2 + Real.sqrt 3 = 2 * ell + 3 := by unfold ell; ring
  have hq := ell_quadratic
  rw [he]
  have hcoeff : -(ell / s - s) ^ 2 + ell / s ^ 2 + 1 -
      2 / s * (ell / s - s) + 1 / (2 * s ^ 2) + s ^ 2 = 2 * ell + 3 := by
    field_simp
    nlinarith only [hq]
  calc
    _ = (-(ell / s - s) ^ 2 + ell / s ^ 2 + 1 -
      2 / s * (ell / s - s) + 1 / (2 * s ^ 2) + s ^ 2) * radialOrbital s := by ring
    _ = _ := by rw [hcoeff]

end MagHK.Monopole
