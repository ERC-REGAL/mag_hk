import MagHK.GaussianRealization

/-! The stronger Gaussian zero-sector bound stated in the manuscript. -/
noncomputable section
namespace MagHK.GaussianGap
open MeasureTheory
open MagHK.Noninteracting MagHK.RadialEndpoints MagHK.RadialRealization
open MagHK.GaussianRealization MagHK.GaussianIntegrals
open MagHK.GaussianDomains MagHK.SecondOrbital
open scoped InnerProductSpace

theorem gaussian_zero_nonzero_energy_ge_four (t : ℝ) (ht : 0 < t)
    (S : RadialSystem)
    (A : StandardRadialFacts S (gaussianA t) (scalar t) (gaussianU t))
    (E : ℝ) (hE : Eigen S 0 E) (hE0 : E ≠ 0) : 4 ≤ E := by
  obtain ⟨ψ, hψ, hψ0, he⟩ := hE
  have hc := gaussian_coefficients t ht
  obtain ⟨hD, hA, hprod, hnorm⟩ := A.zero_product hc ψ hψ
  let φ : State := S.D.map ⟨ψ, hD⟩
  have hm : E * mass ψ = mass φ := by
    rw [he, inner_smul_right, real_inner_self_eq_norm_sq] at hnorm
    simpa only [mass_eq_norm_sq] using hnorm
  have hψm := mass_pos ψ hψ0
  have hφ0 : φ ≠ 0 := by
    intro hz
    have hz' : mass φ = 0 := by rw [hz, mass_eq_norm_sq, norm_zero]; norm_num
    rw [hz'] at hm
    exact hE0 ((mul_eq_zero.mp hm).resolve_right hψm.ne')
  have hφm := mass_pos φ hφ0
  have hprodE := hprod.trans he
  obtain ⟨hAD, htransfer⟩ := MagHK.Ordering.eigenvector_transfer S.D S.A ψ E hD hA hprodE
  have hW (r : ℝ) (hr : 0 < r) : 1 < partnerCorrection (gaussianA t) (gaussianU t) r :=
    gaussian_partner_correction_gt_one t r ht hr
  obtain ⟨hform, hint, hp⟩ := A.partner_product hc
    (fun r hr => le_trans zero_le_one (hW r hr).le) φ hA hAD
  have hground : 2 * mass φ ≤ quadratic S (gaussianA t) (scalar t) (-1) φ := by
    rw [A.ground_transform 2 (gaussianProduct t) (minusState t ht.le)
      (gaussian_minus_solution t ht) φ hform]
    have hg : 0 ≤ groundRemainder S (gaussianProduct t) φ :=
      integral_nonneg (fun _ => sq_nonneg _)
    linarith
  have hmult : mass φ ≤ multiplier (partnerCorrection (gaussianA t) (gaussianU t)) φ := by
    apply integral_mono_ae (density_integrable φ) hint
    filter_upwards [radialMeasure_positive] with r hr
    have hd : 0 ≤ density φ r := sq_nonneg _
    nlinarith [hW r hr]
  rw [htransfer, inner_smul_right, real_inner_self_eq_norm_sq,
    ← mass_eq_norm_sq] at hp
  nlinarith

end MagHK.GaussianGap
